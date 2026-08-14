from dataclasses import replace
from pathlib import Path
import re
import unittest

from src.grammar import (
    CATALOG, CATALOG_BY_ID, DEFAULT_DEPTH_CAP, REGISTRY, AblationResult, Grounds,
    JudgeFootprint, ObjectionType, RecordAccess, TableKind, ablate_table,
    check_footprint, classification_agrees, evidence_projection_classes,
    footprint_classes, judge_objection, legacy_classes, splits_against_legacy)

TABLES = {
    "book.endorsements": {"b:1": 1},
    "book.declared_rates": {"default_resolution_rate": (1, 2)},
    "schedule.procedure": {1: {"threshold": (3, 4)}},
    "settled.record": {"b:1": 0},
    "rulings": {"ru:1": {"basis": "default", "schedule_version": 1,
                         "date": 1, "stakes": 3}},
    "ledger.obligations": {"d:1": "open"},
    "ledger.coverage": {},
    "region": {"infeasible": True},
    "arrivals": {},
    "liabilities": {},
}


def _codes(verdict):
    return {o.code for o in verdict.obstructions}


class GrammarTests(unittest.TestCase):
    # The ledger-completeness check moved to the consolidation, which now
    # owns the claim ledger and enforces coverage in its own runner.
    def test_registry_is_finite_and_kind_typed(self):
        names = [spec.name for spec in REGISTRY]
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual({spec.kind for spec in REGISTRY},
                         {TableKind.STANDARD, TableKind.EVIDENCE})

    def test_every_catalog_type_declares_a_well_formed_footprint(self):
        for objection in CATALOG:
            self.assertEqual(check_footprint(objection), (), objection.type_id)
            self.assertTrue(objection.footprint.declared, objection.type_id)

    # GR-J1: enforcement soundness.
    def test_undeclared_table_access_is_always_caught(self):
        for spec in REGISTRY:
            leaky = ObjectionType(
                f"leak:{spec.name}", JudgeFootprint(("book.endorsements",), ()),
                lambda access, grounds, name=spec.name: bool(access.read(name)))
            verdict = judge_objection(leaky, TABLES, Grounds("g", {}))
            if spec.name == "book.endorsements":
                self.assertTrue(verdict.accepted, spec.name)
                continue
            self.assertFalse(verdict.accepted, spec.name)
            self.assertIn("grammar.undeclared_table_read", _codes(verdict))
            self.assertIn(spec.name, verdict.obstructions[0].tables)
            # A rejected judgement yields no verdict at all.
            self.assertIsNone(verdict.upheld)

    def test_membership_probing_counts_as_a_read(self):
        prober = ObjectionType("probe", JudgeFootprint(("book.endorsements",), ()),
                               lambda access, grounds: access.available("rulings"))
        verdict = judge_objection(prober, TABLES, Grounds("g", {}))
        self.assertFalse(verdict.accepted)
        self.assertIn("grammar.undeclared_table_read", _codes(verdict))

    def test_unknown_and_miskinded_declarations_are_rejected(self):
        unknown = ObjectionType("u", JudgeFootprint(("no.such.table",), ()),
                                lambda access, grounds: True)
        self.assertIn("grammar.unknown_table", {o.code for o in check_footprint(unknown)})
        miskinded = ObjectionType("m", JudgeFootprint(("rulings",), ()),
                                  lambda access, grounds: True)
        self.assertIn("grammar.kind_mismatch", {o.code for o in check_footprint(miskinded)})
        both = ObjectionType("b", JudgeFootprint(("book.endorsements",),
                                                 ("book.endorsements",)),
                             lambda access, grounds: True)
        self.assertIn("grammar.kind_mismatch", {o.code for o in check_footprint(both)})

    def test_a_judge_that_raises_does_not_pass(self):
        def explode(access, grounds):
            raise KeyError("missing")
        broken = ObjectionType("x", JudgeFootprint(("book.endorsements",), ()), explode)
        verdict = judge_objection(broken, TABLES, Grounds("g", {}))
        self.assertFalse(verdict.accepted)
        self.assertIn("grammar.judge_failed", _codes(verdict))

    # GR-J3: the depth cap attaches to disposition-referencing grounds.
    def test_depth_cap_attaches_to_disposition_referencing_grounds(self):
        address = CATALOG_BY_ID["address"]
        self.assertTrue(address.references_dispositions)
        shallow = Grounds("g", {"bound_id": "b:1"}, ("disp:1",), DEFAULT_DEPTH_CAP)
        self.assertTrue(judge_objection(address, TABLES, shallow).accepted)
        deep = replace(shallow, depth=DEFAULT_DEPTH_CAP + 1)
        verdict = judge_objection(address, TABLES, deep)
        self.assertFalse(verdict.accepted)
        self.assertIn("grammar.depth_cap_exceeded", _codes(verdict))
        # A type that does not declare disposition reference may not smuggle one.
        frequency = CATALOG_BY_ID["frequency"]
        self.assertFalse(frequency.references_dispositions)
        smuggled = Grounds("g", {"bound_id": "b:1", "target": "b:1"}, ("disp:1",), 0)
        self.assertIn("grammar.undeclared_disposition_reference",
                      _codes(judge_objection(frequency, TABLES, smuggled)))

    # GR-J2: the computed classification.
    def test_computed_classification_does_not_reproduce_the_legacy_families(self):
        computed = footprint_classes(CATALOG)
        legacy = legacy_classes(CATALOG)
        evidence = evidence_projection_classes(CATALOG)
        self.assertFalse(classification_agrees(computed, legacy))
        self.assertGreater(len(computed), len(legacy))
        # Mixed standard/evidence reads split legacy families.
        splits = splits_against_legacy(CATALOG)
        self.assertTrue(splits)
        self.assertIn(("cross-subsidy", "exposure", "sure-loss"), splits)
        # The evidence projection is coarser than the full footprint, as expected.
        self.assertLessEqual(len(evidence), len(computed))
        for members in computed.values():
            self.assertTrue(members)

    def test_families_are_computed_not_stored(self):
        # No objection type carries a family field that anything reads as content.
        for objection in CATALOG:
            self.assertNotIn("family", objection.footprint.declared)
        # Recomputation is deterministic.
        self.assertEqual(footprint_classes(CATALOG), footprint_classes(CATALOG))

    # GR-N1: per-table ablation necessity.
    def test_dropping_the_rulings_table_blinds_exactly_its_readers(self):
        grounds = {
            "merits-evasion": Grounds("g1", {"ruling_id": "ru:1", "cleared": True}),
            "aggregate-default": Grounds("g2", {"window": (0, 2)}),
            "persistence": Grounds("g3", {}),
        }
        catalog = [CATALOG_BY_ID[name] for name in grounds]
        before = {name: judge_objection(CATALOG_BY_ID[name], TABLES, grounds[name]).upheld
                  for name in grounds}
        self.assertTrue(before["merits-evasion"])
        self.assertTrue(before["persistence"])
        result = ablate_table(catalog, TABLES, grounds, "rulings")
        self.assertIsInstance(result, AblationResult)
        # Exactly the declared readers of `rulings` lose their judgement.
        self.assertEqual(result.became_unavailable,
                         ("aggregate-default", "merits-evasion"))
        self.assertIn("merits-evasion", result.verdict_changed)
        # A type that never declared it is unaffected.
        self.assertEqual(result.still_accepted, ("persistence",))

    def test_ablating_the_book_blinds_the_sure_loss_judge(self):
        grounds = {"sure-loss": Grounds("g", {"farkas": ((1, 2),)})}
        catalog = [CATALOG_BY_ID["sure-loss"]]
        self.assertTrue(judge_objection(catalog[0], TABLES, grounds["sure-loss"]).upheld)
        result = ablate_table(catalog, TABLES, grounds, "book.endorsements")
        self.assertEqual(result.became_unavailable, ("sure-loss",))
        self.assertIn("sure-loss", result.verdict_changed)


if __name__ == "__main__":
    unittest.main()
