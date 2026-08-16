from dataclasses import replace
from pathlib import Path
import re
import unittest

from src.composition import build_two_step_history, verify_history
from src.migration import (
    DispositionCell,
    DispositionMode,
    OccurrenceSort,
    OccurrenceStatus,
    verify_migration,
)
from src.composition import build_merge_migration
from src.standing import (
    BENCHMARK_CASES,
    MAXIMALITY_SCOPE,
    REALIZABLE_SCOPE,
    BurdenRoute,
    CellFacts,
    EnumerationScope,
    OccurrenceFacts,
    ScopedGrant,
    ScopedTermination,
    StandingTransportPlan,
    SupportEdge,
    authority_duplicated_or_transferred,
    available_grants,
    available_terminations,
    benchmark_cell,
    benchmark_plan,
    burden_disappeared,
    canonical_maximality_report,
    canonical_plan,
    check_transport_plan,
    cm_n1_accepts,
    enumerate_cells,
    reinstatement_plan,
    run_enumeration,
    semantic_independence_report,
    standing_created_without_sponsor,
    suspension_laundered,
    verify_history_transport,
)

_LIVE = OccurrenceStatus.LIVE
_SUSP = OccurrenceStatus.SUSPENDED


class StandingTransportTests(unittest.TestCase):
    def _codes(self, verdict):
        return {witness.code for witness in verdict.counterwitnesses}

    def test_standing_claim_ledger_is_complete(self):
        root = Path(__file__).resolve().parents[1]
        theory = (root / "STANDING_TRANSPORT.md").read_text()
        ledger = (root / "LEDGER.md").read_text()
        theory_ids = set(re.findall(r"\{#(ST-[A-Z0-9]+)\}", theory))
        ledger_ids = set(re.findall(r"^\| (ST-[A-Z0-9]+) ", ledger, re.MULTILINE))
        self.assertEqual(theory_ids, ledger_ids)
        self.assertTrue(theory_ids)
        allowed = (
            "PROVED+MACHINE-CHECKED",
            "PROVED+INDEPENDENTLY-REDERIVED",
            "PROVED (single derivation)",
            "PROVED-CONDITIONAL (conditions listed)",
            "REFUTED (witness displayed)",
            "CONJECTURE (not proved)",
            "PROPOSED (interface revision)",
            "OPEN",
        )
        for claim in theory_ids:
            position = theory.index(f"{{#{claim}}}")
            self.assertTrue(
                any(status in theory[position : position + 260] for status in allowed), claim)

    # ---- the mandatory benchmark cases -----------------------------------

    def test_benchmark_cases_classify_as_required(self):
        expected = {"A": False, "B": True, "C": False, "D": False,
                    "E": True, "F": True, "G": True}
        for case in BENCHMARK_CASES:
            cell = benchmark_cell(case)
            verdict = check_transport_plan(cell, benchmark_plan(case))
            self.assertEqual(verdict.accepted, expected[case], (case, self._codes(verdict)))
            for witness in verdict.counterwitnesses:
                self.assertTrue(witness.ids and witness.detail)

    def test_original_laundering_merge_fails(self):
        cell = benchmark_cell("A")
        verdict = check_transport_plan(cell, benchmark_plan("A"))
        self.assertFalse(verdict.accepted)
        # The defect is a disappearing burden, not a status lift.
        self.assertEqual(self._codes(verdict), {"standing.burden_vanished"})
        self.assertEqual(verdict.burden_outcomes["in:S"], "vanished")
        self.assertTrue(burden_disappeared(cell, benchmark_plan("A")))
        self.assertTrue(suspension_laundered(cell, benchmark_plan("A")))

    def test_provenance_separated_merge_passes_and_cm_n1_rejects_it(self):
        cell = benchmark_cell("B")
        verdict = check_transport_plan(cell, benchmark_plan("B"))
        self.assertTrue(verdict.accepted, self._codes(verdict))
        self.assertFalse(cm_n1_accepts(cell))
        # Standing and authority for the merged output come only from the live input.
        self.assertEqual(verdict.standing_sponsors["out:M"], ("in:L",))
        self.assertEqual(verdict.authority_assignment, {"out:M": "in:L"})
        # The suspended branch's burden continues on the residual.
        self.assertEqual(verdict.burden_outcomes["in:S"], "carried:out:S")
        for name, predicate in (("standing", standing_created_without_sponsor),
                                ("authority", authority_duplicated_or_transferred),
                                ("burden", burden_disappeared),
                                ("laundering", suspension_laundered)):
            self.assertFalse(predicate(cell, benchmark_plan("B")), name)

    def test_residual_free_merge_and_authority_split_fail(self):
        residual_free = check_transport_plan(benchmark_cell("C"), benchmark_plan("C"))
        self.assertFalse(residual_free.accepted)
        self.assertIn("standing.burden_vanished", self._codes(residual_free))
        split = check_transport_plan(benchmark_cell("D"), benchmark_plan("D"))
        self.assertFalse(split.accepted)
        self.assertEqual(self._codes(split), {"standing.authority_duplicated"})
        # CM-N1 does not catch the split at all; only the allocation rule does.
        self.assertTrue(cm_n1_accepts(benchmark_cell("D")))

    def test_downward_reconciliation_passes(self):
        cell = benchmark_cell("E")
        verdict = check_transport_plan(cell, benchmark_plan("E"))
        self.assertTrue(verdict.accepted, self._codes(verdict))
        self.assertEqual(verdict.burden_outcomes["in:S"], "carried:out:M")
        self.assertEqual(verdict.authority_assignment, {})
        self.assertTrue(cm_n1_accepts(cell))

    def test_reinstatement_needs_a_scoped_basis(self):
        cell = benchmark_cell("F")
        bare = check_transport_plan(cell, canonical_plan(cell))
        self.assertFalse(bare.accepted)
        self.assertIn("standing.semantic_support_is_not_sponsorship", self._codes(bare))
        with_basis = check_transport_plan(cell, reinstatement_plan(cell))
        self.assertTrue(with_basis.accepted, self._codes(with_basis))
        # A grant whose evidential basis is empty is not a basis.
        hollow = replace(
            reinstatement_plan(cell),
            grants=tuple(replace(grant, basis_ref="")
                         for grant in reinstatement_plan(cell).grants))
        verdict = check_transport_plan(cell, hollow)
        self.assertFalse(verdict.accepted)
        self.assertIn("standing.reinstatement_without_basis", self._codes(verdict))

    def test_mixed_semantic_and_deontic_support_is_coherent(self):
        cell = benchmark_cell("G")
        plan = benchmark_plan("G")
        verdict = check_transport_plan(cell, plan)
        self.assertTrue(verdict.accepted, self._codes(verdict))
        # Both inputs contribute content; only one sponsors standing; a separate
        # scoped grant supplies practical authority, and it must be disclosed.
        self.assertEqual({edge.source_id for edge in plan.semantic_support}, {"in:L", "in:E"})
        self.assertEqual(verdict.standing_sponsors["out:M"], ("in:E",))
        self.assertEqual(verdict.authority_assignment["out:M"], "grant:authority:out:M")
        self.assertFalse(cm_n1_accepts(cell))

    # ---- the required conceptual separations -----------------------------

    def test_terminal_disposition_cannot_manufacture_unrelated_standing(self):
        """CM-N1's exception is per cell; a response to one input is not a warrant."""
        cell = CellFacts(
            "cell:disposal",
            (OccurrenceFacts("in:S1", _SUSP, False, True),
             OccurrenceFacts("in:S2", _SUSP, False, False)),
            (OccurrenceFacts("out:R", _SUSP, False, True),
             OccurrenceFacts("out:M", _LIVE, True, False)),
        )
        self.assertTrue(cm_n1_accepts(cell, cell_has_terminal_disposition=True))
        plan = canonical_plan(cell, terminations=available_terminations(cell))
        verdict = check_transport_plan(cell, plan)
        self.assertFalse(verdict.accepted)
        self.assertIn("standing.semantic_support_is_not_sponsorship", self._codes(verdict))
        self.assertEqual(verdict.standing_sponsors["out:M"], ())

    def test_semantic_support_cannot_substitute_for_standing_or_authority(self):
        cell = CellFacts(
            "cell:semantic",
            (OccurrenceFacts("in:S", _SUSP, False, False),),
            (OccurrenceFacts("out:M", _LIVE, True, False),),
        )
        total = StandingTransportPlan(
            "cell:semantic", (SupportEdge("in:S", "out:M"),), (), (), (), (), ())
        verdict = check_transport_plan(cell, total)
        self.assertFalse(verdict.accepted)
        self.assertIn("standing.semantic_support_is_not_sponsorship", self._codes(verdict))
        self.assertIn("standing.semantic_support_is_not_authority", self._codes(verdict))
        # Declaring the same edge as standing support does not help either: the
        # input is too weak.  Sponsorship is about standing, not about content.
        declared = replace(total, standing_support=(SupportEdge("in:S", "out:M"),),
                           authority_support=(SupportEdge("in:S", "out:M"),))
        again = check_transport_plan(cell, declared)
        self.assertFalse(again.accepted)
        self.assertIn("standing.unsponsored_standing", self._codes(again))

    def test_authority_sources_cannot_be_reused(self):
        cell = CellFacts(
            "cell:reuse",
            (OccurrenceFacts("in:A", _LIVE, True, False),
             OccurrenceFacts("in:B", _LIVE, True, False)),
            (OccurrenceFacts("out:1", _LIVE, True, False),
             OccurrenceFacts("out:2", _LIVE, True, False)),
        )
        standing = tuple(SupportEdge(s, t) for s in ("in:A", "in:B") for t in ("out:1", "out:2"))
        semantic = standing
        reused = StandingTransportPlan(
            "cell:reuse", semantic, standing,
            (SupportEdge("in:A", "out:1"), SupportEdge("in:A", "out:2")), (), (), ())
        verdict = check_transport_plan(cell, reused)
        self.assertFalse(verdict.accepted)
        self.assertIn("standing.authority_duplicated", self._codes(verdict))
        # Counting alone would accept this: two authoritative inputs, two outputs.
        self.assertTrue(cm_n1_accepts(cell))
        allocated = replace(
            reused,
            authority_support=(SupportEdge("in:A", "out:1"), SupportEdge("in:B", "out:2")))
        good = check_transport_plan(cell, allocated)
        self.assertTrue(good.accepted, self._codes(good))
        self.assertEqual(good.authority_assignment, {"out:1": "in:A", "out:2": "in:B"})

    def test_unresolved_burdens_cannot_disappear(self):
        cell = benchmark_cell("A")
        for plan in (
            canonical_plan(cell),
            replace(canonical_plan(cell), burden_routes=()),
            replace(canonical_plan(cell),
                    burden_routes=(BurdenRoute("in:S", "out:M", None),)),
        ):
            verdict = check_transport_plan(cell, plan)
            self.assertFalse(verdict.accepted, plan)
            self.assertTrue(
                {"standing.burden_vanished", "standing.burden_carrier_does_not_carry"}
                & self._codes(verdict), self._codes(verdict))

    def test_burden_carrier_may_not_be_stronger_than_the_input(self):
        """Burden-local monotonicity: the answer-owing lineage cannot strengthen."""
        cell = CellFacts(
            "cell:carry",
            (OccurrenceFacts("in:S", _SUSP, False, True),),
            (OccurrenceFacts("out:M", _LIVE, True, True),),
        )
        plan = replace(canonical_plan(cell),
                       burden_routes=(BurdenRoute("in:S", "out:M", None),))
        verdict = check_transport_plan(cell, plan)
        self.assertFalse(verdict.accepted)
        self.assertIn("standing.burden_carrier_stronger", self._codes(verdict))
        self.assertIn("standing.burden_carrier_authoritative", self._codes(verdict))

    def test_cell_scoped_termination_does_not_discharge_every_input(self):
        cell = CellFacts(
            "cell:multi",
            (OccurrenceFacts("in:S1", _SUSP, False, True),
             OccurrenceFacts("in:S2", _SUSP, False, True)),
            (),
        )
        one_witness = ScopedTermination(
            "termination:cell", "cell-scope:cell:multi", "response",
            "witness:one", "auth:x", True, None)
        plan = StandingTransportPlan(
            "cell:multi", (), (), (),
            (BurdenRoute("in:S1", None, "termination:cell"),
             BurdenRoute("in:S2", None, "termination:cell")),
            (one_witness,), ())
        verdict = check_transport_plan(cell, plan)
        self.assertFalse(verdict.accepted)
        unscoped = [w for w in verdict.counterwitnesses
                    if w.code == "standing.termination_unscoped"]
        self.assertEqual(len(unscoped), 2)

    def test_stored_assertions_cannot_make_a_malformed_plan_pass(self):
        cell = benchmark_cell("F")
        plan = reinstatement_plan(cell)
        self.assertTrue(check_transport_plan(cell, plan).accepted)
        # Asserting that a burden is resolved, with no witness, does not resolve it.
        hollow = replace(plan, terminations=tuple(
            replace(item, witness_ref="", burden_resolved=True) for item in plan.terminations))
        verdict = check_transport_plan(cell, hollow)
        self.assertFalse(verdict.accepted)
        self.assertIn("standing.termination_unwitnessed", self._codes(verdict))
        # Asserting a resolving kind that cannot resolve does not resolve it either.
        mislabelled = replace(plan, terminations=tuple(
            replace(item, kind="loss", burden_resolved=True) for item in plan.terminations))
        second = check_transport_plan(cell, mislabelled)
        self.assertFalse(second.accepted)
        self.assertIn("standing.termination_kind_cannot_resolve", self._codes(second))
        # An idle assertion is reported rather than ignored.
        idle = replace(plan, grants=plan.grants + (
            ScopedGrant("grant:spare", "authority", "out:M", "basis", "auth"),))
        third = check_transport_plan(cell, idle)
        self.assertFalse(third.accepted)
        self.assertIn("standing.unused_assertion", self._codes(third))

    # ---- comparison with CM-N1 -------------------------------------------

    def test_cm_n1_accepts_a_vanishing_burden(self):
        """A minimal 1-to-1 counterexample to CM-N1 itself."""
        cell = CellFacts(
            "cell:drop",
            (OccurrenceFacts("in:S", _SUSP, False, True),),
            (OccurrenceFacts("out:S", _SUSP, False, False),),
        )
        self.assertTrue(cm_n1_accepts(cell))
        verdict = check_transport_plan(cell, canonical_plan(cell))
        self.assertFalse(verdict.accepted)
        self.assertEqual(self._codes(verdict), {"standing.burden_vanished"})

    def test_comparison_over_the_realizable_scope(self):
        report = run_enumeration(REALIZABLE_SCOPE)
        self.assertEqual(report.cells_examined, 5184)
        self.assertEqual(report.plan_checks, 20736)
        self.assertEqual(report.cm_n1_accepted, 1220)
        self.assertEqual(dict(report.transport_accepted)["grants=False,terminations=False"], 1831)
        self.assertEqual(report.agreements, 3991)
        # Strictly weaker on the lift axis, strictly stronger on burden and
        # allocation: the two conditions are incomparable.
        self.assertEqual(report.transport_only_count, 902)
        self.assertEqual(report.cm_n1_only_count, 291)
        self.assertTrue(report.cm_n1_only and report.transport_only)
        lift = report.transport_only[0].cell
        self.assertEqual(len(lift.inputs), 2)
        self.assertEqual(len(lift.outputs), 1)
        drop = report.cm_n1_only[0].cell
        self.assertIn("standing.burden_vanished", drop and report.cm_n1_only[0].codes)

    def test_cm_n1_with_burden_and_allocation_implies_transport(self):
        """The exact implication: CM-N1 is a coarse sufficient special case."""
        stronger = 0
        for cell in enumerate_cells(REALIZABLE_SCOPE):
            plan = canonical_plan(cell)
            accepted = check_transport_plan(cell, plan).accepted
            coarse = (cm_n1_accepts(cell)
                      and not burden_disappeared(cell, plan)
                      and not suspension_laundered(cell, plan)
                      and not authority_duplicated_or_transferred(cell, plan))
            if coarse:
                self.assertTrue(accepted, cell)
            if accepted and not cm_n1_accepts(cell):
                stronger += 1
        self.assertEqual(stronger, 902)

    def test_predicate_is_sound_and_exact_on_the_realizable_scope(self):
        report = run_enumeration(REALIZABLE_SCOPE)
        self.assertEqual(report.unsound_count, 0)
        self.assertEqual(report.stricter_count, 0)
        self.assertEqual(report.unsound, ())
        self.assertEqual(report.stricter_than_safety, ())

    # ---- the finite enumeration ------------------------------------------

    def test_enumeration_is_deterministic_and_reports_its_scope(self):
        first, second = run_enumeration(), run_enumeration()
        self.assertEqual(first, second)
        self.assertEqual(first.scope.shapes, ((1, 1), (1, 2), (2, 1), (2, 2)))
        self.assertEqual(first.scope.configurations, 12)
        self.assertEqual(first.cells_examined, 144 + 1728 + 1728 + 20736)
        self.assertEqual(first.cells_examined, 24336)
        self.assertEqual(first.plan_checks, 24336 * 4)
        self.assertEqual(first.unsound_count, 0)
        self.assertEqual(dict(first.transport_accepted)["grants=True,terminations=True"], 24336)
        cells = list(enumerate_cells(EnumerationScope(shapes=((1, 1),))))
        self.assertEqual(len(cells), 144)
        self.assertEqual(len({(tuple(c.inputs), tuple(c.outputs)) for c in cells}), 144)

    def test_canonical_plan_is_maximally_permissive(self):
        for allow_grants, allow_terminations in ((False, False), (True, True)):
            report = canonical_maximality_report(
                MAXIMALITY_SCOPE, allow_grants=allow_grants,
                allow_terminations=allow_terminations)
            self.assertEqual(report.failures, ())
            self.assertEqual(report.satisfiable_cells, report.canonical_accepted_cells)
            self.assertEqual(report.cells_examined, 576)
            self.assertEqual(report.record_setting, (allow_grants, allow_terminations))
        bare = canonical_maximality_report(MAXIMALITY_SCOPE)
        self.assertEqual(bare.satisfiable_cells, 218)
        self.assertGreater(bare.plans_examined, 15000)

    def test_semantic_support_never_changes_the_verdict(self):
        report = semantic_independence_report()
        self.assertEqual(report.failures, ())
        self.assertEqual(report.invariant_cells, report.cells_examined)
        self.assertEqual(report.cells_examined, 5184)
        self.assertEqual(report.variants_examined, 69760)

    # ---- the two-step history --------------------------------------------

    def test_transport_composes_across_the_two_step_history(self):
        for repair in ("suspended-lineage", "merged-suspension", "authorized-loss"):
            history = build_two_step_history(repair)
            composite = verify_history(history)
            transport = verify_history_transport(history)
            self.assertTrue(composite.passed, repair)
            self.assertTrue(transport.accepted, (repair, transport.counterwitnesses))
            self.assertEqual(transport.cm_n1_rejected_cells, ())
            self.assertEqual(transport.transport_rejected_cells, ())
            self.assertEqual(len(transport.steps), 2)

    def test_laundering_history_is_rejected_for_the_burden_not_the_lift(self):
        history = build_two_step_history("merged-live")
        transport = verify_history_transport(history)
        self.assertFalse(transport.accepted)
        self.assertEqual(transport.transport_rejected_cells, ("step:12/d12:e-merge",))
        self.assertEqual(transport.cm_n1_rejected_cells, ("step:12/d12:e-merge",))
        codes = {witness.code for witness in transport.counterwitnesses}
        self.assertEqual(codes, {"standing.burden_vanished"})
        witness = transport.counterwitnesses[0]
        self.assertEqual(witness.ids, ("e:frustration-suspended",))

    def test_split_then_merge_does_not_duplicate_deontic_sponsorship(self):
        history = build_two_step_history("merged-suspension")
        composite = verify_history(history)
        transport = verify_history_transport(history)
        self.assertTrue(transport.accepted)
        # Two lineage paths reach the merged output; sponsorship is still single.
        self.assertEqual(composite.lineage.duplicate_pairs,
                         (("e:harm", "e:merged-suspended++"),))
        merge = next(v for v in transport.steps[1].verdicts if v.cell_id == "d12:e-merge")
        self.assertEqual(merge.authority_assignment, {})
        self.assertEqual(len(merge.standing_sponsors["e:merged-suspended++"]), 2)
        self.assertEqual(merge.burden_outcomes,
                         {"e:frustration-suspended": "carried:e:merged-suspended++"})

    def test_case_b_is_inexpressible_as_one_frozen_cell(self):
        """The missing expressive resource: a mixed-status many-to-many cell."""
        old, new, certificate = build_merge_migration("suspended-lineage")
        keep = tuple(cell for cell in certificate.cells
                     if cell.cell_id not in ("d12:e-pc", "d12:e-f"))
        rejected = {}
        for mode in DispositionMode:
            hypercell = DispositionCell(
                "d12:e-both", OccurrenceSort.ENTITLEMENT,
                ("e:physical-or-coercion", "e:frustration-suspended"),
                ("e:bodily-or-coercive++", "e:frustration-suspended++"),
                mode, "reconstruct:frustration",
                "auth:migration-2" if mode in (
                    DispositionMode.RETRACT, DispositionMode.DISCHARGE,
                    DispositionMode.LOSS) else None)
            candidate = replace(
                certificate, cells=keep + (hypercell,),
                suspensions=tuple(
                    replace(entry, source_ref="d12:e-both")
                    if entry.suspension_id == "suspension:frustration-entitlement-2" else entry
                    for entry in certificate.suspensions),
                losses=tuple(
                    replace(loss, source_ref="d12:e-both")
                    if loss.loss_id == "loss:coercion-separation" else loss
                    for loss in certificate.losses))
            report = verify_migration(old, new, candidate)
            self.assertFalse(report.passed, mode)
            rejected[mode.value] = tuple(
                sorted({w.code for w in report.counterwitnesses if w.code.startswith("cell.")}))
        self.assertEqual(len(rejected), 8)
        for mode, codes in rejected.items():
            self.assertTrue(codes, mode)
        self.assertIn("cell.merge_cardinality", rejected["merge"])
        self.assertIn("cell.suspend_status", rejected["suspend"])
        self.assertIn("cell.refine_cardinality", rejected["refine"])
        self.assertIn("cell.preserve_cardinality", rejected["preserve"])
        # The separated two-cell form of the same migration does verify.
        self.assertTrue(verify_migration(old, new, certificate).passed)


if __name__ == "__main__":
    unittest.main()
