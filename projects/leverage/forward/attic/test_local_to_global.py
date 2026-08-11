from dataclasses import replace
from pathlib import Path
import re
import unittest

from src.composition import (
    accumulated_authority_bound,
    authority_provenance,
    build_two_step_history,
    compose_certificates,
)
from src.history import (
    AUTHORITY_SCOPE,
    BURDEN_SCOPE,
    HistoryFacts,
    StepFacts,
    associativity_report,
    borne_by_site,
    burden_ledger,
    check_with_burden_ledger,
    compose_transport,
    local_acceptance,
    merge_then_terminate_history,
    outcome_map,
    search_local_to_global,
    split_merge_split_history,
    authority_injection,
)
from src.migration import OccurrenceStatus
from src.standing import (
    BurdenRoute,
    CellFacts,
    OccurrenceFacts,
    ScopedGrant,
    ScopedTermination,
    available_terminations,
    canonical_plan,
    check_transport_plan,
)

_LIVE, _SUSP = OccurrenceStatus.LIVE, OccurrenceStatus.SUSPENDED


class LocalToGlobalTests(unittest.TestCase):
    def test_local_to_global_ledger_is_complete(self):
        root = Path(__file__).resolve().parents[1]
        theory = (root / "LOCAL_TO_GLOBAL.md").read_text()
        ledger = (root / "LEDGER.md").read_text()
        theory_ids = set(re.findall(r"\{#(LG-[A-Z0-9]+)\}", theory))
        ledger_ids = set(re.findall(r"^\| (LG-[A-Z0-9]+) ", ledger, re.MULTILINE))
        self.assertEqual(theory_ids, ledger_ids)
        self.assertTrue(theory_ids)
        allowed = ("PROVED+MACHINE-CHECKED", "PROVED+INDEPENDENTLY-REDERIVED",
                   "PROVED (single derivation)", "PROVED-CONDITIONAL (conditions listed)",
                   "MACHINE-CHECKED (stated finite scope)", "REFUTED (witness displayed)",
                   "CONJECTURE (not proved)", "PROPOSED (interface revision)", "OPEN")
        for claim in theory_ids:
            position = theory.index(f"{{#{claim}}}")
            self.assertTrue(
                any(s in theory[position:position + 300] for s in allowed), claim)

    # 1. The corrected grant-aware CM-J8.
    def test_accumulated_authority_bound_is_grant_aware(self):
        # Extra authority at V_1 needs a grant issued by the *first* step.
        levels = {0: ("u",), 1: ("a", "b"), 2: ("a", "b")}
        self.assertTrue(accumulated_authority_bound(levels, {0: ("b",), 1: ()}))
        self.assertFalse(accumulated_authority_bound(levels, {0: (), 1: ()}))
        # A grant recorded at the wrong step does not license it.
        self.assertFalse(accumulated_authority_bound(levels, {0: (), 1: ("b",)}))
        # Extra authority at V_2 needs a grant issued by the second step.
        later = {0: ("u",), 1: ("a",), 2: ("a", "b")}
        self.assertTrue(accumulated_authority_bound(later, {0: (), 1: ("b",)}))
        self.assertFalse(accumulated_authority_bound(later, {0: ("b",), 1: ()}))
        # Grants at both steps accumulate.
        both = {0: ("u",), 1: ("a", "b"), 2: ("a", "b", "c")}
        self.assertTrue(accumulated_authority_bound(both, {0: ("b",), 1: ("c",)}))
        self.assertFalse(accumulated_authority_bound(both, {0: ("b",), 1: ()}))
        # Grant-free corollary: authority is monotone non-increasing.
        self.assertTrue(accumulated_authority_bound(
            {0: ("u", "v"), 1: ("a",), 2: ()}, {0: (), 1: ()}))
        self.assertFalse(accumulated_authority_bound(
            {0: ("u",), 1: ("a", "b"), 2: ()}, {0: (), 1: ()}))

    def test_one_grant_licenses_one_output(self):
        # Two authoritative outputs, one authoritative input, one grant: the
        # accumulated bound admits exactly one extra, never two.
        self.assertTrue(accumulated_authority_bound(
            {0: ("u",), 1: ("a", "b")}, {0: ("b",)}))
        self.assertFalse(accumulated_authority_bound(
            {0: ("u",), 1: ("a", "b", "c")}, {0: ("b",)}))
        # And the one-cell predicate refuses a plan that reuses one grant.
        cell = CellFacts("cell:g",
                         (OccurrenceFacts("in:A", _LIVE, True),),
                         (OccurrenceFacts("out:1", _LIVE, True),
                          OccurrenceFacts("out:2", _LIVE, True)))
        # The inherited licence is matched to one output; the grant must name
        # the other, and it licenses that one only.
        one_grant = ScopedGrant("grant:only", "authority", "out:1", "basis", "auth")
        plan = canonical_plan(cell, grants=(one_grant,))
        self.assertTrue(check_transport_plan(cell, plan).accepted,
                        check_transport_plan(cell, plan).counterwitnesses)
        reused = replace(plan, grants=(one_grant, replace(one_grant, output_id="out:2")))
        self.assertFalse(check_transport_plan(cell, reused).accepted)

    def test_authority_provenance_is_step_indexed(self):
        history = build_two_step_history("suspended-lineage")
        ledger = authority_provenance(history, compose_certificates(history))
        record = next(r for r in ledger if r.start_occurrence == "e:harm")
        self.assertEqual([level for level, _ in record.levels], [0, 1, 2])
        self.assertEqual([step for step, _ in record.grants_by_step], [0, 1])
        self.assertTrue(record.grant_free)
        self.assertTrue(record.bound_respected)
        for entry in ledger:
            self.assertTrue(entry.bound_respected, entry)

    # 2/3. Two-step and three-step composition.
    def test_two_step_transport_composes_when_burdens_stay_separate(self):
        cell_one = CellFacts(
            "cell:carry", (OccurrenceFacts("in:A", _SUSP, False, True),),
            (OccurrenceFacts("mid:C", _SUSP, False, True),))
        cell_two = CellFacts("cell:close", (OccurrenceFacts("mid:C", _SUSP, False, True),), ())
        history = HistoryFacts("h:clean", (
            StepFacts((cell_one,), (canonical_plan(cell_one),)),
            StepFacts((cell_two,), (canonical_plan(
                cell_two, terminations=available_terminations(cell_two)),))))
        transport = compose_transport(history)
        self.assertTrue(all(ok for _, _, ok in transport.local_acceptance))
        self.assertTrue(transport.accepted, transport.obstructions)
        self.assertEqual(len(transport.burden_routes), 1)
        route = transport.burden_routes[0]
        self.assertEqual(route.origin_occurrence, "in:A")
        self.assertEqual(route.outcome, "terminated")
        self.assertEqual(len(route.hops), 2)

    def test_three_step_split_merge_split_composes(self):
        history = split_merge_split_history()
        self.assertEqual(history.depth, 3)
        transport = compose_transport(history)
        self.assertTrue(all(ok for _, _, ok in transport.local_acceptance),
                        transport.local_acceptance)
        self.assertTrue(transport.accepted, transport.obstructions)
        self.assertEqual(len(transport.accumulated_grants), 1)
        step, _, output = transport.accumulated_grants[0]
        self.assertEqual((step, output), (2, "v3:x"))

    # 4/5. Authority provenance and shared-ancestor split-merge.
    def test_split_merge_split_does_not_duplicate_the_inherited_licence(self):
        transport = compose_transport(split_merge_split_history())
        injection = authority_injection(transport)
        # Two authoritative endpoints, two distinct licences, one of them granted.
        self.assertEqual(len(injection), 2)
        self.assertEqual(len(set(injection.values())), 2)
        inherited = [r for r, site in injection.items() if r.startswith("licence@0:")]
        granted = [r for r in injection if "grant" in r]
        self.assertEqual(len(inherited), 1)
        self.assertEqual(len(granted), 1)
        # The inherited licence crossed the split and the merge without splitting.
        route = next(r for r in transport.authority_routes
                     if r.resource_id == inherited[0])
        self.assertEqual(route.origin_occurrence, "v0:auth")
        self.assertGreaterEqual(len(route.hops), 3)

    # 6/7. Burden preservation and burden switching.
    def test_burden_survives_a_concept_merger_when_it_keeps_a_carrier(self):
        first = CellFacts(
            "cell:merge",
            (OccurrenceFacts("in:A", _SUSP, False, True),
             OccurrenceFacts("in:B", _LIVE, True)),
            (OccurrenceFacts("mid:C", _SUSP, False, True),))
        history = HistoryFacts("h:merge", (StepFacts((first,), (canonical_plan(first),)),))
        transport = compose_transport(history)
        self.assertTrue(transport.accepted, transport.obstructions)
        route = next(r for r in transport.burden_routes if r.origin_occurrence == "in:A")
        self.assertEqual(route.outcome, "outstanding")
        self.assertEqual(route.hops[-1][2], "mid:C")

    def test_burden_switching_to_a_branch_that_does_not_bear_it_is_rejected(self):
        cell = CellFacts(
            "cell:switch", (OccurrenceFacts("in:A", _SUSP, False, True),),
            (OccurrenceFacts("out:0", _SUSP, False, True),
             OccurrenceFacts("out:1", _SUSP, False, False)))
        plan = replace(canonical_plan(cell),
                       burden_routes=(BurdenRoute("in:A", "out:1", None),))
        verdict = check_transport_plan(cell, plan)
        self.assertFalse(verdict.accepted)
        self.assertIn("standing.burden_carrier_does_not_carry",
                      {w.code for w in verdict.counterwitnesses})

    # 8. An unrelated termination is rejected.
    def test_termination_scoped_to_another_ancestor_is_rejected(self):
        cell = CellFacts(
            "cell:multi",
            (OccurrenceFacts("in:A", _SUSP, False, True),
             OccurrenceFacts("in:B", _SUSP, False, True)),
            ())
        foreign = ScopedTermination("termination:A", "in:A", "response",
                                    "witness:A", "auth:x", True, None)
        plan = canonical_plan(cell)
        plan = replace(plan, terminations=(foreign,), burden_routes=(
            BurdenRoute("in:A", None, "termination:A"),
            BurdenRoute("in:B", None, "termination:A")))
        verdict = check_transport_plan(cell, plan)
        self.assertFalse(verdict.accepted)
        self.assertIn("standing.termination_unscoped",
                      {w.code for w in verdict.counterwitnesses})

    # 9. Reinstatement without a scoped basis.
    def test_reinstatement_without_scoped_basis_is_rejected(self):
        cell = CellFacts("cell:reinstate",
                         (OccurrenceFacts("in:S", _SUSP, False, False),),
                         (OccurrenceFacts("out:M", _LIVE, True, False),))
        self.assertFalse(check_transport_plan(cell, canonical_plan(cell)).accepted)
        hollow = ScopedGrant("grant:r", "reinstatement", "out:M", "", "auth")
        plan = canonical_plan(cell, grants=(hollow,))
        self.assertFalse(check_transport_plan(cell, plan).accepted)
        good = canonical_plan(cell, grants=(
            ScopedGrant("grant:r", "reinstatement", "out:M", "root:evidence", "auth"),
            ScopedGrant("grant:a", "authority", "out:M", "root:evidence", "auth")))
        self.assertTrue(check_transport_plan(cell, good).accepted)

    # THE central negative result.
    def test_local_acceptance_does_not_imply_global_acceptance(self):
        history = merge_then_terminate_history()
        acceptance = local_acceptance(history)
        self.assertTrue(all(ok for _, _, ok in acceptance), acceptance)
        transport = compose_transport(history)
        self.assertFalse(transport.accepted)
        self.assertEqual([o.code for o in transport.obstructions],
                         ["global.termination_over_scope"])
        obstruction = transport.obstructions[0]
        self.assertEqual(len(obstruction.resource_ids), 2)
        self.assertIsNotNone(obstruction.witness)
        # Two owed answers, one witness.
        closed = [r for r in transport.burden_routes if r.outcome == "terminated"]
        self.assertEqual(len(closed), 2)
        self.assertEqual(len({r.witness for r in closed}), 1)

    def test_the_ledger_repair_rejects_exactly_the_counterexample(self):
        history = merge_then_terminate_history()
        transport = compose_transport(history)
        borne = borne_by_site(transport)
        self.assertEqual(len(borne["mid:C"]), 2)
        second = history.steps[1]
        self.assertFalse(check_with_burden_ledger(second.cells[0], second.plans[0], borne))
        # With a single owed answer on the carrier the same cell is accepted.
        self.assertTrue(check_with_burden_ledger(
            second.cells[0], second.plans[0], {"mid:C": ("burden@0:in:A",)}))
        self.assertEqual(len(burden_ledger(history)), 1)

    # 10. Associativity.
    def test_associativity_up_to_outcome_equality(self):
        report = associativity_report(split_merge_split_history())
        self.assertTrue(report.associative)
        self.assertTrue(report.agrees_with_direct)
        self.assertEqual(dict(report.left), dict(report.right))
        self.assertEqual(dict(report.left), dict(report.direct))
        self.assertIn((0, "v0:owed"), report.direct)
        self.assertEqual(report.direct[(0, "v0:owed")][0], "terminated")
        # Keys are (origin version, origin occurrence), never the name alone.
        for key in report.direct:
            self.assertIsInstance(key, tuple)
            self.assertEqual(len(key), 2)

    def test_repeated_occurrence_names_across_versions_do_not_collide(self):
        """An occurrence identifier may legitimately repeat at a later version."""
        reused = CellFacts(
            "cell:a", (OccurrenceFacts("x", _SUSP, False, True),),
            (OccurrenceFacts("y", _SUSP, False, True),))
        second = CellFacts(
            "cell:b", (OccurrenceFacts("y", _SUSP, False, True),),
            (OccurrenceFacts("x", _SUSP, False, True),))
        third = CellFacts("cell:c", (OccurrenceFacts("x", _SUSP, False, True),), ())
        history = HistoryFacts("h:reuse", (
            StepFacts((reused,), (canonical_plan(reused),)),
            StepFacts((second,), (canonical_plan(second),)),
            StepFacts((third,), (canonical_plan(
                third, terminations=available_terminations(third)),))))
        transport = compose_transport(history)
        self.assertTrue(all(ok for _, _, ok in transport.local_acceptance))
        mapping = outcome_map(transport)
        # The name "x" occurs at version 0 and again at version 2; keying by the
        # name alone would silently identify two different resources.
        names = [name for _, name in mapping]
        self.assertEqual(names.count("x"), 1)
        self.assertEqual(len(mapping), len(set(mapping)))
        self.assertEqual(sorted(mapping), [(0, "x")])
        route = transport.burden_routes[0]
        self.assertEqual((route.origin_version, route.origin_occurrence), (0, "x"))
        self.assertEqual(route.outcome, "terminated")

    # 11. Mutations flip the verdict.
    def test_mutating_one_transport_edge_flips_the_verdict(self):
        history = split_merge_split_history()
        self.assertTrue(compose_transport(history).accepted)
        # Drop the burden route at the closing cell: the owed answer is abandoned.
        third = history.steps[2]
        broken_plan = replace(third.plans[1], burden_routes=())
        broken = HistoryFacts(history.history_id, history.steps[:2] + (
            StepFacts(third.cells, (third.plans[0], broken_plan)),))
        transport = compose_transport(broken)
        self.assertFalse(transport.accepted)
        self.assertIn("global.burden_abandoned",
                      {o.code for o in transport.obstructions})
        # Remove the scoped grant: the second endpoint licence is unsourced.
        ungranted_plan = replace(third.plans[0], grants=())
        ungranted = HistoryFacts(history.history_id, history.steps[:2] + (
            StepFacts(third.cells, (ungranted_plan, third.plans[1])),))
        self.assertIn("global.authority_unsourced",
                      {o.code for o in compose_transport(ungranted).obstructions})

    # 12. The bounded search, with its exact scope.
    def test_bounded_search_separates_local_from_global_failure(self):
        report = search_local_to_global(BURDEN_SCOPE)
        self.assertEqual(report.histories_examined, 222376)
        self.assertEqual(report.local_failures, 202844)
        self.assertEqual(report.local_pass_global_pass, 18749)
        self.assertEqual(report.local_pass_global_fail, 783)
        self.assertTrue(report.witnesses)
        for _, _, obstructions in report.witnesses:
            self.assertEqual({o.code for o in obstructions},
                             {"global.termination_over_scope"})
        repaired = search_local_to_global(BURDEN_SCOPE, repaired=True)
        self.assertEqual(repaired.local_pass_global_fail, 0)
        # The repair rejects precisely the counterexamples and nothing else.
        self.assertEqual(repaired.local_failures,
                         report.local_failures + report.local_pass_global_fail)
        self.assertEqual(repaired.local_pass_global_pass,
                         report.local_pass_global_pass)

    def test_authority_transport_composes_over_its_scope(self):
        report = search_local_to_global(AUTHORITY_SCOPE)
        self.assertEqual(report.histories_examined, 8400)
        self.assertEqual(report.local_pass_global_fail, 0)
        self.assertEqual(report.witnesses, ())
        self.assertGreater(report.local_pass_global_pass, 0)

    def test_search_is_deterministic(self):
        first = search_local_to_global(AUTHORITY_SCOPE)
        second = search_local_to_global(AUTHORITY_SCOPE)
        self.assertEqual(first.histories_examined, second.histories_examined)
        self.assertEqual(first.local_pass_global_fail, second.local_pass_global_fail)
        self.assertEqual(first.local_failures, second.local_failures)


if __name__ == "__main__":
    unittest.main()
