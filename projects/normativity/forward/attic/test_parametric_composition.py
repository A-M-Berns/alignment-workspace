"""WP-2: the mapping check, and the theorem that consumes the interface."""

from __future__ import annotations

import pathlib
import unittest
from dataclasses import replace
from fractions import Fraction as Q

from src.joint import movement_recursion, uniform_wealth_cap
from src.parametric_composition import (
    AUDIT_CONDITIONALS,
    AUDITED_PAIR,
    CONSUMED_CLAUSES,
    DECLARED_CLAUSES_REQUIRED,
    EQUIVALENT,
    IMPLIED_BY_SI,
    IMPLIES_SI,
    MECHANISM_HYPOTHESES,
    MOVING_INTERFACE_MAP,
    NEITHER,
    NO_COUNTERPART,
    UNCOVERED_HYPOTHESES,
    UNUSED_CLAUSES,
    MechanismParameters,
    composite_hypotheses,
    instance_corollary,
    mapping_findings,
    mapping_is_identity,
    parametric_composite,
)
from src.settlement_interface import (
    CLAUSE_TEXT,
    DeclaredHypothesis,
    ReferenceEngine,
    reference_record,
)

ENGINE = ReferenceEngine().declaration
RECORD = reference_record()
MECHANISM = MechanismParameters(Q(0), Q(2), Q(0), 1)
ALL_HYPOTHESES = composite_hypotheses("the test")


class MappingTests(unittest.TestCase):
    """The mapping check.  Every condition lands somewhere, and gaps are findings."""

    def test_every_condition_of_the_corpus_bundle_is_mapped(self):
        labels = [m.label for m in MOVING_INTERFACE_MAP]
        self.assertEqual(len(labels), len(set(labels)))
        self.assertEqual(len(labels), 9, "eight conditions, the clock one split")
        for mapping in MOVING_INTERFACE_MAP:
            with self.subTest(condition=mapping.label):
                self.assertTrue(mapping.condition.strip())
                self.assertTrue(mapping.note.strip())
                self.assertIn(mapping.relation,
                              (IMPLIED_BY_SI, IMPLIES_SI, EQUIVALENT, NEITHER,
                               NO_COUNTERPART))

    def test_named_clauses_exist_in_the_interface(self):
        for mapping in MOVING_INTERFACE_MAP:
            for clause in mapping.clauses:
                with self.subTest(clause=clause):
                    self.assertIn(clause, CLAUSE_TEXT)
        for clause, note in UNUSED_CLAUSES:
            with self.subTest(clause=clause):
                self.assertIn(clause, CLAUSE_TEXT)
                self.assertTrue(note.strip())

    def test_the_mapping_is_not_an_identity(self):
        self.assertFalse(mapping_is_identity())
        self.assertTrue(mapping_findings())

    def test_the_bundle_has_no_write_once_clause(self):
        """Nothing in the bundle prevents a variable being settled twice."""
        mentioned = {c for m in MOVING_INTERFACE_MAP for c in m.clauses}
        self.assertNotIn("J2", mentioned)
        self.assertIn("J2", dict(UNUSED_CLAUSES))

    def test_the_bundle_has_no_coherence_tolerance_clause(self):
        """It carries a solver-error budget, which is a different quantity."""
        self.assertIn("T1", dict(UNUSED_CLAUSES))
        solver = next(m for m in MOVING_INTERFACE_MAP if m.label == "MI-6")
        self.assertEqual(solver.relation, NEITHER)
        self.assertIn("solver", solver.note)

    def test_at_least_one_condition_is_strictly_stronger_than_any_clause_needs(self):
        stronger = [m.label for m in MOVING_INTERFACE_MAP
                    if m.relation == IMPLIES_SI]
        self.assertTrue(stronger)
        self.assertIn("MI-3", stronger, "the ambient fixed-core condition")

    def test_the_conditions_with_no_counterpart_become_explicit_hypotheses(self):
        absent = [m.label for m in MOVING_INTERFACE_MAP
                  if m.relation == NO_COUNTERPART]
        self.assertTrue(absent)
        for label in absent:
            with self.subTest(label=label):
                self.assertTrue(any(name.startswith(label + "-")
                                    for name in UNCOVERED_HYPOTHESES))

    def test_the_relation_counts_are_what_the_documents_report(self):
        """Pin the counts the prose quotes, so the two cannot drift apart."""
        from collections import Counter

        counts = Counter(m.relation for m in MOVING_INTERFACE_MAP)
        self.assertEqual(counts[IMPLIED_BY_SI], 1)
        self.assertEqual(counts[IMPLIES_SI], 2)
        self.assertEqual(counts[NO_COUNTERPART], 3)
        self.assertEqual(counts[NEITHER], 2)
        self.assertEqual(counts[EQUIVALENT], 1)
        self.assertEqual(len(UNUSED_CLAUSES), 12)
        self.assertEqual(len(UNCOVERED_HYPOTHESES), 4)
        self.assertEqual(len(CLAUSE_TEXT), 18)

    def test_the_published_table_carries_every_row(self):
        """The delivered table and the module cannot drift apart."""
        path = pathlib.Path(__file__).resolve().parents[1] / "MOVING_INTERFACE_MAP.md"
        if not path.is_file():
            self.skipTest("the mapping table has not been written yet")
        text = path.read_text()
        for mapping in MOVING_INTERFACE_MAP:
            self.assertIn(mapping.label, text)
        for clause, _ in UNUSED_CLAUSES:
            self.assertIn(clause, text)


class ParametricTheoremTests(unittest.TestCase):
    """The theorem consumes the interface rather than a condition bundle."""

    def test_it_yields_the_corpus_bound_when_every_hypothesis_is_in_place(self):
        verdict = parametric_composite(ENGINE, RECORD, MECHANISM, ALL_HYPOTHESES)
        self.assertTrue(verdict.holds, verdict.obstructions)
        theta = ENGINE.core_minimum
        caps = movement_recursion(theta, Q(0), Q(2), Q(0), 1)
        self.assertEqual(verdict.movement_cap, caps[1])
        self.assertEqual(verdict.bound,
                         uniform_wealth_cap(theta, Q(0), Q(2), caps[1]))
        self.assertEqual(verdict.bound, Q(30))

    def test_it_reports_no_bound_at_all_when_a_hypothesis_is_missing(self):
        """No number is ever produced on an unearned antecedent."""
        verdict = parametric_composite(ENGINE, RECORD, MECHANISM)
        self.assertFalse(verdict.holds)
        self.assertIsNone(verdict.bound)
        self.assertTrue(verdict.missing_hypotheses)

    def test_every_declared_hypothesis_is_individually_load_bearing(self):
        for omitted in ALL_HYPOTHESES:
            kept = tuple(h for h in ALL_HYPOTHESES if h is not omitted)
            with self.subTest(omitted=omitted.clause):
                verdict = parametric_composite(ENGINE, RECORD, MECHANISM, kept)
                self.assertFalse(verdict.holds)
                self.assertIsNone(verdict.bound)
                self.assertIn(omitted.clause,
                              verdict.missing_hypotheses + verdict.failing_clauses)

    def test_a_failing_checkable_clause_blocks_the_theorem(self):
        record = replace(RECORD, worst_case_exposure=Q(-9))
        engine = replace(ENGINE, downside_limit=Q(2))
        verdict = parametric_composite(engine, record, MECHANISM, ALL_HYPOTHESES)
        self.assertFalse(verdict.holds)
        self.assertIn("P2", verdict.failing_clauses)

    def test_an_engine_without_a_core_minimum_gets_no_bound(self):
        engine = replace(ENGINE, core_minimum=None)
        verdict = parametric_composite(engine, RECORD, MECHANISM, ALL_HYPOTHESES)
        self.assertFalse(verdict.holds)
        self.assertIn("P1", verdict.failing_clauses)

    def test_the_bound_degrades_as_the_core_minimum_shrinks(self):
        """P1's content: force that evaporates as conviction decays."""
        bounds = []
        for theta in (Q(2, 5), Q(1, 4), Q(1, 10), Q(1, 100)):
            engine = replace(ENGINE, core_minimum=theta)
            verdict = parametric_composite(engine, RECORD, MECHANISM,
                                           ALL_HYPOTHESES)
            self.assertTrue(verdict.holds, verdict.obstructions)
            bounds.append(verdict.bound)
        self.assertEqual(bounds, sorted(bounds))
        self.assertGreater(bounds[-1], bounds[0])

    def test_a_core_minimum_the_record_cannot_support_is_refused(self):
        """The check bites: this record's endorsement admits at most 2/5.

        The maximal coefficient here is the closed form `(M - r) / (M - m)`,
        which for the displayed endorsement is `(1 - 3/5) / (1 - 0) = 2/5`.  A
        declaration above it is not a slightly worse bound -- it is no bound.
        """
        engine = replace(ENGINE, core_minimum=Q(1, 2))
        verdict = parametric_composite(engine, RECORD, MECHANISM, ALL_HYPOTHESES)
        self.assertFalse(verdict.holds)
        self.assertIn("P1", verdict.failing_clauses)
        self.assertIsNone(verdict.bound)

    def test_the_theorem_is_not_vacuous(self):
        """An engine satisfying the antecedent exists and is exhibited."""
        verdict = parametric_composite(ENGINE, RECORD, MECHANISM, ALL_HYPOTHESES)
        self.assertTrue(verdict.holds)
        self.assertIsNotNone(verdict.bound)

    def test_what_was_leaned_on_is_reported(self):
        verdict = parametric_composite(ENGINE, RECORD, MECHANISM, ALL_HYPOTHESES)
        self.assertEqual(len(verdict.leaned_on), len(DECLARED_CLAUSES_REQUIRED))

    def test_the_hypothesis_set_covers_every_named_requirement(self):
        clauses = {h.clause for h in ALL_HYPOTHESES}
        for name in (DECLARED_CLAUSES_REQUIRED + UNCOVERED_HYPOTHESES
                     + AUDIT_CONDITIONALS + MECHANISM_HYPOTHESES):
            with self.subTest(name=name):
                self.assertIn(name, clauses)
        for hypothesis in ALL_HYPOTHESES:
            self.assertTrue(hypothesis.statement.strip())

    def test_the_consumed_clauses_are_interface_clauses(self):
        for clause in CONSUMED_CLAUSES:
            self.assertIn(clause, CLAUSE_TEXT)


class InstanceCorollaryTests(unittest.TestCase):
    """The audited pair, with exactly the three named conditionals."""

    def _hypothesis(self, clause: str) -> DeclaredHypothesis:
        return DeclaredHypothesis(f"H:{clause}", clause, "declared", "the audit")

    def test_it_holds_under_exactly_the_three_named_conditionals(self):
        corollary = instance_corollary(
            AUDITED_PAIR, MECHANISM, Q(1, 10),
            self._hypothesis("consistency-of-declared-theory"),
            self._hypothesis("core-minimum-or-clipping-adapter"),
            self._hypothesis("working-tolerance"))
        self.assertTrue(corollary.holds)
        self.assertEqual(corollary.named_conditionals, AUDIT_CONDITIONALS)
        self.assertEqual(len(corollary.named_conditionals), 3)
        self.assertEqual(corollary.bound, Q(198))

    def test_each_conditional_is_required(self):
        supplied = {name: self._hypothesis(name) for name in AUDIT_CONDITIONALS}
        for omitted in AUDIT_CONDITIONALS:
            arguments = dict(supplied)
            arguments[omitted] = None
            with self.subTest(omitted=omitted):
                corollary = instance_corollary(
                    AUDITED_PAIR, MECHANISM, Q(1, 10),
                    arguments["consistency-of-declared-theory"],
                    arguments["core-minimum-or-clipping-adapter"],
                    arguments["working-tolerance"])
                self.assertFalse(corollary.holds)
                self.assertIsNone(corollary.bound)
                self.assertIn(omitted, corollary.missing)

    def test_the_disclosure_says_the_pair_is_read_not_built(self):
        corollary = instance_corollary(AUDITED_PAIR, MECHANISM, Q(1, 10), None,
                                       None, None)
        joined = " ".join(corollary.disclosure)
        self.assertIn("not", joined)
        self.assertIn("construction", joined)

    def test_the_pair_s_outside_set_names_the_open_clauses(self):
        self.assertIn("T1", AUDITED_PAIR.outside)
        self.assertIn("S8-logical", AUDITED_PAIR.outside)
        self.assertNotIn("T1", AUDITED_PAIR.inhabited_clauses)


if __name__ == "__main__":
    unittest.main()
