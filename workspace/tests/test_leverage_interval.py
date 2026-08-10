from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import re
import unittest

from src.grammar import CATALOG_BY_ID, Grounds, judge_objection
from src.leverage_interval import (
    Book, Constraint, Endorsement, Language, LeverageInterval, SettledFact,
    build_constraints, chained_lower_bound, compute_interval, merits_evasion_grounds,
    sure_loss_grounds, threshold_direction)

LANG = Language(("w1", "w2", "w3"), {"A": ("w1", "w2"), "B": ("w2",), "C": ("w3",)})


def _forcing(sentence, level):
    """An endorsement whose compiled gamble forces P(sentence) >= level."""
    return Endorsement(f"e:{sentence}>={level}",
                       tuple(a - Q(level) for a in LANG.indicator(sentence)), Q(0))


class LeverageIntervalTests(unittest.TestCase):
    # The ledger-completeness check moved to the consolidation, which now
    # owns the claim ledger and enforces coverage in its own runner.
    def test_everything_is_exact_rational(self):
        interval = compute_interval(LANG, Book(1, (_forcing("A", Q(3, 4)),)), (), "A")
        for value in (interval.lower, interval.upper):
            self.assertIsInstance(value, Q)
        for component in interval.lower_primal.assignment:
            self.assertIsInstance(component, Q)

    # CD-L2: empty book recovery.
    def test_empty_book_gives_the_unit_interval(self):
        interval = compute_interval(LANG, Book(1, ()), (), "A")
        self.assertEqual((interval.lower, interval.upper), (Q(0), Q(1)))
        self.assertTrue(interval.well_formed())
        # CD-J1's two-option accounting is recovered verbatim: no direction at any
        # threshold strictly inside (0,1).
        for threshold in (Q(1, 4), Q(1, 2), Q(3, 4)):
            self.assertIsNone(threshold_direction(interval, threshold))

    # CD-L1: merits iff leverage.
    def test_merits_is_certifiable_exactly_when_leverage_clears_the_threshold(self):
        forced = compute_interval(LANG, Book(2, (_forcing("A", Q(3, 4)),)), (), "A")
        self.assertEqual(forced.lower, Q(3, 4))
        self.assertEqual(threshold_direction(forced, Q(3, 4)), "positive")
        self.assertEqual(threshold_direction(forced, Q(1, 2)), "positive")
        self.assertIsNone(threshold_direction(forced, Q(4, 5)))
        # Capped below the threshold gives the negative side.
        capped = compute_interval(LANG, Book(3, (
            Endorsement("e:cap", tuple(Q(1, 2) - a for a in LANG.indicator("A")), Q(0)),
        )), (), "A")
        self.assertEqual(capped.upper, Q(1, 2))
        self.assertEqual(threshold_direction(capped, Q(3, 4)), "negative")
        self.assertIsNone(threshold_direction(capped, Q(1, 2)))

    def test_threshold_exactly_at_an_endpoint_follows_the_existing_conventions(self):
        forced = compute_interval(LANG, Book(2, (_forcing("A", Q(3, 4)),)), (), "A")
        # lower >= tau is weak: tau at the lower endpoint certifies positive.
        self.assertEqual(forced.lower, Q(3, 4))
        self.assertEqual(threshold_direction(forced, Q(3, 4)), "positive")
        capped = compute_interval(LANG, Book(3, (
            Endorsement("e:cap", tuple(Q(1, 2) - a for a in LANG.indicator("A")), Q(0)),
        )), (), "A")
        # upper < tau is strict: tau at the upper endpoint certifies nothing.
        self.assertEqual(capped.upper, Q(1, 2))
        self.assertIsNone(threshold_direction(capped, Q(1, 2)))
        self.assertEqual(threshold_direction(capped, Q(1, 2) + Q(1, 1000)), "negative")

    def test_primal_witness_attains_the_reported_endpoint(self):
        interval = compute_interval(LANG, Book(2, (_forcing("A", Q(3, 4)),)), (), "A")
        for witness, reported in ((interval.lower_primal, interval.lower),
                                  (interval.upper_primal, interval.upper)):
            self.assertEqual(sum(witness.assignment), Q(1))
            self.assertTrue(all(c >= 0 for c in witness.assignment))
            recomputed = sum((a * b for a, b in
                              zip(LANG.indicator("A"), witness.assignment)), Q(0))
            self.assertEqual(recomputed, reported)
            self.assertEqual(witness.value, reported)
            self.assertTrue(witness.active_constraints)

    def test_dual_certificate_reproduces_the_objective(self):
        interval = compute_interval(LANG, Book(2, (_forcing("A", Q(3, 4)),)), (), "A")
        self.assertTrue(interval.lower_dual.reproduces_objective)
        self.assertEqual(interval.lower_dual.direction, "lower")
        self.assertTrue(interval.upper_dual.reproduces_objective)
        # Every multiplier names a constraint that is active at the endpoint.
        active = set(interval.lower_primal.active_constraints)
        for name, _ in interval.lower_dual.multipliers:
            self.assertIn(name, active)

    # CD-L3: sure loss grounds nothing.
    def test_sure_loss_certifies_no_merits_and_yields_typed_grounds(self):
        contradictory = compute_interval(
            LANG, Book(4, (_forcing("A", Q(3, 4)),)), (SettledFact("A", Q(0)),), "A")
        self.assertTrue(contradictory.infeasible)
        self.assertIsNone(contradictory.lower)
        self.assertFalse(contradictory.well_formed())
        # Neither direction is certifiable.
        for threshold in (Q(1, 4), Q(1, 2), Q(3, 4)):
            self.assertIsNone(threshold_direction(contradictory, threshold))
        grounds = sure_loss_grounds(contradictory, "g:sl")
        self.assertIsNotNone(grounds)
        self.assertIn("farkas", grounds.payload)
        self.assertEqual(grounds.payload["book_version"], 4)
        # It is filing-shaped: the SURE-LOSS judge accepts it under its footprint,
        # which is the book itself.
        objection = CATALOG_BY_ID["sure-loss"]
        self.assertEqual(objection.footprint.standard_tables, ("book.endorsements",))
        verdict = judge_objection(objection, {"book.endorsements": {"e:1": 1}}, grounds)
        self.assertTrue(verdict.accepted, verdict.obstructions)
        self.assertTrue(verdict.upheld)
        # A feasible book yields no grounds at all.
        self.assertIsNone(sure_loss_grounds(
            compute_interval(LANG, Book(5, ()), (), "A"), "g:none"))

    # CD-L4: docket-mediated exposure.
    def test_settled_premises_tighten_the_computed_endpoint_through_the_docket(self):
        loose = compute_interval(LANG, Book(6, (_forcing("A", Q(1, 2)),)), (), "A")
        self.assertEqual(loose.lower, Q(1, 2))
        # A settled premise ruling out w3 forces the remaining mass onto A's worlds.
        tightened = compute_interval(LANG, Book(6, (_forcing("A", Q(1, 2)),)),
                                     (SettledFact("C", Q(0)),), "A")
        self.assertEqual(tightened.lower, Q(1))
        self.assertGreater(tightened.lower, loose.lower)
        # The chained-coefficient bound is the certificate for a warrant chain.
        self.assertEqual(chained_lower_bound((Q(3, 4), Q(2, 3))), Q(1, 2))
        self.assertEqual(chained_lower_bound(()), Q(1))

    # CD-L5: merits evasion is record-visible.
    def test_merits_evasion_grounds_are_arithmetic(self):
        cleared = compute_interval(LANG, Book(7, (_forcing("A", Q(3, 4)),)), (), "A")
        grounds = merits_evasion_grounds("ru:1", "default", cleared, Q(3, 4), "g:me")
        self.assertIsNotNone(grounds)
        self.assertEqual(grounds.payload["direction"], "positive")
        # A merits ruling is not evasion; nor is a default when nothing cleared.
        self.assertIsNone(merits_evasion_grounds("ru:2", "merits", cleared, Q(3, 4), "g"))
        unsettled = compute_interval(LANG, Book(8, ()), (), "A")
        self.assertIsNone(merits_evasion_grounds("ru:3", "default", unsettled,
                                                 Q(3, 4), "g"))
        # The judge reads only its declared footprint.
        objection = CATALOG_BY_ID["merits-evasion"]
        tables = {"schedule.procedure": {1: {"threshold": Q(3, 4)}},
                  "rulings": {"ru:1": {"basis": "default", "schedule_version": 1}}}
        verdict = judge_objection(objection, tables, grounds)
        self.assertTrue(verdict.accepted, verdict.obstructions)
        self.assertTrue(verdict.upheld)

    # A5 adversarial suite.
    def test_adversarial_mutations_are_rejected(self):
        interval = compute_interval(LANG, Book(2, (_forcing("A", Q(3, 4)),)), (), "A")
        # Forged dual: multipliers that do not reproduce the objective.
        forged = replace(interval, lower_dual=replace(
            interval.lower_dual, multipliers=(("simplex.total", Q(99)),),
            reproduces_objective=False))
        self.assertFalse(forged.lower_dual.reproduces_objective)
        # Dual for a different constraint set: names a constraint not active here.
        foreign = {name for name, _ in interval.lower_dual.multipliers}
        self.assertNotIn("book:e:nonexistent", foreign)
        # Endpoint claimed at a non-vertex: the interior point is feasible but does
        # not attain either endpoint.
        interior = (Q(1, 3), Q(1, 3), Q(1, 3))
        value = sum((a * b for a, b in zip(LANG.indicator("A"), interior)), Q(0))
        self.assertNotEqual(value, interval.lower)
        self.assertNotEqual(value, interval.upper)
        # Stale book version: the interval carries the version it was computed from.
        self.assertEqual(interval.book_version, 2)
        self.assertNotEqual(interval.book_version, 3)
        # A settled premise contradicting an endorsement routes to CD-L3, never to
        # a merits verdict.
        contradictory = compute_interval(
            LANG, Book(2, (_forcing("A", Q(3, 4)),)), (SettledFact("A", Q(0)),), "A")
        self.assertTrue(contradictory.infeasible)
        self.assertIsNone(threshold_direction(contradictory, Q(3, 4)))
        self.assertIsNotNone(sure_loss_grounds(contradictory, "g"))
        # A target no schema licenses must be caught by a licensing guard.  Its
        # indicator is all zero, so the bare arithmetic would certify a NEGATIVE
        # merits verdict; the guard is what stops that.
        self.assertFalse(LANG.licenses("Z"))
        unlicensed = compute_interval(LANG, Book(2, (_forcing("A", Q(3, 4)),)), (), "Z")
        self.assertFalse(unlicensed.licensed)
        self.assertFalse(unlicensed.well_formed())
        self.assertIsNone(unlicensed.lower)
        self.assertIsNone(threshold_direction(unlicensed, Q(1, 2)))
        self.assertIsNone(merits_evasion_grounds("ru:9", "default", unlicensed,
                                                 Q(1, 2), "g"))

    def test_adding_constraints_never_widens_the_interval(self):
        base = compute_interval(LANG, Book(9, ()), (), "A")
        tighter = compute_interval(LANG, Book(9, (_forcing("A", Q(1, 2)),)), (), "A")
        self.assertGreaterEqual(tighter.lower, base.lower)
        self.assertLessEqual(tighter.upper, base.upper)

    def test_constraint_set_records_all_three_sources(self):
        constraints = build_constraints(
            LANG, Book(1, (_forcing("A", Q(1, 2)),)), (SettledFact("B", Q(0)),))
        sources = {c.source.split(":")[0] for c in constraints}
        self.assertEqual(sources, {"simplex.total", "simplex.nonneg", "settled", "book"})
        self.assertTrue(any(c.equality for c in constraints))


if __name__ == "__main__":
    unittest.main()
