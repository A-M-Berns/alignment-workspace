"""WP-1: the incoherence functional, the robust docket, and the layering."""

from __future__ import annotations

import unittest
from fractions import Fraction as Q

from src.coherence import (
    BOOK_BREACH,
    ENGINE_BREACH,
    EXACT_SCHEDULE,
    NO_BREACH,
    PriceAssignment,
    ToleranceDeclaration,
    ToleranceSchedule,
    attribute_breach,
    certificate_excess,
    coherence_polytope,
    docket_polytope,
    incoherence,
    incoherence_is_monotone,
    incoherence_is_zero_iff_feasible,
    prices_are_feasible,
    relax,
    robust_certify_merits,
    robust_interval,
    robust_reduces_at_zero,
    robust_sure_loss_grounds,
    tolerance_is_working,
    verify_certificate,
    working_boundary,
)
from src.leverage_interval import (
    Book,
    Endorsement,
    Language,
    SettledFact,
    compute_interval,
    threshold_direction,
)

# Three worlds; A and B overlap at w2 and C is exactly w2, so the three prices
# are linked by the simplex identity  A + B - C = 1.
LANGUAGE = Language(("w1", "w2", "w3"),
                    {"A": ("w1", "w2"), "B": ("w2", "w3"), "C": ("w2",)})

# The displayed two-sentence book: p(A) >= 3/5 and p(B) >= 4/5.
BOOK = Book(1, (Endorsement("e:A", (Q(1), Q(1), Q(0)), Q(3, 5)),
                Endorsement("e:B", (Q(0), Q(1), Q(1)), Q(4, 5))))

COHERENT = PriceAssignment(1, {"A": Q(9, 10), "B": Q(1, 10)})
INCOHERENT = PriceAssignment(1, {"A": Q(9, 10), "B": Q(9, 10), "C": Q(0)})


class IncoherenceFunctionalTests(unittest.TestCase):

    def test_the_value_is_the_hand_computed_rational(self):
        """A + B - C = 1 forces the three prices apart by exactly 4/15.

        Pricing A and B at 9/10 each and their conjunction at 0 demands
        A + B - C = 9/5, while every assignment satisfies A + B - C = 1.  The
        excess 4/5 is spread over the three rows, giving 4/15 each.
        """
        report = incoherence(LANGUAGE, (), INCOHERENT)
        self.assertEqual(report.value, Q(4, 15))
        self.assertEqual(sum(report.witness), Q(1))
        self.assertTrue(all(value >= 0 for value in report.witness))

    def test_the_certificate_is_normalized_and_tight(self):
        report = incoherence(LANGUAGE, (), INCOHERENT)
        certificate = report.certificate
        self.assertIsNotNone(certificate)
        self.assertEqual(certificate.absolute_mass, Q(1))
        self.assertTrue(certificate.normalized)
        self.assertEqual(certificate.excess, Q(4, 15))
        self.assertTrue(verify_certificate(LANGUAGE, (), INCOHERENT, certificate))

    def test_the_certificate_is_verified_independently_of_its_extraction(self):
        """The bound is recomputed by its own program, not read back."""
        report = incoherence(LANGUAGE, (), INCOHERENT)
        recomputed = certificate_excess(LANGUAGE, (), INCOHERENT,
                                        report.certificate.multipliers)
        self.assertEqual(recomputed, report.value)

    def test_an_overweight_certificate_is_rejected(self):
        """Soundness needs total absolute mass at most one; more is refused."""
        from src.coherence import IncoherenceCertificate

        inflated = IncoherenceCertificate(
            (("A", Q(1)), ("B", Q(1)), ("C", Q(-1))), Q(4, 5), Q(3))
        self.assertFalse(inflated.normalized)
        self.assertFalse(verify_certificate(LANGUAGE, (), INCOHERENT, inflated))

    def test_zero_exactly_when_feasible(self):
        for assignment in (COHERENT, INCOHERENT):
            with self.subTest(assignment=assignment):
                self.assertTrue(
                    incoherence_is_zero_iff_feasible(LANGUAGE, (), assignment))
        self.assertEqual(incoherence(LANGUAGE, (), COHERENT).value, Q(0))
        self.assertTrue(prices_are_feasible(LANGUAGE, (), COHERENT))
        self.assertFalse(prices_are_feasible(LANGUAGE, (), INCOHERENT))

    def test_monotone_under_adding_a_pin(self):
        """Pinning C at 1/2 shrinks the coherent set, so the value cannot drop."""
        before = incoherence(LANGUAGE, (), INCOHERENT).value
        after = incoherence(LANGUAGE, (SettledFact("C", Q(1, 2)),), INCOHERENT).value
        self.assertGreaterEqual(after, before)
        self.assertTrue(incoherence_is_monotone(LANGUAGE, (), INCOHERENT,
                                                (SettledFact("C", Q(1, 2)),)))

    def test_a_coherent_price_state_is_never_charged_for_an_infeasible_book(self):
        """The guard on the two polytopes.

        The book's endorsements are jointly infeasible with the pins while the
        engine's prices are exactly coherent.  The docket's region is empty --
        that is the book's sure-loss, chargeable to the book -- and the
        engine's incoherence is zero, so the layering tolls nothing.  Were the
        functional defined against the book's constraints, this would read as an
        engine breach and the wrong party would carry it.
        """
        infeasible_book = Book(2, (
            Endorsement("e:hi", (Q(1), Q(1), Q(0)), Q(3, 4)),
            Endorsement("e:lo", (Q(-1), Q(-1), Q(0)), Q(-1, 4))))
        prices = PriceAssignment(2, {"A": Q(1, 2)})
        self.assertTrue(
            compute_interval(LANGUAGE, infeasible_book, (), "A").infeasible)
        self.assertEqual(incoherence(LANGUAGE, (), prices).value, Q(0))
        attribution = attribute_breach(ToleranceDeclaration(0, Q(0)), Q(0))
        self.assertEqual(attribution.attributed_to, NO_BREACH)
        self.assertFalse(attribution.tolled)

    def test_the_two_polytopes_are_distinct_objects(self):
        engine_side = coherence_polytope(LANGUAGE, ())
        docket_side = docket_polytope(LANGUAGE, BOOK, ())
        self.assertNotEqual(engine_side, docket_side)
        self.assertFalse(any(c.source.startswith("book:") for c in engine_side))
        self.assertTrue(any(c.source.startswith("book:") for c in docket_side))


class RobustDocketTests(unittest.TestCase):

    def test_relaxation_never_touches_a_pin_or_the_simplex(self):
        settled = (SettledFact("C", Q(1, 5)),)
        base = docket_polytope(LANGUAGE, BOOK, settled)
        relaxed = relax(base, Q(1, 3))
        for before, after in zip(base, relaxed):
            if before.source.startswith(("simplex.", "settled:")):
                self.assertEqual(before, after)
            else:
                self.assertLess(after.rhs, before.rhs)

    def test_the_robust_forms_reduce_to_the_exact_ones_at_zero(self):
        """A theorem, not a remark: at zero the two programs are one program."""
        self.assertTrue(robust_reduces_at_zero(LANGUAGE, BOOK, (), "A"))
        exact = compute_interval(LANGUAGE, BOOK, (), "A")
        self.assertEqual(robust_interval(LANGUAGE, BOOK, (), "A", Q(0)), exact)
        certificate = robust_certify_merits(LANGUAGE, BOOK, (), "A", Q(1, 2), Q(0),
                                            "c:0")
        self.assertIsNotNone(certificate)
        self.assertEqual(certificate.interval, exact)
        self.assertEqual(certificate.direction,
                         threshold_direction(exact, Q(1, 2)))
        self.assertTrue(EXACT_SCHEDULE.exact)

    def test_the_robust_interval_widens_with_the_tolerance(self):
        widths = []
        for tolerance in (Q(0), Q(1, 20), Q(1, 5), Q(1, 2)):
            interval = robust_interval(LANGUAGE, BOOK, (), "A", tolerance)
            widths.append(interval.upper - interval.lower)
        self.assertEqual(widths, sorted(widths))

    def test_the_sure_loss_objection_fires_only_above_the_schedule(self):
        below = robust_sure_loss_grounds(LANGUAGE, (), INCOHERENT, Q(1, 3), "g:below")
        above = robust_sure_loss_grounds(LANGUAGE, (), INCOHERENT, Q(1, 5), "g:above")
        self.assertIsNone(below, "4/15 does not exceed a declared 1/3")
        self.assertIsNotNone(above, "4/15 does exceed a declared 1/5")
        self.assertEqual(above.payload["excess"], Q(4, 15))
        self.assertEqual(above.payload["absolute_mass"], Q(1))
        self.assertLessEqual(above.payload["absolute_mass"], Q(1))

    def test_a_coherent_engine_never_grounds_the_objection(self):
        self.assertIsNone(
            robust_sure_loss_grounds(LANGUAGE, (), COHERENT, Q(0), "g:none"))


class NonVacuityTests(unittest.TestCase):
    """Whether a declared tolerance is *working*, and where it stops being so."""

    def test_the_exact_schedule_works_on_the_displayed_book(self):
        self.assertTrue(
            tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2), Q(0)))

    def test_a_maximal_declaration_is_sound_and_useless(self):
        """The audit's finding, as a computation: at tolerance one nothing clears."""
        interval = robust_interval(LANGUAGE, BOOK, (), "A", Q(1))
        self.assertEqual((interval.lower, interval.upper), (Q(0), Q(1)))
        self.assertFalse(
            tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2), Q(1)))

    def test_the_boundary_is_exactly_one_tenth(self):
        """The displayed book's certificate clears until the schedule passes 1/10.

        The lower bound of the robust interval on A is `3/5 - tolerance`, and
        the threshold is `1/2`, so the certificate clears exactly while
        `tolerance <= 1/10`.  The grid brackets that value, and both endpoints
        are then checked directly.
        """
        working, failing = working_boundary(LANGUAGE, BOOK, (), "A", Q(1, 2),
                                            denominator=240)
        self.assertLessEqual(working, Q(1, 10))
        self.assertGreater(failing, Q(1, 10))
        self.assertTrue(
            tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2), Q(1, 10)))
        self.assertFalse(
            tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2),
                                 Q(1, 10) + Q(1, 240)))
        interval = robust_interval(LANGUAGE, BOOK, (), "A", Q(1, 10))
        self.assertEqual(interval.lower, Q(1, 2))

    def test_the_boundary_is_not_the_empty_book_degeneration(self):
        """The crossover is a real one, distinct from the catalogued degeneration.

        At the boundary the interval is a proper subinterval of the unit
        interval and the book is non-empty, so this is not the case where the
        region has collapsed to everything.
        """
        interval = robust_interval(LANGUAGE, BOOK, (), "A", Q(1, 10))
        self.assertNotEqual((interval.lower, interval.upper), (Q(0), Q(1)))
        self.assertTrue(BOOK.endorsements)


class CertificationLayeringTests(unittest.TestCase):
    """T2: who carries a breach, and what follows."""

    def test_within_every_declared_tolerance_nothing_fires(self):
        declaration = ToleranceDeclaration(3, Q(1, 2), Q(1, 4))
        attribution = attribute_breach(declaration, Q(1, 5))
        self.assertEqual(attribution.attributed_to, NO_BREACH)
        self.assertFalse(attribution.tolled)
        self.assertFalse(attribution.chargeable)

    def test_a_breach_of_the_book_s_own_tighter_bound_is_chargeable(self):
        """Witness one way: the book assumed the risk, so the book pays."""
        declaration = ToleranceDeclaration(3, Q(1, 2), Q(1, 4))
        attribution = attribute_breach(declaration, Q(1, 3))
        self.assertEqual(attribution.attributed_to, BOOK_BREACH)
        self.assertTrue(attribution.chargeable)
        self.assertFalse(attribution.tolled,
                         "the book's own bet does not toll the mechanism's clocks")

    def test_a_breach_of_the_engine_s_certified_tolerance_tolls(self):
        """Witness the other way: substrate failure never becomes book liability."""
        declaration = ToleranceDeclaration(3, Q(1, 2), Q(1, 4))
        attribution = attribute_breach(declaration, Q(3, 4))
        self.assertEqual(attribution.attributed_to, ENGINE_BREACH)
        self.assertTrue(attribution.tolled)
        self.assertFalse(attribution.chargeable)

    def test_a_book_tolerance_looser_than_the_engine_s_is_refused(self):
        with self.assertRaises(ValueError):
            attribute_breach(ToleranceDeclaration(0, Q(1, 4), Q(1, 2)), Q(0))

    def test_the_layering_route_supplies_a_working_tolerance(self):
        """The audit's rescue, as a computation.

        The engine certifies the maximal tolerance, under which nothing clears.
        The book declares a tighter working one, which does clear, and carries
        the liability for it.
        """
        engine_certified = Q(1)
        book_declared = Q(1, 20)
        self.assertFalse(tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2),
                                              engine_certified))
        self.assertTrue(tolerance_is_working(LANGUAGE, BOOK, (), "A", Q(1, 2),
                                             book_declared))
        declaration = ToleranceDeclaration(0, engine_certified, book_declared)
        attribution = attribute_breach(declaration, Q(1, 10))
        self.assertEqual(attribution.attributed_to, BOOK_BREACH)
        self.assertTrue(attribution.chargeable)


class ScheduleTests(unittest.TestCase):

    def test_a_schedule_reads_per_date_with_a_declared_default(self):
        schedule = ToleranceSchedule("t:s", {0: Q(1, 2), 1: Q(1, 4)}, Q(1, 8))
        self.assertEqual(schedule.at(0), Q(1, 2))
        self.assertEqual(schedule.at(1), Q(1, 4))
        self.assertEqual(schedule.at(99), Q(1, 8))
        self.assertFalse(schedule.exact)


if __name__ == "__main__":
    unittest.main()
