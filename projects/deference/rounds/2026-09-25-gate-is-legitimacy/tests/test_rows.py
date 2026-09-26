"""Every row of the classification table computed from the definitions, the restart
property, the derived routing closure, forged and replayed approvals, the deviation
boundary, the finite-time window, and the frame-level special case.  `ϖ = 10`, `D = 4`."""

import unittest
from fractions import Fraction as Q

from src.consult import (ROWS, EXPECTED, ROW10_NO_OBLIGATION, ROW13_REPLAYED, DECL, Model, Decl,
                         Frame, Interface, present, canonical, view, deviates, decide_on, eval_at,
                         classify, classify_row, counted, legit_on, table, mismatches, row_evolution,
                         ev_admit, ev_void, ev_two, ev_second, state_admit, initial_state,
                         run_evolution, admit, receipt_errors, gated_value, handling_of,
                         handled_value, bypass_score, lexical_score, grounded_at, mediated_at,
                         transparent_at, ref, v_at, admitted_at, entries_at, WANTS, AGENT, THIRD)

VARPI, D, WINDOW = Q(10), Q(4), Q(0)


class Table(unittest.TestCase):

    def test_every_row_matches_its_expectation(self):
        self.assertEqual(mismatches(want=True), {})
        self.assertEqual(table(want=True), EXPECTED)

    def test_rows_at_the_other_want(self):
        # the classification is of the frame (all wants audited), so the want the branch
        # actually took does not change it, except that row 15's branch is admitted at A
        t = table(want=False)
        for n in ROWS:
            if n != 15:
                self.assertEqual(t[n], EXPECTED[n], n)
        self.assertEqual(t[15], ("tainted", "transparency"))

    def test_row1_is_non_vacuous(self):
        r = legit_on(ROWS[1], ev_admit(False))
        self.assertTrue(all(r[c] for c in ("integrity", "authorship", "robust_openness",
                                           "transparency")))
        self.assertEqual(r["steps"], [((0,), 1), ((0, 1), 2)])
        self.assertEqual(entries_at((ROWS[1], True), 2), [("principal", ("verdict", False))])

    def test_rows_2_to_5_fail_transparency_at_the_first_consultation(self):
        for n in (2, 3, 4, 5):
            M = ROWS[n]
            self.assertEqual(transparent_at(Interface, Frame(M), lambda p, x: ref(M, p, x), 1),
                             AGENT, n)
            self.assertIsNone(transparent_at(Interface, Frame(M), lambda p, x: ref(M, p, x), 2))
            # authorship is fine: the manipulation is a channel failure, not a verdict failure
            self.assertTrue(grounded_at(Interface, Frame(M), (0, 1), 2))

    def test_row6_uniform_convention_counts_and_a_nonconvention_slant_does_not(self):
        self.assertEqual(classify_row(6), ("counts", None))
        slanted_off_convention = Model(DECL, ("frameByWant",), ("own", False))
        self.assertEqual(classify(slanted_off_convention, ev_admit(False)),
                         ("tainted", "transparency"))

    def test_row7_disclosed_shaping_is_a_declared_input(self):
        p = present(DECL, "shapeDisclosed", True)
        self.assertEqual(canonical(DECL, view(DECL, p)), p)
        p = present(DECL, "shapeUndisclosed", True)
        self.assertNotEqual(canonical(DECL, view(DECL, p)), p)

    def test_row9_rubber_stamping_counts_and_follows(self):
        self.assertEqual(classify_row(9), ("counts", None))
        self.assertEqual(v_at((ROWS[9], True), 2), True)
        self.assertEqual(v_at((ROWS[9], False), 2), False)
        # her verdict is mediated by the prefix (the recommendation is in it)
        self.assertTrue(mediated_at(Interface, Frame(ROWS[9]), (0, 1), 2))

    def test_row10_needs_the_declared_obligation(self):
        self.assertEqual(classify_row(10), ("tainted", "transparency"))
        self.assertEqual(classify(ROW10_NO_OBLIGATION, ev_admit(True)), ("counts", None))

    def test_row11_third_party_fails_transparency_for_all_influencers(self):
        M = ROWS[11]
        self.assertEqual(transparent_at(Interface, Frame(M), lambda p, x: ref(M, p, x), 1), THIRD)
        # the agent's own contribution is fine
        self.assertEqual(classify(Model(DECL, ("honest",), ("own", False)), ev_admit(False)),
                         ("counts", None))

    def test_row12_void_handled(self):
        self.assertEqual(classify_row(12), ("void handled", None))
        self.assertFalse(admitted_at((ROWS[12], True), 0))
        self.assertTrue(counted(ROWS[12], ev_void()))
        h = handling_of(True, False, Q(3))
        self.assertEqual(h, ("voidFallback", Q(3)))
        self.assertEqual(handled_value(WINDOW, h), Q(3))

    def test_row13_forged_and_replayed_have_no_receipt(self):
        self.assertEqual(classify_row(13), ("tainted", "integrity(authentication)"))
        self.assertEqual(classify(ROW13_REPLAYED, ev_admit(False, "replayed")),
                         ("tainted", "integrity(freshness)"))
        self.assertIn("authentication", receipt_errors(admit((0, 1), 2, True, "forged").receipt))
        self.assertIn("freshness", receipt_errors(admit((0, 1), 2, True, "replayed").receipt))
        self.assertEqual(receipt_errors(admit((0, 1), 2, True).receipt), [])

    def test_row14_restart(self):
        M = ROWS[14]
        self.assertEqual(classify(M, ev_admit(False)), ("tainted", "transparency"))
        self.assertEqual(classify(M, ev_two(False, False)), ("tainted", "transparency"))
        self.assertEqual(classify(M, ev_second(False, False), start=state_admit(False)),
                         ("counts", None))
        r = legit_on(M, ev_second(False, False), start=state_admit(False))
        self.assertEqual(r["steps"], [((0, 1, 2), 3), ((0, 1, 2, 3), 4)])

    def test_row15_routing_closure_is_derived(self):
        M = ROWS[15]
        self.assertFalse(counted(M, ev_void()))
        honest, fallback = Q(1), Q(3)
        self.assertEqual(gated_value(counted(M, ev_void()), fallback, WINDOW), WINDOW)
        self.assertEqual(gated_value(counted(ROWS[1], ev_admit(False)), honest, WINDOW), honest)
        self.assertLess(gated_value(counted(M, ev_void()), fallback, WINDOW),
                        gated_value(counted(ROWS[1], ev_admit(False)), honest, WINDOW))
        self.assertEqual(handling_of(counted(M, ev_void()), False, fallback), ("tainted",))
        # at want A the agent does not interfere and her response is admitted
        self.assertTrue(admitted_at((M, False), 0))
        self.assertFalse(admitted_at((M, True), 0))


class Gate(unittest.TestCase):

    def test_capture_window_on_the_gate(self):
        for is_counted in (True, False):
            for ord in (Q(0), Q(2), D):
                self.assertLess(bypass_score(VARPI, D), gated_value(is_counted, ord, WINDOW))
                for admitted in (True, False):
                    h = handling_of(is_counted, admitted, ord)
                    self.assertEqual(handled_value(WINDOW, h), gated_value(is_counted, ord, WINDOW))
                    self.assertLess(bypass_score(VARPI, D), handled_value(WINDOW, h))

    def test_finite_time_window_without_a_legitimacy_estimate(self):
        # any expectation g in [0, 1] of the normalized gated quantity keeps
        # window + (D - window) g in [window, D], above bypass
        for g in (Q(0), Q(1, 3), Q(1, 2), Q(1)):
            v = WINDOW + (D - WINDOW) * g
            self.assertTrue(WINDOW <= v <= D)
            self.assertLess(bypass_score(VARPI, D), v)
        # the gated value is such an affine image
        for is_counted in (True, False):
            for ord in (Q(0), Q(3), D):
                g = (ord - WINDOW) / (D - WINDOW) if is_counted else Q(0)
                self.assertTrue(0 <= g <= 1)
                self.assertEqual(gated_value(is_counted, ord, WINDOW), WINDOW + (D - WINDOW) * g)

    def test_deviation_boundary(self):
        finite = {n: deviates(DECL, present(DECL, ROWS[n].policies[0], True))
                  for n in (2, 3, 4, 5, 10, 15)}
        self.assertTrue(all(finite.values()), finite)
        self.assertFalse(deviates(DECL, present(DECL, "shapeUndisclosed", True)))
        self.assertFalse(deviates(DECL, present(DECL, "honest", True)))
        # a deviation counted into n scores below D - ϖ at every ordinary value
        for ord in (Q(0), Q(2), D):
            self.assertLessEqual(lexical_score(VARPI, ord, 1), D - VARPI)
        # row 8 and row 11 are tainted with no self-checkable deviation: asymptotic
        self.assertEqual(classify_row(8), ("tainted", "transparency"))
        self.assertEqual(classify_row(11), ("tainted", "transparency"))
        # without the obligation the disclosure deviation is not a deviation and row 10 counts
        self.assertFalse(deviates(ROW10_NO_OBLIGATION.decl,
                                  present(ROW10_NO_OBLIGATION.decl, "selectiveDisclosure", True)))


class Interfaces(unittest.TestCase):

    def test_grounding_implies_extensional(self):
        M = ROWS[9]
        sel = lambda parts: {AGENT: parts[AGENT]}   # grounds: the agent's entries only
        self.assertTrue(grounded_at(Interface, Frame(M), (0, 1), 2, selection=sel))
        self.assertTrue(mediated_at(Interface, Frame(M), (0, 1), 2))
        # the verdict-indexed form does not: equal prefixes may cite different grounds
        # (recorded in the report; the selection form is what is stated)

    def test_evaluator_is_a_state(self):
        self.assertEqual(eval_at("follow", ["present", "respond", ("amend", None, ("own", True)),
                                            "present"]), ("own", True))
        self.assertEqual(eval_at("follow", ["present", "respond", ("delegate", None),
                                            ("revoke", None), ("reserve", None)]), "follow")

    def test_one_clock(self):
        _, pre, _ = run_evolution(initial_state(), ev_two(False, True))
        self.assertEqual([e for (_, e) in pre], [1, 2, 3, 4])
        self.assertEqual([h for (h, _) in pre], [(0,), (0, 1), (0, 1, 2), (0, 1, 2, 3)])
        self.assertEqual(Interface.at_history((ROWS[1], True), (0, 1, 2)),
                         entries_at((ROWS[1], True), 1) + entries_at((ROWS[1], True), 2))

    def test_frame_level_is_the_special_case(self):
        # a frame-level segment over the trivial interface: the whole trace re-entered at
        # every event, all agent-sourced; transparency per step is the landed Realizes
        class Trivial:
            agent, principal = True, False

            @staticmethod
            def entries_at(r, e):
                return [(True, r)]

            @staticmethod
            def sourced(p, l):
                return [x for (q, x) in l if q == p]

            @classmethod
            def at_history(cls, r, h):
                return [x for e in h for x in cls.entries_at(r, e)]

            @classmethod
            def parts(cls, r, h):
                return {p: cls.sourced(p, cls.at_history(r, h)) for p in (True, False)}

        class Landed:
            D = WANTS
            beta = staticmethod(lambda q, z=None: q)
            x = staticmethod(lambda w, e=None: w)          # declared inputs: the want
            R = staticmethod(lambda w: ("trace", w))
            V = staticmethod(lambda w, e=None: w)          # payload: the want

        kappa = lambda p, x: [("trace", x)] if p else []
        for (h, e) in [((0,), 1), ((0, 1), 2)]:
            self.assertTrue(grounded_at(Trivial, Landed, h, e))
            self.assertIsNone(_transparent_all(Trivial, Landed, kappa, e))
        # with an empty pre-history the lifted authorship demands a constant payload
        self.assertFalse(grounded_at(Trivial, Landed, (), 1))


def _transparent_all(I, F, kappa, e):
    for p in (True, False):
        if p == I.principal:
            continue
        for q in F.D:
            w = F.beta(q)
            if I.sourced(p, I.entries_at(F.R(w), e)) != kappa(p, F.x(w, e)):
                return p
    return None


if __name__ == "__main__":
    unittest.main()
