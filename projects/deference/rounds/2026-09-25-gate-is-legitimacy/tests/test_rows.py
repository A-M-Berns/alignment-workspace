"""Every row of the classification table (1–20) computed from the definitions, the
restart property, the derived routing closure, forged and replayed approvals, the
pool-not-selection default, relational authorship and the tie-break lemma, the deviation
boundary, the finite-time window, the frame-level special case, and the two class theorems
swept over the model class.  `ϖ = 10`, `D = 4`."""

import unittest
from fractions import Fraction as Q

from src.consult import (ROWS, EXPECTED, ROW17_OFF_RULE, ROW13_REPLAYED, FOLLOW_UNTRUSTED, DECL,
                         DECL_RECENT, POOL, Model, Decl, Frame, Interface, present, canonical,
                         view, deviates, decide_on, eval_at, classify, classify_row, counted,
                         legit_on, table, mismatches, ev_admit, ev_void, ev_two, ev_second,
                         state_admit, initial_state, run_evolution, admit, receipt_errors,
                         gated_value, handling_of, handled_value, bypass_score, lexical_score,
                         grounded_at, mediated_at, licensed_at, licensed, licensed_set,
                         singleton_license, transparent_at, tiebreak, ref, v_at, admitted_at,
                         entries_at, apply_rule, misleads, class_models, class_taint_holds,
                         class_conform_holds, WANTS, AGENT, PRINCIPAL, THIRD)

VARPI, D, WINDOW = Q(10), Q(4), Q(0)


class Table(unittest.TestCase):

    def test_every_row_matches_its_expectation(self):
        self.assertEqual(mismatches(want=True), {})
        self.assertEqual(table(want=True), EXPECTED)

    def test_rows_at_the_other_want(self):
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
            lic = lambda g, v, M=M: licensed(M, g, v)
            self.assertTrue(licensed_at(Interface, Frame(M), lic, (0, 1), 2))

    def test_row6_uniform_convention_counts_and_a_nonconvention_slant_does_not(self):
        self.assertEqual(classify_row(6), ("counts", None))
        self.assertEqual(classify(Model(DECL, ("frameByWant",), ("own", False)), ev_admit(False)),
                         ("tainted", "transparency"))

    def test_row7_disclosed_shaping_is_a_declared_input(self):
        p = present(DECL, "shapeDisclosed", True)
        self.assertEqual(canonical(DECL, view(p)), p)
        p = present(DECL, "shapeUndisclosed", True)
        self.assertNotEqual(canonical(DECL, view(p)), p)

    def test_row9_rubber_stamping_counts_and_follows(self):
        self.assertEqual(classify_row(9), ("counts", None))
        self.assertEqual(v_at((ROWS[9], True), 2), True)
        self.assertEqual(v_at((ROWS[9], False), 2), False)
        # the followed recommendation is licensed because trust is among her grounds
        g = Interface.parts((ROWS[9], True), (0, 1))
        self.assertIn(("trust",), g[PRINCIPAL])
        self.assertTrue(licensed(ROWS[9], g, True))
        self.assertFalse(licensed(ROWS[9], g, False))

    def test_follow_without_trust_fails_authorship(self):
        self.assertEqual(classify(FOLLOW_UNTRUSTED, ev_admit(True)), ("tainted", "authorship"))
        g = Interface.parts((FOLLOW_UNTRUSTED, True), (0, 1))
        self.assertEqual(licensed_set(FOLLOW_UNTRUSTED, g), {None})

    def test_row10_selective_disclosure_is_tainted_under_the_pool_default(self):
        self.assertEqual(classify_row(10), ("tainted", "transparency"))
        self.assertTrue(deviates(DECL, present(DECL, "selectiveDisclosure", True)))

    def test_row11_third_party_fails_transparency_for_all_influencers(self):
        M = ROWS[11]
        self.assertEqual(transparent_at(Interface, Frame(M), lambda p, x: ref(M, p, x), 1), THIRD)
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
        self.assertTrue(admitted_at((M, False), 0))
        self.assertFalse(admitted_at((M, True), 0))

    def test_row16_pool_not_selection(self):
        # the pool is declared; the selection is reference-fixed unless a rule is declared
        self.assertEqual(classify_row(16), ("tainted", "transparency"))
        self.assertTrue(deviates(DECL, present(DECL, "selectiveDisclosure", True)))
        self.assertEqual(canonical(DECL, view(present(DECL, "honest", True))).disclosure, POOL)

    def test_row17_declared_selection_rule(self):
        self.assertEqual(classify_row(17), ("counts", None))
        self.assertEqual(present(DECL_RECENT, "honest", True).disclosure, apply_rule(("recent", 2), POOL))
        # selection by anything else under the rule is a deviation and tainted
        self.assertEqual(classify(ROW17_OFF_RULE, ev_admit(False)), ("tainted", "transparency"))
        self.assertTrue(deviates(DECL_RECENT, present(DECL_RECENT, "selectiveDisclosure", True)))

    def test_row18_permissive_choice(self):
        M = ROWS[18]
        self.assertEqual(classify_row(18), ("counts", None))
        g = Interface.parts((M, False), (0, 1))
        self.assertEqual(licensed_set(M, g), {None, False, True})
        self.assertEqual(v_at((M, False), 2), True)
        # relational authorship holds; the extensional form holds too (her pick is constant)
        lic = lambda g, v: licensed(M, g, v)
        self.assertTrue(licensed_at(Interface, Frame(M), lic, (0, 1), 2))
        self.assertTrue(mediated_at(Interface, Frame(M), (0, 1), 2))

    def test_row19_nudge_decides_the_tie_break(self):
        M = ROWS[19]
        self.assertEqual(classify_row(19), ("tainted", "transparency"))
        lic = lambda g, v: licensed(M, g, v)
        # both verdicts licensed, authorship holds, verdicts differ with equal declared inputs
        self.assertTrue(licensed_at(Interface, Frame(M), lic, (0, 1), 2))
        self.assertNotEqual(v_at((M, False), 2), v_at((M, True), 2))
        F = Frame(M)
        self.assertEqual(F.x(F.beta(False), 1), F.x(F.beta(True), 1))
        self.assertTrue(tiebreak(Interface, F, lambda p, x: ref(M, p, x), AGENT, False, True, 1))

    def test_row20_false_recommendation_counts_and_is_flagged(self):
        M = ROWS[20]
        self.assertEqual(classify_row(20), ("counts", None))
        self.assertTrue(misleads(M, True))
        self.assertFalse(misleads(M, False))


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
        for g in (Q(0), Q(1, 3), Q(1, 2), Q(1)):
            v = WINDOW + (D - WINDOW) * g
            self.assertTrue(WINDOW <= v <= D)
            self.assertLess(bypass_score(VARPI, D), v)
        for is_counted in (True, False):
            for ord in (Q(0), Q(3), D):
                g = (ord - WINDOW) / (D - WINDOW) if is_counted else Q(0)
                self.assertTrue(0 <= g <= 1)
                self.assertEqual(gated_value(is_counted, ord, WINDOW), WINDOW + (D - WINDOW) * g)

    def test_deviation_boundary(self):
        finite = {n: deviates(ROWS[n].decl, present(ROWS[n].decl, ROWS[n].policies[0], True))
                  for n in (2, 3, 4, 5, 10, 15, 16, 19)}
        self.assertTrue(all(finite.values()), finite)
        self.assertTrue(deviates(DECL_RECENT, present(DECL_RECENT, "selectiveDisclosure", True)))
        self.assertFalse(deviates(DECL, present(DECL, "shapeUndisclosed", True)))
        self.assertFalse(deviates(DECL, present(DECL, "honest", True)))
        for ord in (Q(0), Q(2), D):
            self.assertLessEqual(lexical_score(VARPI, ord, 1), D - VARPI)
        # rows 8 and 11 are tainted with no self-checkable deviation: asymptotic
        self.assertEqual(classify_row(8), ("tainted", "transparency"))
        self.assertEqual(classify_row(11), ("tainted", "transparency"))


class Authorship(unittest.TestCase):

    def test_grounding_implies_extensional_and_singleton_licenses_are_extensional(self):
        M = ROWS[9]
        sel = lambda parts: {AGENT: parts[AGENT]}
        self.assertTrue(grounded_at(Interface, Frame(M), (0, 1), 2, selection=sel))
        self.assertTrue(mediated_at(Interface, Frame(M), (0, 1), 2))
        # the singleton license of the value the grounds determine
        ell = lambda g: (next(x[1].recommend for x in g[AGENT] if x[0] == "pres")
                         if any(x[0] == "pres" for x in g[AGENT]) else None)
        self.assertTrue(licensed_at(Interface, Frame(M), singleton_license(ell), (0, 1), 2))
        # a permissive license is strictly weaker: row 18 is licensed but no singleton of the
        # agent's grounds alone captures a free choice made against the recommendation
        M18 = Model(DECL, ("honest",), ("free", False))
        lic = lambda g, v: licensed(M18, g, v)
        self.assertTrue(licensed_at(Interface, Frame(M18), lic, (0, 1), 2))
        self.assertFalse(licensed_at(Interface, Frame(M18), singleton_license(ell), (0, 1), 2))

    def test_evaluator_is_a_state(self):
        self.assertEqual(eval_at("follow", ["present", "respond", ("amend", None, ("own", True)),
                                            "present"]), ("own", True))
        self.assertEqual(eval_at("follow", ["present", "respond", ("delegate", None),
                                            ("revoke", None), ("reserve", None)]), "follow")

    def test_one_clock(self):
        _, pre, _ = run_evolution(initial_state(), ev_two(False, True))
        self.assertEqual([e for (_, e) in pre], [1, 2, 3, 4])
        self.assertEqual([h for (h, _) in pre], [(0,), (0, 1), (0, 1, 2), (0, 1, 2, 3)])
        self.assertEqual(Interface.at_history((ROWS[9], True), (0, 1, 2)),
                         entries_at((ROWS[9], True), 0) + entries_at((ROWS[9], True), 1)
                         + entries_at((ROWS[9], True), 2))

    def test_frame_level_is_the_special_case(self):
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
            x = staticmethod(lambda w, e=None: w)
            R = staticmethod(lambda w: ("trace", w))
            V = staticmethod(lambda w, e=None: w)

        kappa = lambda p, x: [("trace", x)] if p else []
        lift_lic = lambda g, v: any(("trace", q) in g[True] and Landed.V(q) == v for q in WANTS)
        for (h, e) in [((0,), 1), ((0, 1), 2)]:
            self.assertTrue(grounded_at(Trivial, Landed, h, e))
            self.assertTrue(licensed_at(Trivial, Landed, lift_lic, h, e))
            self.assertIsNone(_transparent_all(Trivial, Landed, kappa, e))
        self.assertFalse(grounded_at(Trivial, Landed, (), 1))


class ClassTheorems(unittest.TestCase):

    def test_selection_dependence_taints_over_the_class(self):
        models = list(class_models())
        self.assertGreater(len(models), 400)
        failing = [M for M in models if not class_taint_holds(M)]
        self.assertEqual(failing, [])
        # and the hypothesis is not vacuous
        self.assertTrue(any(any(deviates(M.decl, present(M.decl, M.policies[0], w)) for w in WANTS)
                            for M in models))

    def test_protocol_conformance_counts_over_the_class(self):
        models = list(class_models())
        failing = [M for M in models if not class_conform_holds(M)]
        self.assertEqual(failing, [])
        conforming = [M for M in models
                      if all(not deviates(M.decl, present(M.decl, M.policies[0], w)) for w in WANTS)
                      and M.third is None and not M.impaired]
        self.assertGreater(len(conforming), 20)

    def test_conformance_hypotheses_are_each_needed(self):
        base = dict(decl=DECL, policies=("honest",), prog=("own", False))
        self.assertTrue(counted(Model(**base), ev_admit(False)))
        self.assertFalse(counted(Model(**dict(base, third=True)), ev_admit(False)))
        self.assertFalse(counted(Model(**dict(base, policies=("shapeUndisclosed",))), ev_admit(False)))
        self.assertFalse(counted(Model(**dict(base, prog="follow")), ev_admit(False)))
        self.assertTrue(counted(Model(**dict(base, prog="follow", trusts=True)), ev_admit(False)))


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
