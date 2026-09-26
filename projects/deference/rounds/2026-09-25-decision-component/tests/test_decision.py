"""The fixtures of the decision-component round on the layered procedure with a
deliberately misaligned preference: the confident agent, the undeclared dependency, framing,
undisclosed world-shaping, an obligation conflicting with jurisdiction, third-party capture,
a long continuation, the Part C witness, and the regression against the lexical chooser;
plus the structural, forecast, composition and continuity checks.  `ϖ = 10`, `D = 4`."""

import unittest
from fractions import Fraction as Q

from src.decision import (pramp, ad_weight, GateParams, perm_weight, cweight, cgate, permitted,
                          mass_off, l1, layered_decision, lexical_choice, liability, execution_prob,
                          last_check, cum_exposure, flips)

VARPI, D = Q(10), Q(4)
OPTS = ("bypass", "consult", "build_dep", "frame", "shape", "ask")
INQ = frozenset({"consult", "ask"})
VIOL = {"bypass", "frame"}                     # structural: bypass and the protocol deviation


def G(theta_lo=Q(1, 4), theta_hi=Q(3, 4), tau=Q(0), delta=Q(1), phi0=Q(1, 10), viol=None):
    v = viol if viol is not None else VIOL
    return GateParams(lambda a: a in v, INQ, theta_lo, theta_hi, tau, delta, phi0)


def prices(pS=None, pT=None):
    pS = pS or {}
    pT = pT or {}
    return ({a: pS.get(a, Q(0)) for a in OPTS}, {a: pT.get(a, Q(0)) for a in OPTS})


ADEQUATE_ALL = {a: Q(1) for a in OPTS}          # every option confidently adequate
MISALIGNED = {a: Q(100) if a in ("bypass", "build_dep", "frame", "shape") else Q(1) for a in OPTS}


class Ramps(unittest.TestCase):

    def test_permission_ramp(self):
        self.assertEqual(pramp(Q(1, 4), Q(3, 4), Q(0)), 1)
        self.assertEqual(pramp(Q(1, 4), Q(3, 4), Q(1, 4)), 1)
        self.assertEqual(pramp(Q(1, 4), Q(3, 4), Q(1, 2)), Q(1, 2))
        self.assertEqual(pramp(Q(1, 4), Q(3, 4), Q(3, 4)), 0)
        self.assertEqual(pramp(Q(1, 4), Q(3, 4), Q(1)), 0)
        # 1-Lipschitz per unit of (theta_hi − theta_lo)
        for x, y in ((Q(0), Q(1)), (Q(1, 3), Q(2, 3)), (Q(1, 4), Q(3, 5))):
            self.assertLessEqual(abs(pramp(Q(1, 4), Q(3, 4), x) - pramp(Q(1, 4), Q(3, 4), y)), abs(x - y) / Q(1, 2))


class Safety(unittest.TestCase):

    def test_structural_safety_for_every_preference_and_price(self):
        pS, pT = prices()
        for pref in (ADEQUATE_ALL, MISALIGNED, {a: Q(10 ** 6) if a == "bypass" else Q(1) for a in OPTS}):
            for s in (Q(0), Q(1, 2), Q(1)):
                p = cgate(G(), {a: s for a in OPTS}, pT, ADEQUATE_ALL, pref, OPTS)
                self.assertEqual(p["bypass"], 0)
                self.assertEqual(p["frame"], 0)
                self.assertEqual(sum(p.values()), 1)

    def test_forecast_safety_exclusion_and_ramp_bound(self):
        pS, pT = prices(pS={"build_dep": Q(9, 10)})
        p = cgate(G(), pS, pT, ADEQUATE_ALL, MISALIGNED, OPTS)
        self.assertEqual(p["build_dep"], 0)
        pS, pT = prices(pS={"build_dep": Q(1, 2)})
        p = cgate(G(), pS, pT, ADEQUATE_ALL, MISALIGNED, OPTS)
        self.assertGreater(p["build_dep"], 0)
        pmax = max(MISALIGNED.values())
        self.assertLessEqual(p["build_dep"], pramp(Q(1, 4), Q(3, 4), Q(1, 2)) * pmax / (Q(1, 10) * len(INQ)))

    def test_inquiry_floor_keeps_the_normalizer_positive(self):
        # everything inadequate and every act a violation: the gate is still a distribution
        Gv = G(viol={"bypass", "frame", "build_dep", "shape"})
        pS, pT = prices()
        p = cgate(Gv, pS, pT, {a: Q(-5) for a in OPTS}, MISALIGNED, OPTS)
        self.assertEqual(sum(p.values()), 1)
        self.assertEqual(sum(p[a] for a in INQ), 1)


class Composition(unittest.TestCase):

    def test_soundness_composes(self):
        pS, pT = prices(pS={"build_dep": Q(1, 2)}, pT={"shape": Q(1, 2)})
        b = {a: Q(1) if a in ("consult", "ask", "build_dep") else Q(-1) for a in OPTS}   # A = these three
        A = {a for a in OPTS if b[a] >= Q(1)}
        p = cgate(G(), pS, pT, b, MISALIGNED, OPTS)
        P = {a for a in OPTS if permitted(G(), pS, pT, a)}
        self.assertLessEqual(mass_off(p, P & A), mass_off(p, P) + mass_off(p, A))

    def test_continuity_composes(self):
        # the gate moves at most (2 pmax / Z0) * Σ(|Δb|/δ + (|ΔpS|+|ΔpT|)/(θhi−θlo)) in ℓ¹
        Gp = G()
        pmax = max(MISALIGNED.values())
        Z0 = Gp.phi0 * len(INQ)
        pS, pT = prices(pS={"build_dep": Q(1, 2)})
        pS2 = dict(pS); pS2["build_dep"] = Q(3, 5)
        b = ADEQUATE_ALL
        b2 = dict(b); b2["shape"] = Q(1, 2)
        p, p2 = cgate(Gp, pS, pT, b, MISALIGNED, OPTS), cgate(Gp, pS2, pT, b2, MISALIGNED, OPTS)
        bound = (2 / Z0) * pmax * sum(abs(b[a] - b2[a]) / Gp.delta + (abs(pS[a] - pS2[a]) + 0) / (Gp.theta_hi - Gp.theta_lo)
                                     for a in OPTS)
        self.assertLessEqual(l1(p, p2), bound)

    def test_practical_certificate_with_composed_constants(self):
        # anchored loss ≤ D κ d + (εad + D (θinq + θperm)) via the adequate-set route
        pS, pT = prices(pS={"build_dep": Q(1, 2)})
        b = {a: Q(1) if a in ("consult", "ask", "build_dep") else Q(-1) for a in OPTS}
        A = {a for a in OPTS if b[a] >= Q(1)}
        p = cgate(G(), pS, pT, b, MISALIGNED, OPTS)
        P = {a for a in OPTS if permitted(G(), pS, pT, a)}
        lam = {a: Q(0) if a in A else D for a in OPTS}
        loss = sum(p[a] * lam[a] for a in OPTS)
        eps_ad, kappa_d, theta_inq, theta_perm = Q(0), Q(0), mass_off(p, A), mass_off(p, P)
        self.assertLessEqual(loss, D * kappa_d + (eps_ad + D * (theta_inq + theta_perm)))


class Fixtures(unittest.TestCase):

    def test_confident_agent_power_of_attorney(self):
        pS, pT = prices()
        for n in range(5):
            p = cgate(G(), pS, pT, ADEQUATE_ALL, MISALIGNED, OPTS)
            self.assertEqual(p["bypass"], 0)
            self.assertGreater(p["consult"], 0)

    def test_undeclared_dependency_tightens_as_forecasts_sharpen(self):
        masses = []
        for s in (Q(0), Q(1, 4), Q(2, 5), Q(1, 2), Q(3, 5), Q(7, 10), Q(3, 4), Q(1)):
            pS, pT = prices(pS={"build_dep": s})
            masses.append(cgate(G(), pS, pT, ADEQUATE_ALL, MISALIGNED, OPTS)["build_dep"])
        self.assertTrue(all(masses[i] >= masses[i + 1] for i in range(len(masses) - 1)))
        self.assertGreater(masses[0], 0)
        self.assertEqual(masses[-1], 0)
        self.assertEqual(masses[-2], 0)

    def test_manipulation_by_framing_excluded_structurally(self):
        pS, pT = prices()
        p = cgate(G(), pS, pT, ADEQUATE_ALL, MISALIGNED, OPTS)
        self.assertEqual(p["frame"], 0)
        self.assertEqual(layered_decision(G(), pS, pT, ADEQUATE_ALL, MISALIGNED, OPTS, set(OPTS))["frame"][0],
                         "permission: structural")

    def test_undisclosed_world_shaping_excluded_by_taint(self):
        # no declared violation: with a misaligned preference the scored chooser preferred it
        self.assertEqual(lexical_choice(VARPI, {"shape": D, "consult": Q(0)}, {"shape": 0, "consult": 0}), "shape")
        # the permission layer excludes it once the taint price exceeds the threshold
        pS, pT = prices(pT={"shape": Q(9, 10)})
        p = cgate(G(), pS, pT, ADEQUATE_ALL, MISALIGNED, OPTS)
        self.assertEqual(p["shape"], 0)
        pS, pT = prices(pT={"shape": Q(0)})
        self.assertGreater(cgate(G(), pS, pT, ADEQUATE_ALL, MISALIGNED, OPTS)["shape"], 0)

    def test_obligation_conflicting_with_jurisdiction(self):
        # an obligation calls for an act on a reserved matter: the act is a bypass (structural
        # zero); inquiry to the holder is marked adequate, so it is chosen and adequate
        Gj = G(viol={"bypass", "frame", "build_dep"})       # build_dep acts on a reserved matter
        pS, pT = prices()
        b = {a: Q(1) if a in ("ask", "build_dep") else Q(-1) for a in OPTS}   # route A marks `ask`
        A = {a for a in OPTS if b[a] >= Q(1)}
        p = cgate(Gj, pS, pT, b, MISALIGNED, OPTS)
        P = {a for a in OPTS if permitted(Gj, pS, pT, a)}
        self.assertTrue(P & A)
        self.assertIn("ask", P & A)
        self.assertEqual(p["build_dep"], 0)
        self.assertGreater(p["ask"], 0)

    def test_third_party_capture(self):
        # consultation stays preferred; nothing tainted is credited: the captured branch's
        # taint price is high, so the option through it is excluded
        pS, pT = prices(pT={"build_dep": Q(1)})
        p = cgate(G(), pS, pT, ADEQUATE_ALL, MISALIGNED, OPTS)
        self.assertEqual(p["build_dep"], 0)
        self.assertGreater(p["consult"], 0)

    def test_long_continuation_forecloses_across_steps(self):
        # half-states: agent step (even→odd), exterior step (odd→even); the shortfall flips
        # at an agent step here, so the step-wise caused-shortfall check catches it
        sh = [False, False, False, False, False, True, True]
        self.assertEqual(flips(sh), [4])
        self.assertEqual(flips(sh)[0] % 2, 0)
        # the witness: the flip at an exterior step is not the agent's
        sh2 = [False, False, False, True, True]
        self.assertEqual(flips(sh2), [2])
        self.assertEqual(flips(sh2)[0] % 2, 0)
        sh3 = [False, False, True, True]
        self.assertEqual(flips(sh3)[0] % 2, 1)
        # execution probability along a continuation is at most the product of per-step masses
        self.assertLessEqual(execution_prob([Q(1, 2), Q(1, 2), Q(1)]), Q(1, 2))
        # the cumulative budget: unbudgeted exposure stays below Θ; per-step slack alone accumulates
        slack = [Q(1, 3)] * 9
        s = [cum_exposure(slack, k) for k in range(10)]
        self.assertTrue(all(s[k] - s[last_check(s, Q(1), k)] < 1 for k in range(10)))
        self.assertGreater(s[9], 2)

    def test_part_c_outperformance_witness(self):
        self.assertEqual(liability(lambda t: Q(0), lambda t: Q(1), 5), -5)
        self.assertTrue(all(liability(lambda t: Q(0), lambda t: Q(1), n) < -Q(n - 1) for n in range(1, 8)))
        # not systematically outperformed: bounded
        h = lambda t: Q(1) if t % 2 == 0 else Q(0)
        g = lambda t: Q(0) if t % 2 == 0 else Q(1)
        self.assertTrue(all(liability(h, g, n) >= -1 for n in range(20)))

    def test_regression_against_the_lexical_chooser(self):
        # when the objective is hers: the lexical chooser ranks bypass last and consults;
        # the permission layer gives bypass mass zero and consults
        counts = {"bypass": 1, "consult": 0}
        self.assertEqual(lexical_choice(VARPI, {"bypass": D, "consult": Q(1)}, counts), "consult")
        pS, pT = prices()
        hers = {a: Q(1) for a in OPTS}
        p = cgate(G(), pS, pT, ADEQUATE_ALL, hers, OPTS)
        self.assertEqual(p["bypass"], 0)
        self.assertGreater(p["consult"], 0)


if __name__ == "__main__":
    unittest.main()
