"""The grounded rule, the fixture's bundle, the certificates and the gate — exact rationals."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from inductor import (ALL_TRUE, C, GROUNDS, N0, N1, NE, P1, P2, RHO, TOL, W_AY, X, XA, XAY, Y, Z,
                      Occurrence, active_ids, bankroll_reopened, bundle, certificates, cert_mass,
                      cert_value, compile_at, defeated_at, dominated, enforced_bundle, excess,
                      functional_of, in_region, kappa, occA, occP, occS, occZ, one_step_survivors,
                      row_in_bundle, score, settlement_at, soft_gate, state_bundle, survivors,
                      transport_bound, witness_at, worlds_pinned_by)


class TheGroundedRule(unittest.TestCase):

    def test_strength_leaves_at_the_undercut(self):
        # the repair: occurrence 3 cites 2 and leaves when 2 is undercut, before Y is refuted
        self.assertEqual([o.id for o in survivors(GROUNDS, defeated_at(4), settlement_at(4))], [1, 2, 3, 4])
        self.assertEqual([o.id for o in survivors(GROUNDS, defeated_at(5), settlement_at(5))], [1, 4])
        self.assertEqual([o.id for o in survivors(GROUNDS, defeated_at(9), settlement_at(9))], [1, 4])

    def test_one_step_rule_kept_the_orphan(self):
        # the rebuttal round's rule kept the strength occurrence through [n₀, n_E)
        self.assertEqual([o.id for o in one_step_survivors(GROUNDS, defeated_at(6), settlement_at(6))], [1, 3, 4])
        self.assertEqual([o.id for o in survivors(GROUNDS, defeated_at(6), settlement_at(6))], [1, 4])

    def test_retirement_propagates_without_closure(self):
        # X refuted with no closure pins: the chain P → A → S leaves entirely under the grounded rule
        s = (False, None, None, None, None)
        self.assertEqual([o.id for o in survivors(GROUNDS, set(), s)], [4])
        # the one-step rule kept the last link
        self.assertEqual([o.id for o in one_step_survivors(GROUNDS, set(), s)], [3, 4])

    def test_fixed_point(self):
        for n in range(12):
            S = active_ids(GROUNDS, defeated_at(n), settlement_at(n))
            self.assertEqual({o.id for o in survivors(GROUNDS, defeated_at(n), settlement_at(n))}, S)

    def test_cycle_is_inactive(self):
        a = Occurrence(1, ("applicability", X, XA, F(1, 2)), 2, "p")
        b = Occurrence(2, ("applicability", X, XA, F(1, 2)), 1, "p")
        self.assertEqual(survivors([a, b], set(), (None,) * 5), [])

    def test_dangling_citation_is_inactive(self):
        a = Occurrence(1, ("applicability", X, XA, F(1, 2)), 9, "p")
        self.assertEqual(survivors([a], set(), (None,) * 5), [])


class TheBundle(unittest.TestCase):

    def test_every_date_checks(self):
        for n in range(12):
            self.assertTrue(in_region(state_bundle(n), witness_at(n)))
            self.assertEqual(enforced_bundle(n), state_bundle(n))

    def test_withholding(self):
        bad = [F(0)] * 5
        self.assertEqual(compile_at(state_bundle(0), bad), [])

    def test_phases(self):
        for n in range(12):
            k = 0 if n < N1 else N1 if n < N0 else N0 if n < NE else NE
            self.assertEqual(state_bundle(n), state_bundle(k))

    def test_row_counts(self):
        # 4 warrant rows + 3 coherence rows, then the X pins, then the undercut, then the refutation pins
        self.assertEqual([len(state_bundle(n)) for n in (0, 3, 5, 8)], [7, 9, 7, 11])

    def test_region_excludes_then_lapses(self):
        # at date 4 every region point prices refraining at most 1/3; at date 9 a region point prices it 1
        B4 = state_bundle(4)
        for x in ([F(1), F(3, 4), F(1, 2), F(1, 2), F(3, 4)], [F(1)] * 5, [F(1), F(1), F(2, 3), F(1), F(3, 4)]):
            self.assertTrue(in_region(B4, x))
            self.assertLessEqual(score(P1, 1, x), F(1, 3))
        x9 = [F(1), F(1), F(0), F(0), F(1)]
        self.assertTrue(in_region(state_bundle(9), x9))
        self.assertEqual(score(P1, 1, x9), F(1))


class TheBankroll(unittest.TestCase):

    def test_domination_before_and_after(self):
        for n in range(NE):
            live = worlds_pinned_by(settlement_at(n))
            self.assertTrue(dominated(enforced_bundle(n), ALL_TRUE, live))
        for n in range(NE, 12):
            live = worlds_pinned_by(settlement_at(n))
            self.assertTrue(dominated(enforced_bundle(n), W_AY, live))

    def test_the_slack_world_switches(self):
        # all-true is not live after the refutation, and does not dominate the pin rows there
        self.assertNotIn(ALL_TRUE, worlds_pinned_by(settlement_at(NE)))
        # wAY does not dominate the strength row before the undercut
        live = worlds_pinned_by(settlement_at(4))
        self.assertFalse(dominated(enforced_bundle(4), W_AY, live))

    def test_constant(self):
        self.assertEqual(bankroll_reopened(), F(72))
        self.assertEqual(RHO, max(c / (1 - c) for c in C.values()))


class TheCertificates(unittest.TestCase):

    def test_functionals_values_masses(self):
        c = certificates()
        mults, rows, _ = c["upS"]
        self.assertEqual(functional_of(mults, rows), P1["ell"][1])
        self.assertEqual((cert_value(mults, rows), cert_mass(mults)), (F(1, 3), F(4, 3)))
        mults, rows, _ = c["loS"]
        self.assertEqual(functional_of(mults, rows), [-v for v in P1["ell"][0]])
        self.assertEqual((cert_value(mults, rows), cert_mass(mults)), (F(-1, 2), F(5, 3)))
        mults, rows, _ = c["certZ"]
        self.assertEqual(functional_of(mults, rows), [-v for v in P2["ell"][0]])
        self.assertEqual((cert_value(mults, rows), cert_mass(mults)), (F(-3, 4), F(1)))

    def test_cited_into_the_bundle(self):
        c = certificates()
        B4, B9 = state_bundle(4), state_bundle(9)
        for mults, rows, cites in (c["upS"], c["loS"]):
            for m, row, cite in zip(mults, rows, cites):
                if cite is not None:
                    self.assertTrue(row_in_bundle(B4, cite, row))
        mults, rows, cites = c["certZ"]
        self.assertTrue(row_in_bundle(B9, cites[0], rows[0]))

    def test_exclusion_and_margin_with_tolerance(self):
        c = certificates()
        # exclusion: offset + value ≤ τ; displayed: ≤ τ + mass · tol
        self.assertLessEqual(P1["offset"][1] + cert_value(*c["upS"][:2]), P1["tau"])
        self.assertEqual(P1["offset"][1] + transport_bound(*c["upS"][:2], TOL), F(1, 3) + F(4, 3) * TOL)
        # margin: τ + δ ≤ offset − value − mass · tol
        self.assertLessEqual(P1["tau"] + P1["delta"],
                             P1["offset"][0] - cert_value(*c["loS"][:2]) - cert_mass(c["loS"][0]) * TOL)
        self.assertLessEqual(P2["offset"][1] + cert_value(*c["certZ"][:2]), P2["tau"])
        self.assertLessEqual(P2["tau"] + P2["delta"],
                             P2["offset"][0] - cert_value(*c["certZ"][:2]) - cert_mass(c["certZ"][0]) * TOL)

    def test_transport_is_sharp_in_the_excess(self):
        # a price with every cited row at excess exactly tol realizes value + mass · tol
        mults, rows, _ = certificates()["loS"]
        p = [F(1), F(3, 4) - TOL, F(1, 2) - F(5, 3) * TOL, F(1, 2), F(3, 4)]
        self.assertTrue(all(excess(r, p) == TOL for r in rows))
        self.assertEqual(-p[XAY], transport_bound(mults, rows, TOL))


class TheGate(unittest.TestCase):

    def test_kappa_and_bounds(self):
        k1 = kappa(P1["pref"], P1["adequate"], P1["W"], P1["delta"])
        k2 = kappa(P2["pref"], P2["adequate"], P2["W"], P2["delta"])
        self.assertEqual((k1, k2), (F(12), F(4)))
        self.assertEqual(k1 * F(4, 3) * TOL, F(1, 25))
        self.assertEqual(k2 * F(1) * TOL, F(1, 100))

    def test_gate_reads_the_prices(self):
        conforming = [F(1), F(3, 4), F(1, 2), F(1, 2), F(3, 4)]
        off = [F(1), F(1), F(0), F(0), F(3, 4)]
        g1 = soft_gate([score(P1, q, conforming) for q in range(2)], P1["pref"], P1["tau"], P1["delta"])
        g2 = soft_gate([score(P1, q, off) for q in range(2)], P1["pref"], P1["tau"], P1["delta"])
        self.assertEqual(g1, [F(1), F(0)])
        self.assertEqual(g2, [F(0), F(1)])

    def test_gate_at_the_tolerance(self):
        # at the worst displayed price the certificates allow, the inadequate mass is below the bound
        d = F(4, 3) * TOL
        scores = [F(1, 2) - F(5, 3) * TOL, F(1, 3) + d]
        g = soft_gate(scores, P1["pref"], P1["tau"], P1["delta"])
        self.assertLessEqual(g[1], F(12) * d)
        self.assertGreater(g[1], 0)

    def test_progress_terms(self):
        # modulus² = Γ² Σρ/Σλ with ρ_s = (massCap_s · tol)²; error = Σ T ε; residual = 1 − Σ T
        rho = [(F(4, 3) * TOL) ** 2, (F(1) * TOL) ** 2]
        lam = [F(1), F(1)]
        gamma = F(12)
        modulus_sq = gamma ** 2 * sum(rho) / sum(lam)
        self.assertEqual(modulus_sq, F(144) * (F(1, 90000) + F(1, 160000)) / 2)
        T = {(0, 4): F(1, 2), (1, 9): F(1, 4)}
        error = sum(t * F(1, 10) for t in T.values())
        residual = 1 - sum(T.values())
        self.assertEqual((error, residual), (F(3, 40), F(1, 4)))
        # amplification: Σ_e T e s · D κ_s ≤ Γ λ_s / Σλ
        self.assertLessEqual(F(1, 2) * 12, gamma * F(1, 2))
        self.assertLessEqual(F(1, 4) * 4, gamma * F(1, 2))


if __name__ == "__main__":
    unittest.main()
