"""§10: the lift is computable by interposition on the declared effect interface, from a
black-box policy, with one principal round-trip per declared effect; and where the
declared interface is incomplete no interposition finds the violation."""

import unittest
from fractions import Fraction as Q

from src.world import paths, declared_mediated, mediated
from src.shop import never, deliberative
from src.lift import lift, approve_all
from src.fixtures import ShopA, ShopE, ShopF, ShopB, pi_A, pi_E, pi_F, pi_B, raw


class EffectiveRepairability(unittest.TestCase):

    def test_lift_reads_only_moves_and_the_declared_interface(self):
        # a black box: the lift never inspects the policy, only its emitted move
        calls = []

        def opaque(h):
            calls.append(h.t)
            return pi_A(h.state, h.t)

        g = ShopA()
        L = lift(opaque, g)
        for tr, _ in paths(g, L, approve_all):
            pass
        self.assertTrue(calls)
        self.assertEqual(declared_mediated(g, L, approve_all), (True, None))

    def test_overhead_is_one_round_trip_per_declared_effect(self):
        for g, pi in ((ShopA(), raw(pi_A)), (ShopE(), raw(pi_E)), (ShopB(), raw(pi_B))):
            L = lift(pi, g)
            for tr, _ in paths(g, L, approve_all):
                proposals = [t for (t, s, a, p, e) in tr.steps
                             if a[1] is not None and a[1][0] == "propose"]
                gated = [t for (t, s, a, p, e) in tr.steps
                         if a[1] is not None and a[1][0] == "gated"]
                self.assertEqual(len(proposals), 1)
                self.assertEqual(len(gated), 1)
                self.assertEqual(gated[0], proposals[0] + 1)

    def test_lift_lands_in_the_declared_corrigible_class(self):
        for g, pi in ((ShopA(), raw(pi_A)), (ShopE(), raw(pi_E)), (ShopB(), raw(pi_B))):
            L = lift(pi, g)
            self.assertFalse(declared_mediated(g, pi, never)[0])
            self.assertTrue(declared_mediated(g, L, approve_all)[0])
            self.assertTrue(mediated(g, L, approve_all, deliberative)[0])

    def test_semantic_repairability_without_effective_repairability(self):
        # F: a semantically corrigible policy exists (the one that never overclocks), but
        # no interposition on the declared alphabet produces it from pi_F: the lift is the
        # identity on pi_F's moves, and the violation is in the physics of a declared-inert
        # move.
        g = ShopF()
        pi = raw(pi_F)
        L = lift(pi, g)
        for (tr, _), (tl, _) in zip(paths(g, pi, never), paths(g, L, never)):
            self.assertEqual([a for (_, _, a, _, _) in tr.steps],
                             [a for (_, _, a, _, _) in tl.steps])
        self.assertFalse(mediated(g, L, never, deliberative)[0])
        safe = raw(lambda s, t: ("work", None))
        self.assertTrue(mediated(g, safe, never, deliberative)[0])


if __name__ == "__main__":
    unittest.main()
