import unittest
from itertools import product

from src.authority import TOP, geq, join, lane, profiles, tolerant_geq, uncovered


class Preorder(unittest.TestCase):
    def test_preorder_and_top(self):
        P = profiles()
        self.assertEqual(len(P), 9)
        for a in P:
            self.assertTrue(geq(a, a))
            self.assertTrue(geq(TOP, a))  # shutdown is maximal, not a loss
        for a, b, c in product(P, repeat=3):
            if geq(b, a) and geq(c, b):
                self.assertTrue(geq(c, a))

    def test_incomparable_pairs_exist(self):
        a = (frozenset({"g1"}), frozenset({"g1"}))   # narrow scope, uncovered
        b = (frozenset({"g1", "g2"}), frozenset())   # wide scope, fully covered
        self.assertEqual(lane(a, b), "mixed")
        self.assertEqual(lane(b, a), "mixed")

    def test_fast_lane_closed_under_composition(self):
        """L2: a chain of fast-lane transitions is fast, so no slow transition can be
        laundered as a sequence of fast ones."""
        P = profiles()
        for a, b, c in product(P, repeat=3):
            if lane(a, b) == "fast" and lane(b, c) == "fast":
                self.assertEqual(lane(a, c), "fast")

    def test_salami_countermodel(self):
        """CM-L: a tolerance letting one grant's coverage lapse per step is laundered by
        composition — every step is tolerably fast, the composite is total loss."""
        grants = ("g1", "g2", "g3")
        G = frozenset(grants)
        chain = [(G, frozenset()), (G, frozenset({"g1"})), (G, frozenset({"g1", "g2"})),
                 (G, G)]
        for x, y in zip(chain, chain[1:]):
            self.assertTrue(tolerant_geq(y, x))
            self.assertFalse(geq(y, x))          # the exact relation rejects each step
        self.assertFalse(tolerant_geq(chain[-1], chain[0]))
        self.assertEqual(uncovered(chain[-1]), G)

    def test_lattice_factorization(self):
        """L3: every transition factors as fast (a -> a ⊔ b) then slow (a ⊔ b -> b), and
        the join is the least such midpoint, so the slow leg is the minimal amendment."""
        P = profiles()
        for a, b in product(P, repeat=2):
            m = join(a, b)
            self.assertIn(m, P)
            self.assertEqual(lane(a, m), "fast")
            self.assertIn(lane(m, b), ("fast", "slow"))
            for m2 in P:
                if geq(m2, a) and geq(m2, b):
                    self.assertTrue(geq(m2, m))

    def test_join_required_for_canonical_split(self):
        """CM-J: in a preorder with two incomparable minimal upper bounds there is no
        least fast leg; the amendment content depends on the midpoint chosen."""
        order = {("a", "m1"), ("a", "m2"), ("b", "m1"), ("b", "m2"),
                 ("a", "top"), ("b", "top"), ("m1", "top"), ("m2", "top")}
        elems = ("a", "b", "m1", "m2", "top")

        def ge(y, x):
            return x == y or (x, y) in order
        ubs = [m for m in elems if ge(m, "a") and ge(m, "b")]
        minimal = [m for m in ubs if not any(m2 != m and ge(m, m2) for m2 in ubs)]
        self.assertEqual(sorted(minimal), ["m1", "m2"])


if __name__ == "__main__":
    unittest.main()
