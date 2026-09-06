import unittest
from itertools import product

from src.authority import geq, lane, profiles
from src.provisional import finalize, grant, recall, recall_possible

GRANTS = ("g1", "g2", "g3")


def subsets(xs):
    for bits in product((0, 1), repeat=len(xs)):
        yield frozenset(x for x, b in zip(xs, bits) if b)


class Provisional(unittest.TestCase):
    def test_state_machine_lanes(self):
        """PR: grant is slow, recall is fast and possible, finalize is slow exactly when
        it makes some grant unoverridable; after that, recall is no longer possible."""
        for live in profiles(GRANTS):
            G, U = live
            for R in subsets(GRANTS):
                if R & G:
                    continue
                prov = grant(live, R)
                self.assertIn(lane(live, prov), ("slow", "fast"))
                if R:
                    self.assertEqual(lane(live, prov), "slow")
                self.assertEqual(lane(prov, recall(prov, R)), "fast")
                self.assertEqual(recall(prov, R), live)
                self.assertTrue(recall_possible(prov, R))
                for Rp in subsets(sorted(R)):
                    fin = finalize(prov, Rp)
                    self.assertEqual(lane(prov, fin), "slow" if Rp else "fast")
                    self.assertTrue(geq(prov, fin))           # provisional ⪰ final
                    self.assertTrue(geq(live, prov))           # floor ⪰ provisional
                    self.assertEqual(recall_possible(fin, R), not Rp)

    def test_recovery_is_one_fast_step_until_finalization(self):
        live = (frozenset({"g1"}), frozenset())
        R = frozenset({"g2", "g3"})
        prov = grant(live, R)
        self.assertEqual(lane(prov, live), "fast")
        fin = finalize(prov, frozenset({"g2"}))
        # in the order, revocation would still be fast — but it is not possible
        self.assertEqual(lane(fin, live), "fast")
        self.assertFalse(recall_possible(fin, R))


if __name__ == "__main__":
    unittest.main()
