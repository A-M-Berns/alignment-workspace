import unittest

from family import systems
from src import cases


class SelfMaintenance(unittest.TestCase):
    def test_union_closed_with_a_greatest_element(self):
        for s, _ in systems(200):
            sm = set(s.self_maintaining_sets())
            for a in sm:
                for b in sm:
                    self.assertIn(a | b, sm)
            self.assertEqual(s.G(s.P), frozenset().union(*sm))

    def test_not_closed_under_intersection(self):
        sm = set(cases.organism.self_maintaining_sets())
        minimal = [x for x in sm if x and not any(y and y < x for y in sm)]
        self.assertEqual(len(minimal), 2)
        self.assertNotIn(minimal[0] & minimal[1], sm)

    def test_necessity_is_transitive(self):
        for s, _ in systems(200):
            S = s.G(s.P)
            nec = s.necessity(S)
            for q in S:
                for p in nec[q]:
                    self.assertLessEqual(nec[p] - {q}, nec[q])

    def test_relevance_is_not_transitive(self):
        failures = 0
        for s, _ in systems(200):
            S = s.G(s.P)
            rel = s.relevance(S)
            failures += any(r != q and r not in rel[q] for q in S for p in rel[q] for r in rel[p])
        self.assertGreater(failures, 0)
