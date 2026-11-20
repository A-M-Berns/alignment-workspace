from fractions import Fraction as Q
import unittest

from family import systems
from src import cases
from src.system import functions, influence, split


class JointlyNeededHalves(unittest.TestCase):
    def test_influence_under_the_split(self):
        d = Q(1, 20)
        worst = Q(0)
        seen = 0
        for s, g in systems(120, seed=2):
            S = s.G(s.P)
            if len(S) < 3:
                continue
            q = sorted(S)[g.below(len(S))]
            s2, subs = split(s, q, "all")
            r_old = {x: d for x in S}
            r_old[q] = 1 - (1 - d) ** 2
            r_new = {x: d for x in s2.G(s2.P)}
            I0, I1 = influence(s, r_old), influence(s2, r_new)
            old = [x for x in S if x != q]
            seen += 1
            for a in old:
                for b in old:
                    if a != b:
                        self.assertEqual(I1[a][b], I0[a][b])
                self.assertEqual(I1[subs[0]][a], (1 - d) * I0[q][a])
                gap = abs(I1[a][subs[0]] - I0[a][q])
                self.assertLessEqual(gap, (1 - d) * d)
                worst = max(worst, gap)
        self.assertGreater(seen, 40)
        self.assertEqual(worst, (1 - d) * d)

    def test_ascription_by_relevance_is_not_preserved(self):
        s = cases.split_witness
        self.assertEqual(functions(s), {"p0", "p1", "p2"})
        s2, subs = split(s, "p3", "all")
        self.assertEqual(functions(s2), {"p0", "p1", "p2", *subs})


class RedundantCopies(unittest.TestCase):
    def test_ascription_by_relevance_is_preserved_on_the_family(self):
        for s, g in systems(150, seed=3):
            S = s.G(s.P)
            if not S:
                continue
            q = sorted(S)[g.below(len(S))]
            before = functions(s)
            s2, subs = split(s, q, "any")
            expected = (before - {q}) | set(subs) if q in before else before
            self.assertEqual(functions(s2), expected)
