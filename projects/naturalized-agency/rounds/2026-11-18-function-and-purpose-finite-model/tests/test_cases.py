from fractions import Fraction as Q
import unittest

from src import cases
from src.system import functions, influence, merge


class Ascriptions(unittest.TestCase):
    def test_vortex_with_air_given_has_no_function(self):
        self.assertEqual(functions(cases.vortex_air_given), set())

    def test_vortex_with_parcels_as_parts_is_ascribed_functions(self):
        self.assertEqual(functions(cases.vortex_and_parcels), set(cases.vortex_and_parcels.P))

    def test_catalyst_and_membrane(self):
        self.assertEqual(functions(cases.catalyst_membrane), {"Cat", "Mem", "RawIn"})

    def test_organism(self):
        self.assertEqual(functions(cases.organism), set(cases.organism.P))
        S = cases.organism.G(cases.organism.P)
        nec = cases.organism.necessity(S)
        self.assertEqual(len(nec["Heart"]), 8)
        self.assertEqual(nec["Kidney1"], set())

    def test_thermostat_kept_by_the_person_is_like_an_organ(self):
        self.assertEqual(functions(cases.household), set(cases.household.P))

    def test_thermostat_supplied_from_outside_is_useful_only(self):
        s = cases.household_supplied
        self.assertNotIn("Thermostat", functions(s))
        self.assertTrue(s.relevance(s.G(s.P))["Thermostat"])

    def test_lab(self):
        s = cases.lab
        self.assertEqual(functions(s), set(s.P))
        self.assertEqual(s.G(s.P - {"Staff"}), frozenset())

    def test_lab_whose_model_operates_itself(self):
        s = cases.lab_self_operating
        self.assertEqual(s.G(s.P - {"Staff"}), frozenset({"Model", "Compute", "Revenue"}))
        self.assertEqual(functions(s), {"Model", "Compute", "Revenue"})

    def test_merging_every_part_removes_every_function(self):
        m = cases.organism
        names = sorted(m.P)
        acc = names[0]
        for i, x in enumerate(names[1:]):
            m = merge(m, acc, x, f"m{i}")
            acc = f"m{i}"
        self.assertEqual(len(m.P), 1)
        self.assertEqual(functions(m), set())


class Influence(unittest.TestCase):
    def test_organism_graded(self):
        I = influence(cases.organism, {x: Q(1, 10) for x in cases.organism.P})
        self.assertEqual(I["Heart"]["Lungs"], Q(52612659, 100000000))
        self.assertEqual(I["Kidney1"]["Lungs"], Q(4782969, 100000000))

    def test_interchangeable_parcels(self):
        prev = None
        for n in (4, 6, 8):
            s = cases.parcels(n)
            self.assertEqual(len(s.kinds(s.G(s.P))), 1)
            self.assertEqual(functions(s), set())
            v = influence(s, {x: Q(1, 10) for x in s.P})["a0"]["a1"]
            if prev is not None:
                self.assertLess(v, prev)
            prev = v
        four = cases.parcels(4)
        self.assertEqual(influence(four, {x: Q(1, 10) for x in four.P})["a0"]["a1"], Q(9, 1000))
