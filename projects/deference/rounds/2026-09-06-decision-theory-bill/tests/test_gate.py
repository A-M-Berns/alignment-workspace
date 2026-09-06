import unittest
from fractions import Fraction as Q
from itertools import product

from src.gate import (BOT, bribe_needed, gated_choice, hard_gate, kappa, mass_off,
                      region_point, scalarized_choice, soft_gate, sup_dist)

MENU = ("a", "b", "c")
ADEQ = {"a", "b"}
TAU, DELTA = Q(1, 2), Q(1, 10)
PREF = {"a": Q(1), "b": Q(2), "c": Q(3)}     # the task prefers the inadequate response


def perturbations(u, step, radius):
    grid = [Q(k) * step for k in range(-radius, radius + 1)]
    for shifts in product(grid, repeat=len(u)):
        yield {q: u[q] + s for q, s in zip(u, shifts)}


class Gate(unittest.TestCase):
    def test_soft_gate_coupling_holds_with_margin(self):
        """(AC): mass off A ≤ κ·d for every price vector, exhaustively on a grid."""
        u = region_point(MENU, ADEQ, TAU, DELTA)
        k = kappa(MENU, PREF, DELTA)
        for b in perturbations(u, Q(1, 40), 12):
            d = sup_dist(b, u)
            self.assertLessEqual(mass_off(soft_gate(b, PREF, TAU, DELTA), ADEQ), k * d)

    def test_soft_gate_is_sound_and_competent_at_region_points(self):
        u = region_point(MENU, ADEQ, TAU, DELTA)
        dist = soft_gate(u, PREF, TAU, DELTA)
        self.assertEqual(mass_off(dist, ADEQ), Q(0))
        self.assertEqual(max(dist, key=dist.get), "b")   # best task value inside A

    def test_hard_gate_has_no_lipschitz_constant(self):
        """CM-10: a price state at sup-distance d from the region admits the inadequate
        response with mass 1, for every d > 0."""
        u = region_point(MENU, ADEQ, TAU, DELTA)
        for d in (Q(1, 2), Q(1, 100), Q(1, 10**6)):
            b = dict(u)
            b["c"] = TAU + d
            self.assertEqual(sup_dist(b, u), d)
            self.assertEqual(mass_off(hard_gate(b, PREF, TAU), ADEQ), Q(1))

    def test_no_margin_means_inquiry_not_violation(self):
        """CM-2: no confidently adequate response — the soft gate inquires; the mass
        off A is 1 and is charged, but no inadequate response is executed."""
        b = {"a": TAU + DELTA / 2, "b": TAU + DELTA / 2, "c": TAU + DELTA / 2}
        dist = soft_gate(b, PREF, TAU, DELTA)
        self.assertEqual(dist, {BOT: Q(1)})
        self.assertEqual(mass_off(dist, ADEQ), Q(1))
        self.assertEqual(mass_off(dist, ADEQ | {BOT}), Q(0))

    def test_conflicting_vetoes_route_to_inquiry(self):
        """CM-4: two hard reasons eliminate every task action; the gated chooser
        returns the inquiry response rather than a violation."""
        self.assertEqual(gated_choice({"a": Q(1), "b": Q(1)}, adequate=set()), BOT)

    def test_finite_scalar_bribery(self):
        """CM-1 / NFL: for any λ and loss range D, a task stake above λ·D on the
        forbidden option flips the scalarized chooser; the gated chooser is invariant."""
        loss = {"a": Q(0), "c": Q(1)}     # D = 1
        for lam in (Q(1), Q(10), Q(1000)):
            task = {"a": Q(1), "c": Q(1) + lam + Q(1)}
            self.assertEqual(scalarized_choice(task, loss, lam), "c")
            self.assertEqual(gated_choice(task, adequate={"a"}), "a")
            small = {"a": Q(1), "c": Q(1) + lam - Q(1)}
            self.assertEqual(scalarized_choice(small, loss, lam), "a")
            self.assertEqual(bribe_needed(small, loss, lam, "c", "a"), Q(1))

    def test_bounded_penalty_is_the_same_failure(self):
        """A penalty bounded by P is a scalar penalty with λ·D ≤ P."""
        loss = {"a": Q(0), "c": Q(1)}
        P = Q(5)
        task = {"a": Q(0), "c": P + Q(1)}
        self.assertEqual(scalarized_choice(task, loss, P), "c")


if __name__ == "__main__":
    unittest.main()
