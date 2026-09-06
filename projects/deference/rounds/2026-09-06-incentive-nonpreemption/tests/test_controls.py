"""The negative controls of the dispatch's §11, numbered as there."""
import unittest
from fractions import Fraction as Q

from src.lemma import Frame, all_selectors, gain, principal_regret, selected_gap, sup_gain

W_TRUE = {"x": {"a": Q(1), "b": Q(0)}, "y": {"a": Q(0), "b": Q(1)}}
J_GOOD = {"x": "a", "y": "b"}
J_BAD = {"x": "b", "y": "a"}
SWAP = {"x": "b", "y": "a"}
HALF = {"x": Q(1, 2), "y": Q(1, 2)}


def plus_gap(f: Frame):
    """The weakest form: gap against the positive part of the principal's margin."""
    return sum(f.p[x] * ((f.EX[x][f.sigma[x]] - f.EX[x][f.J[x]])
                         - max(f.W[x][f.sigma[x]] - f.W[x][f.J[x]], Q(0))) for x in f.cells)


def plus_regret(f: Frame):
    return sum(f.p[x] * max(f.W[x][f.sigma[x]] - f.W[x][f.J[x]], Q(0)) for x in f.cells)


class Controls(unittest.TestCase):
    def test_1_no_selected_trust(self):
        """Perfect prediction of the principal's choice; opposite operative values."""
        EX = {"x": {"a": Q(0), "b": Q(1)}, "y": {"a": Q(1), "b": Q(0)}}
        f = Frame(HALF, EX, W_TRUE, J_GOOD, SWAP)
        self.assertEqual(selected_gap(f), Q(2))
        self.assertEqual(gain(f), Q(1))
        self.assertEqual(sup_gain(f, list(all_selectors(f))), Q(1))

    def test_2_no_protected_target(self):
        """The target reads the quote: `target(b) = 1[b ≤ 1/2]` is at distance ≥ 1/2 from
        every quote, so no correspondence radius below 1/2 exists and the composed
        bound `2δ + 2ζ + η ≥ 1` is vacuous on a [0,1] menu."""
        gaps = [abs((Q(1) if b <= Q(1, 2) else Q(0)) - b) for b in (Q(k, 100) for k in range(101))]
        self.assertEqual(min(gaps), Q(1, 2))
        self.assertGreaterEqual(2 * min(gaps), Q(1))

    def test_3_no_principal_decision_quality(self):
        """The agent's operative values equal the protected values exactly (selected gap
        0), and the principal picks the worst item: the agent's gain is the principal's
        own regret, 1, and nothing in selected trust prevents it."""
        f = Frame(HALF, W_TRUE, W_TRUE, J_BAD, {"x": "a", "y": "b"})
        self.assertEqual(selected_gap(f), Q(0))
        self.assertEqual(principal_regret(f), Q(1))
        self.assertEqual(gain(f), Q(1))

    def test_5_constraint_versus_incentive(self):
        """A membrane removes the substituting selectors from the feasible set; the
        counterfactual gain of the removed selector is unchanged."""
        EX = {"x": {"a": Q(0), "b": Q(1)}, "y": {"a": Q(1), "b": Q(0)}}
        f = Frame(HALF, EX, W_TRUE, J_GOOD, SWAP)
        feasible = [s for s in all_selectors(f) if s == J_GOOD]
        self.assertEqual(sup_gain(f, feasible), Q(0))
        self.assertEqual(gain(f), Q(1))              # the incentive is intact

    def test_6_epistemic_operative_mismatch(self):
        """The agent's *prediction* of the protected values is exact; its operative
        values are anti-correlated.  A 'trust' computed against the prediction reads
        zero; the real selected gap is maximal."""
        predicted_W = {x: dict(W_TRUE[x]) for x in W_TRUE}
        EX = {"x": {"a": Q(0), "b": Q(1)}, "y": {"a": Q(1), "b": Q(0)}}
        fake = Frame(HALF, predicted_W, W_TRUE, J_GOOD, SWAP)
        real = Frame(HALF, EX, W_TRUE, J_GOOD, SWAP)
        self.assertEqual(selected_gap(fake), Q(0))
        self.assertEqual(selected_gap(real), Q(2))
        self.assertEqual(gain(real), Q(1))

    def test_7_capture(self):
        """Against an evaluator the agent selected (`W = EX`), selected trust holds at
        zero and the bound 'proves' non-preemption relative to that evaluator; against
        the sealed evaluator the same selector has the maximal gap."""
        EX = {"x": {"a": Q(0), "b": Q(1)}, "y": {"a": Q(1), "b": Q(0)}}
        captured = Frame(HALF, EX, EX, J_GOOD, SWAP)
        sealed = Frame(HALF, EX, W_TRUE, J_GOOD, SWAP)
        self.assertEqual(selected_gap(captured), Q(0))
        self.assertEqual(gain(captured), selected_gap(captured) + principal_regret(captured))
        self.assertEqual(selected_gap(sealed), Q(2))
        self.assertEqual(gain(captured), gain(sealed))   # the same act, two verdicts

    def test_8_selector_dependent_payoff(self):
        """Punishing-menu shape: the payoff of an item depends on whether the agent
        substituted it.  Selected trust certified under the non-substituting selector
        says nothing about the substituting one."""
        def EX_for(sigma):
            return {x: {m: (Q(1) if (sigma[x] == m and m != J_GOOD[x]) else Q(1, 2))
                        for m in ("a", "b")} for x in ("x", "y")}
        f0 = Frame(HALF, EX_for(J_GOOD), W_TRUE, J_GOOD, J_GOOD)
        f1 = Frame(HALF, EX_for(SWAP), W_TRUE, J_GOOD, SWAP)
        self.assertEqual(selected_gap(f0), Q(0))
        self.assertEqual(gain(f0), Q(0))
        self.assertEqual(gain(f1), Q(1, 2))
        self.assertEqual(selected_gap(f1), Q(3, 2))
        f_fixed = Frame(HALF, EX_for(J_GOOD), W_TRUE, J_GOOD, SWAP)   # the wrong payoff table
        self.assertEqual(selected_gap(f_fixed), Q(1))
        self.assertLess(gain(f_fixed), gain(f1))

    def test_plus_form_is_weakest_and_tight_on_control_1(self):
        """ST⁺: gap against the positive part of the principal's margin.  Implied by ST,
        and on control 1 it equals the agent's gain exactly."""
        EX = {"x": {"a": Q(0), "b": Q(1)}, "y": {"a": Q(1), "b": Q(0)}}
        f = Frame(HALF, EX, W_TRUE, J_GOOD, SWAP)
        self.assertLessEqual(plus_gap(f), selected_gap(f))
        self.assertEqual(plus_gap(f), gain(f))
        self.assertEqual(plus_regret(f), Q(0))
        self.assertLessEqual(gain(f), plus_gap(f) + plus_regret(f))


if __name__ == "__main__":
    unittest.main()
