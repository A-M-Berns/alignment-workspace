"""Endogenous admissibility: the comparator class and why a myopic gated learner's
guarantee against it is vacuous without dynamic evaluation."""
import unittest
from fractions import Fraction as Q

from src.structure import (branch_adequate, constitutional_adequate, myopic, run_policy,
                           world_read_adequate)

# A two-state admissibility process.  State "base": {work, request, hack} where `hack`
# is admissible only under the untyped gate.  `request` is an authorized slow-lane act
# that moves to "expanded", where {work, expanded} are admissible.  `hack` moves to
# "hacked", where {work, violate} are admissible under the untyped gate.
REWARD = {("base", "work"): Q(1), ("base", "request"): Q(0), ("base", "hack"): Q(11, 10),
          ("expanded", "work"): Q(1), ("expanded", "expanded"): Q(3),
          ("hacked", "work"): Q(1), ("hacked", "violate"): Q(5)}


def transition(h, q):
    return {"request": "expanded", "hack": "hacked"}.get(q, h)


def reward_of(h, q):
    return REWARD[(h, q)]


def typed_admissible(h):
    return {"base": {"work", "request"}, "expanded": {"work", "expanded"},
            "hacked": {"work"}}[h]


def untyped_admissible(h):
    return {"base": {"work", "request", "hack"}, "expanded": {"work", "expanded"},
            "hacked": {"work", "violate"}}[h]


def investor(h, t):
    return "request" if h == "base" else "expanded"


class Dynamic(unittest.TestCase):
    def test_legitimate_comparators_exist_and_differ_in_induced_admissibility(self):
        H = 6
        v_my, ok_my = run_policy(myopic(typed_admissible, reward_of), typed_admissible,
                                 reward_of, transition, "base", H)
        v_inv, ok_inv = run_policy(investor, typed_admissible, reward_of, transition, "base", H)
        self.assertTrue(ok_my and ok_inv)              # both are legitimate
        self.assertEqual(v_my, Q(H))
        self.assertEqual(v_inv, 3 * (H - 1))
        # the investor's later action is inadmissible on the myopic learner's own trajectory
        self.assertNotIn("expanded", typed_admissible("base"))

    def test_myopic_regret_against_legitimate_comparators_is_linear(self):
        """Comparator restriction (C) without dynamic evaluation (B) is vacuous: the
        myopic gated learner is legitimate and its regret grows linearly."""
        for H in (2, 5, 20):
            v_my, _ = run_policy(myopic(typed_admissible, reward_of), typed_admissible,
                                 reward_of, transition, "base", H)
            v_inv, _ = run_policy(investor, typed_admissible, reward_of, transition, "base", H)
            self.assertEqual(v_inv - v_my, 2 * H - 3)

    def test_untyped_gate_is_hacked(self):
        """Without domain typing (A), the myopic learner takes the representation-changing
        act and then the violation; it is not a legitimate policy."""
        pol = myopic(untyped_admissible, reward_of)
        v, ok = run_policy(pol, typed_admissible, reward_of, transition, "base", 3)
        self.assertFalse(ok)
        self.assertEqual(pol("base", 0), "hack")
        self.assertEqual(pol("hacked", 1), "violate")

    def test_branch_persistence_adequate_set_form(self):
        """An action that destroys a protected branch is inadequate for that branch under
        the charter-anchored index; under the world-read index the branch drops out."""
        actions = ("work", "kill")
        charter = ("g1", "g2")
        keeps = lambda g, q: not (g == "g2" and q == "kill")
        meets = lambda g, q: True
        self.assertFalse(branch_adequate("kill", "g2", keeps, meets))
        self.assertEqual(constitutional_adequate(actions, charter, keeps, meets), {"work"})
        self.assertEqual(world_read_adequate(actions, charter, keeps, meets), {"work", "kill"})


if __name__ == "__main__":
    unittest.main()
