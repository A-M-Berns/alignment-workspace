import unittest
from fractions import Fraction as Q

from src.structure import (admissible_anchored, admissible_world_read, collapse,
                           myopic_gated_run, pareto_dominates, successor_choice)

ACTIONS = ("work", "kill")
BRANCHES = ("g1", "g2")
VALUES = {"g1": {"work": Q(1), "kill": Q(1)}, "g2": {"work": Q(1), "kill": Q(0)}}
BASE = {"g1": Q(1, 2), "g2": Q(1, 2)}


class Structure(unittest.TestCase):
    def test_9_branch_deletion(self):
        """CM-9: with a world-read branch index, destroying g2's affordance removes g2
        from the criterion and `kill` becomes admissible; anchored, it stays vetoed."""
        available = lambda g, q: not (g == "g2" and q == "kill")
        destroyed = lambda g, q: g == "g2" and q == "kill"
        self.assertEqual(admissible_world_read(ACTIONS, BRANCHES, VALUES, BASE, available),
                         {"work", "kill"})
        self.assertEqual(admissible_anchored(ACTIONS, BRANCHES, VALUES, BASE, destroyed),
                         {"work"})

    def test_branch_incompleteness(self):
        """Two actions trading branches are incomparable under the Pareto order; a
        completion is charter content."""
        vals = {"g1": {"x": Q(1), "y": Q(0)}, "g2": {"x": Q(0), "y": Q(1)}}
        self.assertFalse(pareto_dominates(vals, BRANCHES, "x", "y"))
        self.assertFalse(pareto_dominates(vals, BRANCHES, "y", "x"))

    def test_5_norm_hacking_through_endogenous_admissibility(self):
        """CM-5 / CM-11: a myopic gated learner picks an admissible action that rewrites
        the next round's adequacy; its preferred inadequate action is then 'adequate'."""
        r1 = {"safe": Q(1), "rewrite": Q(11, 10)}
        r2 = {"safe": Q(1), "violate": Q(5)}
        a1, a2, adeq2 = myopic_gated_run(
            actions=("safe", "rewrite", "violate"), adequate_round1={"safe", "rewrite"},
            reward1=r1, rewrite={"rewrite": {"safe", "violate"}},
            adequate_round2={"safe"}, reward2=r2)
        self.assertEqual(a1, "rewrite")
        self.assertEqual(a2, "violate")
        # with representation change classified as a slow-lane act it is not in A_1
        a1b, a2b, _ = myopic_gated_run(("safe", "rewrite", "violate"), {"safe"}, r1,
                                       {"rewrite": {"safe", "violate"}}, {"safe"}, r2)
        self.assertEqual((a1b, a2b), ("safe", "safe"))

    def test_7_self_modification(self):
        """CM-7: an atomic-action gate lets the chooser install an ungated successor
        (more task value); a two-level gate blocks it unless certified."""
        installs = ("keep-gate", "drop-gate")
        tv = {"keep-gate": Q(1), "drop-gate": Q(10)}
        ok = {"keep-gate": True, "drop-gate": False}
        self.assertEqual(successor_choice("atomic", installs, tv, ok), "drop-gate")
        self.assertEqual(successor_choice("two-level", installs, tv, ok), "keep-gate")

    def test_hierarchy_collapses_to_two_levels(self):
        state, folded = collapse(("C3", "C2", "C1", "R"))
        self.assertEqual(state, (("C3", "C2", "C1"), "R"))
        self.assertEqual(folded, 3)


if __name__ == "__main__":
    unittest.main()
