from __future__ import annotations

import sys
import unittest
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from kernel_witnesses import (  # noqa: E402
    EPSILON,
    Rewrite,
    aggregate_defeat_key_repairs_locality,
    all_prefix_languages,
    basis_loss_epochs,
    canonical_now_meet,
    derivative_meet,
    eventually_a_has_no_bad_finite_prefix,
    fresh_defeater_breaks_locality,
    hidden_control_pair,
    joint_transport_laundering,
    local_to_global_chain,
    now_meet_counterexample,
    now_need_not_be_convex,
    same_equation_different_ancestry,
    shared_merge_accounts,
    split_merge_accounts,
    unrelated_stronger_impersonates,
)


class ReasonInterfaceWitnesses(unittest.TestCase):
    def test_fresh_defeater_breaks_finite_locality_without_an_aggregate_key(self):
        agrees, valid_before, valid_after = fresh_defeater_breaks_locality()
        self.assertTrue(agrees)
        self.assertTrue(valid_before)
        self.assertFalse(valid_after)

    def test_aggregate_defeat_key_makes_the_change_declared(self):
        agrees, key_changed = aggregate_defeat_key_repairs_locality()
        self.assertFalse(agrees)
        self.assertTrue(key_changed)

    def test_valid_undertaken_basis_does_not_imply_reason_guided_control(self):
        faithful = hidden_control_pair(0)
        steered = hidden_control_pair(1)
        self.assertEqual(faithful[0], steered[0])
        self.assertNotEqual(faithful[1], steered[1])


class RewriteWitnesses(unittest.TestCase):
    def test_multiset_equation_does_not_determine_ancestry(self):
        parallel, crossed = same_equation_different_ancestry()
        live = Counter({"a": 1, "b": 1})
        self.assertEqual(parallel.equation(live), crossed.equation(live))
        self.assertNotEqual(parallel.links, crossed.links)

    def test_split_then_merge_unfolds_to_a_shared_dag_leaf(self):
        after_split, after_merge = split_merge_accounts()
        self.assertEqual(after_split, frozenset({"b", "c"}))
        self.assertEqual(after_merge, frozenset({"d"}))

    def test_a_merge_child_remains_in_each_ancestor_account(self):
        account_a, account_b = shared_merge_accounts()
        self.assertEqual(account_a, frozenset({"c"}))
        self.assertEqual(account_b, frozenset({"c"}))

    def test_fresh_liability_does_not_enter_an_old_account_without_a_link(self):
        rewrite = Rewrite(Counter({"a": 1}), Counter(), Counter({"f": 1}),
                          frozenset())
        self.assertEqual(rewrite.equation(Counter({"a": 1})), Counter({"f": 1}))
        from kernel_witnesses import account_frontier
        self.assertEqual(account_frontier("a", (rewrite,)), frozenset())

    def test_joint_transport_can_launder_one_parent(self):
        verdict = joint_transport_laundering()
        self.assertTrue(verdict["joint"])
        self.assertFalse(verdict["per_parent_a"])
        self.assertTrue(verdict["per_parent_b"])

    def test_semantic_refinement_alone_does_not_authenticate_lineage(self):
        self.assertTrue(unrelated_stronger_impersonates())


class SafetyAndProjectionWitnesses(unittest.TestCase):
    def test_derivative_distributes_over_meet_exhaustively_at_horizon_two(self):
        languages = all_prefix_languages(2)
        for left in languages:
            for right in languages:
                for event in ("a", "b"):
                    self.assertTrue(derivative_meet(event, left, right))

    def test_local_transport_implies_global_transport_in_all_two_step_chains(self):
        languages = all_prefix_languages(2)
        for first in languages:
            for second in languages:
                for third in languages:
                    for history in ("aa", "ab", "ba", "bb"):
                        self.assertTrue(local_to_global_chain(
                            (first, second, third), history))

    def test_existential_now_does_not_preserve_conjunction(self):
        joint, separate = now_meet_counterexample()
        self.assertEqual(joint, frozenset())
        self.assertEqual(separate, frozenset({0, 1}))

    def test_canonical_visible_events_make_now_meet_preserving(self):
        self.assertTrue(canonical_now_meet(frozenset({0}), frozenset({0, 1})))

    def test_prefix_safety_does_not_make_the_current_set_convex(self):
        current, contains_midpoint = now_need_not_be_convex()
        self.assertEqual(current, frozenset({0, 2}))
        self.assertFalse(contains_midpoint)

    def test_unbounded_eventual_service_has_no_bad_finite_prefix(self):
        for length in range(8):
            self.assertTrue(eventually_a_has_no_bad_finite_prefix(length))

    def test_basis_loss_mints_once_per_invalidation_epoch(self):
        self.assertEqual(basis_loss_epochs((True, False, False, True, False)), (1, 4))

    def test_null_input_is_rejected(self):
        with self.assertRaises(ValueError):
            local_to_global_chain((), "a")


if __name__ == "__main__":
    unittest.main()
