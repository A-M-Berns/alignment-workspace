import unittest

from transfer_models import (
    MatterState,
    TransferBatch,
    Translation,
    answerability_conserved,
    compose,
    exhaustive_two_atom_conservation,
    response_structure_local,
    terminal_closure_sound,
)


def state(anchor, live=("q",), loads=None):
    a = frozenset(anchor)
    return MatterState(a, frozenset(live), loads or {live[0]: a})


class CarrierHostileExamples(unittest.TestCase):
    def test_01_one_faithful_successor(self):
        pre = state({"a"})
        batch = TransferBatch(frozenset({"q"}), {"q1": frozenset({"q"})}, {"q1": frozenset({"a"})})
        self.assertTrue(batch.valid(pre))
        self.assertTrue(answerability_conserved(pre, (batch,)))

    def test_02_structural_but_semantically_bogus_successor(self):
        pre = state({"a"})
        bogus = TransferBatch(frozenset({"q"}), {"q1": frozenset({"q"})}, {"q1": frozenset({"b"})})
        self.assertTrue(bogus.structural_ok(pre))
        self.assertFalse(bogus.transfer_sound(pre))

    def test_03_two_successors_jointly_carry_whole(self):
        pre = state({"a", "b"})
        split = TransferBatch(
            frozenset({"q"}),
            {"qa": frozenset({"q"}), "qb": frozenset({"q"})},
            {"qa": frozenset({"a"}), "qb": frozenset({"b"})},
        )
        self.assertTrue(split.valid(pre))
        self.assertEqual(split.apply(pre).carrier_frontier, frozenset({"qa", "qb"}))

    def test_04_redundant_same_half_is_incomplete(self):
        pre = state({"a", "b"})
        half = TransferBatch(
            frozenset({"q"}),
            {"q1": frozenset({"q"}), "q2": frozenset({"q"})},
            {"q1": frozenset({"a"}), "q2": frozenset({"a"})},
        )
        self.assertTrue(half.transfer_sound(pre))
        self.assertFalse(half.transfer_complete(pre))

    def test_05_valid_merge(self):
        pre = state({"a", "b"}, ("qa", "qb"), {"qa": frozenset({"a"}), "qb": frozenset({"b"})})
        merge = TransferBatch(
            frozenset({"qa", "qb"}), {"m": frozenset({"qa", "qb"})},
            {"m": frozenset({"a", "b"})},
        )
        self.assertTrue(merge.valid(pre))

    def test_06_merge_drops_one_parent(self):
        pre = state({"a", "b"}, ("qa", "qb"), {"qa": frozenset({"a"}), "qb": frozenset({"b"})})
        drop = TransferBatch(
            frozenset({"qa", "qb"}), {"m": frozenset({"qa", "qb"})},
            {"m": frozenset({"a"})},
        )
        self.assertTrue(drop.transfer_sound(pre))
        self.assertFalse(drop.transfer_complete(pre))

    def test_07_partial_satisfaction_and_transfer(self):
        pre = state({"a", "b"})
        partial = TransferBatch(
            frozenset({"q"}), {"qb": frozenset({"q"})}, {"qb": frozenset({"b"})},
            satisfy=frozenset({"a"}),
        )
        self.assertTrue(partial.valid(pre))
        self.assertEqual(partial.apply(pre).unresolved, frozenset({"b"}))

    def test_08_terminal_satisfaction(self):
        pre = state({"a"})
        terminal = TransferBatch(frozenset({"q"}), {}, {}, satisfy=frozenset({"a"}))
        self.assertTrue(terminal_closure_sound(pre, terminal))

    def test_09_terminal_authorized_disposition(self):
        pre = state({"a"})
        terminal = TransferBatch(
            frozenset({"q"}), {}, {}, dispose=frozenset({"a"}), disposition_authorized=True,
        )
        self.assertTrue(terminal_closure_sound(pre, terminal))

    def test_10_ontology_deletion_is_not_satisfaction(self):
        pre = state({"a"})
        deletion = TransferBatch(frozenset({"q"}), {}, {})
        self.assertFalse(deletion.valid(pre))

    def test_11_live_issue_can_launder_semantics_without_transfer(self):
        pre = state({"a"})
        laundered = MatterState(pre.anchor, pre.live, {"q": frozenset()})
        self.assertTrue(laundered.live)
        self.assertFalse(laundered.realizes_anchor())

    def test_12_live_frontier_contains_noncarriers(self):
        pre = MatterState(
            frozenset({"a"}), frozenset({"carrier", "helper", "obsolete"}),
            {"carrier": frozenset({"a"}), "helper": frozenset(), "obsolete": frozenset()},
        )
        self.assertEqual(pre.carrier_frontier, frozenset({"carrier"}))
        self.assertNotEqual(pre.carrier_frontier, pre.live)

    def test_13_coverage_translation_preserves_criticisms(self):
        pre = state({"criticism-a", "criticism-b"})
        carry = TransferBatch(
            frozenset({"q"}), {"sigma2": frozenset({"q"})},
            {"sigma2": frozenset({"criticism-a", "criticism-b"})},
        )
        self.assertTrue(carry.valid(pre))

    def test_14_coverage_translation_drops_criticism(self):
        pre = state({"criticism-a", "criticism-b"})
        drop = TransferBatch(
            frozenset({"q"}), {"sigma2": frozenset({"q"})},
            {"sigma2": frozenset({"criticism-a"})},
        )
        self.assertFalse(drop.transfer_complete(pre))

    def test_15_reason_carry_translation(self):
        t = Translation(
            {"old-reason": frozenset({"new-reason"})},
            {"old-reason": frozenset({"repair-a"})},
            {"new-reason": frozenset({"repair-a"})},
        )
        self.assertTrue(t.sound())

    def test_16_two_step_composition(self):
        t1 = Translation(
            {"r0": frozenset({"r1a", "r1b"})}, {"r0": frozenset({"a", "b"})},
            {"r1a": frozenset({"a"}), "r1b": frozenset({"b"})},
        )
        t2 = Translation(
            {"r1a": frozenset({"r2a"}), "r1b": frozenset({"r2b"})},
            t1.target_meaning,
            {"r2a": frozenset({"a"}), "r2b": frozenset({"b"})},
        )
        self.assertIsNotNone(compose(t1, t2))

    def test_17_plausible_links_can_lose_meaning(self):
        t1 = Translation({"r0": frozenset({"r1"})}, {"r0": frozenset({"a"})}, {"r1": frozenset({"a"})})
        t2 = Translation({"r1": frozenset({"r2"})}, {"r1": frozenset({"a"})}, {"r2": frozenset({"b"})})
        self.assertTrue(t1.complete() and t2.complete())
        self.assertFalse(t2.sound())
        self.assertIsNone(compose(t1, t2))

    def test_18_empty_successor_without_exit_fails(self):
        pre = state({"a"})
        empty = TransferBatch(frozenset({"q"}), {}, {})
        self.assertFalse(terminal_closure_sound(pre, empty))

    def test_19_same_response_rule_different_actions(self):
        rule = {0: "ignore", 1: "investigate"}
        self.assertTrue(response_structure_local(rule, (0, 1)))

    def test_20_no_independent_burden_lifecycle_needed_for_finite_graph(self):
        pre = state({"a", "b"})
        split = TransferBatch(
            frozenset({"q"}), {"qa": frozenset({"q"}), "qb": frozenset({"q"})},
            {"qa": frozenset({"a"}), "qb": frozenset({"b"})},
        )
        post = split.apply(pre)
        self.assertEqual(post.loads["qa"] | post.loads["qb"], pre.anchor)
        self.assertTrue(answerability_conserved(pre, (split,)))

    def test_exhaustive_two_atom_splits(self):
        self.assertTrue(exhaustive_two_atom_conservation())


if __name__ == "__main__":
    unittest.main()
