"""Write-separation and the `O_t` projection the downstream slice consumes.

This checks that the repaired architecture permits the pipeline; it does not
build it. What is asserted is exactly the write separation and the shape of the
projection, which is what the compilation to force needs from the record.
"""
from __future__ import annotations

import unittest

from ri_core import History, PAuth, PForce, Transfer
import scenarios as S


class TestWriteSeparation(unittest.TestCase):
    def test_settle_writes_only_the_settlement_ledger(self):
        h = S.supersession_history()
        before = (h.reasons(), h.norm_events(), h.responses(), h.std(), h.roots())
        h.settle("s1")
        self.assertEqual(1, len(h.settlements()))
        self.assertEqual(before[0], h.reasons())
        self.assertEqual(before[1], h.norm_events())
        self.assertEqual(before[3], h.std())
        self.assertEqual({q.id for q in before[4]}, {q.id for q in h.roots()})

    def test_reason_writes_only_the_reason_ledger(self):
        h = S.supersession_history()
        std_before, roots_before = h.std(), {q.id for q in h.roots()}
        h.settle("s1")
        h.reason("e1", s_L=frozenset(["s1"]), target="p")
        self.assertEqual(1, len(h.reasons()))
        self.assertEqual(std_before, h.std())
        self.assertEqual(roots_before, {q.id for q in h.roots()})

    def test_norm_is_the_only_step_that_changes_standing(self):
        for build in (S.supersession_history, S.transfer_history,
                      S.suspension_history, lambda: S.chain_history(2)):
            h = build()
            h.settle("s1")
            h.reason("e1", s_L=frozenset(["s1"]), target="p")
            h.respond("rho0", roots=[h.roots()[0].id], cited=[])
            for t in range(h.now):
                if h.std(t) != h.std(t + 1):
                    self.assertEqual("Norm", type(h.steps[t]).__name__)

    def test_respond_accounts_without_disposing(self):
        h = S.supersession_history()
        q0 = h.root("q0:x")
        disposers_before = [a.id for a in h.norm_events() if h.disposes(a, q0)]
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        self.assertEqual(disposers_before,
                         [a.id for a in h.norm_events() if h.disposes(a, h.root("q0:x"))])
        self.assertEqual(h.std(h.now - 1), h.std())


class TestOperativeProjection(unittest.TestCase):
    def test_o_t_is_the_active_force_projection(self):
        h = S.force_history()
        self.assertEqual(frozenset(["clause:phi"]), h.operative())
        self.assertEqual(frozenset(), h.operative(0))

    def test_a_downstream_consumer_reads_o_t_and_writes_nothing(self):
        """A stand-in for the trader side: it consumes the projection, and the
        record is bit-identical afterwards."""
        h = S.force_history()
        snapshot = (h.std(), tuple(q.id for q in h.roots()), h.now)
        consumed = sorted(h.operative())
        self.assertEqual(["clause:phi"], consumed)
        self.assertEqual(snapshot, (h.std(), tuple(q.id for q in h.roots()), h.now))

    def test_force_standing_is_answerable_like_any_other(self):
        h = S.force_history()
        force_ids = [x for x, s in h.std().items() if isinstance(s.payload, PForce)]
        self.assertEqual(1, len(force_ids))
        eps = [q for q in h.roots() if q.subject == force_ids[0]]
        self.assertEqual(1, len(eps))
        self.assertTrue(h.current_episode(eps[0]))


if __name__ == "__main__":
    unittest.main()
