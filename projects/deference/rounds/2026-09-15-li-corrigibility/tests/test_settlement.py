"""Occurrence expiry and what settles under which architecture."""

import unittest
from fractions import Fraction as Q

from src import settlement as S

ISSUE, OPEN, COMMIT, CLOSE_SESSION, CLOSE_OCC = S.ISSUE, S.OPEN, S.COMMIT, S.CLOSE_SESSION, S.CLOSE_OCC


class Expiry(unittest.TestCase):

    def test_slot_never_opens_is_never_resolved(self):
        log = [(0, ISSUE, 1), (1, "NOISE", None), (2, "NOISE", None), (3, "NOISE", None)]
        self.assertTrue(S.never_resolved(log, 1))
        for k in range(len(log) + 1):
            self.assertFalse(S.activated_at(log, k, 1))

    def test_explicit_closure_settles_void(self):
        log = [(0, ISSUE, 1), (1, "NOISE", None), (2, CLOSE_OCC, None)]
        self.assertFalse(S.resolved_at(log, 2, 1))
        self.assertTrue(S.resolved_at(log, 3, 1))
        self.assertFalse(S.activated_at(log, 3, 1))

    def test_horizon_determines_the_security(self):
        vec = (Q(1, 4), Q(3, 4))
        log = [(0, ISSUE, 1), (1, OPEN, 1), (2, COMMIT, (1, vec)), (3, CLOSE_SESSION, 1)]
        for K in range(len(log) + 1):
            self.assertTrue(S.determined_after(log, K, 1, 1))
        self.assertEqual(S.security_with_horizon(log, 2, 1, 1), Q(0))
        self.assertEqual(S.security_with_horizon(log, 3, 1, 1), Q(3, 4))

    def test_late_commit_after_horizon_does_not_count(self):
        vec = (Q(1, 2), Q(1, 2))
        log = [(0, ISSUE, 1), (1, OPEN, 1), (2, "NOISE", None), (3, COMMIT, (1, vec))]
        K = 3
        self.assertEqual(S.security_with_horizon(log, K, 1, 0), Q(0))
        self.assertTrue(S.determined_after(log, K, 1, 0))
        # without the horizon the occurrence is eventually answered
        self.assertTrue(S.activated_at(log, len(log), 1))

    def test_commit_while_closed_is_not_an_answer(self):
        vec = (Q(1), Q(0))
        log = [(0, ISSUE, 1), (1, OPEN, 1), (2, CLOSE_SESSION, 1), (3, COMMIT, (1, vec))]
        self.assertFalse(S.activated_at(log, len(log), 1))
        self.assertTrue(S.never_resolved(log, 1))


class Categories(unittest.TestCase):

    def test_sequenced_settlement_settles_the_pair(self):
        for sel in ("raw", "corr"):
            self.assertEqual(S.settles("U_raw", "sequenced", sel), S.ADJUDICATED)
            self.assertEqual(S.settles("U_corr", "sequenced", sel), S.ADJUDICATED)
            self.assertEqual(S.settles("U_raw - U_corr", "sequenced", sel), S.ADJUDICATED)

    def test_same_branch_settles_only_the_selected_option(self):
        self.assertEqual(S.settles("U_raw", "same-branch", "raw"), S.ADJUDICATED)
        self.assertEqual(S.settles("U_corr", "same-branch", "raw"), S.NONSETTLING)
        self.assertEqual(S.settles("U_raw - U_corr", "same-branch", "raw"), S.NONSETTLING)
        self.assertEqual(S.settles("U_raw - U_corr", "same-branch", "corr"), S.NONSETTLING)

    def test_the_four_kinds(self):
        self.assertEqual(S.settles("structural-inequality", "sequenced", "raw"), S.DEDUCTIVE)
        self.assertEqual(S.settles("program-output-on-trace", "sequenced", "raw"), S.ADJUDICATED)
        self.assertEqual(S.settles("trace", "sequenced", "raw"), S.EMPIRICAL)
        self.assertEqual(S.settles("amendment-is-good", "sequenced", "raw"), S.NONSETTLING)


if __name__ == "__main__":
    unittest.main()
