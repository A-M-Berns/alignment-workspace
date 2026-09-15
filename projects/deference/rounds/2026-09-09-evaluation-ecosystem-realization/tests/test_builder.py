"""The protocol instance and the Integrity builder (E2)."""
from __future__ import annotations

import unittest

from src import ecosystem as eco
from src import protocol as pr
from src.fixtures import W0, W1, W2, W3, WORLDS
from src.log import COMMIT, P


def _logs():
    for w in list(WORLDS) + [eco.World("close", close_at=3), eco.World("delegate", delegate_at=1)]:
        for z in ("reading", "susceptible", "eager"):
            fr = eco.Frame(w, eco.PRINCIPALS[z])
            for n in eco.AUDITED:
                yield w, z, n, fr.log(eco.ADVISORS[n])


class TestBuilder(unittest.TestCase):
    def test_propagation_agrees_with_canonical_account(self):
        """`Segment.complete_accounting` from the empty prefix equals `account_at` at every
        prefix, for every occurrence: propagation is a function of the log."""
        for w, z, n, log in _logs():
            for K in range(len(log) + 1):
                acc = pr.accounts_at(log, K)
                B = pr.boundary(log, K)
                self.assertEqual(set(acc), B["exposed"])
                for o in B["exposed"]:
                    self.assertEqual(acc[o], pr.account_at(log, K, o), (w.name, z, n, K, o))

    def test_boundaries_and_steps_are_well_formed(self):
        for w, z, n, log in _logs():
            for k in range(len(log)):
                st = pr.step(log, k)
                A_, B_ = pr.boundary(log, k), pr.boundary(log, k + 1)
                self.assertEqual(st["event"], k)
                self.assertNotIn(k, A_["history"])
                self.assertEqual(B_["history"], A_["history"] + [k])
                self.assertTrue(A_["exposed"] <= B_["exposed"])
                for o in B_["exposed"] - A_["exposed"]:
                    self.assertTrue(pr.admitted(log.prefix(k + 1), o, pr.anchor(log, o)))

    def test_first_resolution_binds(self):
        """Once resolved, the account is terminal and every later prefix agrees."""
        for w, z, n, log in _logs():
            for o in pr.boundary(log, len(log))["exposed"]:
                r = pr.resolver(log, len(log), o)
                if r is None:
                    continue
                j, fate = r
                for K in range(j + 1, len(log) + 1):
                    t = pr.account_at(log, K, o)
                    self.assertEqual(t[0], "answer" if fate == "answered" else "close")
                    self.assertEqual(t[1]["event"], j)

    def test_activation_reads_the_fates(self):
        log = eco.Frame(W0, eco.PRINCIPALS["reading"]).log(eco.ADVISORS["honest"])
        t = pr.account_at(log, len(log), 0)
        self.assertTrue(pr.activated(t))
        self.assertEqual(pr.fates(t), ["answered"])
        # a closure of the same occurrence is a different fate and does not activate
        logc = eco.Frame(eco.World("close", close_at=3), eco.PRINCIPALS["reading"]).log(eco.ADVISORS["honest"])
        tc = pr.account_at(logc, len(logc), 0)
        self.assertEqual(pr.fates(tc), ["closed"])
        self.assertFalse(pr.activated(tc))
        # the principal's later commit does not enter the closed account
        self.assertTrue(any(e.kind == COMMIT and e.author == P for e in logc))
        # a live occurrence (slot never opens) is not activated
        logl = eco.Frame(W3, eco.PRINCIPALS["reading"]).log(eco.ADVISORS["honest"])
        self.assertEqual(pr.fates(pr.account_at(logl, len(logl), 0)), ["live"])

    def test_local_trace_is_a_projection(self):
        """The local trace of the evaluation occurrence is its account at each prefix
        from issuance, and its endpoint is the globally propagated account."""
        for w, z, n, log in _logs():
            tr = pr.local_trace(log, 0, len(log))
            self.assertEqual(len(tr), len(log))
            self.assertEqual(tr[-1][1], pr.accounts_at(log, len(log))[0])
            for k, t in tr:
                self.assertEqual(t, pr.account_at(log, k, 0))

    def test_answer_receipt_is_at_strict_prefix(self):
        log = eco.Frame(W1, eco.PRINCIPALS["reading"]).log(eco.ADVISORS["honest"])
        rc = pr.answer_receipt(pr.account_at(log, len(log), 0))
        self.assertNotIn(rc["event"], rc["atHistory"])
        self.assertEqual(rc["atHistory"], list(range(rc["event"])))
        self.assertTrue(pr.answer_ok(log.prefix(rc["event"]), pr.anchor(log, 0), rc["warrant"]))
        self.assertTrue(pr.authorized(log.prefix(rc["event"]), rc["warrant"]))


if __name__ == "__main__":
    unittest.main()
