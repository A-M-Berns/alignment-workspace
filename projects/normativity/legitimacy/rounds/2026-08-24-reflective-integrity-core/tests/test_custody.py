"""Custody Locality, Transfer, and the answerability cases of the v1 battery."""
from __future__ import annotations

import unittest

from ri_core import (History, PAuth, Transfer, standing_tag, superseding,
                     transferring)
import scenarios as S


def custody_changes(h: History, x: str):
    """Every (t, before, after) at which `x`'s custodian changes."""
    out = []
    for t in range(h.now):
        before, after = h.custodian(x, t), h.custodian(x, t + 1)
        if before is not None and after is not None and before != after:
            out.append((t + 1, before, after))
    return out


class TestCustodyLocality(unittest.TestCase):
    def test_transfer_is_the_only_way_custody_of_a_live_object_moves(self):
        h = S.repeated_transfer_history()
        changes = custody_changes(h, "x")
        self.assertEqual([(1, "A", "B"), (2, "B", "C")], changes)
        for tau, _, _ in changes:
            a = [e for e in h.norm_events() if e.tau == tau][0]
            self.assertIsInstance(h.effect(a), Transfer)
            self.assertEqual("x", h.effect(a).x)

    def test_suspension_and_resume_do_not_move_custody(self):
        h = S.suspension_history()
        self.assertEqual([], custody_changes(h, "x"))
        self.assertEqual("A", h.custodian("x"))
        self.assertEqual(("Suspended",), h.status("x", 1))
        self.assertEqual(("Active",), h.status("x", 2))

    def test_supersession_ends_custody_rather_than_moving_it(self):
        h = S.supersession_history()
        self.assertIsNone(h.custodian("x"))
        self.assertEqual([], custody_changes(h, "x"))
        self.assertEqual("A", h.custodian(standing_tag(1, 0)))

    def test_third_party_disposition_is_permitted_and_still_accounted(self):
        """The disposing author need not be the debtor; the episode is still
        the one selected, and the successor's debtor is the author."""
        h = S.third_party_history()
        self.assertEqual("Due", h.fate(h.root("q0:x")))
        self.assertEqual("A", h.root("q0:x").debtor)
        self.assertEqual("C", h.root("@q1.0").debtor)
        self.assertEqual("C", h.custodian(standing_tag(1, 0)))
        self.assertEqual([], h.answerability_conservation())


class TestTransfer(unittest.TestCase):
    def test_transfer_leaves_the_old_episode_due_and_mints_the_new_one(self):
        h = S.transfer_history()
        old, new = h.root("q0:x"), h.root("@q1.0")
        self.assertEqual("Due", h.fate(old))
        self.assertEqual("LiveNotDue", h.fate(new))
        self.assertEqual("x", new.subject)
        self.assertEqual("B", new.debtor)
        self.assertEqual({new.id}, {r.id for r in h.succ(old)})

    def test_transfer_does_not_write_standing(self):
        """Transfer Neutrality: the normative view is identical across it."""
        h = S.transfer_history()
        self.assertEqual(h.std(0), h.std(1))

    def test_transfer_admissibility_is_not_recipient_consent(self):
        """`B` is charged with the successor episode without any record of B
        having accepted. Admissibility comes from the authorising schema; what
        it does not establish is consent, and nothing here claims it."""
        h = S.transfer_history()
        self.assertEqual("B", h.custodian("x"))
        self.assertEqual([], [r for r in h.responses() if r.roots])

    def test_transfer_before_the_old_response_is_accounted(self):
        h = S.repeated_transfer_history()
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        self.assertEqual("Closed", h.fate(h.root("q0:x")))
        self.assertEqual("Due", h.fate(h.root("@q1.0")))
        self.assertEqual("LiveNotDue", h.fate(h.root("@q2.0")))
        self.assertEqual(["@q1.0"],
                         [r.id for r in h.due_witnesses(h.root("q0:x"))])

    def test_response_after_disposition_closes_exactly_its_own_root(self):
        h = S.split_history()
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        self.assertEqual("Closed", h.fate(h.root("q0:x")))
        self.assertEqual("LiveNotDue", h.fate(h.root("@q1.0")))


class TestDispositionUniqueness(unittest.TestCase):
    def test_a_root_is_disposed_at_most_once(self):
        h = S.repeated_transfer_history()
        q0 = h.root("q0:x")
        disposers = [a.id for a in h.norm_events() if h.disposes(a, q0)]
        self.assertEqual(["a1"], disposers)

    def test_digest_is_stable_across_later_events(self):
        h = S.repeated_transfer_history()
        a1 = [a for a in h.norm_events() if a.id == "a1"][0]
        early = h.digest(a1)
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        h.settle("s1")
        self.assertEqual(early, h.digest(a1))


if __name__ == "__main__":
    unittest.main()
