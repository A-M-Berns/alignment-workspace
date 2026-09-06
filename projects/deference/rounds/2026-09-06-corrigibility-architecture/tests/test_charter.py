import unittest

from src.charter import closure_receipt, supersede

H0 = [0, 1, 2]
STOP = ("cmd", "P", "stop", (0, 1, 2))          # authenticated at prefix [0,1,2]
REL = ("cmd", "P", "release", (0, 1, 2))
OUT = ("cmd", "P", "transfer_out", (0, 1, 2))
CLASS = {"task1": "task", "task2": "task", "corr": "correction"}


def in_force_with_charter(h):
    return {"w_supersede", "w_release", "w_amend"}


def in_force_no_charter(h):
    return {"w_release"}


class Charter(unittest.TestCase):
    def test_supersession_is_closure_not_answer_and_keeps_history(self):
        docket = {"task1": "live", "task2": ("answered", "rcpt"), "corr": "live"}
        new, receipts = supersede(docket, H0 + [3], in_force_with_charter, STOP, "w_supersede",
                                  CLASS)
        self.assertEqual(new["task1"][0], "closed")
        self.assertEqual(new["task1"][1]["atHistory"], (0, 1, 2, 3))   # where, stored
        self.assertEqual(new["task2"], ("answered", "rcpt"))           # untouched
        self.assertEqual(new["corr"], "live")                          # charter silent
        self.assertEqual(new["respond:stop"], "live")                  # fresh occurrence
        self.assertEqual(set(receipts), {"task1"})

    def test_present_over_past_is_charter_content(self):
        """Without the supersession warrant in force nothing closes; the same act is
        recorded only as a fresh response obligation."""
        docket = {"task1": "live"}
        new, receipts = supersede(docket, H0 + [3], in_force_no_charter, STOP, "w_supersede",
                                  CLASS)
        self.assertEqual(new["task1"], "live")
        self.assertEqual(receipts, {})
        self.assertEqual(new["respond:stop"], "live")

    def test_item_must_be_available_at_the_prefix(self):
        early = ("cmd", "P", "stop", (0, 1, 2, 3, 4))    # issued later than h
        self.assertIsNone(closure_receipt(H0, in_force_with_charter, "task", early, "w_supersede"))
        self.assertIsNotNone(closure_receipt(H0, in_force_with_charter, "task", STOP, "w_supersede"))

    def test_release_and_transfer_out_are_closures_under_their_own_warrants(self):
        """No fourth fate: release and outward transfer are closure receipts whose
        warrants are charter content; the outward transfer of the correction concern
        needs the amendment warrant."""
        self.assertIsNotNone(closure_receipt(H0, in_force_with_charter, "task", REL, "w_release"))
        self.assertIsNone(closure_receipt(H0, in_force_with_charter, "correction", REL, "w_release"))
        self.assertIsNotNone(closure_receipt(H0, in_force_with_charter, "correction", OUT, "w_amend"))
        self.assertIsNone(closure_receipt(H0, in_force_no_charter, "correction", OUT, "w_amend"))


if __name__ == "__main__":
    unittest.main()
