"""Due-Witness, over issued roots, and the eight cases of the battery.

The biconditional is asserted exhaustively: for every scenario, every state and
every issued root, `not ContinuityOK` holds exactly when some descendant is
`Due`. The quantifier is `q in Roots_t` — the theorem says nothing about root
values that were never issued.
"""
from __future__ import annotations

import unittest

from ri_core import History, PAuth, standing_tag, superseding
import scenarios as S


def biconditional_holds(h: History) -> bool:
    for t in range(h.now + 1):
        for q in h.roots(t):
            if h.continuity_ok(q, t) == bool(h.due_witnesses(q, t)):
                return False
    return True


class TestBiconditional(unittest.TestCase):
    def test_holds_in_every_scenario_at_every_state(self):
        builders = [S.transfer_history, S.supersession_history, S.split_history,
                    S.merge_history, S.revocation_history, S.suspension_history,
                    S.force_history, S.third_party_history,
                    S.repeated_transfer_history, S.licensed_inference_history,
                    lambda: S.chain_history(3)]
        for build in builders:
            h = build()
            self.assertTrue(biconditional_holds(h), build)

    def test_unissued_root_is_outside_the_domain(self):
        """A root value not in `Roots_t` is neither Closed, Live nor Due, so
        the trichotomy and the biconditional are stated over `Roots_t` only."""
        h = S.supersession_history()
        ghost = S.AnsRoot("q:ghost", ("P0", 0), "A", "x",
                          S.ACCOUNT_FOR_SUCCESSION, S.GENESIS, 0)
        self.assertEqual("NotIssued", h.fate(ghost))
        self.assertFalse(h.continuity_ok(ghost))
        self.assertEqual((), h.due_witnesses(ghost))


class TestBattery(unittest.TestCase):
    def test_due_root_is_its_own_witness(self):
        h = S.chain_history(1)
        q0 = h.root("q0:x")
        self.assertEqual("Due", h.fate(q0))
        self.assertFalse(h.continuity_ok(q0))
        self.assertEqual(["q0:x"], [r.id for r in h.due_witnesses(q0)])

    def test_closed_parent_with_due_child(self):
        h = S.chain_history(2)
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        q0, child = h.root("q0:x"), h.root("@q1.0")
        self.assertEqual("Closed", h.fate(q0))
        self.assertEqual("Due", h.fate(child))
        self.assertFalse(h.continuity_ok(q0))
        self.assertEqual(["@q1.0"], [r.id for r in h.due_witnesses(q0)])

    def test_deep_due_descendant_with_closed_ancestors(self):
        h = S.chain_history(3)
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        h.respond("rho1", roots=["@q1.0"], cited=["a2"])
        self.assertEqual("Closed", h.fate(h.root("@q1.0")))
        self.assertEqual("Due", h.fate(h.root("@q2.0")))
        self.assertEqual(["@q2.0"], [r.id for r in h.due_witnesses(h.root("q0:x"))])

    def test_split_with_one_due_branch(self):
        seed = S.seed_from({
            "x": S.commitment("x"),
            "auth:split": PAuth(superseding(
                "split", ["x"], [S.commitment("l"), S.commitment("r")])),
            "auth:left": PAuth(superseding(
                "left", [standing_tag(1, 0)], [S.commitment("l2")])),
        }, debtor="A")
        h = History(seed)
        h.norm("a1", "auth:split", author="A")
        h.norm("a2", "auth:left", author="A")
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        q0 = h.root("q0:x")
        self.assertEqual("Closed", h.fate(q0))
        self.assertEqual({"@q1.0", "@q1.1"}, {r.id for r in h.succ(q0)})
        self.assertEqual(["@q1.0"], [r.id for r in h.due_witnesses(q0)])
        self.assertFalse(h.continuity_ok(q0))
        self.assertTrue(h.continuity_ok(h.root("@q1.1")))

    def test_merge_shares_one_descendant(self):
        seed = S.seed_from({
            "x": S.commitment("x"),
            "y": S.commitment("y"),
            "auth:merge": PAuth(superseding(
                "merge", ["x", "y"], [S.commitment("xy")])),
            "auth:kill": PAuth(superseding("kill", [standing_tag(1, 0)], [])),
        }, debtor="A")
        h = History(seed)
        h.norm("a1", "auth:merge", author="A")
        h.respond("rho0", roots=["q0:x", "q0:y"], cited=["a1"])
        qx, qy = h.root("q0:x"), h.root("q0:y")
        self.assertEqual("Closed", h.fate(qx))
        self.assertEqual("Closed", h.fate(qy))
        self.assertEqual({"@q1.0"}, {r.id for r in h.succ(qx)})
        self.assertEqual({"@q1.0"}, {r.id for r in h.succ(qy)})
        self.assertTrue(h.continuity_ok(qx) and h.continuity_ok(qy))
        h.norm("a2", "auth:kill", author="A")
        self.assertEqual(["@q1.0"], [r.id for r in h.due_witnesses(h.root("q0:x"))])
        self.assertEqual(["@q1.0"], [r.id for r in h.due_witnesses(h.root("q0:y"))])

    def test_closed_revocation_has_no_witness(self):
        h = S.revocation_history()
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        q0 = h.root("q0:x")
        self.assertEqual("Closed", h.fate(q0))
        self.assertEqual((), h.succ(q0))
        self.assertTrue(h.continuity_ok(q0))
        self.assertEqual((), h.due_witnesses(q0))

    def test_live_not_due_leaf_has_no_witness(self):
        h = History(S.seed_from({"x": S.commitment("x")}))
        q0 = h.root("q0:x")
        self.assertEqual("LiveNotDue", h.fate(q0))
        self.assertEqual((q0,), h.desc_star(q0))
        self.assertTrue(h.continuity_ok(q0))

    def test_multi_level_graph_with_no_due_anywhere(self):
        h = S.chain_history(2)
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        h.respond("rho1", roots=["@q1.0"], cited=["a2"])
        q0 = h.root("q0:x")
        self.assertEqual(3, len(h.desc_star(q0)))
        self.assertEqual((), h.due_witnesses(q0))
        self.assertTrue(all(h.continuity_ok(r) for r in h.desc_star(q0)))


if __name__ == "__main__":
    unittest.main()
