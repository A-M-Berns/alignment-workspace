"""The interpreter's event context, the count/ids split, and debtor by case.

These pin the parts of the signature that carry event identity and time:
`Terminated` records *which* event terminated, ids are drawn from *that event's*
time, and the debtor of a minted root depends on which constructor minted it.
"""
from __future__ import annotations

import unittest

from ri_core import (ACTIVE, ApplyCtx, Create, History, PAuth, Standing,
                     Supersede, Transfer, apply_effect, ctx_of, fresh_count,
                     fresh_ids, fresh_n, mint_ids, root_tag,
                     sampled_episode_demand_violations, standing_tag,
                     superseding, transferring)
import scenarios as S


class TestApplyContext(unittest.TestCase):
    def test_same_effect_at_different_times_allocates_different_ids(self):
        """The ids are a function of the effect *and* the context, so one
        effect value applied at two times introduces two distinct objects."""
        alpha = Create((S.commitment("k"),))
        one = apply_effect({}, ApplyCtx("a1", 1), Standing(alpha))
        two = apply_effect({}, ApplyCtx("a2", 2), Standing(alpha))
        self.assertEqual({standing_tag(1, 0)}, set(one))
        self.assertEqual({standing_tag(2, 0)}, set(two))
        self.assertEqual(set(), set(one) & set(two))

    def test_the_same_effect_reused_in_one_history_stays_disjoint(self):
        h = History(S.seed_from({
            "x": S.commitment("x"),
            "auth:mk": PAuth(S.creating("mk", [S.commitment("k")])),
        }))
        h.norm("a1", "auth:mk", author="A")
        h.norm("a2", "auth:mk", author="A")
        minted = {x for x in h.std() if x.startswith("@")}
        self.assertEqual({standing_tag(1, 0), standing_tag(2, 0)}, minted)
        self.assertEqual([], h.answerability_conservation())

    def test_fresh_count_is_a_cardinality_and_fresh_ids_is_a_set(self):
        alpha = Create((S.commitment("a"), S.commitment("b")))
        self.assertEqual(2, fresh_count(alpha))
        self.assertEqual((standing_tag(7, 0), standing_tag(7, 1)),
                         fresh_ids(ApplyCtx("a", 7), alpha))
        self.assertEqual((), fresh_n(ApplyCtx("a", 7), Transfer("x", "B")))
        self.assertEqual((root_tag(7, 0),), mint_ids(ApplyCtx("a", 7), 1))

    def test_supersede_records_the_disposing_event_id(self):
        h = S.supersession_history()
        self.assertEqual(("Terminated", "a1"), h.status("x"))

    def test_the_recorded_termination_id_is_stable(self):
        """Later steps do not rewrite it, and it names the event that actually
        disposed the object rather than the latest event."""
        h = S.chain_history(3)
        self.assertEqual(("Terminated", "a1"), h.status("x"))
        self.assertEqual(("Terminated", "a2"), h.status(standing_tag(1, 0)))
        h.settle("s1")
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        self.assertEqual(("Terminated", "a1"), h.status("x"))

    def test_termination_preserves_pred_and_payload(self):
        h = S.chain_history(2)
        successor = h.std()[standing_tag(1, 0)]
        self.assertEqual(frozenset(["x"]), successor.pred)
        self.assertEqual("Terminated", successor.status[0])


class TestDebtorByCase(unittest.TestCase):
    def test_transfer_mints_to_the_transferee_not_the_author(self):
        h = S.transfer_history()
        a1 = h.norm_events()[0]
        self.assertEqual("A", a1.author)
        minted = h.mint(a1)
        self.assertEqual(1, len(minted))
        self.assertEqual("B", minted[0].debtor)
        self.assertEqual("x", minted[0].subject)
        self.assertEqual("B", h.custodian("x"))

    def test_create_mints_to_the_author(self):
        h = History(S.seed_from({
            "x": S.commitment("x"),
            "auth:mk": PAuth(S.creating("mk", [S.commitment("k")])),
        }, debtor="P0"))
        h.norm("a1", "auth:mk", author="A")
        minted = h.mint(h.norm_events()[0])
        self.assertEqual(["A"], [q.debtor for q in minted])
        self.assertEqual("A", h.custodian(standing_tag(1, 0)))

    def test_supersede_mints_to_the_author_even_from_a_third_party(self):
        h = S.third_party_history()
        a1 = h.norm_events()[0]
        self.assertEqual("C", a1.author)
        self.assertEqual("A", h.root("q0:x").debtor)     # disposed episode's debtor
        self.assertEqual(["C"], [q.debtor for q in h.mint(a1)])

    def test_creditor_is_the_authors_stage_in_every_case(self):
        for h in (S.transfer_history(), S.supersession_history(),
                  S.third_party_history()):
            a1 = h.norm_events()[0]
            for q in h.mint(a1):
                self.assertEqual((a1.author, a1.tau), q.creditor)


class TestSampledCheckerIsNotAProof(unittest.TestCase):
    def test_the_checker_refutes_a_known_bad_demand(self):
        d = S.always_closed()
        q = S.AnsRoot("q0:x", ("P0", 0), "A", "x", d, S.GENESIS, 0)
        self.assertTrue(sampled_episode_demand_violations(d, S.sample_for(q)))

    def test_passing_the_checker_is_not_universal_D1(self):
        """A demand monotone on one sample and non-monotone off it passes the
        narrow probe and fails the wider one. The specification assumes D1
        universally; this harness can only refute, never establish."""
        from ri_core import ACCOUNT_FOR_SUCCESSION, DemandCode, Digest, Response

        def run(root, rs, cited):
            if any(r.id == "rho:hidden" for r in rs):
                return False
            return ACCOUNT_FOR_SUCCESSION.run(root, rs, cited)

        sneaky = DemandCode("MonotoneOnlyHere", run)
        q = S.AnsRoot("q0:x", ("P0", 0), "A", "x", sneaky, S.GENESIS, 0)

        narrow = S.sample_for(q)
        self.assertEqual([], sampled_episode_demand_violations(sneaky, narrow))

        hidden = Response("rho:hidden", frozenset([q.id]), frozenset(["a3"]), 4)
        wider = S.EpisodeDemandSample(
            q, narrow.responses + (hidden,),
            {**narrow.cited, "a3": Digest(1, "A", None, frozenset())})
        self.assertTrue(any(v[0] == "D1" for v in
                            sampled_episode_demand_violations(sneaky, wider)))


if __name__ == "__main__":
    unittest.main()
