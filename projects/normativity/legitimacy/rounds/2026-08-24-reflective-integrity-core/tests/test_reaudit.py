"""The independent adversarial pass over the repaired signature.

Each case is the smallest finite history that would recreate one of the
failures the surviving red-team recap describes, run against the repaired
model. `TestConservation` sweeps every scenario at every state for `GC and AC`,
Fate Monotonicity, the trichotomy and TargetCoverage together.
"""
from __future__ import annotations

import unittest

from ri_core import (History, PAuth, Standing, Transfer, fresh_n, standing_tag,
                     standing_changes, superseding, targets_n, setting, ACTIVE,
                     SUSPENDED, issued_cohort, new_in_cohort)
import scenarios as S


FATE_ORDER = {"LiveNotDue": 0, "Due": 1, "Closed": 2}


def all_scenarios():
    return [S.transfer_history(), S.supersession_history(), S.split_history(),
            S.merge_history(), S.revocation_history(), S.suspension_history(),
            S.force_history(), S.third_party_history(),
            S.repeated_transfer_history(), S.licensed_inference_history(),
            S.chain_history(3)]


class TestConservation(unittest.TestCase):
    def test_good_holds_at_every_state_of_every_scenario(self):
        for h in all_scenarios():
            for t in range(h.now + 1):
                self.assertTrue(h.grounding_conservation(t))
                self.assertEqual([], h.answerability_conservation(t))

    def test_trichotomy_over_issued_roots(self):
        for h in all_scenarios():
            for t in range(h.now + 1):
                for q in h.roots(t):
                    flags = [h.closed(q, t),
                             h.live(q, t) and not h.due(q, t),
                             h.due(q, t)]
                    self.assertEqual(1, sum(flags), (q.id, t))

    def test_fate_monotonicity(self):
        for h in all_scenarios():
            for q in h.roots():
                seen = [FATE_ORDER[h.fate(q, t)] for t in range(h.now + 1)
                        if h.fate(q, t) != "NotIssued"]
                self.assertEqual(sorted(seen), seen, q.id)

    def test_closure_passes_through_due(self):
        """D2 forces the middle state: a root cannot go from live custody to
        closed without being `Due` at the state its disposer arrived in."""
        h = S.supersession_history()
        h.respond("rho0", roots=["q0:x"], cited=["a1"])
        fates = [h.fate(h.root("q0:x"), t) for t in range(h.now + 1)]
        self.assertEqual(["LiveNotDue", "Due", "Closed"], fates)

    def test_target_coverage(self):
        for h in all_scenarios():
            for a in h.norm_events():
                eff = h.effect(a)
                allowed = set(targets_n(eff)) | set(fresh_n(eff, a.tau))
                if isinstance(eff, Transfer):
                    allowed = set(fresh_n(eff, a.tau))   # Transfer writes nothing
                for x in set(h.std(a.tau)) | set(h.std(a.tau - 1)):
                    if standing_changes(h, a, x):
                        self.assertIn(x, allowed, (a.id, x))

    def test_roots_never_vanish(self):
        for h in all_scenarios():
            for t in range(h.now):
                self.assertTrue({q.id for q in h.roots(t)}
                                <= {q.id for q in h.roots(t + 1)})


class TestReAudit(unittest.TestCase):
    def test_ep_under_respond_with_an_uncited_response(self):
        """A Respond step naming a live root and citing nothing changes no
        fate; D2 is what makes that true rather than the step's own check."""
        h = S.suspension_history()
        before = h.custodian("x")
        h.respond("rho0", roots=["q0:x"], cited=[])
        self.assertEqual(before, h.custodian("x"))
        self.assertEqual([], h.answerability_conservation())

    def test_ep_under_a_create_at_the_same_index_as_a_supersede(self):
        """Both allocate index 0; different times keep them apart."""
        seed = S.seed_from({
            "x": S.commitment("x"),
            "auth:mk": PAuth(S.creating("mk", [S.commitment("k")])),
            "auth:sup": PAuth(superseding("sup", ["x"], [S.commitment("x2")])),
        }, debtor="A")
        h = History(seed)
        h.norm("a1", "auth:mk", author="A")
        h.norm("a2", "auth:sup", author="A")
        self.assertEqual({standing_tag(1, 0), standing_tag(2, 0)},
                         {x for x in h.std() if x.startswith("@")})
        self.assertEqual([], h.answerability_conservation())

    def test_strict_pre_state_evaluation(self):
        """The effect of `a` reads the state strictly before `a`, so an event
        cannot see itself. Superseding the very authority that licenses the
        event is admissible and does not change that event's own effect."""
        seed = S.seed_from({
            "x": S.commitment("x"),
            "auth:self": PAuth(superseding("self", ["auth:self"], [])),
        }, debtor="A")
        h = History(seed)
        h.norm("a1", "auth:self", author="A")
        a = h.norm_events()[0]
        self.assertEqual("Active", h.std(0)["auth:self"].kind)
        self.assertEqual("Terminated", h.std(1)["auth:self"].status[0])
        self.assertIsInstance(h.effect(a), Standing)
        self.assertEqual([], h.answerability_conservation())

    def test_self_licensing_is_impossible_without_g4_2(self):
        """`schemaRef` resolves in the strict pre-state and fresh ids are
        disjoint from it, so no event can be licensed by standing it creates.
        This is why the old `schemaRef not in fresh(effect a)` clause is gone."""
        for h in all_scenarios():
            for a in h.norm_events():
                self.assertNotIn(a.schema_ref, fresh_n(h.effect(a), a.tau))
                self.assertIn(a.schema_ref, h.std(a.tau - 1))

    def test_digest_stability_under_a_later_disposition(self):
        h = S.chain_history(2)
        a1 = [a for a in h.norm_events() if a.id == "a1"][0]
        early = h.digest(a1)
        h.respond("rho0", roots=["@q1.0"], cited=["a2"])
        self.assertEqual(early, h.digest(a1))
        self.assertEqual(frozenset(["q0:x"]), early.disposed)

    def test_source_closure(self):
        """The retained cohort lemma: a stage's issued cohort is fixed at
        issuance, because minting stamps the creditor with the event's own
        time."""
        for h in all_scenarios():
            for s in range(h.now + 1):
                for principal in {q.creditor[0] for q in h.roots()}:
                    self.assertEqual((), new_in_cohort(h, principal, s, h.now))

    def test_issued_cohort_members_stay_issued(self):
        h = S.chain_history(3)
        cohort = issued_cohort(h, "A", 1)
        self.assertEqual(["@q1.0"], [q.id for q in cohort])
        for t in range(1, h.now + 1):
            self.assertTrue({q.id for q in cohort} <= {q.id for q in h.roots(t)})


if __name__ == "__main__":
    unittest.main()
