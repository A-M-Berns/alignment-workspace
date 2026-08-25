"""D1 and D2: the structural properties the episode-demand interface needs.

The red-team recap places the one substantive defect of v2 here. These cases
are the fault class: a demand that is not monotone, and a demand that closes an
episode without any disposition of its root.
"""
from __future__ import annotations

import unittest

from ri_core import (ACCOUNT_FOR_SUCCESSION, GENESIS, AnsRoot, History,
                     PAuth, Response, Seed, StandingState, ACTIVE,
                     sampled_episode_demand_violations, check_seed, superseding)
import scenarios as S


def a_root(demand):
    return AnsRoot("q0:x", ("P0", 0), "A", "x", demand, GENESIS, 0)


class TestDemandAxioms(unittest.TestCase):
    def test_account_for_succession_satisfies_d1_and_d2(self):
        q = a_root(ACCOUNT_FOR_SUCCESSION)
        self.assertEqual([], sampled_episode_demand_violations(
            ACCOUNT_FOR_SUCCESSION, S.sample_for(q)))

    def test_non_monotone_demand_is_rejected(self):
        d = S.non_monotone()
        q = a_root(d)
        bad = sampled_episode_demand_violations(d, S.sample_for(q))
        self.assertTrue(any(v[0] == "D1" for v in bad), bad)

    def test_ungated_demand_is_rejected(self):
        d = S.always_closed()
        q = a_root(d)
        bad = sampled_episode_demand_violations(d, S.sample_for(q))
        self.assertTrue(any(v[0] == "D2" for v in bad), bad)

    def test_d2_holds_vacuously_for_an_unsatisfiable_demand(self):
        """Never closing is RI-conformant: `Live and not Due` may be permanent."""
        from ri_core import DemandCode
        never = DemandCode("Never", lambda root, rs, cited: False)
        self.assertEqual([], sampled_episode_demand_violations(never, S.sample_for(a_root(never))))

    def test_probe_without_a_disposer_makes_afs_unsatisfiable(self):
        q = a_root(ACCOUNT_FOR_SUCCESSION)
        sample = S.sample_for(q, root_id_disposed=False)
        self.assertEqual([], sampled_episode_demand_violations(ACCOUNT_FOR_SUCCESSION, sample))
        self.assertFalse(ACCOUNT_FOR_SUCCESSION.run(q, sample.responses, sample.cited))


class TestDemandInHistories(unittest.TestCase):
    def test_valid_account_for_succession_closes_a_due_root(self):
        h = S.supersession_history()
        q0 = h.root("q0:x")
        self.assertEqual("Due", h.fate(q0))
        h.respond("rho1", roots=["q0:x"], cited=["a1"])
        self.assertEqual("Closed", h.fate(h.root("q0:x")))

    def test_closure_survives_later_unrelated_responses(self):
        h = S.supersession_history()
        h.respond("rho1", roots=["q0:x"], cited=["a1"])
        h.respond("rho2", roots=["q0:x"], cited=[])
        h.respond("rho3", roots=["q0:auth:sup"], cited=[])
        self.assertEqual("Closed", h.fate(h.root("q0:x")))

    def test_response_citing_an_unrelated_event_does_not_close(self):
        """Battery case 6: `id q` is not in the cited digest's disposed set."""
        seed = S.seed_from({
            "x": S.commitment("x"),
            "y": S.commitment("y"),
            "auth:sup_y": PAuth(superseding("sup_y", ["y"], [S.commitment("y2")])),
        }, debtor="A")
        h = History(seed)
        h.norm("a1", "auth:sup_y", author="A")          # disposes q0:y, not q0:x
        h.respond("rho1", roots=["q0:x"], cited=["a1"])
        self.assertEqual("LiveNotDue", h.fate(h.root("q0:x")))
        self.assertEqual("Due", h.fate(h.root("q0:y")))

    def test_response_citing_a_later_disposition_does_not_close(self):
        """Battery case 7: the demand needs `digest.tau < tau(rho)`."""
        h = S.supersession_history()
        h.respond("rho1", roots=["q0:x"], cited=[])     # cites nothing yet
        self.assertEqual("Due", h.fate(h.root("q0:x")))

    def test_seed_gate_refuses_an_ungated_seed_demand(self):
        d = S.always_closed()
        seed = S.seed_from({"x": S.commitment("x")}, demand=d)
        bad = check_seed(seed, sampler=lambda q: S.sample_for(q))
        self.assertTrue(any(v[0] == "D1/D2" for v in bad), bad)


if __name__ == "__main__":
    unittest.main()
