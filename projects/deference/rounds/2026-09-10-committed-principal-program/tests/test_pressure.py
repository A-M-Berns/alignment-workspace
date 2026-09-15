"""The pressure pass on the 2026-09-09 round (`PRESSURE.md`, P1–P6)."""
from __future__ import annotations

import unittest
from dataclasses import replace
from fractions import Fraction as F

from src import ecosystem as eco
from src import market as mk
from src import program as pg
from src import protocol as pr
from src.fixtures import W0, W1, W2, W3, WORLDS
from src.log import (BIND, COMMIT, DELIB, DISPOSE, DISPOSE_W, ISSUE, RAISE, ROUTE, ROUTE_OPEN,
                     SESSION_OPEN, A, Log, P, S, T)

READING = eco.PRINCIPALS["reading"]


def frame(w, z=READING, cfg=eco.Config()):
    return eco.Frame(w, z, cfg)


class TestP1_ResolverAndPropagation(unittest.TestCase):
    """What `activated_iff` / `propagate_segment_eq` use: issued occurrences never
    un-issue, a valid resolving event names an already-issued occurrence, ports are
    occurrences, and the first valid resolver is stable.  The cases below probe each."""

    def test_two_valid_commits_first_binds(self):
        """A late reason after the first commit lets a second commit re-execute validly
        with a different vector; the account is the first receipt (the theory's "first
        answer binds", `fates_subst_of_terminal`), the second never enters."""
        log = frame(W0, eco.PRINCIPALS["recommit"]).log(eco.ADVISORS["late_honest"])
        commits = [e.index for e in log if e.kind == COMMIT]
        self.assertEqual(len(commits), 2)
        self.assertTrue(pr.valid_answer(log, commits[0], 0))
        self.assertTrue(pr.valid_answer(log, commits[1], 0))
        self.assertNotEqual(log[commits[0]].payload["V"], log[commits[1]].payload["V"])
        rc = pr.answer_receipt(pr.account_at(log, len(log), 0))
        self.assertEqual(rc["event"], commits[0])
        self.assertEqual(eco.Frame.V(log), {"a": F(1, 2), "b": F(1, 2)})

    def test_commit_before_issuance_is_not_a_receipt(self):
        log = Log()
        log.append(0, P, COMMIT, {"occ": 0, "key": "kP", "V": {"a": F(1), "b": F(0)},
                                  "proc": {"issue": 0, "prefix": 0}}, warrant=BIND)
        log.append(0, P, ISSUE, {"req": {"role": P, "matter": "alpha", "menu": eco.CANDS, "slot": 1,
                                         "tau": ""}, "key": "kP", "program": pg.CONST})
        self.assertFalse(pr.valid_answer(log, 0, 0))
        self.assertEqual(pr.account_at(log, 2, 0)[0], "live")

    def test_commit_at_unissued_occurrence(self):
        log = frame(W0).log(eco.ADVISORS["silent"])
        bad = Log(list(log.events))
        bad.append(6, P, COMMIT, {"occ": 1, "key": "kP", "V": {"a": F(1), "b": F(0)},
                                  "proc": {"issue": 0, "prefix": len(bad)}}, warrant=BIND)
        self.assertFalse(pr.valid_answer(bad, len(bad) - 1, 1))
        self.assertEqual(pr.boundary(bad, len(bad))["portCount"], 1)

    def test_delegation_revoked_before_commit(self):
        w = eco.World("revoke", delegate_at=1, revoke_at=3)
        C, cl, log = eco.activation(frame(w), eco.ADVISORS["delegate_commit"])
        adv = log.first(lambda e: e.kind == COMMIT and e.author == A)
        self.assertIsNotNone(adv)
        self.assertFalse(pr.valid_answer(log, adv.index, 0))
        self.assertEqual(eco.Frame.author(log), P)
        self.assertTrue(cl[3][0])
        self.assertFalse(C)   # the advisor's commit is a write under the strict reading
        C2, _, _ = eco.activation(frame(w, cfg=eco.Config(clause6="tolerant")), eco.ADVISORS["delegate_commit"])
        self.assertTrue(C2)

    def test_key_theft_break_and_repair(self):
        """BREAK (2026-09-09): the registry held keys alone, so a commit authored by the
        advisor under the principal's key was an authenticated receipt.  REPAIR: the
        registry binds each key to the party that registered it."""
        log = frame(W0).log(eco.ADVISORS["stolen_key"])
        adv = log.first(lambda e: e.kind == COMMIT and e.author == A)
        self.assertEqual(adv.payload["key"], eco.PRINCIPAL_KEY)
        old_reading = adv.payload["key"] in {k for _, k in pr.holders(log.prefix(adv.index), BIND)}
        self.assertTrue(old_reading)
        self.assertFalse(pr.valid_answer(log, adv.index, 0))
        self.assertEqual(eco.Frame.author(log), P)

    def test_delegate_binds_only_the_program_output(self):
        """Under re-execution a delegated key binds only the mandated program's output:
        the advisor's own vector under the delegated key is void."""
        w = eco.World("delegate", delegate_at=1)
        log = frame(w).log(eco.ADVISORS["advisor_commit"])
        adv = log.first(lambda e: e.kind == COMMIT and e.author == A)
        self.assertFalse(pr.valid_answer(log, adv.index, 0))
        log2 = frame(w).log(eco.ADVISORS["delegate_commit"])
        adv2 = log2.first(lambda e: e.kind == COMMIT and e.author == A)
        self.assertTrue(pr.valid_answer(log2, adv2.index, 0))


class TestP2_PinnedBranches(unittest.TestCase):
    def _verdicts(self, w, J, pinned_actual, cfg):
        fr = frame(w, cfg=cfg)
        log = fr.log(eco.ADVISORS["honest"])
        m = eco.commit_index(log) + 1
        out = []
        for k in range(1, min(m, len(log)) + 1):
            actual = pr.cov_state(log, k, eco.PROTECTED, cfg.independence, cfg.robust_registrar)
            if pinned_actual:
                cfs = [actual for _ in J]
            else:
                cfs = [pr.cov_state(fr.log(eco.ADVISORS[j]), k, eco.PROTECTED, cfg.independence,
                                    cfg.robust_registrar) for j in J]
            out.append(pr.robust_open_actual(actual, cfs))
        return all(out)

    def test_advisor_only_interventions_cannot_be_hidden_by_pinning(self):
        """For the 2026-09-09 class `J = {silent, honest}`, every world gives the same
        all-snapshots verdict whether the branches are re-simulated or pinned to the
        actual branch: the advisor's events do not touch routes, so the counterfactual
        half of Robust Openness is empty for that `J`.  (Exhaustive over the worlds.)"""
        cfg = eco.Config(J=("silent", "honest"))
        for w in list(WORLDS) + [eco.World("destroy", raise_time=1, destroy_route_at=1),
                                  eco.World("reopen", raise_time=1, destroy_route_at=1, reopen_route_at=3)]:
            self.assertEqual(self._verdicts(w, cfg.J, True, cfg), self._verdicts(w, cfg.J, False, cfg), w.name)

    def test_jam_branch_pinning_hides_a_failure(self):
        """BREAK: with the coverage-affecting intervention `jam` in `J` and a fragile
        registrar, the re-simulated branch is closed at the slot (live concern, no
        route exercised) while the actual branch is open; pinning the actual branch as
        the counterfactual reports openness.  That is the model declaring its own
        openness.  REPAIR (Lean): the branches are declared log transforms, not data."""
        cfg = eco.Config(J=("silent", "honest", "jam"), robust_registrar=False)
        w = W1
        self.assertTrue(self._verdicts(w, cfg.J, True, cfg))
        self.assertFalse(self._verdicts(w, cfg.J, False, cfg))
        C, cl, _ = eco.activation(frame(w, cfg=cfg), eco.ADVISORS["honest"])
        self.assertFalse(cl[5][0])

    def test_robust_registrar_survives_the_jam_branch(self):
        """With a robust registrar the jam branch is open and clause 5 is nonvacuous."""
        cfg = eco.Config(J=("silent", "honest", "jam"), robust_registrar=True)
        C, cl, _ = eco.activation(frame(W1, cfg=cfg), eco.ADVISORS["honest"])
        self.assertTrue(cl[5][0] and C)
        # the realized jam under a fragile registrar voids by the barrier, not by openness
        cfg2 = eco.Config(J=("silent", "honest", "jam"), robust_registrar=False)
        C2, cl2, log2 = eco.activation(frame(W1, cfg=cfg2), eco.ADVISORS["jam"])
        self.assertFalse(C2)


class TestP3_ContentReferences(unittest.TestCase):
    def test_duplicate_reasons_keep_blindness(self):
        fr = frame(W0)
        pairs = eco.prohibited_pairs(("dup",))
        self.assertTrue(fr.blind(fr.R, pairs))
        self.assertEqual(fr.V(fr.log(eco.ADVISORS["dup"])), fr.V(fr.log(eco.ADVISORS["honest"])))

    def test_position_embedding_content_breaks_blindness(self):
        """A reason whose content is the log position: inserting a prohibited event
        shifts it, the traces differ, and the pair is no longer "differing only through
        a prohibited channel".  Blindness needs content intrinsic to the admitted
        history."""
        fr = frame(W0)
        pairs = [(eco.ADVISORS["pos_ref"], eco.with_prohibited(eco.ADVISORS["pos_ref"], k, t=1))
                 for k in sorted(eco.PROHIBITED)]
        self.assertFalse(fr.blind(fr.R, pairs))
        # the effect is mediated: the payload is still the program on the trace
        for q, q2 in pairs:
            for l in (fr.log(q), fr.log(q2)):
                self.assertEqual(fr.V(l), pg.evaluate(pg.READING, fr.R(l), eco.CANDS))

    def test_prefix_hash_settlement_breaks_blindness(self):
        w = eco.World("hash", raise_time=4, flood=3, engine_settles_at=4, engine_settle_content="pos")
        fr = frame(w)
        pairs = eco.prohibited_pairs(("honest",))
        self.assertFalse(fr.blind(fr.R, pairs))
        w2 = replace(w, engine_settle_content="plain")
        self.assertTrue(frame(w2).blind(frame(w2).R, pairs))


class TestP4_RepFaithfulVacuity(unittest.TestCase):
    def test_unnameable_scope_is_vacuous(self):
        cfg = eco.Config(gamma_eval=("c9",))
        C, cl, log = eco.activation(frame(W2, cfg=cfg), eco.ADVISORS["honest"])
        self.assertTrue(cl[7][0])
        self.assertTrue(eco.rep_faithful(log, ("c9",)))
        # the protected concern of the real scope is live at the slot and the verdict
        # under the real scope is void: the theorem is scope-relative
        C2, _, _ = eco.activation(frame(W2), eco.ADVISORS["honest"])
        self.assertFalse(C2)

    def test_route_forgery_break_and_repair(self):
        """BREAK (2026-09-09): representation was any `ROUTE` event, so the advisor could
        write one and clear the barrier.  REPAIR: representation is the registrar's
        move."""
        log = frame(W2).log(eco.ADVISORS["route_forger"])
        forged = log.first(lambda e: e.kind == ROUTE and e.author == A)
        self.assertIsNotNone(forged)
        old_reading = any(e.kind == ROUTE and e.payload["concern"] == eco.PROTECTED
                          for e in log.prefix(eco.commit_index(log)))
        self.assertTrue(old_reading)
        close = log.first(lambda e: e.kind == "SESSION_CLOSE")
        self.assertTrue(pr.live(pr.cov_state(log, close.index, eco.PROTECTED)))
        self.assertFalse(eco.activation(frame(W2), eco.ADVISORS["route_forger"])[0])

    def test_late_registered_route(self):
        """A route destroyed while the concern is live and registered again later: the
        snapshots in between fail openness, and `Covered` keeps its meaning."""
        w = eco.World("reopen", raise_time=1, destroy_route_at=1, reopen_route_at=3)
        C, cl, log = eco.activation(frame(w), eco.ADVISORS["honest"])
        self.assertFalse(cl[5][0])
        k = log.first(lambda e: e.kind == RAISE).index + 1
        self.assertFalse(pr.covered(pr.cov_state(log, k, eco.PROTECTED)))
        k2 = log.first(lambda e: e.kind == ROUTE_OPEN and e.index > 1).index + 1
        self.assertTrue(pr.covered(pr.cov_state(log, k2, eco.PROTECTED)))


class TestP5_StrictVersusTolerant(unittest.TestCase):
    def test_table(self):
        strict, tolerant = eco.Config(clause6="strict"), eco.Config(clause6="tolerant")
        diffs = {}
        for w in WORLDS:
            for n in eco.AUDITED:
                cs = eco.activation(frame(w, cfg=strict), eco.ADVISORS[n])[0]
                ct = eco.activation(frame(w, cfg=tolerant), eco.ADVISORS[n])[0]
                if cs != ct:
                    diffs[(w.name, n)] = (cs, ct)
        # tolerant certifies exactly the prohibited-event continuations on certified worlds
        self.assertEqual({k for k in diffs if k[0] == "w0"},
                         {("w0", n) for n in ("covert", "honest_covert", "early_write", "coerce",
                                              "side", "advisor_commit", "stolen_key", "delegate_commit")})
        self.assertTrue(all(cs is False and ct is True for cs, ct in diffs.values()))
        # and under tolerant the payload is the program's output whatever the write did
        for (wn, n), _ in diffs.items():
            w = next(x for x in WORLDS if x.name == wn)
            log = frame(w, cfg=tolerant).log(eco.ADVISORS[n])
            self.assertEqual(eco.Frame.V(log), pg.evaluate(pg.READING, eco.reason_trace(log), eco.CANDS))

    def test_eta_on_simulated_sequences(self):
        outs_s = mk.simulated_outcomes(eco.Config(clause6="strict"))
        outs_t = mk.simulated_outcomes(eco.Config(clause6="tolerant"))
        eta_s, eta_t = mk.eta_sequence(outs_s)[-1], mk.eta_sequence(outs_t)[-1]
        self.assertEqual(sum(1 - o for o in outs_s), 6)
        self.assertEqual(sum(1 - o for o in outs_t), 0)
        self.assertEqual(eta_s, F(7, 22))
        self.assertEqual(eta_t, F(1, 22))


class TestP6_TypedRuleAttacks(unittest.TestCase):
    def test_launder_through_own_deliberation(self):
        """(a) `DELIB("considered c1")` with no representation, then `DISPOSE` on it."""
        w = eco.World("fake", raise_time=4, flood=3)
        for rule, expect in (("typed", True), ("typed+", False), ("strict", False)):
            C, cl, log = eco.activation(frame(w, eco.PRINCIPALS["fake_delib"], eco.Config(independence=rule)),
                                        eco.ADVISORS["honest"])
            self.assertEqual(C, expect, rule)

    def test_launder_through_engine_at_request(self):
        """(b) the engine settles the external fact at the principal's request."""
        w = eco.World("request", raise_time=4, flood=3)
        for rule, expect in (("typed", True), ("typed+", False)):
            C, cl, log = eco.activation(frame(w, eco.PRINCIPALS["requester"], eco.Config(independence=rule)),
                                        eco.ADVISORS["honest"])
            self.assertEqual(C, expect, rule)
            d = log.first(lambda e: e.kind == DISPOSE)
            self.assertEqual(pr.valid_dispose(log, d, rule), expect)

    def _two_occurrence_log(self, first_commit_valid):
        req = lambda slot: {"role": P, "matter": "alpha", "menu": eco.CANDS, "slot": slot, "tau": ""}
        log = Log()
        log.append(0, P, ISSUE, {"req": req(1), "key": "kP", "program": pg.CONST})
        log.append(0, S, ROUTE_OPEN, "r0")
        if first_commit_valid:
            log.append(1, S, SESSION_OPEN, 1)
        c0 = log.append(1, P, COMMIT, {"occ": 0, "key": "kP", "V": {"a": F(1, 2), "b": F(1, 2)},
                                       "proc": {"issue": 0, "prefix": len(log)}}, warrant=BIND)
        log.append(2, P, ISSUE, {"req": req(2), "key": "kP", "program": pg.CONST})
        log.append(3, T, RAISE, eco.PROTECTED)
        d = log.append(4, P, DISPOSE, eco.PROTECTED, warrant=DISPOSE_W, refs=(c0.index,))
        return log, c0, d

    def test_launder_through_own_earlier_commit(self):
        """(c) a disposal grounded in a threshold of the principal's own earlier
        evaluation: observational of its move, admitted by `typed`; `typed+` admits it
        exactly when that evaluation was an activated answer — the strongest laundering
        the typed rule admits is a chain through activated evaluations."""
        log, c0, d = self._two_occurrence_log(first_commit_valid=True)
        self.assertTrue(pr.valid_answer(log, c0.index, 0))
        self.assertTrue(pr.valid_dispose(log, d, "typed"))
        self.assertTrue(pr.valid_dispose(log, d, "typed+"))
        self.assertFalse(pr.valid_dispose(log, d, "strict"))
        log2, c02, d2 = self._two_occurrence_log(first_commit_valid=False)
        self.assertFalse(pr.valid_answer(log2, c02.index, 0))
        self.assertTrue(pr.valid_dispose(log2, d2, "typed"))
        self.assertFalse(pr.valid_dispose(log2, d2, "typed+"))


if __name__ == "__main__":
    unittest.main()
