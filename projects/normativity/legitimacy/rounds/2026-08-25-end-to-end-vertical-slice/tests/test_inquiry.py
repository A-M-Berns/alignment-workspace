"""The return loop, one invariant at a time.

The hypothesis under test is that inquiry closes the loop **without becoming a
second reasoner**: no new historical event kind, the only durable epistemic
return an ordinary `ReasonOcc`, and the only mover of standing an ordinary
licensed `NormEvent`.

The six snapshots the loop passes through are named `T0`–`T5` below and are
asserted separately, because the interesting content of the round is that the
intermediate states are distinguishable at all.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import inquiry
import li
import toy
from epistemic import (SettlementReading, SettlementSemantics, pc_worlds,
                       stage_satisfiable)
from inquiry import (PROBE, WAIT, InquiryNeed, ReasonProposal,
                     ServiceCertificate, certifiable, settled_facts,
                     valid_cert)
from pipeline import operative_projection
from standing import values_projection
from toy import J0_STANDING, J1_STANDING, V0_STANDING, V1_STANDING, Trajectory


class T0_NeedIsDerivedAndInert(unittest.TestCase):
    """A real charged result yields a need, and deriving it changes nothing."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.run = self.traj.day(0)

    def test_the_need_comes_from_the_real_charged_result(self):
        need = self.traj.need(self.run)
        self.assertIsInstance(need, InquiryNeed)
        self.assertEqual(need.pressure.sharp, self.run.charged.sharp)
        self.assertEqual(need.pressure.charge, self.run.charged.charge)
        self.assertGreater(need.pressure.sharp, Q(0))

    def test_the_need_names_the_force_bearing_standing(self):
        need = self.traj.need(self.run)
        self.assertEqual(need.ref.subject, J0_STANDING)
        self.assertEqual(need.pressure.standing_id, J0_STANDING)

    def test_deriving_it_appends_nothing(self):
        before = (self.traj.history.now,
                  [s.id for s in self.traj.history.settlements()],
                  [e.id for e in self.traj.history.reasons()],
                  [a.id for a in self.traj.history.norm_events()])
        self.traj.need(self.run)
        self.traj.need(self.run)
        after = (self.traj.history.now,
                 [s.id for s in self.traj.history.settlements()],
                 [e.id for e in self.traj.history.reasons()],
                 [a.id for a in self.traj.history.norm_events()])
        self.assertEqual(before, after)

    def test_deriving_it_moves_no_standing_and_no_allowance(self):
        std = dict(self.traj.history.std())
        remaining = self.traj.account.remaining
        self.traj.need(self.run)
        self.assertEqual(std, self.traj.history.std())
        self.assertEqual(remaining, self.traj.account.remaining)

    def test_no_need_where_there_is_no_pressure(self):
        """An inert injunction carries no liability, so nothing is unresolved."""
        import variants as v
        run = v.inert_injunction()
        need = inquiry.derive_need(run, toy.inquiry_ref("s:inert"), "q0")
        self.assertIsNone(need)

    def test_no_need_once_the_specification_is_serviced(self):
        traj = Trajectory().stage_a().stage_b()
        run = traj.day(1)
        self.assertIsNone(traj.need(run), "serviced, so nothing is needed")


class T1_ActionGoesThroughTheEnvironment(unittest.TestCase):
    """An ordinary action and a raw outcome. No oracle, no epistemic effect."""

    def setUp(self):
        self.traj = Trajectory().stage_a()

    def test_gamma_is_history_relational_and_set_valued(self):
        out = self.traj.gamma((), PROBE)
        self.assertIsInstance(out, tuple)
        self.assertGreaterEqual(len(out), 1, "P+ is nonempty")

    def test_the_probe_is_recorded_as_a_receipt(self):
        outcome, receipt = self.traj.act(PROBE)
        self.assertEqual(receipt.action, PROBE)
        self.assertEqual(receipt.outcome_id, outcome.id)
        self.assertEqual(self.traj.log.receipts, [receipt])

    def test_the_raw_outcome_alone_changes_no_ledger(self):
        before = self.traj.history.now
        self.traj.act(PROBE)
        self.assertEqual(self.traj.history.now, before)
        self.assertEqual([s.id for s in self.traj.history.settlements()], [])

    def test_and_eliminates_no_world(self):
        baseline = len(pc_worlds(self.traj.stage(), ()))
        self.traj.act(PROBE)
        self.assertEqual(len(pc_worlds(self.traj.stage(), ())), baseline)

    def test_the_interaction_log_is_not_the_record(self):
        """It is the environment's side; RI never reads it."""
        self.traj.act(PROBE)
        self.assertTrue(self.traj.log.receipts)
        self.assertEqual(self.traj.history.now, 2, "still just stage A")


class T2_SettlementMovesEpistemicsAndNothingElse(unittest.TestCase):
    """The settlement changes `Sigma` before any reason exists."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.before_worlds = len(pc_worlds(self.traj.stage(), ()))
        outcome, receipt = self.traj.act(PROBE)
        self.reading = self.traj.settle_outcome(outcome, receipt)

    def test_the_stage_grew(self):
        stage = self.traj.stage()
        for phi in self.reading.sentences:
            self.assertIn(phi, stage.sentences())

    def test_worlds_were_eliminated(self):
        self.assertLess(len(pc_worlds(self.traj.stage(), ())),
                        self.before_worlds)

    def test_no_reason_exists_yet(self):
        self.assertEqual([e.id for e in self.traj.history.reasons()], [])

    def test_no_standing_changed(self):
        self.assertEqual(values_projection(self.traj.history.std()),
                         ((V0_STANDING, "v0"),))
        self.assertEqual([sid for sid, _ in
                          operative_projection(self.traj.history.std())],
                         [J0_STANDING])

    def test_the_reading_froze_its_provenance(self):
        self.assertEqual(self.reading.provenance[1], PROBE)
        self.assertEqual(self.reading.provenance[0], self.reading.of_outcome)

    def test_sem_L_is_blind_to_the_provenance(self):
        """`sem_L` returns sentences; the action is not among them."""
        sentences = self.traj.sem.sem("l:trial")
        self.assertEqual(tuple(sentences), tuple(self.reading.sentences))
        self.assertNotIn(PROBE, [repr(s) for s in sentences])


class T2b_ServiceIsCertifiable(unittest.TestCase):
    """The settlement supports a valid diagnostic certificate."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        outcome, receipt = self.traj.act(PROBE)
        self.traj.settle_outcome(outcome, receipt)
        self.facts = self.traj.facts()

    def test_a_certificate_exists_and_the_judge_accepts_it(self):
        cert = self.traj.certify()
        self.assertIsInstance(cert, ServiceCertificate)
        self.assertTrue(valid_cert(self.traj.spec, self.facts, cert))
        self.assertTrue(certifiable(self.traj.spec, self.facts))

    def test_the_certificate_cites_settlements(self):
        cert = self.traj.certify()
        self.assertEqual(cert.cited, ("l:trial",))

    def test_certifying_appends_no_reason_and_no_event(self):
        before = self.traj.history.now
        self.traj.certify()
        self.assertEqual(self.traj.history.now, before)
        self.assertEqual([e.id for e in self.traj.history.reasons()], [])

    def test_historical_service_persists_under_extension(self):
        """`ValidCert(sigma, L, kappa) => ValidCert(sigma, L ++ L', kappa)`."""
        cert = self.traj.certify()
        self.traj.sem.admit(SettlementReading(
            "l:later", "o:later", (li.Atom("something-else"),), "unrelated"))
        self.traj.history.settle("l:later")
        self.assertTrue(valid_cert(self.traj.spec, self.traj.facts(), cert))

    def test_the_specification_is_conclusion_neutral(self):
        """The opposite branch of the experiment is equally adequate service."""
        sem = SettlementSemantics()
        sem.admit(SettlementReading(
            "l:neg", "o:probe", (li.Neg(self.traj.X0.luv.gt(Q(1, 3))),),
            "the trial came back the other way",
            provenance=("o:probe", PROBE, 0)))
        facts = settled_facts(["l:neg"], sem)
        self.assertTrue(certifiable(self.traj.spec, facts))


class T3_AssessmentReturnsAReasonAndNothingElse(unittest.TestCase):

    def setUp(self):
        self.traj = Trajectory().stage_a()
        outcome, receipt = self.traj.act(PROBE)
        self.traj.settle_outcome(outcome, receipt)
        self.traj.certify()

    def test_the_canonical_proposal_is_admitted(self):
        proposal = self.traj.propose_revaluation()
        self.assertTrue(self.traj.assessment.admits(
            toy.inquiry_ref(), self.traj.certificate, self.traj.facts(),
            proposal))

    def test_a_proposal_grounded_outside_the_certificate_is_refused(self):
        bad = ReasonProposal("e:ungrounded", frozenset(),
                             frozenset(["l:elsewhere"]), li.Atom("x"))
        self.assertFalse(self.traj.assessment.admits(
            toy.inquiry_ref(), self.traj.certificate, self.traj.facts(), bad))
        self.assertFalse(self.traj.assess_and_append(bad))
        self.assertEqual([e.id for e in self.traj.history.reasons()], [])

    def test_an_ungrounded_proposal_is_refused(self):
        bad = ReasonProposal("e:floating", frozenset(), frozenset(),
                             li.Atom("x"))
        self.assertFalse(self.traj.assess_and_append(bad))

    def test_assessment_is_conclusion_neutral(self):
        """The opposite target on the same grounds is equally admissible."""
        other = ReasonProposal("e:other", frozenset(), frozenset(["l:trial"]),
                               li.Atom("v0-should-stand"))
        self.assertTrue(self.traj.assessment.admits(
            toy.inquiry_ref(), self.traj.certificate, self.traj.facts(), other))

    def test_appending_the_reason_moves_no_standing(self):
        std = dict(self.traj.history.std())
        self.assertTrue(self.traj.assess_and_append(
            self.traj.propose_revaluation()))
        self.assertEqual([e.id for e in self.traj.history.reasons()],
                         ["e:revalue"])
        self.assertEqual(std, self.traj.history.std())
        self.assertEqual(values_projection(self.traj.history.std()),
                         ((V0_STANDING, "v0"),))


class T4_T5_TheCanonicalTrajectoryIsUnchanged(unittest.TestCase):
    """Reaching stage B through inquiry produces the same record as before.

    This is the round's strongest result: the loop adds **no** historical
    event, so the `tau` of every step, every minted standing id and both
    downstream theorems are exactly what they were.
    """

    def setUp(self):
        self.traj = Trajectory().stage_a().stage_b()

    def test_the_record_is_the_canonical_one(self):
        self.assertEqual(self.traj.history.now, 5)
        self.assertEqual([s.id for s in self.traj.history.settlements()],
                         ["l:trial"])
        self.assertEqual([e.id for e in self.traj.history.reasons()],
                         ["e:revalue"])
        self.assertEqual([(a.id, a.tau) for a in self.traj.history.norm_events()],
                         [("a:value", 1), ("a:force", 2), ("a:revalue", 5)])

    def test_value_revision_is_not_operative_revision(self):
        std = self.traj.history.std()
        self.assertEqual(values_projection(std), ((V1_STANDING, "v1"),))
        self.assertEqual(std[V0_STANDING].kind, "Terminated")
        self.assertEqual([sid for sid, _ in operative_projection(std)],
                         [J0_STANDING], "J0 is untouched")

    def test_the_compiled_fragment_still_names_the_superseded_quantity(self):
        run = self.traj.day(1)
        self.assertTrue(any("X[v0:q]" in repr(c) for c in run.coords))

    def test_only_stage_C_moves_the_injunction(self):
        self.traj.stage_c()
        std = self.traj.history.std()
        self.assertEqual([sid for sid, _ in operative_projection(std)],
                         [J1_STANDING])
        self.assertEqual(std[J0_STANDING].status[1], "a:reforce")

    def test_RI_is_good_at_every_state(self):
        self.traj.stage_c()
        for t in range(self.traj.history.now + 1):
            self.assertTrue(self.traj.history.good(t), f"state {t}")


class PolicyParametricity(unittest.TestCase):
    """Same semantics, different policy, different trajectory."""

    def test_probe_services_and_wait_does_not(self):
        probed = Trajectory().stage_a().stage_b(policy=inquiry.probe_policy)
        waited = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        self.assertTrue(certifiable(probed.spec, probed.facts()))
        self.assertFalse(certifiable(waited.spec, waited.facts()))

    def test_the_records_differ(self):
        probed = Trajectory().stage_a().stage_b(policy=inquiry.probe_policy)
        waited = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        self.assertEqual(values_projection(probed.history.std()),
                         ((V1_STANDING, "v1"),))
        self.assertEqual(values_projection(waited.history.std()),
                         ((V0_STANDING, "v0"),))

    def test_the_service_semantics_is_the_same_object(self):
        probed = Trajectory().stage_a().stage_b(policy=inquiry.probe_policy)
        waited = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        self.assertEqual(probed.spec.spec_id, waited.spec.spec_id)

    def test_waiting_still_acts(self):
        """A policy that waits is still interacting, just uninformatively."""
        waited = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        self.assertTrue(waited.log.receipts)
        self.assertEqual(waited.log.receipts[0].action, WAIT)


class ServiceDoesNotFactorThroughPC(unittest.TestCase):
    """The acceptance criterion: same `PC(Sigma)`, different service verdict."""

    def setUp(self):
        import variants as v
        self.X = v.x0()
        self.fx = inquiry.provenance_fixture(self.X.luv, Q(1, 3), Q(2, 3))

    def test_the_two_ledgers_denote_the_same_sentences(self):
        self.assertEqual(self.fx["good"].sem("l:same"),
                         self.fx["bad"].sem("l:same"))

    def test_and_induce_the_same_worlds(self):
        import variants as v
        from epistemic import Stage
        good = Stage.of(v._chain(self.X), self.fx["good"].entries(["l:same"]))
        bad = Stage.of(v._chain(self.X), self.fx["bad"].entries(["l:same"]))
        self.assertEqual(set(good.sentences()), set(bad.sentences()))
        self.assertEqual(pc_worlds(good, ()), pc_worlds(bad, ()))

    def test_but_service_succeeds_on_one_and_fails_on_the_other(self):
        good = settled_facts(["l:same"], self.fx["good"])
        bad = settled_facts(["l:same"], self.fx["bad"])
        self.assertTrue(certifiable(self.fx["spec"], good))
        self.assertFalse(certifiable(self.fx["spec"], bad))

    def test_so_service_is_not_a_function_of_the_epistemic_quotient(self):
        """Stated as the non-factorization it is."""
        good = settled_facts(["l:same"], self.fx["good"])
        bad = settled_facts(["l:same"], self.fx["bad"])
        same_quotient = (self.fx["good"].sem("l:same")
                         == self.fx["bad"].sem("l:same"))
        different_verdict = (certifiable(self.fx["spec"], good)
                             != certifiable(self.fx["spec"], bad))
        self.assertTrue(same_quotient and different_verdict)


class NoInquiryOperationMintsAllowance(unittest.TestCase):
    """The Level-II seam stays shut: nothing here can increase the account."""

    def test_the_whole_loop_never_raises_the_account(self):
        traj = Trajectory()
        traj.stage_a()
        start = traj.account.remaining
        ceiling = traj.account.lifetime_ceiling
        granted = traj.account.capital
        traj.stage_b()
        traj.stage_c()
        self.assertLessEqual(traj.account.remaining, start)
        self.assertEqual(traj.account.lifetime_ceiling, ceiling)
        self.assertEqual(traj.account.capital, granted)

    def test_no_inquiry_object_exposes_a_grant(self):
        """A structural check: none of the loop's types has such an operation."""
        for obj in (inquiry.InquiryRef, inquiry.InquiryNeed,
                    inquiry.ServiceCertificate, inquiry.ServiceSpec,
                    inquiry.AssessmentCode, inquiry.ReasonProposal,
                    inquiry.SettledFact, inquiry.InteractionLog):
            names = [n for n in dir(obj) if not n.startswith("_")]
            for bad in ("grant", "replenish", "spend", "credit", "fund"):
                self.assertNotIn(bad, names, f"{obj.__name__}.{bad}")

    def test_servicing_does_not_make_a_withheld_date_affordable(self):
        """Service answers a question; it does not pay for force."""
        import safety
        traj = Trajectory(capital=Q(6))
        traj.stage_a()
        traj.stage_b()
        self.assertLessEqual(traj.account.remaining, Q(6))


class InquiryIdentity(unittest.TestCase):
    """Q1: is `(StandingId, InquiryKey)` the right key?"""

    def test_the_reference_is_keyed_by_standing_not_episode(self):
        ref = toy.inquiry_ref()
        self.assertEqual(ref.subject, J0_STANDING)
        self.assertNotIn("q0:", ref.subject)

    def test_the_episode_is_carried_by_the_need_rather_than_the_reference(self):
        traj = Trajectory().stage_a()
        need = traj.need(traj.day(0), episode="q0:auth:force")
        self.assertEqual(need.episode, "q0:auth:force")
        self.assertEqual(need.ref, toy.inquiry_ref())

    def test_the_same_reference_survives_a_change_of_episode(self):
        """Which is the case that decides the key.

        The matter under inquiry is a property of the standing. Handing the
        need a different current episode leaves the reference identical, so an
        inquiry does not lose its identity when custody moves.
        """
        traj = Trajectory().stage_a()
        run = traj.day(0)
        a = traj.need(run, episode="q0:auth:force")
        b = traj.need(run, episode="q-after-transfer")
        self.assertEqual(a.ref, b.ref)
        self.assertNotEqual(a.episode, b.episode)


if __name__ == "__main__":
    unittest.main()
