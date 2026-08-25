"""The return loop, prosecuted.

The bar: **no arrow in the loop exists because a caller said it did.** So the
tests come in two halves — the six snapshots `T0`–`T5` that show the loop
running, and the attacks that show each seam refusing what it should.

Each attack names the layer that rejects it. That division of responsibility is
itself part of the result: the loop needs no authority of its own, because the
authority it would have needed already lives in Reflective Integrity.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import inquiry
import li
import toy
import variants as v
from epistemic import (RawOutcome, SettlementReading, SettlementSemantics,
                       Stage, pc_worlds)
from inquiry import (PROBE, WAIT, InquiryView, InteractionLog,
                     InteractionProvenance, InteractionReceipt,
                     InteractionRefused, ProvenanceRefused, ReasonProposal,
                     ServiceCertificate, SpecMismatch, admissible_assessment,
                     authenticate, certifiable, current_episode_for, execute,
                     read_and_admit, settled_facts, superseded_by_round,
                     valid_cert)
from pipeline import operative_projection, run_day
from standing import values_projection
from toy import J0_STANDING, J1_STANDING, V0_STANDING, V1_STANDING, Trajectory


# ===========================================================================
#  The loop runs
# ===========================================================================


class T0_NeedIsDerivedAndInert(unittest.TestCase):

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.run = self.traj.read_pressure(0)

    def test_the_need_comes_from_the_real_charged_result(self):
        need = self.traj.need(self.run)
        self.assertIsNotNone(need)
        self.assertGreater(need.pressure.sharp, Q(0))

    def test_the_episode_is_derived_and_belongs_to_the_subject(self):
        need = self.traj.need(self.run)
        root = self.traj.history.root(need.episode)
        self.assertEqual(root.subject, J0_STANDING)
        self.assertTrue(self.traj.history.current_episode(root))

    def test_the_authoritys_genesis_root_is_not_the_injunctions_episode(self):
        self.assertEqual(self.traj.history.root("q0:auth:force").subject,
                         "auth:force")
        self.assertNotEqual(self.traj.need(self.run).episode, "q0:auth:force")

    def test_deriving_it_appends_nothing_and_spends_nothing(self):
        before = (self.traj.history.now, self.traj.account.remaining)
        self.traj.need(self.run)
        self.assertEqual((self.traj.history.now, self.traj.account.remaining),
                         before)


class T1_ActionGoesThroughGamma(unittest.TestCase):

    def setUp(self):
        self.traj = Trajectory().stage_a()

    def test_the_raw_outcome_alone_changes_no_ledger_and_no_world(self):
        baseline = len(pc_worlds(self.traj.stage(), ()))
        before = self.traj.history.now
        self.traj.act(PROBE)
        self.assertEqual(self.traj.history.now, before)
        self.assertEqual(len(pc_worlds(self.traj.stage(), ())), baseline)

    def test_the_raw_outcome_alone_creates_no_service_and_no_reason(self):
        self.traj.act(PROBE)
        self.assertFalse(certifiable(self.traj.spec, self.traj.facts()))
        self.assertEqual([e.id for e in self.traj.history.reasons()], [])


class T2_SettlementMovesEpistemicsAndNothingElse(unittest.TestCase):

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.before_worlds = len(pc_worlds(self.traj.stage(), ()))
        outcome, receipt = self.traj.act(PROBE)
        self.reading = self.traj.settle_outcome(outcome, receipt)

    def test_worlds_were_eliminated(self):
        self.assertLess(len(pc_worlds(self.traj.stage(), ())),
                        self.before_worlds)

    def test_no_reason_and_no_standing_change(self):
        self.assertEqual([e.id for e in self.traj.history.reasons()], [])
        self.assertEqual(values_projection(self.traj.history.std()),
                         ((V0_STANDING, "v0"),))

    def test_the_provenance_is_authenticated(self):
        self.assertIsInstance(self.reading.provenance, InteractionProvenance)
        self.assertEqual(self.reading.provenance.action, PROBE)

    def test_sem_L_is_blind_to_the_provenance(self):
        for s in self.traj.sem.sem("l:trial"):
            self.assertNotIn(PROBE, repr(s))

    def test_service_is_certifiable_and_cites_settlements(self):
        cert = self.traj.certify()
        self.assertTrue(valid_cert(self.traj.spec, self.traj.facts(), cert))
        self.assertEqual(cert.cited, ("l:trial",))

    def test_historical_service_persists_under_unrelated_extension(self):
        cert = self.traj.certify()
        self.traj.sem.admit(SettlementReading(
            "l:later", "o:later", (li.Atom("something-else"),), "unrelated"))
        self.traj.history.settle("l:later")
        self.assertTrue(valid_cert(self.traj.spec, self.traj.facts(), cert))


class T3_AssessmentReturnsAReasonAndNothingElse(unittest.TestCase):

    def setUp(self):
        self.traj = Trajectory().stage_a()
        outcome, receipt = self.traj.act(PROBE)
        self.traj.settle_outcome(outcome, receipt)
        self.traj.certify()

    def test_the_canonical_proposal_passes_the_whole_gate(self):
        self.assertTrue(admissible_assessment(
            toy.inquiry_ref(), self.traj.spec, self.traj.facts(),
            self.traj.certificate, self.traj.assessment,
            self.traj.propose_revaluation()))

    def test_appending_the_reason_moves_no_standing(self):
        std = dict(self.traj.history.std())
        self.assertTrue(self.traj.assess_and_append(
            self.traj.propose_revaluation()))
        self.assertEqual(std, self.traj.history.std())

    def test_assessment_is_maximally_permissive_over_targets(self):
        """Documented as grounding-only, and checked to be exactly that."""
        other = ReasonProposal("e:other", frozenset(), frozenset(["l:trial"]),
                               li.Atom("v0-should-stand"))
        self.assertTrue(admissible_assessment(
            toy.inquiry_ref(), self.traj.spec, self.traj.facts(),
            self.traj.certificate, self.traj.assessment, other))


class T4_T5_TheCanonicalRecordIsUnchanged(unittest.TestCase):

    def setUp(self):
        self.traj = Trajectory().stage_a().stage_b()

    def test_the_record_is_the_canonical_one(self):
        self.assertEqual(self.traj.history.now, 5)
        self.assertEqual([s.id for s in self.traj.history.settlements()],
                         ["l:trial"])
        self.assertEqual([e.id for e in self.traj.history.reasons()],
                         ["e:revalue"])
        self.assertEqual(
            [(a.id, a.tau) for a in self.traj.history.norm_events()],
            [("a:value", 1), ("a:force", 2), ("a:revalue", 5)])

    def test_the_canonical_seed_is_literally_the_pre_inquiry_seed(self):
        """Four authorities. The transfer fixture supplies its own separately."""
        self.assertEqual(sorted(self.traj.history.seed.std0),
                         ["auth:force", "auth:reforce", "auth:revalue",
                          "auth:value"])

    def test_value_revision_is_not_operative_revision(self):
        std = self.traj.history.std()
        self.assertEqual(values_projection(std), ((V1_STANDING, "v1"),))
        self.assertEqual([sid for sid, _ in operative_projection(std)],
                         [J0_STANDING])

    def test_only_stage_C_moves_the_injunction(self):
        self.traj.stage_c()
        self.assertEqual(
            [sid for sid, _ in operative_projection(self.traj.history.std())],
            [J1_STANDING])

    def test_RI_is_good_at_every_state(self):
        self.traj.stage_c()
        for t in range(self.traj.history.now + 1):
            self.assertTrue(self.traj.history.good(t), f"state {t}")


# ===========================================================================
#  Attacks
# ===========================================================================


class TheActionPathIsMediatedByGamma(unittest.TestCase):
    """Seam: `Need -> Action -> RawOutcome`. Refused by `inquiry.execute`."""

    def test_the_log_has_no_public_append(self):
        """So no caller can pair an action with an outcome of its choosing."""
        log = InteractionLog("t")
        self.assertFalse(hasattr(log, "record"))
        self.assertFalse(hasattr(log, "append"))

    def test_execute_records_only_what_gamma_returned(self):
        log = InteractionLog("t")
        outcome, receipt = execute(log, inquiry.diagnostic_gamma(), PROBE)
        self.assertEqual(receipt.action, PROBE)
        self.assertIs(log.outcome(outcome.id), outcome)

    def test_a_selector_returning_an_unpermitted_outcome_is_refused(self):
        log = InteractionLog("t")
        ghost = RawOutcome("o:invented", {"band": (Q(0), Q(1))})
        with self.assertRaises(InteractionRefused):
            execute(log, inquiry.diagnostic_gamma(), PROBE,
                    choose=lambda permitted: ghost)
        self.assertEqual(log.receipts, [])

    def test_an_environment_permitting_nothing_is_refused(self):
        log = InteractionLog("t")
        with self.assertRaises(InteractionRefused):
            execute(log, lambda h, a: (), PROBE)

    def test_an_outcome_never_executed_cannot_be_settled(self):
        traj = Trajectory().stage_a()
        traj.act(PROBE)
        ghost = RawOutcome("o:invented", {"band": (Q(1, 3), Q(2, 3))})
        with self.assertRaises(ProvenanceRefused):
            authenticate(traj.log, ghost, traj.log.receipts[0].receipt_id)


class ReceiptIdentityIsById(unittest.TestCase):
    """Seam: `RawOutcome -> Settlement`. Refused by `inquiry.authenticate`."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.outcome, self.receipt = self.traj.act(PROBE)

    def test_a_copied_receipt_authenticates_via_the_logs_own(self):
        """Object identity is not the model; the id resolves in the log."""
        clone = InteractionReceipt(self.receipt.receipt_id, self.receipt.index,
                                   self.receipt.action, self.receipt.outcome_id)
        self.assertIsNot(clone, self.receipt)
        self.assertEqual(clone, self.receipt)
        prov = authenticate(self.traj.log, self.outcome, clone.receipt_id)
        self.assertEqual(prov.receipt_id, self.receipt.receipt_id)

    def test_a_forged_receipt_cannot_change_the_authenticated_action(self):
        """The action comes off the log's receipt, never off the argument."""
        forged = InteractionReceipt(self.receipt.receipt_id, 0, "Hearsay",
                                    self.outcome.id)
        prov = authenticate(self.traj.log, self.outcome, forged.receipt_id)
        self.assertEqual(prov.action, PROBE)

    def test_an_unknown_receipt_id_is_refused(self):
        with self.assertRaises(ProvenanceRefused):
            authenticate(self.traj.log, self.outcome, "toy#99")

    def test_an_id_from_another_log_is_refused(self):
        other = Trajectory().stage_a()
        other_outcome, other_receipt = other.act(PROBE)
        with self.assertRaises(ProvenanceRefused):
            authenticate(self.traj.log, other_outcome,
                         other_receipt.receipt_id)

    def test_an_outcome_from_another_log_is_refused(self):
        other = Trajectory().stage_a()
        other_outcome, _ = other.act(PROBE)
        with self.assertRaises(ProvenanceRefused):
            authenticate(self.traj.log, other_outcome,
                         self.receipt.receipt_id)

    def test_provenance_cannot_be_constructed_directly(self):
        with self.assertRaises(ProvenanceRefused):
            InteractionProvenance(object(), "toy#0", 0, PROBE, "o:trial")

    def test_unauthenticated_provenance_is_refused_when_read(self):
        sem = SettlementSemantics()
        sem.admit(SettlementReading("l:fake", "o:fake", (li.Atom("p"),), "",
                                    provenance=("o:fake", PROBE, 0)))
        with self.assertRaises(ProvenanceRefused):
            settled_facts(["l:fake"], sem)


class WaitCannotTeachTheAgent(unittest.TestCase):
    """Seam: `RawOutcome -> Settlement`. Refused by the pinned reader."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.before = len(pc_worlds(self.traj.stage(), ()))
        outcome, receipt = self.traj.act(WAIT)
        self.reading = self.traj.settle_outcome(outcome, receipt)

    def test_wait_is_authenticated_honestly_as_wait(self):
        self.assertEqual(self.reading.provenance.action, WAIT)

    def test_wait_carries_no_diagnostic_sentences(self):
        self.assertEqual(self.reading.sentences, ())
        self.assertFalse(self.reading.exposes)

    def test_wait_eliminates_no_world(self):
        self.assertEqual(len(pc_worlds(self.traj.stage(), ())), self.before)

    def test_wait_makes_no_service_certifiable(self):
        self.assertFalse(certifiable(self.traj.spec, self.traj.facts()))

    def test_a_waiting_trajectory_produces_no_reason_and_no_event(self):
        traj = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        self.assertEqual([e.id for e in traj.history.reasons()], [])
        self.assertEqual([a.id for a in traj.history.norm_events()],
                         ["a:value", "a:force"])
        self.assertEqual(values_projection(traj.history.std()),
                         ((V0_STANDING, "v0"),))

    def test_the_sentences_track_the_readout_the_environment_gave(self):
        """A probe reporting a different band settles different sentences."""
        log = InteractionLog("alt")
        band = (Q(0), Q(1, 3))
        outcome, receipt = execute(
            log, lambda h, a: (RawOutcome("o:alt", {"band": band}),), PROBE)
        reading = read_and_admit(SettlementSemantics(), log, outcome,
                                 receipt.receipt_id, self.traj.reader, "l:alt")
        self.assertEqual(reading.sentences,
                         (self.traj.X0.luv.gt(Q(0)),
                          li.Neg(self.traj.X0.luv.gt(Q(1, 3)))))
        self.assertNotEqual(reading.sentences,
                            (self.traj.X0.luv.gt(Q(1, 3)),
                             li.Neg(self.traj.X0.luv.gt(Q(2, 3)))))


class TheSpecIsPinnedAtBothBoundaries(unittest.TestCase):
    """Seam: `InquiryRef -> ServiceSpec`. Refused by `SpecMismatch`."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.run = self.traj.read_pressure(0)
        self.other = inquiry.diagnostic_spec("sigma:other", self.traj.X0.luv,
                                             Q(1, 3), action=PROBE)

    def test_a_mismatched_spec_cannot_decide_whether_an_inquiry_is_live(self):
        with self.assertRaises(SpecMismatch):
            inquiry.derive_need(self.run, self.traj.history, toy.inquiry_ref(),
                                self.traj.facts(), self.other)

    def test_the_pinned_spec_is_accepted(self):
        self.assertIsNotNone(inquiry.derive_need(
            self.run, self.traj.history, toy.inquiry_ref(), self.traj.facts(),
            self.traj.spec))

    def test_a_mismatched_spec_is_refused_at_assessment(self):
        outcome, receipt = self.traj.act(PROBE)
        self.traj.settle_outcome(outcome, receipt)
        self.traj.certify()
        self.assertFalse(admissible_assessment(
            toy.inquiry_ref(), self.other, self.traj.facts(),
            self.traj.certificate, self.traj.assessment,
            self.traj.propose_revaluation()))


class AttacksOnAssessment(unittest.TestCase):
    """Seam: `Service -> Assessment`. Refused by `admissible_assessment`."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        outcome, receipt = self.traj.act(PROBE)
        self.traj.settle_outcome(outcome, receipt)
        self.traj.certify()
        self.proposal = self.traj.propose_revaluation()

    def refused(self, **kw):
        return not admissible_assessment(
            toy.inquiry_ref(), kw.get("spec", self.traj.spec),
            self.traj.facts(), kw.get("cert", self.traj.certificate),
            self.traj.assessment, kw.get("proposal", self.proposal),
            current_use=kw.get("current_use"))

    def test_a_wrong_spec_certificate_is_refused(self):
        self.assertTrue(self.refused(
            cert=ServiceCertificate("sigma:something-else", ("l:trial",))))

    def test_a_certificate_citing_a_nonexistent_settlement_is_refused(self):
        self.assertTrue(self.refused(
            cert=ServiceCertificate(self.traj.spec.spec_id, ("l:imaginary",))))

    def test_a_none_certificate_is_refused(self):
        self.assertTrue(self.refused(cert=None))

    def test_an_invalid_certificate_with_matching_citations_is_refused(self):
        waiting = Trajectory().stage_a()
        outcome, receipt = waiting.act(WAIT)
        waiting.settle_outcome(outcome, receipt)
        cert = ServiceCertificate(waiting.spec.spec_id, ("l:trial",))
        self.assertFalse(valid_cert(waiting.spec, waiting.facts(), cert))
        self.assertFalse(admissible_assessment(
            toy.inquiry_ref(), waiting.spec, waiting.facts(), cert,
            waiting.assessment, waiting.propose_revaluation()))

    def test_a_lapsed_certificate_is_refused_while_history_stands(self):
        self.assertTrue(self.refused(current_use=superseded_by_round(99)))
        self.assertTrue(valid_cert(self.traj.spec, self.traj.facts(),
                                   self.traj.certificate),
                        "historical validity is untouched")

    def test_a_proposal_grounded_outside_the_certificate_is_refused(self):
        self.assertTrue(self.refused(proposal=ReasonProposal(
            "e:ungrounded", frozenset(), frozenset(["l:elsewhere"]),
            li.Atom("x"))))

    def test_an_ungrounded_proposal_is_refused(self):
        self.assertTrue(self.refused(proposal=ReasonProposal(
            "e:floating", frozenset(), frozenset(), li.Atom("x"))))

    def test_a_refused_gate_appends_nothing(self):
        bad = ReasonProposal("e:bad", frozenset(), frozenset(["l:elsewhere"]),
                             li.Atom("x"))
        self.assertFalse(self.traj.assess_and_append(bad))
        self.assertEqual([e.id for e in self.traj.history.reasons()], [])


class AFailedGateStopsTheTrajectory(unittest.TestCase):
    """`stage_b` must not proceed past a step that refused."""

    def test_wait_stops_before_service_and_no_event_occurs(self):
        traj = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        self.assertIsNone(traj.certificate)
        self.assertEqual([e.id for e in traj.history.reasons()], [])
        self.assertEqual(len(traj.history.norm_events()), 2)

    def test_a_reader_that_exposes_nothing_yields_no_norm_event(self):
        traj = Trajectory().stage_a()
        traj.reader = lambda prov, outcome: ()
        traj.stage_b()
        self.assertEqual([e.id for e in traj.history.reasons()], [])
        self.assertEqual(len(traj.history.norm_events()), 2)
        self.assertEqual(values_projection(traj.history.std()),
                         ((V0_STANDING, "v0"),))


class NeedSemantics(unittest.TestCase):
    """Need depends on present usability, not on ever having been serviced.

    Read at day 1. At day 0 the settlement makes the ceiling incompatible with
    deduction outright — the precision-1 mesh reads the settled quantity at `1`
    — so that day has no charged result and no pressure to be under.
    """

    def setUp(self):
        self.traj = Trajectory().stage_a()
        outcome, receipt = self.traj.act(PROBE)
        self.traj.settle_outcome(outcome, receipt)
        self.run = self.traj.read_pressure(1)

    def test_a_blocked_day_yields_no_pressure(self):
        blocked = self.traj.read_pressure(0)
        self.assertTrue(blocked.conflict.blocking)
        self.assertIsNone(inquiry.pressure_of(blocked, J0_STANDING))
        self.assertIsNone(self.traj.need(blocked))

    def test_present_service_suppresses_the_need(self):
        self.assertIsNone(self.traj.need(self.run))

    def test_a_lapse_reopens_the_need_while_history_stands(self):
        stale = self.traj.need(self.run, current_use=superseded_by_round(99))
        self.assertIsNotNone(stale, "the need returns when service lapses")
        self.assertTrue(certifiable(self.traj.spec, self.traj.facts()),
                        "and the historical fact of service is untouched")


class InquiryIdentitySurvivesARealTransfer(unittest.TestCase):
    """The reference survives custody change; the episode does not.

    Decided by an actual RI `Transfer` on a fixture seed of its own, so the
    canonical seed keeps exactly its pre-inquiry four authorities.
    """

    def setUp(self):
        self.traj = Trajectory(extra_seed=toy.transfer_authority()).stage_a()
        self.run = self.traj.read_pressure(0)

    def test_the_fixture_seed_is_the_canonical_one_plus_one_authority(self):
        self.assertEqual(sorted(self.traj.history.seed.std0),
                         ["auth:force", "auth:reforce", "auth:revalue",
                          "auth:transfer", "auth:value"])

    def test_a_real_transfer_moves_the_episode_and_keeps_the_reference(self):
        before = current_episode_for(self.traj.history, J0_STANDING)
        need_before = self.traj.need(self.run)

        self.traj.history.norm("a:xfer", "auth:transfer", author="A",
                               wit=J0_STANDING)

        after = current_episode_for(self.traj.history, J0_STANDING)
        need_after = self.traj.need(self.traj.read_pressure(0))

        self.assertNotEqual(before.id, after.id)
        self.assertEqual(before.debtor, "A")
        self.assertEqual(after.debtor, "B")
        self.assertEqual(after.subject, J0_STANDING)
        self.assertEqual(need_before.ref, need_after.ref)
        self.assertNotEqual(need_before.episode, need_after.episode)
        self.assertTrue(self.traj.history.good())


class PressureIsStandingLocal(unittest.TestCase):
    """A standing is answerable for its own demand, not for the day's total."""

    def two_forces(self):
        from waist import Expect, Ineq, Injunction
        X = toy.x0()
        a = Injunction("JA", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 4)),))
        b = Injunction("JB", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 3)),))
        return run_day(2, v.base_stage(X), v._std([("sA", a), ("sB", b)]),
                       observe=True)

    def test_each_standing_gets_its_own_share(self):
        run = self.two_forces()
        pa = inquiry.pressure_of(run, "sA")
        pb = inquiry.pressure_of(run, "sB")
        self.assertNotEqual(pa.charge, pa.joint_charge)
        self.assertGreaterEqual(pa.charge + pb.charge, run.charged.charge)

    def test_a_standing_with_no_active_force_has_no_pressure(self):
        self.assertIsNone(inquiry.pressure_of(self.two_forces(), "s:absent"))


class PressureObservationIsFree(unittest.TestCase):
    """Observing certified liability is not exercising normative force."""

    def test_observation_consults_no_account_and_emits_nothing(self):
        traj = Trajectory().stage_a()
        before = traj.account.remaining
        run = traj.read_pressure(0)
        self.assertTrue(run.charged.observed)
        self.assertFalse(run.charged.emitted)
        self.assertIsNone(run.charged.account_remaining)
        self.assertEqual(run.prices, ())
        self.assertEqual(traj.account.remaining, before)

    def test_it_reads_the_same_charge_as_enforcement_on_the_same_prestate(self):
        traj = Trajectory().stage_a()
        observed = traj.read_pressure(0)
        charged = traj.day(0)
        self.assertEqual(observed.charged.sharp, charged.charged.sharp)
        self.assertEqual(observed.charged.charge, charged.charged.charge)
        self.assertEqual(observed.charged.certificate.aggregate,
                         charged.charged.certificate.aggregate)


class PolicyParametricity(unittest.TestCase):
    """One semantics, two policies, two trajectories."""

    def test_probe_services_and_wait_does_not(self):
        probed = Trajectory().stage_a().stage_b(policy=inquiry.probe_policy)
        waited = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        self.assertTrue(certifiable(probed.spec, probed.facts()))
        self.assertFalse(certifiable(waited.spec, waited.facts()))
        self.assertEqual(values_projection(probed.history.std()),
                         ((V1_STANDING, "v1"),))
        self.assertEqual(values_projection(waited.history.std()),
                         ((V0_STANDING, "v0"),))

    def test_the_service_semantics_is_the_same_object_in_both(self):
        probed = Trajectory().stage_a().stage_b(policy=inquiry.probe_policy)
        waited = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        sample = probed.facts() + waited.facts()
        for cited in ((), ("l:trial",)):
            cert = ServiceCertificate(probed.spec.spec_id, cited)
            self.assertEqual(probed.spec.check(sample, cert),
                             waited.spec.check(sample, cert))

    def test_the_policy_takes_a_view_and_not_a_bool(self):
        self.assertEqual(inquiry.probe_policy(InquiryView(None)), WAIT)
        self.assertEqual(inquiry.wait_policy(InquiryView(None)), WAIT)


class ServiceDoesNotFactorThroughPC(unittest.TestCase):
    """Two execution-backed histories, one `Sigma`, different verdicts."""

    def setUp(self):
        self.X = toy.x0()
        self.fx = inquiry.provenance_fixture(self.X.luv, Q(1, 3), Q(2, 3))

    def test_the_two_ledgers_denote_the_same_sentences(self):
        self.assertEqual(self.fx["good"].sem("l:same"),
                         self.fx["bad"].sem("l:same"))
        self.assertTrue(self.fx["good"].sem("l:same"),
                        "and both actually settled something")

    def test_and_induce_the_same_worlds(self):
        good = Stage.of(v._chain(self.X), self.fx["good"].entries(["l:same"]))
        bad = Stage.of(v._chain(self.X), self.fx["bad"].entries(["l:same"]))
        self.assertEqual(pc_worlds(good, ()), pc_worlds(bad, ()))

    def test_both_histories_are_execution_backed(self):
        """Neither verdict rests on a label; both ran a real action."""
        for key, log in (("good", "good_log"), ("bad", "bad_log")):
            prov = self.fx[key].reading("l:same").provenance
            self.assertIsInstance(prov, InteractionProvenance)
            self.assertEqual(len(self.fx[log].receipts), 1)
            self.assertEqual(self.fx[log].receipts[0].action, prov.action)

    def test_but_service_succeeds_on_one_and_fails_on_the_other(self):
        good = settled_facts(["l:same"], self.fx["good"])
        bad = settled_facts(["l:same"], self.fx["bad"])
        self.assertTrue(certifiable(self.fx["spec"], good))
        self.assertFalse(certifiable(self.fx["spec"], bad))


class NoAllowanceIsEverMinted(unittest.TestCase):
    """Servicing an inquiry buys no permission to spend."""

    def account_across(self, step):
        traj = Trajectory().stage_a()
        outcome, receipt = traj.act(PROBE)
        before = traj.account.remaining
        step(traj, outcome, receipt)
        return before, traj.account.remaining

    def test_need_derivation_does_not_move_the_account(self):
        b, a = self.account_across(lambda t, o, r: t.need(t.read_pressure(0)))
        self.assertEqual(b, a)

    def test_settlement_service_and_assessment_do_not_move_the_account(self):
        def step(t, o, r):
            t.settle_outcome(o, r)
            t.certify()
            certifiable(t.spec, t.facts())
            t.assess_and_append(t.propose_revaluation())
        b, a = self.account_across(step)
        self.assertEqual(b, a)

    def test_the_whole_loop_never_raises_the_account(self):
        traj = Trajectory().stage_a()
        start = traj.account.remaining
        traj.stage_b()
        traj.stage_c()
        self.assertLessEqual(traj.account.remaining, start)

    def test_a_withheld_request_stays_unaffordable_after_service(self):
        """Both days are well-formed; only affordability is in question."""
        poor = Trajectory(capital=Q(1)).stage_a()
        before = poor.day(1)
        self.assertFalse(before.conflict.blocking, "well-formed before")
        self.assertFalse(before.charged.emitted, "and unaffordable")

        poor.stage_b()
        after = poor.day(1)
        self.assertFalse(after.conflict.blocking, "well-formed after")
        self.assertFalse(after.charged.emitted,
                         "servicing bought no allowance")
        self.assertLessEqual(poor.account.remaining, Q(1))


if __name__ == "__main__":
    unittest.main()
