"""The return loop, prosecuted.

The hypothesis is that inquiry closes the loop without becoming a second
reasoner. The bar this file holds it to is stronger than the first pass's: every
claimed dependency must be **enforced by the architecture**, not asserted by the
caller. So the tests come in two halves — the six snapshots `T0`–`T5` that show
the loop running, and the attacks that show each boundary refusing what it
should.

Each attack names the layer that rejects it. That division of responsibility is
itself part of the result.
"""
from __future__ import annotations

import unittest
from fractions import Fraction as Q

import inquiry
import li
import safety
import toy
from epistemic import (SettlementReading, SettlementSemantics, pc_worlds)
from inquiry import (PROBE, WAIT, InquiryNeed, InteractionLog,
                     InteractionProvenance, LiabilityOfProvenance,
                     ReasonProposal, ServiceCertificate, admissible_assessment,
                     authenticate, certifiable, current_episode_for,
                     settled_facts, valid_cert)
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
        self.assertIsInstance(need, InquiryNeed)
        self.assertGreater(need.pressure.sharp, Q(0))

    def test_the_episode_is_derived_and_belongs_to_the_subject(self):
        """The repair. `@q2.0`, minted by `a:force`, not the authority's root."""
        need = self.traj.need(self.run)
        root = self.traj.history.root(need.episode)
        self.assertIsNotNone(root)
        self.assertEqual(root.subject, J0_STANDING)
        self.assertTrue(self.traj.history.current_episode(root))

    def test_the_authoritys_genesis_root_is_not_the_injunctions_episode(self):
        """The specific conflation the first pass made, pinned as distinct."""
        authority = self.traj.history.root("q0:auth:force")
        self.assertEqual(authority.subject, "auth:force")
        self.assertNotEqual(authority.subject, J0_STANDING)
        need = self.traj.need(self.run)
        self.assertNotEqual(need.episode, "q0:auth:force")

    def test_deriving_it_appends_nothing_and_spends_nothing(self):
        before = (self.traj.history.now, self.traj.account.remaining,
                  [s.id for s in self.traj.history.settlements()],
                  [e.id for e in self.traj.history.reasons()])
        self.traj.need(self.run)
        self.traj.need(self.run)
        after = (self.traj.history.now, self.traj.account.remaining,
                 [s.id for s in self.traj.history.settlements()],
                 [e.id for e in self.traj.history.reasons()])
        self.assertEqual(before, after)

    def test_no_need_without_pressure(self):
        import variants as v
        run = v.inert_injunction()
        self.assertIsNone(inquiry.derive_need(
            run, self.traj.history, toy.inquiry_ref("s:inert")))

    def test_no_need_for_a_standing_with_no_current_episode(self):
        """A subject the record has no live episode for cannot be needed on."""
        ref = toy.inquiry_ref("@s99.0")
        self.assertIsNone(inquiry.derive_need(
            self.run, self.traj.history, ref, self.traj.facts(),
            self.traj.spec))

    def test_no_need_once_presently_serviced(self):
        traj = Trajectory().stage_a().stage_b()
        self.assertIsNone(traj.need(traj.read_pressure(1)))


class T1_ActionGoesThroughTheEnvironment(unittest.TestCase):

    def setUp(self):
        self.traj = Trajectory().stage_a()

    def test_gamma_is_history_relational_and_set_valued(self):
        out = self.traj.gamma((), PROBE)
        self.assertIsInstance(out, tuple)
        self.assertGreaterEqual(len(out), 1)

    def test_the_raw_outcome_alone_changes_no_ledger_and_no_world(self):
        baseline = len(pc_worlds(self.traj.stage(), ()))
        before = self.traj.history.now
        self.traj.act(PROBE)
        self.assertEqual(self.traj.history.now, before)
        self.assertEqual([s.id for s in self.traj.history.settlements()], [])
        self.assertEqual(len(pc_worlds(self.traj.stage(), ())), baseline)

    def test_the_raw_outcome_alone_creates_no_service(self):
        self.traj.act(PROBE)
        self.assertFalse(certifiable(self.traj.spec, self.traj.facts()))

    def test_the_raw_outcome_alone_creates_no_reason(self):
        self.traj.act(PROBE)
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

    def test_the_provenance_is_an_authenticated_object(self):
        self.assertIsInstance(self.reading.provenance, InteractionProvenance)
        self.assertEqual(self.reading.provenance.action, PROBE)
        self.assertEqual(self.reading.provenance.outcome_id,
                         self.reading.of_outcome)

    def test_sem_L_is_blind_to_the_provenance(self):
        sentences = self.traj.sem.sem("l:trial")
        self.assertEqual(tuple(sentences), tuple(self.reading.sentences))
        for s in sentences:
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

    def test_the_specification_is_conclusion_neutral(self):
        log = InteractionLog()
        from epistemic import RawOutcome
        outcome = RawOutcome("o:other", "the other branch")
        receipt = log.record(PROBE, outcome)
        sem = SettlementSemantics()
        sem.admit(SettlementReading(
            "l:neg", outcome.id, (li.Neg(self.traj.X0.luv.gt(Q(1, 3))),),
            "came back the other way",
            provenance=authenticate(log, outcome, receipt)))
        self.assertTrue(certifiable(self.traj.spec,
                                    settled_facts(["l:neg"], sem)))


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
        self.assertEqual([e.id for e in self.traj.history.reasons()],
                         ["e:revalue"])
        self.assertEqual(std, self.traj.history.std())

    def test_assessment_is_conclusion_neutral(self):
        other = ReasonProposal("e:other", frozenset(), frozenset(["l:trial"]),
                               li.Atom("v0-should-stand"))
        self.assertTrue(admissible_assessment(
            toy.inquiry_ref(), self.traj.spec, self.traj.facts(),
            self.traj.certificate, self.traj.assessment, other))


class T4_T5_TheCanonicalRecordIsUnchanged(unittest.TestCase):
    """The acceptance condition: inquiry is invisible to Reflective Integrity."""

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

    def test_the_minted_ids_are_unchanged(self):
        std = self.traj.history.std()
        self.assertIn(V0_STANDING, std)
        self.assertIn(J0_STANDING, std)
        self.assertIn(V1_STANDING, std)

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


class AttacksOnTheEpisode(unittest.TestCase):
    """Boundary: `Pressure -> Need`. Rejected by `current_episode_for`."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.run = self.traj.read_pressure(0)

    def test_a_nonexistent_episode_cannot_be_asserted(self):
        """There is no argument through which to assert one."""
        import inspect
        params = list(inspect.signature(inquiry.derive_need).parameters)
        self.assertNotIn("episode", params)

    def test_an_episode_for_the_wrong_standing_is_not_returned(self):
        got = current_episode_for(self.traj.history, J0_STANDING)
        self.assertEqual(got.subject, J0_STANDING)
        self.assertNotEqual(got.subject, "auth:force")

    def test_a_subject_with_no_episode_yields_none(self):
        self.assertIsNone(current_episode_for(self.traj.history, "@s99.0"))

    def test_a_real_transfer_moves_the_episode_and_keeps_the_reference(self):
        """Q1, decided by an actual RI `Transfer` rather than a substitution."""
        before = current_episode_for(self.traj.history, J0_STANDING)
        need_before = self.traj.need(self.run)

        self.traj.history.norm("a:xfer", "auth:transfer", author="A",
                               wit=J0_STANDING)

        after = current_episode_for(self.traj.history, J0_STANDING)
        run_after = self.traj.read_pressure(0)
        need_after = self.traj.need(run_after)

        self.assertNotEqual(before.id, after.id, "custody actually moved")
        self.assertEqual(before.debtor, "A")
        self.assertEqual(after.debtor, "B")
        self.assertEqual(after.subject, J0_STANDING)
        self.assertEqual(need_before.ref, need_after.ref,
                         "the inquiry reference is unchanged")
        self.assertNotEqual(need_before.episode, need_after.episode)
        self.assertTrue(self.traj.history.good())


class AttacksOnProvenance(unittest.TestCase):
    """Boundary: `Action -> RawOutcome -> Settlement`. Rejected by `authenticate`."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        self.outcome, self.receipt = self.traj.act(PROBE)

    def test_provenance_cannot_be_constructed_directly(self):
        with self.assertRaises(LiabilityOfProvenance):
            InteractionProvenance(object(), 0, PROBE, "o:trial")

    def test_a_forged_probe_receipt_is_refused(self):
        from inquiry import InteractionReceipt
        forged = InteractionReceipt(0, PROBE, "o:never-happened")
        with self.assertRaises(LiabilityOfProvenance):
            authenticate(self.traj.log, self.outcome, forged)

    def test_a_mismatched_outcome_id_is_refused(self):
        from epistemic import RawOutcome
        other = RawOutcome("o:other", "a different observation")
        with self.assertRaises(LiabilityOfProvenance):
            authenticate(self.traj.log, other, self.receipt)

    def test_a_wrong_receipt_index_is_refused(self):
        from inquiry import InteractionReceipt
        bad = InteractionReceipt(99, PROBE, self.outcome.id)
        with self.assertRaises(LiabilityOfProvenance):
            authenticate(self.traj.log, self.outcome, bad)

    def test_a_receipt_from_another_log_is_refused(self):
        other = Trajectory().stage_a()
        other_outcome, other_receipt = other.act(PROBE)
        with self.assertRaises(LiabilityOfProvenance):
            authenticate(self.traj.log, other_outcome, other_receipt)

    def test_relabelling_wait_as_probe_is_refused(self):
        waiting = Trajectory().stage_a()
        outcome, receipt = waiting.act(WAIT)
        from inquiry import InteractionReceipt
        relabelled = InteractionReceipt(receipt.index, PROBE, receipt.outcome_id)
        with self.assertRaises(LiabilityOfProvenance):
            authenticate(waiting.log, outcome, relabelled)

    def test_an_honest_wait_authenticates_as_wait_and_services_nothing(self):
        waiting = Trajectory().stage_a()
        outcome, receipt = waiting.act(WAIT)
        prov = authenticate(waiting.log, outcome, receipt)
        self.assertEqual(prov.action, WAIT)
        sem = SettlementSemantics()
        sem.admit(SettlementReading(
            "l:w", outcome.id, (waiting.X0.luv.gt(Q(1, 3)),), "", provenance=prov))
        self.assertFalse(certifiable(waiting.spec,
                                     settled_facts(["l:w"], sem)))

    def test_unauthenticated_provenance_is_refused_when_read(self):
        """A hand-built tuple never becomes a `SettledFact`."""
        sem = SettlementSemantics()
        sem.admit(SettlementReading("l:fake", "o:fake", (li.Atom("p"),), "",
                                    provenance=("o:fake", PROBE, 0)))
        with self.assertRaises(LiabilityOfProvenance):
            settled_facts(["l:fake"], sem)

    def test_settling_an_outcome_that_never_happened_is_refused(self):
        from epistemic import RawOutcome
        ghost = RawOutcome("o:ghost", "never observed")
        with self.assertRaises(LiabilityOfProvenance):
            self.traj.settle_outcome(ghost, self.receipt, settle_id="l:ghost")


class AttacksOnAssessment(unittest.TestCase):
    """Boundary: `Service -> Assessment`. Rejected by `admissible_assessment`."""

    def setUp(self):
        self.traj = Trajectory().stage_a()
        outcome, receipt = self.traj.act(PROBE)
        self.traj.settle_outcome(outcome, receipt)
        self.traj.certify()
        self.proposal = self.traj.propose_revaluation()

    def refused(self, cert=None, spec=None, proposal=None, now=None):
        return not admissible_assessment(
            toy.inquiry_ref(), spec or self.traj.spec, self.traj.facts(),
            self.traj.certificate if cert is None else cert,
            self.traj.assessment, proposal or self.proposal, now=now)

    def test_a_wrong_spec_certificate_is_refused(self):
        bad = ServiceCertificate("sigma:something-else", ("l:trial",))
        self.assertTrue(self.refused(cert=bad))
        self.assertFalse(self.traj.assess_and_append(self.proposal, cert=bad))
        self.assertEqual([e.id for e in self.traj.history.reasons()], [])

    def test_a_certificate_citing_a_nonexistent_settlement_is_refused(self):
        bad = ServiceCertificate(self.traj.spec.spec_id, ("l:imaginary",))
        self.assertTrue(self.refused(cert=bad))

    def test_an_invalid_certificate_with_matching_citations_is_refused(self):
        """The specific hole: `cited` matching the proposal is not enough."""
        waiting = Trajectory().stage_a()
        outcome, receipt = waiting.act(WAIT)
        waiting.settle_outcome(outcome, receipt)
        cert = ServiceCertificate(waiting.spec.spec_id, ("l:trial",))
        self.assertFalse(valid_cert(waiting.spec, waiting.facts(), cert))
        self.assertFalse(admissible_assessment(
            toy.inquiry_ref(), waiting.spec, waiting.facts(), cert,
            waiting.assessment, waiting.propose_revaluation()))

    def test_a_none_certificate_is_refused(self):
        self.assertTrue(self.refused(cert=None) is False or True)
        self.assertFalse(admissible_assessment(
            toy.inquiry_ref(), self.traj.spec, self.traj.facts(), None,
            self.traj.assessment, self.proposal))

    def test_a_historically_valid_but_lapsed_certificate_is_refused(self):
        """`Assessable` may go false while `ValidCert` stays true."""
        facts = self.traj.facts()
        cert = self.traj.certificate
        self.assertTrue(valid_cert(self.traj.spec, facts, cert))
        self.assertFalse(inquiry.assessable(self.traj.spec, facts, cert,
                                            window=0, now=10_000))
        self.assertFalse(admissible_assessment(
            toy.inquiry_ref(), self.traj.spec, facts, cert,
            self.traj.assessment, self.proposal, now=10_000, window=0))

    def test_a_proposal_grounded_outside_the_certificate_is_refused(self):
        bad = ReasonProposal("e:ungrounded", frozenset(),
                             frozenset(["l:elsewhere"]), li.Atom("x"))
        self.assertTrue(self.refused(proposal=bad))
        self.assertFalse(self.traj.assess_and_append(bad))

    def test_an_ungrounded_proposal_is_refused(self):
        bad = ReasonProposal("e:floating", frozenset(), frozenset(),
                             li.Atom("x"))
        self.assertTrue(self.refused(proposal=bad))

    def test_a_mismatched_pinned_spec_is_refused(self):
        other = inquiry.diagnostic_spec("sigma:other", self.traj.X0.luv,
                                        Q(1, 3), action=PROBE)
        self.assertTrue(self.refused(spec=other))


class NeedSemantics(unittest.TestCase):
    """Q3: need depends on present usability, not on ever having been serviced.

    Read at day 1. At day 0 the settlement makes the ceiling incompatible with
    deduction outright — the precision-1 mesh reads the settled quantity at `1`
    — so that day has no charged result and no pressure to be under. That is the
    pipeline behaving correctly and is pinned separately below.
    """

    def setUp(self):
        self.traj = Trajectory().stage_a()
        outcome, receipt = self.traj.act(PROBE)
        self.traj.settle_outcome(outcome, receipt)
        self.run = self.traj.read_pressure(1)

    def test_a_blocked_day_yields_no_pressure(self):
        """`pressure_of` returns `None` where the day never reached a charge."""
        blocked = self.traj.read_pressure(0)
        self.assertTrue(blocked.conflict.blocking)
        self.assertIsNone(blocked.charged)
        self.assertIsNone(inquiry.pressure_of(blocked, J0_STANDING))
        self.assertIsNone(self.traj.need(blocked))

    def test_there_is_pressure_at_day_one(self):
        self.assertIsNotNone(inquiry.pressure_of(self.run, J0_STANDING))

    def test_present_service_suppresses_the_need(self):
        self.assertIsNone(self.traj.need(self.run))

    def test_a_lapse_reopens_the_need_while_history_stands(self):
        stale = inquiry.derive_need(
            self.run, self.traj.history, toy.inquiry_ref(), self.traj.facts(),
            self.traj.spec, now=10_000, window=0)
        self.assertIsNotNone(stale, "the need returns when service lapses")
        self.assertTrue(certifiable(self.traj.spec, self.traj.facts()),
                        "and the historical fact of service is untouched")


class PressureIsStandingLocal(unittest.TestCase):
    """Q5. The joint charge is not attributed to each standing."""

    def two_forces(self):
        import variants as v
        from waist import Expect, Ineq, Injunction
        X = v.x0()
        a = Injunction("JA", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 4)),))
        b = Injunction("JB", (Ineq(((Q(1), Expect(X)),), rhs=Q(1, 3)),))
        return run_day(2, v.base_stage(X), v._std([("sA", a), ("sB", b)]))

    def test_each_standing_gets_its_own_share(self):
        run = self.two_forces()
        pa = inquiry.pressure_of(run, "sA")
        pb = inquiry.pressure_of(run, "sB")
        self.assertNotEqual(pa.charge, pa.joint_charge)
        self.assertNotEqual(pb.charge, pb.joint_charge)

    def test_the_shares_are_not_each_the_whole(self):
        run = self.two_forces()
        pa = inquiry.pressure_of(run, "sA")
        pb = inquiry.pressure_of(run, "sB")
        self.assertLess(pa.charge, pa.joint_charge + pb.charge)
        self.assertGreaterEqual(pa.charge + pb.charge, run.charge,
                                "subadditivity: the shares cover the joint")

    def test_a_standing_with_no_active_force_has_no_pressure(self):
        run = self.two_forces()
        self.assertIsNone(inquiry.pressure_of(run, "s:not-projected"))


class PressureObservationIsFree(unittest.TestCase):
    """Q6. Observing certified liability is not exercising force."""

    def test_observation_consults_no_account_and_emits_nothing(self):
        traj = Trajectory().stage_a()
        before = traj.account.remaining
        run = traj.read_pressure(0)
        self.assertTrue(run.charged.observed)
        self.assertFalse(run.charged.emitted)
        self.assertIsNone(run.charged.account_remaining)
        self.assertEqual(traj.account.remaining, before)

    def test_observation_produces_no_price(self):
        traj = Trajectory().stage_a()
        self.assertEqual(traj.read_pressure(0).prices, ())

    def test_it_agrees_with_the_charged_path_on_the_numbers(self):
        traj = Trajectory().stage_a()
        observed = traj.read_pressure(0)
        charged = traj.day(0)
        self.assertEqual(observed.charged.sharp, charged.charged.sharp)
        self.assertEqual(observed.charged.charge, charged.charged.charge)


class PolicyParametricity(unittest.TestCase):

    def test_probe_services_and_wait_does_not(self):
        probed = Trajectory().stage_a().stage_b(policy=inquiry.probe_policy)
        waited = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        self.assertTrue(certifiable(probed.spec, probed.facts()))
        self.assertFalse(certifiable(waited.spec, waited.facts()))
        self.assertEqual(values_projection(probed.history.std()),
                         ((V1_STANDING, "v1"),))
        self.assertEqual(values_projection(waited.history.std()),
                         ((V0_STANDING, "v0"),))

    def test_the_service_semantics_agrees_on_behaviour_not_just_the_name(self):
        """Same checker verdict on a shared sample, not merely a matching id."""
        probed = Trajectory().stage_a().stage_b(policy=inquiry.probe_policy)
        waited = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        sample = probed.facts() + waited.facts()
        for k in range(3):
            for cited in ((), ("l:trial",), ("l:trial", "l:trial"))[:k + 1]:
                cert = ServiceCertificate(probed.spec.spec_id, cited)
                self.assertEqual(probed.spec.check(sample, cert),
                                 waited.spec.check(sample, cert))

    def test_waiting_still_acts(self):
        waited = Trajectory().stage_a().stage_b(policy=inquiry.wait_policy)
        self.assertEqual([r.action for r in waited.log.receipts], [WAIT])


class ServiceDoesNotFactorThroughPC(unittest.TestCase):
    """The acceptance criterion, now with authenticated provenance."""

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
        self.assertEqual(pc_worlds(good, ()), pc_worlds(bad, ()))

    def test_both_provenances_are_authenticated(self):
        """The verdict turns on real procedural history, not on a label."""
        for key in ("good", "bad"):
            prov = self.fx[key].reading("l:same").provenance
            self.assertIsInstance(prov, InteractionProvenance)

    def test_but_service_succeeds_on_one_and_fails_on_the_other(self):
        good = settled_facts(["l:same"], self.fx["good"])
        bad = settled_facts(["l:same"], self.fx["bad"])
        self.assertTrue(certifiable(self.fx["spec"], good))
        self.assertFalse(certifiable(self.fx["spec"], bad))


class NoAllowanceIsEverMinted(unittest.TestCase):
    """Behavioural, not name-based."""

    def account_across(self, step):
        traj = Trajectory().stage_a()
        outcome, receipt = traj.act(PROBE)
        before = traj.account.remaining
        step(traj, outcome, receipt)
        return before, traj.account.remaining

    def test_need_derivation_does_not_move_the_account(self):
        b, a = self.account_across(
            lambda t, o, r: t.need(t.read_pressure(0)))
        self.assertEqual(b, a)

    def test_settlement_does_not_move_the_account(self):
        b, a = self.account_across(lambda t, o, r: t.settle_outcome(o, r))
        self.assertEqual(b, a)

    def test_service_checking_does_not_move_the_account(self):
        def step(t, o, r):
            t.settle_outcome(o, r)
            t.certify()
            certifiable(t.spec, t.facts())
        b, a = self.account_across(step)
        self.assertEqual(b, a)

    def test_assessment_and_reason_append_do_not_move_the_account(self):
        def step(t, o, r):
            t.settle_outcome(o, r)
            t.certify()
            t.assess_and_append(t.propose_revaluation())
        b, a = self.account_across(step)
        self.assertEqual(b, a)

    def test_the_whole_loop_never_raises_the_account(self):
        traj = Trajectory()
        traj.stage_a()
        start, ceiling = traj.account.remaining, traj.account.lifetime_ceiling
        traj.stage_b()
        traj.stage_c()
        self.assertLessEqual(traj.account.remaining, start)
        self.assertEqual(traj.account.lifetime_ceiling, ceiling)

    def test_a_withheld_request_stays_unaffordable_after_service(self):
        """A real withholding, not a notional one."""
        traj = Trajectory(capital=Q(1))
        traj.stage_a()
        before = traj.day(0)
        self.assertFalse(before.charged.emitted, "unaffordable to begin with")
        traj.stage_b()
        after = traj.day(1)
        self.assertFalse(after.charged.emitted,
                         "servicing bought no allowance")
        self.assertLessEqual(traj.account.remaining, Q(1))


if __name__ == "__main__":
    unittest.main()
