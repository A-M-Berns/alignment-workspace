from __future__ import annotations

import unittest

from role_kernel import (
    Certificate,
    CommitmentContextState,
    CommitmentOp,
    Event,
    Liability,
    OperationPolicy,
    PublicState,
    ReasonViews,
    Rewrite,
    SocialCommitment,
    StandingWrapper,
    TypedOperation,
    adjudicate,
    answerable_to,
    basis_losses,
    check_commitment_operation,
    check_rewrite,
    derivative,
    factorizes,
    joint_transport_only,
    private_basis_verdicts,
    raise_challenge,
    relabel_liability,
    relabel_public,
    relabel_rewrite,
    safety_language,
)


def closure_case(
    ident: str,
    respondent: str,
    move: Event,
    certificate_id: str,
):
    old = {ident: Liability(ident, respondent, safety_language((move,)))}
    certificate = Certificate(certificate_id, move)
    rewrite = Rewrite(move, certificate, ((ident, ()),), ((ident, "witness"),))
    public = PublicState(frozenset({certificate_id}))
    return old, certificate, rewrite, public


class DiachronicAndInterpersonalCases(unittest.TestCase):
    def test_01_future_self_may_reverse_with_an_account(self):
        move = Event("Later", "reverse")
        old, _, rewrite, public = closure_case("ell", "Later", move, "p-reverse")
        self.assertEqual(check_rewrite(old, {}, rewrite, public), ())

    def test_02_future_self_cannot_silently_delete(self):
        move = Event("Later", "tick")
        old = {"ell": Liability("ell", "Later", safety_language((move,)))}
        rewrite = Rewrite(move, Certificate("p", move), (), ())
        errors = check_rewrite(old, {}, rewrite, PublicState(frozenset({"p"})))
        self.assertIn("lineage.input_not_total", errors)
        self.assertIn("lineage.forgotten:ell", errors)

    def test_03_bob_can_give_a_reason_backed_refusal_when_the_claim_allows_it(self):
        move = Event("Bob", "refuse-with-reasons", "Alice")
        old, _, rewrite, public = closure_case("alice-claim", "Bob", move, "p-no")
        self.assertEqual(check_rewrite(old, {}, rewrite, public), ())

    def test_04_an_uninspectable_account_is_only_bob_internal(self):
        move = Event("Bob", "revise", "Alice")
        old, certificate, rewrite, public = closure_case("ell", "Bob", move, "p")
        self.assertEqual(check_rewrite(old, {}, rewrite, public), ())
        wrapper = StandingWrapper(
            holders=frozenset({("Alice", "ell")}),
            challenge_rights=frozenset({("Alice", "ell")}),
            visible=frozenset({("Alice", "account:ell")}),
        )
        self.assertFalse(answerable_to("Alice", old["ell"], certificate, "account:ell", wrapper))

    def test_09_bob_cannot_unilaterally_weaken_alices_claim(self):
        move = Event("Bob", "restate", "Alice")
        pay = Event("Bob", "pay", "Alice")
        skip = Event("Bob", "skip", "Alice")
        old = {"ell": Liability("ell", "Bob", safety_language((move, pay)))}
        new = {"weak": Liability("weak", "Bob", safety_language((pay,), (skip,)))}
        rewrite = Rewrite(move, Certificate("p", move), (("ell", ("weak",)),))
        self.assertIn(
            "semantic.transport:ell",
            check_rewrite(old, new, rewrite, PublicState(frozenset({"p"}))),
        )

    def test_respondent_erasure_confuses_personal_performance(self):
        bob = Event("Bob", "apologize", "Alice")
        carol = Event("Carol", "apologize", "Alice")
        old = Liability("ell", "Bob", safety_language((bob,)))
        # A role-erasing semantics sees only the common action kind.
        erase = lambda language: frozenset(
            tuple(event.kind for event in trace) for trace in language
        )
        self.assertEqual(erase(old.specification), erase(safety_language((carol,))))
        self.assertEqual(derivative(old.specification, carol), frozenset())


class StandingAndChallengeCases(unittest.TestCase):
    def setUp(self):
        self.views = ReasonViews(
            private=(
                ("Alice", frozenset()),
                ("Bob", frozenset({"p"})),
            ),
            recognized=frozenset({"p"}),
        )

    def test_05_successful_challenge_changes_recognized_standing_and_reopens(self):
        after = adjudicate(self.views, "p", successful=True)
        self.assertEqual(basis_losses(self.views, after, frozenset({"p"})), frozenset({"p"}))

    def test_06_unsuccessful_challenge_does_not_reopen(self):
        after = adjudicate(self.views, "p", successful=False)
        self.assertEqual(basis_losses(self.views, after, frozenset({"p"})), frozenset())

    def test_07_private_views_do_not_determine_one_basis_loss_verdict(self):
        self.assertEqual(private_basis_verdicts(self.views, "p"), frozenset({False, True}))

    def test_08_merely_raising_a_challenge_does_not_change_standing(self):
        raised = raise_challenge(self.views)
        self.assertEqual(raised.recognized, self.views.recognized)
        self.assertEqual(basis_losses(self.views, raised, frozenset({"p"})), frozenset())


class DelegationAndMergeCases(unittest.TestCase):
    def delegation_fixture(self, authorized: bool):
        delegate = Event("Bob", "delegate", "Carol")
        perform = Event("Carol", "perform", "Alice")
        old = {
            "ell": Liability(
                "ell",
                "Bob",
                safety_language((delegate, perform)),
            )
        }
        new = {"ell-carol": Liability("ell-carol", "Carol", safety_language((perform,)))}
        rewrite = Rewrite(delegate, Certificate("p-delegate", delegate), (("ell", ("ell-carol",)),))
        grants = frozenset({("ell", "Bob", "Carol")}) if authorized else frozenset()
        public = PublicState(frozenset({"p-delegate"}), grants)
        return old, new, rewrite, public

    def test_10_authorized_delegation_is_a_sound_role_changing_rewrite(self):
        self.assertEqual(check_rewrite(*self.delegation_fixture(True)), ())

    def test_11_semantically_adequate_but_unauthorized_delegation_fails(self):
        errors = check_rewrite(*self.delegation_fixture(False))
        self.assertEqual(errors, ("role.transfer_unauthorized:ell",))

    def test_12_one_response_can_answer_two_claimants_without_contracting_claims(self):
        move = Event("Bob", "joint-repair")
        old = {
            "alice": Liability("alice", "Bob", safety_language((move,))),
            "dana": Liability("dana", "Bob", safety_language((move,))),
        }
        rewrite = Rewrite(
            move,
            Certificate("p-joint", move),
            (("alice", ()), ("dana", ())),
            (("alice", "coverage-A"), ("dana", "coverage-D")),
        )
        self.assertEqual(
            check_rewrite(old, {}, rewrite, PublicState(frozenset({"p-joint"}))),
            (),
        )
        self.assertEqual(len(dict(rewrite.closed)), 2)

    def test_13_joint_strength_can_still_launder_one_parent(self):
        move = Event("Bob", "rewrite")
        a = Event("Bob", "future-a")
        b = Event("Bob", "future-b")
        old = {
            "p-a": Liability("p-a", "Bob", safety_language((move, b))),
            "p-b": Liability("p-b", "Bob", safety_language((move, a))),
        }
        new = {
            "c-a": Liability("c-a", "Bob", safety_language((a,), (b,))),
            "c-b": Liability("c-b", "Bob", frozenset({()})),
        }
        rewrite = Rewrite(
            move,
            Certificate("p", move),
            (("p-a", ("c-a",)), ("p-b", ("c-b",))),
        )
        self.assertTrue(joint_transport_only(old, new, move))
        self.assertIn(
            "semantic.transport:p-a",
            check_rewrite(old, new, rewrite, PublicState(frozenset({"p"}))),
        )

    def test_14_mutual_answerability_is_two_inputs_not_a_new_primitive(self):
        move = Event("Joint", "settle-both")
        old = {
            "ab": Liability("ab", "Bob", safety_language((move,))),
            "ba": Liability("ba", "Alice", safety_language((move,))),
        }
        rewrite = Rewrite(
            move,
            Certificate("p-settle", move),
            (("ab", ()), ("ba", ())),
            (("ab", "A-coverage"), ("ba", "B-coverage")),
        )
        public = PublicState(
            frozenset({"p-settle"}),
            rewrite_grants=frozenset({("ab", "Joint"), ("ba", "Joint")}),
        )
        self.assertEqual(check_rewrite(old, {}, rewrite, public), ())


class SeparationAndEquivarianceCases(unittest.TestCase):
    def test_15_answerability_records_do_not_imply_authorship(self):
        reason_trace = frozenset({"p-yes", "p-no"})
        response = lambda reasons, hidden_policy: "yes" if hidden_policy else "no"
        self.assertFalse(factorizes(reason_trace, (False, True), response))
        # Each selected answer can still carry a valid undertaken certificate;
        # the failure is only visible across the coupled pair of runs.
        self.assertIn(response(reason_trace, False), {"yes", "no"})
        self.assertIn(response(reason_trace, True), {"yes", "no"})

    def test_authorship_does_not_imply_answerability(self):
        response = lambda reasons, policy: tuple(sorted(reasons))
        self.assertTrue(factorizes(frozenset({"p"}), (False, True), response))
        # The deterministic reason-mediated response coexists with an omitted
        # liability account, exactly the failure from microcase 2.
        move = Event("Bob", "tick")
        old = {"ell": Liability("ell", "Bob", safety_language((move,)))}
        rewrite = Rewrite(move, Certificate("p", move), (), ())
        self.assertIn(
            "lineage.forgotten:ell",
            check_rewrite(old, {}, rewrite, PublicState(frozenset({"p"}))),
        )

    def test_16_diachronic_and_interagent_histories_are_role_relabelings(self):
        revise = Event("Later", "revise", "Earlier")
        old = {"ell": Liability("ell", "Later", safety_language((revise,)))}
        rewrite = Rewrite(
            revise,
            Certificate("p", revise),
            (("ell", ()),),
            (("ell", "account"),),
        )
        public = PublicState(frozenset({"p"}))
        first = check_rewrite(old, {}, rewrite, public)

        rename = {"Earlier": "Alice", "Later": "Bob"}
        renamed_old = {key: relabel_liability(value, rename) for key, value in old.items()}
        second = check_rewrite(
            renamed_old,
            {},
            relabel_rewrite(rewrite, rename),
            relabel_public(public, rename),
        )
        self.assertEqual(first, ())
        self.assertEqual(second, first)

    def test_a_claimant_is_not_needed_for_core_conservation(self):
        move = Event("Office", "file-report")
        old, _, rewrite, public = closure_case("constitutional-duty", "Office", move, "p")
        self.assertEqual(check_rewrite(old, {}, rewrite, public), ())
        wrapper = StandingWrapper()  # no privileged holder at all
        self.assertEqual(wrapper.holders, frozenset())

    def test_answerability_does_not_imply_cooperation(self):
        move = Event("Bob", "refuse-with-reasons", "Alice")
        old, _, rewrite, public = closure_case("request", "Bob", move, "p-no")
        self.assertEqual(check_rewrite(old, {}, rewrite, public), ())
        self.assertNotEqual(move.kind, "agree")


class SinghCommitmentOperationCases(unittest.TestCase):
    def commitment(
        self,
        ident: str,
        debtor: str,
        creditor: str,
        discharge: Event,
        *traces,
    ) -> SocialCommitment:
        return SocialCommitment(
            ident,
            debtor,
            creditor,
            "Forum",
            discharge,
            safety_language(*traces),
        )

    def typed_closure(
        self,
        kind: CommitmentOp,
        source: SocialCommitment,
        move: Event,
        witness: str,
    ) -> TypedOperation:
        rewrite = Rewrite(
            move,
            Certificate(f"p-{kind.value}", move),
            ((source.ident, ()),),
            ((source.ident, witness),),
        )
        return TypedOperation(kind, rewrite)

    def test_discharge_and_release_have_different_account_proofs(self):
        satisfy = Event("Bob", "deliver", "Alice")
        release = Event("Alice", "release", "Bob")
        source = self.commitment(
            "c", "Bob", "Alice", satisfy, (satisfy,), (release,)
        )
        discharged = self.typed_closure(
            CommitmentOp.DISCHARGE, source, satisfy, "condition-obtained"
        )
        released = self.typed_closure(
            CommitmentOp.RELEASE, source, release, "creditor-release"
        )
        discharge_state = CommitmentContextState("Forum", frozenset({"p-discharge"}))
        release_state = CommitmentContextState(
            "Forum",
            frozenset({"p-release"}),
            frozenset(
                {OperationPolicy("Alice", CommitmentOp.RELEASE, "c")}
            ),
        )
        self.assertEqual(
            check_commitment_operation({"c": source}, {}, discharged, discharge_state),
            (),
        )
        self.assertEqual(
            check_commitment_operation({"c": source}, {}, released, release_state),
            (),
        )
        self.assertNotEqual(discharged.rewrite.closed, released.rewrite.closed)

    def test_context_policy_distinguishes_cancellation_from_deletion(self):
        cancel = Event("Bob", "cancel", "Alice")
        satisfy = Event("Bob", "deliver", "Alice")
        source = self.commitment("c", "Bob", "Alice", satisfy, (cancel,))
        operation = self.typed_closure(
            CommitmentOp.CANCEL, source, cancel, "policy-cancellation"
        )
        no_power = CommitmentContextState("Forum", frozenset({"p-cancel"}))
        with_power = CommitmentContextState(
            "Forum",
            frozenset({"p-cancel"}),
            frozenset({OperationPolicy("Bob", CommitmentOp.CANCEL, "c")}),
        )
        self.assertIn(
            "power.cancel_missing",
            check_commitment_operation({"c": source}, {}, operation, no_power),
        )
        self.assertEqual(
            check_commitment_operation({"c": source}, {}, operation, with_power),
            (),
        )

    def test_delegate_and_assign_change_different_directed_roles(self):
        delegate = Event("Forum", "delegate", "Carol")
        assign = Event("Alice", "assign", "Dana")
        done = Event("World", "task-done")

        source_d = self.commitment("c-d", "Bob", "Alice", done, (delegate, done))
        child_d = self.commitment("c-d2", "Carol", "Alice", done, (done,))
        rewrite_d = Rewrite(
            delegate,
            Certificate("p-delegate", delegate),
            (("c-d", ("c-d2",)),),
        )
        op_d = TypedOperation(CommitmentOp.DELEGATE, rewrite_d, "Carol")
        state_d = CommitmentContextState(
            "Forum",
            frozenset({"p-delegate"}),
            frozenset(
                {OperationPolicy("Forum", CommitmentOp.DELEGATE, "c-d", "Carol")}
            ),
        )

        source_a = self.commitment("c-a", "Bob", "Alice", done, (assign, done))
        child_a = self.commitment("c-a2", "Bob", "Dana", done, (done,))
        rewrite_a = Rewrite(
            assign,
            Certificate("p-assign", assign),
            (("c-a", ("c-a2",)),),
        )
        op_a = TypedOperation(CommitmentOp.ASSIGN, rewrite_a, "Dana")
        state_a = CommitmentContextState(
            "Forum",
            frozenset({"p-assign"}),
            frozenset(
                {OperationPolicy("Alice", CommitmentOp.ASSIGN, "c-a", "Dana")}
            ),
        )

        self.assertEqual(
            check_commitment_operation(
                {"c-d": source_d}, {"c-d2": child_d}, op_d, state_d
            ),
            (),
        )
        self.assertEqual(
            check_commitment_operation(
                {"c-a": source_a}, {"c-a2": child_a}, op_a, state_a
            ),
            (),
        )
        self.assertEqual(child_d.creditor, source_d.creditor)
        self.assertEqual(child_a.debtor, source_a.debtor)

    def test_context_can_be_creditor_of_an_impersonal_ought(self):
        file_report = Event("Office", "file-report", "Forum")
        ought = self.commitment(
            "public-duty", "Office", "Forum", file_report, (file_report,)
        )
        operation = self.typed_closure(
            CommitmentOp.DISCHARGE, ought, file_report, "report-filed"
        )
        state = CommitmentContextState("Forum", frozenset({"p-discharge"}))
        self.assertEqual(
            check_commitment_operation({"public-duty": ought}, {}, operation, state),
            (),
        )
        self.assertEqual(ought.creditor, ought.context)

    def test_policy_power_not_action_permission_changes_the_relation(self):
        cancel = Event("Bob", "say-cancel", "Alice")
        satisfy = Event("Bob", "deliver", "Alice")
        source = self.commitment("c", "Bob", "Alice", satisfy, (cancel,))
        operation = self.typed_closure(
            CommitmentOp.CANCEL, source, cancel, "recognized-cancel"
        )
        # Bob can utter the event in either state.  Only the context policy makes
        # the utterance an operative fact that closes the commitment.
        permission_only = CommitmentContextState("Forum", frozenset({"p-cancel"}))
        power = CommitmentContextState(
            "Forum",
            frozenset({"p-cancel"}),
            frozenset({OperationPolicy("Bob", CommitmentOp.CANCEL, "c")}),
        )
        self.assertIn(
            "power.cancel_missing",
            check_commitment_operation({"c": source}, {}, operation, permission_only),
        )
        self.assertEqual(
            check_commitment_operation({"c": source}, {}, operation, power),
            (),
        )
