from __future__ import annotations

import unittest

from role_kernel import (
    Certificate,
    Event,
    Liability,
    PublicState,
    ReasonViews,
    Rewrite,
    StandingWrapper,
    adjudicate,
    answerable_to,
    basis_losses,
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
