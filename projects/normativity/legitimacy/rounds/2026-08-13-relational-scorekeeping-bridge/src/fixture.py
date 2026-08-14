"""The finite population the prosecution runs against.

Three agents. `H` is the reasoner under test — the learner on one arc, the
principal on the other. `C` is a second scorekeeper who attributes and
challenges. `A` is an advisor with real epistemic authority and deliberately
partial practical authority.

Contents, and why each is here:

    p, q       the committive pair. `p => q` is the inference H will try to
               escape, first by disavowing q and then by dropping the rule.
    r          the ground of C's challenge. Incompatible with q.
    alpha      the premise of the reified-applicability pattern.
    beta       its conclusion.
    a_rho      the *content* that the pattern rho applies. Explicit and
               contestable: an object of commitment, entitlement and challenge
               like any other, not a rule.
    u          the undercutter. Incompatible with a_rho, so commitment to u
               defeats entitlement to a_rho while leaving commitment to a_rho
               untouched. That gap is the whole point of the pattern.
    s          an empirical input, entitled by default to whoever acknowledges
               it, used to witness that unanimity does not settle.
    act_x      an operational practical content, subject `operations`.
    act_c      the corrective move, subject `correction`.

The reified-applicability pattern is

    {alpha, a_rho} committive-entails beta

so `a_rho` sits in the premise set as an ordinary content. Asserting `a_rho`
does not install the rule; the rule is a fact about a practice, and an agent
whose practice lacks it draws no conclusion from `a_rho` at all. That is the
answer to the rule regress, and `test_applicability` is where it is checked.
"""
from __future__ import annotations

from scorekeeping import (
    Grant,
    Practice,
    State,
    Vocabulary,
    authority_over,
    pair,
    rule,
)

H, C, A = "H", "C", "A"

P, Q, R, W = "p", "q", "r", "w"
ALPHA, BETA, A_RHO, U = "alpha", "beta", "a_rho", "u"
S = "s"
ACT_X, ACT_C = "act_x", "act_c"

OPERATIONS = "operations"
CORRECTION = "correction"

VOCABULARY = Vocabulary(
    contents=frozenset(
        {P, Q, R, W, ALPHA, BETA, A_RHO, U, S, ACT_X, ACT_C}
    ),
    practical={ACT_X: OPERATIONS, ACT_C: CORRECTION},
)

#: The applicability pattern. `a_rho` is an ordinary content in the premise set.
#: Declared in *both* relations: it transmits commitment and, separately,
#: entitlement. That is what lets the undercutter defeat entitlement to `beta`
#: by defeating entitlement to `a_rho`, while leaving both commitments in force.
RHO = rule({ALPHA, A_RHO}, BETA)
#: What makes `a_rho` more than a bare assertion: it has a basis. Retracting the
#: acknowledgment therefore does not retract the commitment, which is what turns
#: the applicability-laundering attack into a real test rather than a retraction.
A_RHO_FROM_ALPHA = rule({ALPHA}, A_RHO)
P_ENTAILS_Q = rule({P}, Q)
#: The committive-only witness. Commitment to `q` commits to `w`; nothing
#: entitles anyone to `w`. `w` is therefore an ordinary unentitled consequence —
#: committed, never entitled, and not precluded — which is the state the model
#: could not express while committive rules transmitted entitlement.
Q_ENTAILS_W = rule({Q}, W)

#: The practice all three endorse at the start. `H` starting with the same one is
#: what makes the self-revision attack a revision rather than a standing
#: disagreement.
SHARED = Practice(
    committive=frozenset({P_ENTAILS_Q, RHO, A_RHO_FROM_ALPHA, Q_ENTAILS_W}),
    permissive=frozenset({P_ENTAILS_Q, RHO, A_RHO_FROM_ALPHA}),
    incompatible=frozenset({pair(Q, R), pair(A_RHO, U), pair(BETA, S)}),
)


def base_state(**overrides) -> State:
    """The starting position: H has asserted p, C has asserted r, A nothing."""
    defaults = dict(
        vocabulary=VOCABULARY,
        ack={H: frozenset({P}), C: frozenset({R}), A: frozenset()},
        practice={H: SHARED, C: SHARED, A: SHARED},
        grants=frozenset(
            {
                # H holds the corrective jurisdiction, and holds authority over
                # its own authority. Nothing else does — which is what the
                # corrigibility enumeration turns on.
                Grant(H, CORRECTION),
                Grant(H, authority_over(H)),
                Grant(H, authority_over(A)),
                # A may operate. It may not correct, and it may not alter anyone's
                # authority, including its own.
                Grant(A, OPERATIONS),
            }
        ),
    )
    defaults.update(overrides)
    return State(**defaults)
