"""Can a return route arise from independently legitimate reasons?

The previous pass claimed that a normatively coherent repair class always leaves
its targets transient, on the ground that a return route would have to say "there
is an exposed burden, so having acknowledged, stop acknowledging".

That inference was too quick. A return route does **not** have to be licensed by
the same reason. It can be licensed by a *different* consideration that happens to
be active at the same time.

The three classes below are the prosecution.

`ONE_WAY`     a single repair, no return route.
`INCOHERENT`  a direct anti-repair: the same certificate licenses the undoing.
`COMPETING`   a return route licensed by a **different** public certificate, each
              edge defensible in its own right.

`COMPETING` uses two certificates that already exist in the merged model and were
not invented for this purpose:

    exposed_consequential_burden   a raised consequence is unanswered
                                   -> answer it rather than sit still

    defeated_applicability         a commitment is materially precluded and
                                   unsuspended
                                   -> do not take on further commitments while an
                                      incoherence is outstanding; sit still

Neither is an anti-repair. The second is a recognisable piece of normative
caution: while you are holding something you cannot defend, adding commitments
compounds the problem. Both can hold at once, and where they do the repair graph
has a cycle through the targeted response.
"""
from __future__ import annotations

from typing import Sequence, Tuple

from dynamics import Rule, identity_rule, surgical_rule
from learning import ACKNOWLEDGE, HOLD, LAMBDA, PublicStatus, certify

ACTIONS: Tuple[str, ...] = LAMBDA


class CertifiedEdge:
    """A repair edge together with the certificate licensing it."""

    def __init__(self, identifier: str, certificate: str, source: str, target: str):
        self.identifier = identifier
        self.certificate = certificate
        self.source = source
        self.target = target

    def fires(self, status: PublicStatus) -> bool:
        return certify(self.certificate, status)

    def rule(self) -> Rule:
        return surgical_rule(self.identifier, ACTIONS, self.source, self.target)


#: One repair, pointing away from the mistake. No route back.
ONE_WAY: Tuple[CertifiedEdge, ...] = (
    CertifiedEdge(
        "answer_the_exposed_burden", "exposed_consequential_burden", HOLD, ACKNOWLEDGE
    ),
)

#: The same certificate licensing the undoing. Normatively incoherent: it says
#: that a raised burden is a reason to stop answering it.
INCOHERENT: Tuple[CertifiedEdge, ...] = ONE_WAY + (
    CertifiedEdge(
        "unanswer_the_exposed_burden",
        "exposed_consequential_burden",
        ACKNOWLEDGE,
        HOLD,
    ),
)

#: A return route licensed by a different consideration. Each edge stands on its
#: own certificate, and both certificates can hold in one public state.
COMPETING: Tuple[CertifiedEdge, ...] = ONE_WAY + (
    CertifiedEdge(
        "do_not_compound_an_incoherence",
        "defeated_applicability",
        ACKNOWLEDGE,
        HOLD,
    ),
)


def active_rules(edges: Sequence[CertifiedEdge], status: PublicStatus) -> Tuple[Rule, ...]:
    """The rule list at this public status: the identity, plus every edge that fires.

    An edge whose certificate does not hold contributes the identity, which is
    what `surgical_rule` gives when the source is left alone — so the graph is
    built from the edges that actually fire.
    """
    rules = [identity_rule(ACTIONS)]
    for edge in edges:
        if edge.fires(status):
            rules.append(edge.rule())
    return tuple(rules)


def both_certificates_hold(status: PublicStatus) -> bool:
    """Whether the two competing certificates are simultaneously satisfied."""
    return status.has_unacknowledged and status.has_defeated_acknowledgment
