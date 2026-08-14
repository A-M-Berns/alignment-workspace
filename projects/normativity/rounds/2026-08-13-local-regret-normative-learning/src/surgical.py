"""Source-action-specific repairs, and the regret quantity they induce.

The previous round's comparators rewrite many actions at once. That is fatal for
the result this round wants, because a comparator free to change several actions
can gain on the targeted mistake and lose elsewhere, and the loss on one action
cancels the gain on another before any lower bound can be read off.

A **surgical repair** is the shape the source theorem's own internal-regret family
already has:

    F^t(b) = r   when the public selector fires at t
    F^t(a) = a   for every other action, and at every unselected date

With that shape the regret decomposes exactly, with nothing to cancel:

    L_{H,I} - L_{H,I,F}
        = sum_t I(t) * p_b^t * ( loss_t(b) - loss_t(r) )

so if the gap is at least `delta` whenever the selector fires, the regret is at
least `delta` times the mixed mass the learner put on `b` at selected dates.

Each repair carries a **certificate** naming the positive public reason that
licenses it. The certificate is evaluated against `PublicStatus`, which carries no
loss, saving, future or date field, so lawfulness cannot be a function of what the
repair is worth.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Mapping, Sequence, Tuple

from learning import LAMBDA, PublicStatus, certify


@dataclass(frozen=True)
class SurgicalRepair:
    """A fixed declarative repair: one selector, one source action, one target.

    Holds strings only. There is no callable, so the record cannot close over a
    trajectory, a horizon, or anything about what the repair earns.
    """

    identifier: str
    #: The public normative reason licensing this repair, evaluated by `certify`.
    certificate: str
    #: The single source action this rule rewrites.
    source: str
    #: What it rewrites that action to.
    replacement: str

    def fires(self, status: PublicStatus) -> bool:
        """Whether the selector is on. A predicate of public status alone."""
        return certify(self.certificate, status)

    def transformation(self, status: PublicStatus) -> Dict[str, str]:
        """`F^t`: identity everywhere except the source action, when selected."""
        image = {label: label for label in LAMBDA}
        if self.fires(status):
            image[self.source] = self.replacement
        return image

    def indices(self, status: PublicStatus, alphabet: Sequence[str]) -> Tuple[int, ...]:
        """The same map as source-index -> target-index, for the learner."""
        image = self.transformation(status)
        position = {label: i for i, label in enumerate(alphabet)}
        return tuple(position[image[label]] for label in alphabet)


#: The repairs this round puts forward as theorem-facing. Each is identity except
#: on one source action, and each names a reason a scorekeeper could state.
REPAIRS: Tuple[SurgicalRepair, ...] = (
    SurgicalRepair(
        identifier="answer_the_exposed_burden",
        certificate="exposed_consequential_burden",
        source="hold",
        replacement="acknowledge",
    ),
    SurgicalRepair(
        identifier="stop_deploying_the_undercut",
        certificate="defeated_applicability",
        source="hold",
        replacement="suspend",
    ),
    SurgicalRepair(
        identifier="answer_rather_than_erase",
        certificate="live_unresolved_challenge",
        source="disavow",
        replacement="query",
    ),
    SurgicalRepair(
        identifier="vindicate_rather_than_hold",
        certificate="live_challenge_with_available_justification",
        source="hold",
        replacement="vindicate",
    ),
)


def identity_indices(alphabet: Sequence[str]) -> Tuple[int, ...]:
    return tuple(range(len(alphabet)))


# ------------------------------------------------------------------- regret


def modified_distribution(
    mixed: Mapping[str, Fraction], image: Mapping[str, str]
) -> Dict[str, Fraction]:
    """`f^t = F^t(p^t)`: mass moves from each source to its image.

    The source theorem's own definition — `f_i = sum over j with F(j) = i of p_j`.
    """
    out = {label: Fraction(0) for label in mixed}
    for label, mass in mixed.items():
        out[image[label]] += mass
    return out


def round_regret(
    mixed: Mapping[str, Fraction],
    losses: Mapping[str, Fraction],
    repair: SurgicalRepair,
    status: PublicStatus,
) -> Fraction:
    """One date's contribution to `L_{H,I} - L_{H,I,F}`.

    Both terms are scored against the **same** loss vector, which is the whole
    point: the transformed action is evaluated at the state that actually
    obtained, and the comparator's trajectory is never constructed.
    """
    image = repair.transformation(status)
    modified = modified_distribution(mixed, image)
    played = sum((mixed[a] * losses[a] for a in mixed), Fraction(0))
    swapped = sum((modified[a] * losses[a] for a in modified), Fraction(0))
    return played - swapped


def round_bad_mass(
    mixed: Mapping[str, Fraction], repair: SurgicalRepair, status: PublicStatus
) -> Fraction:
    """The mixed mass on the targeted pattern at this date: selector on, action `b`."""
    return mixed[repair.source] if repair.fires(status) else Fraction(0)


def round_gap(
    losses: Mapping[str, Fraction], repair: SurgicalRepair, status: PublicStatus
) -> Fraction:
    """`loss(b) - loss(r)` where the selector fires, else zero."""
    if not repair.fires(status):
        return Fraction(0)
    return losses[repair.source] - losses[repair.replacement]


# --------------------------------------------------- the reachability structure


def mixture_edges(
    repairs: Sequence[SurgicalRepair], status: PublicStatus
) -> Dict[str, frozenset]:
    """`a -> b` when some rule of the class (or the identity) sends `a` to `b`."""
    maps = [{label: label for label in LAMBDA}]
    maps.extend(repair.transformation(status) for repair in repairs)
    out: Dict[str, set] = {label: set() for label in LAMBDA}
    for image in maps:
        for label in LAMBDA:
            out[label].add(image[label])
    return {label: frozenset(targets) for label, targets in out.items()}


def reachable(edges: Mapping[str, frozenset], start: str) -> frozenset:
    seen, frontier = {start}, [start]
    while frontier:
        current = frontier.pop()
        for following in edges[current]:
            if following not in seen:
                seen.add(following)
                frontier.append(following)
    return frozenset(seen)


def transient(
    repairs: Sequence[SurgicalRepair], status: PublicStatus
) -> frozenset:
    """Actions that leak under the rule mixture and cannot be returned to.

    The Theorem 18 construction plays a stationary distribution of the
    rule-mixture chain, and a stationary distribution is supported on the
    recurrent states. So a transient action carries **zero mixed mass at every
    date**, and the pattern-elimination conclusion holds for it vacuously.

    This is what happens when the repair class consists only of genuine repairs:
    every rule points away from a mistake toward a better response, so every
    targeted action leaks and nothing points back. See `PROSECUTION.md`.
    """
    edges = mixture_edges(repairs, status)
    return frozenset(
        label
        for label in LAMBDA
        if not all(label in reachable(edges, other) for other in reachable(edges, label))
    )
