"""When can a swap-regret fixed point put mass on a targeted bad response?

The Blum--Mansour construction plays `p^t`, the stationary distribution of the
Markov chain whose row `i` mixes the rules' images of `i` by their weights. A
stationary distribution is supported on the recurrent states, so an action that is
transient in that chain carries **zero mass**, whatever the weights are and
whatever has been observed.

That makes the graph, not the feedback, decide whether a targeted response is ever
played. This module states the condition exactly and lets it be tested.

Two facts do the work.

**The identity is always in the class**, so every action has a self-loop and no
row is empty. Self-loops do not rescue a state from transience: an action that can
leak to somewhere it cannot return from is transient regardless.

**A repair fires exactly when its selector fires.** So at every date the repair
`g` is *selected* — which is exactly the set of dates `M_T(g)` counts — the source
`b_g` has an outgoing edge to `r_g`. Its mass is therefore zero at those dates
unless the class also supplies a route back to `b_g` **active at the same date**.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, FrozenSet, Iterable, Mapping, Sequence, Tuple

Action = str


@dataclass(frozen=True)
class Rule:
    """One date's modification map, as data."""

    identifier: str
    image: Mapping[Action, Action]

    def sends(self, action: Action) -> Action:
        return self.image[action]


def identity_rule(actions: Sequence[Action]) -> Rule:
    return Rule("identity", {a: a for a in actions})


def surgical_rule(
    identifier: str, actions: Sequence[Action], source: Action, replacement: Action
) -> Rule:
    image = {a: a for a in actions}
    image[source] = replacement
    return Rule(identifier, image)


def edges(rules: Sequence[Rule], actions: Sequence[Action]) -> Dict[Action, FrozenSet[Action]]:
    """`i -> j` when some active rule sends `i` to `j`.

    The support of row `i` of the mixture chain, for any strictly positive weights.
    """
    out: Dict[Action, set] = {a: set() for a in actions}
    for rule in rules:
        for a in actions:
            out[a].add(rule.sends(a))
    return {a: frozenset(targets) for a, targets in out.items()}


def reachable(graph: Mapping[Action, FrozenSet[Action]], start: Action) -> FrozenSet[Action]:
    seen, stack = {start}, [start]
    while stack:
        current = stack.pop()
        for following in graph[current]:
            if following not in seen:
                seen.add(following)
                stack.append(following)
    return frozenset(seen)


def is_transient(graph: Mapping[Action, FrozenSet[Action]], action: Action) -> bool:
    """`action` leaks somewhere it cannot return from.

    Equivalently: some state reachable from it cannot reach it back. A stationary
    distribution assigns zero to exactly these.
    """
    return any(action not in reachable(graph, other) for other in reachable(graph, action))


def zero_mass_actions(
    rules: Sequence[Rule], actions: Sequence[Action]
) -> FrozenSet[Action]:
    """Actions the stationary distribution must give zero, for any positive weights."""
    graph = edges(rules, actions)
    return frozenset(a for a in actions if is_transient(graph, a))


def has_return_route(
    rules: Sequence[Rule], actions: Sequence[Action], source: Action
) -> bool:
    """Whether some action `source` can reach can reach `source` back.

    The exact thing that has to be true, at a selected date, for the targeted
    response to carry any mass at all.
    """
    graph = edges(rules, actions)
    return not is_transient(graph, source)


# ------------------------------------------------- the pre-registered criterion


@dataclass(frozen=True)
class LearningEvidence:
    """What a run would have to show to count as learning rather than compliance.

    Fixed before looking for a learner, so that a construction cannot be declared
    to learn on the strength of whatever it happens to do.
    """

    #: (1) the learner put real mass on the targeted response before any relevant
    #: feedback.
    initial_mass: object
    #: (2) the pattern recurred.
    selected_dates: int
    #: (5) mass at late selected dates is below mass at early ones.
    early_mass: object
    late_mass: object
    #: (6) the same adaptation does not occur when the loss carries no information.
    adapts_without_information: bool

    def counts_as_learning(self, threshold) -> bool:
        return (
            self.initial_mass > threshold
            and self.selected_dates > 0
            and self.late_mass < self.early_mass
            and not self.adapts_without_information
        )
