"""The comparator-collapse attack, run in both readings.

Two candidate comparator classes over the same alphabet and the same states.

**Uniform reading.** A comparator is one state-independent map `phi: Lambda ->
Lambda` required to carry admissible labels to admissible labels at *every*
state. This is the reading that has the clean normative gloss — "a repair never
turns a permitted response into a forbidden one" — and it is the reading under
which the class was found to be the identity alone.

**Fixed-program reading.** A comparator is a fixed program whose guard reads the
public scorekeeping status, inducing a different map at different states. This is
the history-indexed modification rule the source online-learning theorem actually
quantifies over.

`core` implements the characterization that makes the uniform class computable
without enumerating `|Lambda|^|Lambda|` maps: `phi` is uniformly admissibility-
preserving exactly when `phi(a)` lies in the intersection of the admissible sets
containing `a`. `uniform_class_by_enumeration` checks that characterization
against brute force on a restricted alphabet, so the shortcut is verified rather
than assumed.
"""
from __future__ import annotations

from itertools import product
from typing import Dict, FrozenSet, Iterable, Sequence, Tuple

from learning import LAMBDA, defect, step
from scorekeeping import Agent, State


#: The two admissibility notions the attack is run under.
#:
#: `tolerant` — a label is admissible when it does not increase the public
#: answerability defect. Permissive, and the sets are wide.
#:
#: `responsive` — a label is admissible when it attains the least defect
#: available at that state. This is the notion that *responds to the record*, and
#: it is the one under which admissible sets pin down their own elements. The
#: architecture this round tests against found its collapse under a constraint of
#: this kind, so running only the tolerant notion would be a dodge.
TOLERANT = "tolerant"
RESPONSIVE = "responsive"


def admissible(
    state: State,
    learner: Agent,
    critic: Agent,
    alphabet: Sequence[str] = LAMBDA,
    notion: str = TOLERANT,
) -> FrozenSet[str]:
    """Labels admissible at this state. A predicate of state and label only."""
    losses = {
        label: defect(step(state, learner, critic, label), learner, critic)
        for label in alphabet
    }
    if notion == TOLERANT:
        here = defect(state, learner, critic)
        return frozenset(l for l in alphabet if losses[l] <= here)
    if notion == RESPONSIVE:
        least = min(losses.values())
        return frozenset(l for l in alphabet if losses[l] == least)
    raise ValueError(f"no such admissibility notion: {notion}")


def core(
    states: Iterable[State],
    learner: Agent,
    critic: Agent,
    alphabet: Sequence[str] = LAMBDA,
    notion: str = TOLERANT,
) -> Dict[str, FrozenSet[str]]:
    """`Core(a)`: the intersection of the admissible sets that contain `a`.

    A uniform map is admissibility-preserving over `states` exactly when it sends
    each label into that label's core, so the class is a product of the cores and
    is trivial exactly when every core is a singleton.
    """
    sets = [admissible(s, learner, critic, alphabet, notion) for s in states]
    out: Dict[str, FrozenSet[str]] = {}
    for label in alphabet:
        containing = [a for a in sets if label in a]
        if not containing:
            out[label] = frozenset(alphabet)
            continue
        intersection = frozenset(alphabet)
        for a in containing:
            intersection &= a
        out[label] = intersection
    return out


def pinned_labels(
    states: Iterable[State],
    learner: Agent,
    critic: Agent,
    alphabet: Sequence[str] = LAMBDA,
    notion: str = TOLERANT,
) -> FrozenSet[str]:
    """Labels a uniform comparator must leave alone: those with a singleton core.

    A label is pinned exactly when some state's admissible set pins it down. The
    collapse is the statement that every label is pinned; partial collapse — some
    labels pinned and others free — is the case the fixture actually exhibits, and
    it is more informative than either extreme.
    """
    cores = core(states, learner, critic, alphabet, notion)
    return frozenset(l for l in alphabet if cores[l] == frozenset({l}))


def uniform_class_is_identity_only(
    states: Iterable[State],
    learner: Agent,
    critic: Agent,
    alphabet: Sequence[str] = LAMBDA,
    notion: str = TOLERANT,
) -> bool:
    """Whether the uniform comparator class contains nothing but the identity."""
    cores = core(states, learner, critic, alphabet, notion)
    return all(cores[label] == frozenset({label}) for label in alphabet)


def uniform_class_by_enumeration(
    states: Sequence[State],
    learner: Agent,
    critic: Agent,
    alphabet: Sequence[str],
    notion: str = TOLERANT,
) -> Tuple[Tuple[Tuple[str, str], ...], ...]:
    """Every uniformly admissibility-preserving map, by brute force.

    Exponential in the alphabet, so it is used only to check `core` on a
    restricted alphabet. The shortcut is the thing that scales; this is what says
    the shortcut is right.
    """
    sets = [admissible(s, learner, critic, alphabet, notion) for s in states]
    out = []
    for image in product(alphabet, repeat=len(alphabet)):
        phi = dict(zip(alphabet, image))
        if all(
            all(phi[label] in a for label in a) for a in sets
        ):
            out.append(tuple(sorted(phi.items())))
    return tuple(sorted(out))
