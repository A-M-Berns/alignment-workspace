"""The finite episode, with the principal's choice as an argument of the world.

The change from `projects/deference/notes/FINITE_MODEL_SKELETON.md` v2 is one
type. There a conduct is a proposal `alpha : Omega -> Pi_n`, so the principal's
judgment enters only by way of `J_n`, and a conduct predicting `J_n` perfectly
*is* `DELEGATE` as a function. Here a conduct carries three things,

    prep      : cell -> Preparation             chosen at t(n)
    channel   : cell x choice -> choice         what the world sees, given what
                                                the principal chose
    implement : cell x choice -> action         read at the realized choice

and the quantity is `X(omega, prep, choice, action)`. The principal-level choice
is an argument of the world rather than a route to one. This is
`prompts/2026-08-11-deference-channel/REPORT.md` §9.2's *report coordinate*
patch, instantiated.

**There is no authorization field.** Whether a conduct defers is read off
`channel` — it defers at a cell exactly when `channel` is the identity on what
the preparation left open. `lean/Workspace/Deference/Contrib/StaticViewFactorization.lean`
says a value factoring through price and realization cannot see a hidden
authorization payload, and the reply it forces is that authorization must enter
before that boundary. Here it enters as the identity of a function, which is
before it: two conducts with the same realized quantity everywhere can have
different channels.

Nothing here relates the principal's grade to the quantity. The skeleton
declares that relation absent (§8.5) and this round does not supply it;
`repair.py` is where the absence surfaces, as a term that is named and not
bounded.

The order on `choices` is fixed and is the tie-break, so no statement below can
exploit tie-break freedom. Every number is a `fractions.Fraction`.

Provisional names (`AGENTS.md` §6): `Preparation`, `residual`, `forecloses`,
`Episode`, `selector`, `Conduct`, `channel`, `mediates`, `preemptive`,
`response`, `Predictor`, `prediction_error`, `channel_disagreement`.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Iterable, Mapping, Sequence


@dataclass(frozen=True)
class Preparation:
    """An action taken at `t(n)`, before the principal's choice is available.

    `residual` is what the principal can still realize after it. A preparation
    carrying the whole choice set preserves the selector; one carrying a single
    element has destroyed it. Nothing else about a preparation is modelled: what
    it costs is in the quantity, what it leaves open is here.
    """

    name: str
    residual: tuple[str, ...]

    def forecloses(self, choices: Sequence[str]) -> bool:
        return len(self.residual) < 2 <= len(choices)

    def narrows(self, choices: Sequence[str]) -> bool:
        return set(self.residual) != set(choices)


@dataclass(frozen=True)
class Episode:
    """One decision index, in two stages.

    `cell` is `A`'s information at `t(n)`: every coordinate of a conduct is
    constant on a cell. The principal's choice need not be, and that is the
    asymmetry the round runs on. As in the skeleton, a model in which it happens
    to be cell-constant is permitted — that is the perfectly predictable
    principal, which the programme is forbidden to rule out.
    """

    name: str
    states: tuple[str, ...]
    cell: Mapping[str, str]
    credence: Mapping[str, Fraction]
    choices: tuple[str, ...]
    preparations: tuple[Preparation, ...]
    actions: tuple[str, ...]
    grade: Mapping[tuple[str, str], Fraction]
    quantity: Mapping[tuple[str, str, str, str], Fraction]
    bound: Fraction

    def __post_init__(self) -> None:
        if sum(self.credence.values()) != Fraction(1):
            raise ValueError(f"{self.name}: credence does not sum to one")
        if any(mass < 0 for mass in self.credence.values()):
            raise ValueError(f"{self.name}: negative credence")
        for state, choice in product(self.states, self.choices):
            if abs(self.grade[(state, choice)]) > self.bound:
                raise ValueError(f"{self.name}: grade at {state},{choice} out of bound")
        for prep, choice, action in product(self.preparations, self.choices,
                                            self.actions):
            for state in self.states:
                key = (state, prep.name, choice, action)
                if key not in self.quantity:
                    raise ValueError(f"{self.name}: quantity undefined at {key}")
                if abs(self.quantity[key]) > self.bound:
                    raise ValueError(f"{self.name}: quantity {key} out of bound")

    @property
    def cells(self) -> tuple[str, ...]:
        seen: list[str] = []
        for state in self.states:
            if self.cell[state] not in seen:
                seen.append(self.cell[state])
        return tuple(seen)

    def states_of(self, cell: str) -> tuple[str, ...]:
        return tuple(s for s in self.states if self.cell[s] == cell)

    def mass(self, cell: str) -> Fraction:
        return sum((self.credence[s] for s in self.states_of(cell)), Fraction(0))

    def preparation(self, name: str) -> Preparation:
        for prep in self.preparations:
            if prep.name == name:
                return prep
        raise KeyError(f"{self.name}: no preparation {name}")

    # ---------------------------------------------------------------- selector

    def selector(self, state: str, prep_name: str) -> str:
        """`D_n`: the principal's own choice, over what is still open.

        The least grade-maximiser in the fixed order, taken over the residual
        range. With the full range this is the skeleton's `J_n`; with a narrowed
        range it is what the principal can still reach, so a preparation that
        destroys options shows up inside the selector rather than beside it.
        """
        residual = self.preparation(prep_name).residual
        return max(residual,
                   key=lambda d: (self.grade[(state, d)], -self.choices.index(d)))

    def unconstrained_selector(self, state: str) -> str:
        return max(self.choices,
                   key=lambda d: (self.grade[(state, d)], -self.choices.index(d)))

    def project(self, choice: str, prep_name: str) -> str:
        """Where a choice lands when the preparation has closed it off."""
        residual = self.preparation(prep_name).residual
        if choice in residual:
            return choice
        return min(residual, key=self.choices.index)


@dataclass(frozen=True)
class Conduct:
    """A preparation, a channel and an implementation table.

    `channel[(cell, d)]` is the choice the world sees when the principal chose
    `d`. Deference is `channel` being the identity; preemption is anything else.
    A conduct writing a constant is the rigid preemptor; a conduct writing a
    permutation is the systematic overrider, which varies with the principal and
    still does not defer to it.
    """

    name: str
    prep: Mapping[str, str]
    channel: Mapping[tuple[str, str], str]
    implement: Mapping[tuple[str, str], str]


def well_formed(episode: Episode, conduct: Conduct) -> bool:
    for cell in episode.cells:
        if cell not in conduct.prep:
            return False
        try:
            episode.preparation(conduct.prep[cell])
        except KeyError:
            return False
        for choice in episode.choices:
            if conduct.channel.get((cell, choice)) not in episode.choices:
                return False
            if conduct.implement.get((cell, choice)) not in episode.actions:
                return False
    return True


def mediates(episode: Episode, conduct: Conduct, cell: str) -> bool:
    """The channel is the identity on what the preparation left open."""
    residual = episode.preparation(conduct.prep[cell]).residual
    return all(conduct.channel[(cell, d)] == d for d in residual)


def mediated(episode: Episode, conduct: Conduct) -> bool:
    return all(mediates(episode, conduct, cell) for cell in episode.cells)


def preemptive(episode: Episode, conduct: Conduct) -> bool:
    return not mediated(episode, conduct)


def realized_choice(episode: Episode, conduct: Conduct, state: str) -> str:
    cell = episode.cell[state]
    return conduct.channel[(cell, episode.selector(state, conduct.prep[cell]))]


def realized_quantity(episode: Episode, conduct: Conduct, state: str) -> Fraction:
    cell = episode.cell[state]
    prep = conduct.prep[cell]
    choice = realized_choice(episode, conduct, state)
    return episode.quantity[(state, prep, choice, conduct.implement[(cell, choice)])]


def value(episode: Episode, conduct: Conduct) -> Fraction:
    """`V_n`, the ordinary register. No authority term, by construction.

    A repair that fails here and passes once delegation is paid a bonus has not
    been tested, so the bonus is not available.
    """
    return sum((episode.credence[s] * realized_quantity(episode, conduct, s)
                for s in episode.states), Fraction(0))


# --------------------------------------------------------------------------
# The response map: what the conduct does under an intervention on the choice
# --------------------------------------------------------------------------

def response(episode: Episode, conduct: Conduct, cell: str,
             choice: str) -> tuple[str, str, str]:
    """`(preparation, realized choice, action)` when the principal chooses `choice`.

    The object a realized run does not contain, and the reason conducts are typed
    on the choice coordinate. `prompts/2026-08-11-deference-channel/REPORT.md`
    Proposition 8 says no criterion computable from one realized instance
    separates delegation from an accurate simulator, and nothing here contradicts
    it: this is a criterion on the conduct, not on its trace.

    The intervention is surgical — it sets the principal's choice and does not
    propagate to whatever `A` used to predict it. `mediation.py` records that
    this is well defined exactly under non-capture; where the advisor authors the
    choice, the two are not independently variable and there is no map to take.
    """
    prep = conduct.prep[cell]
    reached = episode.project(choice, prep)
    realized = conduct.channel[(cell, reached)]
    return (prep, realized, conduct.implement[(cell, realized)])


def response_map(episode: Episode, conduct: Conduct) -> dict:
    return {(cell, choice): response(episode, conduct, cell, choice)
            for cell in episode.cells for choice in episode.choices}


def responds_to_the_choice(episode: Episode, conduct: Conduct) -> bool:
    """Some intervention on the principal's choice changes what the conduct does.

    Strictly weaker than mediation, and the round keeps them apart because the
    Cartesian-frame register cannot: a process executing the negation of the
    principal's choice responds to it and does not defer to it.
    """
    seen = response_map(episode, conduct)
    return any(seen[(cell, a)] != seen[(cell, b)]
               for cell in episode.cells
               for a, b in product(episode.choices, repeat=2))


# --------------------------------------------------------------------------
# Prediction
# --------------------------------------------------------------------------

Predictor = Mapping[str, str]


def best_prediction(episode: Episode, prep: Mapping[str, str]) -> dict[str, str]:
    """`d^`: `A`'s cell-measurable guess at the selector, by credence mass.

    Ties break by the fixed order on choices, as everywhere else.
    """
    out: dict[str, str] = {}
    for cell in episode.cells:
        weight = {choice: Fraction(0) for choice in episode.choices}
        for state in episode.states_of(cell):
            weight[episode.selector(state, prep[cell])] += episode.credence[state]
        out[cell] = max(episode.choices,
                        key=lambda d: (weight[d], -episode.choices.index(d)))
    return out


def prediction_error(episode: Episode, prep: Mapping[str, str],
                     predictor: Predictor) -> Fraction:
    """`eps_pred`: the credence of states where the guess misses the selector.

    A magnitude quantity and not a signed one. `LI_PREDICTION_INTERFACE.md` says
    why the distinction decides whether Logical Induction can supply it.
    """
    return sum((episode.credence[s] for s in episode.states
                if episode.selector(s, prep[episode.cell[s]])
                != predictor[episode.cell[s]]), Fraction(0))


def channel_disagreement(episode: Episode, conduct: Conduct) -> Fraction:
    """The credence on which the conduct's channel moves the principal's choice.

    This — not the prediction error — is what the repair bound is in. The two
    coincide for a conduct that preempts in order to act on what it predicts,
    and come apart for one that preempts in order to install something else.
    """
    total = Fraction(0)
    for state in episode.states:
        cell = episode.cell[state]
        chosen = episode.selector(state, conduct.prep[cell])
        if conduct.channel[(cell, chosen)] != chosen:
            total += episode.credence[state]
    return total


# --------------------------------------------------------------------------
# Conduct constructors and enumeration
# --------------------------------------------------------------------------

def identity_channel(episode: Episode) -> dict[tuple[str, str], str]:
    return {(cell, choice): choice
            for cell in episode.cells for choice in episode.choices}


def constant_channel(episode: Episode,
                     written: Mapping[str, str]) -> dict[tuple[str, str], str]:
    return {(cell, choice): written[cell]
            for cell in episode.cells for choice in episode.choices}


def permuted_channel(episode: Episode,
                     permutation: Mapping[str, str]) -> dict[tuple[str, str], str]:
    return {(cell, choice): permutation[choice]
            for cell in episode.cells for choice in episode.choices}


def mediated_conducts(episode: Episode,
                      preps: Iterable[Mapping[str, str]] | None = None
                      ) -> list[Conduct]:
    """Every mediated conduct over a family of preparations, exhaustively.

    The comparisons in `repair.py` are against the whole class rather than
    against a chosen member of it.
    """
    cells = episode.cells
    family = (list(preps) if preps is not None else
              [dict(zip(cells, combo))
               for combo in product([p.name for p in episode.preparations],
                                    repeat=len(cells))])
    keys = [(cell, choice) for cell in cells for choice in episode.choices]
    channel = identity_channel(episode)
    out: list[Conduct] = []
    for prep in family:
        for actions in product(episode.actions, repeat=len(keys)):
            out.append(Conduct(f"mediated-{len(out)}", dict(prep), channel,
                               dict(zip(keys, actions))))
    return out


def best_mediated(episode: Episode,
                  preps: Iterable[Mapping[str, str]] | None = None) -> Conduct:
    return max(mediated_conducts(episode, preps),
               key=lambda c: value(episode, c))
