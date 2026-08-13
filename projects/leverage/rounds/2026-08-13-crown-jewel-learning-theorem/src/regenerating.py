"""The regenerating fixture, and the one decisive dynamics prosecution.

Every earlier fixture exhausted: a finite content set runs out of things to raise,
so the reason stops recurring with a positive margin and the dynamics question
cannot be asked. This one regenerates by construction.

**The process.** One demand type. Each date a fresh instance arrives and is due.
`answer` discharges it; `hold` leaves it outstanding. Loss is `w` if a demand is
left outstanding and `0` otherwise, so the margin is exactly `w` at every date and
the loss is bounded — a backlog is never accumulated, which is what keeps `H1`
true while the reason recurs forever.

**Why two responses.** With `|A| = 2` and both edges active the rule-mixture chain
is *irreducible*, so its stationary distribution is unique and fully determined by
the weights. Earlier fixtures had many absorbing actions, a reducible chain, and a
stationary distribution the implementation had to disambiguate from the initial
uniform — which pinned the recurrent class's total mass and capped how far
anything could move. This removes that confound rather than working around it.

**Why the return edge is coherent.** `hold` is licensed as an answer to a standing
`incoherence` demand: while something you cannot defend is outstanding, do not
take on further commitments. That is an independently certified consideration, not
an undoing of the first reason, and it is the same modest sense of coherence the
competing-reasons construction used.

**The control.** Identical process and identical graph, with the loss flat so
there is no margin. Any adaptation that survives the control is not feedback.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from interfaces import AnswerabilityProcess, CompiledRepair

HOLD = "hold"
ANSWER = "answer"
RESPONSES: Tuple[str, ...] = (HOLD, ANSWER)

#: The two public reasons. `service` regenerates; `incoherence` stands.
SERVICE = "service"
INCOHERENCE = "incoherence"

WEIGHT = Fraction(1)


@dataclass(frozen=True)
class State:
    """`outstanding` — a demand is owed an answer. `incoherent` — the standing one."""

    outstanding: bool
    incoherent: bool = True


def due(state: State, demand: str) -> bool:
    if demand == SERVICE:
        return state.outstanding
    if demand == INCOHERENCE:
        return state.incoherent
    raise ValueError(demand)


def licensed(state: State, demand: str, response: str) -> bool:
    """Admissibility, decided without reference to any loss.

    Answering discharges a due service demand. Holding is admissible while an
    incoherence stands — the caution against compounding it.
    """
    if demand == SERVICE:
        return response == ANSWER and state.outstanding
    if demand == INCOHERENCE:
        return response == HOLD and state.incoherent
    raise ValueError(demand)


def loss(state: State, response: str) -> Fraction:
    """`w` if a demand is left outstanding after the response, else `0`."""
    if not state.outstanding:
        return Fraction(0)
    return Fraction(0) if response == ANSWER else WEIGHT


def flat_loss(state: State, response: str) -> Fraction:
    """The uninformative control: same value for every response."""
    return WEIGHT if state.outstanding else Fraction(0)


def step(state: State, response: str) -> State:
    if state.outstanding and response == ANSWER:
        return State(outstanding=False, incoherent=state.incoherent)
    return state


def arrive(state: State) -> State:
    """A fresh service demand every date. This is what makes coverage sustained."""
    return State(outstanding=True, incoherent=state.incoherent)


def process(informative: bool = True) -> AnswerabilityProcess:
    return AnswerabilityProcess(
        responses=RESPONSES,
        due=due,
        licensed=licensed,
        loss=loss if informative else flat_loss,
        step=step,
        arrive=arrive,
        bound=WEIGHT,
    )


#: The targeted repair, and the independently certified return route.
ANSWER_THE_DEMAND = CompiledRepair("answer_the_demand", SERVICE, HOLD, ANSWER)
DO_NOT_COMPOUND = CompiledRepair("do_not_compound", INCOHERENCE, ANSWER, HOLD)
REPAIRS: Tuple[CompiledRepair, ...] = (ANSWER_THE_DEMAND, DO_NOT_COMPOUND)

START = State(outstanding=True, incoherent=True)


# ------------------------------------------------------------------ the run


@dataclass(frozen=True)
class Trace:
    """One trajectory's record, in the registers the theorem distinguishes."""

    target_mass: Tuple[Fraction, ...]
    selected: Tuple[bool, ...]
    margins: Tuple[Fraction, ...]
    bad_mass: Fraction
    exposure: int
    regret: Fraction

    def share(self, start: int, stop: int) -> Fraction:
        window = [m for m, s in zip(self.target_mass[start:stop], self.selected[start:stop]) if s]
        if not window:
            return Fraction(0)
        return sum(window, Fraction(0)) / Fraction(len(window))


def run(horizon: int, *, informative: bool = True, precision: int = 60) -> Trace:
    """Drive the repository's Theorem 18 learner on the regenerating process."""
    from phi_learner import BlumMansourLearner

    proc = process(informative)
    position = {a: i for i, a in enumerate(RESPONSES)}
    k_eff = len(REPAIRS) + 1
    engine = BlumMansourLearner(
        horizon, len(RESPONSES), k_eff, loss_max=proc.bound, precision=precision
    )

    state = START
    masses: List[Fraction] = []
    selected: List[bool] = []
    margins: List[Fraction] = []
    bad = Fraction(0)
    exposure = 0
    regret = Fraction(0)

    for _ in range(horizon):
        state = proc.arrive(state)
        maps = [tuple(range(len(RESPONSES)))]
        for repair in REPAIRS:
            image = repair.image(proc, state)
            maps.append(tuple(position[image[a]] for a in RESPONSES))
        prepared = engine.prepare(tuple(maps))
        distribution = {a: prepared.distribution[i] for i, a in enumerate(RESPONSES)}
        vector = proc.loss_vector(state)

        fires = ANSWER_THE_DEMAND.selects(proc, state)
        selected.append(fires)
        masses.append(distribution[HOLD])
        if fires:
            exposure += 1
            bad += distribution[HOLD]
            gap = vector[HOLD] - vector[ANSWER]
            margins.append(gap)
            regret += distribution[HOLD] * gap

        engine.update(prepared, [vector[a] for a in RESPONSES])
        action = max(RESPONSES, key=lambda a: (distribution[a], -RESPONSES.index(a)))
        state = proc.step(state, action)

    return Trace(
        tuple(masses), tuple(selected), tuple(margins), bad, exposure, regret
    )
