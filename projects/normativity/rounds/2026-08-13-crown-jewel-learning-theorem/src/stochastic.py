"""The stochastic register: what is random once the action is genuinely sampled.

The earlier rounds realized the action deterministically, which made `Q_T` a
number. Under genuine sampling the state depends on the drawn action, so

    S_t, p_t, E_t^g, M_T^g, Q_T^g, N_T^g

are all random. In particular `Q_T` is **not** deterministic, so

    E[N_T] = Q_T

is ill-typed. The correct identity is between expectations:

    E[N_T] = E[Q_T]

and structurally, writing `D_t = 1[a_t = b] - p_t(b)` on selected dates, each
`D_t` has conditional mean zero given the strict history, so `N_T - Q_T` is a sum
of martingale differences. Its expectation is zero; bounding it with high
probability needs a concentration argument this round does not supply.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from random import Random
from typing import List, Sequence, Tuple

from actual import loaded_start, loss_vector, replenishing
from competing import ACTIONS, COMPETING, active_rules
from fixture import C, H, U
from learning import HOLD, public_status, step
from moves import Move, apply_move
from phi_learner import BlumMansourLearner

POSITION = {a: i for i, a in enumerate(ACTIONS)}
TARGET = HOLD


def draw(distribution: Sequence[Fraction], random: Random) -> int:
    """Exact sampling from a rational distribution. No floating point."""
    threshold = Fraction(random.randrange(10 ** 9), 10 ** 9)
    cumulative = Fraction(0)
    for index, mass in enumerate(distribution):
        cumulative += mass
        if threshold < cumulative:
            return index
    return len(distribution) - 1


@dataclass(frozen=True)
class SampledRun:
    """One realized trajectory, with both registers recorded."""

    #: `Q_T`: cumulative mixed mass on the target at selected dates. Random.
    bad_mass: Fraction
    #: `N_T`: cumulative count of *drawn* target actions at selected dates. Random.
    bad_count: int
    #: `M_T`: number of selected dates. Also random.
    selected: int


def sampled_run(seed: int, horizon: int = 12) -> SampledRun:
    """Play the competing-reasons class with a genuinely sampled action."""
    random = Random(seed)
    k_eff = len(COMPETING) + 1
    engine = BlumMansourLearner(
        horizon, len(ACTIONS), k_eff, loss_max=Fraction(22), precision=50
    )
    state = apply_move(loaded_start(), Move("assert", H, content=U))
    mass, count, selected = Fraction(0), 0, 0
    for _ in range(horizon):
        state = replenishing(state, C, H)
        status = public_status(state, H, C)
        rules = active_rules(COMPETING, status)
        maps = [tuple(POSITION[r.sends(a)] for a in ACTIONS) for r in rules]
        while len(maps) < k_eff:
            maps.append(tuple(range(len(ACTIONS))))
        prepared = engine.prepare(tuple(maps))
        distribution = list(prepared.distribution)
        vector = loss_vector(state, H, C)
        if status.has_unacknowledged:
            selected += 1
            mass += distribution[POSITION[TARGET]]
        index = draw(distribution, random)
        if status.has_unacknowledged and ACTIONS[index] == TARGET:
            count += 1
        engine.update(prepared, [vector[label] for label in ACTIONS])
        state = step(state, H, C, ACTIONS[index])
    return SampledRun(mass, count, selected)


def expected_counts(runs: Sequence[SampledRun]) -> Tuple[Fraction, Fraction]:
    """Empirical `(mean N_T, mean Q_T)`. The identity is between these."""
    size = Fraction(len(runs))
    mean_count = Fraction(sum(r.bad_count for r in runs)) / size
    mean_mass = sum((r.bad_mass for r in runs), Fraction(0)) / size
    return mean_count, mean_mass


def compensator_gap(runs: Sequence[SampledRun]) -> Fraction:
    """Empirical mean of `N_T - Q_T`, which the martingale structure centres at zero."""
    mean_count, mean_mass = expected_counts(runs)
    return mean_count - mean_mass
