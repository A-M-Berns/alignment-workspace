"""Frozen item-30 fixtures, policy runs, and answerability/service audit."""

from __future__ import annotations

from dataclasses import dataclass, replace
from decimal import Context, Decimal, localcontext
from fractions import Fraction as Q
from math import lcm
from random import Random
from typing import Mapping, Sequence

from phi_learner import (
    BlumMansourLearner,
    HedgeLearner,
    decimal_of,
    stationary_distribution,
    uniform_distribution,
)
from semantic_bridge import (
    AUDITED_PROGRAMS,
    LAMBDA,
    LawfulProgram,
    compile_label_map,
    decode_action,
    encode_response,
    frozen_environment_violations,
    label_loss,
    non_capture_audit,
)
from src import experiments as ex
from src.model import Accounting, ActualHistory, Response
from src.replay import actual_run, charge_of, faithful


HORIZONS = (12, 24, 48, 96)
LOSS_MAX = Q(2)
FAILURE_DELTA = Q(1, 2)


@dataclass(frozen=True)
class Fixture:
    fixture_id: str
    description: str
    history: ActualHistory


def persistent_interval(horizon: int) -> Fixture:
    """Every round carries an interval licensing decline-to-merits repair."""
    occasions = [ex.occasion(index) for index in range(horizon)]
    reasons = [ex.clearing_interval(index) for index in range(horizon)]
    history = ex.history(
        f"h:learner:persistent:{horizon}", occasions, ex.declines(occasions), reasons,
        horizon=horizon, accounting=Accounting({}, suspends=False))
    return Fixture("persistent_interval",
                   "a uniform positive decline-to-merits saving is available every round",
                   history)


def fully_licensed(horizon: int) -> Fixture:
    """All three reason kinds are live, exposing the common fixed default action."""
    occasions = [ex.occasion(index) for index in range(horizon)]
    reasons = []
    for index in range(horizon):
        reasons.extend((ex.clearing_interval(index),
                        ex.impediment(index, dates=4), ex.ripeness(index)))
    history = ex.history(
        f"h:learner:full:{horizon}", occasions, ex.declines(occasions), reasons,
        horizon=horizon, accounting=Accounting({}, suspends=False))
    return Fixture("fully_licensed",
                   "all nine programs are evaluated where interval, toll, and ripeness grounds are live",
                   history)


def impediment_pressure(horizon: int) -> Fixture:
    """Toll comparators create a nontrivial recurrent decline class."""
    occasions = [ex.occasion(index) for index in range(horizon)]
    reasons = [ex.impediment(index, dates=4) for index in range(horizon)]
    history = ex.history(
        f"h:learner:impediment:{horizon}", occasions, ex.declines(occasions), reasons,
        horizon=horizon, accounting=Accounting({}, suspends=False))
    return Fixture("impediment_pressure",
                   "toll-four repeatedly saves charge inside a recurrent decline class",
                   history)


FIXTURE_BUILDERS = (persistent_interval, impediment_pressure, fully_licensed)


def maps_for(history: ActualHistory, occasion) -> tuple[tuple[int, ...], ...]:
    """Compile all nine lawful programs into action-index maps."""
    index = {label: position for position, label in enumerate(LAMBDA)}
    return tuple(tuple(index[transform[label]] for label in LAMBDA)
                 for program in AUDITED_PROGRAMS
                 for transform in (compile_label_map(history, occasion, program),))


def charge_vector(occasion) -> tuple[Q, ...]:
    return tuple(label_loss(occasion, label) for label in LAMBDA)


def expected(distribution: Sequence[Q], values: Sequence[Q]) -> Q:
    return sum((probability * value
                for probability, value in zip(distribution, values)), Q(0))


def comparator_expected(distribution: Sequence[Q], loss: Sequence[Q],
                        action_map: Sequence[int]) -> Q:
    return sum((distribution[source] * loss[action_map[source]]
                for source in range(len(distribution))), Q(0))


def exact_sample(distribution: Sequence[Q], random: Random) -> int:
    """Sample a rational distribution without converting it to binary float."""
    denominator = 1
    for probability in distribution:
        denominator = lcm(denominator, probability.denominator)
    masses = [probability.numerator * (denominator // probability.denominator)
              for probability in distribution]
    draw = random.randrange(denominator)
    cumulative = 0
    for index, mass in enumerate(masses):
        cumulative += mass
        if draw < cumulative:
            return index
    raise AssertionError("rational sampler missed the unit interval")


@dataclass(frozen=True)
class PolicyRun:
    fixture_id: str
    horizon: int
    policy: str
    expected_charge: Decimal
    comparator_charge: Mapping[str, Decimal]
    regret: Mapping[str, Decimal]
    max_regret: Decimal
    normalized_regret: Decimal
    theorem_scale_ratio: Decimal
    source_bound: Decimal | None
    beta: Decimal | None
    failure_mass: Mapping[str, Decimal]
    sampled_history: ActualHistory | None = None


@dataclass(frozen=True)
class IntegrationAudit:
    well_formed_record: bool
    identity_replay_faithful: bool
    canonical_responses: bool
    no_burden_erasure: bool
    response_service_feasible: bool
    legality_non_capture: bool
    learning_computation_accounted: bool

    @property
    def integrated(self) -> bool:
        return all((self.well_formed_record, self.identity_replay_faithful,
                    self.canonical_responses, self.no_burden_erasure,
                    self.response_service_feasible, self.legality_non_capture,
                    self.learning_computation_accounted))


def _run_policy(fixture: Fixture, policy: str, *, precision: int = 80,
                sample_seed: int = 30) -> PolicyRun:
    history = fixture.history
    context = Context(prec=precision)
    action_count, rule_count = len(LAMBDA), len(AUDITED_PROGRAMS)
    learner = None
    hedge = None
    if policy == "blum_mansour":
        learner = BlumMansourLearner(history.horizon, action_count, rule_count,
                                     loss_max=LOSS_MAX, precision=precision)
    elif policy == "hedge_actions":
        hedge = HedgeLearner(history.horizon, action_count,
                             loss_max=LOSS_MAX, precision=precision)
    elif policy != "uniform":
        raise ValueError(f"unknown policy {policy!r}")

    expected_charge = Decimal(0)
    comparator_charge = {program.program_id: Decimal(0)
                         for program in AUDITED_PROGRAMS}
    failure_mass = {program.program_id: Decimal(0)
                    for program in AUDITED_PROGRAMS}
    sampled = dict(history.responses)
    random = Random(sample_seed)

    for occasion in history.actual_occasions():
        rolling = replace(history, responses=dict(sampled))
        maps = maps_for(rolling, occasion)
        losses = charge_vector(occasion)
        if learner is not None:
            prepared = learner.prepare(maps)
            distribution = prepared.distribution
        elif hedge is not None:
            distribution = hedge.distribution()
        else:
            distribution = uniform_distribution(action_count)

        with localcontext(context):
            expected_charge += decimal_of(expected(distribution, losses), context)
            for program_index, program in enumerate(AUDITED_PROGRAMS):
                transformed = comparator_expected(distribution, losses,
                                                  maps[program_index])
                comparator_charge[program.program_id] += decimal_of(transformed,
                                                                    context)
                mass = sum((distribution[source]
                            for source in range(action_count)
                            if maps[program_index][source] != source
                            and losses[source] - losses[maps[program_index][source]]
                            >= FAILURE_DELTA), Q(0))
                failure_mass[program.program_id] += decimal_of(mass, context)

        if learner is not None:
            learner.update(prepared, losses)
            chosen = exact_sample(distribution, random)
            sampled[occasion.occasion_id] = decode_action(occasion, LAMBDA[chosen])
        if hedge is not None:
            hedge.update(losses)

    regrets = {program.program_id: expected_charge
               - comparator_charge[program.program_id]
               for program in AUDITED_PROGRAMS}
    maximum = max(regrets.values())
    with localcontext(context):
        normalized = maximum / Decimal(history.horizon)
        theorem_scale = (decimal_of(LOSS_MAX, context)
                         * (Decimal(8 * history.horizon) * Decimal(9).ln()).sqrt())
        ratio = maximum / theorem_scale
    sampled_history = replace(history, history_id=f"{history.history_id}|sampled",
                              responses=dict(sampled)) if learner is not None else None
    return PolicyRun(
        fixture.fixture_id, history.horizon, policy, +expected_charge,
        {key: +value for key, value in comparator_charge.items()},
        {key: +value for key, value in regrets.items()}, +maximum, +normalized,
        +ratio, learner.source_regret_bound() if learner else None,
        learner.beta if learner else None,
        {key: +value for key, value in failure_mass.items()}, sampled_history)


def run_fixture(fixture: Fixture, *, precision: int = 80) -> tuple[PolicyRun, ...]:
    return tuple(_run_policy(fixture, policy, precision=precision)
                 for policy in ("uniform", "hedge_actions", "blum_mansour"))


def integration_audit(run: PolicyRun) -> IntegrationAudit:
    if run.sampled_history is None:
        raise ValueError("integration audit requires a sampled learner history")
    history = run.sampled_history
    replayed = actual_run(history)
    canonical = all(encode_response(occasion,
                                    history.responses[occasion.occasion_id]) in LAMBDA
                    for occasion in history.actual_occasions())
    no_erasure = all(
        not response.ledger.drops and not response.ledger.retargets
        and all(obligation == f"d:{occasion.occasion_id}"
                for obligation, _ in response.ledger.closes)
        for occasion in history.actual_occasions()
        for response in (history.responses[occasion.occasion_id],)
    )
    return IntegrationAudit(
        well_formed_record=not history.well_formed()
        and not frozen_environment_violations(history),
        identity_replay_faithful=faithful(history, replayed),
        canonical_responses=canonical,
        no_burden_erasure=no_erasure,
        response_service_feasible=replayed.feasible,
        legality_non_capture=not non_capture_audit(),
        # ServiceCosts prices dispositions only. It has no coordinate for the
        # 72 updates or exact stationary solve, so passing response capacity
        # cannot certify computation capacity.
        learning_computation_accounted=False,
    )


def recurrent_lower_bound(run: PolicyRun, program: LawfulProgram,
                          delta: Q = FAILURE_DELTA,
                          transient: Q = Q(0), *, precision: int = 80) -> Decimal:
    """Numerical instance of delta * mixed failure mass - B."""
    context = Context(prec=precision)
    with localcontext(context):
        return +(run.failure_mass[program.program_id] * decimal_of(delta, context)
                 - decimal_of(transient, context))


def repository_expected_loss(history: ActualHistory, occasion,
                             distribution: Sequence[Q]) -> Q:
    """Decode the mixture and recompute its repository charge exactly."""
    return sum((distribution[index]
                * charge_of(occasion, decode_action(occasion, label))
                for index, label in enumerate(LAMBDA)), Q(0))
