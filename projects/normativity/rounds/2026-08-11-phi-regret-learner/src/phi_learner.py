"""Theorem-facing Blum--Mansour learner and controlled numerical baselines.

The source update contains a real parameter raised to rational exponents.  The
weights are therefore numerical ``Decimal`` approximations.  At every round the
finite decimals are reinterpreted as exact rationals; the transition matrix and
the selected stationary distribution are exact for those approximate weights.
No theorem claim depends on agreement between Decimal and real arithmetic.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Context, Decimal, localcontext
from fractions import Fraction as Q
from typing import Sequence


def decimal_of(value: Q | int | Decimal, context: Context) -> Decimal:
    """Convert an exact rational to Decimal under the declared context."""
    if isinstance(value, Decimal):
        return context.create_decimal(value)
    value = Q(value)
    with localcontext(context):
        return Decimal(value.numerator) / Decimal(value.denominator)


def decimal_text(value: Decimal, places: int = 12) -> str:
    """Stable fixed-width output for numerical experiment tables."""
    quantum = Decimal(1).scaleb(-places)
    return format(value.quantize(quantum), "f")


def _validate_distribution(distribution: Sequence[Q]) -> None:
    if any(value < 0 for value in distribution):
        raise ValueError("a probability is negative")
    if sum(distribution, Q(0)) != 1:
        raise ValueError("probabilities do not sum to one")


def _validate_transition(matrix: Sequence[Sequence[Q]]) -> None:
    size = len(matrix)
    if not size or any(len(row) != size for row in matrix):
        raise ValueError("transition matrix must be nonempty and square")
    for row in matrix:
        _validate_distribution(row)


def _solve_unique(matrix: Sequence[Sequence[Q]], target: Sequence[Q]) -> tuple[Q, ...]:
    """Exact RREF solver for a consistent system with a unique solution."""
    rows = [list(map(Q, row)) + [Q(rhs)] for row, rhs in zip(matrix, target)]
    if not rows:
        return ()
    columns = len(rows[0]) - 1
    pivot_row = 0
    pivots: dict[int, int] = {}
    for column in range(columns):
        found = next((index for index in range(pivot_row, len(rows))
                      if rows[index][column]), None)
        if found is None:
            continue
        rows[pivot_row], rows[found] = rows[found], rows[pivot_row]
        scale = rows[pivot_row][column]
        rows[pivot_row] = [value / scale for value in rows[pivot_row]]
        for index in range(len(rows)):
            if index == pivot_row or not rows[index][column]:
                continue
            multiple = rows[index][column]
            rows[index] = [left - multiple * right
                           for left, right in zip(rows[index], rows[pivot_row])]
        pivots[column] = pivot_row
        pivot_row += 1
        if pivot_row == len(rows):
            break
    for row in rows:
        if all(value == 0 for value in row[:-1]) and row[-1] != 0:
            raise ValueError("stationary system is inconsistent")
    if len(pivots) != columns:
        raise ValueError("stationary system is not uniquely determined")
    return tuple(rows[pivots[column]][-1] for column in range(columns))


def _communicating_classes(matrix: Sequence[Sequence[Q]]) -> tuple[tuple[int, ...], ...]:
    """Closed communicating classes of a finite transition matrix."""
    size = len(matrix)
    reachable = [[bool(matrix[i][j]) for j in range(size)] for i in range(size)]
    for i in range(size):
        reachable[i][i] = True
    for k in range(size):
        for i in range(size):
            if reachable[i][k]:
                for j in range(size):
                    reachable[i][j] = reachable[i][j] or reachable[k][j]
    unused = set(range(size))
    components: list[tuple[int, ...]] = []
    while unused:
        first = min(unused)
        component = tuple(i for i in range(size)
                          if reachable[first][i] and reachable[i][first])
        unused.difference_update(component)
        components.append(component)
    return tuple(component for component in components
                 if all(matrix[i][j] == 0
                        for i in component for j in range(size)
                        if j not in component))


def _class_stationary(matrix: Sequence[Sequence[Q]],
                      component: Sequence[int]) -> tuple[Q, ...]:
    """Unique stationary distribution within one closed irreducible class."""
    indices = tuple(component)
    size = len(indices)
    equations: list[list[Q]] = []
    targets: list[Q] = []
    for destination in indices:
        equations.append([
            matrix[source][destination] - (Q(1) if source == destination else Q(0))
            for source in indices
        ])
        targets.append(Q(0))
    equations.append([Q(1)] * size)
    targets.append(Q(1))
    return _solve_unique(equations, targets)


def stationary_distribution(matrix: Sequence[Sequence[Q]],
                            initial: Sequence[Q] | None = None) -> tuple[Q, ...]:
    """Exact uniform-start Cesaro-limit stationary distribution.

    A reducible finite chain has many stationary distributions.  This selector
    uses the limiting recurrent-class weights obtained from ``initial`` (uniform
    by default), then the unique stationary distribution inside each closed
    class.  It is deterministic and remains an admissible choice in Theorem 18.
    """
    _validate_transition(matrix)
    size = len(matrix)
    start = tuple(initial) if initial is not None else tuple(Q(1, size)
                                                            for _ in range(size))
    _validate_distribution(start)
    classes = _communicating_classes(matrix)
    recurrent = frozenset(index for component in classes for index in component)
    transient = tuple(index for index in range(size) if index not in recurrent)
    result = [Q(0)] * size

    for component in classes:
        class_weight = sum((start[index] for index in component), Q(0))
        if transient:
            equations = []
            targets = []
            for source in transient:
                equations.append([
                    (Q(1) if source == destination else Q(0))
                    - matrix[source][destination]
                    for destination in transient
                ])
                targets.append(sum((matrix[source][destination]
                                    for destination in component), Q(0)))
            absorption = _solve_unique(equations, targets)
            class_weight += sum((start[source] * absorption[offset]
                                 for offset, source in enumerate(transient)), Q(0))
        within = _class_stationary(matrix, component)
        for offset, index in enumerate(component):
            result[index] += class_weight * within[offset]

    distribution = tuple(result)
    _validate_distribution(distribution)
    pushed = tuple(sum((distribution[source] * matrix[source][destination]
                        for source in range(size)), Q(0))
                   for destination in range(size))
    if pushed != distribution:
        raise AssertionError("stationary selector returned a nonstationary vector")
    return distribution


def transition_from_weights(weights: Sequence[Sequence[Decimal]],
                            maps: Sequence[Sequence[int]]) -> tuple[tuple[Q, ...], ...]:
    """Build the exact rational transformation-weighted transition matrix."""
    action_count = len(weights)
    if not action_count or len(maps) == 0:
        raise ValueError("weights and modification maps must be nonempty")
    rule_count = len(maps)
    if any(len(row) != rule_count for row in weights):
        raise ValueError("one weight is required per source action and rule")
    if any(len(rule) != action_count for rule in maps):
        raise ValueError("every modification rule must be total on the actions")
    result: list[tuple[Q, ...]] = []
    for source, row in enumerate(weights):
        exact = tuple(Q(value) for value in row)
        if any(value <= 0 for value in exact):
            raise ValueError("Blum--Mansour row weights must remain positive")
        total = sum(exact, Q(0))
        transition = [Q(0)] * action_count
        for rule_index, target in enumerate(rule[source] for rule in maps):
            if target < 0 or target >= action_count:
                raise ValueError("a modification rule leaves the action set")
            transition[target] += exact[rule_index] / total
        result.append(tuple(transition))
    matrix = tuple(result)
    _validate_transition(matrix)
    return matrix


@dataclass(frozen=True)
class BMRound:
    distribution: tuple[Q, ...]
    transition: tuple[tuple[Q, ...], ...]
    maps: tuple[tuple[int, ...], ...]
    row_modified_loss: tuple[Q, ...]


class BlumMansourLearner:
    """Theorem 18 with M=1: N source rows and K modification weights per row."""

    def __init__(self, horizon: int, action_count: int, rule_count: int,
                 *, loss_max: Q, precision: int = 80) -> None:
        if min(horizon, action_count, rule_count) <= 0 or loss_max <= 0:
            raise ValueError("positive horizon, dimensions, and loss_max are required")
        self.horizon = horizon
        self.action_count = action_count
        self.rule_count = rule_count
        self.loss_max = Q(loss_max)
        self.context = Context(prec=precision)
        with localcontext(self.context):
            complexity = Decimal(action_count) * Decimal(rule_count).ln()
            self.eta = (complexity / Decimal(horizon)).sqrt()
            self.beta = (-self.eta).exp()
        self.weights = [[Decimal(1) for _ in range(rule_count)]
                        for _ in range(action_count)]

    @property
    def weight_count(self) -> int:
        return sum(len(row) for row in self.weights)

    def prepare(self, maps: Sequence[Sequence[int]]) -> BMRound:
        frozen_maps = tuple(tuple(rule) for rule in maps)
        transition = transition_from_weights(self.weights, frozen_maps)
        distribution = stationary_distribution(transition)
        # Filled after feedback; retained in the round object to pin dimensions.
        return BMRound(distribution, transition, frozen_maps,
                       tuple(Q(0) for _ in range(self.action_count)))

    def update(self, prepared: BMRound, charge_loss: Sequence[Q]) -> BMRound:
        if len(charge_loss) != self.action_count:
            raise ValueError("full-information loss vector has the wrong dimension")
        normalized = tuple(Q(value) / self.loss_max for value in charge_loss)
        if any(value < 0 or value > 1 for value in normalized):
            raise ValueError("normalized losses must lie in [0,1]")
        row_loss = tuple(sum((prepared.transition[source][target]
                              * normalized[target]
                              for target in range(self.action_count)), Q(0))
                         for source in range(self.action_count))
        with localcontext(self.context):
            log_beta = self.beta.ln()
            for source in range(self.action_count):
                probability = decimal_of(prepared.distribution[source], self.context)
                baseline = decimal_of(row_loss[source], self.context)
                for rule_index, rule in enumerate(prepared.maps):
                    modified = decimal_of(normalized[rule[source]], self.context)
                    exponent = probability * (modified - self.beta * baseline)
                    factor = (log_beta * exponent).exp()
                    self.weights[source][rule_index] = +(self.weights[source][rule_index]
                                                         * factor)
                    if not self.weights[source][rule_index].is_finite() \
                            or self.weights[source][rule_index] <= 0:
                        raise ArithmeticError("numerical weight left the positive finite cone")
        return BMRound(prepared.distribution, prepared.transition,
                       prepared.maps, row_loss)

    def source_regret_bound(self) -> Decimal:
        """Worst-case charge-regret bound from the source proof at this beta."""
        with localcontext(self.context):
            beta = self.beta
            log_inverse = -beta.ln()
            complexity = Decimal(self.action_count) * Decimal(self.rule_count).ln()
            normalized = ((Decimal(1) / beta - Decimal(1)) * Decimal(self.horizon)
                          + complexity / (beta * log_inverse))
            return +(decimal_of(self.loss_max, self.context) * normalized)


class HedgeLearner:
    """Cheap full-information external-regret baseline over the eight actions."""

    def __init__(self, horizon: int, action_count: int, *, loss_max: Q,
                 precision: int = 80) -> None:
        self.action_count = action_count
        self.loss_max = Q(loss_max)
        self.context = Context(prec=precision)
        with localcontext(self.context):
            self.eta = (Decimal(2) * Decimal(action_count).ln()
                        / Decimal(horizon)).sqrt()
        self.weights = [Decimal(1)] * action_count

    def distribution(self) -> tuple[Q, ...]:
        exact = tuple(Q(weight) for weight in self.weights)
        total = sum(exact, Q(0))
        result = tuple(value / total for value in exact)
        _validate_distribution(result)
        return result

    def update(self, charge_loss: Sequence[Q]) -> None:
        if len(charge_loss) != self.action_count:
            raise ValueError("full-information loss vector has the wrong dimension")
        with localcontext(self.context):
            for action, charge in enumerate(charge_loss):
                normalized = decimal_of(Q(charge) / self.loss_max, self.context)
                self.weights[action] = +(self.weights[action]
                                         * (-self.eta * normalized).exp())


def uniform_distribution(action_count: int) -> tuple[Q, ...]:
    if action_count <= 0:
        raise ValueError("action_count must be positive")
    return tuple(Q(1, action_count) for _ in range(action_count))
