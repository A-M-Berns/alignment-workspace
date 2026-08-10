"""Certificate-invalidating book changes, and the tightened movement cap.

`NL-J2` bounds total adverse movement by `U_m` over `m` active-book changes.
The proof only ever needs the changes that can move the incumbent reference.  A
change leaving the incumbent reference's **core certificate** valid contributes
zero reference jump, so the cap may be restated over `m*` core-invalidating
changes with `m* <= Psi_0`.

**Bare-point admission is NOT the certificate.**  The condition the frozen cap
assumes is the fixed-core condition `q + theta(P - q) subset S`
(`src/joint.py::jump_step_cap`).  A constraint-adding change can admit the bare
incumbent while cutting its core: with `theta = 1/10`, `q = 3/5`, base region
`x >= 1/2`, adding `x >= 3/5` admits `q` exactly while killing the core lower end
`q(1-theta) = 27/50`, and a compiler honoring the fixed-core hypothesis is forced
to `q' >= q/(1-theta) = 2/3`, charging `2/15` at holdings `(2,)`.  An earlier
version of this module tested bare-point admission and was unsound; the witness
is now `NL-N-J2a`.

Per decision P-4 this lands beside the frozen joint module rather than editing
it: `src/joint.py` is byte-frozen and `movement_recursion` is imported, never
redefined.  `NL-J2'` is a new claim citing `NL-J2`; it supersedes nothing.

Finiteness discipline.  A history is a finite sequence of book changes; a region
is a finite set of half-space endorsements; membership and the tightening count
are finite exact-rational computations.  No live state grows with date.

All arithmetic is exact rationals.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Iterable, Mapping, Sequence

from src.joint import movement_recursion, positive_part


@dataclass(frozen=True)
class HalfSpace:
    """One compiled endorsement: `coefficients . x >= rhs`."""

    endorsement_id: str
    coefficients: tuple[Q, ...]
    rhs: Q

    def admits(self, point: Sequence[Q]) -> bool:
        return sum((Q(a) * Q(b) for a, b in zip(self.coefficients, point)),
                   Q(0)) >= Q(self.rhs)


@dataclass(frozen=True)
class Region:
    """The compiled region as a finite set of half-spaces."""

    endorsements: tuple[HalfSpace, ...]

    def admits(self, point: Sequence[Q]) -> bool:
        return all(h.admits(point) for h in self.endorsements)

    def without(self, endorsement_id: str) -> "Region":
        return Region(tuple(h for h in self.endorsements
                            if h.endorsement_id != endorsement_id))

    def with_added(self, half_space: HalfSpace) -> "Region":
        return Region(self.endorsements + (half_space,))


@dataclass(frozen=True)
class BookChange:
    """One active-book change, with the region before and after."""

    change_id: str
    kind: str
    before: Region
    after: Region

    def expands(self) -> bool:
        """A deactivation or suspension removes constraints, so it only expands."""
        return set(h.endorsement_id for h in self.after.endorsements) <= set(
            h.endorsement_id for h in self.before.endorsements)


UNIT_INTERVAL_VERTICES: tuple[tuple[Q, ...], ...] = ((Q(0),), (Q(1),))


def core_vertices(incumbent_reference: Sequence[Q], theta: Q,
                  vertices: Sequence[Sequence[Q]]) -> tuple[tuple[Q, ...], ...]:
    """The vertices of the shrunk simplex `q + theta(P - q)`."""
    if not Q(0) < Q(theta) <= Q(1):
        raise ValueError("theta must be in (0,1]")
    return tuple(
        tuple(Q(q) + Q(theta) * (Q(v) - Q(q))
              for q, v in zip(incumbent_reference, vertex))
        for vertex in vertices)


def retains_core_certificate(change: BookChange, incumbent_reference: Sequence[Q],
                             theta: Q,
                             vertices: Sequence[Sequence[Q]] = UNIT_INTERVAL_VERTICES,
                             ) -> bool:
    """Does the incumbent's fixed-core certificate survive the change?

    The core `q + theta(P - q)` is the convex hull of the shrunk vertices, and a
    region is an intersection of half-spaces hence convex, so checking the
    vertices decides inclusion.  In the one-dimensional fixtures these are the
    two endpoints `q(1-theta)` and `q(1-theta) + theta`.

    Retention is a **theta-relative** property, not a shape property of the
    change: the same constraint can retain at one core coefficient and invalidate
    at another.
    """
    return all(change.after.admits(point)
               for point in core_vertices(incumbent_reference, theta, vertices))


def reference_jump(holdings: Sequence[Q], before: Sequence[Q],
                   after: Sequence[Q]) -> Q:
    """The adverse movement charged by one reference move."""
    return positive_part(-sum((Q(h) * (Q(a) - Q(b))
                               for h, a, b in zip(holdings, before, after)), Q(0)))


def zero_jump(change: BookChange, incumbent_reference: Sequence[Q],
              holdings: Sequence[Q], theta: Q,
              vertices: Sequence[Sequence[Q]] = UNIT_INTERVAL_VERTICES) -> Q:
    """The jump a core-retaining change contributes.

    `NL-J2'` (a).  If the incumbent's whole core survives the change, a
    certificate-retaining compiler keeps the reference, so it does not move and
    the charge is exactly zero.
    """
    if not retains_core_certificate(change, incumbent_reference, theta, vertices):
        raise ValueError("the change invalidates the incumbent's core certificate")
    return reference_jump(holdings, incumbent_reference, incumbent_reference)


@dataclass(frozen=True)
class RecordedChange:
    """One change together with the incumbent reference in force before it.

    The trajectory is **read from public history**, never synthesized: this
    module invents no compiler policy and produces no successor reference.  The
    dependence on public history is the extensionality cost `C-PROV-IRR` already
    concedes; `NL-J2'` inherits it and makes it explicit in this input type.
    """

    change: BookChange
    incumbent_before: tuple[Q, ...]


def tightening_count(trajectory: Sequence[RecordedChange], theta: Q,
                     vertices: Sequence[Sequence[Q]] = UNIT_INTERVAL_VERTICES) -> int:
    """`m*`: the changes whose *pre-change* incumbent loses its core.

    Each change is judged against the incumbent in force at that change, not
    against the initial reference.  Judging a whole history against one fixed
    reference is wrong in both directions once the reference has moved.
    """
    return sum(1 for step in trajectory
               if not retains_core_certificate(step.change, step.incumbent_before,
                                               theta, vertices))


def tightened_cap(theta: Q, error_budget: Q, risk: Q, ordinary_budget: Q,
                  trajectory: Sequence[RecordedChange],
                  vertices: Sequence[Sequence[Q]] = UNIT_INTERVAL_VERTICES,
                  ) -> tuple[Q, Q, int, int]:
    """`(U_{m*}, U_{Psi_0}, m*, Psi_0)` — the tightened cap beside the coarse one."""
    naive = len(trajectory)
    tightened = tightening_count(trajectory, theta, vertices)
    caps = movement_recursion(theta, error_budget, risk, ordinary_budget, naive)
    return caps[tightened], caps[naive], tightened, naive


# --------------------------------------------------------------------------
# (b) The attained optimum in the scalar two-world setting
# --------------------------------------------------------------------------


def attained_stage_factor(theta: Q) -> Q:
    """The per-stage growth the worst case actually attains: `(1-theta)/theta`."""
    if not Q(0) < Q(theta) <= Q(1):
        raise ValueError("theta must be in (0,1]")
    return (Q(1) - Q(theta)) / Q(theta)


def recursion_stage_factor(theta: Q) -> Q:
    """The per-stage growth the recursion charges: `(1-theta)/theta + 1`."""
    return attained_stage_factor(theta) + Q(1)


def attained_sequence(theta: Q, base: Q, stages: int) -> tuple[Q, ...]:
    """The attained worst case iterated: multiplier `(1-theta)/theta` per stage."""
    factor = attained_stage_factor(theta)
    value = Q(base)
    values = [value]
    for _ in range(stages):
        value = factor * value
        values.append(value)
    return tuple(values)


def looseness(theta: Q, base: Q, stages: int) -> tuple[Q, ...]:
    """Ratio of the recursion's bound to the attained worst case, per stage."""
    bound = movement_recursion(theta, Q(0), Q(0), base, stages)
    attained = attained_sequence(theta, base, stages)
    return tuple(b / a if a != 0 else Q(0) for b, a in zip(bound, attained))
