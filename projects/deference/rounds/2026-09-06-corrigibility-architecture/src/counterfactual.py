"""One counterfactual frame, three predicates.

A `Frame` holds, for a declared intervention class `J` (with a distinguished null
intervention), one branch per intervention.  Each branch records:
  cov   — the coverage state of the authority concern `c_auth` on that branch (the
          Lean `CovState` bits, one route);
  aff   — the principal's actual correction affordance on that branch (True/False);
  amended — whether a valid amendment/disposition on that branch lowered the floor;
  jp    — the principal-side judgment endpoint `J_P(X_j)` on that branch, a rational.

Three predicates over the same frame:
  robust_open        pointwise: Covered ∧ OpenTo on the actual branch and on each j
  robust_authority   pointwise: aff ⪰ floor on each j unless amended there
  exposure_robust    relational: J_P equal on every pair of branches, null included

Nothing here produces the branches; that is the external coupling (the August
counterfactual round's `Coupled` / variation class, the dose-response arms).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q

from src.layers import Cov


@dataclass(frozen=True)
class Branch:
    cov: Cov
    aff: bool
    amended: bool
    jp: Q


@dataclass(frozen=True)
class Frame:
    actual: Branch
    cf: dict            # j -> Branch; the key "null" is the zero-exposure branch


def robust_open(f: Frame) -> bool:
    return f.actual.cov.actual_open and all(b.cov.actual_open for b in f.cf.values())


def robust_authority(f: Frame) -> bool:
    return all(b.aff or b.amended for b in [f.actual, *f.cf.values()])


def exposure_robust(f: Frame, include_null=True) -> bool:
    arms = [b for j, b in f.cf.items() if include_null or j != "null"]
    return all(a.jp == b.jp for a in arms for b in arms)


def answerable_to_authority_failure(f: Frame) -> bool:
    """The corollary: on every branch where `c_auth` is live, an adequate route exists
    and the principal stands.  This is what `robust_open` says about `c_auth`."""
    for b in [f.actual, *f.cf.values()]:
        if b.cov.live and not (b.cov.adequate and b.cov.stands):
            return False
    return True
