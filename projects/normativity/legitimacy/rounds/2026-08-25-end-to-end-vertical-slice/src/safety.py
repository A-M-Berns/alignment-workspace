"""The charged branch, on the canonical safety layer's own objects.

The slice does not compute its own liability quantity. It converts the compiled
rows into the traderized-enforcement round's `Region`, hands that to
`LiveDeficitCertificate.by_enumeration`, and pays the resulting `charge` into an
`OutflowAccount` through `compile_safe_force`. Everything numeric a reader can
walk back to a theorem comes from those functions and not from here.

**The quantity, said once.** The sharp live-world deficit is

    D_t = max over omega live at t of  sum_j d_{t,j}(omega)

— the worst single world's *total* row deficit — where `d_{t,j}` are the
deficits of exactly the rows about to be enforced, over exactly the worlds
supplied, in exactly the day's coordinates. The charge is

    q_t = (eps_t + M_t) * D_t / delta_t

which is `contract.declared_liability_bound` at that aggregate, and it is
debited from the account before the position exists.

A second aggregate exists and is not the charge: `rowwise` sums each row's own
worst world, which is larger whenever different rows are worst at different
worlds. It is kept because a per-row account must use it. The slice reports both
and bills the sharp one, which is what `charge(..., sharp=True)` does.

**Which region is charged.** The rows handed over are the operative ones —
`K^N`'s. The deductive region is world-inclusive by construction, so its rows
have deficit zero at every live world and add nothing to `D_t`; that is the
zero-liability calibration case the deduction special case already isolates.
What the normative layer pays for is exactly its own increment.
"""
from __future__ import annotations

import pathlib
import sys
from dataclasses import dataclass
from fractions import Fraction
from typing import Optional, Sequence

_HERE = pathlib.Path(__file__).resolve().parent
_FORCE = (_HERE.parents[3] / "rounds" / "2026-08-16-traderized-enforcement"
          / "src")
if str(_FORCE) not in sys.path:
    sys.path.insert(0, str(_FORCE))

from contract import declared_liability_bound          # noqa: E402
from enforcement import Region, Row                    # noqa: E402
from force_api import compile_safe_force               # noqa: E402
from outflow import (Insufficient, LiveDeficitCertificate,  # noqa: E402
                     OutflowAccount, charge)

ZERO = Fraction(0)


def region_of(compiled) -> Region:
    """The compiled rows as the enforcement layer's own `Region`.

    `CompiledRow` already carries `c . p >= r` in that convention, so this is a
    change of type and not of content. `test_safety.py` checks that the two
    agree on violations at sampled prices.
    """
    return Region(len(compiled.coords),
                  [Row(row.coefficients, row.rhs) for row in compiled.rows])


def support_of(compiled) -> tuple:
    """One sentence name per coordinate, which is what a certificate binds to."""
    return tuple(repr(phi) for phi in compiled.coords)


@dataclass(frozen=True)
class Charged:
    """One date's charged force, and everything the number depends on."""

    date: int
    sharp: Fraction                   # D_t, the billed aggregate
    rowwise: Fraction                 # the conservative aggregate, not billed
    charge: Fraction                  # q_t
    slack: Fraction                   # eps_t
    volume: Fraction                  # M_t
    tolerance: Fraction               # delta_t
    live_worlds: int
    certificate: object = None
    force: object = None              # SafetyCertifiedForce, or None
    account_remaining: Optional[Fraction] = None
    safety_bound: Optional[Fraction] = None
    withheld: Optional[str] = None    # why no force was emitted

    @property
    def emitted(self) -> bool:
        return self.force is not None

    @property
    def zero_liability(self) -> bool:
        """Whether the request is the world-inclusive, free case."""
        return self.sharp == ZERO


def certify(compiled, live_worlds: Sequence, date: int) -> LiveDeficitCertificate:
    """`D_t` for this exact request, by the canonical enumeration."""
    return LiveDeficitCertificate.by_enumeration(
        date, region_of(compiled), support_of(compiled), live_worlds)


def price_request(compiled, live_worlds: Sequence, date: int,
                  slack: Fraction, volume: Fraction,
                  tolerance: Fraction) -> tuple:
    """What the request would cost, without paying for it.

    Returns `(certificate, q_t)`. Nothing is debited and no position exists, so
    a caller holding these is entitled to nothing.
    """
    cert = certify(compiled, live_worlds, date)
    return cert, charge(slack, volume, tolerance, cert)


def charge_force(compiled, live_worlds: Sequence, date: int,
                 witness: Sequence[Fraction], account: OutflowAccount,
                 slack: Fraction = Fraction(1, 100),
                 volume: Fraction = Fraction(1),
                 tolerance: Fraction = Fraction(1, 10),
                 policy: str = "quarantine",
                 label: str = "") -> Charged:
    """Certify, charge, debit, then emit — in that order, through the canonical API.

    `compile_safe_force` computes the certificate from the very region it is
    about to enforce, so a certificate for one request cannot fund another. The
    order is not an implementation detail: an unaffordable request never reaches
    the step that constructs a position.

    Under `quarantine`, an exhausted account returns force `None`. The
    injunction keeps its normative standing and receives no operative force at
    this date; the slice reports that rather than pricing as if it had.
    """
    rows = [(row.coefficients, row.rhs) for row in compiled.rows]
    dimension = len(compiled.coords)
    support = support_of(compiled)
    cert = certify(compiled, live_worlds, date)
    q = charge(slack, volume, tolerance, cert)

    force = compile_safe_force(
        rows, dimension, support, date, live_worlds, slack, volume, tolerance,
        witness, account, policy=policy, label=label or f"day-{date}")

    if force is None:
        return Charged(date, cert.aggregate, cert.rowwise, q, Fraction(slack),
                       Fraction(volume), Fraction(tolerance), len(live_worlds),
                       certificate=cert, force=None,
                       account_remaining=account.remaining,
                       safety_bound=account.lifetime_ceiling,
                       withheld="the account cannot fund this date's charge")
    return Charged(date, cert.aggregate, cert.rowwise, q, Fraction(slack),
                   Fraction(volume), Fraction(tolerance), len(live_worlds),
                   certificate=cert, force=force,
                   account_remaining=account.remaining,
                   safety_bound=account.lifetime_ceiling)


def cumulative(charges: Sequence[Charged]) -> Fraction:
    """`sum_t q_t` over a trajectory — the quantity the safety condition bounds."""
    return sum((c.charge for c in charges), ZERO)
