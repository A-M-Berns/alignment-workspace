"""The consumable entry point for traderized force.

One function in, one certificate out. A component that has an admissibility
constraint in price space calls `compile_force`; everything else in this round is
the justification for what it returns.

Specified in `projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md`. Names
are provisional.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from contract import ForceDeclaration, declared_liability_bound
from enforcement import Region, Row
from market import ONE, ZERO


class ForceCertificate:
    """What a caller receives: a position, a promise, and an **obligation**.

    Not a safety certificate. The obligation is discharged by paying an outflow
    account, which `compile_funded_force` does and this does not.

    The promise is `conformance`: every row violation at a contract-satisfying
    price is at most the declared tolerance. The obligation is
    `liability_ceiling`: the caller's own layer must show the cumulative value of
    the positions over its assessment worlds is bounded, and this is the per-date
    ceiling it may use.
    """

    def __init__(self, declaration: ForceDeclaration) -> None:
        self.declaration = declaration
        self.intensity = declaration.intensity
        self.tolerance = declaration.tolerance

    def position(self, prices: Sequence[Fraction]):
        """The realised day-`t` position at the displayed prices."""
        return self.declaration.trader().coefficients(prices)

    def conformance_holds(self, prices: Sequence[Fraction]) -> bool:
        return self.declaration.conformance_holds(prices)

    def budget_consumed(self, prices: Sequence[Fraction]) -> Fraction:
        return self.declaration.budget_consumed(prices)

    def liability_ceiling(self, deficits: Sequence[Fraction]) -> Fraction:
        """The per-date ceiling in declared quantities, given the exclusion
        deficits of an assessment world."""
        return declared_liability_bound(self.declaration.slack,
                                        self.declaration.volume,
                                        self.declaration.tolerance, deficits)


def compile_force(rows: Sequence[tuple[Sequence[Fraction], Fraction]],
                  dimension: int, slack: Fraction, volume: Fraction,
                  tolerance: Fraction,
                  feasibility: Sequence[Fraction]) -> ForceCertificate:
    """Compile a price-space row system into a certified enforcement position.

    `rows` are `(coefficients, right-hand side)` pairs meaning `⟪c, P⟫ ≥ r`. The
    caller supplies the market maker's slack, a bound on the ordinary aggregate's
    realised position, and the tolerance it wants promised.

    **Nonemptiness is the caller's precondition, discharged by a witness.**
    `feasibility` is a point of the region — the cheapest certificate that says
    what it means — and it is checked exactly. Nothing here searches for one: a
    search over a rational grid is unsound as a screen, because a region can be
    nonempty and miss every grid point. `K = {p = 1/3}` is the standing example.

    Producing the witness is the feasibility adapter's job, upstream. The
    settlement interface already decides nonemptiness of an admissible-reference
    polytope by one linear program (`NL-SI-A3`), which is exactly this
    obligation.
    """
    region = Region(dimension, [Row(c, r) for c, r in rows])
    witness = tuple(Fraction(x) for x in feasibility)
    if len(witness) != dimension:
        raise ValueError("the feasibility witness has the wrong dimension")
    if not region.contains(witness):
        raise ValueError("the feasibility witness is not in the region")
    return ForceCertificate(ForceDeclaration(region, volume, slack, tolerance))


class SafetyCertifiedForce(ForceCertificate):
    """Force whose charge came from a **verified certificate bound to this request**.

    The proposition a holder may quote is exact:

        for every omega live at date t under this assessment state,
            -E_t(omega)  <=  q_t  =  (eps_t + C_t) * D_t / delta_t ,

    where `E_t` is *this* position, compiled from *this* row presentation over
    *this* support, and `D_t` was computed by enumerating *those* live worlds.
    A holder may quote the account's lifetime ceiling as the safety bound `B`,
    because the charge is debited from that account before the position exists.

    Nothing weaker produces one of these. A caller with only an asserted bound
    gets a `LiveDeficitClaim` and no certified force; that is the whole reason
    the types are separate.
    """

    def __init__(self, declaration, certificate, charged, account, relaxed,
                 policy) -> None:
        super().__init__(declaration)
        self.deficit_certificate = certificate
        self.charged = charged
        self.date = certificate.date
        self.support = certificate.support
        self.presentation = certificate.presentation
        self.assessment = certificate.live_worlds
        self.deficit_bound = certificate.aggregate
        self.deficit_basis = certificate.basis
        self.slack = declaration.slack
        self.volume = declaration.volume
        self.remaining = account.remaining
        self.safety_bound = account.lifetime_ceiling
        self.relaxed = relaxed
        self.policy = policy

    @property
    def deficit_is_verified(self) -> bool:
        return True

    def ingredients(self) -> dict:
        """Everything the certified proposition depends on, for a reader."""
        return {"date": self.date, "support": self.support,
                "presentation": self.presentation,
                "assessment": self.assessment,
                "deficit_bound": self.deficit_bound,
                "deficit_basis": self.deficit_basis,
                "slack": self.slack, "volume": self.volume,
                "tolerance": self.tolerance, "charge": self.charged,
                "safety_bound": self.safety_bound,
                "remaining": self.remaining, "policy": self.policy}


def compile_safe_force(rows, dimension: int, support, date: int,
                       live_worlds, slack: Fraction, volume: Fraction,
                       tolerance: Fraction, feasibility: Sequence[Fraction],
                       account, policy: str = "refuse",
                       label: str = "", ceiling: Fraction = None):
    """The safety-bearing entry point. Certifies, charges, then emits.

    The deficit is computed **from the same `Region` instance that is about to
    be enforced**, over the live worlds the caller supplies, so the certificate
    cannot describe a different force request than the one emitted. That is the
    hole this function closes: previously a caller could hand in a certificate
    for `p >= 0` — aggregate zero, honestly verified — and have enforcement of
    `p >= 1/2` funded for nothing while the emitted position really lost at a
    live world.

    Order matters and is not an implementation detail: feasibility, then
    certification, then charge, then debit, then position. An unaffordable
    request never reaches the last step, and a provenance mismatch cannot arise
    because there is no separate certificate to mismatch.

    `policy` is `refuse`, `quarantine`, or `relax`, and relaxation only ever
    loosens the requested tolerance.
    """
    from outflow import (Insufficient, LiveDeficitCertificate, charge,
                         relax as _relax)

    ceiling = ONE if ceiling is None else Fraction(ceiling)
    region = Region(dimension, [Row(c, r) for c, r in rows])
    witness = tuple(Fraction(x) for x in feasibility)
    if len(witness) != dimension:
        raise ValueError("the feasibility witness has the wrong dimension")
    if not region.contains(witness):
        raise ValueError("the feasibility witness is not in the region")

    certificate = LiveDeficitCertificate.by_enumeration(
        date, region, support, live_worlds)

    if policy == "relax":
        granted = _relax(account, slack, volume, certificate, tolerance, label,
                         ceiling)
        if granted is None:
            return None
        return SafetyCertifiedForce(
            ForceDeclaration(region, volume, slack, granted), certificate,
            charge(slack, volume, granted, certificate), account,
            granted != Fraction(tolerance), policy)

    try:
        paid = account.spend(slack, volume, tolerance, certificate, label)
    except Insufficient:
        if policy == "quarantine":
            return None
        raise
    return SafetyCertifiedForce(
        ForceDeclaration(region, volume, slack, tolerance), certificate, paid,
        account, False, policy)


class FundedForceCertificate(ForceCertificate):
    """**Paid**, and not necessarily safety-certified.

    Retained as the lower-level path for a caller that already holds a verified
    certificate and wants to pass it rather than have one computed. The
    certificate must bind to this exact request — date, support and row
    presentation — and an unverified claim is refused outright, because a
    holder of this type is entitled to quote the account bound and an asserted
    number does not earn that.

    New callers should use `compile_safe_force`, which removes the possibility
    of a mismatch by computing the certificate from the region it enforces. This
    path exists for a caller that already holds a certificate; it takes the same
    four identities so it can check all four, and returns the same type only
    because it enforces the same invariant.

    A force certificate whose safety charge has already been paid.

    The distinction from `ForceCertificate` is the whole point of this type.
    `ForceCertificate` promises conformance and *emits an obligation*: the
    caller's layer must still bound the cumulative liability. This one carries
    a live-world deficit certificate that has been checked, a charge computed
    from it, and the account entry recording that the charge was paid before the
    position was emitted.

    A caller holding one of these may quote the account's lifetime ceiling as its
    `B`. A caller holding the base class may not.
    """

    def __init__(self, declaration, certificate, charged, remaining,
                 relaxed: bool) -> None:
        super().__init__(declaration)
        self.deficit_certificate = certificate
        self.charged = charged
        self.remaining = remaining
        self.relaxed = relaxed

    @property
    def deficit_is_verified(self) -> bool:
        """Whether the live-world aggregate was computed or merely asserted."""
        return self.deficit_certificate.verified


def compile_funded_force(rows, dimension: int, support, date: int,
                         live_worlds,
                         slack: Fraction, volume: Fraction,
                         tolerance: Fraction,
                         feasibility: Sequence[Fraction],
                         account, deficit_certificate,
                         policy: str = "refuse",
                         label: str = "",
                         ceiling: Fraction = None):
    """Compile force **and pay for it**, or decline to emit it.

    The safety-bearing entry point. `compile_force` promises conformance and
    nothing else; a caller that read a conformance certificate as a safety
    certificate has misread it, and until this function existed nothing in the
    API made that mistake hard to commit. Here the account is consumed before the
    position is constructed, so an unaffordable request cannot produce a
    certificate at all.

    `policy` selects the exhaustion behaviour, and the choice is the caller's
    because it is constitutional rather than mathematical:

    * `refuse` — raise. The request was for force at a stated tolerance and the
      account cannot fund it.
    * `quarantine` — return `None`. The endorsement keeps its normative standing
      and receives no operative force at this date.
    * `relax` — emit force at the tightest affordable tolerance, up to `ceiling`,
      and return `None` if even that is unaffordable.

    Returns a `FundedForceCertificate`, or `None` under the withholding
    policies.
    """
    from outflow import Insufficient, charge, relax as _relax

    ceiling = ONE if ceiling is None else Fraction(ceiling)
    region = Region(dimension, [Row(c, r) for c, r in rows])
    witness = tuple(Fraction(x) for x in feasibility)
    if len(witness) != dimension:
        raise ValueError("the feasibility witness has the wrong dimension")
    if not region.contains(witness):
        raise ValueError("the feasibility witness is not in the region")

    if not getattr(deficit_certificate, "verified", False):
        raise TypeError(
            "funded force needs a verified certificate; a LiveDeficitClaim "
            "prices a request and cannot certify one")
    mismatch = deficit_certificate.binds(date, region, support, live_worlds)
    if mismatch is not None:
        raise ValueError(f"certificate does not bind to this request: {mismatch}")

    if policy == "relax":
        granted = _relax(account, slack, volume, deficit_certificate, tolerance,
                         label, ceiling)
        if granted is None:
            return None
        return FundedForceCertificate(
            ForceDeclaration(region, volume, slack, granted),
            deficit_certificate,
            charge(slack, volume, granted, deficit_certificate),
            account.remaining, granted != tolerance)

    try:
        paid = account.spend(slack, volume, tolerance, deficit_certificate,
                             label)
    except Insufficient:
        if policy == "quarantine":
            return None
        raise
    return FundedForceCertificate(
        ForceDeclaration(region, volume, slack, tolerance),
        deficit_certificate, paid, account.remaining, False)
