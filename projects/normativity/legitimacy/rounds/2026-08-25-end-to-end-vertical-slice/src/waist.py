"""The two candidate waists, and the compiler between them and price geometry.

**Value waist.** `compile_value : ValueSpecCode x QueryCode -> CertifiedLUV`,
partial, with the partiality represented rather than raised. A `CertifiedLUV` is
a `li.LUV` — the pinned dependency's own object — together with the two
certificates its expectation theorems actually consume: a threshold-code
efficiency witness, and a world-value presentation. No new security is
introduced.

**Operative waist.** `Injunction`, a finite conjunction of rational affine
inequalities over `CognitiveQuantity`, which is `Prob(phi) | Expect(X)`. The
payload is operative terms only; why it was issued is recovered through the
issuing normative event, not from the payload.

**The compiler.** `kappa(J, n)` rewrites each `Expect(X)` as the day-`n`
threshold bundle `sum_{i<n+1} (1/(n+1)) <X > i/(n+1)>` — the pinned
`LUV.expectAffine (n+1)`, whose day-`n` price is `LUV.expect P n` by
`expectAffine_price` — and each `Prob(phi)` as the price of `phi`. What comes
out is a finite rational row system over ordinary sentence prices.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Mapping, Optional, Sequence

from li import ONE, ZERO, AffineForm, LUV, Sentence, valued_at


# ------------------------------------------------------------ value waist


@dataclass(frozen=True)
class CertifiedLUV:
    """A LUV the market may be asked about, with what certifies it.

    `luv` is `li.LUV` unchanged — the value layer exposes the dependency's own
    object and adds no wrapper the operative layer would have to know about.

    `code_witness` names the threshold-code efficiency certificate
    (`LUV.RpnThresholdCodes` / `PolyThresholdCodes`): the family `i,k |-> <X >
    i/k>` is emitted by one program. Without it the compiled bundle is a
    functional written outside the framework rather than a legal trading
    strategy.

    `values` is the world-value presentation (`ExactTheoryPresentation.value`):
    the rational the LUV takes in each named world. It is what
    `threshold_axioms` and the admissibility test read, and it is what makes the
    exposure *certified* rather than merely syntactic.

    `origin` records which value specification and query produced it. It is
    provenance and has no semantic role; the operative layer never reads it,
    which is the interchangeability the waist is supposed to buy.
    """

    luv: LUV
    code_witness: str
    values: tuple                      # tuple[(world_label, Fraction), ...]
    origin: tuple = ()                 # (spec_id, query) when value-generated

    def value_in(self, world_label: str) -> Fraction:
        for label, x in self.values:
            if label == world_label:
                return Fraction(x)
        raise KeyError(f"{self.luv.name} has no certified value at {world_label}")

    def presentation_sentences(self, world_label: str, k: int) -> tuple:
        """`threshold_iff` at one world, on the precision-`k` grid."""
        return valued_at(self.luv, self.value_in(world_label), k)

    def bounded(self) -> bool:
        return all(ZERO <= Fraction(x) <= ONE for _, x in self.values)


@dataclass(frozen=True)
class NonExposure:
    """A value query that compiles to no legitimate LUV.

    A representable state, not an error. Rich value may outrun quantification,
    and the architecture is supposed to say so rather than fail or invent a
    surrogate.
    """

    spec_id: str
    query: str
    reason: str

    @property
    def exposes(self) -> bool:
        return False


@dataclass(frozen=True)
class ValueSpec:
    """A frozen historical value specification.

    `payload` is opaque and is never read by anything downstream. It is not
    required to be a utility function, to be scalar, or to be complete;
    `exposures` says which queries it can currently answer with a bounded LUV,
    and a specification may answer none.

    `supersedes` is a diachronic link and carries no justificatory force. It is
    here so a trace can display lineage; no compilation consults it.
    """

    spec_id: str
    payload: object
    exposures: tuple                   # tuple[(query, exposure_builder), ...]
    supersedes: tuple = ()

    def queries(self) -> tuple:
        return tuple(q for q, _ in self.exposures)


class ValueRegistry:
    """Append-only store of value specifications, and the compiler over it.

    Write-once by `spec_id`. A specification that has entered is never rewritten,
    which is what makes `X_{v0,q}` mean at day 9 what it meant at day 1.
    """

    def __init__(self) -> None:
        self._specs: dict = {}
        self._order: list = []

    def admit(self, spec: ValueSpec) -> ValueSpec:
        if spec.spec_id in self._specs:
            raise ValueError(
                f"value specification {spec.spec_id} is already frozen")
        self._specs[spec.spec_id] = spec
        self._order.append(spec.spec_id)
        return spec

    def spec(self, spec_id: str) -> ValueSpec:
        return self._specs[spec_id]

    def known(self) -> tuple:
        return tuple(self._order)

    def compile_value(self, spec_id: str, query: str):
        """`compileValue : ValueSpecCode x QueryCode -> CertifiedLUV`, partial.

        The LUV's name is derived from the *specification id*, which is frozen,
        and never from "the currently active value specification". That is the
        whole mechanism of historical rigidity: there is no expression in the
        system that denotes a value quantity relative to whatever is active now.
        """
        spec = self._specs.get(spec_id)
        if spec is None:
            return NonExposure(spec_id, query, "no such value specification")
        for q, builder in spec.exposures:
            if q != query:
                continue
            exposure = builder(spec, query)
            if isinstance(exposure, NonExposure):
                return exposure
            if not exposure.bounded():
                return NonExposure(spec_id, query,
                                   "exposed quantity is not a [0,1] LUV")
            return exposure
        return NonExposure(spec_id, query, "specification exposes no such query")


def luv_exposure(code_witness: str, values: Mapping) -> Callable:
    """Build an exposure that names its LUV after the frozen specification."""

    def builder(spec: ValueSpec, query: str) -> CertifiedLUV:
        return CertifiedLUV(
            luv=LUV(f"X[{spec.spec_id}:{query}]"),
            code_witness=code_witness,
            values=tuple((w, Fraction(x)) for w, x in sorted(values.items())),
            origin=(spec.spec_id, query))

    return builder


def refusing(reason: str) -> Callable:
    """An exposure that declines: the representable non-exposure state."""

    def builder(spec: ValueSpec, query: str) -> NonExposure:
        return NonExposure(spec.spec_id, query, reason)

    return builder


# -------------------------------------------------------- cognitive waist


@dataclass(frozen=True)
class Prob:
    """`Prob(phi)`; `[[Prob(phi)]]_n = P_n(phi)`."""

    phi: Sentence

    def form(self, n: int) -> AffineForm:
        return AffineForm.of_sentence(self.phi)

    def __repr__(self) -> str:
        return f"Prob({self.phi!r})"


@dataclass(frozen=True)
class Expect:
    """`Expect(X)`; `[[Expect(X)]]_n = E_n(X)`, at the pinned definition.

    A derived cognitive coordinate, not a primitive asset. The day-`n` reading
    is `LUV.expectAffine (n+1)` priced on day `n`, so the coordinate's low-level
    realization changes with `n` while the term itself does not.
    """

    x: CertifiedLUV

    def form(self, n: int) -> AffineForm:
        return self.x.luv.expect_affine(n + 1)

    def __repr__(self) -> str:
        return f"Expect({self.x.luv.name})"


CognitiveQuantity = object             # Prob | Expect


# -------------------------------------------------------- operative waist


class MalformedInjunction(Exception):
    """A payload refused at the waist, before any compilation."""


@dataclass(frozen=True)
class Ineq:
    """`sum_i c_i * q_i + const <= rhs`, with every number an exact rational."""

    atoms: tuple                       # tuple[(Fraction, CognitiveQuantity), ...]
    const: Fraction = ZERO
    rhs: Fraction = ZERO
    label: str = ""

    def form(self, n: int) -> AffineForm:
        out = AffineForm(Fraction(self.const), ())
        for c, q in self.atoms:
            out = out.add(q.form(n).scale(Fraction(c)))
        return out

    def quantities(self) -> tuple:
        return tuple(q for _, q in self.atoms)

    def __repr__(self) -> str:
        lhs = " + ".join(f"{c}*{q!r}" for c, q in self.atoms)
        if self.const:
            lhs = f"{lhs} + {self.const}"
        return f"[{self.label}] {lhs} <= {self.rhs}"


@dataclass(frozen=True)
class Injunction:
    """`J`: a frozen operative payload, and nothing else.

    No authority, no reasons, no derivation, no predecessor, no budget, no
    tolerance, no intensity. Those are recovered from the issuing normative
    event through the injunction's standing, which is where they live.
    """

    injunction_id: str
    ineqs: tuple

    def check_wellformed(self) -> None:
        """Syntactic admissibility. Says nothing about satisfiability."""
        if not self.ineqs:
            raise MalformedInjunction(
                f"{self.injunction_id}: an injunction with no inequality "
                "constrains nothing and is not an operative payload")
        for k, ineq in enumerate(self.ineqs):
            if not ineq.atoms:
                if Fraction(ineq.const) <= Fraction(ineq.rhs):
                    raise MalformedInjunction(
                        f"{self.injunction_id}#{k}: a constant-true inequality "
                        "carries no operative content")
                raise MalformedInjunction(
                    f"{self.injunction_id}#{k}: a constant-false inequality is "
                    "unsatisfiable at every price and every day")
            for c, q in ineq.atoms:
                if not isinstance(c, Fraction):
                    raise MalformedInjunction(
                        f"{self.injunction_id}#{k}: coefficient {c!r} is not an "
                        "exact rational")
                if not isinstance(q, (Prob, Expect)):
                    raise MalformedInjunction(
                        f"{self.injunction_id}#{k}: {q!r} is not a cognitive "
                        "quantity")
                if isinstance(q, Expect) and not q.x.bounded():
                    raise MalformedInjunction(
                        f"{self.injunction_id}#{k}: {q.x.luv.name} is not "
                        "certified as a [0,1] LUV")

    def luvs(self) -> tuple:
        out = []
        for ineq in self.ineqs:
            for q in ineq.quantities():
                if isinstance(q, Expect) and q.x not in out:
                    out.append(q.x)
        return tuple(out)


# ------------------------------------------------------------- the compiler


@dataclass(frozen=True)
class CompiledRow:
    """One rational half-space over prices, in the enforcement layer's sense.

    `c . p >= r`, matching `enforcement.Row`, together with the standing and the
    inequality it came from. The provenance travels with the row so that a
    separator, an infeasibility certificate or a trade can be walked back to the
    injunction term that demanded it.
    """

    coefficients: tuple                # aligned with the day's coordinate list
    rhs: Fraction
    standing_id: str
    injunction_id: str
    index: int
    label: str = ""

    def slack(self, prices: Sequence[Fraction]) -> Fraction:
        return sum((c * Fraction(p) for c, p in zip(self.coefficients, prices)),
                   ZERO) - Fraction(self.rhs)

    def violation(self, prices: Sequence[Fraction]) -> Fraction:
        v = -self.slack(prices)
        return v if v > ZERO else ZERO


@dataclass(frozen=True)
class Compiled:
    """`kappa_n(J)` for a whole operative projection: coordinates plus rows."""

    day: int
    coords: tuple                      # the day's priced fragment, no repeats
    rows: tuple                        # tuple[CompiledRow, ...]

    def index(self, phi) -> int:
        return self.coords.index(phi)

    def satisfied_by(self, prices: Sequence[Fraction]) -> bool:
        return all(row.slack(prices) >= ZERO for row in self.rows)

    def violations(self, prices: Sequence[Fraction]) -> tuple:
        return tuple((row, row.violation(prices)) for row in self.rows
                     if row.violation(prices) > ZERO)


def coordinates_for(items: Sequence, day: int) -> tuple:
    """The day-`n` priced fragment of a set of `(standing_id, Injunction)`.

    Every sentence any compiled term mentions, listed once. Deduplication is not
    cosmetic: the schedule type on the other side carries `nodup`, and two LUVs
    sharing a threshold sentence, or a `Prob(phi)` naming one, would otherwise
    present the same coordinate twice.
    """
    coords: list = []
    for _, J in items:
        for ineq in J.ineqs:
            for phi in ineq.form(day).sentences():
                if phi not in coords:
                    coords.append(phi)
    return tuple(coords)


def kappa(items: Sequence, day: int, coords: Optional[tuple] = None) -> Compiled:
    """Compile an operative projection to rational rows over sentence prices.

    `items` is `[(standing_id, Injunction)]` — the projection, paired with the
    standing that carries each payload. Each `sum c_i q_i + const <= rhs`
    becomes `(-a) . p >= const - rhs` where `a` is the normal form of the
    expanded affine combination, which is the sign convention
    `enforcement.Row` uses.

    Exactness: the compiled row's value at a price vector equals the
    inequality's own left-hand side there, by construction, and
    `test_compilation.py` checks that against independently computed `E_n(X)`.
    """
    coords = coordinates_for(items, day) if coords is None else tuple(coords)
    position = {phi: i for i, phi in enumerate(coords)}
    rows: list = []
    for standing_id, J in items:
        J.check_wellformed()
        for k, ineq in enumerate(J.ineqs):
            form = ineq.form(day)
            coeffs = [ZERO] * len(coords)
            for phi, c in form.coefficients().items():
                if phi not in position:
                    raise KeyError(f"{phi!r} is not in the day's fragment")
                coeffs[position[phi]] = -c
            rows.append(CompiledRow(
                coefficients=tuple(coeffs),
                rhs=Fraction(form.const) - Fraction(ineq.rhs),
                standing_id=standing_id,
                injunction_id=J.injunction_id,
                index=k,
                label=ineq.label))
    return Compiled(day, coords, tuple(rows))
