"""The Logical Induction substrate, at the pinned dependency's own definitions.

Every object here tracks a declaration in Formalized-Agent-Foundations at the
commit `lean/lakefile.toml` pins, `c0d885bfb2f84054ada18c65acec672e04d6d380`.
The correspondence is stated per object and is what the round's compilation
exactness rests on; nothing here is a paraphrase of the paper from memory.

| here | there |
|---|---|
| `Sentence` | `LogicalInduction.Sentence`, a propositional formula |
| `PCWorld` | `Framework/Criterion.lean`, `def PCWorld` — an atom valuation |
| `holds` | `PCWorld.Holds` — Boolean evaluation |
| `payout` | `PCWorld.payout` — `1` if it holds, else `0` |
| `consistent_with` | `PCWorld.ConsistentWith v D := forall phi in D, v.Holds phi` |
| `LUV.gt` | `Framework/Expectations.lean`, `structure LUV` — `gt : Q -> Sentence` |
| `LUV.expect_affine` | `Properties/ExpectationAffine.lean`, `LUV.expectAffine` |
| `LUV.expect` | `Framework/Expectations.lean`, `LUV.expect` |
| `AffineForm` | `Framework/Affine.lean`, `structure AffineCombination` |

Exact rationals throughout.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Callable, Iterable, Mapping, Sequence

ZERO = Fraction(0)
ONE = Fraction(1)


# ------------------------------------------------------------- sentences


@dataclass(frozen=True)
class Atom:
    name: str

    def __repr__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Neg:
    inner: object

    def __repr__(self) -> str:
        return f"~{self.inner!r}"


@dataclass(frozen=True)
class And:
    left: object
    right: object

    def __repr__(self) -> str:
        return f"({self.left!r} & {self.right!r})"


@dataclass(frozen=True)
class Or:
    left: object
    right: object

    def __repr__(self) -> str:
        return f"({self.left!r} | {self.right!r})"


@dataclass(frozen=True)
class Implies:
    left: object
    right: object

    def __repr__(self) -> str:
        return f"({self.left!r} -> {self.right!r})"


Sentence = object            # Atom | Neg | And | Or | Implies


def atoms_of(phi) -> frozenset:
    """The atom names occurring in a sentence."""
    if isinstance(phi, Atom):
        return frozenset([phi.name])
    if isinstance(phi, Neg):
        return atoms_of(phi.inner)
    if isinstance(phi, (And, Or, Implies)):
        return atoms_of(phi.left) | atoms_of(phi.right)
    raise TypeError(f"not a sentence: {phi!r}")


def holds(world: Mapping[str, bool], phi) -> bool:
    """`PCWorld.Holds`: Boolean evaluation of `phi` at an atom valuation.

    An atom the valuation does not mention reads as false, which is what makes
    a partial dictionary a total valuation in the model's sense.
    """
    if isinstance(phi, Atom):
        return bool(world.get(phi.name, False))
    if isinstance(phi, Neg):
        return not holds(world, phi.inner)
    if isinstance(phi, And):
        return holds(world, phi.left) and holds(world, phi.right)
    if isinstance(phi, Or):
        return holds(world, phi.left) or holds(world, phi.right)
    if isinstance(phi, Implies):
        return (not holds(world, phi.left)) or holds(world, phi.right)
    raise TypeError(f"not a sentence: {phi!r}")


def payout(world: Mapping[str, bool], phi) -> Fraction:
    """`PCWorld.payout`: the value of a `phi`-share in this world."""
    return ONE if holds(world, phi) else ZERO


def consistent_with(world: Mapping[str, bool], stage: Iterable) -> bool:
    """`PCWorld.ConsistentWith`: the world makes every stage sentence true."""
    return all(holds(world, phi) for phi in stage)


# ------------------------------------------------------------------- LUVs


@dataclass(frozen=True)
class LUV:
    """`structure LUV` — a `[0,1]`-LUV presented by its threshold sentences.

    The paper's LUVs are first-order; the pinned formalization models one by its
    observable content for a market, the family `gt r = "X > r"`, and this
    carries that model over unchanged. `name` is the only datum, and the
    threshold sentences are derived from it, so two LUVs are equal exactly when
    their threshold families are — the `LUV.ext` lemma.
    """

    name: str

    def gt(self, r: Fraction) -> Sentence:
        """`X.gt r`, the sentence `X > r`."""
        return Atom(f"{self.name}>{Fraction(r)}")

    def expect_affine(self, k: int) -> "AffineForm":
        """`LUV.expectAffine`: the precision-`k` threshold bundle.

        `sum_{i<k} (1/k) * <X > i/k>`, constant zero. This is the whole of the
        compilation of an expectation into sentence prices; there is no other
        content to it.
        """
        if k <= 0:
            raise ValueError("precision is positive")
        return AffineForm(ZERO, tuple(
            (Fraction(1, k), self.gt(Fraction(i, k))) for i in range(k)))

    def expect(self, prices: Mapping, n: int) -> Fraction:
        """`LUV.expect P n` — the day-`n` expectation, at the day's own grid.

        `expectAffine (n+1)` priced on day `n`; the pinned lemma
        `expectAffine_price` is the statement that these two agree, and this
        function is the only place the round relies on it.
        """
        return self.expect_affine(n + 1).price(prices)

    def value_in(self, world: Mapping[str, bool], k: int) -> Fraction:
        """`LUV.expectApprox` at a world: the precision-`k` value of `X` there.

        A world's payouts are `0/1`, so this is `#{i < k : world holds X > i/k}/k`
        — the world's own reading of `X` to precision `k`.
        """
        return self.expect_affine(k).price(
            {s: payout(world, s) for s in self.expect_affine(k).sentences()})


def threshold_chain(luv: LUV, grid: Sequence[Fraction]) -> tuple:
    """Threshold coherence of a LUV over an explicit grid, as sentences.

    `X > r'` implies `X > r` when `r < r'`. In the source these are consequences
    of the background theory that represents `X`'s computation, revealed by the
    deductive process; here they are stage sentences, which is the same role.
    Without them a world may hold `X > 2/3` and deny `X > 1/3`, and no reading of
    `X` as a number survives.

    The grid is explicit because a stage is one fixed finite set of sentences
    while the day's grid moves: the chain a trajectory needs is the one over
    every threshold any day of it will price.
    """
    rs = sorted({Fraction(r) for r in grid})
    return tuple(Implies(luv.gt(hi), luv.gt(lo)) for lo, hi in zip(rs, rs[1:]))


def threshold_axioms(luv: LUV, k: int) -> tuple:
    """Threshold coherence on the precision-`k` grid alone."""
    return threshold_chain(luv, [Fraction(i, k) for i in range(k)])


def day_grid(n: int) -> tuple:
    """The thresholds day `n` prices: `i/(n+1)` for `i < n+1`."""
    return tuple(Fraction(i, n + 1) for i in range(n + 1))


def merged_grid(days: Iterable[int]) -> tuple:
    """Every threshold any of the given days prices, once, in order.

    A stage is one fixed finite set of sentences and the day's grid moves, so a
    trajectory that will be inspected at days `0..N` needs threshold coherence
    over the union of those grids. Supplying less is not merely incomplete: the
    thresholds the chain misses are unconstrained atoms, so worlds appear that
    hold `X > 3/4` while denying `X > 1/3`, and the LUV has no reading as a
    number in them.
    """
    out: set = set()
    for n in days:
        out |= set(day_grid(n))
    return tuple(sorted(out))


def valued_at(luv: LUV, x: Fraction, k: int) -> tuple:
    """`PCWorld.ValuesAt`, restricted to the precision-`k` grid, as sentences.

    `ExactTheoryPresentation.threshold_iff` says a consistent world holds
    `X > r` exactly when `r < x`. On a finite grid that is a finite conjunction
    of literals, which is what a finite stage can carry.
    """
    out = []
    for i in range(k):
        r = Fraction(i, k)
        out.append(luv.gt(r) if r < x else Neg(luv.gt(r)))
    return tuple(out)


# ----------------------------------------------------- affine combinations


@dataclass(frozen=True)
class AffineForm:
    """`structure AffineCombination` — `c + sum_i e_i * phi_i`.

    Repeated sentences are permitted, exactly as in the source, because the
    value and price arguments never need a normal form. `coefficients` is where
    a caller that does need one asks for it.
    """

    const: Fraction
    terms: tuple                          # tuple[(Fraction, Sentence), ...]

    def sentences(self) -> tuple:
        return tuple(s for _, s in self.terms)

    def price(self, prices: Mapping) -> Fraction:
        """`AffineCombination.price`: the value at a price vector."""
        total = Fraction(self.const)
        for c, s in self.terms:
            if s not in prices:
                raise KeyError(f"unpriced sentence {s!r}")
            total += Fraction(c) * Fraction(prices[s])
        return total

    def coefficients(self) -> dict:
        """The normal form: one rational coefficient per distinct sentence."""
        out: dict = {}
        for c, s in self.terms:
            out[s] = out.get(s, ZERO) + Fraction(c)
        return {s: c for s, c in out.items() if c != ZERO}

    def scale(self, a: Fraction) -> "AffineForm":
        a = Fraction(a)
        return AffineForm(self.const * a, tuple((c * a, s) for c, s in self.terms))

    def add(self, other: "AffineForm") -> "AffineForm":
        return AffineForm(self.const + other.const, self.terms + other.terms)

    @staticmethod
    def zero() -> "AffineForm":
        return AffineForm(ZERO, ())

    @staticmethod
    def of_sentence(phi) -> "AffineForm":
        return AffineForm(ZERO, ((ONE, phi),))


# ---------------------------------------------------------------- worlds


def worlds_over(names: Sequence[str]) -> list:
    """Every `{0,1}` valuation of the given atoms, as dictionaries."""
    names = tuple(names)
    return [dict(zip(names, bits))
            for bits in product((False, True), repeat=len(names))]
