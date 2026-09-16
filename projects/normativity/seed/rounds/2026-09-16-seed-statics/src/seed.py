"""The seed as a typed object, and the forced-region statics over it.

Mirrors `lean/Workspace/Normativity/Contrib/SeedStatics.lean`: a fragment is a list of
named coordinates; a settlement pins some of them; a row is `a . x <= b`; substantive
items are leverage forms with a port and a strength; structural items are rows with a
kind and a surface id; the docket state has two withdrawal channels; the forced bundle
is the live specialized rows plus the pin rows, and its region is `cube ∩ rows`.

Intervals are computed by the exact simplex in `lp.py`; `fm.py` cross-checks small
cases with the elimination the Lean file proves correct.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Optional

from . import lp

F = Fraction


# --- fragment and settlement -------------------------------------------------------------

class Fragment:
    """Named coordinates; `index(name)` is the canonical security identity."""

    def __init__(self, names):
        self.names = list(names)
        self.idx = {n: i for i, n in enumerate(self.names)}
        assert len(self.idx) == len(self.names)

    @property
    def d(self):
        return len(self.names)

    def index(self, name):
        return self.idx[name]

    def row(self, coeffs: dict, b) -> "Row":
        a = [F(0)] * self.d
        for name, v in coeffs.items():
            a[self.index(name)] += F(v)
        return Row(a, F(b))


@dataclass(frozen=True)
class Row:
    a: tuple
    b: Fraction

    def __init__(self, a, b):
        object.__setattr__(self, "a", tuple(F(v) for v in a))
        object.__setattr__(self, "b", F(b))

    def sat(self, x) -> bool:
        return sum(ai * xi for ai, xi in zip(self.a, x)) <= self.b

    def sat_strict(self, x) -> bool:
        return sum(ai * xi for ai, xi in zip(self.a, x)) < self.b

    def pair(self):
        return (list(self.a), self.b)


class Settlement:
    """Settled coordinates with truth values; `le(other)` is inclusion with compatible
    valuations."""

    def __init__(self, val: Optional[dict] = None):
        self.val = dict(val or {})

    def le(self, other: "Settlement") -> bool:
        return all(other.val.get(i) == v for i, v in self.val.items())

    def extend(self, more: dict) -> "Settlement":
        out = dict(self.val)
        for i, v in more.items():
            assert out.get(i, v) == v, "incompatible valuation"
            out[i] = v
        return Settlement(out)

    def pinned(self, x) -> bool:
        return all(x[i] == (F(1) if v else F(0)) for i, v in self.val.items())

    def specialize(self, r: Row) -> Row:
        a = [F(0) if i in self.val else ai for i, ai in enumerate(r.a)]
        b = r.b - sum(r.a[i] * (F(1) if v else F(0)) for i, v in self.val.items())
        return Row(a, b)

    def pin_rows(self, d: int) -> list[Row]:
        out = []
        for i, v in self.val.items():
            e = [F(0)] * d
            e[i] = F(1)
            t = F(1) if v else F(0)
            out.append(Row(e, t))
            out.append(Row([-x for x in e], -t))
        return out


# --- the seed ------------------------------------------------------------------------------

@dataclass(frozen=True)
class Form:
    """A leverage form: kind in {premise, applicability, strength}, coordinates, and c."""
    kind: str
    coords: tuple
    c: Fraction

    def row(self, d: int) -> Row:
        a = [F(0)] * d
        if self.kind == "premise":
            (X,) = self.coords
            a[X] = F(-1)
            return Row(a, -self.c)
        if self.kind == "applicability":
            X, XA = self.coords
            a[X] += self.c
            a[XA] += F(-1)
            return Row(a, F(0))
        if self.kind == "strength":
            XA, XAY = self.coords
            a[XA] += self.c
            a[XAY] += F(-1)
            return Row(a, F(0))
        raise ValueError(self.kind)


@dataclass(frozen=True)
class SubItem:
    form: Form
    port: int
    label: str = ""


@dataclass(frozen=True)
class StrItem:
    row: Row
    kind: str          # dominance | impartiality | coherence
    id: int
    label: str = ""


@dataclass
class Constitutive:
    standing: frozenset = frozenset()
    protected_class: frozenset = frozenset()


@dataclass
class Seed:
    sub: list = field(default_factory=list)
    str_: list = field(default_factory=list)
    con: Constitutive = field(default_factory=Constitutive)

    def humble_items(self) -> bool:
        return all(0 < it.form.c < 1 for it in self.sub)

    def dogmatic_items(self):
        return [it for it in self.sub if not (0 < it.form.c < 1)]

    def structural(self) -> "Seed":
        return Seed([], list(self.str_), self.con)

    def merge(self, other: "Seed") -> "Seed":
        assert self.str_ == other.str_
        return Seed(self.sub + other.sub, list(self.str_), self.con)


@dataclass(frozen=True)
class DocketState:
    defeated: frozenset = frozenset()     # ports with a landed defeater
    withdrawn: frozenset = frozenset()    # structural ids withdrawn by surface change


QUIET = DocketState()


def live_sub(S: Seed, st: DocketState):
    return [it for it in S.sub if it.port not in st.defeated]


def live_str(S: Seed, st: DocketState):
    return [it for it in S.str_ if it.id not in st.withdrawn]


# --- the forced region ---------------------------------------------------------------------

def forced_rows(S: Seed, W, st: DocketState, Fset: Settlement, d: int):
    """The forced bundle, as (cite, row) pairs, before the pin rows."""
    out = []
    for it in live_sub(S, st) + list(W):
        out.append((("sub", it.port, it.label), Fset.specialize(it.form.row(d))))
    for it in live_str(S, st):
        out.append((("str", it.id, it.label), Fset.specialize(it.row)))
    return out


def forced_bundle(S, W, st, Fset, d):
    rows = forced_rows(S, W, st, Fset, d)
    rows += [(("settled", i), r) for i, r in zip(
        [i for i in Fset.val for _ in (0, 1)], Fset.pin_rows(d))]
    return rows


def check_compiled(bundle, x) -> bool:
    """`checkCompiled`: cube membership and every row."""
    return all(0 <= xi <= 1 for xi in x) and all(r.sat(x) for _, r in bundle)


def in_region(S, W, st, Fset, d, x) -> bool:
    return check_compiled(forced_bundle(S, W, st, Fset, d), x)


def _pairs(bundle):
    return [r.pair() for _, r in bundle]


def forced_interval(S, W, st, Fset, d, phi) -> Optional[tuple]:
    return lp.interval(_pairs(forced_bundle(S, W, st, Fset, d)), d, phi)


def forced_intervals(S, W, st, Fset, d, coords=None) -> dict:
    coords = list(range(d)) if coords is None else coords
    return {phi: forced_interval(S, W, st, Fset, d, phi) for phi in coords}


def is_feasible(S, W, st, Fset, d) -> bool:
    return lp.feasible(_pairs(forced_bundle(S, W, st, Fset, d)), d)


def sure_loss_certificate(S, W, st, Fset, d):
    """The Farkas certificate over the forced bundle (plus cube), and the names of the
    bundle rows in its support."""
    bundle = forced_bundle(S, W, st, Fset, d)
    lam = lp.farkas_certificate(_pairs(bundle), d)
    if lam is None:
        return None
    support = [bundle[i][0] for i in range(len(bundle)) if lam[i] > 0]
    return {"multipliers": lam, "support": support}


def minimal_infeasible_subset(S, W, st, Fset, d):
    bundle = forced_bundle(S, W, st, Fset, d)
    keep = lp.minimal_infeasible_subset(_pairs(bundle), d)
    return [bundle[i][0] for i in keep]


def seed_leverage(intervals: dict, unsettled) -> Fraction:
    """Σ_φ (1 − |I_φ|) over the listed coordinates."""
    return sum(F(1) - (intervals[phi][1] - intervals[phi][0]) for phi in unsettled)


def level_neutral(S: Seed, d: int, coords=None, kinds=None) -> dict:
    """Structure alone (no substantive item, no warrant, quiet docket, empty settlement)
    must leave every coordinate at [0, 1].  Returns the offending coordinates.  `kinds`
    restricts which structural kinds are included."""
    T = S.structural()
    if kinds is not None:
        T = Seed([], [it for it in T.str_ if it.kind in kinds], T.con)
    ivs = forced_intervals(T, [], QUIET, Settlement(), d, coords)
    bad = {}
    for phi, iv in ivs.items():
        if iv is None or iv != (F(0), F(1)):
            bad[phi] = iv
    return bad


def symmetry_generated(S: Seed, sym) -> list:
    """Impartiality rows must be `P(s) − P(sym(s)) = 0` for the declared symmetry `sym`
    (a permutation of coordinates).  Returns the impartiality items that are not."""
    bad = []
    for it in S.str_:
        if it.kind != "impartiality":
            continue
        nz = [(i, v) for i, v in enumerate(it.row.a) if v != 0]
        ok = (len(nz) == 2 and it.row.b == 0 and nz[0][1] == -nz[1][1]
              and (sym(nz[0][0]) == nz[1][0] or sym(nz[1][0]) == nz[0][0]))
        if not ok:
            bad.append(it)
    return bad


# --- transport ------------------------------------------------------------------------------

def transport_row(rho, r: Row, d_new: int) -> Row:
    """Reindex a row along `rho : old coordinate -> new coordinate`."""
    a = [F(0)] * d_new
    for i, v in enumerate(r.a):
        a[rho[i]] += v
    return Row(a, r.b)


def transport_seed(rho, S: Seed, d_new: int) -> Seed:
    """Transport every item; leverage forms are transported coordinatewise."""
    sub = [SubItem(Form(it.form.kind, tuple(rho[c] for c in it.form.coords), it.form.c),
                   it.port, it.label) for it in S.sub]
    str_ = [StrItem(transport_row(rho, it.row, d_new), it.kind, it.id, it.label)
            for it in S.str_]
    return Seed(sub, str_, S.con)


# --- coherence helpers ----------------------------------------------------------------------

def frechet_rows(frag: Fragment, conj: str, parts: list[str], id0: int) -> list[StrItem]:
    """Coherence rows for a conjunction coordinate: conj <= each part, and
    conj >= Σ parts − (k − 1)."""
    out = []
    for p in parts:
        out.append(StrItem(frag.row({conj: 1, p: -1}, 0), "coherence", id0, f"{conj}<={p}"))
        id0 += 1
    coeffs = {conj: -1}
    for p in parts:
        coeffs[p] = coeffs.get(p, 0) + 1
    out.append(StrItem(frag.row(coeffs, len(parts) - 1), "coherence", id0,
                       f"{conj}>=sum-{len(parts) - 1}"))
    return out


def equality_rows(frag: Fragment, coeffs: dict, b, kind: str, id0: int, label: str):
    r1 = frag.row(coeffs, b)
    r2 = frag.row({k: -v for k, v in coeffs.items()}, -F(b))
    return [StrItem(r1, kind, id0, label + " (<=)"), StrItem(r2, kind, id0 + 1, label + " (>=)")]
