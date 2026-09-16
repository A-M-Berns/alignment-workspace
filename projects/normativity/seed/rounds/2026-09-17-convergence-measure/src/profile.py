"""The convergence profile over interval data, mirroring `ConvergenceMeasure.lean`.

A reasoner is a `(seed, warrants, docket state)` triple over a shared settlement; its
forced intervals come from the seed round's exact simplex (loaded by path, unmodified).
Hull, common interval, discord and the three masses are computed on a declared fragment
with declared weights.  Discord certificates merge two bound certificates into a Farkas
certificate for the merged bundle, exactly as `mergeCert` does.
"""

from __future__ import annotations

import importlib.util
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

F = Fraction

SEED_ROUND = Path(__file__).resolve().parents[2] / "2026-09-16-seed-statics"


def _load_seed_round():
    """Import the seed round's `src` package by path, without modifying it."""
    if "seedround" in sys.modules:
        return sys.modules["seedround"]
    spec = importlib.util.spec_from_file_location(
        "seedround", SEED_ROUND / "src" / "__init__.py",
        submodule_search_locations=[str(SEED_ROUND / "src")])
    mod = importlib.util.module_from_spec(spec)
    sys.modules["seedround"] = mod
    spec.loader.exec_module(mod)
    return mod


seedround = _load_seed_round()
from seedround import lp, fm, seed as S  # noqa: E402
from seedround import fixtures as seedfix  # noqa: E402


@dataclass
class Reasoner:
    name: str
    seed: "S.Seed"
    W: list
    st: "S.DocketState"

    def region_rows(self, Fset, d):
        return S.forced_bundle(self.seed, self.W, self.st, Fset, d)

    def interval(self, Fset, d, phi):
        return S.forced_interval(self.seed, self.W, self.st, Fset, d, phi)

    def feasible(self, Fset, d):
        return S.is_feasible(self.seed, self.W, self.st, Fset, d)


def intervals(reasoners, Fset, d, Phi):
    """`I[i][phi]`; a refuted reasoner (empty region) is excluded from the profile and
    reported."""
    out = {}
    refuted = []
    for r in reasoners:
        ivs = multi_interval([row.pair() for _, row in r.region_rows(Fset, d)], d, Phi)
        if ivs is None:
            refuted.append(r.name)
            continue
        out[r.name] = ivs
    return out, refuted


def multi_interval(rows, d, coords):
    """All forced intervals of `coords` from one phase-one solve: the feasible tableau is
    copied and re-optimised for each of the `2·|coords|` objectives.  Same answers as
    the seed round's `lp.interval`, which the tests cross-check; `None` if infeasible."""
    all_rows = list(rows)
    for i in range(d):
        e = [F(0)] * d
        e[i] = F(1)
        all_rows.append((e, F(1)))
    m, n = len(all_rows), d + len(all_rows)
    A, b = [], []
    for k, (a, bk) in enumerate(all_rows):
        A.append([F(v) for v in a] + [F(1) if j == k else F(0) for j in range(m)])
        b.append(F(bk))
    for i in range(m):
        if b[i] < 0:
            A[i] = [-v for v in A[i]]
            b[i] = -b[i]
    unit_of_row, used = {}, set()
    for j in range(n):
        col = [A[i][j] for i in range(m)]
        nz = [i for i in range(m) if col[i] != 0]
        if len(nz) == 1 and col[nz[0]] == 1 and nz[0] not in unit_of_row and j not in used:
            unit_of_row[nz[0]] = j
            used.add(j)
    art_rows = [i for i in range(m) if i not in unit_of_row]
    na = len(art_rows)
    ncols = n + na
    T = []
    for i in range(m):
        art = [F(0)] * na
        if i in art_rows:
            art[art_rows.index(i)] = F(1)
        T.append(A[i] + art + [b[i]])
    obj = [F(0)] * n + [F(1)] * na + [F(0)]
    basis = [0] * m
    for i in range(m):
        if i in unit_of_row:
            basis[i] = unit_of_row[i]
        else:
            basis[i] = n + art_rows.index(i)
            obj = [o - t for o, t in zip(obj, T[i])]
    T.append(obj)
    lp._run(T, basis, ncols)
    if T[m][ncols] != 0:
        return None
    drop = []
    for i in range(m):
        if basis[i] >= n:
            s_ = next((j for j in range(n) if T[i][j] != 0), None)
            if s_ is None:
                drop.append(i)
            else:
                lp._pivot(T, i, s_)
                basis[i] = s_
    for i in sorted(drop, reverse=True):
        del T[i]
        del basis[i]
    m2 = len(T) - 1
    base = [row[:n] + [row[ncols]] for row in T[:m2]]
    out = {}
    for phi in coords:
        vals = []
        for sign in (1, -1):
            c = [F(0)] * n
            c[phi] = F(sign)
            T2 = [list(r) for r in base]
            ob = c + [F(0)]
            bs = list(basis)
            for i in range(m2):
                f = ob[bs[i]]
                if f != 0:
                    ob = [o - f * t for o, t in zip(ob, T2[i])]
            T2.append(ob)
            status = lp._run(T2, bs, n)
            assert status == "optimal"
            x = [F(0)] * n
            for i in range(m2):
                x[bs[i]] = T2[i][n]
            vals.append(x[phi])
        out[phi] = (vals[0], vals[1])
    return out


def hull(I, phi):
    los = [I[i][phi][0] for i in I]
    his = [I[i][phi][1] for i in I]
    return (min(los), max(his))


def common(I, phi):
    los = [I[i][phi][0] for i in I]
    his = [I[i][phi][1] for i in I]
    return (max(los), min(his))


def discord(I, phi):
    lo, hi = common(I, phi)
    return hi < lo


def uniform(Phi):
    return {phi: F(1, len(Phi)) for phi in Phi}


def profile(I, Phi, w=None):
    w = uniform(Phi) if w is None else w
    assert all(w[phi] > 0 for phi in Phi) and sum(w[phi] for phi in Phi) == 1
    H = sum(w[phi] * (hull(I, phi)[1] - hull(I, phi)[0]) for phi in Phi)
    O = sum(w[phi] * max(F(0), common(I, phi)[1] - common(I, phi)[0]) for phi in Phi)
    D = sum(w[phi] for phi in Phi if discord(I, phi))
    delta = [phi for phi in Phi if discord(I, phi)]
    return {"hull": H, "overlap": O, "discord": D, "delta": delta,
            "hulls": {phi: hull(I, phi) for phi in Phi},
            "commons": {phi: common(I, phi) for phi in Phi}}


def blocked_hull(I, Phi):
    widths = [hull(I, phi)[1] - hull(I, phi)[0] for phi in Phi]
    unp = [x for x in widths if x > 0]
    return sum(widths) / len(unp) if unp else F(0)


def naive_hull(I, Phi):
    widths = [hull(I, phi)[1] - hull(I, phi)[0] for phi in Phi]
    return sum(widths) / len(Phi)


def discord_graph(I, Phi):
    """Edges `(i, j, phi)` where reasoner `j`'s interval lies strictly above `i`'s."""
    edges = []
    names = list(I)
    for a in names:
        for b in names:
            if a < b:
                for phi in Phi:
                    if I[a][phi][1] < I[b][phi][0] or I[b][phi][1] < I[a][phi][0]:
                        edges.append((a, b, phi))
    return edges


def discord_certificate(r1, r2, Fset, d, phi):
    """For two reasoners with `hi_2 < lo_1` on `phi` (or the reverse): a lower-bound
    certificate over reasoner 1's bundle and an upper-bound certificate over reasoner
    2's bundle, merged into a Farkas certificate for the merged bundle (rows of both plus
    the cube), verified exactly; and the minimal infeasible subset of the merged bundle."""
    B1 = r1.region_rows(Fset, d)
    B2 = r2.region_rows(Fset, d)
    I1 = r1.interval(Fset, d, phi)
    I2 = r2.interval(Fset, d, phi)
    if I1 is None or I2 is None:
        return None
    if I2[1] < I1[0]:
        lower, upper, Blo, Bup = r1, r2, B1, B2
        lo, hi = I1[0], I2[1]
    elif I1[1] < I2[0]:
        lower, upper, Blo, Bup = r2, r1, B2, B1
        lo, hi = I2[0], I1[1]
    else:
        return None
    rows_lo = [r.pair() for _, r in Blo]
    rows_up = [r.pair() for _, r in Bup]
    lam = lp.bound_certificate(rows_lo, d, phi, -1, -lo)     # Σλa = -e_phi, Σλb = -lo
    mu = lp.bound_certificate(rows_up, d, phi, 1, hi)        # Σμa = e_phi,  Σμb = hi
    assert lam is not None and mu is not None
    # merged multipliers over rows_lo ++ cube ++ rows_up ++ cube
    allrows = rows_lo + lp.cube_rows(d) + rows_up + lp.cube_rows(d)
    mult = list(lam) + list(mu)
    assert lp.verify_farkas(allrows, d, mult)
    cites_lo = [Blo[i][0] for i in range(len(Blo)) if lam[i] > 0]
    cites_up = [Bup[i][0] for i in range(len(Bup)) if mu[i] > 0]
    merged = B1 + B2
    named = minimal_infeasible_items(merged, d)
    return {"gap": lo - hi, "lower_reasoner": lower.name, "upper_reasoner": upper.name,
            "support_lower": cites_lo, "support_upper": cites_up,
            "merged_feasible": False, "minimal_infeasible_subset": named}


def merged_feasible(reasoners, Fset, d):
    rows = []
    for r in reasoners:
        rows += [row.pair() for _, row in r.region_rows(Fset, d)]
    return lp.feasible(rows, d)


def merged_certificate(reasoners, Fset, d):
    rows = []
    cites = []
    for r in reasoners:
        for cite, row in r.region_rows(Fset, d):
            rows.append(row.pair())
            cites.append((r.name, cite))
    lam = lp.farkas_certificate(rows, d)
    if lam is None:
        return None
    bundle = []
    for r in reasoners:
        for cite, row in r.region_rows(Fset, d):
            bundle.append(((r.name, cite), row))
    return {"support": [cites[i] for i in range(len(rows)) if lam[i] > 0],
            "minimal_infeasible_subset": minimal_infeasible_items(bundle, d)}


def minimal_infeasible_items(bundle, d):
    """Deletion filter over the substantive and warrant rows of a merged bundle, with
    the shared structural and pin rows held fixed: the items some reasoner would have to
    give up.  Returns their cites."""
    def is_item(cite):
        c = cite[1] if isinstance(cite[0], str) and cite[0] not in ("sub", "str", "settled") else cite
        return c[0] == "sub"
    fixed = [r.pair() for cite, r in bundle if not is_item(cite)]
    cands = [(cite, r.pair()) for cite, r in bundle if is_item(cite)]
    assert not lp.feasible(fixed + [r for _, r in cands], d)
    keep = list(range(len(cands)))
    for i in list(keep):
        trial = fixed + [cands[j][1] for j in keep if j != i]
        if not lp.feasible(trial, d):
            keep.remove(i)
    return [cands[i][0] for i in keep]


def transport_seed_keeping_forms(rho, seed, d_new):
    """Corrected twin of the seed round's `transport_seed`: that function rebuilds every
    leverage form as a plain `Form`, which drops the negated forms (`NegPremise`) the
    fixtures use.  This one reindexes the coordinates and keeps the form's class."""
    sub = []
    for it in seed.sub:
        f = it.form
        g = object.__new__(type(f))
        object.__setattr__(g, "kind", f.kind)
        object.__setattr__(g, "coords", tuple(rho[c] for c in f.coords))
        object.__setattr__(g, "c", f.c)
        sub.append(S.SubItem(g, it.port, it.label))
    str_ = [S.StrItem(S.transport_row(rho, it.row, d_new), it.kind, it.id, it.label)
            for it in seed.str_]
    return S.Seed(sub, str_, seed.con)
