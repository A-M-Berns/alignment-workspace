"""The selected-trust non-preemption lemma, in the finite cell register.

A `Frame` has cells `x` with the agent's credence `p[x]`, a menu, the agent's operative
value `EX[x][m]` of executing `m` on `x`, the protected principal's value `W[x][m]`, the
principal's selection `J[x]` and a candidate selector `sigma[x]`.  All rationals.

    valuation(sel) = Σ_x p[x] EX[x][sel[x]]
    selected_gap   = Σ_x p[x] [ (EX[x][σx] − EX[x][Jx]) − (W[x][σx] − W[x][Jx]) ]
    principal_regret = Σ_x p[x] (W[x][σx] − W[x][Jx])

    valuation(σ) − valuation(J) = selected_gap + principal_regret        (identity)

Mirrors `lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q


@dataclass(frozen=True)
class Frame:
    p: dict            # cell -> credence
    EX: dict           # cell -> {item: agent operative value}
    W: dict            # cell -> {item: protected principal value}
    J: dict            # cell -> item chosen by the protected principal
    sigma: dict        # cell -> item the candidate selector substitutes

    @property
    def cells(self):
        return list(self.p)

    @property
    def menu(self):
        return list(next(iter(self.EX.values())))


def valuation(f: Frame, sel):
    return sum(f.p[x] * f.EX[x][sel[x]] for x in f.cells)


def agent_diff(f: Frame, x):
    return f.EX[x][f.sigma[x]] - f.EX[x][f.J[x]]


def principal_diff(f: Frame, x):
    return f.W[x][f.sigma[x]] - f.W[x][f.J[x]]


def selected_gap(f: Frame):
    return sum(f.p[x] * (agent_diff(f, x) - principal_diff(f, x)) for x in f.cells)


def principal_regret(f: Frame):
    return sum(f.p[x] * principal_diff(f, x) for x in f.cells)


def gain(f: Frame):
    return valuation(f, f.sigma) - valuation(f, f.J)


def pair_gap(f: Frame, j, m):
    return sum(f.p[x] * ((f.EX[x][m] - f.EX[x][j]) - (f.W[x][m] - f.W[x][j]))
               for x in f.cells if f.J[x] == j and f.sigma[x] == m)


def disagreement_mass(f: Frame):
    return sum(f.p[x] for x in f.cells if f.sigma[x] != f.J[x])


def grade_trust_level(f: Frame):
    """The smallest η with |EX − W| ≤ η everywhere: pointwise two-sided trust."""
    return max(abs(f.EX[x][m] - f.W[x][m]) for x in f.cells for m in f.menu)


def principal_regret_bound_cellwise(f: Frame, b, w):
    """(δ, ζ, η) read off displayed values `b`, correspondence points `w` and the
    principal's choice: the cellwise argmax-transfer constants."""
    delta = max(abs(w[x][m] - b[x][m]) for x in f.cells for m in f.menu)
    zeta = max(abs(f.W[x][m] - w[x][m]) for x in f.cells for m in f.menu)
    eta = max(max(b[x][m] for m in f.menu) - b[x][f.J[x]] for x in f.cells)
    return delta, zeta, eta


def sup_gain(f: Frame, selectors):
    return max(valuation(f, s) - valuation(f, f.J) for s in selectors)


def all_selectors(f: Frame):
    from itertools import product
    cells = f.cells
    for combo in product(f.menu, repeat=len(cells)):
        yield dict(zip(cells, combo))
