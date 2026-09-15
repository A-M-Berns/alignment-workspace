"""The market / inductor side (E7).

The regret algebra is the consolidation round's `src/regret.py`, loaded from its own
directory (reused, not forked).  This module adds: the worlds-to-log map for one
occurrence, the activated securities computed from `C_n` and the payload, the exact
regrets on finite `W`, and a concrete credence process for the day-`n` prices of the
activation sentence across a sequence of occurrences (the Laplace rule), with its
exact rate.
"""
from __future__ import annotations

import importlib.util
import pathlib
from fractions import Fraction as F

from . import ecosystem as eco

_CONSOLIDATION = (pathlib.Path(__file__).resolve().parents[2]
                  / "2026-09-08-legitimate-deference-consolidation" / "src" / "regret.py")
_spec = importlib.util.spec_from_file_location("consolidation_regret", _CONSOLIDATION)
regret = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(regret)


def occurrence(worlds, pi, advisor, principal, sigma, cfg=eco.Config()):
    """One evaluation occurrence over finite `W`: for each world the log, `C_n(w)`, the
    clause table, and `Ṽ_n(w)` where certified."""
    out = {}
    for w in worlds:
        fr = eco.Frame(w, principal, cfg)
        C, clauses, log = eco.activation(fr, advisor, sigma(w))
        out[w.name] = {"C": C, "clauses": clauses, "log": log,
                       "V": fr.V(log) if C else None, "pi": pi[w.name]}
    return out


def securities(occ, cands=eco.CANDS):
    """`U_{n,a} = C_n · V̄_a` for the canonical zero completion; completion-invariant."""
    pi = {n: d["pi"] for n, d in occ.items()}
    C = lambda n: occ[n]["C"]
    Vp = {n: d["V"] for n, d in occ.items() if d["C"]}
    Vbar = regret.complete(pi, C, Vp, cands, lambda w, a: F(0))
    U = {a: regret.activated(C, Vbar, a) for a in cands}
    return pi, C, Vp, Vbar, U


def regrets(occ, alpha, cands=eco.CANDS):
    """`R_U`, `R_auth`, `p`, `η` for the followed strategy `alpha[world][cand]`."""
    pi, C, Vp, Vbar, _ = securities(occ, cands)
    RU = regret.regret_U(pi, C, Vbar, alpha, cands)
    p = regret.mass(pi, C)
    eta = regret.void_mass(pi, C)
    RA = regret.regret_auth(pi, C, Vp, alpha, cands) if p > 0 else None
    return {"R_U": RU, "R_auth": RA, "p": p, "eta": eta,
            "bound": (max(RU, F(0)) / (1 - eta)) if eta < 1 else None}


def hard_selector(occ, choice):
    """`α(w)` as a hard selector `choice(world_name) ∈ Q`."""
    return {n: {a: (F(1) if a == choice(n) else F(0)) for a in eco.CANDS} for n in occ}


# --------------------------------------------------------------- credence process


def laplace(outcomes):
    """The Laplace-rule price of the next activation sentence after the settled
    activation outcomes `outcomes` (a list of 0/1): `(successes + 1) / (n + 2)`.  The
    void-mass bound `η_n` is one minus it."""
    n = len(outcomes)
    return F(sum(outcomes) + 1, n + 2)


def eta_sequence(outcomes):
    """`η_n = 1 − P_n(C_n)` for `n = 0..N` along a settled outcome sequence."""
    return [1 - laplace(outcomes[:n]) for n in range(len(outcomes) + 1)]


def eta_rate_bound(outcomes):
    """Exact rate facts for the Laplace process, checked in `tests/test_market.py` and
    proved in Lean (`EvaluationEcosystem.laplace_eta_le`, `laplace_eta_sub_freq_abs_le`):

        η_n = (F_n + 1)/(n + 2)     with F_n the failures among the first n,
        |η_n − F_n/n| ≤ 3/(n + 2)  for n ≥ 1,
        η_n ≤ (F_∞ + 1)/(n + 2)    whenever the total failure count is F_∞."""
    out = []
    for n in range(1, len(outcomes) + 1):
        Fn = n - sum(outcomes[:n])
        eta = F(Fn + 1, n + 2)
        assert eta == 1 - laplace(outcomes[:n])
        out.append((n, eta, F(Fn, n), abs(eta - F(Fn, n)), F(3, n + 2)))
    return out
