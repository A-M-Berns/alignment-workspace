"""Transparency as reference-relative factorization, on the repo's frame.

Objects (as in `ReasonMediatedAuthorship.lean`): a frame `beta(q, z)` from the
advisor's continuation `q` and the exterior `z` (principal policy and nature) to a
world; readings of the world — the declared-input view `x`, a channel `f` (reason
trace, activation, specification), the payload `V`; an audited class `D` of
continuations; a finite credence `pi` over `Z`.

Two primitives, both fiber invariance:

    transparent(beta, x, f, D, Z)      ∀z ∀q q' ∈ D. x = x'  →  f = f'     (class-relative)
    realizes(beta, x, f, kappa, D, Z)  ∀q ∈ D ∀z.  f(beta q z) = kappa(x(beta q z), z)   (reference-relative)

`transparent` is `ReasonMediated beta x f D z` at every `z`; `realizes` is the same with
the factor map declared.  Everything else is finite exact algebra over `pi`.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product


# ----------------------------------------------------------------- fiber invariance

def fiber_invariant(x, f, points):
    """`f` factors through `x` on `points`: equal `x` gives equal `f`."""
    table = {}
    for p in points:
        k, v = x(p), f(p)
        if k in table and table[k] != v:
            return False
        table[k] = v
    return True


def factor_map(x, f, points):
    """The factor `x-value -> f-value` when fiber invariance holds, else `None`."""
    table = {}
    for p in points:
        k, v = x(p), f(p)
        if k in table and table[k] != v:
            return None
        table[k] = v
    return table


def transparent(beta, x, f, D, Z):
    """Class-relative transparency: `ReasonMediated beta x f D z` at every `z`."""
    return all(fiber_invariant(lambda q: x(beta(q, z)), lambda q: f(beta(q, z)), D)
               for z in Z)


def realizes(beta, x, f, kappa, D, Z):
    """Reference-relative transparency: every audited continuation realizes `kappa`."""
    return all(f(beta(q, z)) == kappa(x(beta(q, z)), z) for q in D for z in Z)


def reference_of(beta, x, f, D, Z):
    """`transparent ⇔ ∃ kappa. realizes`: the reference the class implicitly declares,
    as a table `(x-value, z) -> f-value`, or `None`."""
    table = {}
    for z in Z:
        for q in D:
            k, v = (x(beta(q, z)), z), f(beta(q, z))
            if k in table and table[k] != v:
                return None
            table[k] = v
    return table


def blind(beta, f, pairs, z):
    """`Blind beta f P z`: every declared pair reads the same."""
    return all(f(beta(q, z)) == f(beta(q2, z)) for q, q2 in pairs)


# ---------------------------------------------------------------- finite credences

def expect(pi, g):
    """Expectation of `g : Z -> Q` under the credence `pi : dict Z -> Q`."""
    return sum((w * g(z) for z, w in pi.items()), Q(0))


def disagree(f, g):
    """The pathwise disagreement indicator of two readings of `z`."""
    return lambda z: Q(0) if f(z) == g(z) else Q(1)


def defect(beta, x, f, kappa, q):
    """The pathwise transparency defect of `q`: `[f(beta q z) ≠ kappa(x(beta q z), z)]`."""
    return disagree(lambda z: f(beta(q, z)), lambda z: kappa(x(beta(q, z)), z))


def law(pi, g):
    """The pushforward of `pi` under `g`."""
    out = {}
    for z, w in pi.items():
        out[g(z)] = out.get(g(z), Q(0)) + w
    return out


def tv(mu, nu):
    """Total variation between two finite laws."""
    keys = set(mu) | set(nu)
    return sum((abs(mu.get(k, Q(0)) - nu.get(k, Q(0))) for k in keys), Q(0)) / 2


def ind(b):
    return Q(1) if b else Q(0)


def mismatch_mass(pi, c_raw, c_corr):
    """`E[c_raw ∧ ¬c_corr]`, the directional activation mismatch."""
    return expect(pi, lambda z: ind(c_raw(z)) * (1 - ind(c_corr(z))))


def marginal_gap(pi, c_raw, c_corr):
    """`E[c_raw] − E[c_corr]`, the marginal-rate form (false as a charge)."""
    return expect(pi, lambda z: ind(c_raw(z))) - expect(pi, lambda z: ind(c_corr(z)))


# ------------------------------------------------------------------- posteriors

def posterior(prior, beta, f, y):
    """Posterior over `(q, z)` given the observation `f(beta q z) = y`, from a prior
    `dict (q, z) -> Q`.  Returns the normalized table, or `None` if `y` has mass 0."""
    lik = {p: w for p, w in prior.items() if f(beta(*p)) == y}
    total = sum(lik.values(), Q(0))
    return None if total == 0 else {p: w / total for p, w in lik.items()}


def reference_posterior(prior, beta, x, kappa, y):
    """The same posterior computed with the reference likelihood `kappa(x, z) = y`."""
    lik = {p: w for p, w in prior.items() if kappa(x(beta(*p)), p[1]) == y}
    total = sum(lik.values(), Q(0))
    return None if total == 0 else {p: w / total for p, w in lik.items()}


# -------------------------------------------------------------- normalization

def normalize(subst, moves):
    """Provenance normalization on a move alphabet: prohibited moves are replaced by
    the authorized move for the same matter (`subst`), or dropped (`None`)."""
    return tuple(m for m in (subst(m) for m in moves) if m is not None)


def normalization_exists(subst, moves, prohibited):
    """Every prohibited move `q` uses has an authorized substitute."""
    return all(subst(m) is not None for m in moves if m in prohibited)


# ------------------------------------------------------------ amendment tower

def tower(amend, c0, grounds, events, T):
    """`C_{t+1} = Amend(C_t, g_t, e_t)` from a fixed floor `c0`."""
    c = c0
    out = [c]
    for t in range(T):
        c = amend(c, grounds[t], events[t])
        out.append(c)
    return tuple(out)


def all_pairs(D):
    return [(q, q2) for q, q2 in product(D, D) if q != q2]
