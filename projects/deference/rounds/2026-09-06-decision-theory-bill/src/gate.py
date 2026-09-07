"""The decision adapter as a gate over adequacy prices.

Register.  A finite menu `Q` plus the inquiry response `BOT`.  The market displays an
adequacy price `b[q] ∈ [0,1]` for each `q` (the price of the sentence "q is adequate for
the live obligations").  The compiled region encodes the norm as: at a region point `u`,
every inadequate response has `u[q] ≤ tau` and some adequate response has
`u[q] ≥ tau + 2·delta` (the margin).  The public defect is `d = sup_q |b[q] − u[q]|`.

Gates map prices to a distribution over `Q ∪ {BOT}`:
  soft_gate   weight `ramp((b[q] − tau)/delta)` times a task preference; if no response
              is confidently adequate (weight 1) it returns BOT;
  hard_gate   task-argmax over `{q : b[q] > tau}`; BOT if that set is empty.

`mass_off(dist, A)` is the mass outside the true adequate set `A` (BOT counts as off `A`:
it is charged, not forgiven).  The theorem checked here: for the soft gate with the margin,
`mass_off ≤ kappa · d` with `kappa = |Q|·R/delta`, `R = max pref / min pref`; for the hard
gate no `kappa` exists.
"""
from __future__ import annotations

from fractions import Fraction as Q

BOT = "inquire"


def ramp(x):
    return max(Q(0), min(Q(1), x))


def sup_dist(b, u):
    return max(abs(b[q] - u[q]) for q in b)


def soft_gate(b, pref, tau, delta):
    w = {q: ramp((b[q] - tau) / delta) for q in b}
    if not any(w[q] == 1 for q in b):
        return {BOT: Q(1)}
    total = sum(w[q] * pref[q] for q in b)
    return {q: w[q] * pref[q] / total for q in b if w[q] > 0}


def hard_gate(b, pref, tau):
    admitted = [q for q in b if b[q] > tau]
    if not admitted:
        return {BOT: Q(1)}
    best = max(admitted, key=lambda q: (pref[q], q))
    return {best: Q(1)}


def mass_off(dist, adequate):
    return sum(p for q, p in dist.items() if q not in adequate)


def kappa(menu, pref, delta):
    R = max(pref.values()) / min(pref.values())
    return Q(len(menu)) * R / delta


def kappa_sharp(menu, adequate, marked, pref, delta):
    """`(Σ_{q ∉ A} pref) / W / δ` with `W` the preference mass of the marked adequate
    responses: inadequate preference mass over certified adequate mass."""
    off = sum(pref[q] for q in menu if q not in adequate)
    W = sum(pref[q] for q in marked)
    return off / W / delta


def region_point(menu, adequate, tau, delta):
    """A canonical region point with the margin."""
    return {q: (tau + 2 * delta if q in adequate else tau) for q in menu}


# --- scalar compensation ---------------------------------------------------------------

def scalarized_choice(task, loss, lam):
    return max(task, key=lambda q: (task[q] - lam * loss[q], q))


def gated_choice(task, adequate):
    if not adequate:
        return BOT
    return max(adequate, key=lambda q: (task[q], q))


def bribe_needed(task, loss, lam, forbidden, best_adequate):
    """The smallest stake increase on `forbidden` that flips the scalarized choice."""
    gap = (task[best_adequate] - lam * loss[best_adequate]) - (task[forbidden] - lam * loss[forbidden])
    return max(Q(0), gap)
