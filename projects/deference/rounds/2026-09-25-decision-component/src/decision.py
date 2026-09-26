"""Authority as a constraint on action: the Normative Inductor's decision component with
a permission layer.

Mirrors `lean/Workspace/Deference/Contrib/DecisionComponent.lean`: the permission ramp, the
permission weight (1 on inquiry, 0 on a declared violation, the product of the shortfall
and taint ramps otherwise), the composed gate (permission × adequacy ramp × any bounded
preference, normalized, with an inquiry floor), the layered procedure, the Part C
liability identity, the continuation bounds, and the fixtures.  Exact arithmetic."""

from dataclasses import dataclass
from fractions import Fraction as Q


# --------------------------------------------------------------------------- ramps

def clamp01(x):
    return max(Q(0), min(Q(1), x))


def pramp(theta_lo, theta_hi, x):
    """1 below theta_lo, 0 above theta_hi, linear between."""
    return clamp01((theta_hi - x) / (theta_hi - theta_lo))


def ad_weight(b, tau, delta, a):
    """The landed adequacy ramp."""
    return clamp01((b[a] - tau) / delta)


# --------------------------------------------------------------------------- the composed gate

@dataclass(frozen=True)
class GateParams:
    viol: object            # option -> bool (structural, from the interface and J)
    inq: frozenset          # inquiry options
    theta_lo: Q
    theta_hi: Q
    tau: Q
    delta: Q
    phi0: Q                 # the inquiry floor


def perm_weight(G, pS, pT, a):
    if a in G.inq:
        return Q(1)
    if G.viol(a):
        return Q(0)
    return pramp(G.theta_lo, G.theta_hi, pS[a]) * pramp(G.theta_lo, G.theta_hi, pT[a])


def cweight(G, pS, pT, b, pref, a):
    if a in G.inq:
        return max(G.phi0, ad_weight(b, G.tau, G.delta, a) * pref[a])
    return perm_weight(G, pS, pT, a) * ad_weight(b, G.tau, G.delta, a) * pref[a]


def cgate(G, pS, pT, b, pref, options):
    """The composed gate's distribution over the options."""
    w = {a: cweight(G, pS, pT, b, pref, a) for a in options}
    Z = sum(w.values())
    return {a: w[a] / Z for a in options}


def permitted(G, pS, pT, a):
    return a in G.inq or (not G.viol(a) and pS[a] <= G.theta_lo and pT[a] <= G.theta_lo)


def mass_off(p, S):
    return sum(v for a, v in p.items() if a not in S)


def l1(p, p2):
    return sum(abs(p[a] - p2[a]) for a in p)


def layered_decision(G, pS, pT, b, pref, options, A):
    """The layered procedure's record: which layer settles each option."""
    p = cgate(G, pS, pT, b, pref, options)
    rows = {}
    for a in options:
        if a in G.inq:
            rows[a] = ("inquiry", p[a])
        elif G.viol(a):
            rows[a] = ("permission: structural", p[a])
        elif pS[a] >= G.theta_hi or pT[a] >= G.theta_hi:
            rows[a] = ("permission: forecast", p[a])
        elif a not in A:
            rows[a] = ("adequacy", p[a])
        else:
            rows[a] = ("competence", p[a])
    return rows


# --------------------------------------------------------------------------- the lexical chooser, for regression

def lexical_choice(varpi, ord_values, counts):
    """The scored chooser: argmax of ord − ϖ·n."""
    scores = {a: ord_values[a] - varpi * counts[a] for a in ord_values}
    return max(scores, key=lambda a: scores[a])


# --------------------------------------------------------------------------- Part C

def liability(h, g, n):
    """The enforcer's cumulative liability: her decision's ordinary value less the agent's
    alternative, summed."""
    return sum(h(t) - g(t) for t in range(n))


# --------------------------------------------------------------------------- continuations

def execution_prob(rhos):
    out = Q(1)
    for r in rhos:
        out *= r
    return out


def last_check(s, theta, t):
    lr = 0
    for u in range(1, t + 1):
        if theta <= s[u] - s[lr]:
            lr = u
    return lr


def cum_exposure(slack, k):
    return sum(slack[:k])


def flips(sh):
    """Indices j with sh[j] false and sh[j+1] true; even j = agent step, odd = exterior."""
    return [j for j in range(len(sh) - 1) if not sh[j] and sh[j + 1]]
