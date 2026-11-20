"""A regulator: a policy from disturbances to actions.  Its aim, relative to a class of
target sets of outcomes, is the target it hits more often than any fixed action does."""
from fractions import Fraction
from itertools import combinations, product

D = [-1, 0, 1]
OUTCOMES = [-2, -1, 0, 1, 2]
UNIFORM = {d: Fraction(1, 3) for d in D}


def outcome(d, a):
    return d + a


def policies(actions):
    return [dict(zip(D, acts)) for acts in product(actions, repeat=len(D))]


def constant(a):
    return {d: a for d in D}


def hit(pol, T, pD):
    return sum(pD[d] for d in D if outcome(d, pol[d]) in T)


def gain(pol, T, pD, actions):
    return hit(pol, T, pD) - max(hit(constant(a), T, pD) for a in actions)


def all_targets(outcomes):
    return [frozenset(c) for r in range(1, len(outcomes)) for c in combinations(outcomes, r)]


def interval_targets(outcomes):
    lo, hi = min(outcomes), max(outcomes)
    return [frozenset(range(a, b + 1)) for a in outcomes for b in outcomes if a <= b and (a, b) != (lo, hi)]


def aim(pol, targets, pD, actions):
    """(strength, the targets attaining it)."""
    g = {T: gain(pol, T, pD, actions) for T in targets}
    best = max(g.values())
    return best, [T for T in targets if g[T] == best]
