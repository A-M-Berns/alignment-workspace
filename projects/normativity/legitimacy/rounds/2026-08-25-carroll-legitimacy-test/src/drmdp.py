"""Definition 1 of the source, and nothing else.

    M = <S, Theta, A, T, R_theta>

No standing, reason, authority, consent, legitimacy or narrative label reaches
this module. That is the point of it: everything the legitimacy layer later
adds has to be shown not to have leaked in here, and the only way to show that
is for the type to have no room for it.

Transitions and rewards are stored as sorted tuples rather than functions, so a
`DRMDP` has value equality. `Q_DR(a) == Q_DR(b)` is then a real test rather
than an identity check on two closures.

Arithmetic is exact: every reward is a `Fraction` and every transition weight is
a `Fraction` summing to one.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Iterable, Mapping, Sequence


def _key(item) -> str:
    return repr(item)


@dataclass(frozen=True)
class DRMDP:
    """`M = <S, Theta, A, T, R_theta>`.

    `transition` maps `(s, theta, a)` to a distribution over `(s', theta')`,
    given as a sorted tuple of `((s', theta'), Fraction)` pairs. `reward` maps
    `(theta, s, a, s')` to a `Fraction`, also as a sorted tuple of pairs.
    Both are total on their index sets; construction checks it.
    """

    states: tuple
    thetas: tuple
    actions: tuple
    transition: tuple
    reward: tuple
    s0: object
    theta0: object

    def __post_init__(self) -> None:
        if self.s0 not in self.states:
            raise ValueError("s0 outside S")
        if self.theta0 not in self.thetas:
            raise ValueError("theta0 outside Theta")
        T = dict(self.transition)
        for s in self.states:
            for th in self.thetas:
                for a in self.actions:
                    dist = T.get((s, th, a))
                    if dist is None:
                        raise ValueError(f"T undefined at {(s, th, a)}")
                    if sum(p for _, p in dist) != Fraction(1):
                        raise ValueError(f"T({s},{th},{a}) is not a distribution")
                    for (s2, th2), p in dist:
                        if s2 not in self.states or th2 not in self.thetas:
                            raise ValueError("T leaves the index sets")
                        if p < 0:
                            raise ValueError("negative transition weight")
        R = dict(self.reward)
        for th in self.thetas:
            for s in self.states:
                for a in self.actions:
                    for s2 in self.states:
                        if (th, s, a, s2) not in R:
                            raise ValueError(f"R undefined at {(th, s, a, s2)}")

    # -- readers ----------------------------------------------------------

    def T(self, s, theta, a) -> tuple:
        return dict(self.transition)[(s, theta, a)]

    def R(self, theta, s, a, s2) -> Fraction:
        return dict(self.reward)[(theta, s, a, s2)]


def build(states: Sequence, thetas: Sequence, actions: Sequence,
          T: Callable, R: Callable, s0, theta0) -> DRMDP:
    """Build a `DRMDP` from callables, freezing them into tables.

    `T(s, theta, a)` returns either a single `(s', theta')` pair — read as the
    point mass on it — or an iterable of `((s', theta'), weight)` pairs.
    `R(theta, s, a, s')` returns anything `Fraction` accepts.
    """
    trans = []
    for s in states:
        for th in thetas:
            for a in actions:
                out = T(s, th, a)
                if isinstance(out, tuple) and len(out) == 2 and not isinstance(out[0], tuple):
                    dist = (((out[0], out[1]), Fraction(1)),)
                else:
                    dist = tuple((tuple(k), Fraction(p)) for k, p in out)
                dist = tuple(sorted(dist, key=lambda kv: _key(kv[0])))
                trans.append(((s, th, a), dist))
    rew = []
    for th in thetas:
        for s in states:
            for a in actions:
                for s2 in states:
                    rew.append(((th, s, a, s2), Fraction(R(th, s, a, s2))))
    return DRMDP(tuple(states), tuple(thetas), tuple(actions),
                 tuple(sorted(trans, key=lambda kv: _key(kv[0]))),
                 tuple(sorted(rew, key=lambda kv: _key(kv[0]))),
                 s0, theta0)


# ------------------------------------------------------------------ relabel


def relabel(m: DRMDP, smap: Mapping, thmap: Mapping, amap: Mapping) -> DRMDP:
    """Rename the three alphabets. The only operation that touches names.

    An isomorphism of DR-MDPs is exactly a triple of bijections making this the
    identity, which is what `Q_DR(bob) == relabel(Q_DR(diana), ...)` asserts.
    """
    S = tuple(smap[s] for s in m.states)
    Th = tuple(thmap[t] for t in m.thetas)
    A = tuple(amap[a] for a in m.actions)
    if len(set(S)) != len(S) or len(set(Th)) != len(Th) or len(set(A)) != len(A):
        raise ValueError("relabelling is not injective")
    trans = tuple(sorted(
        (((smap[s], thmap[th], amap[a]),
          tuple(sorted((((smap[s2], thmap[th2]), p) for (s2, th2), p in dist),
                       key=lambda kv: _key(kv[0]))))
         for (s, th, a), dist in m.transition),
        key=lambda kv: _key(kv[0])))
    rew = tuple(sorted(
        (((thmap[th], smap[s], amap[a], smap[s2]), v)
         for (th, s, a, s2), v in m.reward),
        key=lambda kv: _key(kv[0])))
    return DRMDP(S, Th, A, trans, rew, smap[m.s0], thmap[m.theta0])


def canonical(m: DRMDP, order_s: Sequence = None, order_th: Sequence = None,
              order_a: Sequence = None) -> DRMDP:
    """Relabel onto the neutral alphabet `s0..`, `th0..`, `a0..`.

    The orders are the caller's isomorphism candidate. Two DR-MDPs are
    isomorphic under the supplied orders exactly when their canonical forms are
    equal, and that equality is what the projection tests assert.
    """
    S = list(order_s if order_s is not None else m.states)
    Th = list(order_th if order_th is not None else m.thetas)
    A = list(order_a if order_a is not None else m.actions)
    if sorted(map(_key, S)) != sorted(map(_key, m.states)):
        raise ValueError("state order is not a permutation of S")
    if sorted(map(_key, Th)) != sorted(map(_key, m.thetas)):
        raise ValueError("theta order is not a permutation of Theta")
    if sorted(map(_key, A)) != sorted(map(_key, m.actions)):
        raise ValueError("action order is not a permutation of A")
    return relabel(m,
                   {s: f"s{i}" for i, s in enumerate(S)},
                   {t: f"th{i}" for i, t in enumerate(Th)},
                   {a: f"a{i}" for i, a in enumerate(A)})


# -------------------------------------------------------- policies and runs


def reachable_points(m: DRMDP, H: int) -> tuple:
    """`(s, theta, t)` triples reachable at time `t` under some action sequence.

    Decision points off this set are unreachable, so policies differing only
    there are the same policy. Enumeration runs over this set and nothing else.
    """
    layer = {(m.s0, m.theta0)}
    out = []
    for t in range(H):
        out.extend(sorted(((s, th, t) for s, th in layer), key=_key))
        nxt = set()
        for s, th in layer:
            for a in m.actions:
                for (s2, th2), p in m.T(s, th, a):
                    if p:
                        nxt.add((s2, th2))
        layer = nxt
    return tuple(out)


def policies(m: DRMDP, H: int, cap: int = 200000) -> list:
    """Every deterministic policy `pi(s, theta, t)` over the reachable points.

    Exhaustive and exact. `cap` is a budget, not an approximation: exceeding it
    raises rather than sampling, because a sampled maximum is not a maximum.
    """
    points = reachable_points(m, H)
    total = len(m.actions) ** len(points)
    if total > cap:
        raise ValueError(f"{total} policies exceeds the cap {cap}")
    out = [dict()]
    for pt in points:
        out = [{**pol, pt: a} for pol in out for a in m.actions]
    return out


def noop_policy(m: DRMDP, H: int, a_noop) -> dict:
    return {pt: a_noop for pt in reachable_points(m, H)}


def rollouts(m: DRMDP, policy: Mapping, H: int) -> tuple:
    """Every trajectory with positive probability, with its exact probability.

    A trajectory is `((s_t, theta_t, a_t, s_{t+1}, theta_{t+1}))_{t<H}`, which
    is the source's `xi`.
    """
    runs = [(Fraction(1), (m.s0, m.theta0), ())]
    for t in range(H):
        nxt = []
        for p, (s, th), traj in runs:
            a = policy[(s, th, t)]
            for (s2, th2), q in m.T(s, th, a):
                if q:
                    nxt.append((p * q, (s2, th2), traj + ((s, th, a, s2, th2),)))
        runs = nxt
    return tuple((p, traj) for p, _, traj in runs)


#: The two readings of Definition 5's `xi^theta`. The definition writes
#: `(theta_0, ..., theta_{H-1})`, which is `"H-1"`. A trajectory of Definition 4
#: also carries `theta_H`, and including it is `"H"`. The two are not
#: interchangeable: under `"H-1"` an influence taken at the last step is
#: invisible to the constrained objective, and `table4.py` reports the one cell
#: of Table 4 where that difference decides the answer.
THETA_INDEX_READINGS = ("H-1", "H")


def theta_trajectory_law(m: DRMDP, policy: Mapping, H: int,
                         upto: str = "H-1") -> tuple:
    """`P(xi^theta | pi)`, under the named reading of Definition 5's index range."""
    if upto not in THETA_INDEX_READINGS:
        raise ValueError(upto)
    law: dict = {}
    for p, traj in rollouts(m, policy, H):
        key = tuple(step[1] for step in traj)
        if upto == "H":
            key = key + (traj[-1][4],)
        law[key] = law.get(key, Fraction(0)) + p
    return tuple(sorted(((k, v) for k, v in law.items() if v),
                        key=lambda kv: _key(kv[0])))
