"""Theorem A: opportunity-adaptive wide-range regret.

No legitimacy vocabulary appears in this module. It is an online-learning kernel
and nothing else.

```text
per occasion t
    menu        A_t, a finite set of actions
    choice      p_t, a distribution on A_t
    loss        l_t : A_t -> [0,1], full information, revealed after
    selector    I(t) in [0,1], predictable: a function of the history before t
    repair      f_t : A_t -> A_t, history-dependent, predictable
```

Comparative advantage of the pair `(I, f)` over the horizon:

```text
Adv_T(I,f) = sum_t I(t) * ( <p_t, l_t> - <p_t M_f, l_t> )
```

which is the round's *repair regret*: what the process gave up by not applying
`f` on the occasions `I` selects.

## What the bound adapts to, derived rather than assumed

The construction is Khot and Ponnuswami's reduction of wide-range regret to
external regret, run with AdaNormalHedge as the black box. The reduction feeds
the black box

```text
l'_t(I,f) = I(t) * p_t^T (M_f - 1) l_t          in [-1, +1]
```

and Khot-Ponnuswami's equation (5) proves `sum_{(I,f)} q_t(I,f) l'_t(I,f) = 0`:
the inner player's own loss is **identically zero** every round. AdaNormalHedge's
adaptive quantity is the cumulative magnitude of instantaneous regret,
`C_T(i) = sum_t |lhat_t - l_t(i)|`, so here it collapses to

```text
C_T(I,f) = sum_t I(t) * | p_t^T (M_f - 1) l_t |
```

That is the effective mass this kernel adapts to. It is **not**
`sum_t I(t) 1[f != id on supp(p_t)]` and **not**
`sum_t I(t) sum_a p_t(a) 1[f(a) != a]`. Those two count occasions or moved mass;
this one weighs each occasion by how much the repair would actually have changed
the incurred loss. A repair that moves `1e-12` of the probability mass
contributes `~1e-12` to `C_T`, and contributes the same to `Adv_T` -- so the
bound is small exactly when the thing it bounds is small, which is what makes it
non-vacuous rather than merely flattering.

Since losses are in `[0,1]`, `|p_t^T(M_f - 1)l_t| <= 1` and therefore

```text
C_T(I,f) <= W_T(I) := sum_t I(t)
```

so opportunity-mass adaptivity follows as a corollary, and is strictly weaker.

## Status of each ingredient

```text
imported   Khot-Ponnuswami Thm 3, the reduction and its equations (3),(4),(5)
imported   AdaNormalHedge Thm 1 and Thm 3, the potential and the C_T bound
re-derived the two composed: ANH is stated for losses in [0,1], the reduction
           produces [-1,+1]. What the drifting-game analysis actually needs is
           |r_t(i)| <= 1, which holds here because lhat_t = 0 and |l'_t| <= 1.
           This module checks that numerically; it is not an imported theorem.
```
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional, Sequence


# ------------------------------------------------------------ AdaNormalHedge


def _phi(r: float, c: float) -> float:
    if c <= 0:
        return 1.0
    return math.exp(max(r, 0.0) ** 2 / (3.0 * c))


def weight(r: float, c: float) -> float:
    """`w(R,C) = (Phi(R+1,C+1) - Phi(R-1,C+1)) / 2`, Luo-Schapire §3."""
    return 0.5 * (_phi(r + 1.0, c + 1.0) - _phi(r - 1.0, c + 1.0))


@dataclass
class AdaNormalHedge:
    """Parameter-free, anytime, prior-weighted, confidence-rated.

    Experts may be introduced at any time: one never seen starts at `R=0, C=0`,
    which is what makes a countable comparator set admissible. No horizon is
    used anywhere.
    """

    prior: Callable[[object], float] = lambda i: 1.0
    R: dict = field(default_factory=dict)
    C: dict = field(default_factory=dict)

    def _seen(self, i) -> None:
        self.R.setdefault(i, 0.0)
        self.C.setdefault(i, 0.0)

    def distribution(self, experts: Sequence, conf: Optional[Mapping] = None) -> dict:
        """`p_i ∝ q_i * I_i * w(R_i, C_i)`. Uniform when every weight vanishes."""
        raw = {}
        for i in experts:
            self._seen(i)
            c = 1.0 if conf is None else float(conf.get(i, 1.0))
            raw[i] = self.prior(i) * c * weight(self.R[i], self.C[i])
        total = sum(raw.values())
        if total <= 0:
            live = [i for i in experts
                    if conf is None or float(conf.get(i, 1.0)) > 0]
            if not live:
                return {i: 0.0 for i in experts}
            return {i: (1.0 / len(live) if i in live else 0.0) for i in experts}
        return {i: v / total for i, v in raw.items()}

    def update(self, inst: Mapping) -> None:
        """`r_t(i)` supplied already confidence-weighted, as Luo-Schapire §4."""
        for i, r in inst.items():
            self._seen(i)
            self.R[i] += r
            self.C[i] += abs(r)

    def bound(self, i, n_seen: int) -> float:
        """Theorem 1 with a point competitor: `sqrt(3 C (ln(1/q) + ln B + ...))`."""
        self._seen(i)
        b = 1.0 + 1.5 * (1.0 + math.log(1.0 + self.C[i]))
        ent = math.log(1.0 / max(self.prior(i), 1e-300))
        return math.sqrt(3.0 * self.C[i]
                         * (ent + math.log(b) + math.log(1.0 + math.log(
                             max(n_seen, 2)))))


# ------------------------------------------------- the wide-range reduction


@dataclass(frozen=True)
class Occasion:
    """One learning occasion. `loss` is revealed only after `p_t` is committed."""

    menu: tuple
    loss: Mapping
    tag: object = None


@dataclass(frozen=True)
class Comparator:
    """A `(selector, repair)` pair: when to compare, and against what.

    `select` and `repair` are **predictable**: both are given the prefix and the
    menu, never the current loss. That is what stops the comparator from being a
    hindsight oracle, and it is checked in the tests.
    """

    name: str
    select: Callable          # (prefix, occasion) -> [0,1]
    repair: Callable          # (prefix, occasion, action) -> action


def _apply(p: Mapping, occ: Occasion, prefix, comp: Comparator) -> dict:
    out = {a: 0.0 for a in occ.menu}
    for a, m in p.items():
        out[comp.repair(prefix, occ, a)] += m
    return out


def _fixed_point(occ: Occasion, comps: Sequence[Comparator], prefix,
                 q: Mapping, sel: Mapping, iters: int = 400) -> dict:
    """Khot-Ponnuswami equation (1): the stationary distribution of the mixture.

    `p^T = p^T ( sum I(t) q(I,f) M_f / sum I(t) q(I,f) )`. Solved by power
    iteration, which converges because the matrix is stochastic. When every
    selector is zero the equation is vacuous and any `p` is admissible; the
    reduction then contributes nothing that round.
    """
    wts = {c.name: sel[c.name] * q[c.name] for c in comps}
    z = sum(wts.values())
    n = len(occ.menu)
    p = {a: 1.0 / n for a in occ.menu}
    if z <= 0:
        return p
    for _ in range(iters):
        nxt = {a: 0.0 for a in occ.menu}
        for c in comps:
            w = wts[c.name] / z
            if w <= 0:
                continue
            moved = _apply(p, occ, prefix, c)
            for a, m in moved.items():
                nxt[a] += w * m
        shift = sum(abs(nxt[a] - p[a]) for a in occ.menu)
        p = nxt
        if shift < 1e-14:
            break
    return p


@dataclass
class Learner:
    """The composed algorithm. One expert per comparator, as Khot-Ponnuswami."""

    comparators: tuple
    prior: Callable[[object], float] = None
    inner: AdaNormalHedge = None
    prefix: list = field(default_factory=list)
    adv: dict = field(default_factory=dict)          # Adv_T(I,f)
    mass: dict = field(default_factory=dict)         # C_T(I,f), the effective mass
    opportunity: dict = field(default_factory=dict)  # W_T(I) = sum_t I(t)
    plays: list = field(default_factory=list)

    def __post_init__(self):
        if self.prior is None:
            n = len(self.comparators)
            self.prior = lambda i, n=n: 1.0 / n
        if self.inner is None:
            self.inner = AdaNormalHedge(prior=self.prior)
        for c in self.comparators:
            self.adv.setdefault(c.name, 0.0)
            self.mass.setdefault(c.name, 0.0)
            self.opportunity.setdefault(c.name, 0.0)

    def act(self, occ: Occasion) -> dict:
        sel = {c.name: float(c.select(self.prefix, occ)) for c in self.comparators}
        q = self.inner.distribution([c.name for c in self.comparators])
        return _fixed_point(occ, self.comparators, self.prefix, q, sel)

    def observe(self, occ: Occasion, p: dict) -> dict:
        """Reveal the loss, score every comparator, update. Returns the round's
        instantaneous advantages."""
        own = sum(p[a] * occ.loss[a] for a in occ.menu)
        inst = {}
        for c in self.comparators:
            i = float(c.select(self.prefix, occ))
            moved = _apply(p, occ, self.prefix, c)
            theirs = sum(moved[a] * occ.loss[a] for a in occ.menu)
            gap = own - theirs                       # p^T (1 - M_f) l
            inst[c.name] = i * gap
            self.adv[c.name] += i * gap
            self.mass[c.name] += abs(i * gap)
            self.opportunity[c.name] += i
        # Khot-Ponnuswami feed the black box l'_t(I,f) = I(t) p^T(M_f - 1)l,
        # which is -inst; their (5) makes the inner player's own loss zero, so
        # AdaNormalHedge's instantaneous regret is r_t = 0 - l'_t = +inst.
        self.inner.update(inst)
        self.plays.append((occ, dict(p), own, dict(inst)))
        self.prefix.append((occ, dict(p), dict(occ.loss)))
        return inst

    def run(self, occasions: Sequence[Occasion]) -> None:
        for occ in occasions:
            self.observe(occ, self.act(occ))

    # ------------------------------------------------------------- reporting

    def bound(self, name: str) -> float:
        return self.inner.bound(name, max(len(self.comparators), 2))

    def report(self) -> dict:
        return {c.name: {"adv": self.adv[c.name],
                         "mass": self.mass[c.name],
                         "opportunity": self.opportunity[c.name],
                         "bound": self.bound(c.name)}
                for c in self.comparators}


def thm_a_repair_regret(learner: Learner) -> tuple:
    """**Theorem A.** For every comparator `(I,f)` in the class,

    ```text
    Adv_T(I,f) <= B_T(I,f) = sqrt( 3 C_T(I,f) (ln(1/q(I,f)) + ln B + lnln n) )
    C_T(I,f)   = sum_t I(t) | p_t^T (M_f - 1) l_t |  <=  W_T(I) = sum_t I(t)
    ```

    anytime, with no horizon and no tuning. Returns the comparators on which the
    realized advantage exceeds its bound -- empty is the claim holding.

    *Proof.* Khot-Ponnuswami Theorem 3 gives `Adv_T(I,f) <= R_ext(T,|S|)` where
    `R_ext` is the external regret of the inner algorithm on the fed-back losses
    `l'_t(I,f) = I(t) p_t^T(M_f - 1)l_t`; their equation (3) identifies `l'` as
    exactly the per-round decrement of `Adv`, and (5) shows the inner player's
    own loss is zero each round. Instantiating the inner algorithm with
    AdaNormalHedge and reading its Theorem 1 with `lhat_t = 0` gives the stated
    `C_T`. ∎

    The composition step is **re-derived, not imported**: the published
    AdaNormalHedge theorems assume losses in `[0,1]` while the reduction emits
    `[-1,+1]`. What the analysis uses is `|r_t(i)| <= 1`, which holds here. This
    function is the numerical check of that step.
    """
    return tuple(c.name for c in learner.comparators
                 if learner.adv[c.name] > learner.bound(c.name) + 1e-9)


def cor_opportunity_adaptive(learner: Learner) -> tuple:
    """**Corollary.** The same with `W_T(I)` in place of `C_T(I,f)`.

    Weaker, and the form a consumer usually wants, because `W` is the mass of
    occasions the selector designated and is knowable in advance of any loss.
    """
    bad = []
    for c in learner.comparators:
        w = learner.opportunity[c.name]
        b = math.sqrt(3.0 * w * (math.log(1.0 / max(learner.prior(c.name), 1e-300))
                                 + math.log(4.0) + 1.0))
        if learner.adv[c.name] > b + 1e-9:
            bad.append(c.name)
    return tuple(bad)


def predictability_violations(learner: Learner, occasions: Sequence[Occasion],
                              probe: Callable) -> tuple:
    """Comparators whose selector or repair reads the current loss.

    Re-runs each decision with the loss replaced by `probe` and reports any
    comparator that answers differently. A hindsight selector breaks Theorem A,
    so this is a hypothesis check rather than a stylistic one.
    """
    bad = []
    prefix = []
    for occ in occasions:
        other = Occasion(occ.menu, probe(occ), occ.tag)
        for c in learner.comparators:
            if float(c.select(prefix, occ)) != float(c.select(prefix, other)):
                bad.append((c.name, "select", occ.tag))
            for a in occ.menu:
                if c.repair(prefix, occ, a) != c.repair(prefix, other, a):
                    bad.append((c.name, "repair", occ.tag))
                    break
        prefix.append((occ, {a: 1.0 / len(occ.menu) for a in occ.menu},
                       dict(occ.loss)))
    return tuple(bad)
