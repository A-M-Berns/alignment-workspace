"""The auction construction of Oesterheld–`Demski`–Conitzer Theorem 1, over blocks.

A hypothesis proposes, at macro-round `k` from the actual history, a pair
`(controller, promise)`: an `m_k`-step contingent controller and a per-step promise in
[0, 1] about the block average obtained if that controller is executed through the gate
from this history.  The learner runs a first-price sealed-bid auction.

Weighted (`weight = "duration"`): wealth is in total-reward units; the per-step bid is
`min(promise, W / m_k)`; the winner pays `m_k · bid` and receives `m_k · G_k`.
Unweighted (`weight = "block"`): the paper's construction applied verbatim to the macro
sequence, one block = one round, bid `min(promise, W)`, pays `bid`, receives `G_k`.
With every `m_k = 1` and controllers that are single actions, both are the paper's
one-step construction.

Ties go to the lowest index.  Wealth starts at 0; allowance `A(k, i)` is paid to every
hypothesis every round, before the auction, so a hypothesis is active from the first
round with positive allowance.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as Q

from src.envs import execute


@dataclass
class Hyp:
    name: str
    propose: object            # ctx -> (controller, promise)
    wealth: Q = Q(0)
    wins: list = field(default_factory=list)      # macro-rounds won
    record: Q = Q(0)                               # Σ_{tested} w_k (G_k − promise_k)
    rejections: list = field(default_factory=list)  # rounds with promise > α^e
    own: list = field(default_factory=list)       # (state, m, G) on own tests


@dataclass
class Round:
    k: int
    t: int
    state: object
    m: int
    winner: int
    alpha_e: Q
    G: Q
    bids: tuple
    promises: tuple
    refused: int = 0


def run_auction(env, hyps, schedule, allowance, K, weight="duration", start=None,
                t0=0, gated=True, reset=None):
    """Run K macro-rounds.  Returns the list of `Round`s; hypotheses are mutated.

    `schedule(k)` = block length m_k (k from 1);  `allowance(k, i)` with i the
    hypothesis index from 1;  `reset(state)` optionally maps the state at a block
    boundary (episodic fixtures)."""
    s = env.start if start is None else start
    t = t0
    rounds = []
    history = []
    for k in range(1, K + 1):
        m = schedule(k)
        w = Q(m) if weight == "duration" else Q(1)
        for i, h in enumerate(hyps, 1):
            h.wealth += allowance(k, i)
        ctx = {"state": s, "t": t, "k": k, "m": m, "history": history}
        proposals = []
        bids = []
        for h in hyps:
            ctrl, e = h.propose(dict(ctx, own=h.own))
            e = Q(e)
            assert 0 <= e <= 1
            proposals.append((ctrl, e))
            bids.append(min(e, h.wealth / w))
        star = max(range(len(hyps)), key=lambda i: (bids[i], -i))
        alpha_e = bids[star]
        ctrl, e_star = proposals[star]
        if hasattr(env, "block"):
            G, s2, refused = env.block(s, t, ctrl, m)
            t2 = t + m
        else:
            G, s2, t2, traj, refused = execute(env, s, t, ctrl, m, gated)
        win = hyps[star]
        win.wealth += w * (G - alpha_e)
        win.wins.append(k)
        win.record += w * (G - e_star)
        win.own.append((s, m, G))
        for i, h in enumerate(hyps):
            if proposals[i][1] > alpha_e:
                h.rejections.append(k)
        rounds.append(Round(k, t, s, m, star, alpha_e, G, tuple(bids),
                            tuple(p[1] for p in proposals), refused))
        history.append((k, s, t, m, star, G))
        s, t = s2, t2
        if reset is not None:
            s = reset(s)
    return rounds


# --- accounting -----------------------------------------------------------------------

def primitive_average(rounds):
    """Σ m_k G_k / Σ m_k — the primitive-time average reward."""
    S = sum(r.m for r in rounds)
    return sum(r.m * r.G for r in rounds) / S


def macro_average(rounds):
    return sum(r.G for r in rounds) / len(rounds)


def weighted_overestimation(rounds):
    """Σ m_k (α^e_k − G_k) / Σ m_k."""
    S = sum(r.m for r in rounds)
    return sum(r.m * (r.alpha_e - r.G) for r in rounds) / S


def macro_overestimation(rounds):
    return sum(r.alpha_e - r.G for r in rounds) / len(rounds)


def total_allowance(allowance, K, n):
    return sum(allowance(k, i) for k in range(1, K + 1) for i in range(1, n + 1))


def cumulative_allowance(allowance, K, i):
    return sum(allowance(k, i) for k in range(1, K + 1))


def wealth_identity_holds(hyps, rounds, allowance, weight="duration"):
    """Σ_i W_i(K) = Σ_i Σ_{k≤K} A(k, i) + Σ_k w_k (G_k − α^e_k), exactly."""
    K = len(rounds)
    lhs = sum(h.wealth for h in hyps)
    rhs = total_allowance(allowance, K, len(hyps)) + sum(
        (Q(r.m) if weight == "duration" else Q(1)) * (r.G - r.alpha_e) for r in rounds)
    return lhs == rhs


# --- standard hypotheses -------------------------------------------------------------

def const_hyp(name, controller, promise):
    """A context-free hypothesis: always the same controller and promise."""
    return Hyp(name, lambda ctx: (controller, Q(promise)))


def contextual_hyp(name, controller, promise_of):
    """`promise_of(state, m, t)` — a contextual promise from the actual history."""
    return Hyp(name, lambda ctx: (controller, Q(promise_of(ctx["state"], ctx["m"], ctx["t"]))))


def sound_hyp(name, env, controller):
    """Promises exactly the gated block value from the current state: sound by
    construction (it computes the value it promises)."""
    def promise_of(s, m, t):
        return execute(env, s, t, controller, m)[0]
    return contextual_hyp(name, controller, promise_of)


def learning_hyp(name, controller, margin, prior=Q(0)):
    """Promises, per state, the minimum block average observed on its own past tests
    from that state, less a margin (fixture O); `prior` before any test."""
    def propose(ctx):
        seen = [G for (s, m, G) in ctx["own"] if s == ctx["state"]]
        if not seen:
            return controller, prior
        return controller, max(Q(0), min(seen) - margin)
    return Hyp(name, propose)


def waiting_liar(name, controller, wake, n):
    """Promises 0 until macro-round `wake`, then 1 for the next `n` rounds, then 0
    (fixture I).  Its controller is whatever it is told; its promises are lies."""
    def propose(ctx):
        k = ctx["k"]
        return controller, Q(1) if wake <= k < wake + n else Q(0)
    return Hyp(name, propose)


# --- allowances ----------------------------------------------------------------------

def paper_allowance(k, i):
    """A(n, i) = n^{-1} i^{-2} for i < n, else 0 — the paper's finite-support example."""
    return Q(1, k * i * i) if i < k else Q(0)


def paper_allowance_all(k, i):
    return Q(1, k * i * i)


def replenishing_allowance(schedule, support):
    """a_k = (M_k − M_{k−1}) + 1/k for i ≤ support(k), with M_k the running maximum of
    the schedule.  Satisfies A_i(k) − m_k → ∞ for every i (WEIGHTED_BRIA.md §4)."""
    def A(k, i):
        if i > support(k):
            return Q(0)
        M = max(schedule(j) for j in range(1, k + 1))
        Mprev = max(schedule(j) for j in range(1, k)) if k > 1 else 0
        return Q(M - Mprev) + Q(1, k)
    return A


def prefix_allowance(schedule):
    """The uniform online constructor of the pressure pass (WEIGHTED_BRIA.md §4).

    Support `s(k) = ⌊√(S_k / M_k)⌋` and allowance `a_k = (M_k − M_{k−1}) + 1/k` for
    `i ≤ s(k)`, both computed from the observed prefix `(S_k, M_k)` alone.  Needs no
    modulus of convergence: under `m_K / S_K → 0` it satisfies capital adequacy and
    `𝒜_K ≤ 2 √(S_K M_K) + √S_K (1 + ln K)`."""
    import math
    cache = {}

    def prefix(k):
        if k not in cache:
            S, M = 0, 0
            for j in range(1, k + 1):
                m = schedule(j)
                S += m
                M = max(M, m)
                cache[j] = (S, M)
        return cache[k]

    def A(k, i):
        S, M = prefix(k)
        if i > math.isqrt(S // M):
            return Q(0)
        Mprev = prefix(k - 1)[1] if k > 1 else 0
        return Q(M - Mprev) + Q(1, k)
    A.support = lambda k: math.isqrt(prefix(k)[0] // prefix(k)[1])
    A.prefix = prefix
    return A


# --- execution treatments ------------------------------------------------------------
#
# A hypothesis promises the return of its controller under a declared *treatment*: an
# advisor-side execution protocol the wrapper can run inside the block.  The whole-block
# lease is the identity treatment; `prefix_then(j, tail)` hands control to `tail` after
# `j` steps.  Data generated under a different treatment is not a test of the promise.

def lease(controller):
    return controller


def prefix_then(j, tail):
    def treat(controller):
        def c(s, i, t):
            return controller(s, i, t) if i < j else tail(s, i, t)
        c.treatment = ("prefix_then", j, tail)
        return c
    return treat


def valid_test(promised, executed):
    """Data counts against a promise only if generated by the promised (controller,
    treatment) pair."""
    return promised == executed
