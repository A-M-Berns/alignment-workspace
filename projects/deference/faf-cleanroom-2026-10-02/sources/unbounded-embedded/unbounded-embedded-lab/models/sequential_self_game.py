#!/usr/bin/env python3
"""Sequential self-game: the finite shadow of Cole Wyeth's revised Theorem 1
(delta-self-trust => epsilon-optimality).  Exact rational arithmetic throughout.

Model (see sequential-self-game.md section 1):
  * finite decision tree; histories are tuples of (a, e) pairs; a history is
    terminal iff tree.actions(h) == [] or len(h) == T;
  * rewards r(h) >= 0 attached to every non-empty history, discount gamma^t
    (absolute), normalised so that every path return lies in [0, 1];
  * hypotheses = (action kernel, percept kernel) pairs; the SELF hypothesis
    has action kernel pi (the agent's policy) and percept kernel equal to the
    non-self mixture's percept conditional (audit fact F1);
  * prior: self gets 1 - delta, the others get weights summing to delta.
Conventions: continuous extension at xi-null nodes (xi(a|h) := pi(a|h) there),
and, where the non-self mass after (h, a) is zero, the self percept kernel
falls back to the prior-weighted non-self percept mixture at (h, a).
"""
from fractions import Fraction as F
import itertools
import random
import sys

# ----------------------------------------------------------------------------
# (i) tree + hypothesis class
# ----------------------------------------------------------------------------


class Tree:
    """actions(h) -> list of actions ([] = terminal); percepts(h, a) -> list;
    reward(h) for non-empty h; T = max depth; gamma = discount base."""

    def __init__(self, actions, percepts, reward, T, gamma=F(1)):
        self._actions, self._percepts, self._reward = actions, percepts, reward
        self.T, self.gamma = T, F(gamma)
        self.nodes = []          # all histories, breadth-first
        self.nonterminal = []    # decision nodes
        self._build()

    def actions(self, h):
        return [] if len(h) >= self.T else list(self._actions(h))

    def percepts(self, h, a):
        return list(self._percepts(h, a))

    def reward(self, h):
        return F(self._reward(h))

    def disc(self, h):
        """discount weight of the reward received on arriving at h (depth t)."""
        return self.gamma ** (len(h) - 1)

    def _build(self):
        frontier = [()]
        while frontier:
            nxt = []
            for h in frontier:
                self.nodes.append(h)
                acts = self.actions(h)
                if acts:
                    self.nonterminal.append(h)
                for a in acts:
                    for e in self.percepts(h, a):
                        nxt.append(h + ((a, e),))
            frontier = nxt

    def max_return(self, h=()):
        """max over paths of the (discounted) return from h; used to normalise."""
        acts = self.actions(h)
        if not acts:
            return F(0)
        return max(max(self.disc(h + ((a, e),)) * self.reward(h + ((a, e),))
                       + self.max_return(h + ((a, e),))
                       for e in self.percepts(h, a)) for a in acts)


class Hyp:
    """A fixed (non-self) hypothesis: act(h) -> {a: prob}, env(h, a) -> {e: prob}."""

    def __init__(self, name, act, env):
        self.name, self.act, self.env = name, act, env


def joint_prob(tree, hyp, h):
    """hyp's joint probability of history h (actions and percepts)."""
    p, pre = F(1), ()
    for (a, e) in h:
        p *= F(hyp.act(pre).get(a, 0)) * F(hyp.env(pre, a).get(e, 0))
        if p == 0:
            return F(0)
        pre = pre + ((a, e),)
    return p


def det_policy(table):
    """table: {h: a} -> policy {h: {a: 1}}."""
    return {h: {a: F(1)} for h, a in table.items()}

# ----------------------------------------------------------------------------
# (ii) given pi: xi, posteriors, Q_xi, V^pi, V^*, fixed-pointness, trust bound
# ----------------------------------------------------------------------------


class Analysis:
    """All quantities of the self-game at a given policy pi (dict h -> {a: prob})."""

    def __init__(self, tree, hyps, weights, delta, pi):
        assert sum(weights) == delta, "non-self weights must sum to delta"
        self.tree, self.hyps, self.weights, self.delta, self.pi = tree, hyps, weights, F(delta), pi
        self.nu_joint = {(i, h): joint_prob(tree, nu, h) for i, nu in enumerate(hyps) for h in tree.nodes}
        self.xi_ns = {h: sum(weights[i] * self.nu_joint[(i, h)] for i in range(len(hyps))) for h in tree.nodes}
        self._envS = {}
        self.xi_S = {}
        for h in tree.nodes:
            p, pre = F(1), ()
            for (a, e) in h:
                p *= pi[pre].get(a, F(0)) * self.envS(pre, a).get(e, F(0))
                pre = pre + ((a, e),)
            self.xi_S[h] = p
        self.xi = {h: (1 - self.delta) * self.xi_S[h] + self.xi_ns[h] for h in tree.nodes}
        self.w = {h: ((1 - self.delta) * self.xi_S[h] / self.xi[h]) if self.xi[h] > 0 else F(1) for h in tree.nodes}
        self._values()

    def envS(self, h, a):
        """xi's percept conditional at (h, a) = the non-self mixture's (F1); fallback at non-self-null (h, a)."""
        key = (h, a)
        if key in self._envS:
            return self._envS[key]
        ha_mass = sum(self.weights[i] * self.nu_joint[(i, h)] * F(nu.act(h).get(a, 0)) for i, nu in enumerate(self.hyps))
        out = {}
        for e in self.tree.percepts(h, a):
            if ha_mass > 0:
                num = sum(self.weights[i] * self.nu_joint[(i, h)] * F(nu.act(h).get(a, 0)) * F(nu.env(h, a).get(e, 0))
                          for i, nu in enumerate(self.hyps))
                out[e] = num / ha_mass
            else:  # fallback: prior-weighted non-self percept mixture
                out[e] = sum(self.weights[i] * F(nu.env(h, a).get(e, 0)) for i, nu in enumerate(self.hyps)) / self.delta
        self._envS[key] = out
        return out

    def xi_act(self, h, a):
        """xi(a|h); continuous extension pi(a|h) at xi-null h."""
        if self.xi[h] > 0:
            return sum(self.xi[h + ((a, e),)] for e in self.tree.percepts(h, a)) / self.xi[h]
        return self.pi[h].get(a, F(0))

    def _values(self):
        t = self.tree
        self.Qpi, self.Vpi, self.Qstar, self.Vstar, self.pistar = {}, {}, {}, {}, {}
        self.Qxi, self.Vxi, self.Qnu = {}, {}, {}
        for h in reversed(t.nodes):
            acts = t.actions(h)
            if not acts:
                self.Vpi[h] = self.Vstar[h] = self.Vxi[h] = F(0)
                for i in range(len(self.hyps)):
                    self.Qnu[(i, h)] = F(0)
                continue
            for a in acts:
                env = self.envS(h, a)
                kids = [(h + ((a, e),), env[e]) for e in t.percepts(h, a)]
                imm = {c: t.disc(c) * t.reward(c) for c, _ in kids}
                self.Qpi[(h, a)] = sum(p * (imm[c] + self.Vpi[c]) for c, p in kids)
                self.Qstar[(h, a)] = sum(p * (imm[c] + self.Vstar[c]) for c, p in kids)
                self.Qxi[(h, a)] = sum(p * (imm[c] + self.Vxi[c]) for c, p in kids)
                for i, nu in enumerate(self.hyps):   # hypothesis-internal values (for Lemma A)
                    envn = nu.env(h, a)
                    self.Qnu[(i, h, a)] = sum(F(envn.get(e, 0)) * (imm[h + ((a, e),)] + self.Qnu[(i, h + ((a, e),))])
                                              for e in t.percepts(h, a))
            self.Vpi[h] = sum(self.pi[h].get(a, F(0)) * self.Qpi[(h, a)] for a in acts)
            self.Vstar[h] = max(self.Qstar[(h, a)] for a in acts)
            self.pistar[h] = [a for a in acts if self.Qstar[(h, a)] == self.Vstar[h]][0]   # first argmax (canonical)
            self.Vxi[h] = sum(self.xi_act(h, a) * self.Qxi[(h, a)] for a in acts)
            for i, nu in enumerate(self.hyps):
                self.Qnu[(i, h)] = sum(F(nu.act(h).get(a, 0)) * self.Qnu[(i, h, a)] for a in acts)

    # --- per-node predicates -------------------------------------------------
    def argmax(self, h):
        m = max(self.Qxi[(h, a)] for a in self.tree.actions(h))
        return [a for a in self.tree.actions(h) if self.Qxi[(h, a)] == m]

    def M(self, h):
        return max(self.Qxi[(h, a)] for a in self.tree.actions(h))

    def odds(self, h):
        """O_h = (1 - w_h) / w_h."""
        return (1 - self.w[h]) / self.w[h]

    def trust_bound(self, h):
        return self.M(h) >= self.w[h] * self.Vstar[h]

    def gap(self, h):
        return self.Vstar[h] - self.Vpi[h]

    def floor_sign(self, h):
        """sign of M(h) - w_h V^*(h): -1 reset, 0 equality, +1 argmax."""
        d = self.M(h) - self.w[h] * self.Vstar[h]
        return -1 if d < 0 else (1 if d > 0 else 0)

    def is_fixed_point(self):
        return all(set(a for a, p in self.pi[h].items() if p > 0) <= set(self.argmax(h)) for h in self.tree.nonterminal)

    def is_floored_fixed_point(self):
        for h in self.tree.nonterminal:
            supp = set(a for a, p in self.pi[h].items() if p > 0)
            s = self.floor_sign(h)
            ok = {-1: supp == {self.pistar[h]}, 1: supp <= set(self.argmax(h)),
                  0: supp <= set(self.argmax(h)) | {self.pistar[h]}}[s]
            if not ok:
                return False
        return True

# ----------------------------------------------------------------------------
# (iii) enumeration of pure fixed points; sink-or-swim exact solution
# ----------------------------------------------------------------------------


def pure_policies(tree, hyps, weights, delta, last_level_prune=True):
    """Yield every deterministic policy.  Last-level pruning: at depth T-1 the
    argmax of Q_xi does not depend on pi (it is the immediate expected reward),
    so only argmax actions there can appear in any fixed point (plain or floored:
    the floor's pi^* action at the last level is itself an argmax)."""
    nodes = tree.nonterminal
    choices = []
    if last_level_prune:
        probe = Analysis(tree, hyps, weights, delta, {h: {tree.actions(h)[0]: F(1)} for h in nodes})
    for h in nodes:
        if last_level_prune and all(not tree.actions(h + ((a, e),)) for a in tree.actions(h) for e in tree.percepts(h, a)):
            choices.append(probe.argmax(h))
        else:
            choices.append(tree.actions(h))
    for combo in itertools.product(*choices):
        yield det_policy(dict(zip(nodes, combo)))


def enumerate_fixed_points(tree, hyps, weights, delta, floored=False):
    out = []
    for pi in pure_policies(tree, hyps, weights, delta):
        an = Analysis(tree, hyps, weights, delta, pi)
        if (an.is_floored_fixed_point() if floored else an.is_fixed_point()):
            out.append(an)
    return out


def check_facts(an):
    """F1 (percepts never move the self-posterior), F2 (odds update by pi/xi_ns ratio),
    Lemma A (mixture decomposition of Q_xi) at every node with xi > 0."""
    t = an.tree
    for h in t.nonterminal:
        for a in t.actions(h):
            ha_xi = sum(an.xi[h + ((a, e),)] for e in t.percepts(h, a))
            for e in t.percepts(h, a):
                c = h + ((a, e),)
                if an.xi[c] > 0:
                    # F1: posterior after (h a e) equals posterior after (h a)
                    w_ha = (1 - an.delta) * an.xi_S[h] * an.pi[h].get(a, F(0)) / ha_xi
                    assert an.w[c] == w_ha, ("F1", h, a, e)
            if ha_xi > 0 and an.xi[h] > 0:
                # F2: odds(self | h a) = odds(self | h) * pi(a|h) / xi_ns(a|h)
                w_ha = (1 - an.delta) * an.xi_S[h] * an.pi[h].get(a, F(0)) / ha_xi
                ns_a = sum(an.weights[i] * an.nu_joint[(i, h)] * F(nu.act(h).get(a, 0)) for i, nu in enumerate(an.hyps))
                lhs = w_ha * ((1 - an.w[h]) * ns_a / an.xi_ns[h] if an.xi_ns[h] > 0 else F(0))
                rhs = (1 - w_ha) * an.w[h] * an.pi[h].get(a, F(0))
                assert lhs == rhs, ("F2", h, a)
                # Lemma A: xi(ha) Q_xi(h,a) = (1-delta) xi_S(ha) Q^pi(h,a) + sum_nu w_nu nu(ha) Q^nu(h,a)
                lhsA = ha_xi * an.Qxi[(h, a)]
                rhsA = (1 - an.delta) * an.xi_S[h] * an.pi[h].get(a, F(0)) * an.Qpi[(h, a)] + sum(
                    an.weights[i] * an.nu_joint[(i, h)] * F(nu.act(h).get(a, 0)) * an.Qnu[(i, h, a)]
                    for i, nu in enumerate(an.hyps))
                assert lhsA == rhsA, ("LemmaA", h, a)
                # Lemma A': the non-self conditional value is a policy value in the xi-environment, so <= Q^*
                ns_ha = sum(an.weights[i] * an.nu_joint[(i, h)] * F(nu.act(h).get(a, 0)) for i, nu in enumerate(an.hyps))
                if ns_ha > 0:
                    Qbar = sum(an.weights[i] * an.nu_joint[(i, h)] * F(nu.act(h).get(a, 0)) * an.Qnu[(i, h, a)]
                               for i, nu in enumerate(an.hyps)) / ns_ha
                    assert Qbar <= an.Qstar[(h, a)], ("LemmaA'", h, a)
    return True


# --- sink-or-swim -------------------------------------------------------------
ISL, WATER = (), (("jump", "-"),)


def sink_or_swim(b, c, delta, s):
    """Island: stay (reward c, terminal) / jump; water: swim (b) / sink (0)."""
    b, c, delta, s = F(b), F(c), F(delta), F(s)

    def actions(h):
        return ["stay", "jump"] if h == ISL else (["swim", "sink"] if h == WATER else [])

    def percepts(h, a):
        return ["-"]

    def reward(h):
        return {(("stay", "-"),): c, (("jump", "-"), ("swim", "-")): b}.get(h, F(0))

    tree = Tree(actions, percepts, reward, T=2)
    unit = {"-": F(1)}
    sinker = Hyp("sink", lambda h: {"jump": F(1)} if h == ISL else {"sink": F(1)}, lambda h, a: unit)
    swimmer = Hyp("swim", lambda h: {"jump": F(1)} if h == ISL else {"swim": F(1)}, lambda h, a: unit)
    return tree, [sinker, swimmer], [delta * s, delta * (1 - s)]


def sos_policy(j):
    """island: jump w.p. j; water: swim."""
    j = F(j)
    return {ISL: {"jump": j, "stay": 1 - j}, WATER: {"swim": F(1), "sink": F(0)}}


def sos_theorem_check():
    """Theorem (sink-or-swim): trapped fp iff s >= 1 - c/b; good fp iff delta*s <= 1 - c/b;
    mixed fp j* = delta (c - b(1-s)) / ((1-delta)(b-c)) in (0,1) iff both strict.
    TB at trap iff delta >= 1 - c/b; TB at good always.  Returns summary counts."""
    grid = [F(k, 8) for k in range(0, 9)]
    n = 0
    worst_ratio = F(0)
    for b in [F(1), F(3, 4)]:
        for c in [F(1, 8), F(1, 2), F(5, 8)]:
            if not c < b:
                continue
            for delta in [F(1, 100), F(1, 10), F(1, 4), F(1, 2), F(3, 4)]:
                for s in grid:
                    tree, hyps, wts = sink_or_swim(b, c, delta, s)
                    trap = Analysis(tree, hyps, wts, delta, sos_policy(0))
                    good = Analysis(tree, hyps, wts, delta, sos_policy(1))
                    check_facts(trap), check_facts(good)
                    assert trap.Qxi[(ISL, "jump")] == b * (1 - s)
                    assert good.Qxi[(ISL, "jump")] == b * (1 - delta * s)
                    assert trap.is_fixed_point() == (s >= 1 - c / b)
                    assert good.is_fixed_point() == (delta * s <= 1 - c / b)
                    assert trap.trust_bound(ISL) == (max(c, b * (1 - s)) >= (1 - delta) * b)
                    if trap.is_fixed_point():      # sketch's form: at the trap M = c
                        assert trap.trust_bound(ISL) == (delta >= 1 - c / b)
                    assert good.trust_bound(ISL)
                    assert trap.gap(ISL) == b - c and good.gap(ISL) == 0 and trap.Vstar[ISL] == b
                    # negative result: Cole's premise w = 1-delta, conclusion fails by b-c whenever trapped
                    if trap.is_fixed_point() and trap.trust_bound(ISL):   # positive result must hold there
                        assert trap.gap(ISL) <= trap.odds(ISL)
                        worst_ratio = max(worst_ratio, trap.gap(ISL) / trap.odds(ISL))
                    # mixed fixed point
                    if b * (1 - s) < c and b * (1 - delta * s) > c:
                        j = delta * (c - b * (1 - s)) / ((1 - delta) * (b - c))
                        assert 0 < j < 1
                        mix = Analysis(tree, hyps, wts, delta, sos_policy(j))
                        assert mix.is_fixed_point() and mix.Qxi[(ISL, "jump")] == c
                        if mix.trust_bound(ISL):
                            assert mix.gap(ISL) <= mix.odds(ISL)
                            worst_ratio = max(worst_ratio, mix.gap(ISL) / mix.odds(ISL))
                    else:   # no interior mixed point: check a few interior j are not fixed points
                        for j in [F(1, 3), F(1, 2), F(2, 3)]:
                            assert not Analysis(tree, hyps, wts, delta, sos_policy(j)).is_fixed_point()
                    n += 1
    return n, worst_ratio


# ----------------------------------------------------------------------------
# (iv) the floored agent pi^dagger: chain family (lower bound) and strict reset
# ----------------------------------------------------------------------------


def chain_instance(K, delta, leaf_rewards, ns_first_bad=False):
    """Chain h_0 ... h_K.  At h_k (k<K): 'go' (continue) or 'out' (leaf, reward leaf_rewards[k]).
    At h_K: 'go' (leaf, reward 1) or 'out' (leaf, reward 0).  One non-self hypothesis
    (weight delta): plays 'go' at h_0..h_{K-1} and 'out' at h_K.  Deterministic percepts.
    ns_first_bad: the non-self hypothesis plays 'out' already at h_1 (for the strict-reset test)."""
    delta = F(delta)

    def depth(h):
        return len(h)

    def actions(h):
        if any(a == "out" for a, _ in h):
            return []
        return ["go", "out"] if depth(h) <= K else []

    def percepts(h, a):
        return ["-"]

    def reward(h):
        a, k = h[-1][0], len(h) - 1   # action taken at h_k
        if a == "out":
            return F(leaf_rewards[k]) if k < K else F(0)
        return F(1) if k == K else F(0)

    tree = Tree(actions, percepts, reward, T=K + 1)
    unit = {"-": F(1)}

    def ns_act(h):
        k = len(h)
        if k < K and not (ns_first_bad and k >= 1):
            return {"go": F(1)}
        return {"out": F(1)}

    return tree, [Hyp("ns", ns_act, lambda h, a: unit)], [delta]


def chain_fixed_point(K, delta, lam=F(1, 2)):
    """The lambda-mixing fixed point of pi^dagger on the chain whose leaf rewards are the
    self-posteriors w_k = 1/(1 + O_0 / lam^k) it generates.  Returns (Analysis, w list)."""
    delta, lam = F(delta), F(lam)
    O0 = delta / (1 - delta)
    ws = [1 / (1 + O0 / lam ** k) for k in range(K)]
    tree, hyps, wts = chain_instance(K, delta, ws)
    pi = {}
    for h in tree.nonterminal:
        k = len(h)
        pi[h] = {"go": lam, "out": 1 - lam} if k < K else {"go": F(1), "out": F(0)}
    an = Analysis(tree, hyps, wts, delta, pi)
    return an, ws


def chain_theorem_check():
    """Verifies: the chain policy is a floored fixed point with equality at every h_k (k<K),
    posteriors w_k as designed, and loss eps(h_0) = (O_0/2) sum_k 1/(1 + O_0 2^k)  (lam = 1/2).
    Returns list of (delta, K, gap, gap/O_0)."""
    rows = []
    for m in [2, 3, 4, 5, 6, 8, 10]:
        delta = F(1, 2 ** m)
        K = m
        an, ws = chain_fixed_point(K, delta)
        check_facts(an)
        assert an.is_floored_fixed_point() and not an.is_fixed_point()
        root = ()
        for h in an.tree.nonterminal:
            k = len(h)
            if k < K:
                assert an.floor_sign(h) == 0 and an.w[h] == ws[k] and an.Vstar[h] == 1 and an.pistar[h] == "go"
            else:
                assert an.floor_sign(h) == 1
        O0 = an.odds(root)
        predicted = (O0 / 2) * sum(1 / (1 + O0 * 2 ** k) for k in range(K))
        assert an.gap(root) == predicted
        assert an.gap(root) <= O0 * (1 + K)          # the horizon-T form of Theorem C
        rows.append((delta, K, an.gap(root), an.gap(root) / O0))
    return rows


def strict_reset_check(K=4, delta=F(1, 16)):
    """A floored fixed point at which the reset fires w.p. 1 at h_0 with a STRICT inequality
    (M < w V^*): r_0 = 0, agent plays 'go' w.p. 1 at h_0, then the lam=1/2 chain from h_1.
    Self-posterior at h_1 equals w_0 (deterministic action, non-self also plays 'go').
    Returns (w_0, w_1, M(h_0), gap(h_0), gap(h_1))."""
    delta = F(delta)
    O0 = delta / (1 - delta)
    rewards = [F(0)] + [1 / (1 + O0 * 2 ** (k - 1)) for k in range(1, K)]
    tree, hyps, wts = chain_instance(K, delta, rewards)
    pi = {}
    for h in tree.nonterminal:
        k = len(h)
        pi[h] = {"go": F(1), "out": F(0)} if k in (0, K) else {"go": F(1, 2), "out": F(1, 2)}
    an = Analysis(tree, hyps, wts, delta, pi)
    check_facts(an)
    h0, h1 = (), (("go", "-"),)
    assert an.is_floored_fixed_point() and an.floor_sign(h0) == -1 and an.w[h1] == an.w[h0]
    assert an.gap(h0) == an.gap(h1) > 0 and an.gap(h0) <= an.odds(h0) * (1 + K)
    return an.w[h0], an.w[h1], an.M(h0), an.gap(h0), an.gap(h1)


def tight_trap_check():
    """Theorem B's constant O_h is asymptotically tight: sink-or-swim with b = 1, c = 1 - delta,
    s = 1: the trap satisfies TB with equality and gap / O_h = 1 - delta."""
    out = []
    for delta in [F(1, 2), F(1, 4), F(1, 10), F(1, 100), F(1, 1000)]:
        tree, hyps, wts = sink_or_swim(F(1), 1 - delta, delta, F(1))
        trap = Analysis(tree, hyps, wts, delta, sos_policy(0))
        assert trap.is_fixed_point() and trap.trust_bound(ISL) and trap.M(ISL) == trap.w[ISL] * trap.Vstar[ISL]
        assert trap.gap(ISL) / trap.odds(ISL) == 1 - delta
        out.append((delta, trap.gap(ISL) / trap.odds(ISL)))
    return out


# ----------------------------------------------------------------------------
# (v) randomized stress test
# ----------------------------------------------------------------------------


def random_instance(rng, T, nA, nE, nH, delta, zero_prob=F(1, 4)):
    """Random rational rewards (k/8), random action/percept kernels with occasional zeros,
    random non-self weights summing to delta; returns normalised so path returns lie in [0,1]."""
    A, E = list(range(nA)), list(range(nE))
    R = {}
    tree = Tree(lambda h: A, lambda h, a: E, lambda h: R[h], T)
    for h in tree.nodes:
        if h:
            R[h] = F(rng.randint(0, 8), 8)
    mx = tree.max_return()
    if mx > 0:
        for h in R:
            R[h] /= mx
    assert tree.max_return() <= 1

    def rand_dist(keys):
        while True:
            wts = [0 if rng.random() < zero_prob else rng.randint(1, 4) for _ in keys]
            if sum(wts):
                return {k: F(x, sum(wts)) for k, x in zip(keys, wts)}
    hyps = []
    for i in range(nH):
        act = {h: rand_dist(A) for h in tree.nonterminal}
        env = {(h, a): rand_dist(E) for h in tree.nonterminal for a in A}
        hyps.append(Hyp("nu%d" % i, (lambda t: lambda h: t[h])(act), (lambda t: lambda h, a: t[(h, a)])(env)))
    raw = [rng.randint(1, 5) for _ in range(nH)]
    weights = [F(delta) * x / sum(raw) for x in raw]
    return tree, hyps, weights


def ns_action_mass(an, h, supp):
    """non-self conditional mass on the actions in supp at h (0 if the non-self mass at h is 0)."""
    if an.xi_ns[h] == 0:
        return F(0)
    return sum(an.weights[i] * an.nu_joint[(i, h)] * F(nu.act(h).get(a, 0)) for i, nu in enumerate(an.hyps)
               for a in supp) / an.xi_ns[h]


def stress(seed=1, n_per_config=60, configs=((2, 2, 2, 2), (2, 3, 2, 2), (3, 2, 1, 2), (3, 2, 2, 1), (3, 2, 2, 2)),
           deltas=(F(1, 100), F(1, 10), F(1, 4), F(1, 2))):
    """configs = (T, |A|, |E|, #non-self hyps).  Returns a dict of statistics."""
    rng = random.Random(seed)
    st = dict(instances=0, plain_fps=0, floored_fps=0, no_plain=0, no_floored=0, tb_nodes=0,
              worst_plain=F(0), worst_plain_where=None, worst_floored=F(0), worst_floored_where=None,
              floored_with_strict_reset=0, no_plain_tb_everywhere=0, floored_gap_at_reset_nodes=0,
              worst_floored_vs_T=F(0))
    for (T, nA, nE, nH) in configs:
        for delta in deltas:
            for _ in range(n_per_config):
                tree, hyps, wts = random_instance(rng, T, nA, nE, nH, delta)
                st["instances"] += 1
                n_plain = n_floored = 0
                tb_everywhere = False
                for pi in pure_policies(tree, hyps, wts, delta):
                    an = Analysis(tree, hyps, wts, delta, pi)
                    fp, ffp = an.is_fixed_point(), an.is_floored_fixed_point()
                    if not (fp or ffp):
                        continue
                    check_facts(an)
                    if fp:
                        n_plain += 1
                        if all(an.trust_bound(h) for h in tree.nonterminal if an.xi[h] > 0):
                            tb_everywhere = True
                        for h in tree.nonterminal:
                            if an.trust_bound(h) and an.w[h] > 0:      # w_h = 0: both bounds vacuous
                                st["tb_nodes"] += 1
                                supp = [a for a, p in pi[h].items() if p > 0]
                                pbar = ns_action_mass(an, h, supp)
                                w = an.w[h]
                                assert an.gap(h) <= (1 - w) * (an.Vstar[h] * (1 - pbar) + pbar / w)   # p-dependent form
                                assert an.gap(h) <= (1 - w) * an.Vstar[h] * (1 + pbar * (1 - w) / w)     # refined via Lemma A'
                                assert an.gap(h) <= an.odds(h)                                          # Theorem B
                                if an.odds(h) > 0 and an.gap(h) / an.odds(h) > st["worst_plain"]:
                                    st["worst_plain"], st["worst_plain_where"] = an.gap(h) / an.odds(h), (T, nA, nE, nH, delta)
                    if ffp:
                        n_floored += 1
                        if any(an.floor_sign(h) == -1 for h in tree.nonterminal):
                            st["floored_with_strict_reset"] += 1
                        for h in tree.nonterminal:
                            if an.w[h] == 0:
                                continue
                            assert an.gap(h) <= an.odds(h) * (1 + T)                                    # Theorem C (horizon form)
                            if an.floor_sign(h) == -1 and an.gap(h) > 0:
                                st["floored_gap_at_reset_nodes"] += 1
                            if an.odds(h) > 0:
                                r = an.gap(h) / an.odds(h)
                                if r > st["worst_floored"]:
                                    st["worst_floored"], st["worst_floored_where"] = r, (T, nA, nE, nH, delta)
                st["plain_fps"] += n_plain
                st["floored_fps"] += n_floored
                st["no_plain"] += (n_plain == 0)
                st["no_floored"] += (n_floored == 0)
                st["no_plain_tb_everywhere"] += (not tb_everywhere)
    return st


def pure_existence_search(seed=7, n=150, zero_prob=F(3, 5)):
    """Targeted search for instances WITHOUT a pure fixed point (plain / floored): T = 3,
    |A| = 2, |E| in {1, 2}, 2-3 near-deterministic non-self hypotheses.  Returns
    (instances, no_plain, no_floored, worst gap/O_h at TB nodes)."""
    rng = random.Random(seed)
    no_plain = no_floored = 0
    worst = F(0)
    total = 0
    for nE in (1, 2):
        for nH in (2, 3):
            for delta in (F(1, 10), F(1, 2)):
                for _ in range(n):
                    tree, hyps, wts = random_instance(rng, 3, 2, nE, nH, delta, zero_prob=zero_prob)
                    total += 1
                    n_plain = n_floored = 0
                    for pi in pure_policies(tree, hyps, wts, delta):
                        an = Analysis(tree, hyps, wts, delta, pi)
                        if an.is_fixed_point():
                            n_plain += 1
                            for h in tree.nonterminal:
                                if an.trust_bound(h) and 0 < an.w[h] < 1:
                                    assert an.gap(h) <= an.odds(h) * an.Vstar[h]
                                    worst = max(worst, an.gap(h) / an.odds(h))
                        if an.is_floored_fixed_point():
                            n_floored += 1
                    no_plain += (n_plain == 0)
                    no_floored += (n_floored == 0)
    return total, no_plain, no_floored, worst


# ----------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------


def main(n_per_config=60, seed=1):
    n, worst = sos_theorem_check()
    print("sink-or-swim: %d (b,c,delta,s) grid points; trapped/good/mixed conditions, TB thresholds and gaps all exact; "
          "worst gap/O_h at TB fixed points on the grid = %s" % (n, worst))
    print("tight trap (b=1, c=1-delta, s=1): gap/O_h = " + ", ".join("%s->%s" % (d, r) for d, r in tight_trap_check()))
    print("floored chain family (lam=1/2), gap(h_0)/O_0 must grow like (1/2) log2(1/delta):")
    for delta, K, gap, ratio in chain_theorem_check():
        print("   delta=%-7s K=%-2d gap=%.5f gap/O_0=%.4f" % (delta, K, float(gap), float(ratio)))
    w0, w1, M0, g0, g1 = strict_reset_check()
    print("strict reset at a floored fixed point: w_0=%s M(h_0)=%.4f < w_0; w_1=%s (unchanged); gap(h_0)=gap(h_1)=%.4f"
          % (w0, float(M0), w1, float(g0)))
    tot, np_, nf, w_ = pure_existence_search(n=max(5, n_per_config))
    print("pure-existence search (T=3, near-deterministic hypotheses): %d instances, %d without a pure plain fixed point, "
          "%d without a pure floored fixed point; worst gap/O_h = %s" % (tot, np_, nf, w_))
    st = stress(seed=seed, n_per_config=n_per_config)
    print("stress: %d instances; %d pure plain fps (%d instances with none), %d pure floored fps (%d with none); "
          "%d TB nodes checked" % (st["instances"], st["plain_fps"], st["no_plain"], st["floored_fps"], st["no_floored"], st["tb_nodes"]))
    print("   Theorem B at every TB node (gap <= O_h and p-dependent form): worst gap/O_h = %s (%.4f) at (T,|A|,|E|,#hyp,delta)=%s"
          % (st["worst_plain"], float(st["worst_plain"]), st["worst_plain_where"]))
    print("   Theorem C horizon form gap <= O_h (1+T) at every node of every floored fp: worst gap/O_h = %s (%.4f) at %s"
          % (st["worst_floored"], float(st["worst_floored"]), st["worst_floored_where"]))
    print("   floored fps with a strict reset somewhere: %d; reset nodes with positive gap: %d; instances with no pure plain fp "
          "satisfying TB at every xi-positive node: %d" % (st["floored_with_strict_reset"], st["floored_gap_at_reset_nodes"],
                                                            st["no_plain_tb_everywhere"]))
    print("ALL ASSERTIONS PASSED")


if __name__ == "__main__":
    main(n_per_config=int(sys.argv[1]) if len(sys.argv) > 1 else 60)
