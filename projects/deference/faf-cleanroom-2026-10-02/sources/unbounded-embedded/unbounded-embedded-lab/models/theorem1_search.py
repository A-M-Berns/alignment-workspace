#!/usr/bin/env python3
"""Task R2-B: is Cole Wyeth's revised Theorem 1 TRUE for the plain agent pi_S in the
finite shadow, i.e. can its "there is a reflective oracle" existential be witnessed?

Best-fixed-point loss of an instance (see theorem1-as-stated.md section 1):
    L(instance) := min over fixed points pi of  max over h with w_h >= 1-delta of  V^*(h) - V^pi(h).

This file (exact fractions.Fraction throughout; sympy only for the mixed-point solver):
  (i)   pi^R (residual-argmax policy) -- a pure fixed point of EVERY instance (Theorem D0);
  (ii)  pi^B (best-on-path policy) -- a pure fixed point with loss <= 1 - (1-delta)^(T-1-t) at every
        node of depth t (Theorem D1), computed by the backward recursion B(h);
  (iii) brute-force L_pure by enumerating all pure fixed points (library enumerator);
  (iv)  the trap chain (Instance-B family of depth K) attaining L = 1 - (1-delta')^K, delta' < delta,
        with a UNIQUE fixed point, pure or mixed (Theorem D2);
  (v)   random + targeted searches over small instances, asserting L_pure <= 1 - (1-delta)^(T-1);
  (vi)  exact mixed-fixed-point solver (T <= 3, |A| = 2, |E| = 1) via sympy on the worst instances.
Library: sequential_self_game.py (imported, not modified; its main() only runs under __main__).
Run: python3 theorem1_search.py [n_per_config]   (default 40; ~2-4 min).  Ends with ALL ASSERTIONS PASSED.
"""
import os
import random
import sys
import itertools
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sequential_self_game import (Tree, Hyp, Analysis, det_policy, pure_policies,  # noqa: E402
                                  enumerate_fixed_points, random_instance, check_facts)


# ----------------------------------------------------------------------------
# (i) structural quantities of an instance that do not depend on pi
# ----------------------------------------------------------------------------

class Structure:
    """pi-independent data of an instance: residual joint xi_ns(h), residual action conditional
    pibar(a|h), residual continuation Qbar(h,a) = Q^{pibar}_xi(h,a), optimal Q^*(h,a), the
    on-path posterior wt(h) (posterior at h under ANY pure policy that reaches h), the set N(h)
    of actions no residual hypothesis plays at h, and Alt_h(a) := Qbar(h,a) if a not in N(h), else Q^*(h,a)."""

    def __init__(self, tree, hyps, weights, delta):
        self.tree, self.hyps, self.weights, self.delta = tree, hyps, weights, F(delta)
        # any policy gives the pi-independent quantities; use the first action everywhere
        probe = Analysis(tree, hyps, weights, delta, {h: {tree.actions(h)[0]: F(1)} for h in tree.nonterminal})
        self.probe = probe
        self.xi_ns = probe.xi_ns
        self.Qstar, self.Vstar = probe.Qstar, probe.Vstar
        self.env = {(h, a): probe.envS(h, a) for h in tree.nonterminal for a in tree.actions(h)}
        # residual mass after (h, a) and residual continuation value
        self.ns_ha, self.Qbar, self.N, self.Alt, self.pibar = {}, {}, {}, {}, {}
        for h in tree.nonterminal:
            self.N[h] = set()
            for a in tree.actions(h):
                m = sum(weights[i] * probe.nu_joint[(i, h)] * F(nu.act(h).get(a, 0)) for i, nu in enumerate(hyps))
                self.ns_ha[(h, a)] = m
                self.pibar[(h, a)] = (m / self.xi_ns[h]) if self.xi_ns[h] > 0 else None
                if m > 0:
                    self.Qbar[(h, a)] = sum(weights[i] * probe.nu_joint[(i, h)] * F(nu.act(h).get(a, 0)) * probe.Qnu[(i, h, a)]
                                            for i, nu in enumerate(hyps)) / m
                    self.Alt[(h, a)] = self.Qbar[(h, a)]
                else:
                    self.N[h].add(a)
                    self.Alt[(h, a)] = self.Qstar[(h, a)]
        # percept-only path probability P_e(h) and on-path posterior wt(h)
        self.Pe, self.wt = {(): F(1)}, {}
        for h in tree.nodes:
            if h:
                pre, (a, e) = h[:-1], h[-1]
                self.Pe[h] = self.Pe[pre] * self.env[(pre, a)][e]
        for h in tree.nodes:
            num = (1 - self.delta) * self.Pe[h]
            self.wt[h] = num / (num + self.xi_ns[h]) if num + self.xi_ns[h] > 0 else F(1)
        # posterior after (h, a) if a is played surely at on-path h
        self.wt_ha = {}
        for h in tree.nonterminal:
            for a in tree.actions(h):
                num = (1 - self.delta) * self.Pe[h]
                self.wt_ha[(h, a)] = num / (num + self.ns_ha[(h, a)]) if num + self.ns_ha[(h, a)] > 0 else F(1)

    def residual_value(self, h):
        """V^{pibar}(h) = sum_a pibar(a|h) Qbar(h,a) (None where the residual mass at h is 0)."""
        if self.xi_ns[h] == 0 or not self.tree.actions(h):
            return None
        return sum(self.pibar[(h, a)] * self.Qbar[(h, a)] for a in self.tree.actions(h) if self.pibar[(h, a)] > 0)


def residual_argmax_policy(st):
    """pi^R: at every node play the (first) argmax of Alt_h.  Theorem D0: always a pure fixed point."""
    tab = {}
    for h in st.tree.nonterminal:
        acts = st.tree.actions(h)
        m = max(st.Alt[(h, a)] for a in acts)
        tab[h] = [a for a in acts if st.Alt[(h, a)] == m][0]
    return det_policy(tab)


def best_onpath(st):
    """Backward recursion for B(h) = best value of a sub-policy that is fixed-point-consistent on the
    subtree of h, GIVEN that h is on-path.  Returns (B, choice) with choice[h] the action attaining it.
    Feasibility of a at h (a not in N): wt_ha * cont(a) + (1 - wt_ha) * Qbar(h,a) >= max_{a' != a} Alt(a');
    for a in N: Q^*(h,a) >= max_{a' != a} Alt(a').  cont(a) = sum_e xi(e|ha) [r + B(hae)]."""
    t = st.tree
    B, choice, S = {}, {}, {}
    for h in reversed(t.nodes):
        acts = t.actions(h)
        if not acts:
            B[h] = F(0)
            continue
        best, arg = None, None
        for a in acts:
            kids = [(h + ((a, e),), st.env[(h, a)][e]) for e in t.percepts(h, a)]
            cont = sum(p * (t.disc(c) * t.reward(c) + B[c]) for c, p in kids)
            if a in st.N[h]:
                cont = st.Qstar[(h, a)]           # null subtree: optimal there
                S[(h, a)] = cont
            else:
                S[(h, a)] = st.wt_ha[(h, a)] * cont + (1 - st.wt_ha[(h, a)]) * st.Qbar[(h, a)]
            rival = max([st.Alt[(h, a2)] for a2 in acts if a2 != a], default=F(0))
            if S[(h, a)] >= rival and (best is None or cont > best):
                best, arg = cont, a
        assert best is not None, ("no feasible action at", h)   # cannot happen: argmax Alt is feasible
        B[h], choice[h] = best, arg
    return B, choice, S


def best_onpath_policy(st):
    """pi^B: top-down, play choice[h] at on-path nodes and pi^R at off-path nodes."""
    B, choice, _ = best_onpath(st)
    piR = residual_argmax_policy(st)
    tab, onpath = {}, {(): True}
    t = st.tree
    for h in t.nodes:
        if h and h not in onpath:
            pre, (a, e) = h[:-1], h[-1]
            onpath[h] = onpath[pre] and tab[pre] == a
        if t.actions(h):
            tab[h] = choice[h] if onpath[h] else list(piR[h])[0]
    return det_policy(tab), B


def loss_profile(an, thresh):
    """max over non-terminal h with w_h >= thresh of the gap V^*(h) - V^pi(h), and the argmax node."""
    worst, where = F(0), None
    for h in an.tree.nonterminal:
        if an.w[h] >= thresh:
            g = an.gap(h)
            if g > worst:
                worst, where = g, h
    return worst, where


def L_pure(tree, hyps, weights, delta, thresh=None):
    """(L_pure, witness Analysis, number of pure fixed points).  L_pure = None if no pure fixed point."""
    thresh = (1 - F(delta)) if thresh is None else thresh
    best, wit, n = None, None, 0
    for an in enumerate_fixed_points(tree, hyps, weights, delta):
        n += 1
        l, _ = loss_profile(an, thresh)
        if best is None or l < best:
            best, wit = l, an
    return best, wit, n


def bound(delta, T):
    """Theorem D1: L <= 1 - (1 - delta)^(T-1)."""
    return 1 - (1 - F(delta)) ** (T - 1)


# ----------------------------------------------------------------------------
# (iv) the trap chain: Instance B of oracle-side-gaps-reaudit.md, generalised to depth K
# ----------------------------------------------------------------------------

def chain_trap(K, delta, deltap=None, rewards=None):
    """Nodes h_0..h_{K-1}: `stay` (terminal, reward c_k) or `go`; after h_{K-1} go: water, `swim` 1 / `sink` 0.
    One residual hypothesis of weight delta: go at every h_k, sink in the water.  c_k = (1-delta')^(K-k)
    with delta' < delta (default delta' = delta * 9/10); T = K + 1; deterministic percepts; gamma = 1."""
    delta = F(delta)
    deltap = F(deltap) if deltap is not None else delta * F(9, 10)
    if rewards is None:
        rewards = {k: (1 - deltap) ** (K - k) for k in range(K)}

    def depth(h):
        return len(h)

    def actions(h):
        if any(a == "stay" for a, _ in h):
            return []
        return ["stay", "go"] if depth(h) < K else ["swim", "sink"]

    def percepts(h, a):
        return ["-"]

    def reward(h):
        a = h[-1][0]
        if a == "stay":
            return rewards[depth(h) - 1]
        return F(1) if a == "swim" else F(0)

    tree = Tree(actions, percepts, reward, K + 1)
    res = Hyp("residual", lambda h: {"go": F(1)} if depth(h) < K else {"sink": F(1)}, lambda h, a: {"-": F(1)})
    return tree, [res], [delta], delta, rewards


def chain_check(K, delta, deltap=None):
    """Enumerate pure fixed points of the chain; return (L_pure, n_fps, c_0, all preferences strict?)."""
    tree, hyps, wts, delta, rewards = chain_trap(K, delta, deltap)
    L, wit, n = L_pure(tree, hyps, wts, delta)
    # strictness of the trap at the unique fixed point: at every h_k, stay beats go strictly
    strict = all(wit.Qxi[(h, "stay")] > wit.Qxi[(h, "go")] for h in tree.nonterminal if "stay" in tree.actions(h))
    return L, n, rewards[0], strict, wit
