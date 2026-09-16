"""The inquiry model (third pass): finite worlds, an inquiry repertoire, adaptive
policies, information cells, the certain docket, the frontier, and the minimax value.

Objects (all exact):

  worlds      `name -> frozenset` of the *adverse* declared reasons true in that world.
              The advisor's pro content `pro` is fixed (it supplies its own reasons); the
              program `F` is required to be antitone in the adverse reasons given `pro`
              (`is_antitone` checks it).  Verdict of a content `S`: `V(S) := F(pro ∪ S)`.
  action      `Action(name, cost, outcome)`: `outcome(world)` is what running the action
              reveals; a direct query on `r` reveals whether `r` is true.  The outcome is a
              function of the world alone (evidence soundness).
  cell        the set of worlds consistent with the outcomes observed so far.
  certain     the reasons true in every world of a cell: what can be *docketed* as true.
  residual    `V(D) − V(Truth(ω))` for a docket `D ⊆ Truth(ω)`: the advisor's omission
              gain from what is undiscovered (≥ 0 by antitonicity).
  gap         of a cell `K`: `max_{ω ∈ K} V(certain(K)) − V(Truth(ω))`, the residual of
              the exhaustive docket on the worst world of the cell.
  frontier    given a cell and a docket: the reasons undetermined in the cell whose
              conditional adverse sensitivity above the docket is positive.
  potential   `max_{ω ∈ K} Σ_{r ∈ Truth(ω) \\ D} A_{r|D}`: the worst-case conditional
              adverse mass still undiscovered.
  minimax     `V(K, B)`: the least worst-case residual any adaptive policy with budget
              `B` achieves from cell `K`, by the exact recursion.
"""
from fractions import Fraction as Q
from itertools import combinations

from .sensitivity import subsets, clamp


class Action:
    def __init__(self, name, cost, outcome):
        self.name, self.cost, self.outcome = name, Q(cost), outcome

    def __repr__(self):
        return f"Action({self.name!r}, cost={self.cost})"


def query(r, cost=1):
    return Action(f"q:{r}", cost, lambda truth: r in truth)


class Inquiry:
    def __init__(self, worlds, actions, F, pro=frozenset()):
        self.worlds = {k: frozenset(v) for k, v in worlds.items()}
        self.actions = list(actions)
        self.F, self.pro = F, frozenset(pro)
        self.universe = frozenset().union(*self.worlds.values()) if self.worlds else frozenset()

    # ------------------------------------------------------------ program side
    def V(self, S):
        return self.F(self.pro | frozenset(S))

    def is_antitone(self):
        U = sorted(self.universe)
        for c in subsets(U):
            for r in U:
                if r not in c and self.V(c | {r}) > self.V(c):
                    return False
        return True

    def cond_adverse(self, r, D):
        """`A_{r|D} := max_{c ⊇ D, r ∉ c} (V(c) − V(c ∪ {r}))⁺` over the adverse universe."""
        D = frozenset(D)
        rest = sorted(self.universe - D - {r})
        best = Q(0)
        for extra in subsets(rest):
            c = D | extra
            best = max(best, self.V(c) - self.V(c | {r}))
        return best

    # ------------------------------------------------------------ information side
    def outcomes(self, w, actions):
        return tuple(a.outcome(self.worlds[w]) for a in actions)

    def cell(self, w, actions):
        sig = self.outcomes(w, actions)
        return frozenset(w2 for w2 in self.worlds if self.outcomes(w2, actions) == sig)

    def cells(self, actions):
        seen, out = set(), []
        for w in self.worlds:
            if w in seen:
                continue
            K = self.cell(w, actions)
            seen |= K
            out.append(K)
        return out

    def certain(self, K):
        return frozenset.intersection(*(self.worlds[w] for w in K))

    def residual(self, D, w):
        assert frozenset(D) <= self.worlds[w]
        return self.V(D) - self.V(self.worlds[w])

    def gap(self, K, D=None):
        D = self.certain(K) if D is None else frozenset(D)
        return max(self.V(D) - self.V(self.worlds[w]) for w in K)

    def obstruction(self):
        """The repertoire obstruction: the largest gap of a cell of the full repertoire."""
        return max(self.gap(K) for K in self.cells(self.actions))

    def frontier(self, K, D):
        D = frozenset(D)
        out = []
        for r in sorted(self.universe - D):
            vals = {r in self.worlds[w] for w in K}
            if vals == {True, False} and self.cond_adverse(r, D) > 0:
                out.append(r)
        return out

    def potential(self, K, D):
        D = frozenset(D)
        return max(sum((self.cond_adverse(r, D) for r in self.worlds[w] - D), Q(0)) for w in K)

    # ------------------------------------------------------------ policies
    def minimax(self, K=None, B=None, memo=None):
        """`V(K, B) = min( gap(K), min_{a affordable} max_o V(K_o, B − c(a)) )`."""
        K = frozenset(self.worlds) if K is None else frozenset(K)
        B = Q(10**9) if B is None else Q(B)
        memo = {} if memo is None else memo
        key = (K, B)
        if key in memo:
            return memo[key]
        best = self.gap(K)
        for a in self.actions:
            if a.cost > B:
                continue
            parts = {}
            for w in K:
                parts.setdefault(a.outcome(self.worlds[w]), set()).add(w)
            if len(parts) == 1:
                continue
            worst = max(self.minimax(frozenset(p), B - a.cost, memo) for p in parts.values())
            best = min(best, worst)
        memo[key] = best
        return best

    def nonadaptive(self, B):
        """The best fixed set of actions within budget: min over sets of the max cell gap."""
        best = self.gap(frozenset(self.worlds))
        acts = self.actions
        for k in range(1, len(acts) + 1):
            for combo in combinations(acts, k):
                if sum(a.cost for a in combo) <= B:
                    best = min(best, max(self.gap(K) for K in self.cells(list(combo))))
        return best

    def run(self, policy, w, B):
        """Run an adaptive policy (a function of (cell, docket, remaining budget) returning an
        action or None) in world `w`.  Returns (docket, cell, spent)."""
        K, spent, done = frozenset(self.worlds), Q(0), []
        while True:
            D = self.certain(K)
            a = policy(self, K, D, B - spent)
            if a is None or a.cost > B - spent:
                return D, K, spent
            spent += a.cost
            done.append(a)
            K = self.cell(w, done)


def greedy_frontier(inq, K, D, budget):
    """Query the undetermined reason of largest conditional adverse mass (direct queries
    only); stop when the frontier is empty."""
    fr = inq.frontier(K, D)
    if not fr:
        return None
    r = max(fr, key=lambda r: (inq.cond_adverse(r, D), r))
    for a in inq.actions:
        if a.name == f"q:{r}" and a.cost <= budget:
            return a
    return None
