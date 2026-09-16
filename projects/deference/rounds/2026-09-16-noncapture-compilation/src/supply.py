"""The reason-supply service problem, exactly (second pass).

Objects (all exact, `fractions.Fraction`, integer capacities):

  Reason      `Reason(id, weight, cost, release, protected, declared, auth_ok)`:
              `weight`   the reason's adverse sensitivity for the advisor's candidate
                         (how much the candidate's verdict falls when the reason is
                         present; `≥ 0`);
              `cost`     service cost in capacity units (discover-route-authenticate);
              `release`  the slot at which the ecosystem learns the reason is true and
                         relevant; `None` = never discovered before commitment;
              `protected` whether the coverage barrier protects it;
              `declared` whether its type is in the declared interface;
              `auth_ok`  whether authentication succeeds once served.
  Instance    `Instance(reasons, T, cap)`: slots `0 .. T-1` before the commitment
              deadline `T`; `cap[t]` capacity units available at slot `t`.
  Schedule    a map reason -> slot -> units, respecting release, horizon and capacity;
              a reason is served when it receives `cost` units.  Service is
              preemptive (units of one reason may be spread over slots).

The service problem: choose which discovered declared reasons to serve so that the
missed adverse mass `Miss = Σ_{true declared, unserved} weight` is least.

Facts implemented and tested:
  * `cut_ok`        the suffix-cut condition `∀ s: Demand(s) ≤ Cap(s)`, with
                    `Demand(s)` the cost of reasons released at or after `s` and
                    `Cap(s)` the capacity of slots `s .. T-1`;
  * `feasible`      a set is servable iff its own cut condition holds (the flow argument;
                    checked against exhaustive schedule search on unit instances);
  * `cut_excess`    `max_s (Demand(s) − Cap(s))⁺`: the least unserved cost (Hall
                    deficiency), exact;
  * `min_miss`      exhaustive minimum of the weighted miss over servable sets;
  * `greedy`        largest weight first, feasibility by the cut test: optimal for unit
                    costs (a transversal matroid on nested neighbourhoods), not for
                    general costs (`attacks_second_pass` fixture);
  * `decompose`     the missed mass split into discovery, service, authentication, with
                    scope reported outside.
"""
from fractions import Fraction as Q
from itertools import combinations


class Reason:
    def __init__(self, rid, weight, cost=1, release=0, protected=False, declared=True, auth_ok=True):
        self.id, self.weight, self.cost = rid, Q(weight), int(cost)
        self.release, self.protected, self.declared, self.auth_ok = release, protected, declared, auth_ok

    @property
    def discovered(self):
        return self.release is not None

    def __repr__(self):
        return f"Reason({self.id!r}, w={self.weight}, c={self.cost}, a={self.release})"


class Instance:
    def __init__(self, reasons, T, cap):
        self.reasons = list(reasons)
        self.T = int(T)
        self.cap = list(cap) if not callable(cap) else [cap(t) for t in range(self.T)]
        assert len(self.cap) == self.T

    def by_id(self, rid):
        return next(r for r in self.reasons if r.id == rid)

    def servable(self):
        """The reasons the service problem is about: discovered, declared, released before T."""
        return [r for r in self.reasons if r.declared and r.discovered and r.release < self.T]

    def Cap(self, s):
        return sum(self.cap[t] for t in range(max(s, 0), self.T))

    def Demand(self, s, S=None):
        pool = self.servable() if S is None else [r for r in self.servable() if r.id in S]
        return sum(r.cost for r in pool if r.release >= s)

    def cut_ok(self, S=None):
        return all(self.Demand(s, S) <= self.Cap(s) for s in range(self.T + 1))

    def cut_excess(self, S=None):
        return max(max(self.Demand(s, S) - self.Cap(s), 0) for s in range(self.T + 1))

    def feasible(self, S):
        return self.cut_ok(set(S))

    # ---------------------------------------------------------------- optimisation

    def miss(self, served):
        served = set(served)
        return sum((r.weight for r in self.reasons if r.declared and r.id not in served), Q(0))

    def min_miss(self):
        """Exhaustive: the least weighted miss over servable sets (the ideal, against N_full)."""
        pool = self.servable()
        best, best_S = None, None
        for k in range(len(pool), -1, -1):
            for combo in combinations(pool, k):
                S = {r.id for r in combo}
                if self.feasible(S):
                    m = self.miss(S)
                    if best is None or m < best:
                        best, best_S = m, S
        return best, best_S

    def greedy(self):
        """Largest adverse weight first; keep a reason if the set stays servable."""
        S = set()
        for r in sorted(self.servable(), key=lambda r: (-r.weight, r.id)):
            if self.feasible(S | {r.id}):
                S.add(r.id)
        return S

    def online_greedy(self):
        """Unit costs: at each slot serve the heaviest discovered unserved reason.  The
        supplier never sees a future release; for a common deadline this attains the
        offline optimum (exchange argument)."""
        served, pool = set(), [r for r in self.servable() if r.cost == 1]
        for t in range(self.T):
            for _ in range(self.cap[t]):
                avail = [r for r in pool if r.release <= t and r.id not in served]
                if not avail:
                    break
                served.add(max(avail, key=lambda r: (r.weight, r.id)).id)
        return served

    # ---------------------------------------------------------------- the exact dual (unit costs)

    def rank(self, S):
        """Unit costs: the largest servable subset of `S` has size
        `|S| − max_s (#{r ∈ S : release ≥ s} − Cap(s))⁺` (Hall deficiency on suffix cuts)."""
        S = set(S)
        return len(S) - self.cut_excess(S)

    def layer_value(self):
        """Unit costs: the largest servable adverse mass, by the matroid layer formula
        `Σ_j (w_(j) − w_(j+1)) · rank(top-j)` over the reasons sorted by weight.  Its
        complement in the total mass is the least miss (checked against `min_miss`)."""
        pool = sorted(self.servable(), key=lambda r: (-r.weight, r.id))
        assert all(r.cost == 1 for r in pool)
        total = Q(0)
        for j in range(1, len(pool) + 1):
            w_j = pool[j - 1].weight
            w_next = pool[j].weight if j < len(pool) else Q(0)
            total += (w_j - w_next) * self.rank({r.id for r in pool[:j]})
        return total

    def min_miss_formula(self):
        """Unit costs: the exact least miss, `total adverse mass − layer value`."""
        return sum((r.weight for r in self.reasons if r.declared), Q(0)) - self.layer_value()

    # ---------------------------------------------------------------- decomposition

    def decompose(self, served):
        """Missed adverse mass by cause.  Scope (undeclared) is reported, not charged:
        it is outside the declared interface and outside the theorem."""
        served = set(served)
        out = {"discovery": Q(0), "service": Q(0), "authentication": Q(0), "scope": Q(0)}
        for r in self.reasons:
            if not r.declared:
                out["scope"] += r.weight
            elif not r.discovered or r.release >= self.T:
                out["discovery"] += r.weight
            elif r.id not in served:
                out["service"] += r.weight
            elif not r.auth_ok:
                out["authentication"] += r.weight
        return out

    def realizable_regret(self, served):
        """Content residual against the *discovered* comparator: service + authentication."""
        d = self.decompose(served)
        return d["service"] + d["authentication"]

    def ideal_regret(self, served):
        """Content residual against the fully-informed comparator: adds discovery."""
        d = self.decompose(served)
        return d["discovery"] + d["service"] + d["authentication"]


# -------------------------------------------------------------------- exhaustive schedules


def unit_schedules_exist(inst, S):
    """For unit costs and unit capacities: does an injective assignment of the reasons in
    `S` to slots in their windows exist?  Exhaustive, to validate `feasible`."""
    pool = [r for r in inst.servable() if r.id in S]
    assert all(r.cost == 1 for r in pool) and all(c <= 1 for c in inst.cap)
    slots = [t for t in range(inst.T) if inst.cap[t] == 1]

    def rec(i, used):
        if i == len(pool):
            return True
        r = pool[i]
        for t in slots:
            if t >= r.release and t not in used:
                if rec(i + 1, used | {t}):
                    return True
        return False
    return rec(0, frozenset())


def general_schedule_exists(inst, S):
    """Preemptive integer schedule search for small general instances: distribute each
    reason's units over its window subject to slot capacities.  Exhaustive."""
    pool = [r for r in inst.servable() if r.id in S]
    cap = list(inst.cap)

    def rec(i, cap):
        if i == len(pool):
            return True
        r = pool[i]
        window = [t for t in range(r.release, inst.T)]

        def place(j, remaining, cap):
            if remaining == 0:
                return rec(i + 1, cap)
            if j == len(window):
                return False
            t = window[j]
            for u in range(min(remaining, cap[t]), -1, -1):
                cap2 = list(cap); cap2[t] -= u
                if place(j + 1, remaining - u, cap2):
                    return True
            return False
        return place(0, r.cost, cap)
    return rec(0, cap)
