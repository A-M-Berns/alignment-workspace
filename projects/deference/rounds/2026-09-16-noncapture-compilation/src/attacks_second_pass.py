"""The second-pass countermodels: the service problem under pressure (dispatch §11).

Each fixture is a supply instance (or a program), the quantity the theorem charges on it,
and the hypothesis it isolates as structural or wishful.
"""
from fractions import Fraction as Q

from .supply import Reason, Instance
from .sensitivity import WeightedCount, Defeat, Redundant, adverse, sensitivity, omission_gain

W = Q(1, 4)


class Case:
    def __init__(self, name, inst, hypothesis, structural, note, prog=None):
        self.name, self.inst, self.hypothesis = name, inst, hypothesis
        self.structural, self.note, self.prog = structural, note, prog

    def report(self):
        I = self.inst
        out = {"name": self.name, "hypothesis": self.hypothesis, "structural": self.structural}
        if I is not None:
            best, S = I.min_miss()
            out.update({"cut_ok": I.cut_ok(), "cut_excess": I.cut_excess(), "min_miss": best,
                        "best_set": S, "greedy": I.greedy(), "greedy_miss": I.miss(I.greedy()),
                        "decomposition": I.decompose(S)})
        return out


def cases():
    out = []

    # 1. two reasons competing for one pre-deadline slot
    I = Instance([Reason("r1", W, release=0), Reason("r2", W, release=0)], T=1, cap=[1])
    out.append(Case("1 two reasons, one slot", I, "capacity ≥ demand (the suffix cut)", True,
                    "cut excess 1: exactly one reason is missed whatever the policy"))

    # 2. high- and low-value reasons with one slot
    I = Instance([Reason("hi", Q(1, 2), release=0), Reason("lo", Q(1, 8), release=0)], T=1, cap=[1])
    out.append(Case("2 high and low value, one slot", I, "weighted service (serve by adverse mass)", True,
                    "the least miss is the low value; count would charge 1 either way"))

    # 3. protected high-value versus unprotected low-value, one slot
    I = Instance([Reason("hi", Q(1, 2), release=0, protected=True), Reason("lo", Q(1, 8), release=0)],
                 T=1, cap=[1])
    out.append(Case("3 protected high vs unprotected low, one slot", I,
                    "protect what you can afford to serve", True,
                    "serving the protected reason keeps the audit on and charges the low mass; "
                    "serving the low one voids the evaluation instead"))

    # 4. supplier knows both reasons but can service one
    I = Instance([Reason("r1", W, release=0), Reason("r2", W, release=0)], T=2, cap=[1, 0])
    out.append(Case("4 known but unservable", I, "knowledge is not service", True,
                    "both discovered at 0; capacity 1 before the deadline: one is missed"))

    # 5. supplier learns a reason only near the deadline
    I = Instance([Reason("late", W, cost=2, release=3)], T=4, cap=[1, 1, 1, 1])
    out.append(Case("5 discovered near the deadline", I, "release-window capacity, not total capacity", True,
                    "total capacity 4 ≥ cost 2, but the window [3,4) has capacity 1: the cut at s=3 fails"))

    # 6. authentication consumes capacity
    I_auth = Instance([Reason("r", W, cost=2, release=0), Reason("q", W, cost=2, release=0)], T=3, cap=[1, 1, 1])
    I_noauth = Instance([Reason("r", W, cost=1, release=0, auth_ok=False),
                         Reason("q", W, cost=1, release=0, auth_ok=False)], T=3, cap=[1, 1, 1])
    out.append(Case("6 authentication consumes capacity", I_auth,
                    "cost includes authentication", True,
                    "with authentication in the cost one reason is missed; skipping it serves both "
                    "and moves the same mass to the authentication term"))
    out[-1].alt = I_noauth

    # 7. defeat changes marginal importance (a program fixture)
    prog7 = Defeat({"for": W, "against": -W}, {"against": {"d"}})   # d defeats `against`
    out.append(Case("7 defeat", None, "sensitivity certificate is per reason, not per weight", True,
                    "the defeater has weight 0 and adverse sensitivity 0 but symmetric sensitivity W; "
                    "the counterreason's adverse sensitivity is W", prog=prog7))

    # 8. duplicate / redundant evidence
    prog8 = Redundant([(-W, {"a1", "a2"})])
    out.append(Case("8 redundant evidence", None, "the telescoping bound is not tight", True,
                    "two reasons establishing one counter-conclusion: omitting both gains W, "
                    "the adverse mass charges 2W; the direct discrepancy is the sharp quantity",
                    prog=prog8))

    # 9. correlated reasons: servicing one reveals another
    I_a = Instance([Reason("r1", Q(1, 8), release=0), Reason("r2", Q(1, 2), release=None)], T=2, cap=[1, 1])
    I_b = Instance([Reason("r1", Q(1, 8), release=0), Reason("r2", Q(1, 2), release=1)], T=2, cap=[1, 1])
    out.append(Case("9 correlated discovery", I_a, "discovery is policy-dependent", True,
                    "r2 is discovered only by serving r1 at slot 0; a supplier that treats r2 as "
                    "undiscovered charges it to discovery loss, one that serves r1 first discovers and serves it"))
    out[-1].alt = I_b

    # 10. adversarial arrival times
    I = Instance([Reason("r1", W, release=2), Reason("r2", W, release=2), Reason("r3", W, release=2)],
                 T=3, cap=[1, 1, 1])
    out.append(Case("10 adversarial arrivals", I, "the cut condition, not total capacity", True,
                    "total capacity 3 = demand 3, but everything arrives at slot 2: cut excess 2"))

    # 11. advisor floods the docket
    I_flood = Instance([Reason("noise1", Q(0), release=0), Reason("noise2", Q(0), release=0),
                        Reason("against", W, release=0)], T=2, cap=[1, 1])
    out.append(Case("11 flooding", I_flood, "supplier capacity independent of advisor load", True,
                    "if the advisor's submissions consume the supplier's capacity, weight-0 noise "
                    "cannot crowd out the counterreason under weighted service, but FIFO would be crowded"))

    # 12. advisor influences service cost
    I_cheap = Instance([Reason("against", W, cost=1, release=0)], T=1, cap=[1])
    I_dear = Instance([Reason("against", W, cost=3, release=0)], T=1, cap=[1])
    out.append(Case("12 cost influence", I_dear, "exogenous cost profile", False,
                    "obfuscation raising the counterreason's cost from 1 to 3 defeats the cut; "
                    "the bound must be taken over the advisor's cost-influence class"))
    out[-1].alt = I_cheap

    # 13. multiple independent suppliers
    I_two = Instance([Reason("r1", W, release=0), Reason("r2", W, release=0)], T=1, cap=[2])
    I_indiv = Instance([Reason("big", W, cost=2, release=0)], T=1, cap=[2])
    out.append(Case("13 two suppliers", I_two, "capacity adds for divisible service", True,
                    "two unit suppliers serve two unit reasons; a cost-2 reason needs both units in "
                    "one slot, which is fine when service is divisible across suppliers"))
    out[-1].alt = I_indiv

    # 14. a reason impossible to discover before commitment
    I = Instance([Reason("hidden", W, release=None), Reason("seen", W, release=0)], T=1, cap=[1])
    out.append(Case("14 undiscoverable", I, "discovery loss is outside the service theorem", True,
                    "no capacity serves it; against N_full it is residual, against N_disc it is zero"))

    # 15. a reason type outside the declared ontology
    I = Instance([Reason("secret", W, release=0, declared=False), Reason("seen", W, release=0)], T=1, cap=[1])
    out.append(Case("15 undeclared type", I, "scope is external", True,
                    "reported as scope, charged to nothing: the comparator does not contain it"))

    # 16. a comparator assuming content no realizable process could produce
    I = Instance([Reason("hidden", Q(1, 2), release=None), Reason("seen", W, release=0)], T=1, cap=[1])
    out.append(Case("16 unrealizable comparator", I, "realizable supplier comparator", True,
                    "ideal regret 1/2 against N_full, realizable regret 0 against N_disc"))

    # 17. greedy is not optimal for general costs (knapsack)
    I = Instance([Reason("big", Q(3, 8), cost=2, release=0), Reason("a", W, cost=1, release=0),
                  Reason("b", W, cost=1, release=0)], T=2, cap=[1, 1])
    out.append(Case("17 greedy fails with general costs", I, "unit costs for the exact greedy", True,
                    "greedy by weight serves the cost-2 reason and misses 1/2; the optimum serves the two "
                    "unit reasons and misses 3/8"))
    return out
