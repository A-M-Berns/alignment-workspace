"""The third-pass countermodels: discovery under pressure (dispatch §12).

Each case is an inquiry model (or a pair, for a contrast), the residual quantity on it,
and the interface that catches the failure: discovery, service, authentication, ontology,
effect-side containment, or an audit/causal-contract failure.
"""
from fractions import Fraction as Q

from .inquiry import Inquiry, Action, query
from .sensitivity import WeightedCount, Defeat, Redundant

W = Q(1, 4)


def wc(weights, base=Q(1, 2)):
    return WeightedCount(weights, base)


class DCase:
    def __init__(self, name, inq, failure, note, alt=None, budget=None):
        self.name, self.inq, self.failure, self.note, self.alt, self.budget = name, inq, failure, note, alt, budget

    def report(self):
        I = self.inq
        out = {"name": self.name, "failure": self.failure}
        if I is not None:
            out["obstruction"] = I.obstruction()
            if self.budget is not None:
                out["minimax"] = I.minimax(B=self.budget)
                out["nonadaptive"] = I.nonadaptive(self.budget)
        return out


def cases():
    out = []

    # 1. one hidden high-adverse counterreason with a direct available query
    I = Inquiry({"w0": set(), "w1": {"against"}}, [query("against")], wc({"for": W, "against": -W}), pro={"for"})
    out.append(DCase("1 hidden counterreason, direct query", I, "discovery (closed)",
                     "one query determines it: obstruction 0", budget=1))

    # 2. two reasons, one query budget
    I = Inquiry({"w0": set(), "w1": {"a"}, "w2": {"b"}, "w3": {"a", "b"}},
                [query("a"), query("b")], wc({"a": -W, "b": -W}))
    out.append(DCase("2 two reasons, one query", I, "discovery (budget)",
                     "repertoire obstruction 0; with one query the worst case leaves W", budget=1))

    # 3. many low-value distractors plus one high-value hidden counterreason
    worlds = {"w0": set()}
    for i in range(4):
        worlds[f"d{i}"] = {f"lo{i}"}
    worlds["hi"] = {"hi"}
    acts = [query(f"lo{i}") for i in range(4)] + [query("hi")]
    I = Inquiry(worlds, acts, wc({**{f"lo{i}": -Q(1, 16) for i in range(4)}, "hi": -Q(1, 2)}))
    out.append(DCase("3 distractors and one heavy reason", I, "discovery (prioritization)",
                     "greedy by conditional adverse mass asks about `hi` first: one query suffices "
                     "for the heavy reason, the light ones cost 1/16 each", budget=1))

    # 4. advisor floods the search space with heavy-but-false candidates
    worlds = {"w0": set(), "wt": {"against"}}
    acts = [query(f"fake{i}") for i in range(3)] + [query("against")]
    I_flood = Inquiry(worlds, acts, wc({"against": -W, **{f"fake{i}": -W for i in range(3)}}))
    out.append(DCase("4 flooding with false heavy candidates", I_flood, "discovery (independence of candidate generation)",
                     "the fake candidates are false in every world: undetermined in no cell, so they are "
                     "not on the frontier; a FIFO engine that must test every candidate wastes 3 queries", budget=1))

    # 5. inquiry cost manipulated by the advisor
    I_cheap = Inquiry({"w0": set(), "w1": {"against"}}, [query("against", 1)], wc({"against": -W}))
    I_dear = Inquiry({"w0": set(), "w1": {"against"}}, [query("against", 3)], wc({"against": -W}))
    out.append(DCase("5 cost manipulation", I_dear, "discovery (exogenous costs: hypothesis)",
                     "at budget 1 the cheap query closes the residual, the obfuscated one cannot",
                     alt=I_cheap, budget=1))

    # 6. discovering one reason reveals another (a test whose outcome carries both)
    worlds = {"w0": set(), "w1": {"a"}, "w2": {"a", "b"}}
    joint = Action("test:a,b", 1, lambda t: ("a" in t, "b" in t))
    I = Inquiry(worlds, [query("a"), query("b"), joint], wc({"a": -W, "b": -W}))
    out.append(DCase("6 one test reveals two reasons", I, "discovery (repertoire structure)",
                     "the joint test closes the residual with one unit; direct queries need two", budget=1))

    # 7. discovering a pro reason creates a defeater obligation
    # the advisor's `for` is defeated by `d`; `d` is adverse; `against` is a plain counterreason
    F7 = Defeat({"for": W, "against": -W}, {"for": {"d"}})
    worlds = {"w0": set(), "wd": {"d"}, "wa": {"against"}, "wda": {"d", "against"}}
    I = Inquiry(worlds, [query("d"), query("against")], F7, pro={"for"})
    out.append(DCase("7 defeater obligation", I, "discovery (defeat closure)",
                     "with `for` on the docket, `d` has conditional adverse mass W: an obligation; "
                     "both queries close it", budget=2))

    # 8. mutually defeating reasons: `x` defeats `y` and `y` defeats `x` (both adverse to `for`?)
    # here: counterreason `c` (adverse) is defeated by `e`; `e` is pro, so not in the inquiry universe:
    # once `e` is known (advisor supplies it), `c`'s conditional adverse mass is 0
    F8 = Defeat({"for": W, "c": -W}, {"c": {"e"}})
    I_without = Inquiry({"w0": set(), "w1": {"c"}}, [query("c")], F8, pro={"for"})
    I_with = Inquiry({"w0": set(), "w1": {"c"}}, [query("c")], F8, pro={"for", "e"})
    out.append(DCase("8 defeated counterreason", I_without, "discovery (conditional mass)",
                     "without the defeater the counterreason is an obligation (mass W); with the advisor's "
                     "defeater on the docket its conditional adverse mass is 0 and the frontier is empty",
                     alt=I_with, budget=1))

    # 9. redundant reasons: any of two establishes the counter-conclusion
    F9 = Redundant([(-W, {"r1", "r2"})])
    worlds = {"w0": set(), "w1": {"r1"}, "w2": {"r2"}, "w12": {"r1", "r2"}}
    I = Inquiry(worlds, [query("r1"), query("r2")], F9)
    out.append(DCase("9 redundant reasons", I, "discovery (residual is the direct gain)",
                     "the additive mass double-counts; the gap is W, and after one true answer the "
                     "other reason's conditional mass is 0", budget=1))

    # 10. reason truth determined only by an expensive empirical test
    I = Inquiry({"w0": set(), "w1": {"against"}}, [query("against", 5)], wc({"against": -W}))
    out.append(DCase("10 expensive test", I, "discovery (budget) — authentication if the test is the certificate",
                     "repertoire obstruction 0; below cost 5 the residual is W", budget=4))

    # 11. ontology contains the reason but the repertoire cannot distinguish it
    I = Inquiry({"w0": set(), "w1": {"against"}}, [Action("noise", 1, lambda t: 0)], wc({"against": -W}))
    out.append(DCase("11 undistinguishable by the repertoire", I, "discovery (repertoire obstruction)",
                     "one cell containing both worlds: obstruction W whatever the budget", budget=100))

    # 12. two worlds observationally indistinguishable with different principal values
    I = Inquiry({"w0": set(), "w1": {"a"}, "w2": {"a", "b"}},
                [query("a")], wc({"a": -Q(1, 8), "b": -W}))
    out.append(DCase("12 indistinguishable worlds, different values", I, "discovery (information cell)",
                     "w1 and w2 share the cell {a}: the gap W is the exact residual", budget=100))

    # 13. all reasons discoverable eventually but not before commitment: modeled as budget < need
    worlds = {"w0": set(), "w1": {"a"}, "w2": {"b"}, "w3": {"c"}}
    I = Inquiry(worlds, [query("a"), query("b"), query("c")], wc({"a": -W, "b": -W, "c": -W}))
    out.append(DCase("13 discoverable but not in time", I, "discovery (budget) — service if docketed late",
                     "three units close it; two leave W in the worst case", budget=2))

    # 14. the needle: n candidates each true in one world; no fractional progress
    n = 4
    worlds = {"none": set(), **{f"w{i}": {f"r{i}"} for i in range(n)}}
    I = Inquiry(worlds, [query(f"r{i}") for i in range(n)], wc({f"r{i}": -W for i in range(n)}))
    out.append(DCase("14 needle: no fractional progress", I, "discovery (budget; adaptivity useless)",
                     "the worst-case residual stays W until the last query: minimax W at budget n−1, 0 at n",
                     budget=n - 1))

    # 15. adaptive inquiry dramatically outperforms nonadaptive: a chain of implications
    # worlds w_k = {a_1..a_k}; a "level" query at k reveals whether ≥ k reasons hold (binary search)
    m = 3
    worlds = {f"w{k}": {f"a{j}" for j in range(1, k + 1)} for k in range(m + 1)}
    levels = [Action(f"lvl≥{k}", 1, (lambda k: lambda t: len(t) >= k)(k)) for k in range(1, m + 1)]
    I = Inquiry(worlds, levels, wc({f"a{j}": -Q(1, 8) for j in range(1, m + 1)}))
    out.append(DCase("15 adaptive vs nonadaptive", I, "discovery (adaptivity)",
                     "four worlds: binary search closes the residual with 2 queries; any fixed pair of "
                     "level queries leaves a cell of gap 1/8", budget=2))

    # 16. advisor controls stopping
    I = Inquiry({"w0": set(), "w1": {"against"}}, [query("against")], wc({"against": -W}))
    out.append(DCase("16 advisor controls stopping", I, "discovery (independence of the policy)",
                     "the policy that stops at once leaves W; the frontier is nonempty, so stopping "
                     "violates the frontier obligation", budget=1))

    # 17. honest but resource-bounded engine: same as 2/13, the budget is the obstruction
    I = Inquiry({"w0": set(), "w1": {"a"}, "w2": {"b"}}, [query("a"), query("b")], wc({"a": -W, "b": -W}))
    out.append(DCase("17 honest, resource-bounded", I, "discovery (budget)",
                     "with one unit the worst case leaves W; two close it", budget=1))

    # 18. reason outside the ontology: not in the universe at all
    I = Inquiry({"w0": set(), "w1": set()}, [query("against")], wc({"against": -W}))
    out.append(DCase("18 outside the ontology", I, "ontology (external)",
                     "the worlds do not carry the reason; the model's obstruction is 0 and the theory "
                     "does not see the omission", budget=1))

    # 19. insufficient granularity: one id for two facts of different force
    I = Inquiry({"w-weak": {"g"}, "w-strong": {"g"}}, [query("g")], wc({"g": -W}))
    out.append(DCase("19 insufficient granularity", I, "ontology (external)",
                     "both worlds docket `g`; the program cannot see which fact it stood for", budget=1))

    # 20. perfect discovery but the service cut fails: handled by the supply model
    out.append(DCase("20 discovered, unserved", None, "service",
                     "see `attacks_second_pass` case 1: discovery loss 0, service loss W"))
    return out
