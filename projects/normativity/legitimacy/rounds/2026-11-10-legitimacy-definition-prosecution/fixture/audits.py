"""§5b satisfiability and non-vacuity; §5c vocabulary attacks on W; the
triviality audit; and the replay-F reading of L1, reported beside the pairwise one."""
from __future__ import annotations

from fractions import Fraction as Q

from .case import Variant, d0, honest_pair
from .cases.b4 import extra_reason
from .clauses import l1 as L1, w as W
from .evaluate import clause_results, failing, runs_of, variant_verdict
from .individuation import BY_NAME
from .model import Event, initial_state, replay, with_actions


def honest_class():
    """V0: four honest advisors on one history; H3 and H4 add different licensed
    reasons, so F is not constant on V0."""
    cat = {"d0": d0()}
    e = [Event(due={"d0"}), Event(), Event(autonomous=("judge",))]
    pol = honest_pair(e, cat)
    pol["H3"] = with_actions(dict(pol["H1"], name="H3"), 1, extra_reason())
    pol["H4"] = with_actions(dict(pol["H1"], name="H4"), 1, extra_reason(Q(1, 8), ("gq",)))
    return Variant("V0", e, pol, initial_state(beliefs={"chi": Q(2, 3)}))


def satisfiability():
    v = honest_class()
    runs = runs_of(v)
    F = {name: replay(v.e, v.s0, r.L, v.seed_after).z_trace for name, r in runs.items()}
    factor_ok = all(F[name] == runs[name].z_trace for name in runs)
    nonconstant = len(set(tuple(z) for z in F.values())) > 1
    pairs = L1.trace_equal_pairs(runs, BY_NAME["house"])
    res = clause_results(v, runs)
    clean = failing(res) == []
    return {"ok": factor_ok and nonconstant and bool(pairs) and clean,
            "factor_equation_holds": factor_ok, "F_nonconstant": nonconstant,
            "trace_equal_pairs": pairs, "clauses_hold_on_V0": clean,
            "members": sorted(runs)}


def replay_form(case):
    """Per policy of the primary variant: does Z* equal F(e, L) with F the canonical
    replay?  The single-run reading of L1, reported and not adopted."""
    v = case.primary
    runs = runs_of(v)
    out = {}
    for name, r in runs.items():
        out[name] = replay(v.e, v.s0, r.L, v.seed_after).z_trace == r.z_trace
    return out


def coarse_convicts_b4(case_b4):
    v = case_b4.primary
    verdict = variant_verdict(v, individuation="coarse")
    runs = verdict["runs"]
    w = W.w(runs, BY_NAME["coarse"], v.merit_pairs)
    return {"ok": "L1" in verdict["failing"], "failing": verdict["failing"],
            "l1_pairs": {str(k): val for k, val in verdict["results"]["L1"].items()},
            "w_fine_fails": bool(w["fine"])}


def refined_acquits_t10(case_t10):
    v = case_t10.primary
    verdict = variant_verdict(v, individuation="refined", ablate=("W",))
    runs = verdict["runs"]
    w = W.w(runs, BY_NAME["refined"], v.merit_pairs)
    return {"ok": verdict["category"] == "legitimate", "category": verdict["category"],
            "failing": verdict["failing"], "pairs": verdict["pairs"],
            "w_coarse_fails": bool(w["coarse"])}


def triviality(verdicts):
    cats = [v["category"] for v in verdicts.values()]
    return {"ok": "legitimate" in cats and "illegitimate" in cats,
            "legitimate": sum(c == "legitimate" for c in cats),
            "illegitimate": sum(c == "illegitimate" for c in cats)}


def realized_transition_reading(run, e):
    """The trace reading of L0 the definition does not use: at each decision the
    realized world change equals e's consequence of the chosen option.  True means
    that reading acquits."""
    from .model import _freeze
    for t, ev in enumerate(e):
        if ev.decide is None:
            continue
        chosen = [d for (s, d) in run.z_trace[t][6] if s == t]
        if not chosen:
            return False
        opt = chosen[0]
        if opt not in ev.decide.options:
            continue
        before = dict(run.world_trace[t - 1]) if t else {}
        after = dict(run.world_trace[t])
        delta = {g: after.get(g, Q(0)) - before.get(g, Q(0)) - Q(ev.world.get(g, 0))
                 for g in set(before) | set(after) | set(ev.world)}
        delta = {g: x for g, x in delta.items() if x != 0}
        if _freeze(delta) != _freeze({g: Q(x) for g, x in ev.decide.options[opt].items() if Q(x) != 0}):
            return False
    return True


def extras(case):
    """Per-policy diagnostics the report reads: endpoint judgment, anchor,
    decisions, grounds-bearing contributions; B3's endpoint-only reading; T1's
    realized-transition reading."""
    v = case.primary
    runs = runs_of(v)
    out = {}
    for name, r in runs.items():
        z = r.z_trace[-1]
        out[name] = {"judgment": z[4], "anchor": z[5], "decisions": z[6],
                     "values": z[1], "reason_giving": r.reason_giving, "L_len": len(r.L)}
    if case.id == "B3":
        out["endpoint_only_L1_pairs"] = list(L1.endpoint_only(runs, BY_NAME["house"]))
        out["process_L1_positions"] = {str(k): x for k, x in L1.l1(runs, BY_NAME["house"]).items()}
    if case.id == "T1":
        out["realized_transition_reading_acquits"] = {n: realized_transition_reading(r, v.e) for n, r in runs.items()}
    return out
