"""Compute a case's verdict from the clause predicates."""
from __future__ import annotations

from .clauses import l0 as L0, l1 as L1, l2 as L2, l3 as L3, w as W, coverage as COV
from .individuation import BY_NAME
from .model import run

CLAUSES = ("L0", "L1", "L2", "L3", "W")


def runs_of(v):
    return {name: run(script, v.e, v.s0, v.seed_after) for name, script in v.policies.items()}


def clause_results(v, runs, individuation=None):
    ind = BY_NAME[individuation or v.individuation]
    return {
        "L0": L0.holds(runs, v.e),
        "L1": L1.l1(runs, ind),
        "L2": L2.l2(runs, v.e),
        "L3": L3.holds(runs),
        "W": W.w(runs, ind, v.merit_pairs),
    }


def failing(results, ablate=()):
    out = []
    for c in CLAUSES:
        if c in ablate:
            continue
        r = results[c]
        bad = (r["fine"] or r["coarse"]) if c == "W" else r
        if bad:
            out.append(c)
    return out


def variant_verdict(v, ablate=(), individuation=None):
    runs = runs_of(v)
    results = clause_results(v, runs, individuation)
    bad = failing(results, ablate)
    cov = COV.coverage(runs[v.actual], v.e)
    if "W" in bad:
        category = "ill-formed"
    elif bad:
        category = "illegitimate"
    else:
        category = "legitimate"
    if category == "legitimate":
        formation = "formed" if not cov else "not-formed(coverage)"
    elif category == "illegitimate":
        formation = "not-formed"
    else:
        formation = "-"
    return {"category": category, "failing": bad, "formation": formation,
            "results": results, "runs": runs, "coverage": cov,
            "pairs": L1.trace_equal_pairs(runs, BY_NAME[individuation or v.individuation])}


def case_verdict(case, ablate=(), individuation=None):
    vs = [(v.name, variant_verdict(v, ablate, individuation)) for v in case.variants]
    first = vs[0][1]
    agree = all(x["category"] == first["category"] and x["failing"] == first["failing"]
                for _, x in vs)
    if case.mode == "plain":
        out = dict(first)
    elif case.mode == "same":
        out = dict(first) if agree else {"category": "divergent-variants", "failing": [], "formation": "-"}
    elif case.mode == "individuation":
        out = dict(first) if agree else {"category": "individuation-dependent", "failing": [], "formation": "-"}
    elif case.mode == "parameter":
        out = dict(first) if agree else {"category": "out-of-scope", "failing": [], "formation": "-",
                                         "reason": case.reason}
    else:
        raise ValueError(case.mode)
    out["variants"] = vs
    return out


def verdict_string(v):
    c = v["category"]
    if c == "illegitimate":
        return "illegitimate(%s)" % ",".join(v["failing"])
    if c == "out-of-scope":
        return "out-of-scope(%s)" % v.get("reason", "?")
    return c
