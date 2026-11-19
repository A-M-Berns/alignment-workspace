"""The small model behind BRIDGE.md, in exact rationals: the graded verdict of ACCOUNT.md section 8
turned into a predicate with a tolerance; what a tolerance gives of non-inflation and self-trust;
the thin conditions beside the three measures; the control surface beside the wide options
condition; the gate and the violation count after an issue.

`report()` compares the table of BRIDGE.md with what is computed here."""
from __future__ import annotations

import pathlib
import random
import re
from fractions import Fraction as F

from .value_results import (E, Pol, cond, conditions, in_hull, measures, rnd_pair, separator, sq,
                            standing_bias, uhat, knows_less)

HERE = pathlib.Path(__file__).resolve().parent


# -- 1. a predicate with a tolerance -----------------------------------------------------------
def defects(sig, rho, phat, f, c):
    """How far each of conditions 1 (for her own way of valuing), 2 and 3 is from holding against rho."""
    ms, mr = measures(sig, phat, f, c), measures(rho, phat, f, c)
    d1 = max(F(0), mr["best_move"] - ms["best_move"])
    d2 = max([F(0)] + [ms["M"][a] - (mr["M"][a] if a in rho.moves else 0) for a in sig.moves])
    d3 = max(F(0), ms["R"] - mr["R"])
    return d1, d2, d3


def legit(sig, P, phat, f, c, eps):
    """Some single permitted policy against which every defect is at most eps."""
    return any(max(defects(sig, rho, phat, f, c)) <= eps for rho in P)


def offer_scene():
    """She stays (worth 1/2 to her) or takes a course.  Facts: whether the course changes her.

    idle: no course.  honest: the course changes her surely, she is told and forecasts it, and
    values being changed at 1/4, so she stays.  covert: the same course, untold, forecast 0,
    valued unchanged at 1.  imposed: she is changed whatever she does."""
    f = lambda x, a: {"stay": F(1, 2), "course": F(1) if x == "same" else F(1, 4), "none": F(1, 4)}[a]
    ph = {"no offer": {"same": F(1)}, "told": {"changed": F(1)}, "untold": {"same": F(1)}, "done": {"changed": F(1)}}
    c = lambda s: {"no offer": "stay", "told": "stay", "untold": "course", "done": "none"}[s]
    pols = {"idle": Pol([(1, "same", "no offer")], ["stay"]),
            "honest offer": Pol([(1, "changed", "told")], ["stay", "course"]),
            "covert change": Pol([(1, "changed", "untold")], ["stay", "course"]),
            "imposed change": Pol([(1, "changed", "done")], ["none"])}
    # the law on the protected feature (her later way of valuing: f or f') each move gives
    later = {"idle": {"stay": [F(1), F(0)]},
             "honest offer": {"stay": [F(1), F(0)], "course": [F(0), F(1)]},
             "covert change": {"stay": [F(1), F(0)], "course": [F(0), F(1)]},
             "imposed change": {"none": [F(0), F(1)]}}
    return pols, later, (lambda s: ph[s]), f, c


def predicate_facts():
    pols, later, phat, f, c = offer_scene()
    P = [pols["idle"]]
    out = {}
    for name, sig in pols.items():
        d = defects(sig, pols["idle"], phat, f, c)
        hull = all(in_hull(d0, list(later[name].values())) is not None for d0 in later["idle"].values())
        out[name] = {"defects": d, "wide": hull,
                     "legit": {str(e): legit(sig, P, phat, f, c, e) and hull for e in (F(0), F(1, 4), F(1))}}
    assert out["idle"]["legit"] == {"0": True, "1/4": True, "1": True}
    assert out["honest offer"]["defects"] == (0, 0, 0) and out["honest offer"]["wide"]
    assert out["covert change"]["defects"] == (0, F(9, 16), 0) and out["covert change"]["wide"]
    assert out["imposed change"]["defects"] == (F(1, 4), 0, 0) and not out["imposed change"]["wide"]
    assert out["covert change"]["legit"] == {"0": False, "1/4": False, "1": True}
    # one realised trajectory, two policies, two verdicts (VALUE_RESULTS.md, result 7)
    sig, idle, phat2, f2, c2 = standing_bias()
    shared = {(x, s) for _, x, s in sig.pts} & {(x, s) for _, x, s in idle.pts}
    assert ("same", "the course") in shared
    assert max(defects(idle, idle, phat2, f2, c2)) == 0 and max(defects(sig, idle, phat2, f2, c2)) > 0
    return out


# -- 2. what a tolerance gives --------------------------------------------------------------------
def inflated_choice():
    """Each valuation calibrated given its own value; the valuation of the move she takes inflated by 1/4."""
    f = lambda x, a: F(x[0]) if a == "a" else F(x[1])
    ph = {"s1": {(0, 0): F(3, 8), (0, 1): F(1, 8), (1, 0): F(3, 8), (1, 1): F(1, 8)},
          "s2": {(0, 0): F(1, 8), (0, 1): F(3, 8), (1, 0): F(1, 8), (1, 1): F(3, 8)}}
    pts = [(F(3, 8), (0, 0), "s1"), (F(1, 8), (0, 1), "s1"), (F(1, 8), (1, 0), "s2"), (F(3, 8), (1, 1), "s2")]
    c = lambda s: "a" if s == "s1" else "b"
    return Pol(pts, ["a", "b"]), (lambda s: ph[s]), f, c


def tolerance_facts():
    rng = random.Random(921)
    n = 0
    for _ in range(300):
        sig, rho, phat, f, c = rnd_pair(rng)
        for pol in (sig, rho):
            m = measures(pol, phat, f, c)
            for a in pol.moves:
                uh = lambda x, s, a=a: uhat(phat, f, a, s)
                infl = E(pol.pts, lambda x, s: uh(x, s) - f(x, a))
                assert sq(infl) <= m["M"][a]
                for thr in (F(-1), F(0), F(1, 2), F(1)):
                    trust = E(pol.pts, lambda x, s: (f(x, a) - thr) if uh(x, s) >= thr else 0)
                    assert trust >= 0 or sq(trust) <= m["M"][a]
                n += 1
            taken = E(pol.pts, lambda x, s: uhat(phat, f, c(s), s) - f(x, c(s)))
            assert sq(taken) <= m["Mbar"] + m["Wbar"]
    pol, phat, f, c = inflated_choice()
    m = measures(pol, phat, f, c)
    taken = E(pol.pts, lambda x, s: uhat(phat, f, c(s), s) - f(x, c(s)))
    assert m["Mbar"] == 0 and m["R"] == 0 and taken == F(1, 4) and m["Wbar"] == F(1, 4)
    return {"valuations": n, "inflation of the move she takes with every valuation calibrated": taken}


# -- 3. the thin conditions ---------------------------------------------------------------------------
def thin_facts():
    rng = random.Random(923)
    n = 0
    for _ in range(200):
        sig, rho, phat, f, c = rnd_pair(rng, calibrated_sigma=True)
        m = measures(sig, phat, f, c)
        assert all(m["M"][a] == 0 and m["W"][a] == 0 for a in sig.moves)
        n += 1
    # calibrated valuations, an appraisal that is not the conditional law: a fair fact she observes, appraised at 1/2,
    # with a way of valuing that does not depend on the fact
    f = lambda x, a: F(1) if a == "a" else F(0)
    phat = lambda s: {0: F(1, 2), 1: F(1, 2)}
    pol = Pol([(F(1, 2), 0, "saw 0"), (F(1, 2), 1, "saw 1")], ["a", "b"])
    m = measures(pol, phat, f, lambda s: "a")
    assert m["Mbar"] == 0 and m["Wbar"] == 0
    post = cond(pol.pts, lambda x, s: s, lambda x, s: x)
    assert post(0, "saw 0") != phat("saw 0")[1]
    # the three conditions hold and the reference is not a garbling of what she observes
    sig, rho, phat, f, c = knows_less()
    ms, mr = measures(sig, phat, f, c), measures(rho, phat, f, c)
    assert conditions(sig, rho, ms, mr, f) == (True, True, True) and ms["best_rule"] < mr["best_rule"]
    return {"laws with the appraisal the conditional law": n}


# -- 4. the control surface -----------------------------------------------------------------------------
def surface_facts():
    """Outcomes: her later way of valuing is f or f'.  Under idle she keeps f surely."""
    idle = [[F(1), F(0)]]
    cases = {
        "an offer she can refuse": ([[F(1), F(0)], [F(0), F(1)]], "her"),
        "a default she can undo": ([[F(1), F(0)], [F(0), F(1)]], "the adviser"),
        "a change with no way back": ([[F(0), F(1)]], "the adviser"),
        "a way back that works half the time": ([[F(1, 2), F(1, 2)], [F(0), F(1)]], "the adviser"),
    }
    out = {}
    for name, (laws, resolver) in cases.items():
        hull = all(in_hull(d0, laws) is not None for d0 in idle)
        # the model's convention, not the module's: a value is reachable when some move gives it positive probability
        reach = all(any(all(d[j] > 0 for j in range(2) if d0[j] > 0) for d in laws) for d0 in idle)
        margin = max(separator(d0, laws)[0] for d0 in idle)
        assert hull == (margin == 0)
        out[name] = {"wide options": hull, "clause 1 (in the surface)": reach,
                     "clause 2 (resolved by the holder)": resolver == "her"}
    assert out["an offer she can refuse"] == {"wide options": True, "clause 1 (in the surface)": True, "clause 2 (resolved by the holder)": True}
    assert out["a default she can undo"] == {"wide options": True, "clause 1 (in the surface)": True, "clause 2 (resolved by the holder)": False}
    assert out["a change with no way back"] == {"wide options": False, "clause 1 (in the surface)": False, "clause 2 (resolved by the holder)": False}
    assert out["a way back that works half the time"] == {"wide options": False, "clause 1 (in the surface)": True, "clause 2 (resolved by the holder)": False}
    return out


# -- 5. the gate and the count after an issue ----------------------------------------------------------------
def gate_facts(delta=F(1), lam=F(3), window=F(-1, 2), honest=F(1, 2), changed=F(1), by_old=F(0)):
    """Decision 0: an honest act or an illegitimate change of her way of valuing.  Then T decisions over a
    clean segment, each scored by her verdict: `honest` on the honest path, `changed` after the change
    (worth `by_old` by the way of valuing she had)."""
    assert delta > 0 and lam > 1 + delta and -delta <= window < 0 and 0 <= honest <= 1 and 0 <= changed <= 1
    def total(T, counted, gated):
        first = (window if gated else changed) - (lam if counted else 0)
        return first + T * changed, honest + T * honest
    def first_T(counted, gated):
        return next(T for T in range(0, 1000) if total(T, counted, gated)[0] > total(T, counted, gated)[1])
    out = {"score of decision 0, change counted and gated": total(0, True, True)[0],
           "score of decision 0, honest": total(0, True, True)[1],
           "least clean run after which the change scores more, counted and gated": first_T(True, True),
           "the same, gated and not counted": first_T(False, True),
           "the same, neither": first_T(False, False),
           "her utility by the way of valuing she had, per later decision": (by_old, honest)}
    assert total(0, True, True)[0] < total(0, True, True)[1]
    # the dominance theorem's lower bound (weight - D) * Pr(violation) is positive when the violating branch's
    # ordinary value, gated at decision 0 and by her changed verdict after, stays below the weight
    out["longest clean run with the violating branch's ordinary value below the weight"] = \
        max(T for T in range(0, 1000) if window + T * changed < lam)
    # tainting every later segment instead
    assert all(window - lam + T * window < honest + T * honest for T in range(0, 50))
    return out


FACTS = {
    "covert change: defects against idle (options, accuracy, self-command)": lambda: ", ".join(str(v) for v in predicate_facts()["covert change"]["defects"]),
    "imposed change: defects against idle": lambda: ", ".join(str(v) for v in predicate_facts()["imposed change"]["defects"]),
    "inflation of the valuation of the move she takes, every valuation calibrated": lambda: str(tolerance_facts()["inflation of the move she takes with every valuation calibrated"]),
    "score of decision 0 after a counted, gated change": lambda: str(gate_facts()["score of decision 0, change counted and gated"]),
    "least clean run after which the change scores more: counted and gated": lambda: str(gate_facts()["least clean run after which the change scores more, counted and gated"]),
    "least clean run after which the change scores more: gated, not counted": lambda: str(gate_facts()["the same, gated and not counted"]),
    "least clean run after which the change scores more: neither": lambda: str(gate_facts()["the same, neither"]),
    "longest clean run for which the dominance theorem's lower bound is positive": lambda: str(gate_facts()["longest clean run with the violating branch's ordinary value below the weight"]),
}


def report():
    text = (HERE / "BRIDGE.md").read_text(encoding="utf-8")
    stated = dict(re.findall(r"^\|\s*([^|]+?)\s*\|\s*`([^`]*)`\s*\|\s*$", text, flags=re.M))
    failures = []
    if not stated:
        failures.append("BRIDGE.md's table parsed to nothing")
    thin_facts()
    surface = surface_facts()
    for key, fn in FACTS.items():
        got = fn()
        if stated.get(key) != got:
            failures.append("%s: BRIDGE.md says %r, computed %r" % (key, stated.get(key), got))
    summary = ["%s: %s" % (k, fn()) for k, fn in FACTS.items()]
    summary += ["surface, %s: %s" % (k, v) for k, v in surface.items()]
    return {"summary": summary, "failures": failures}


if __name__ == "__main__":
    rep = report()
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
