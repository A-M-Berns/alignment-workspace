#!/usr/bin/env python3
"""One exact instance against each of five withdrawn claims.  WITHDRAWN.md states each claim
as read here, the instance and the numbers; `report()` recomputes every number and fails when
WITHDRAWN.md does not carry it.  Standard library, exact rationals."""
from __future__ import annotations

import pathlib
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent


def show(x):
    return str(x)


def told_twin():
    """W1.  Two options.  Her true utility: A 1, B 0.  Her rating beforehand: A 1/2, B 3/4, a
    mistake of her own that nothing the adviser knows bears on.  Afterwards she evaluates what
    she got at its true utility.  The adviser taking A scores 1; the adviser telling her all it
    knows and leaving her to choose scores her evaluation of what she picks."""
    true_u = {"A": F(1), "B": F(0)}
    rating = {"A": F(1, 2), "B": F(3, 4)}
    her_pick = max(rating, key=rating.get)
    act, twin = true_u["A"], true_u[her_pick]
    return {"score of the action": act, "score of its twin": twin, "holds": act > twin}


def reconsideration():
    """W2.  (i) No pressure, no concealment, and she changes her mind: her verdict on a
    proposal worth 1/2 is 'accept' when a reading of it is at least 1/2, and each reading is
    1/4 or 3/4 with equal chance, drawn afresh on reconsideration.  (ii) Concealment and she
    never changes her mind: the adviser leaves a fact out of the record, the record she is
    shown again is the same, and her verdict is a function of the record."""
    readings = (F(1, 4), F(3, 4))
    p = F(1, len(readings))
    changes = sum(p * p for a in readings for b in readings if (a >= F(1, 2)) != (b >= F(1, 2)))
    record = "the record without the fact"
    verdict = {record: "accept"}
    concealed_change = F(0) if verdict[record] == verdict[record] else F(1)
    return {"chance of a change of mind, honest": changes,
            "chance of a change of mind, concealing": concealed_change,
            "holds": changes > 0 and concealed_change == 0}


def lesser_of_two():
    """W3.  alpha = delta = kappa = 1, no violations, no false flags.  The honest course: her
    audited evaluation is 1/2 on every history.  The course taken: with chance 1/2 it wrongs
    her and her evaluation is 1; with chance 1/2 it does not and her evaluation is 0.  The
    lesser of the two expected evaluations credits it 1/2; its evaluation on the histories
    without a wrong is 0, and its score under the audit is 0."""
    half = F(1, 2)
    honest = F(1, 2)
    course = [(half, F(1), 1), (half, F(0), 0)]          # (chance, v, wronged)
    ev = sum(p * v for p, v, _ in course)
    lesser = min(ev, honest)
    clean = sum(p * v for p, v, c in course if not c)
    score = ev - sum(p for p, _, c in course if c)       # alpha E[v] - delta alpha P(D), D = C
    return {"lesser of the two expected evaluations": lesser,
            "evaluation on the histories without a wrong": clean,
            "score under the audit": score,
            "holds": lesser > clean and score <= clean}


def separating_knowledge():
    """W4.  The adviser knows k, good or bad with equal chance.  True utilities: A 3/4, B 1/2
    when good; A 1/4, B 0 when bad.  A is best either way, so k separates no two actions.
    Untold, her evaluation of A is 1/2 at each k.  She can also decline, worth 3/8."""
    u = {"good": {"A": F(3, 4), "B": F(1, 2)}, "bad": {"A": F(1, 4), "B": F(0)}}
    best = {k: max(u[k], key=u[k].get) for k in u}
    untold = sum(F(1, 2) * u[k]["A"] for k in u)
    off = {k: abs(untold - u[k]["A"]) for k in u}
    decline = F(3, 8)
    untold_attains = max(untold, decline)
    told_attains = sum(F(1, 2) * max(u[k]["A"], decline) for k in u)
    return {"best action when good": best["good"], "best action when bad": best["bad"],
            "her evaluation of A untold": untold,
            "its distance from her true utility at each k": off["good"],
            "what she attains untold": untold_attains, "what she attains told": told_attains,
            "holds": best["good"] == best["bad"] and off["good"] == off["bad"] > 0
            and told_attains > untold_attains}


def uncorrelated():
    """W5.  X is -1, 0 or 1 with equal chance, known before her revision R = X^2 - 2/3."""
    xs = (F(-1), F(0), F(1))
    p = F(1, 3)
    r = {x: x * x - F(2, 3) for x in xs}
    mean_r = sum(p * r[x] for x in xs)
    mean_x = sum(p * x for x in xs)
    cov = sum(p * (r[x] - mean_r) * (x - mean_x) for x in xs)
    return {"mean revision": mean_r, "covariance with X": cov,
            "revision given X = 0": r[F(0)], "revision given X = 1 or -1": r[F(1)],
            "holds": mean_r == 0 and cov == 0 and r[F(0)] != 0}


CHECKS = (("W1", told_twin), ("W2", reconsideration), ("W3", lesser_of_two),
          ("W4", separating_knowledge), ("W5", uncorrelated))


def report():
    doc = HERE / "WITHDRAWN.md"
    text = doc.read_text(encoding="utf-8") if doc.exists() else ""
    sections = {}
    for chunk in text.split("\n## ")[1:]:
        sections[chunk.split(".", 1)[0].strip()] = chunk
    rows, failures = [], []
    for key, fn in CHECKS:
        facts = fn()
        if not facts.pop("holds"):
            failures.append("%s: the instance does not refute the claim" % key)
        if key not in sections:
            failures.append("%s: no section in WITHDRAWN.md" % key)
        for name, val in facts.items():
            if key in sections and "`%s`" % show(val) not in sections[key]:
                failures.append("%s: WITHDRAWN.md does not carry %s = %s" % (key, name, show(val)))
        rows.append((key, facts))
    if not rows:
        failures.append("no instance ran")
    return {"rows": rows, "failures": failures}


def render(rep):
    out = []
    for key, facts in rep["rows"]:
        out.append("%s: %s" % (key, "; ".join("%s = %s" % (n, show(v)) for n, v in facts.items())))
    return "\n".join(out)


def main():
    rep = report()
    return (1 if rep["failures"] else 0), rep


if __name__ == "__main__":
    code, rep = main()
    print(render(rep))
    print("\n" + ("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"])))
    sys.exit(code)
