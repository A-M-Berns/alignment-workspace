"""Nine candidate tests of "acts manipulatively", computed on the outside reviewer's forty
cases (`intent_cases.json`, the JSON block of its second reply in
`REVIEW-astra-followup-15.md`, unaltered).

A case gives the adviser's courses, the one taken (`t`), a non-interfering default (`d`),
named mistakes `m`, and by the adviser's own beliefs: `p[m][c]`, its credence that course
`c` produces or sustains `m`; `u[c]`, its expected value of `c`; `u_if_no[m][c]` and
`u_if_given[m][c]`, that value were `m` not to occur, or to occur regardless; the same with
all listed mistakes blocked or granted together.  `avail` is the other available courses and
`ref` is `avail` with the default added.

Six tests put to the reviewer, each "some mistake m qualifies":

- F: some available course makes m less likely than t does.
- D: F, and t is worth more than it would be were m not to occur.
- R1: `p[m][t] > 0`, and were m not to occur under t, some available course would be
  strictly better than t.
- R1s: R1, or the same with all listed mistakes blocked together.
- R2: `p[m][t] > 0`; t is strictly better than every course in `ref`; and were m to occur
  whatever is done, some course in `ref` would be at least as good as t.
- R4: R1s, and she did not validly ask for m.

Three later forms:

- G0: she did not ask for m, and some course in `ref` makes m less likely than t and is at
  least as good as t were m to occur regardless.
- G: G0, and t makes m more likely than the default does.
- S: for each course, its value with the damage undone is `u` with the mistakes it makes
  more likely than the default blocked; its gain is `u` less that.  t qualifies when some
  course in `ref` has value-with-damage-undone at least t's and less gain, unless every
  mistake t may produce is one she asked for.  This is the avoidable-gain test of
  MISTAKES_ACCOUNT.md §3 in an earlier form: it has no separate term for what her mistakes
  cost the adviser, and it reads damage off the case's blocked values.

Verdict under a test: *neither* if no mistake qualifies; *manipulates* if a qualifying
mistake actually occurred and the effect was as intended; otherwise *acts manipulatively
only*.  A test is right on a case when its verdict is the reviewer's `plainly`.

`report()` fails when INTENT_RESULTS.md's rows or counts are not the ones computed.
"""
from __future__ import annotations

import json
import pathlib
import re
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
TESTS = ["F", "D", "R1", "R1s", "R2", "R4", "G0", "G", "S"]
SHORT = {"manipulates": "M", "acts manipulatively only": "A", "neither": "-"}


def load():
    return json.loads((HERE / "intent_cases.json").read_text(encoding="utf-8"))


def qualifying(c, test):
    t = c["taken"]
    avail = [x for x in c["courses"] if x != t]
    d = c["default"]
    ref = list(avail) + ([d] if d not in avail and d != t else [])
    u = {k: F(v) for k, v in c["u"].items()}
    out = []

    def block(m):
        un = F(c["u_if_no"][m][t])
        return any(un < u[o] for o in avail)

    def block_all():
        if "u_if_no_all" not in c:
            return False
        un = F(c["u_if_no_all"][t])
        return any(un < u[o] for o in avail)

    for m in c["mistakes"]:
        p = {k: F(v) for k, v in c["p"][m].items()}
        asked = m in c.get("asked_for", [])
        if test == "F":
            ok = any(p[t] > p[o] for o in avail)
        elif test == "D":
            ok = any(p[t] > p[o] for o in avail) and u[t] > F(c["u_if_no"][m][t])
        elif test == "R1":
            ok = p[t] > 0 and block(m)
        elif test in ("R1s", "R4"):
            ok = p[t] > 0 and (block(m) or block_all()) and not (test == "R4" and asked)
        elif test == "R2":
            ug = c["u_if_given"][m]
            ok = (p[t] > 0 and all(u[t] > u[o] for o in ref if o in u)
                  and any(F(ug[o]) >= F(ug[t]) for o in ref if o in ug))
        elif test in ("G0", "G"):
            ug = c["u_if_given"][m]
            ok = (not asked and any(p.get(o, F(0)) < p[t] and F(ug[o]) >= F(ug[t]) for o in ref if o in ug)
                  and (test == "G0" or p[t] > p.get(d, F(0))))
        else:
            raise ValueError(test)
        if ok:
            out.append(m)
    return out


def qualifying_S(c):
    t = c["taken"]
    avail = [x for x in c["courses"] if x != t]
    d = c["default"]
    ref = list(avail) + ([d] if d not in avail and d != t else [])
    u = {k: F(v) for k, v in c["u"].items()}
    undone = {}
    for o in u:
        raised = [m for m in c["mistakes"] if o in c["p"][m] and F(c["p"][m][o]) > F(c["p"][m].get(d, "0"))]
        undone[o] = u[o] if not raised else (F(c["u_if_no"][raised[0]][o]) if len(raised) == 1 else F(c["u_if_no_all"][o]))
    gain = {k: u[k] - undone[k] for k in undone}
    ms = [m for m in c["mistakes"] if F(c["p"][m][t]) > 0]
    if ms and all(m in c.get("asked_for", []) for m in ms):
        return []
    return ms if any(o in undone and undone[o] >= undone[t] and gain[o] < gain[t] for o in ref) else []


def verdict(c, test):
    q = qualifying_S(c) if test == "S" else qualifying(c, test)
    if not q:
        return "neither"
    if any(c["actual"].get(m) for m in q) and c["effect_as_intended"]:
        return "manipulates"
    return "acts manipulatively only"


def compute():
    rows = []
    for c in load():
        vs = {test: verdict(c, test) for test in TESTS}
        rows.append({"id": c["id"], "plainly": c["plainly"], "confidence": c["confidence_in_plainly"],
                     "other_wrong": c["other_wrong"], "verdicts": vs,
                     "right": {test: vs[test] == c["plainly"] for test in TESTS}})
    return rows


def mark(r, test):
    return SHORT[r["verdicts"][test]] + ("" if r["right"][test] else " x")


def report():
    rows = compute()
    failures = []
    if len(rows) != 40 or len({r["id"] for r in rows}) != 40:
        failures.append("intent_cases.json does not hold forty distinct cases")
    path = HERE / "INTENT_RESULTS.md"
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = {m.group(1): [x.strip() for x in m.group(2).split("|")]
              for m in re.finditer(r"^\|\s*([ALB]\d+)\s*\|(.*)\|\s*$", text, re.M)}
    for r in rows:
        want = [SHORT[r["plainly"]], r["confidence"]] + [mark(r, test) for test in TESTS]
        if stated.get(r["id"]) != want:
            failures.append("%s: INTENT_RESULTS.md says %r, computed %r" % (r["id"], stated.get(r["id"]), want))
    high = [r for r in rows if r["confidence"] == "high"]
    counts = {}
    for test in TESTS:
        counts["%s right of 40" % test] = sum(r["right"][test] for r in rows)
        counts["%s right of the %d of high confidence" % (test, len(high))] = sum(r["right"][test] for r in high)
    for name, val in counts.items():
        if not re.search(r"^- %s: \*\*%d\*\*" % (re.escape(name), val), text, re.M):
            failures.append("INTENT_RESULTS.md does not state '%s: %d'" % (name, val))
    misses = {test: [r["id"] for r in rows if not r["right"][test]] for test in TESTS}
    summary = ["%s: %d of 40" % (test, counts["%s right of 40" % test]) for test in TESTS]
    return {"summary": summary, "failures": failures, "rows": rows, "counts": counts, "misses": misses}


if __name__ == "__main__":
    rep = report()
    print("| | plainly | confidence | " + " | ".join(TESTS) + " |")
    print("|---|---|---|" + "---|" * len(TESTS))
    for r in rep["rows"]:
        print("| %s | %s | %s | %s |" % (r["id"], SHORT[r["plainly"]], r["confidence"], " | ".join(mark(r, t) for t in TESTS)))
    print()
    for k, v in rep["counts"].items():
        print("- %s: **%d**" % (k, v))
    for t in TESTS:
        print(t, "misses:", ", ".join(rep["misses"][t]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
