"""The two forms of the responsibility test of AGENDA.md §3, computed on the outside
reviewer's twenty cases (`resp_cases.json`, the JSON blocks of
`REVIEW-astra-followup-13.md`, first reply, unaltered).

A case gives the adviser's courses, the one taken, how mistaken she is under each, the
adviser's score under each with her acting as she does and with her acting unmistaken, and
the course a declared reference prescribes (or none).

- gain form: the adviser gains from her mistake (its score for the course taken is higher
  with her acting as she does than with her acting unmistaken) and either left her more
  mistaken than it need have (some course leaves her less mistaken) or chose differently
  because of it (with her acting unmistaken, some course scores strictly higher than the
  one taken).
- declared-reference form: there is a declared reference and the course taken is not the
  one it prescribes.

`report()` fails when RESP_RESULTS.md's table or counts are not the ones computed.
"""
from __future__ import annotations

import json
import pathlib
import re
from fractions import Fraction as Fr

HERE = pathlib.Path(__file__).resolve().parent


def load():
    return json.loads((HERE / "resp_cases.json").read_text(encoding="utf-8"))


def gain_form(c):
    t = c["taken"]
    s = {k: Fr(v) for k, v in c["score"].items()}
    su = {k: Fr(v) for k, v in c["score_unmistaken"].items()}
    m = {k: Fr(v) for k, v in c["mistaken"].items()}
    gains = s[t] > su[t]
    more = any(m[k] < m[t] for k in c["courses"])
    differently = any(su[k] > su[t] for k in c["courses"])
    return gains and (more or differently), {"gains": gains, "more": more, "differently": differently}


def declared_form(c):
    return c["declared"] is not None and c["taken"] != c["declared"]


def compute():
    rows = []
    for c in load():
        truth = c["plainly"] in ("induces", "exploits")
        g, parts = gain_form(c)
        d = declared_form(c)
        rows.append({"id": c["id"], "plainly": c["plainly"], "gain": g, "declared": d,
                     "gain_wrong": g != truth, "declared_wrong": d != truth,
                     "claimed": c["claimed_failure"], "no_reference": c["declared"] is None, **parts})
    return rows


def yn(b):
    return "convicts" if b else "clears"


def report():
    rows = compute()
    failures = []
    if len(rows) != 20 or len({r["id"] for r in rows}) != 20:
        failures.append("resp_cases.json does not hold twenty distinct cases")
    path = HERE / "RESP_RESULTS.md"
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = {m.group(1): [x.strip() for x in m.group(2).split("|")]
              for m in re.finditer(r"^\|\s*([XY]\d+)\s*\|(.*)\|\s*$", text, re.M)}
    accepted = set()
    for r in rows:
        cells = stated.get(r["id"])
        if cells is None or len(cells) < 5:
            failures.append("%s: no row in RESP_RESULTS.md" % r["id"])
            continue
        want = [r["plainly"], yn(r["gain"]), yn(r["declared"])]
        if cells[:3] != want:
            failures.append("%s: RESP_RESULTS.md says %r, computed %r" % (r["id"], cells[:3], want))
        if cells[4] == "yes":
            accepted.add(r["id"])
    counts = {
        "gain wrong of 20": sum(r["gain_wrong"] for r in rows),
        "declared wrong of 20": sum(r["declared_wrong"] for r in rows),
        "accepted": len(accepted),
        "gain wrong of accepted": sum(r["gain_wrong"] for r in rows if r["id"] in accepted),
        "declared wrong of accepted": sum(r["declared_wrong"] for r in rows if r["id"] in accepted),
        "declared wrong with no reference": sum(r["declared_wrong"] and r["no_reference"] for r in rows),
        "claims not borne out": sum(
            (r["claimed"] in ("gain", "both") and not r["gain_wrong"])
            or (r["claimed"] in ("declared", "both") and not r["declared_wrong"]) for r in rows),
    }
    for name, val in counts.items():
        if not re.search(r"^- %s: \*\*%d\*\*" % (re.escape(name), val), text, re.M):
            failures.append("RESP_RESULTS.md does not state '%s: %d'" % (name, val))
    summary = ["%s: %d" % kv for kv in counts.items()]
    return {"summary": summary, "failures": failures, "rows": rows, "counts": counts}


if __name__ == "__main__":
    rep = report()
    for r in rep["rows"]:
        print(r["id"], r["plainly"], "gain:", yn(r["gain"]), "(gains %s, more %s, differently %s)" % (r["gains"], r["more"], r["differently"]),
              "declared:", yn(r["declared"]), "| wrong:", "gain" if r["gain_wrong"] else "", "declared" if r["declared_wrong"] else "",
              "| claimed", r["claimed"])
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
