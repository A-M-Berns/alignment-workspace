"""The interpretation: the history model of history_model.py on its episodes.

`report()` runs every episode of the five regression files and fails on one whose verdict is not its expectation; runs
the episodes of known_faults.py and fails on one whose verdict is not the one recorded there (the wrong verdict on
seven, the right one on one); and fails when a table row of INTERPRETATION.md is not among those computed, or the
reverse, or when nothing is computed.
"""
from __future__ import annotations

import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
DOC = "INTERPRETATION.md"
FILES = ("episodes_core", "episodes_views", "episodes_review12", "episodes_review13", "episodes_hard_cases")
# what an episode writes by hand, by the field of the model it supplies
SUPPLIED = (("told", "T"), ("seen", "S"), ("view", "V"), ("work", "W"), ("drift", "D"), ("novel", "N"), ("settled", "Z"), ("others", "O"))


def supplied(ep):
    from . import history_model as hm
    return "".join(mark for field, mark in SUPPLIED if getattr(ep, field) is not hm.DEFAULTS[field]) or "none"


def compute():
    """rows: (file, number, section, name, expected, got, why, supplied); faults: (letter, name, should, recorded, got, why)."""
    import importlib
    from . import history_model as hm
    rows, faults = [], []
    for f in FILES:
        mod = importlib.import_module("." + f, __name__)
        for n, (section, name, ep, want) in enumerate(mod.EPISODES, 1):
            got, why = hm.legit(ep)
            rows.append((f, n, section, name, want, got, why, supplied(ep)))
    kf = importlib.import_module(".known_faults", __name__)
    for letter, name, ep, want in kf.EPISODES:
        got, why = hm.legit(ep)
        faults.append((letter, name, want, kf.RECORDED[letter], got, why))
    return rows, faults


def render(rows=None, faults=None):
    if rows is None:
        rows, faults = compute()
    lines = ["| `%s` %d | %s | %s | %s | %s |" % (f, n, name.replace("|", "/"), got, why or "—", sup) for f, n, _, name, _, got, why, sup in rows]
    lines += ["| review 14, %s | %s | %s | %s | %s |" % (letter, name.replace("|", "/"), should, got, why or "—") for letter, name, should, _, got, why in faults]
    return lines


def report():
    failures = []
    rows, faults = compute()
    for f, n, _, name, want, got, _, _ in rows:
        if got != want:
            failures.append("%s %d (%s): expected %s, the model gives %s" % (f, n, name, want, got))
    for letter, name, should, recorded, got, _ in faults:
        if got != recorded:
            failures.append("known fault %s (%s): recorded %s, the model now gives %s" % (letter, name, recorded, got))
    if not rows or not faults:
        failures.append("nothing computed")
    lines = render(rows, faults)
    path = HERE / DOC
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = [l for l in text.splitlines() if re.match(r"^\| (`episodes_\w+` \d+|review 14, [A-H]) \|", l)]
    for l in lines:
        if l not in stated:
            failures.append("%s does not state: %s" % (DOC, l))
    for l in stated:
        if l not in lines:
            failures.append("%s states what is not computed: %s" % (DOC, l))
    wrong = sum(should != got for _, _, should, _, got, _ in faults)
    summary = ["%d episodes, %d as expected" % (len(rows), sum(r[4] == r[5] for r in rows)),
               "%d episodes of known faults: the model gives the wrong verdict on %d, as recorded on %d" % (
                   len(faults), wrong, sum(f[3] == f[4] for f in faults))]
    return {"summary": summary, "failures": failures}


if __name__ == "__main__":
    print("\n".join(render()))
    rep = report()
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
