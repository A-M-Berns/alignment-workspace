"""Reads the frozen predictions from CASE_BANK.md and applies its matching rule."""
from __future__ import annotations

import pathlib
import re

from .model import CLAUSES, show, verdict

HERE = pathlib.Path(__file__).resolve().parent
HEADING = "## The table the runner reads"
ROW = re.compile(r"^\|\s*([PBTNX]\d+)\s*\|\s*(.+?)\s*\|\s*$")
FORM = re.compile(r"^(legitimate|fails(?:\(([^)]+)\))?|not manipulation|out-of-scope\(stretch-start\))"
                  r"(?:; (manipulation|not manipulation))?$")


def load():
    text = (HERE / "CASE_BANK.md").read_text(encoding="utf-8")
    rows = {}
    for line in text.split(HEADING, 1)[1].splitlines() if HEADING in text else ():
        m = ROW.match(line)
        if not m:
            continue
        if not FORM.match(m.group(2)):
            raise SystemExit("CASE_BANK.md: %s has a prediction outside the vocabulary: %r" % m.groups())
        if m.group(1) in rows:
            raise SystemExit("CASE_BANK.md: %s occurs twice" % m.group(1))
        rows[m.group(1)] = m.group(2)
    return rows


def matches_one(prediction, v):
    head, clause, flag = FORM.match(prediction).groups()
    if flag is not None and v["manipulation"] != (flag == "manipulation"):
        return False
    if head == "legitimate":
        return v["legitimate"]
    if head == "not manipulation":
        return not v["manipulation"]
    if head.startswith("fails"):
        if clause is not None:
            assert clause in CLAUSES, clause
            return clause in v["failing"]
        return not v["legitimate"]
    raise ValueError(prediction)


def evaluate(case, prediction):
    """(computed verdict as a string, whether it matches the prediction)."""
    if case.variants:
        vs = {name: verdict(c) for name, c in case.variants.items()}
        computed = "; ".join("%s: %s" % (n, show(v)) for n, v in vs.items())
        if prediction.startswith("out-of-scope"):
            return "out-of-scope(stretch-start): " + computed, len({show(v) for v in vs.values()}) > 1
        return computed, all(matches_one(prediction, v) for v in vs.values())
    v = verdict(case)
    if prediction.startswith("out-of-scope"):
        return show(v), False
    return show(v), matches_one(prediction, v)
