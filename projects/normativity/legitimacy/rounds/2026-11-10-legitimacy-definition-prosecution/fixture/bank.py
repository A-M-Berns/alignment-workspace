"""Reads the pre-registered table from CASE_BANK.md.  Nothing here edits it."""
from __future__ import annotations

import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent.parent
ROW = re.compile(r"^\|\s*([BT]\d+)\s*\|\s*(build|test)\s*\|\s*((?:[^|\\]|\\\|)+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|$")


class PreRegistration:
    def __init__(self, case, label, verdict, silent, formation):
        self.case, self.label = case, label
        self.verdict = verdict.replace("\\|", "|")
        self.silent = [] if silent == "-" else [s.strip() for s in silent.split(",")]
        self.formation = formation

    def category(self):
        return self.verdict.split("(")[0]

    def clauses(self):
        m = re.match(r"illegitimate\((.*)\)", self.verdict)
        return m.group(1).split("|") if m else []

    def reason(self):
        m = re.match(r"out-of-scope\((.*)\)", self.verdict)
        return m.group(1) if m else None


def load(path=HERE / "CASE_BANK.md"):
    rows = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        m = ROW.match(line.strip())
        if m:
            p = PreRegistration(*m.groups())
            rows[p.case] = p
    return rows


def matches(pre, computed):
    """The matching rule of CASE_BANK.md.  computed: dict with keys
    category, failing (list of clause names), formation."""
    cat = pre.category()
    if cat == "legitimate":
        ok = computed["category"] == "legitimate"
    elif cat == "illegitimate":
        ok = (computed["category"] == "illegitimate"
              and any(c in computed["failing"] for c in pre.clauses())
              and not any(s in computed["failing"] for s in pre.silent))
    elif cat == "out-of-scope":
        ok = computed["category"] == "out-of-scope"
    elif cat == "individuation-dependent":
        ok = computed["category"] == "individuation-dependent"
    else:
        ok = False
    if pre.formation != "-" and ok:
        ok = computed.get("formation") == pre.formation
    return ok
