"""Reads the frozen predictions from CASE_BANK.md and applies its matching rule."""
from __future__ import annotations

import pathlib
import re

from .cases import verdict

HERE = pathlib.Path(__file__).resolve().parent
HEADING = "## The table the runner reads"
ROW = re.compile(r"^\|\s*([DPBTNXY]\d+)\s*\|\s*(.+?)\s*\|\s*$")
ITEM = re.compile(r"^(subversion|no subversion|help|harm|force|nothing|covered|in order|admissible|report)$"
                  r"|^(subversion|force)\((\w+)\)$|^gap\((hers|nobody)\)$|^inadmissible\(([a-z ]+)\)$")


def load():
    text = (HERE / "CASE_BANK.md").read_text(encoding="utf-8")
    rows = {}
    for line in text.split(HEADING, 1)[1].splitlines() if HEADING in text else ():
        m = ROW.match(line)
        if not m:
            continue
        for item in m.group(2).split("; "):
            if not ITEM.match(item):
                raise SystemExit("CASE_BANK.md: %s has an item outside the vocabulary: %r" % (m.group(1), item))
        if m.group(1) in rows:
            raise SystemExit("CASE_BANK.md: %s occurs twice" % m.group(1))
        rows[m.group(1)] = m.group(2)
    return rows


def item_matches(item, v):
    kinds = v["kinds"]
    has = lambda k: any(kk == k for kk, _ in kinds)
    m = ITEM.match(item)
    if item == "report":
        return True
    if item == "subversion":
        return has("subversion")
    if item == "no subversion":
        return not has("subversion")
    if item in ("help", "harm", "force"):
        return has(item)
    if item == "nothing":
        return not kinds and v["fails"] is None and not v["owners"]
    if item == "covered":
        return v["covered"] is True
    if item == "in order":
        return v["in_order"] is True
    if item == "admissible":
        return v["fails"] == []
    if m.group(2):
        return (m.group(2), m.group(3)) in kinds
    if m.group(4):
        owners = {o for o, _ in v["owners"]}
        return ("hers" in owners) if m.group(4) == "hers" else (owners == {"nobody"})
    if m.group(5):
        return v["fails"] is not None and m.group(5) in v["fails"]
    raise ValueError(item)


def show(v):
    if v["fails"] is not None:
        return "admissible" if not v["fails"] else "inadmissible(%s)" % ", ".join(v["fails"])
    if v["owners"]:
        return "; ".join("gap(%s) in %s" % (o, n) for o, n in sorted(v["owners"], key=str))
    s = ", ".join("%s(%s)" % kn for kn in sorted(v["kinds"])) or "nothing"
    if v["covered"] is not None:
        s += "; covered" if v["covered"] else "; not covered"
    if v["in_order"]:
        s += "; in order"
    if v["in_fact"] is not None:
        s += " [in fact: %s]" % (", ".join("%s(%s)" % kn for kn in sorted(v["in_fact"])) or "nothing")
    if v["widening"]:
        s += " [widest %s]" % v["widening"]
    return s


def evaluate(case, prediction):
    """(computed verdict as a string, whether it matches, the verdicts)."""
    vs = {name: verdict(spec) for name, spec in case.variants.items()}
    ok = all(all(item_matches(i, v) for i in prediction.split("; ")) for v in vs.values())
    if len(vs) == 1:
        return show(next(iter(vs.values()))), ok, vs
    return " | ".join("%s: %s" % (n, show(v)) for n, v in vs.items()), ok, vs
