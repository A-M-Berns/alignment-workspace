"""The tallies of NOGGLE_RESULTS.md, from `noggle_bank.json`.

Each entry is one case of the book as one of three readers coded it: the reader's part
(`A`, `B`, `C`), an id, the section and the case's name, the kind of mistake (`K1` false
belief, `K2` unfitting emotion, `K3` misallocated attention or weight, `K4` choice against
her own judgment, `none`, `cannot say`), the verdict the reader took to be the author's, the
verdict the formal statement gives on the reader's encoding, whether they match (`null`
where either is *contested or unclear*), and the reader's note on what the vocabulary could
not express.  The paraphrases the readers wrote, and the fields of the encoding, are not in
the repository, so the tallies below are of the readers' recorded judgments and cannot be
re-derived from the cases.

`report()` fails when NOGGLE_RESULTS.md's counts or its table of mismatches are not the
ones computed.
"""
from __future__ import annotations

import collections
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
FIELDS = {"part", "id", "where", "kind", "author_verdict", "formal_verdict", "match", "expressibility"}


def load():
    return json.loads((HERE / "noggle_bank.json").read_text(encoding="utf-8"))


def clean(c):
    return str(c["expressibility"]).strip().lower() in ("none", "")


def report():
    bank = load()
    failures = []
    if not bank or any(set(c) != FIELDS for c in bank):
        failures.append("noggle_bank.json is empty or an entry has fields other than %s" % sorted(FIELDS))
    counts = collections.OrderedDict()
    counts["entries"] = len(bank)
    counts["distinct ids"] = len({c["id"] for c in bank})
    for p in "ABC":
        counts["entries of reader %s" % p] = sum(c["part"] == p for c in bank)
    counts["verdicts agree"] = sum(c["match"] is True for c in bank)
    counts["verdicts disagree"] = sum(c["match"] is False for c in bank)
    counts["no comparison"] = sum(c["match"] is None for c in bank)
    counts["fits the vocabulary with no note"] = sum(clean(c) for c in bank)
    for k in ("K1", "K2", "K3", "K4", "none", "cannot say"):
        counts["kind %s" % k] = sum(c["kind"] == k for c in bank)
        counts["kind %s, no note" % k] = sum(c["kind"] == k and clean(c) for c in bank)
    for v in ("manipulates", "acts manipulatively only", "loose sense only", "not manipulation", "contested or unclear"):
        counts["author's verdict %s" % v] = sum(c["author_verdict"] == v for c in bank)
    path = HERE / "NOGGLE_RESULTS.md"
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    for name, val in counts.items():
        if not re.search(r"^- %s: \*\*%d\*\*" % (re.escape(name), val), text, re.M):
            failures.append("NOGGLE_RESULTS.md does not state '%s: %d'" % (name, val))
    mism = [c for c in bank if c["match"] is False]
    stated = {(m.group(1), m.group(2)): [x.strip() for x in m.group(3).split("|")]
              for m in re.finditer(r"^\|\s*([ABC])\s*\|\s*`([\w-]+)`\s*\|(.*)\|\s*$", text, re.M)}
    for c in mism:
        want = [c["kind"], c["author_verdict"], c["formal_verdict"]]
        if stated.get((c["part"], c["id"]), [None] * 4)[1:4] != want:
            failures.append("%s %s: NOGGLE_RESULTS.md says %r, computed %r" % (c["part"], c["id"], stated.get((c["part"], c["id"])), want))
    if len(stated) != len(mism):
        failures.append("NOGGLE_RESULTS.md lists %d mismatches, computed %d" % (len(stated), len(mism)))
    summary = ["%s: %d" % (k, counts[k]) for k in ("entries", "distinct ids", "verdicts agree", "verdicts disagree", "no comparison",
                                                   "fits the vocabulary with no note")]
    return {"summary": summary, "failures": failures, "counts": counts, "mismatches": mism}


if __name__ == "__main__":
    rep = report()
    for k, v in rep["counts"].items():
        print("- %s: **%d**" % (k, v))
    for c in rep["mismatches"]:
        print("| %s | `%s` | %s | %s | %s | %s |" % (c["part"], c["id"], c["where"], c["kind"], c["author_verdict"], c["formal_verdict"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
