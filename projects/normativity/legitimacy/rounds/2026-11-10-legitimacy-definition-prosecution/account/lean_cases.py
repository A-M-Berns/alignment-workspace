"""The tables of LEAN_CASES.md, recomputed from the statements of two Lean files and from
legitimacy_checks.py.

Read as text, from lean/Workspace/Deference/Contrib/: in LegitimacyCases.lean every
`theorem <x>_has : <x>.Has ⟨seven booleans⟩`, and in LegitimacyWitness.lean every
`theorem <x>_profile : ... ⟨seven booleans⟩`.  The booleans say which clauses of `Legit` hold on
the term, in the order start rule, proper offers, declines, F1, F2, F2', F3.  This module does
not run Lean: that the theorems are proved is the build's and `tests/audit_axioms.py`'s to say.
It checks that each is stated with the proof `Supplied.has (by decide +kernel)` or
`hasProfile_std (by decide +kernel)`, and that neither file contains `sorry`.

An outcome is computed for each of the 41 cases from the Lean profile and the row
legitimacy_checks.py computes: `differs` when the verdicts differ; `agrees, other clause` when
both fail and the clauses differ; `agrees` otherwise.  `not expressible` is set by hand below,
with the cases that carry data the table's case does not supply and the variants.

`report()` fails when a case has no theorem, when a theorem is not stated in the expected form,
when either file is missing, or when LEAN_CASES.md's rows or counts are not the ones computed.
"""
import pathlib
import re

from . import legitimacy_checks

HERE = pathlib.Path(__file__).resolve().parent
DOC = "LEAN_CASES.md"
CLAUSES = ["start rule", "proper offers", "declines", "F1", "F2", "F2'", "F3"]

NOT_EXPRESSIBLE = {
    "B6": "no field says she had no earlier rating of the matter",
}
ADDED = {
    "B2": "her rating without the nagging",
    "B5": "her rating without the influence",
    "B10": "her rating without the manner",
    "D3": "an earlier decision with the view on offer",
    "D4": "an earlier decision with the view on offer, and its bearing then",
    "D5": "an earlier decision with the other view on offer",
    "D10": "her state after taking up both offers",
    "D11": "her ratings after hearing both",
}
VARIANTS = [
    ("a5q", "A5", "`quit` is among her options"),
    ("a8w", "A8", "in cases of weight 1/5 she rates stopping higher, and stops in half of them"),
    ("d1o", "D1", "nothing is designated as on offer"),
    ("d4o", "D4", "the decline is not designated"),
    ("d6o", "D6", "nothing is designated as on offer"),
    ("d7o", "D7", "nothing is designated as on offer"),
    ("d8o", "D8", "nothing is designated as on offer"),
    ("d10o", "D10", "nothing is designated as on offer"),
]
NEIGHBOURS = [
    ("early", "`start`", "start rule"),
    ("spent", "`optsHeard`", "proper offers"),
    ("unoffered", "`declined`", "declines"),
    ("withheld", "`offered`", "F1"),
    ("covert", "`known`", "F2"),
    ("led", "`act`", "F2'"),
    ("stuck", "`act`", "F3"),
]


def lean_dir():
    for up in HERE.parents:
        d = up / "lean" / "Workspace" / "Deference" / "Contrib"
        if d.is_dir():
            return d
    return None


def profiles(text, pattern, proof):
    """{name: [seven booleans]} for the theorems matching `pattern`, and the names not proved by `proof`."""
    found, odd = {}, []
    for m in re.finditer(pattern, text, re.S):
        cells = [c.strip() for c in m.group(2).split(",")]
        if len(cells) != 7 or not set(cells) <= {"true", "false"}:
            odd.append(m.group(1))
            continue
        found[m.group(1)] = [c == "true" for c in cells]
        if proof not in re.sub(r"\s+", " ", m.group(3)):
            odd.append(m.group(1))
    return found, odd


def read():
    d = lean_dir()
    failures = []
    if d is None:
        return {}, {}, ["no lean/Workspace/Deference/Contrib above %s" % HERE]
    out = []
    for name, pattern, proof in (
            ("LegitimacyCases.lean", r"theorem (\w+)_has : \1\.Has ⟨([^⟩]*)⟩ :=(.*?)\n\n", "Supplied.has (by decide +kernel)"),
            ("LegitimacyWitness.lean", r"theorem (\w+)_profile :\s+\1\.model\.HasProfile[^⟨]*⟨([^⟩]*)⟩ :=(.*?)\n\n",
             "hasProfile_std (by decide +kernel)")):
        path = d / name
        if not path.exists():
            failures.append("%s is missing" % name)
            out.append({})
            continue
        text = path.read_text(encoding="utf-8")
        body = text.split("-/", 1)[1] if "-/" in text else text
        if re.search(r"\bsorry\b", body):
            failures.append("%s contains sorry" % name)
        found, odd = profiles(text, pattern, proof)
        failures += ["%s: %s is not stated in the expected form" % (name, o) for o in odd]
        out.append(found)
    return out[0], out[1], failures


def failing(profile):
    return [c for c, ok in zip(CLAUSES, profile) if not ok]


def table_clauses(why):
    return sorted({w.split(" (")[0].strip() for w in why.split(",") if w.strip()})


def show(profile):
    f = failing(profile)
    return ("holds", "none") if not f else ("fails", ", ".join(f))


def case_rows():
    cases, _, failures = read()
    rows, counts = [], {"agrees": 0, "agrees, other clause": 0, "differs": 0, "not expressible": 0}
    for cid, _, _, _, got, why in legitimacy_checks.rows():
        name = cid.lower()
        if name not in cases:
            failures.append("%s has no theorem %s_has" % (cid, name))
            continue
        verdict, clauses = show(cases[name])
        if cid in NOT_EXPRESSIBLE:
            outcome = "not expressible"
        elif verdict != got:
            outcome = "differs"
        elif verdict == "fails" and sorted(failing(cases[name])) != table_clauses(why):
            outcome = "agrees, other clause"
        else:
            outcome = "agrees"
        counts[outcome] += 1
        note = NOT_EXPRESSIBLE.get(cid) or ADDED.get(cid) or "—"
        rows.append("| %s | %s | %s | %s | %s | %s | %s |" % (cid, got, why or "none", verdict, clauses, outcome, note))
    return rows, counts, failures


def variant_rows():
    cases, _, _ = read()
    return ["| `%s` | %s | %s | %s | %s |" % ((name, of, what) + show(cases[name])) for name, of, what in VARIANTS if name in cases]


def neighbour_rows():
    _, witness, _ = read()
    rows = []
    for name, field, clause in NEIGHBOURS:
        if name in witness:
            rows.append("| `%s` | %s | %s | %s |" % (name, field, clause, ", ".join(failing(witness[name])) or "none"))
    return rows


def counts_line(counts, n):
    return ("Counts: %d cases; agrees %d, agrees by another clause %d, differs %d, not expressible %d; %d of the %d terms carry data the case does not supply."
            % (n, counts["agrees"], counts["agrees, other clause"], counts["differs"], counts["not expressible"], len(ADDED), n))


def report():
    rows, counts, failures = case_rows()
    vrows, nrows = variant_rows(), neighbour_rows()
    if not rows:
        failures.append("no cases")
    if len(vrows) != len(VARIANTS):
        failures.append("%d of %d variants have a theorem" % (len(vrows), len(VARIANTS)))
    if len(nrows) != len(NEIGHBOURS):
        failures.append("%d of %d neighbours have a theorem" % (len(nrows), len(NEIGHBOURS)))
    for name, _, clause in NEIGHBOURS:
        got = [r for r in nrows if r.startswith("| `%s` " % name)]
        if got and not got[0].endswith("| %s | %s |" % (clause, clause)):
            failures.append("neighbour %s does not fail by %s alone" % (name, clause))
    path = HERE / DOC
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    lines = text.splitlines()
    stated = [l for l in lines if re.match(r"^\| [A-D]\d+ \|", l)]
    if stated != rows:
        failures.append("%s states %d case rows, of which %d are among the %d computed" % (DOC, len(stated), len(set(stated) & set(rows)), len(rows)))
    stated_v = [l for l in lines if re.match(r"^\| `[a-d]\d+\w` \|", l)]
    if stated_v != vrows:
        failures.append("%s states %d variant rows, of which %d are among the %d computed" % (DOC, len(stated_v), len(set(stated_v) & set(vrows)), len(vrows)))
    stated_n = [l for l in lines if re.match(r"^\| `[a-z]+` \| `", l)]
    if stated_n != nrows:
        failures.append("%s states %d neighbour rows, of which %d are among the %d computed" % (DOC, len(stated_n), len(set(stated_n) & set(nrows)), len(nrows)))
    line = counts_line(counts, len(rows))
    if line not in lines:
        failures.append("%s does not state: %s" % (DOC, line))
    return {"summary": [line[len("Counts: "):], "%d variants; %d neighbours of the witness, each failing by one clause" % (len(vrows), len(nrows))],
            "failures": failures}


if __name__ == "__main__":
    rows, counts, _ = case_rows()
    print("\n".join(neighbour_rows()))
    print()
    print("\n".join(rows))
    print()
    print("\n".join(variant_rows()))
    print()
    print(counts_line(counts, len(rows)))
    rep = report()
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    raise SystemExit(1 if rep["failures"] else 0)
