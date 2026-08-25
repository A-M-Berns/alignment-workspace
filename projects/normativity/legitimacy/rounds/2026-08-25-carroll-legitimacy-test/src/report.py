#!/usr/bin/env python3
"""Render the three tables. `python3 src/report.py MATRIX.txt` regenerates it.

The tables the documents quote are produced here from the same functions the
tests assert, so a document and a test cannot drift apart without the test
failing.
"""
from __future__ import annotations

import sys

import carroll_cases as cc
import objectives as ob
import suite
import table4


def _policy(pol) -> str:
    if pol is None:
        return "-"
    acts = sorted({a for a in pol.values()})
    if len(acts) == 1:
        return acts[0]
    return "; ".join(f"({s},{th},{t})->{a}"
                     for (s, th, t), a in sorted(pol.items(), key=repr))


def objective_regression() -> str:
    out = ["Table 3/4 regression — exact enumeration, exact rationals.",
           "",
           "'reading' names which of Definition 5's two index ranges recovers",
           "the cell; 'n' is the size of the exact optimal set; 'vac' marks a",
           "cell every policy is optimal for. The annotation column is the",
           "source's own label and is metadata, never a requirement.",
           ""]
    for case in cc.CASES:
        out.append(f"== {case}   H={cc.HORIZON[case]}   "
                   f"a_noop={cc.NOOP_ACTION[case]}   ({cc.SOURCE[case]})")
        for row in table4.compare(case):
            readings = [r for r, hit in row["in_argmax_by_reading"].items() if hit]
            mark = "ok  " if readings else "MISS"
            out.append(f"   {mark} {row['objective']:38s} "
                       f"n={row['argmax_size']:<3d} "
                       f"{'vac ' if row['vacuous'] else '    '}"
                       f"reading={','.join(readings) or '-':7s} "
                       f"paper={_policy(row['paper']):34s} "
                       f"ann={row['annotation']}")
        out.append("")
    miss = table4.mismatches()
    out.append(f"cells: {len(table4.rows())}   recovered: "
               f"{len(table4.rows()) - len(miss)}   not recovered: {len(miss)}")
    for case, name, _ in miss:
        out.append(f"   not recovered: {case} / {name}")
    for case, name, by in table4.reading_sensitive():
        out.append(f"   reading-sensitive: {case} / {name} -> {by}")
    return "\n".join(out)


def adversarial_matrix() -> str:
    out = ["Adversarial suite — C0 to C24, plus the under-generality case C7b.",
           ""]
    for row in suite.run():
        out.append(f"{row['id']:5s} {row['result']:5s} {row['title']}")
        out.append(f"          observed: {row['observed']}")
        out.append(f"          {row['note']}")
    out.append("")
    out.append("Two dictatorship failures, as witnesses:")
    for claim, lhs, rhs in suite.dictatorship():
        out.append(f"   {claim}")
        out.append(f"      antecedent={lhs}   consequent={rhs}")
    return "\n".join(out)


def old_interface() -> str:
    out = ["The August 17 interface on Carroll variation classes.",
           "",
           "'trace differs' marks pairs whose licensed-reason traces differ, so",
           "clause 1's antecedent is false and it says nothing about them.",
           ""]
    for row in suite.old_interface_table():
        fired = [k for k, v in row["clauses"].items() if v]
        out.append(f"{row['class']:14s} legitimate={row['legitimate']!s:5s} "
                   f"fired={fired or '-'}  "
                   f"trace differs={[p for p in row['trace_differs']] or '-'}")
    return "\n".join(out)


def render() -> str:
    return "\n\n".join([objective_regression(), "", adversarial_matrix(),
                        "", old_interface(), ""])


if __name__ == "__main__":
    text = render()
    if len(sys.argv) > 1:
        with open(sys.argv[1], "w") as fh:
            fh.write(text + "\n")
    else:
        print(text)
