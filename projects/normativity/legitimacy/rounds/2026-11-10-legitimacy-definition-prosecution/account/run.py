"""The runner of account/: the eleven results of RESULTS.md, the value-change test of
VALUE_CHANGE.md and the benchmark of BENCHMARK.md (the statement of BASELINE_ACCOUNT.md); the
nine results of VALUE_RESULTS.md, the small model of BRIDGE.md and the two renderings of
RENDERINGS.md (the statement of ACCOUNT.md); the formal checks of BOARD_CHECKS.md and the
counts of LIT_RESULTS.md (the statement of BOARD.md).  Then the formal checks of
STATEMENT_CHECKS.md and the computed tables of SPEC_RESULTS.md (the statement of STATEMENT.md).  Then the
exact instances of DERIVATION.md and the two forms of the responsibility test on the twenty
cases of RESP_RESULTS.md.  Then the exact checks behind MISTAKES_ACCOUNT.md (one decision,
correcting the reward and two periods, the long-run statement) and the counts of
INTENT_RESULTS.md, BLIND_RESULTS.md, NOGGLE_RESULTS.md and VC_RESULTS.md.  Then the exact
cases of LEGITIMACY_CHECKS.md (the statement of LEGITIMACY_STATEMENT.md) and of STOPPING_COST.md,
and the counts of CASE_RUNS.md, those of its second coding included.  Then the tables of LEAN_CASES.md, recomputed from the
statements of the Lean theorems read as text.  Then the history model of interpretation/ on its
episodes and known faults, against INTERPRETATION.md.  A failure is a
status or a count in a document that is not the one computed, a document that parses to
nothing, or a violation count that is not zero."""
from __future__ import annotations

import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent


def table(rel, heading=None, first=r"[\w.\- ]+"):
    """Rows `| key | value | ...` of a markdown table: {key: [cells]}."""
    text = (HERE / rel).read_text(encoding="utf-8")
    if heading is not None:
        if heading not in text:
            return {}
        text = text.split(heading, 1)[1]
        text = re.split(r"\n## ", text, 1)[0]
    rows = {}
    for line in text.splitlines():
        m = re.match(r"^\|\s*(%s?)\s*\|(.*)\|\s*$" % first, line)
        if m and not set(m.group(1)) <= set("-: ") and m.group(1) not in rows:
            rows[m.group(1).strip()] = [c.strip() for c in m.group(2).split("|")]
    return rows


def results_report():
    from . import results
    stated = table("RESULTS.md")
    stated = {k: v[0] for k, v in stated.items() if k.isdigit()}
    failures = []
    if len(stated) != len(results.CHECKS):
        failures.append("RESULTS.md states %d results, the checks cover %d" % (len(stated), len(results.CHECKS)))
    computed = results.run_all()
    for k, (status, _) in computed.items():
        if stated.get(k) != status:
            failures.append("result %s: RESULTS.md says %r, computed %r" % (k, stated.get(k), status))
    return {"statuses": {k: s for k, (s, _) in computed.items()}, "failures": failures}


def value_results_report():
    from . import value_results
    stated = table("VALUE_RESULTS.md")
    stated = {k: v[0] for k, v in stated.items() if k.isdigit()}
    failures = []
    if not stated or len(stated) != len(value_results.CHECKS):
        failures.append("VALUE_RESULTS.md states %d results, the checks cover %d" % (len(stated), len(value_results.CHECKS)))
    computed = value_results.run_all()
    for k, (status, _) in computed.items():
        if stated.get(k) != status:
            failures.append("result %s: VALUE_RESULTS.md says %r, computed %r" % (k, stated.get(k), status))
    return {"statuses": {k: s for k, (s, _) in computed.items()}, "failures": failures}


def main():
    report = {"results": results_report(), "value_results": value_results_report()}
    failures = ["results: " + f for f in report["results"]["failures"]]
    failures += ["value_results: " + f for f in report["value_results"]["failures"]]
    for name in ("value_change", "benchmark", "bridge", "renderings", "board_checks", "lit_results", "statement_checks", "spec_run", "derivation", "responsibility",
                 "mistakes_setting", "mistakes_sequential", "mistakes_longrun", "intent_tests", "blind_coding", "noggle_bank", "value_runs", "legitimacy_checks", "stopping_cost", "case_runs", "second_coding", "lean_cases", "interpretation"):
        mod = __import__("account." + name, fromlist=["report"])
        report[name] = mod.report()
        failures += ["%s: %s" % (name, f) for f in report[name]["failures"]]
    report["failures"] = failures
    return (1 if failures else 0), report


def render(report):
    lines = ["result %s: %s" % kv for kv in report["results"]["statuses"].items()]
    lines += ["value side, result %s: %s" % kv for kv in report["value_results"]["statuses"].items()]
    for name in ("value_change", "benchmark", "bridge", "renderings", "board_checks", "lit_results", "statement_checks", "spec_run", "derivation", "responsibility",
                 "mistakes_setting", "mistakes_sequential", "mistakes_longrun", "intent_tests", "blind_coding", "noggle_bank", "value_runs", "legitimacy_checks", "stopping_cost", "case_runs", "second_coding", "lean_cases", "interpretation"):
        if name in report:
            lines += ["%s: %s" % (name, line) for line in report[name]["summary"]]
    return "\n".join(lines)


if __name__ == "__main__":
    import sys
    code, rep = main()
    print(render(rep))
    print("OK" if not code else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    sys.exit(code)
