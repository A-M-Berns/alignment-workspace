"""The eighth pass's runner: the eleven results of RESULTS.md, the value-change test of
VALUE_CHANGE.md and the benchmark of BENCHMARK.md.  A failure is a status or a count in a
document that is not the one computed, or a document that parses to nothing."""
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


def main():
    report = {"results": results_report()}
    failures = ["results: " + f for f in report["results"]["failures"]]
    for name in ("value_change", "benchmark"):
        try:
            mod = __import__("account." + name, fromlist=["report"])
        except ImportError:
            continue
        report[name] = mod.report()
        failures += ["%s: %s" % (name, f) for f in report[name]["failures"]]
    report["failures"] = failures
    return (1 if failures else 0), report


def render(report):
    lines = ["result %s: %s" % kv for kv in report["results"]["statuses"].items()]
    for name in ("value_change", "benchmark"):
        if name in report:
            lines += ["%s: %s" % (name, line) for line in report[name]["summary"]]
    return "\n".join(lines)


if __name__ == "__main__":
    import sys
    code, rep = main()
    print(render(rep))
    print("OK" if not code else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    sys.exit(code)
