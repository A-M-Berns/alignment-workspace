#!/usr/bin/env python3
"""The round's runner.  Exit nonzero on: a computed verdict diverging from its
pre-registration without a FORCED-REVISION record in FORCING.md; an ablation
that flips no banked case; an audit that fails; a bank that parses to nothing."""
from __future__ import annotations

import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from fixture import audits, bank  # noqa: E402
from fixture.cases import all_cases  # noqa: E402
from fixture.evaluate import case_verdict, verdict_string  # noqa: E402

CLAUSES = ("L0", "L1", "L2", "L3", "W")


def forced_cases():
    text = (HERE / "FORCING.md").read_text(encoding="utf-8")
    return set(re.findall(r"^FORCED-REVISION\s+([BT]\d+)", text, re.M))


def main(argv):
    as_json = "--json" in argv
    pre = bank.load()
    if not pre:
        print("CASE_BANK.md parsed to no cases", file=sys.stderr)
        return 2
    cases = all_cases()
    failures = []
    report = {"verdicts": {}, "ablations": {}, "audits": {}, "replay_form": {}, "extras": {}}

    # -- verdicts
    verdicts = {}
    for case in cases:
        v = case_verdict(case)
        verdicts[case.id] = v
        p = pre.get(case.id)
        if p is None:
            failures.append("%s has no pre-registration" % case.id)
            continue
        ok = bank.matches(p, v)
        rec = {"title": case.title, "label": p.label, "pre": p.verdict, "pre_formation": p.formation,
               "computed": verdict_string(v), "failing": v["failing"], "formation": v["formation"],
               "match": ok, "trace_equal_pairs": [list(x) for x in v.get("pairs", [])],
               "variants": [(n, verdict_string(x), x["failing"], x["formation"]) for n, x in v["variants"]]}
        if v["category"] == "illegitimate":
            rec["positions"] = {str(k): val for k, val in v["results"]["L1"].items()}
            rec["l3_lost_at"] = {k: val for k, val in v["results"]["L3"].items()}
            rec["l0"] = {k: val for k, val in v["results"]["L0"].items()}
            rec["l2"] = {str(k): val for k, val in v["results"]["L2"].items()}
        report["verdicts"][case.id] = rec
        if not ok and case.id not in forced_cases():
            failures.append("%s: computed %s, pre-registered %s, no FORCED-REVISION record"
                            % (case.id, verdict_string(v), p.verdict))
    unregistered = sorted(set(pre) - set(verdicts))
    if unregistered:
        failures.append("banked cases with no fixture: %s" % unregistered)

    # -- ablations
    for c in CLAUSES:
        flips = []
        if c != "W":
            for case in cases:
                base = verdicts[case.id]["category"]
                abl = case_verdict(case, ablate=(c,))["category"]
                if base != abl:
                    flips.append((case.id, base, abl))
            report["ablations"][c] = {"reading": "clause deleted, house L", "flips": flips}
        else:
            house_flips = []
            for case in cases:
                if case_verdict(case, ablate=("W",))["category"] != verdicts[case.id]["category"]:
                    house_flips.append(case.id)
            for ind in ("coarse", "refined"):
                for case in cases:
                    base = verdicts[case.id]["category"]
                    abl = case_verdict(case, ablate=("W",), individuation=ind)["category"]
                    if base != abl:
                        flips.append((case.id, base, abl, ind))
            report["ablations"][c] = {
                "reading": "W deleted: the vocabulary unconstrained; the bank under the coarse and refined L",
                "flips_under_house_L": house_flips, "flips": flips}
        if not flips:
            failures.append("ablation of %s flips no banked case: unforced" % c)

    # -- audits
    sat = audits.satisfiability()
    report["audits"]["satisfiability"] = sat
    if not sat["ok"]:
        failures.append("satisfiability audit failed")
    pair_counts = {cid: len(v["pairs"]) for cid, v in verdicts.items() if "pairs" in v}
    for cid, v in verdicts.items():
        if "pairs" not in v:
            pair_counts[cid] = min(len(x["pairs"]) for _, x in v["variants"])
    report["audits"]["trace_equal_pairs_per_case"] = pair_counts
    kill = [cid for cid, p in pre.items() if p.category() == "illegitimate"]
    zero = [cid for cid in kill if pair_counts.get(cid, 0) == 0]
    report["audits"]["kill_tests_with_zero_pairs"] = zero
    if zero:
        failures.append("kill tests with no trace-equal pair: %s" % zero)
    by_id = {c.id: c for c in cases}
    c_b4 = audits.coarse_convicts_b4(by_id["B4"])
    c_t10 = audits.refined_acquits_t10(by_id["T10"])
    report["audits"]["coarse_L_convicts_B4"] = c_b4
    report["audits"]["refined_L_acquits_T10"] = c_t10
    if not c_b4["ok"]:
        failures.append("the coarsened L does not convict B4")
    if not c_t10["ok"]:
        failures.append("the refined L does not acquit T10")
    triv = audits.triviality(verdicts)
    report["audits"]["triviality"] = triv
    if not triv["ok"]:
        failures.append("triviality audit failed")
    for case in cases:
        report["replay_form"][case.id] = audits.replay_form(case)
        report["extras"][case.id] = audits.extras(case)

    report["failures"] = failures
    if as_json:
        print(json.dumps(report, indent=1, default=str))
    else:
        print("case  label  pre-registered -> computed [formation]  match")
        for cid, r in report["verdicts"].items():
            print("%-4s %-5s %-28s -> %-28s [%s] %s" % (cid, r["label"], r["pre"], r["computed"],
                                                       r["formation"], "ok" if r["match"] else "DIVERGES"))
        print("\nablations:")
        for c, a in report["ablations"].items():
            print("  %s: %s" % (c, a["flips"] or "no flip"))
            if c == "W":
                print("     under house L: %s" % (a["flips_under_house_L"] or "no flip"))
        print("\naudits:")
        for k, a in report["audits"].items():
            print("  %s: %s" % (k, a))
        print("\nreplay-F equation per policy:")
        for cid, r in report["replay_form"].items():
            print("  %s: %s" % (cid, r))
        print("\nextras:")
        for cid, r in report["extras"].items():
            for k, x in r.items():
                print("  %s %s: %s" % (cid, k, x))
        print("\n%s" % ("OK" if not failures else "FAILURES:\n  " + "\n  ".join(failures)))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
