#!/usr/bin/env python3
"""The freshness audit: does the site's derived layer still match the repository's research structure?

Run weekly by .github/workflows/freshness.yml (and by hand: `python3 tests/freshness.py`). It checks:

  1. every merged pull request has a digest in state/prs.json (the GitHub list read with `gh`);
  2. every round in state/rounds.json is carried by some digest, or is on the stated allowlist;
  3. the concept registry's terminal goals match the program frame's roots, both ways;
  4. every substantive wiki page backs a concept entry;
  5. every program root and each of its root frames is referenced by some concept entry.

Findings go to stdout as markdown and the exit code is 1 when there are any, so the scheduled
workflow can file them. The audit reports; it changes nothing and gates no merge.

Null inputs (`--self-test`): an empty digest file, a merged PR with no digest, a program root with
no concept, a terminal goal the frame tree lacks — each must produce a finding, and consistent
synthetic data must produce none.
"""
from __future__ import annotations

import json
import pathlib
import shutil
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

# rounds that predate the digest discipline or never reached main, per the digest run's report
ROUND_ALLOWLIST = {"2026-08-09-consolidation", "2026-08-09-completing-pass", "2026-08-10-repo-scaffolding",
                   "2026-10-22-map-as-canonical", "2026-10-24-site-vertical-slice",
                   # landed by direct push before branch protection was live
                   "2026-08-11-branch-protection", "2026-08-11-licensing-dco-citation"}
# wiki pages that are navigation or registers rather than concepts
WIKI_ALLOWLIST = {"Home", "Architecture", "CONVENTIONS", "Glossary", "ORIGIN", "Prior-Art",
                  "Relation-to-the-Field", "Roadmap", "Sources", "Theorem-Spine", "_Sidebar",
                  "Deconfusing-Corrigibility-Companion", "What-Deference-Requires", "Why-Normativity",
                  "Logical-Induction-and-Deference"}


def check_pr_coverage(merged_numbers: set[int], digests: dict) -> list[str]:
    missing = sorted(n for n in merged_numbers if str(n) not in digests)
    return [f"merged PR #{n} has no digest in state/prs.json" for n in missing]


def check_round_coverage(rounds: set[str], digests: dict) -> list[str]:
    carried = {rid for P in digests.values() for rid in P.get("rounds") or []}
    return [f"round `{rid}` appears in no digest and is not on the allowlist"
            for rid in sorted(rounds - carried - ROUND_ALLOWLIST)]


def check_terminal_goals(program_roots: set[str], concepts: list[dict], links: list[dict]) -> list[str]:
    terminal = {e["id"]: set(e.get("refs") or []) for e in concepts if e.get("kind") == "goal"
                and any(L["from"] == e["id"] and L["to"] == "the-program" and not L.get("undirected") for L in links)}
    out = []
    covered: set[str] = set()
    for cid, refs in terminal.items():
        hit = refs & program_roots
        if not hit:
            out.append(f"terminal goal `{cid}` references no root of the program frame")
        covered |= hit
    for root in sorted(program_roots - covered - {"enabling-work"}):
        out.append(f"program root `{root}` is not referenced by any terminal goal of the concept registry")
    return out


def check_wiki_coverage(wiki_pages: set[str], concepts: list[dict]) -> list[str]:
    backed = {e.get("wiki") for e in concepts if e.get("wiki")}
    return [f"wiki page `{p}` backs no concept entry and is not on the allowlist"
            for p in sorted(wiki_pages - backed - WIKI_ALLOWLIST)]


def check_frame_coverage(nodes: dict, program_roots: set[str], concepts: list[dict]) -> list[str]:
    refs = {x for e in concepts for x in e.get("refs") or []}
    out = []
    for line in sorted(program_roots - {"enabling-work"}):
        frames = [line] + [rt["id"] for rt in (nodes.get(line, {}).get("frame") or {}).get("roots") or []
                           if nodes.get(rt["id"], {}).get("frame")]
        if not any(f in refs for f in frames):
            out.append(f"line `{line}` and its root frames are referenced by no concept entry")
    return out


def live_audit() -> list[str]:
    findings: list[str] = []
    digests = {str(p["number"]): p for p in json.loads((ROOT / "state" / "prs.json").read_text())["prs"]}
    concepts_doc = json.loads((ROOT / "state" / "concepts.json").read_text())
    concepts, links = concepts_doc["concepts"], concepts_doc["links"]
    rounds = {r["id"] for r in json.loads((ROOT / "state" / "rounds.json").read_text())["rounds"]}
    if shutil.which("gh"):
        r = subprocess.run(["gh", "pr", "list", "--repo", "A-M-Berns/alignment-workspace", "--state", "merged",
                            "--limit", "500", "--json", "number"], capture_output=True, text=True)
        if r.returncode == 0:
            merged = {p["number"] for p in json.loads(r.stdout)}
            findings += check_pr_coverage(merged, digests)
        else:
            findings.append("could not list merged pull requests (gh failed); PR coverage unverified this run")
    else:
        findings.append("gh is not available; PR coverage unverified this run")
    findings += check_round_coverage(rounds, digests)
    sys.path.insert(0, str(ROOT / "site"))
    from load import Repo
    repo = Repo()
    program_roots = {rt["id"] for rt in repo.nodes["the-program"]["frame"]["roots"]}
    findings += check_terminal_goals(program_roots, concepts, links)
    findings += check_wiki_coverage(set(repo.wiki), concepts)
    findings += check_frame_coverage(repo.nodes, program_roots, concepts)
    return findings


def self_test() -> int:
    cases = []
    cases.append(("a merged PR with no digest is a finding",
                  bool(check_pr_coverage({1, 2}, {"1": {}})), True))
    cases.append(("full PR coverage is clean",
                  check_pr_coverage({1}, {"1": {}}) == [], True))
    cases.append(("an uncarried round is a finding",
                  bool(check_round_coverage({"r-new"}, {})), True))
    cases.append(("an empty digest file makes every merged PR a finding",
                  len(check_pr_coverage({1, 2, 3}, {})) == 3, True))
    goals = [{"id": "g1", "kind": "goal", "refs": ["lineA"]}]
    links = [{"from": "g1", "to": "the-program"}]
    cases.append(("a program root with no terminal goal is a finding",
                  any("lineB" in f for f in check_terminal_goals({"lineA", "lineB"}, goals, links)), True))
    cases.append(("a terminal goal off the frame tree is a finding",
                  any("g1" in f for f in check_terminal_goals({"lineC"}, goals, links)), True))
    cases.append(("matched goals and roots are clean",
                  check_terminal_goals({"lineA"}, goals, links) == [], True))
    cases.append(("an unbacked substantive wiki page is a finding",
                  bool(check_wiki_coverage({"New-Thing"}, [])), True))
    failures = 0
    print("FRESHNESS SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    findings = live_audit()
    if not findings:
        print("FRESHNESS: clean — digests cover the merged pull requests, the registry matches the program frame, the wiki is accounted for")
        return 0
    print("# Freshness audit findings\n")
    for f in findings:
        print(f"- {f}")
    print(f"\n{len(findings)} finding(s). Each is work for a round, not a merge blocker.")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
