#!/usr/bin/env python3
"""The site builds, or the tree is wrong (ruling S2, 2026-10-24).

`site/build.py --check` builds the whole site into a temporary directory from graph/index.json (written by the plain
checker run when absent), the state files, the registries, DECISIONS.md, the wiki and the ledgers, and fails on an
unresolved reference, two ids that map to one path, or a binding in site/lede.md that disagrees with the state. This
gate runs that build and fails with it.

Null inputs (`--self-test`): a lede binding that disagrees with the state, two ids that collapse to one path, and a
lede that is missing. Each must fail, and a build of the live tree must pass.
"""
from __future__ import annotations

import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SITE = ROOT / "site"
sys.path.insert(0, str(SITE))


def build_check() -> tuple[bool, str]:
    r = subprocess.run([sys.executable, str(SITE / "build.py"), "--check"], cwd=ROOT, capture_output=True, text=True)
    return r.returncode == 0, (r.stdout + r.stderr).strip()


def dom_check() -> tuple[bool, str]:
    """Build into a scratch directory and run the behaviour gate (tests/site_dom.js) against it:
    the app boots, every concept renders, clicks open cards, fragments exist, nothing overlaps.
    Node is required; its absence is a failure, not a skip — a gate that silently skips is no gate."""
    import shutil as _sh
    import tempfile
    node = _sh.which("node")
    if not node:
        return False, "node is not on PATH; the site's behaviour gate cannot run"
    with tempfile.TemporaryDirectory() as d:
        r = subprocess.run([sys.executable, str(SITE / "build.py"), "--out", d], cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            return False, (r.stdout + r.stderr).strip()
        r2 = subprocess.run([node, str(ROOT / "tests" / "site_dom.js"), d], capture_output=True, text=True)
        return r2.returncode == 0, (r2.stdout + r2.stderr).strip()


def self_test() -> int:
    import build as B
    import load as L
    import pages as P
    cases = []
    # a build error is a refusal: the exceptions below are what the gate turns into a failure
    try:
        B.check_bindings("<!--bind:nodes-->1<!--/bind-->", {"nodes": 2}, "lede")
        cases.append(("a lede binding that disagrees with the state is refused", False, True))
    except L.BuildError:
        cases.append(("a lede binding that disagrees with the state is refused", True, True))
    try:
        B.check_bindings("<!--bind:nowhere-->1<!--/bind-->", {"nodes": 2}, "lede")
        cases.append(("a lede binding naming no count is refused", False, True))
    except L.BuildError:
        cases.append(("a lede binding naming no count is refused", True, True))
    cases.append(("a binding that agrees passes and is replaced by the state's value",
                  B.check_bindings("n <!--bind:nodes-->2<!--/bind-->", {"nodes": 2}, "lede") == "n 2", True))
    class FakeRepo:
        nodes = {"a/b": {}, "a--b": {}}
        items = {}
        decisions = {}
        rounds = {}
        registry = {}
        wiki = {}
        handles = {}
        prs = {}
        concepts = {}
    s = P.Site(FakeRepo())
    s.url("n", "a/b")
    try:
        s.url("n", "a--b")
        cases.append(("two ids that map to one path are refused", False, True))
    except L.BuildError:
        cases.append(("two ids that map to one path are refused", True, True))
    s2 = P.Site(FakeRepo())
    s2.url("n", "missing")
    cases.append(("an id that resolves to nothing is recorded as unresolved", s2.unresolved == ["n:missing"], True))
    # a missing lede fails the real build: run the check with site/lede.md set aside
    lede = SITE / "lede.md"
    aside = SITE / "lede.md.selftest-aside"
    try:
        lede.rename(aside)
        r = subprocess.run([sys.executable, str(SITE / "build.py"), "--check"], cwd=ROOT, capture_output=True, text=True)
        cases.append(("a missing lede fails the build", r.returncode != 0 and "lede.md is missing" in r.stderr, True))
    finally:
        if aside.exists():
            aside.rename(lede)
    # the registry validations refuse bad content rather than rendering it wrong
    class FakeRepo2:
        nodes = {"n1": {"statement": "s", "fields": {}}}
        items = {}
        decisions = {}
        rounds = {"r1": {}}
        registry = {}
        wiki = {"Page": "text"}
        handles = {}
        concept_kinds = {"goal": "goal"}
        concepts = {
            "a": {"id": "a", "kind": "goal", "title": "A", "blurb": "fine"},
            "b": {"id": "b", "kind": "nonsense", "title": "B", "blurb": ""},
        }
        concept_links = [
            {"from": "a", "to": "a", "rel": ["part"], "why": "self"},
            {"from": "a", "to": "b", "rel": ["madeup"], "why": "x"},
            {"from": "a", "to": "b", "rel": ["part"], "why": "dup"},
        ]
        prs = {"9": {"number": 9, "title": "t", "merged": "2026-01-01", "rounds": ["no-such-round"],
                     "topics": {"wiki": ["No-Page"], "frames": ["no-node"]}, "summary": "", "superseded": ""}}
        narratives = {}
    s3 = P.Site(FakeRepo2())
    P.map_data(s3)
    bad = "\n".join(s3.unresolved)
    for token, label in (("kind:nonsense", "an unknown concept kind is refused"),
                         ("self-link", "a self-link is refused"),
                         ("rel:madeup", "an unknown relation category is refused"),
                         ("duplicate-link", "a duplicate link is refused"),
                         ("prs:9:round:no-such-round", "a digest naming no round is refused"),
                         ("prs:9:wiki:No-Page", "a digest topic naming no wiki page is refused"),
                         ("prs:9:frame:no-node", "a digest topic naming no node is refused"),
                         ("empty summary", "an empty digest summary is refused")):
        cases.append((label, token in bad, True))
    ok, msg = build_check()
    cases.append(("the live tree builds", ok, True))
    ok2, msg2 = dom_check()
    cases.append(("the map behaves: boots, renders all concepts, cards open, no overlaps", ok2, True))
    if not ok2:
        print("  the dom gate said:", msg2[-600:])
    failures = 0
    print("SITE BUILD SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    if not ok:
        print("  the live build said:", msg[-800:])
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    ok, msg = build_check()
    if not ok:
        print("SITE BUILD FAILED:\n" + msg, file=sys.stderr)
        return 1
    print(msg.splitlines()[-1] if msg else "SITE BUILD: ok")
    ok2, msg2 = dom_check()
    if not ok2:
        print("SITE DOM GATE FAILED:\n" + msg2, file=sys.stderr)
        return 1
    print(msg2.splitlines()[-1] if msg2 else "SITE DOM GATE: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
