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
    ok, msg = build_check()
    cases.append(("the live tree builds", ok, True))
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
    if ok:
        print(msg.splitlines()[-1] if msg else "SITE BUILD: ok")
        return 0
    print("SITE BUILD FAILED:\n" + msg, file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
