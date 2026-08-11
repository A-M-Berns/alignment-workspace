#!/usr/bin/env python3
"""Gate 3: frozen integrity.

Two checks.

**Digests.** Recompute the tree hash of every registered frozen input and diff
against `frozen/FROZEN_INPUT_CHECKSUMS.json`. Any drift fails.

**The manifest rule.** In CI on a pull request, a change to anything under
`frozen/` fails unless the same pull request also updates
`frozen/MANIFEST.md`. The author's sign-off then happens through required
review. Locally, with no base ref to diff against, only the digests are checked.
"""
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
FROZEN = ROOT / "frozen"


def tree_hash(directory: pathlib.Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    count = 0
    for path in sorted(directory.rglob("*")):
        if not path.is_file() or "__pycache__" in path.parts or path.name == ".DS_Store":
            continue
        digest.update(path.relative_to(directory).as_posix().encode())
        digest.update(hashlib.sha256(path.read_bytes()).digest())
        count += 1
    return digest.hexdigest(), count


def check_digests() -> int:
    manifest = json.loads((FROZEN / "FROZEN_INPUT_CHECKSUMS.json").read_text())
    failures = []
    for name, record in sorted(manifest["entries"].items()):
        target = FROZEN / name
        if not target.is_dir():
            failures.append(f"{name}: registered but missing")
            continue
        digest, count = tree_hash(target)
        if digest != record["sha256_tree"]:
            failures.append(f"{name}: tree digest drifted\n"
                            f"    registered {record['sha256_tree']}\n"
                            f"    recomputed {digest}")
        elif count != record["files"]:
            failures.append(f"{name}: file count {count} != registered {record['files']}")
    registered = set(manifest["entries"])
    present = {p.name for p in FROZEN.iterdir() if p.is_dir()}
    for extra in sorted(present - registered):
        failures.append(f"{extra}: present under frozen/ but not registered")
    if failures:
        print("FROZEN INTEGRITY FAILED:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        sys.exit(1)
    return len(registered)


def check_manifest_rule() -> None:
    base = os.environ.get("GITHUB_BASE_REF")
    if not base:
        print("MANIFEST RULE: skipped (no pull-request base ref)")
        return
    subprocess.run(["git", "fetch", "--depth=1", "origin", base],
                   cwd=ROOT, capture_output=True)
    diff = subprocess.run(["git", "diff", "--name-only", f"origin/{base}...HEAD"],
                          cwd=ROOT, capture_output=True, text=True)
    changed = [line for line in diff.stdout.splitlines() if line.strip()]
    touched = [c for c in changed if c.startswith("frozen/")]
    if not touched:
        print("MANIFEST RULE: no frozen/ file touched")
        return
    if "frozen/MANIFEST.md" not in changed:
        print("FROZEN INTEGRITY FAILED: this pull request modifies frozen content "
              "without updating frozen/MANIFEST.md:", file=sys.stderr)
        for t in touched:
            print(f"  - {t}", file=sys.stderr)
        print("  Frozen inputs are immutable. Register a new dated entry instead of "
              "editing one.", file=sys.stderr)
        sys.exit(1)
    print(f"MANIFEST RULE: {len(touched)} frozen path(s) touched, MANIFEST.md updated "
          "in the same pull request — author review decides")


if __name__ == "__main__":
    print(f"FROZEN DIGESTS VERIFIED: {check_digests()} registered inputs")
    check_manifest_rule()
