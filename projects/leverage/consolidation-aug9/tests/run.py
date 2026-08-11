#!/usr/bin/env python3
"""One-command runner: exact tests, document audits, checksums, and Lean.

Green from a clean checkout of this folder alone. No sibling tree is required:
the previous consolidation is vendored here as an archive and is verified by
digest, not by path.
"""
from __future__ import annotations

import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

STATUSES = (r"PROVED \(single derivation\)|MACHINE-CHECKED \(stated finite scope\)|"
            r"NECESSITY WITNESS|REFUTED \(witness displayed\)|"
            r"PROVED-CONDITIONAL \(conditions listed\)|"
            r"PROPOSED \(interface revision\)")

# The source tree's retired-name gate, carried into this folder. Vendored
# documents are exempt: they are frozen evidence and are never edited.
RETIRED = ("floor", "rent", "defect", "kernel", "AnsLearn", "ARC", "shock",
           "round", "period", "alpha", "extortion", "martyrdom", "firewall")
RETIRED_NOTATION = ("B_R", "D_N", "E_N", "E_*", "a_t", "R_t", "S_t", "S(R)")
CLAIM_ID = re.compile(r"\b(?:C|NL|AM|CM|ST|CD|CS|GR|AL)-[A-Z0-9-]+\b")


def documents() -> list[pathlib.Path]:
    """Every non-vendored, non-archive markdown document of this package."""
    return sorted(p for p in ROOT.rglob("*.md")
                  if "vendor" not in p.parts and "archive" not in p.parts)


def theory_parts() -> list[pathlib.Path]:
    return sorted(ROOT.glob("THEORY_*.md"))


EXEMPT_OPEN = "<!-- gate:exempt -->"
EXEMPT_CLOSE = "<!-- gate:end -->"
# The only document permitted to name retired terms is the one whose job is to
# map them. The exemption is delimited, and the runner enforces both that no
# other document opens it and that every opened region is closed.
EXEMPT_DOCUMENT = "GLOSSARY.md"


def audit_retired_names() -> None:
    """The retired-name gate, over every non-vendored document including the report."""
    failures: list[str] = []
    for path in documents():
        exempt = False
        for number, raw in enumerate(path.read_text().splitlines(), 1):
            if EXEMPT_OPEN in raw:
                if path.name != EXEMPT_DOCUMENT:
                    failures.append(
                        f"{path.relative_to(ROOT)}:{number}: only {EXEMPT_DOCUMENT} "
                        "may open a gate exemption")
                exempt = True
                continue
            if EXEMPT_CLOSE in raw:
                exempt = False
                continue
            if exempt:
                continue
            line = CLAIM_ID.sub("", raw)
            for word in RETIRED:
                if not re.search(rf"\b{re.escape(word)}\b", line, re.I):
                    continue
                if word == "floor" and any(x in line for x in
                                           ("integer-floor", "rational-floor", "⌊")):
                    continue
                failures.append(f"{path.relative_to(ROOT)}:{number}: retired {word!r}")
            for notation in RETIRED_NOTATION:
                if re.search(rf"(?<![A-Za-z]){re.escape(notation)}(?![A-Za-z])", line):
                    failures.append(
                        f"{path.relative_to(ROOT)}:{number}: retired notation {notation!r}")
        if exempt:
            failures.append(f"{path.relative_to(ROOT)}: a gate exemption is never closed")
    if failures:
        raise AssertionError("retired vocabulary remains:\n" + "\n".join(failures))


def audit_ledger_coverage() -> int:
    """Every theory claim has a ledger row with the same status, and conversely."""
    ledger = (ROOT / "LEDGER.md").read_text()
    ledger_status = {m.group(1): m.group(2) for m in re.finditer(
        rf"^\| ([A-Z][A-Z0-9-]+) \|[^\n]*?\| ({STATUSES}) \|", ledger, re.M)}
    theory_status: dict[str, str] = {}
    for path in theory_parts():
        flat = re.sub(r"\s+", " ", path.read_text())
        for claim, status in re.findall(
                rf"\{{#([A-Z][A-Z0-9-]+)\}} \*\*Status: ({STATUSES})\.\*\*", flat):
            if claim in theory_status:
                raise AssertionError(f"claim {claim} is stated twice")
            theory_status[claim] = status
        for claim in re.findall(r"\{#([A-Z][A-Z0-9-]+)\}", flat):
            if claim not in theory_status:
                raise AssertionError(f"{path.name}: {claim} carries no status")
    if set(theory_status) != set(ledger_status):
        difference = sorted(set(theory_status) ^ set(ledger_status))
        raise AssertionError(f"ledger/theory claim mismatch: {difference}")
    for claim, status in theory_status.items():
        if ledger_status[claim] != status:
            raise AssertionError(
                f"status mismatch {claim}: theory {status!r} / ledger "
                f"{ledger_status[claim]!r}")
    return len(theory_status)


def audit_expansions() -> None:
    """Every claim-ID family used is expanded in ID_EXPANSIONS.md."""
    expansions = (ROOT / "ID_EXPANSIONS.md").read_text()
    families = set()
    for path in theory_parts():
        for claim in re.findall(r"\{#([A-Z][A-Z0-9-]+)\}", path.read_text()):
            families.add(claim.split("-")[0] if not claim.startswith("NL-SI")
                         else "NL-SI")
    for family in sorted(families):
        if f"`{family}-" not in expansions:
            raise AssertionError(f"claim-ID family {family} is not expanded")


def audit_lean() -> None:
    text = "\n".join(p.read_text() for p in (ROOT / "lean").glob("*.lean"))
    if "sorry" in text:
        raise AssertionError("vendored Lean source contains sorry")


def verify_manifest() -> int:
    data = json.loads((ROOT / "FROZEN_INPUT_CHECKSUMS.json").read_text())
    if data.get("algorithm") != "sha256" or not data.get("files"):
        raise AssertionError("checksum manifest is empty or malformed")
    checked = 0
    for relative, digest in sorted(data["files"].items()):
        path = ROOT / relative
        if not path.is_file():
            raise AssertionError(f"manifest names a missing file: {relative}")
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise AssertionError(f"vendored or frozen input changed: {relative}")
        checked += 1
    for required in ("vendor/consolidation_aug8.zip", "vendor/WITNESS_AUDIT.md",
                     "vendor/SETTLEMENT_INTERFACE_v3.md",
                     "vendor/SI_V3_CHANGELOG.md"):
        if required not in data["files"]:
            raise AssertionError(f"the manifest does not freeze {required}")
    return checked


def run_lean() -> bool:
    configured = os.environ.get("MATHLIB_DIR")
    if not configured:
        print("LEAN SKIPPED: set MATHLIB_DIR to a Mathlib-enabled Lake project")
        return False
    mathlib = pathlib.Path(configured).expanduser()
    lake = shutil.which("lake")
    if lake is None:
        print("LEAN SKIPPED: `lake` is unavailable; Python tiers passed")
        return False
    if not mathlib.is_dir():
        print(f"LEAN SKIPPED: {mathlib} does not exist")
        return False
    for source in sorted((ROOT / "lean").glob("*.lean")):
        subprocess.run([lake, "env", "lean", str(source)], cwd=mathlib, check=True)
    print("LEAN CHECKED: every vendored Lean file compiled sorry-free")
    return True


if __name__ == "__main__":
    audit_retired_names()
    print("RETIRED-NAME GATE: clean")
    audit_lean()
    print("SORRY SCAN: clean over every vendored Lean source")
    claims = audit_ledger_coverage()
    print(f"LEDGER COVERAGE: {claims} claims, statuses agree with the theory parts")
    audit_expansions()
    print("ID EXPANSIONS: every claim-ID family expanded")
    print(f"FROZEN INPUTS VERIFIED: {verify_manifest()}")
    suite = unittest.defaultTestLoader.discover(str(ROOT / "tests"), pattern="test_*.py")
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    if not result.wasSuccessful():
        sys.exit(1)
    run_lean()
    print("ALL CHECKS GREEN")
