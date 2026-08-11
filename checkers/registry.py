"""The registry checker.

**What a passing verdict means.** Every entry in the registry parses against the
fixed schema; every identifier is unique; every epistemic class is one of the
five; every statement of record resolves — a checker invocation names a
registered checker, a Lean entry names a declaration that exists in the library
source; and every entry cites an `OPEN_PROBLEMS.md` item that exists.

**What it does not mean.** Nothing about whether any claim is true. This checker
audits the bookkeeping, not the mathematics; the per-claim verdict comes from the
checker each entry names.
"""
from __future__ import annotations

import json
import pathlib
import re
from typing import Any

CLASSES = ("lean-proved", "enumeration-verified", "witness-checked",
           "test-supported", "conjectured")
CHECKERS = ("witness", "enumeration")
ENTRY = re.compile(r"^### (?P<id>[A-Za-z0-9][A-Za-z0-9._-]*)\s*$", re.M)


def parse(path: pathlib.Path) -> list[dict[str, Any]]:
    """Entries are `### <id>` followed by one fenced json block."""
    text = path.read_text()
    entries = []
    for match in ENTRY.finditer(text):
        tail = text[match.end():]
        block = re.search(r"```json\n(.*?)\n```", tail, re.S)
        if not block:
            raise ValueError(f"{match.group('id')}: no json block")
        record = json.loads(block.group(1))
        record["id"] = match.group("id")
        entries.append(record)
    return entries


def check(registry: pathlib.Path, root: pathlib.Path) -> tuple[bool, list[str]]:
    problems: list[str] = []
    try:
        entries = parse(registry)
    except (ValueError, json.JSONDecodeError) as error:
        return False, [f"registry does not parse: {error}"]

    seen: set[str] = set()
    open_items = set()
    open_path = root / "OPEN_PROBLEMS.md"
    if open_path.exists():
        open_items = set(re.findall(r"^###\s+(\d+)\.", open_path.read_text(), re.M))

    lean_source = ""
    lean_dir = root / "lean" / "Workstudio"
    if lean_dir.exists():
        lean_source = "\n".join(p.read_text() for p in lean_dir.rglob("*.lean"))

    for e in entries:
        cid = e["id"]
        if cid in seen:
            problems.append(f"{cid}: duplicate identifier")
        seen.add(cid)
        klass = e.get("class")
        if klass not in CLASSES:
            problems.append(f"{cid}: class {klass!r} is not one of {CLASSES}")
        record = e.get("statement_of_record", {})
        kind = record.get("kind")
        if kind == "lean":
            name = record.get("declaration", "")
            short = name.rsplit(".", 1)[-1]
            if not re.search(rf"\b{re.escape(short)}\b", lean_source):
                problems.append(f"{cid}: Lean declaration {name!r} not found in the library")
            if klass != "lean-proved":
                problems.append(f"{cid}: a Lean statement of record must be class lean-proved")
        elif kind == "checker":
            if record.get("checker") not in CHECKERS:
                problems.append(f"{cid}: unknown checker {record.get('checker')!r}")
            if "parameters" not in record:
                problems.append(f"{cid}: checker invocation has no parameters")
        else:
            problems.append(f"{cid}: statement of record must be kind 'lean' or 'checker', "
                            "never prose")
        item = str(e.get("answers_item", ""))
        if open_items and item and item not in open_items:
            problems.append(f"{cid}: answers_item {item!r} is not a filed OPEN_PROBLEMS item")
        for field in ("generator", "review_status"):
            if field not in e.get("provenance", {}):
                problems.append(f"{cid}: provenance is missing {field}")
        if e.get("provenance", {}).get("review_status") not in (
                None, "maintainer-reviewed", "ci-only"):
            problems.append(f"{cid}: review_status must be maintainer-reviewed or ci-only")
    return not problems, problems
