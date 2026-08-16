"""Validate the local repository/wiki semantic handshake.

Usage:
    python3 prompts/2026-08-13-wikification-and-normativity/cross_repo_check.py \
        --wiki ../alignment-workspace.wiki
    python3 prompts/2026-08-13-wikification-and-normativity/cross_repo_check.py --self-test
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
from typing import Any
from urllib.parse import unquote


ROOT = pathlib.Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
REPO_URL = "https://github.com/A-M-Berns/alignment-workspace"
WIKI_URL = f"{REPO_URL}/wiki/"
PINNED_REPO_LINK = re.compile(
    rf"{re.escape(REPO_URL)}/(blob|tree)/([^/)]+)/([^)#]+)"
)
MARKDOWN_LINK = re.compile(r"\[[^]]*\]\(([^)]+)\)")
ESTABLISHED_MARKER = re.compile(
    r"<!--\s*established-claim:\s*([a-z0-9][a-z0-9.-]+)\s+"
    r"class=(lean-proved|enumeration-verified|witness-checked|"
    r"contributor-checked|test-supported)\s*-->"
)
ESTABLISHED_LABEL = re.compile(
    r"\*\*Established\s+—\s+`?(lean-proved|enumeration-verified|"
    r"witness-checked|contributor-checked|test-supported)`?\.?\*\*"
)
TABLE_ROW = re.compile(r"^\|(.+)\|\s*$", re.M)


def markdown_files(root: pathlib.Path) -> list[pathlib.Path]:
    return sorted(path for path in root.rglob("*.md") if ".git" not in path.parts)


def wiki_target(raw: str) -> str | None:
    target = raw.split("#", 1)[0]
    if target.startswith(WIKI_URL):
        return unquote(target.removeprefix(WIKI_URL)).rstrip("/")
    if "://" not in target and target and not target.startswith("#"):
        return unquote(target).removesuffix(".md")
    return None


def clean_cell(value: str) -> str:
    return value.strip().replace("`", "")


def list_cell(value: str) -> list[str]:
    value = clean_cell(value)
    if value in {"", "—", "null"}:
        return []
    return [part.strip() for part in value.split(";")]


def marked_table(text: str, marker: str) -> tuple[list[str], list[dict[str, str]]]:
    start = text.find(marker)
    if start < 0:
        return [], []
    lines = text[start + len(marker):].splitlines()
    table_lines = []
    started = False
    for line in lines:
        if line.startswith("|"):
            started = True
            table_lines.append(line)
        elif started:
            break
    if len(table_lines) < 2:
        return [], []
    headers = [clean_cell(cell) for cell in table_lines[0].strip("|").split("|")]
    rows = []
    for line in table_lines[2:]:
        cells = [clean_cell(cell) for cell in line.strip("|").split("|")]
        if len(cells) == len(headers):
            rows.append(dict(zip(headers, cells)))
    return headers, rows


def claims_by_id() -> dict[str, dict[str, Any]]:
    from checkers import registry

    registries = sorted(ROOT.glob("projects/*/CLAIMS.md"))
    claims: dict[str, dict[str, Any]] = {}
    for path in registries:
        for claim in registry.parse(path):
            claims[claim["id"]] = claim
    return claims


def validate_established(text: str, page: str,
                         claims: dict[str, dict[str, Any]]) -> tuple[int, list[str]]:
    problems: list[str] = []
    labels = list(ESTABLISHED_LABEL.finditer(text))
    markers = list(ESTABLISHED_MARKER.finditer(text))
    for label in labels:
        nearby = [marker for marker in markers if abs(marker.start() - label.start()) < 400]
        if len(nearby) != 1:
            problems.append(f"Established label needs exactly one nearby structured claim marker: {page}")
            continue
        marker = nearby[0]
        claim_id, marker_class = marker.groups()
        displayed_class = label.group(1)
        claim = claims.get(claim_id)
        if claim is None:
            problems.append(f"Established marker names unknown claim {claim_id}: {page}")
        elif claim.get("class") != marker_class or marker_class != displayed_class:
            problems.append(
                f"Established class mismatch for {claim_id}: registry={claim.get('class') if claim else None}, "
                f"marker={marker_class}, displayed={displayed_class}: {page}"
            )
    for marker in markers:
        if not any(abs(marker.start() - label.start()) < 400 for label in labels):
            problems.append(f"Established claim marker lacks nearby displayed label: {page}")
    return len(labels), problems


def architecture_projection(ledger: dict[str, Any]) -> dict[str, dict[str, Any]]:
    projection = {}
    for obj in ledger["objects"]:
        projection[obj["id"]] = {
            "notation": obj["notation"],
            "kind": obj["kind"],
            "producers": obj.get("producers", []),
            "consumers": obj.get("consumers", []),
            "write access": obj.get("write_access", []),
            "excluded from loss": obj.get("excluded_from_loss", []),
            "presentation requirements": obj.get("presentation_requirements", []),
            "registered status": "null" if obj.get("registered_status") is None
                                 else str(obj["registered_status"]),
            "soundness claim IDs": obj.get("soundness_claim_ids", []),
        }
    return projection


def architecture_rows(text: str) -> dict[str, dict[str, Any]]:
    _, rows = marked_table(text, "<!-- theorem-interface-ledger: normativity.learning.current -->")
    parsed = {}
    for row in rows:
        identifier = clean_cell(row.get("ID", ""))
        parsed[identifier] = {
            "notation": clean_cell(row.get("notation", "")),
            "kind": clean_cell(row.get("kind", "")),
            "producers": list_cell(row.get("producers", "")),
            "consumers": list_cell(row.get("consumers", "")),
            "write access": list_cell(row.get("write access", "")),
            "excluded from loss": list_cell(row.get("excluded from loss", "")),
            "presentation requirements": list_cell(row.get("presentation requirements", "")),
            "registered status": clean_cell(row.get("registered status", "")),
            "soundness claim IDs": list_cell(row.get("soundness claim IDs", "")),
        }
    return parsed


def compare_architecture(text: str, ledger: dict[str, Any]) -> list[str]:
    expected = architecture_projection(ledger)
    actual = architecture_rows(text)
    problems = []
    if set(actual) != set(expected):
        problems.append(f"Architecture object IDs differ: wiki={sorted(actual)}, repo={sorted(expected)}")
    for identifier in sorted(set(actual) & set(expected)):
        for field, value in expected[identifier].items():
            if actual[identifier].get(field) != value:
                problems.append(
                    f"Architecture {identifier} {field} mismatch: "
                    f"wiki={actual[identifier].get(field)!r}, repo={value!r}"
                )
    return problems


def architecture_fixture(ledger: dict[str, Any]) -> str:
    fields = ["ID", "notation", "kind", "producers", "consumers", "write access",
              "excluded from loss", "presentation requirements", "registered status",
              "soundness claim IDs"]
    lines = ["<!-- theorem-interface-ledger: normativity.learning.current -->",
             "| " + " | ".join(fields) + " |",
             "|" + "|".join("---" for _ in fields) + "|"]
    for identifier, row in architecture_projection(ledger).items():
        values = [identifier]
        for field in fields[1:]:
            value = row[field]
            values.append("; ".join(value) if isinstance(value, list) and value else
                          "—" if isinstance(value, list) else value)
        lines.append("| " + " | ".join(values) + " |")
    return "\n".join(lines)


def vocabulary_rows(text: str) -> dict[str, dict[str, Any]]:
    _, rows = marked_table(text, "<!-- vocabulary-ledger -->")
    return {
        clean_cell(row["stable ID"]): {
            "preferred": clean_cell(row["preferred"]),
            "aliases": list_cell(row["aliases"]),
            "deprecated aliases": list_cell(row["deprecated aliases"]),
        }
        for row in rows
    }


def compare_vocabulary(text: str, terms: list[dict[str, Any]]) -> list[str]:
    expected = {
        term["id"]: {
            "preferred": term["preferred"],
            "aliases": term.get("aliases", []),
            "deprecated aliases": term.get("deprecated_aliases", []),
        }
        for term in terms
    }
    actual = vocabulary_rows(text)
    problems = []
    if set(actual) != set(expected):
        problems.append(f"Glossary vocabulary IDs differ: wiki={sorted(actual)}, repo={sorted(expected)}")
    for identifier in sorted(set(actual) & set(expected)):
        if actual[identifier] != expected[identifier]:
            problems.append(
                f"Glossary vocabulary mismatch for {identifier}: "
                f"wiki={actual[identifier]!r}, repo={expected[identifier]!r}"
            )
    return problems


def git_object_type(ref: str, path: str) -> str | None:
    result = subprocess.run(
        ["git", "cat-file", "-t", f"{ref}:{path}"], cwd=ROOT,
        text=True, capture_output=True
    )
    return result.stdout.strip() if result.returncode == 0 else None


def self_test() -> bool:
    ledger = json.loads((ROOT / "state/theorem_interface.json").read_text())
    valid_architecture = architecture_fixture(ledger)

    fake_claims = {"claim.example": {"id": "claim.example", "class": "lean-proved"}}
    _, wrong_class = validate_established(
        "**Established — witness-checked.**\n"
        "<!-- established-claim: claim.example class=witness-checked -->",
        "fixture.md", fake_claims
    )

    producer_fixture = valid_architecture.replace(
        "substrate.relational-answerability; interface.normative",
        "wrong.producer; interface.normative", 1
    )
    producer_mismatch = any("producers mismatch" in problem
                            for problem in compare_architecture(producer_fixture, ledger))

    write_fixture = valid_architecture.replace("public-pre-action-record", "wrong-writer", 1)
    write_mismatch = any("write access mismatch" in problem
                         for problem in compare_architecture(write_fixture, ledger))

    stale_pointer = wiki_target(f"{WIKI_URL}Missing-Page") not in {"Home"}

    cases = [
        ("wrong Established epistemic class fails", bool(wrong_class)),
        ("Architecture producer mismatch fails", producer_mismatch),
        ("Architecture write-access mismatch fails", write_mismatch),
        ("stale repo-to-wiki page link fails", stale_pointer),
    ]
    print("CROSS-REPO SELF-TEST:")
    for label, passed in cases:
        print(f"  {'ok' if passed else 'FAILED'}: {label}")
    return all(passed for _, passed in cases)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--wiki", type=pathlib.Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return 0 if self_test() else 1
    if args.wiki is None:
        parser.error("--wiki is required unless --self-test is used")

    wiki = args.wiki.resolve()
    problems: list[str] = []
    pages = markdown_files(wiki)
    wiki_pages = {path.stem for path in pages}

    repo_pointer_count = 0
    for path in markdown_files(ROOT):
        for raw in MARKDOWN_LINK.findall(path.read_text(errors="replace")):
            if not raw.startswith(WIKI_URL):
                continue
            repo_pointer_count += 1
            if wiki_target(raw) not in wiki_pages:
                problems.append(f"repo pointer does not resolve: {path.relative_to(ROOT)} -> {raw}")

    internal_link_count = 0
    pinned_link_count = 0
    established_count = 0
    claims = claims_by_id()
    wiki_texts: dict[str, str] = {}
    reference_pages = {"Home", "Roadmap", "Glossary", "Sources", "_Sidebar"}
    for path in pages:
        text = path.read_text()
        wiki_texts[path.stem] = text
        for raw in MARKDOWN_LINK.findall(text):
            target = wiki_target(raw)
            if target is not None and not raw.startswith(WIKI_URL):
                internal_link_count += 1
                if target not in wiki_pages:
                    problems.append(f"wiki link does not resolve: {path.name} -> {raw}")
        for kind, ref, repo_path in PINNED_REPO_LINK.findall(text):
            pinned_link_count += 1
            if not re.fullmatch(r"[0-9a-f]{40}", ref):
                problems.append(f"repo citation is not commit-pinned: {path.name}: {ref}")
                continue
            object_type = git_object_type(ref, unquote(repo_path))
            wanted = "blob" if kind == "blob" else "tree"
            if object_type != wanted:
                problems.append(
                    f"repo citation does not resolve at pin: {path.name}: "
                    f"{ref}:{repo_path} ({object_type!r}, wanted {wanted})"
                )
        count, established_problems = validate_established(text, path.name, claims)
        established_count += count
        problems.extend(established_problems)
        if path.stem not in reference_pages and "Current status" not in text:
            problems.append(f"substantive page lacks a scoped Current status block: {path.name}")

    terms = json.loads((ROOT / "state/vocabulary.json").read_text())["terms"]
    problems.extend(compare_vocabulary(wiki_texts.get("Glossary", ""), terms))

    ledger = json.loads((ROOT / "state/theorem_interface.json").read_text())
    problems.extend(compare_architecture(wiki_texts.get("Architecture", ""), ledger))

    sidebar_targets = {
        target for raw in MARKDOWN_LINK.findall(wiki_texts.get("_Sidebar", ""))
        if (target := wiki_target(raw)) is not None
    }
    linked_targets = {
        target for text in wiki_texts.values() for raw in MARKDOWN_LINK.findall(text)
        if (target := wiki_target(raw)) is not None
    }
    for page in wiki_pages - {"_Sidebar", "Home"}:
        if page not in sidebar_targets and page not in linked_targets:
            problems.append(f"orphan wiki page: {page}")

    if problems:
        print("CROSS-REPO STATE: FAILED")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print(
        "CROSS-REPO STATE: valid — "
        f"{repo_pointer_count} repo pointers, {internal_link_count} internal wiki links, "
        f"{pinned_link_count} pinned repo citations, {established_count} Established claims, "
        f"{len(terms)} vocabulary terms, {len(ledger['objects'])} interface objects"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
