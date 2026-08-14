"""Validate the local repository/wiki handshake for this coordinated round.

Usage:
    python3 prompts/2026-08-13-wikification-and-normativity/cross_repo_check.py \
        --wiki ../alignment-workspace.wiki
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from urllib.parse import unquote


ROOT = pathlib.Path(__file__).resolve().parents[2]
REPO_URL = "https://github.com/A-M-Berns/alignment-workspace"
WIKI_URL = f"{REPO_URL}/wiki/"
PINNED_REPO_LINK = re.compile(
    rf"{re.escape(REPO_URL)}/(blob|tree)/([^/)]+)/([^)#]+)"
)
MARKDOWN_LINK = re.compile(r"\[[^]]*\]\(([^)]+)\)")
ESTABLISHED = re.compile(
    r"\*\*Established\s+—\s+"
    r"(lean-proved|enumeration-verified|witness-checked|contributor-checked|test-supported)\*\*"
)


def markdown_files(root: pathlib.Path) -> list[pathlib.Path]:
    return sorted(path for path in root.rglob("*.md") if ".git" not in path.parts)


def wiki_target(raw: str) -> str | None:
    target = raw.split("#", 1)[0]
    if target.startswith(WIKI_URL):
        return unquote(target.removeprefix(WIKI_URL)).rstrip("/")
    if "://" not in target and target and not target.startswith("#"):
        return unquote(target).removesuffix(".md")
    return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--wiki", required=True, type=pathlib.Path)
    args = parser.parse_args()
    wiki = args.wiki.resolve()
    problems: list[str] = []

    wiki_pages = {path.stem for path in markdown_files(wiki)}
    repo_pointer_count = 0
    for path in markdown_files(ROOT):
        for raw in MARKDOWN_LINK.findall(path.read_text(errors="replace")):
            if not raw.startswith(WIKI_URL):
                continue
            repo_pointer_count += 1
            target = wiki_target(raw)
            if target not in wiki_pages:
                problems.append(f"repo pointer does not resolve: {path.relative_to(ROOT)} -> {raw}")

    internal_link_count = 0
    pinned_link_count = 0
    established_count = 0
    claims_text = (ROOT / "projects/normativity/CLAIMS.md").read_text()
    claim_ids = set(re.findall(r"^###\s+([a-z0-9][a-z0-9.-]+)\s*$", claims_text, re.M))
    wiki_texts: dict[str, str] = {}
    for path in markdown_files(wiki):
        text = path.read_text()
        wiki_texts[path.stem] = text
        for raw in MARKDOWN_LINK.findall(text):
            target = wiki_target(raw)
            if target is not None and not raw.startswith(WIKI_URL):
                internal_link_count += 1
                if target not in wiki_pages:
                    problems.append(f"wiki link does not resolve: {path.name} -> {raw}")
        for match in PINNED_REPO_LINK.finditer(text):
            pinned_link_count += 1
            kind, ref, repo_path = match.groups()
            if not re.fullmatch(r"[0-9a-f]{40}", ref):
                problems.append(f"repo citation is not commit-pinned: {path.name}: {ref}")
            target = ROOT / unquote(repo_path)
            if not target.exists() or (kind == "blob" and not target.is_file()) or (
                kind == "tree" and not target.is_dir()
            ):
                problems.append(f"repo citation path does not resolve: {path.name}: {repo_path}")
        for match in ESTABLISHED.finditer(text):
            established_count += 1
            paragraph = text[match.start():text.find("\n\n", match.start())]
            named = claim_ids.intersection(re.findall(r"`([^`]+)`", paragraph))
            if not named:
                problems.append(f"Established label lacks a registered claim ID: {path.name}")

    vocabulary = json.loads((ROOT / "state/vocabulary.json").read_text())["terms"]
    combined_wiki = "\n".join(wiki_texts.values()).casefold()
    for term in vocabulary:
        if term["preferred"].casefold() not in combined_wiki:
            problems.append(f"preferred vocabulary is absent from wiki: {term['id']}")

    ledger = json.loads((ROOT / "state/theorem_interface.json").read_text())
    architecture = wiki_texts.get("Architecture", "")
    for obj in ledger["objects"]:
        if f"`{obj['notation']}`" not in architecture and obj["notation"] != "coverage":
            problems.append(f"Architecture omits interface notation: {obj['notation']}")
        if obj["notation"] == "coverage" and "| coverage |" not in architecture:
            problems.append("Architecture omits interface notation: coverage")
        for key in ("presentation_requirements", "excluded_from_loss"):
            for value in obj.get(key, []):
                if value.replace("-", " ") not in architecture.replace("-", " "):
                    problems.append(f"Architecture omits {obj['id']} {key}: {value}")
    for module in ledger["modules"]:
        if module["path"] not in architecture:
            problems.append(f"Architecture omits registered module path: {module['id']}")

    if problems:
        print("CROSS-REPO STATE: FAILED")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print(
        "CROSS-REPO STATE: valid — "
        f"{repo_pointer_count} repo pointers, {internal_link_count} internal wiki links, "
        f"{pinned_link_count} pinned repo citations, {established_count} Established claims, "
        f"{len(vocabulary)} vocabulary terms, {len(ledger['objects'])} interface objects"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
