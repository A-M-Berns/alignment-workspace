"""Validate and emit the repository's structured current state.

Usage:
    python3 -m checkers.workspace_state --check
    python3 -m checkers.workspace_state --json
"""
from __future__ import annotations

import json
import pathlib
import re
import sys
from typing import Any

from checkers import registry

ROOT = pathlib.Path(__file__).resolve().parents[1]
STATE = ROOT / "state"
PRIORITY = re.compile(r"^###\s+(\d+)\.\s+(.+?)\s*$", re.M)
SPECIAL_PRIORITY = re.compile(r"^###\s+([QF]\d+)\s+—\s+(.+?)\s*$", re.M)


def load_json(name: str) -> Any:
    return json.loads((STATE / name).read_text())


def priority_project(identifier: str) -> str | None:
    if identifier.startswith("Q"):
        return "deference"
    if identifier.startswith("F"):
        return None
    number = int(identifier)
    if number in {*range(1, 7), *range(29, 34), 35}:
        return "normativity"
    if number in {*range(7, 10), *range(14, 29), 34}:
        return "deference"
    return None


def priorities() -> list[dict[str, Any]]:
    items = []
    text = (ROOT / "PRIORITIES.md").read_text()
    matches = list(PRIORITY.finditer(text)) + list(SPECIAL_PRIORITY.finditer(text))
    for match in sorted(matches, key=lambda item: item.start()):
        identifier, heading = match.groups()
        marks = re.findall(r"\*\*\[([^]]+)\]\*\*", heading)
        title = re.sub(r"\s+—\s+\*\*\[[^]]+\]\*\*.*$", "", heading)
        items.append({
            "id": identifier,
            "project": priority_project(identifier),
            "title": title,
            "state": (marks[0] if marks else
                      "question" if identifier.startswith("Q") else
                      "workspace-friction"),
            "dependencies": [],
            "origin": "PRIORITIES.md",
            "specified_enough_to_dispatch": not (identifier == "35" or identifier[0] in "QF"),
        })
    return items


def current_state() -> dict[str, Any]:
    project_data = load_json("projects.json")["projects"]
    round_data = load_json("rounds.json")["rounds"]
    vocabulary = load_json("vocabulary.json")["terms"]
    interface = load_json("theorem_interface.json")
    registries = sorted(ROOT.glob("projects/*/CLAIMS.md"))
    claims = []
    for path in registries:
        for claim in registry.parse(path):
            claim["registry"] = path.relative_to(ROOT).as_posix()
            claims.append(claim)
    return {
        "projects": project_data,
        "claims": claims,
        "rounds": round_data,
        "vocabulary": vocabulary,
        "priorities": priorities(),
        "interfaces": [interface],
    }


def duplicates(values: list[str]) -> set[str]:
    return {value for value in values if values.count(value) > 1}


def validate(data: dict[str, Any]) -> list[str]:
    problems: list[str] = []
    projects = {p["id"]: p for p in data["projects"]}
    rounds = {r["id"]: r for r in data["rounds"]}
    claims = {c["id"]: c for c in data["claims"]}
    lifecycle_statuses = {"active", "superseded", "refuted"}
    completed_rounds = {
        path.name for path in (ROOT / "prompts").iterdir()
        if path.is_dir() and any(path.glob("REPORT*.md"))
    }
    indexed_rounds = set(rounds)
    if missing := completed_rounds - indexed_rounds:
        problems.append(f"completed prompt round(s) missing from index: {sorted(missing)}")

    for kind, rows in (("project", data["projects"]), ("round", data["rounds"]),
                       ("claim", data["claims"]), ("term", data["vocabulary"]),
                       ("priority", data["priorities"])):
        repeated = duplicates([str(row["id"]) for row in rows])
        if repeated:
            problems.append(f"duplicate {kind} id(s): {sorted(repeated)}")

    registries = sorted(ROOT.glob("projects/*/CLAIMS.md"))
    if len(registries) != 1:
        problems.append(f"expected exactly one authoritative CLAIMS.md; found {len(registries)}")

    for project in data["projects"]:
        if project["status"] == "active":
            if not project.get("path") or not (ROOT / project["path"]).exists():
                problems.append(f"project {project['id']}: active path does not exist")
            for entry in project.get("entry_points", []):
                if not (ROOT / entry).exists():
                    problems.append(f"project {project['id']}: entry point does not exist: {entry}")
        parent = project.get("parent")
        if parent and parent not in projects:
            problems.append(f"project {project['id']}: unknown parent {parent}")
        replacement = project.get("replacement_project")
        if replacement and replacement not in projects:
            problems.append(f"project {project['id']}: unknown replacement {replacement}")

    for round_ in data["rounds"]:
        if not (ROOT / round_["path"]).exists():
            problems.append(f"round {round_['id']}: path does not exist: {round_['path']}")
        prompt = round_.get("prompt")
        if prompt is not None and not (ROOT / prompt).exists():
            problems.append(f"round {round_['id']}: prompt does not exist: {prompt}")
        verdict = round_.get("verdict")
        verdict_source = round_.get("verdict_source")
        if verdict is not None:
            if not verdict_source or not (ROOT / verdict_source).exists():
                problems.append(f"round {round_['id']}: verdict source does not exist")
            else:
                source = (ROOT / verdict_source).read_text().replace("`", "")
                source = " ".join(source.split())
                if " ".join(verdict.split()) not in source:
                    problems.append(f"round {round_['id']}: verdict is not verbatim in "
                                    f"{verdict_source}: {verdict!r}")
        project = round_.get("project")
        if project and (project not in projects or projects[project]["status"] != "active"):
            problems.append(f"round {round_['id']}: project is not active: {project}")
        bad_classes = set(round_.get("registered_classes", [])) - set(registry.CLASSES)
        if bad_classes:
            problems.append(f"round {round_['id']}: unknown classes {sorted(bad_classes)}")
        for claim_id in round_.get("claim_changes", []):
            if claim_id not in claims:
                problems.append(f"round {round_['id']}: unknown claim {claim_id}")

    for claim in data["claims"]:
        owner = claim.get("project")
        if owner not in projects or projects[owner]["status"] != "active":
            problems.append(f"claim {claim['id']}: owner is not an active project: {owner}")
        if claim.get("class") not in registry.CLASSES:
            problems.append(f"claim {claim['id']}: unknown epistemic class {claim.get('class')}")
        if claim.get("status") not in lifecycle_statuses:
            problems.append(f"claim {claim['id']}: unknown lifecycle status "
                            f"{claim.get('status')!r}")
        origin = claim.get("origin_round")
        if origin is not None and origin not in rounds:
            problems.append(f"claim {claim['id']}: unknown origin round {origin}")
        for field in ("supersedes", "superseded_by"):
            target = claim.get(field)
            if target is not None:
                if target == claim["id"]:
                    problems.append(f"claim {claim['id']}: {field} is self-referential")
                elif target not in claims:
                    problems.append(f"claim {claim['id']}: {field} target does not resolve: {target}")
        for target in claim.get("dependencies", []):
            if target not in claims:
                problems.append(f"claim {claim['id']}: dependency does not resolve: {target}")
        for path in claim.get("docs", {}).values():
            if not (ROOT / path).exists():
                problems.append(f"claim {claim['id']}: documentation path does not exist: {path}")

    for item in data["priorities"]:
        project = item.get("project")
        if project is not None and (project not in projects or
                                    projects[project]["status"] != "active"):
            problems.append(f"priority {item['id']}: project is not active: {project}")

    aliases: dict[tuple[str, str], list[str]] = {}
    for term in data["vocabulary"]:
        scope = term.get("scope", "")
        aliases.setdefault((scope, term["preferred"].casefold()), []).append(term["id"])
        for alias in term.get("aliases", []) + term.get("deprecated_aliases", []):
            aliases.setdefault((scope, alias.casefold()), []).append(term["id"])
    for (scope, alias), term_ids in aliases.items():
        if len(term_ids) > 1:
            problems.append(f"vocabulary alias {alias!r} in scope {scope!r} "
                            f"resolves ambiguously: {term_ids}")

    for interface in data["interfaces"]:
        project = interface.get("project")
        if project not in projects or projects[project]["status"] != "active":
            problems.append(f"interface {interface['interface_id']}: project is not active: "
                            f"{project}")
        module_rows = interface.get("modules", [])
        if duplicates([module["id"] for module in module_rows]):
            problems.append(f"interface {interface['interface_id']}: duplicate module ids")
        modules = {module["id"]: module for module in module_rows}
        for module in modules.values():
            if not (ROOT / module["path"]).exists():
                problems.append(f"interface module {module['id']}: path does not exist: "
                                f"{module['path']}")
        object_ids = [obj["id"] for obj in interface["objects"]]
        if duplicates(object_ids):
            problems.append(f"interface {interface['interface_id']}: duplicate object ids")
        for obj in interface["objects"]:
            for module_id in obj.get("producers", []) + obj.get("consumers", []):
                if module_id not in modules:
                    problems.append(f"interface {obj['id']}: unknown module {module_id}")
            for claim_id in obj.get("soundness_claim_ids", []):
                if claim_id not in claims:
                    problems.append(f"interface {obj['id']}: unknown claim {claim_id}")

    for path, expected in render_handoffs(data).items():
        target = ROOT / path
        if not target.exists():
            problems.append(f"generated handoff view is missing: {path}")
        elif target.read_text() != expected:
            problems.append(f"generated handoff view is stale: {path}")

    return problems


def render_handoffs(data: dict[str, Any]) -> dict[str, str]:
    base = "prompts/2026-08-13-wikification-and-normativity"
    command = "python3 -m checkers.workspace_state --write-handoff"

    paths = ["# Final path map", "", f"Generated from `state/projects.json` by `{command}`.", "",
             "| stable ID | display name | status | parent | path | entry points |",
             "|---|---|---|---|---|---|"]
    for project in data["projects"]:
        paths.append("| {id} | {name} | {status} | {parent} | {path} | {entries} |".format(
            id=project["id"], name=project["name"], status=project["status"],
            parent=project.get("parent") or "—", path=project.get("path") or "—",
            entries="<br>".join(f"`{entry}`" for entry in project.get("entry_points", [])) or "—"))

    vocabulary = ["# Canonical vocabulary sheet", "",
                  f"Generated from `state/vocabulary.json` by `{command}`.", "",
                  "| stable ID | preferred | aliases | deprecated aliases | scope | repo identifiers |",
                  "|---|---|---|---|---|---|"]
    for term in data["vocabulary"]:
        vocabulary.append("| {id} | {preferred} | {aliases} | {deprecated} | {scope} | {repo} |".format(
            id=term["id"], preferred=term["preferred"],
            aliases=", ".join(term.get("aliases", [])) or "—",
            deprecated=", ".join(term.get("deprecated_aliases", [])) or "—",
            scope=term.get("scope", "—"),
            repo=", ".join(term.get("repo_identifiers", [])) or "—"))

    rounds = ["# Verdict/status inventory", "",
              f"Generated from `state/rounds.json` and the sole claims registry by `{command}`.", "",
              "Registered classes are classes actually promoted by the round; an empty cell means no claim was registered.", "",
              "| round ID | date | project | current path | verdict (verbatim) | registered classes | prompt | claim changes |",
              "|---|---|---|---|---|---|---|---|"]
    for round_ in data["rounds"]:
        rounds.append("| {id} | {date} | {project} | `{path}` | {verdict} | {classes} | `{prompt}` | {claims} |".format(
            id=round_["id"], date=round_["date"], project=round_.get("project") or "workspace",
            path=round_["path"], verdict=round_.get("verdict") or "—",
            classes=", ".join(round_.get("registered_classes", [])) or "—",
            prompt=round_.get("prompt") or "—",
            claims=", ".join(round_.get("claim_changes", [])) or "—"))

    return {
        f"{base}/FINAL_PATH_MAP.md": "\n".join(paths) + "\n",
        f"{base}/VOCABULARY_SHEET.md": "\n".join(vocabulary) + "\n",
        f"{base}/VERDICT_STATUS_INVENTORY.md": "\n".join(rounds) + "\n",
    }


def self_test() -> bool:
    data = current_state()
    data["projects"][0]["entry_points"].append("missing/stale-path.md")
    problems = validate(data)
    passed = any("missing/stale-path.md" in problem for problem in problems)
    print("WORKSPACE STATE SELF-TEST:")
    print(f"  {'ok' if passed else 'FAILED'}: stale registered path fails loudly")
    return passed


def main(args: list[str]) -> int:
    if args == ["--self-test"]:
        return 0 if self_test() else 1
    if args == ["--write-handoff"]:
        data = current_state()
        for path, content in render_handoffs(data).items():
            target = ROOT / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content)
            print(path)
        return 0
    if args not in (["--check"], ["--json"]):
        print(__doc__.strip())
        return 2
    data = current_state()
    problems = validate(data)
    if args == ["--json"]:
        if problems:
            print(json.dumps({"valid": False, "problems": problems}, indent=2))
            return 1
        print(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False))
        return 0
    if problems:
        print("WORKSPACE STATE: FAILED")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print(f"WORKSPACE STATE: valid — {len(data['projects'])} projects, "
          f"{len(data['claims'])} claims, {len(data['rounds'])} rounds, "
          f"{len(data['vocabulary'])} terms, {len(data['priorities'])} priorities, "
          f"{sum(len(i['objects']) for i in data['interfaces'])} interface objects")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
