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
PRIORITY = re.compile(r"^###\s+(?:(\d+)\.|([A-Z]\d+)\s+—)\s+(.+?)\s*$", re.M)
PRIORITY_META = re.compile(
    r"<!--\s*workspace-priority:\s*project=([a-z0-9.-]+|none);\s*"
    r"dispatchable=(yes|no)\s*-->"
)
FOUNDATION_ROW = re.compile(r"^\|\s*([A-Z0-9][A-Z0-9-]*)\s*\|", re.M)


def load_json(name: str) -> Any:
    return json.loads((STATE / name).read_text())


def parse_priorities(text: str) -> list[dict[str, Any]]:
    items = []
    matches = list(PRIORITY.finditer(text))
    for index, match in enumerate(matches):
        identifier = match.group(1) or match.group(2)
        heading = match.group(3)
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        metadata = PRIORITY_META.search(text, match.end(), end)
        marks = re.findall(r"\*\*\[([^]]+)\]\*\*", heading)
        title = re.sub(r"\s+—\s+\*\*\[[^]]+\]\*\*.*$", "", heading)
        items.append({
            "id": identifier,
            "project": (None if metadata and metadata.group(1) == "none"
                        else metadata.group(1) if metadata else None),
            "title": title,
            "state": marks[0] if marks else "unclassified",
            "dependencies": [],
            "origin": "PRIORITIES.md",
            "specified_enough_to_dispatch": bool(metadata and metadata.group(2) == "yes"),
            "metadata_present": metadata is not None,
        })
    return items


def priorities() -> list[dict[str, Any]]:
    return parse_priorities((ROOT / "PRIORITIES.md").read_text())


def foundation_claim_count(path: pathlib.Path) -> int | None:
    if not path.exists():
        return None
    ids = {identifier for identifier in FOUNDATION_ROW.findall(path.read_text())
           if identifier != "ID"}
    return len(ids)


def interfaces() -> list[dict[str, Any]]:
    """Every theorem-facing interface, one file each.

    A list rather than the single `theorem_interface.json` this once wrapped: the
    repository grew a second theorem-facing interface while the schema had room
    for one, and the alternatives were editing this file per interface or
    overloading one object's identifier with an unrelated one.
    """
    return [json.loads(path.read_text())
            for path in sorted(STATE.glob("theorem_interface*.json"))]


def current_state() -> dict[str, Any]:
    project_data = load_json("projects.json")["projects"]
    round_data = load_json("rounds.json")["rounds"]
    vocabulary = load_json("vocabulary.json")["terms"]
    foundations = load_json("foundations.json")["foundations"]
    for foundation in foundations:
        inventory = foundation["claim_inventory"]
        foundation["claim_count"] = foundation_claim_count(ROOT / inventory["source"])
    registries = sorted(ROOT.glob("projects/*/CLAIMS.md"))
    claims = []
    for path in registries:
        for claim in registry.parse(path):
            claim["registry"] = path.relative_to(ROOT).as_posix()
            claims.append(claim)
    state = {
        "projects": project_data,
        "claims": claims,
        "foundations": foundations,
        "rounds": round_data,
        "vocabulary": vocabulary,
        "priorities": priorities(),
        "interfaces": interfaces(),
    }
    state["rests_on"] = rests_on(round_data)
    state["counts"] = derived_counts(state)
    return state


def rests_on(rounds: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Per round, the `ci-only` rounds it transitively takes as hypotheses.

    Derived from `depends_on`, which records consumption rather than citation.
    Every round here is `ci-only` — that is this repository's designed default —
    so the set is the transitive closure of `depends_on` and the count is its
    size. **This measures the debt and pays none of it.** A round resting on
    twenty unreviewed rounds is not thereby wrong; it is a round whose
    hypotheses nobody has read, which is a fact the emission should be able to
    state.

    Emitted and bound to nothing, per the wiki-bindings decision that a derived
    quantity is seeded by demand. A cycle would not terminate, so `validate`
    refuses one before this runs.
    """
    edges = {r["id"]: list(r.get("depends_on", [])) for r in rounds}
    view = []
    for round_ in rounds:
        seen: set[str] = set()
        frontier = list(edges.get(round_["id"], []))
        while frontier:
            current = frontier.pop()
            if current in seen or current not in edges:
                continue
            seen.add(current)
            frontier.extend(edges[current])
        view.append({"round": round_["id"], "ci_only_rounds": sorted(seen),
                     "count": len(seen)})
    return view


def derived_counts(state: dict[str, Any]) -> dict[str, Any]:
    """Aggregates, so a wiki page can bind one by a plain dotted path.

    The sections above are flat lists, and an aggregate over a list is not
    addressable by a path. Deriving it here rather than in the grammar keeps one
    adjudicator: `checkers/wiki_state_bindings.py` compares strings and computes
    nothing.

    **Seeded by demand.** A key exists here because a page in `wiki/` binds it;
    a count nothing binds is a number with no reader and one more thing to keep
    true. Each key states its derivation.
    """
    return {
        # Every claim in every inherited foundation claim source, counted from
        # each source's own ledger. One source today; a second changes this
        # total, and the binding that reads it fails rather than drifts.
        "foundation_claims": sum(f["claim_count"] for f in state["foundations"]),
        # Active entries in the modern registries, whatever their class. A wiki
        # page saying how much of a line is registered binds one of these rather
        # than counting rows itself, which would make the page a second judge.
        # Per project as well as in total, because a line's own page speaks about
        # its own line and the total moved under it when a second line got a
        # registry.
        "registered_claims": sum(1 for c in state["claims"]
                                 if c.get("status") == "active"),
        "registered_claims_by_project": {
            project["id"]: sum(1 for c in state["claims"]
                               if c.get("status") == "active"
                               and c.get("project") == project["id"])
            for project in state["projects"] if project["status"] == "active"
        },
    }


def duplicates(values: list[str]) -> set[str]:
    return {value for value in values if values.count(value) > 1}


def dependency_cycles(rounds: list[dict[str, Any]]) -> list[str]:
    """`depends_on` is consumption, so a cycle is a round resting on itself.

    Checked before `rests_on` walks the graph, which would otherwise not
    terminate. Unresolvable ids are reported per round elsewhere; here they are
    simply not followed.
    """
    edges = {r["id"]: [c for c in r.get("depends_on", []) if c != r["id"]]
             for r in rounds}
    colour: dict[str, int] = {}
    found: list[str] = []

    def walk(node: str, path: list[str]) -> None:
        colour[node] = 1
        for nxt in edges.get(node, []):
            if nxt not in edges:
                continue
            if colour.get(nxt) == 1:
                found.append("depends_on cycle: "
                             + " -> ".join(path[path.index(nxt):] + [nxt]))
            elif colour.get(nxt, 0) == 0:
                walk(nxt, path + [nxt])
        colour[node] = 2

    for identifier in edges:
        if colour.get(identifier, 0) == 0:
            walk(identifier, [identifier])
    return found


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
                       ("priority", data["priorities"]),
                       ("foundation", data["foundations"])):
        repeated = duplicates([str(row["id"]) for row in rows])
        if repeated:
            problems.append(f"duplicate {kind} id(s): {sorted(repeated)}")

    # One registry per line, and each at its own project's path. The earlier form
    # required exactly one, which was a fact about the workspace rather than a
    # rule about it: the normativity line had a registry and the deference line
    # did not. What has to hold is that a registry belongs to an active project
    # and that at least one exists, so an empty glob cannot read as clean.
    registries = sorted(ROOT.glob("projects/*/CLAIMS.md"))
    if not registries:
        problems.append("no claims registry found under projects/*/CLAIMS.md; "
                        "an empty match is a broken glob, not a workspace with "
                        "nothing registered")
    for registry_path in registries:
        owner = registry_path.parent.name
        if owner not in projects or projects[owner]["status"] != "active":
            problems.append(f"registry {registry_path.relative_to(ROOT).as_posix()}: "
                            f"owner is not an active project: {owner}")

    if not data["interfaces"]:
        problems.append("no theorem-facing interface found; the emitter globs "
                        "state/theorem_interface*.json and an empty match is a "
                        "missing file, not a workspace with no interfaces")

    problems.extend(dependency_cycles(data["rounds"]))

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
        artifact_path = round_.get("artifact_path")
        if artifact_path is not None and not (ROOT / artifact_path).exists():
            problems.append(f"round {round_['id']}: artifact path does not exist: {artifact_path}")
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
        for item in round_.get("verdicts", []):
            source_path = item.get("source")
            if not source_path or not (ROOT / source_path).exists():
                problems.append(f"round {round_['id']}: verdict source does not exist: "
                                f"{source_path}")
            else:
                source = " ".join((ROOT / source_path).read_text().replace("`", "").split())
                if " ".join(item["value"].split()) not in source:
                    problems.append(f"round {round_['id']}: verdict is not verbatim in "
                                    f"{source_path}: {item['value']!r}")
        if "depends_on" not in round_:
            problems.append(f"round {round_['id']}: no depends_on field; an empty "
                            "list is the statement that it consumes nothing")
        # Where a report says nothing and the dispatch does, the dispatch is
        # still part of the round's record — and the two are worth telling
        # apart, because a dispatch says what a round was told to build on and a
        # report says what it did. `prompt` marks the weaker reading.
        source = round_.get("depends_on_source")
        if source is not None and source not in ("report", "prompt"):
            problems.append(f"round {round_['id']}: depends_on_source must be "
                            f"'report' or 'prompt', not {source!r}")
        if source is not None and not round_.get("depends_on"):
            problems.append(f"round {round_['id']}: depends_on_source is set but "
                            "depends_on is empty; there is no reading to source")
        for consumed in round_.get("depends_on", []):
            if consumed == round_["id"]:
                problems.append(f"round {round_['id']}: depends_on is self-referential")
            elif consumed not in rounds:
                problems.append(f"round {round_['id']}: depends_on does not resolve: "
                                f"{consumed}")
        superseded_by = round_.get("superseded_by")
        if superseded_by is not None:
            if superseded_by == round_["id"]:
                problems.append(f"round {round_['id']}: superseded_by is self-referential")
            elif superseded_by not in rounds:
                problems.append(f"round {round_['id']}: superseded_by does not resolve: "
                                f"{superseded_by}")
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
        if not item.get("metadata_present"):
            problems.append(f"priority {item['id']}: missing workspace-priority metadata")
        project = item.get("project")
        if project is not None and (project not in projects or
                                    projects[project]["status"] != "active"):
            problems.append(f"priority {item['id']}: project is not active: {project}")

    for foundation in data["foundations"]:
        project = foundation.get("project")
        if project not in projects or projects[project]["status"] != "active":
            problems.append(f"foundation {foundation['id']}: project is not active: {project}")
        if foundation.get("modern_registry") is not False:
            problems.append(f"foundation {foundation['id']}: must be distinct from modern registry")
        paths = (
            ("path", foundation.get("path")),
            ("ledger", foundation.get("authority", {}).get("ledger")),
            ("status vocabulary", foundation.get("authority", {}).get("status_vocabulary")),
            ("verifier", foundation.get("verification", {}).get("verifier")),
            ("claim inventory", foundation.get("claim_inventory", {}).get("source")),
        )
        for label, path in paths:
            if not path or not (ROOT / path).exists():
                problems.append(f"foundation {foundation['id']}: {label} does not exist: {path}")
        expected = foundation.get("claim_inventory", {}).get("expected_count")
        actual = foundation.get("claim_count")
        if actual is not None and actual != expected:
            problems.append(f"foundation {foundation['id']}: claim inventory count "
                            f"{actual} != expected {expected}")

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
        research_round = interface.get("research_round")
        if research_round and research_round not in rounds:
            problems.append(f"interface {interface['interface_id']}: unknown research round "
                            f"{research_round}")
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
            for field in ("statement_of_record", "research_artifact"):
                path = obj.get(field)
                if path is not None and not (ROOT / path).exists():
                    problems.append(f"interface {obj['id']}: {field} does not exist: {path}")

    for path, expected in render_handoffs(data).items():
        target = ROOT / path
        if not target.exists():
            problems.append(f"generated handoff view is missing: {path}")
        elif target.read_text() != expected:
            problems.append(f"generated handoff view is stale: {path}")

    return problems


def render_handoffs(data: dict[str, Any]) -> dict[str, str]:
    # Generated views of live state. They live beside the state they render
    # from, not inside a round's directory: a round record is history and is not
    # edited, so a view kept there made every round that indexed itself edit an
    # older round's folder to stay green.
    base = "state/views"
    command = "python3 -m checkers.workspace_state --write-handoff"

    paths = ["# Final path map", "", f"Generated from `state/projects.json` by `{command}`.", "",
             "| stable ID | display name | status | parent | path | entry points |",
             "|---|---|---|---|---|---|"]
    for project in data["projects"]:
        paths.append("| {id} | {name} | {status} | {parent} | {path} | {entries} |".format(
            id=project["id"], name=project["name"], status=project["status"],
            parent=project.get("parent") or "—", path=project.get("path") or "—",
            entries="<br>".join(f"`{entry}`" for entry in project.get("entry_points", [])) or "—"))

    paths.extend(["", "## Foundation claim sources", "",
                  "| stable ID | project | kind | path | ledger | verifier | claims | modern registry |",
                  "|---|---|---|---|---|---|---|---|"])
    for foundation in data["foundations"]:
        paths.append("| {id} | {project} | {kind} | `{path}` | `{ledger}` | `{verifier}` | {count} | {modern} |".format(
            id=foundation["id"], project=foundation["project"], kind=foundation["kind"],
            path=foundation["path"], ledger=foundation["authority"]["ledger"],
            verifier=foundation["verification"]["verifier"],
            count=foundation["claim_count"], modern=str(foundation["modern_registry"]).lower()))

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
        verdicts = [round_["verdict"]] if round_.get("verdict") else []
        verdicts.extend(item["value"] for item in round_.get("verdicts", []))
        rounds.append("| {id} | {date} | {project} | `{path}` | {verdict} | {classes} | `{prompt}` | {claims} |".format(
            id=round_["id"], date=round_["date"], project=round_.get("project") or "workspace",
            path=round_["path"], verdict="<br>".join(verdicts) or "—",
            classes=", ".join(round_.get("registered_classes", [])) or "—",
            prompt=round_.get("prompt") or "—",
            claims=", ".join(round_.get("claim_changes", [])) or "—"))

    return {
        f"{base}/FINAL_PATH_MAP.md": "\n".join(paths) + "\n",
        f"{base}/VOCABULARY_SHEET.md": "\n".join(vocabulary) + "\n",
        f"{base}/VERDICT_STATUS_INVENTORY.md": "\n".join(rounds) + "\n",
    }


def self_test() -> bool:
    cases: list[tuple[str, bool]] = []

    data = current_state()
    data["projects"][0]["entry_points"].append("missing/stale-path.md")
    cases.append(("stale registered path fails loudly",
                  any("missing/stale-path.md" in p for p in validate(data))))

    data = current_state()
    data["projects"].append(dict(data["projects"][0]))
    cases.append(("duplicate stable ID fails loudly",
                  any("duplicate project id" in p for p in validate(data))))

    data = current_state()
    data["foundations"][0]["authority"]["ledger"] = "missing/foundation-ledger.md"
    cases.append(("missing foundation source fails loudly",
                  any("foundation-ledger.md" in p for p in validate(data))))

    data = current_state()
    data["foundations"][0]["claim_inventory"]["expected_count"] += 1
    cases.append(("incorrect foundation count fails loudly",
                  any("claim inventory count" in p for p in validate(data))))

    fixture = ("### 947. Future item — **[open]**\n"
               "<!-- workspace-priority: project=normativity; dispatchable=yes -->\n")
    parsed = parse_priorities(fixture)
    cases.append(("arbitrary future priority uses explicit metadata",
                  len(parsed) == 1 and parsed[0]["id"] == "947" and
                  parsed[0]["project"] == "normativity" and
                  parsed[0]["specified_enough_to_dispatch"] is True))

    data = current_state()
    data["projects"][0]["path"] = "projects/leverage"
    cases.append(("live projects/leverage current-state path fails loudly",
                  any("active path does not exist" in p for p in validate(data))))

    # `depends_on`, and the null inputs for it. The dangerous direction is a
    # dependency that silently does not resolve: `rests_on` would then report a
    # smaller debt than the round actually carries, which is the one error the
    # view exists to prevent.
    data = current_state()
    data["rounds"][-1]["depends_on"] = ["2026-08-11-no-such-round"]
    cases.append(("an unresolvable depends_on id fails loudly",
                  any("depends_on does not resolve" in p for p in validate(data))))

    data = current_state()
    data["rounds"][-1]["depends_on"] = [data["rounds"][-1]["id"]]
    cases.append(("a self-referential depends_on fails loudly",
                  any("depends_on is self-referential" in p for p in validate(data))))

    data = current_state()
    first, second = data["rounds"][0], data["rounds"][1]
    first["depends_on"] = [second["id"]]
    second["depends_on"] = [first["id"]]
    cases.append(("a depends_on cycle fails loudly",
                  any("depends_on cycle" in p for p in validate(data))))

    data = current_state()
    del data["rounds"][-1]["depends_on"]
    cases.append(("a round record with no depends_on fails loudly",
                  any("no depends_on field" in p for p in validate(data))))

    data = current_state()
    data["rounds"][-1]["depends_on_source"] = "guessed"
    cases.append(("an unknown depends_on_source fails loudly",
                  any("depends_on_source must be" in p for p in validate(data))))

    data = current_state()
    data["rounds"][-1]["depends_on_source"] = "prompt"
    data["rounds"][-1]["depends_on"] = []
    cases.append(("a depends_on_source with nothing to source fails loudly",
                  any("there is no reading to source" in p for p in validate(data))))

    data = current_state()
    for round_ in data["rounds"]:
        if round_.get("depends_on"):
            round_["depends_on_source"] = "prompt"
            break
    cases.append(("a sourced dependency list is accepted",
                  not any("depends_on_source" in p for p in validate(data))))

    data = current_state()
    data["interfaces"] = []
    cases.append(("no theorem-facing interface fails loudly",
                  any("no theorem-facing interface" in p for p in validate(data))))

    chain = [{"id": "a", "depends_on": ["b"]}, {"id": "b", "depends_on": ["c"]},
             {"id": "c", "depends_on": []}]
    derived = {row["round"]: row for row in rests_on(chain)}
    cases.append(("rests_on is transitive and counts what it lists",
                  derived["a"]["ci_only_rounds"] == ["b", "c"] and
                  derived["a"]["count"] == 2 and derived["c"]["count"] == 0))

    emitted = current_state()["rests_on"]
    cases.append(("rests_on emits one row per round",
                  len(emitted) == len(emitted and current_state()["rounds"]) and
                  {row["round"] for row in emitted} ==
                  {r["id"] for r in current_state()["rounds"]}))

    protection = json.loads((ROOT / ".github/branch-protection.json").read_text())
    contexts_before = protection["required_status_checks"]["contexts"]
    data = current_state()
    data["projects"][0]["name"] = "Renamed Display Only"
    contexts_after = protection["required_status_checks"]["contexts"]
    cases.append(("project display rename leaves branch-protection identity stable",
                  contexts_before == contexts_after and
                  "consolidation-verification" in contexts_after))

    passed = all(result for _, result in cases)
    print("WORKSPACE STATE SELF-TEST:")
    for label, result in cases:
        print(f"  {'ok' if result else 'FAILED'}: {label}")
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
          f"{len(data['claims'])} modern claims, {len(data['foundations'])} foundations, "
          f"{sum(f['claim_count'] or 0 for f in data['foundations'])} foundation claims, "
          f"{len(data['rounds'])} rounds, "
          f"{len(data['vocabulary'])} terms, {len(data['priorities'])} priorities, "
          f"{sum(len(i['objects']) for i in data['interfaces'])} interface objects")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
