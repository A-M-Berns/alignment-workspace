"""`PRIORITIES.md` is a render of the map's item nodes (ruling M6 of 2026-10-22).

Usage:
    python3 -m checkers.priorities_render --check      # the committed file equals the render (the gate)
    python3 -m checkers.priorities_render --write      # write the render (what the plain checker run does)
    python3 -m checkers.priorities_render --self-test  # the null inputs and a round trip

The source of the file is two things. `state/priorities_sections.md` holds the standing preamble and, under each
`## <section>` heading, that section's intro text, in the file's order. Each item is a node under `graph/nodes/`
carrying `item` (its number, or `Q<n>` / `F<n>`), `title`, `section`, `maintainer_order` (the hand ordering,
transcribed), `difficulty` (the bold bracket of the heading, absent on an ingenuity or friction entry),
`heading_notes` (the heading's trailing annotations, verbatim), `project` and `dispatchable` (the
`workspace-priority` marker's values), and a `## Item` section with the entry's body verbatim. The render is:
the preamble; for each section, its heading, its intro and its items in `maintainer_order`, each as the heading
line rebuilt from the fields, the marker line rebuilt from the fields, one line naming the formal results that answer the
item (ruling F2, 2026-10-23: every formal result built from a registry entry points at the item its `answers_item` names,
and the render inverts the pointer; absent when nothing answers the item), a blank line, and the body.

This module reads node files with the checker's own parser and validates only what the render needs: every item
node carries the fields, item ids are unique, every `section` names a section of the sections file, and no body
holds a line that would read as a heading. `checkers.graph` lints the rest. A render over no item nodes, or over a
sections file with no section, is refused rather than written: the null input would be an empty priorities file
reported as a clean render.
"""
from __future__ import annotations

import pathlib
import re
import sys

from checkers import graph as g

ROOT = pathlib.Path(__file__).resolve().parents[1]
SECTION = re.compile(r"^## (.+)$", re.M)


class RenderError(Exception):
    pass


def item_nodes(root: pathlib.Path) -> list[dict]:
    nodes = []
    for p in sorted((root / "graph" / "nodes").glob("*.md")):
        text = p.read_text()
        if "\nitem:" not in text.split("\n---", 1)[0]:
            continue
        n = g.parse_node_text(text, str(p.relative_to(root)))
        if n.get("item") in (None, ""):
            continue
        sec = {}
        name = None
        for line in text.split("\n---", 1)[1].splitlines()[1:]:
            m = re.match(r"^## (\S.*)$", line)
            if m:
                name = m.group(1).strip()
                sec[name] = []
            elif name is not None:
                sec[name].append(line)
        n["_item_body"] = "\n".join(sec.get("Item", [])).strip("\n")
        nodes.append(n)
    return nodes


def answers(root: pathlib.Path) -> dict[str, list[str]]:
    """{item: [formal results answering it]}: every `and` with a record child and a `priorities` pointer (ruling F2). A result
    whose record carries a registry id other than the node's id prints both, `node (registry id)`."""
    nodes = {}
    for p in sorted((root / "graph" / "nodes").glob("*.md")):
        nodes[p.stem] = g.parse_node_text(p.read_text(), str(p.relative_to(root)))
    out: dict[str, list[str]] = {}
    for x, n in nodes.items():
        if n.get("kind") != "and" or n.get("superseded_by"):
            continue
        recs = [c for c in n.get("children") or [] if nodes.get(c, {}).get("leaf_kind") == "record"]
        if not recs:
            continue
        rid = nodes[recs[0]].get("registry_id")
        label = f"{x} ({rid})" if rid and rid != x else x
        for w in n.get("work") or []:
            if isinstance(w, dict) and w.get("kind") == "priorities":
                out.setdefault(str(w.get("ref")), []).append(label)
    return {k: sorted(v) for k, v in out.items()}


def answers_line(ids: list[str]) -> str:
    return "*Registered answers in the map:* " + ", ".join(ids) + "."


def sections(root: pathlib.Path) -> tuple[str, list[tuple[str, str]]]:
    text = (root / "state" / "priorities_sections.md").read_text()
    ms = list(SECTION.finditer(text))
    if not ms:
        raise RenderError("state/priorities_sections.md names no `## ` section")
    pre = text[:ms[0].start()]
    out = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        out.append((m.group(1).strip(), text[m.end():end]))
    return pre, out


def heading(n: dict) -> str:
    key = str(n["item"])
    lead = f"### {key}. " if key.isdigit() else f"### {key} — "
    head = lead + str(n["title"])
    if n.get("difficulty") not in (None, ""):
        head += f" — **[{n['difficulty']}]**"
    head += str(n.get("heading_notes") or "")
    return head


def marker(n: dict) -> str:
    project = n.get("project")
    project = "none" if project in (None, "", "null") else str(project)
    return f"<!-- workspace-priority: project={project}; dispatchable={'yes' if n.get('dispatchable') is True else 'no'} -->"


def render(root: pathlib.Path) -> str:
    nodes = item_nodes(root)
    if not nodes:
        raise RenderError("no item node under graph/nodes (a node carrying `item`); the render would be an empty file")
    pre, secs = sections(root)
    names = [s for s, _ in secs]
    seen = {}
    for n in nodes:
        for f in ("item", "title", "section", "maintainer_order"):
            if n.get(f) in (None, ""):
                raise RenderError(f"{n['_path']}: item node lacks {f}")
        if n["item"] in seen:
            raise RenderError(f"{n['_path']}: item {n['item']} is also {seen[n['item']]}")
        seen[n["item"]] = n["_path"]
        if n["section"] not in names:
            raise RenderError(f"{n['_path']}: section {n['section']!r} is not a section of state/priorities_sections.md")
        if not isinstance(n["maintainer_order"], int):
            raise RenderError(f"{n['_path']}: maintainer_order is an integer")
        if re.search(r"^#{1,3} ", n["_item_body"], re.M):
            raise RenderError(f"{n['_path']}: the Item section holds a heading line")
    by_section = {s: sorted((n for n in nodes if n["section"] == s), key=lambda n: (n["maintainer_order"], str(n["item"])))
                  for s in names}
    orders = sorted(n["maintainer_order"] for n in nodes)
    if len(set(orders)) != len(orders):
        raise RenderError("two item nodes share a maintainer_order")
    ans = answers(root)
    out = [pre.rstrip("\n"), ""]
    for s, intro in secs:
        out += [f"## {s}", intro.strip("\n"), ""]
        for n in by_section[s]:
            out += [heading(n), marker(n)] + ([answers_line(ans[str(n["item"])])] if ans.get(str(n["item"])) else []) + ["", n["_item_body"], ""]
    text = "\n".join(out)
    return re.sub(r"\n{3,}", "\n\n", text).rstrip("\n") + "\n"


def check(root: pathlib.Path) -> tuple[bool, str]:
    try:
        want = render(root)
    except RenderError as e:
        return False, f"render refused: {e}"
    have = (root / "PRIORITIES.md").read_text()
    if have != want:
        import difflib
        d = list(difflib.unified_diff(have.splitlines(), want.splitlines(), "PRIORITIES.md", "render", lineterm="", n=1))
        return False, "PRIORITIES.md differs from the render of the item nodes (edit the item nodes or the sections file, then run the checker):\n" + "\n".join(d[:40])
    return True, f"PRIORITIES RENDER: the committed file equals the render ({len(item_nodes(root))} items)"


def self_test() -> int:
    import shutil
    import tempfile
    tmp = pathlib.Path(tempfile.mkdtemp())
    cases = []
    try:
        # the live tree renders and matches
        ok, msg = check(ROOT)
        cases.append(("the committed PRIORITIES.md equals the render", ok, True))
        # null input 1: no item node
        empty = tmp / "empty"
        (empty / "graph" / "nodes").mkdir(parents=True)
        (empty / "state").mkdir()
        (empty / "state" / "priorities_sections.md").write_text("# P\n\n## S\nintro\n")
        (empty / "PRIORITIES.md").write_text("")
        cases.append(("no item node is refused", check(empty)[0], False))
        # null input 2: a sections file without a section
        one = tmp / "one"
        shutil.copytree(ROOT / "graph" / "nodes", one / "graph" / "nodes", ignore=lambda d, fs: [f for f in fs if not f.startswith("item-")])
        (one / "state").mkdir(parents=True)
        (one / "state" / "priorities_sections.md").write_text("# P\n")
        (one / "PRIORITIES.md").write_text("")
        cases.append(("a sections file with no section is refused", check(one)[0], False))
        # a hand edit of the committed file is caught
        edited = tmp / "edited"
        shutil.copytree(ROOT / "graph" / "nodes", edited / "graph" / "nodes", ignore=lambda d, fs: [f for f in fs if not f.startswith("item-")])
        (edited / "state").mkdir(parents=True)
        shutil.copy(ROOT / "state" / "priorities_sections.md", edited / "state" / "priorities_sections.md")
        (edited / "PRIORITIES.md").write_text(render(edited) + "\nan extra line\n")
        cases.append(("a hand edit of PRIORITIES.md is caught", check(edited)[0], False))
        # a duplicate item number is refused
        dup = tmp / "dup"
        shutil.copytree(edited, dup)
        first = sorted((dup / "graph" / "nodes").glob("item-*.md"))[0]
        (dup / "graph" / "nodes" / "item-dup.md").write_text(first.read_text().replace(f"id: {first.stem}", "id: item-dup"))
        cases.append(("a duplicate item number is refused", check(dup)[0], False))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    failures = 0
    print("PRIORITIES RENDER SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    if "--write" in argv:
        (ROOT / "PRIORITIES.md").write_text(render(ROOT))
        print("PRIORITIES.md written")
        return 0
    ok, msg = check(ROOT)
    print(msg if ok else "PRIORITIES RENDER FAILED: " + msg, file=sys.stdout if ok else sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
