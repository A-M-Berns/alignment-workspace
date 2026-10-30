"""A wiki page that names a registered claim, a priority item, a round or a map node carries a reference the build resolves.

The sibling of `checkers/wiki_state_bindings.py` (2026-10-22): that checker binds a *quantity* to the state emission; this one
binds a *name*. A page writes, invisibly in the rendered wiki, one of

    <!--ref:claim:inductor.conformance-->      a registered claim, by its registry id; it must be an active entry
    <!--ref:item:39-->                          a priority item, by its number (or Q1, F3); it must exist
    <!--ref:item-open:39-->                     a priority item the page says is open; it must exist and be open
    <!--ref:round:2026-10-20-warrant-enforcement-semantics-->   a round, by its id in state/rounds.json
    <!--ref:node:corrigibility-landscape-->     a node of the argument map, by its id

and this compares each against the repository today: a renamed or superseded claim, a closed item the page calls open, a round
not in the index or a node that is gone fails the build rather than going stale. Detection is inverted, as in the bindings
checker: nothing here reads free prose to guess what is a name; the author declares the reference beside the mention. Code
spans and fenced blocks are skipped, so a page can quote the grammar.

Null inputs: a wiki with no pages, a repository with no registry or no item nodes, or a wiki that declares no reference at all
each fail rather than report a clean run over nothing.
"""
from __future__ import annotations

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
WIKI = ROOT / "wiki"
REF = re.compile(r"<!--ref:(claim|item|item-open|round|node):([^<>\s]+)-->")
LOOSE = re.compile(r"<!--\s*ref\b[^>]*-->", re.I)
CODE_SPAN = re.compile(r"`[^`\n]*`")
FENCE = re.compile(r"^\s*```")


def blank(text: str) -> str:
    kept, in_fence = [], False
    for raw in text.split("\n"):
        if FENCE.match(raw):
            in_fence = not in_fence
            kept.append(" " * len(raw))
            continue
        kept.append(" " * len(raw) if in_fence else CODE_SPAN.sub(lambda m: " " * len(m.group(0)), raw))
    return "\n".join(kept)


def targets(root: pathlib.Path) -> dict:
    """What a reference may resolve to: active claims, items with their status, rounds, nodes."""
    sys.path.insert(0, str(root))
    from checkers import registry
    claims = {}
    for path in sorted(root.glob("projects/*/CLAIMS.md")):
        for e in registry.parse(path):
            claims[e["id"]] = e.get("status")
    items = {}
    for p in (root / "graph" / "nodes").glob("item-*.md"):
        fm = p.read_text().split("\n---", 1)[0]
        m = re.search(r'^item: "([^"]+)"', fm, re.M)
        st = re.search(r"^item_status: (\w+)", fm, re.M)
        if m:
            items[m.group(1)] = st.group(1) if st else "open"
    rounds = set()
    rpath = root / "state" / "rounds.json"
    if rpath.is_file():
        rounds = {r["id"] for r in json.loads(rpath.read_text()).get("rounds") or []}
    nodes = {p.stem for p in (root / "graph" / "nodes").glob("*.md")}
    return {"claims": claims, "items": items, "rounds": rounds, "nodes": nodes}


def problems(pages: dict[str, str], T: dict) -> list[str]:
    found = []
    for name in sorted(pages):
        text = blank(pages[name])
        strict = {m.group(0) for m in REF.finditer(text)}
        for m in LOOSE.finditer(text):
            if m.group(0) not in strict:
                found.append(f"{name}:line {text.count(chr(10), 0, m.start()) + 1}: malformed reference {m.group(0)!r}")
        for m in REF.finditer(text):
            kind, ref = m.group(1), m.group(2)
            where = f"{name}:line {text.count(chr(10), 0, m.start()) + 1}"
            if kind == "claim":
                if ref not in T["claims"]:
                    found.append(f"{where}: claim {ref!r} is in no registry (renamed or removed)")
                elif T["claims"][ref] != "active":
                    found.append(f"{where}: claim {ref!r} is {T['claims'][ref]}, not active")
            elif kind in ("item", "item-open"):
                if ref not in T["items"]:
                    found.append(f"{where}: item {ref!r} has no item node")
                elif kind == "item-open" and T["items"][ref] != "open":
                    found.append(f"{where}: item {ref!r} is {T['items'][ref]}, and the page says it is open")
            elif kind == "round":
                if ref not in T["rounds"]:
                    found.append(f"{where}: round {ref!r} is not in state/rounds.json")
            elif kind == "node":
                if ref not in T["nodes"]:
                    found.append(f"{where}: node {ref!r} is no node of the map")
    return found


def count_refs(pages: dict[str, str]) -> int:
    return sum(len(REF.findall(blank(t))) for t in pages.values())


def live_pages() -> dict[str, str]:
    return {p.name: p.read_text() for p in sorted(WIKI.glob("*.md"))}


def run(pages: dict[str, str], T: dict, quiet: bool = False) -> int:
    def say(msg):
        if not quiet:
            print(msg, file=sys.stderr)
    if not pages:
        say("WIKI REFS FAILED: no pages under wiki/")
        return 1
    if not T["claims"] or not T["items"]:
        say("WIKI REFS FAILED: no registry entries or no item nodes to resolve against; the targets would be empty")
        return 1
    if not count_refs(pages):
        say("WIKI REFS FAILED: no page declares a reference; a wiki that names no claim, item, round or node is worth saying deliberately")
        return 1
    found = problems(pages, T)
    if found:
        say("WIKI REFS FAILED:")
        for f in found:
            say(f"  - {f}")
        say("\n  A reference names a registered claim, an item node, a round of state/rounds.json or a node of the map, as it is today; "
            "rename the reference with the object, or wrap a statement about the past in <!--historical-->…<!--/historical-->.")
        return 1
    if not quiet:
        print(f"WIKI REFS: clean over {len(pages)} page(s); {count_refs(pages)} reference(s) resolve")
    return 0


def self_test() -> int:
    T = {"claims": {"a.b": "active", "a.old": "superseded"}, "items": {"7": "open", "8": "closed"}, "rounds": {"2026-01-01-x"}, "nodes": {"n1"}}

    def over(body):
        return len(problems({"P.md": body}, T))
    cases = [
        ("a resolving claim passes", over("x <!--ref:claim:a.b--> y\n"), 0),
        ("a renamed claim is caught", over("<!--ref:claim:a.gone-->\n"), 1),
        ("a superseded claim is caught", over("<!--ref:claim:a.old-->\n"), 1),
        ("an item passes", over("<!--ref:item:7--> and <!--ref:item:8-->\n"), 0),
        ("a missing item is caught", over("<!--ref:item:9-->\n"), 1),
        ("a closed item called open is caught", over("<!--ref:item-open:8-->\n"), 1),
        ("an open item called open passes", over("<!--ref:item-open:7-->\n"), 0),
        ("a round passes and a missing one is caught", over("<!--ref:round:2026-01-01-x--> <!--ref:round:nope-->\n"), 1),
        ("a node passes and a missing one is caught", over("<!--ref:node:n1--> <!--ref:node:n2-->\n"), 1),
        ("a malformed reference is caught", over("<!--ref:claim a.b-->\n"), 1),
        ("a fenced block is not read", over("```\n<!--ref:claim:a.gone-->\n```\n"), 0),
        ("a code span is not read", over("say `<!--ref:item:9-->` to bind\n"), 0),
        ("no pages is refused", run({}, T, quiet=True), 1),
        ("empty targets are refused", run({"P.md": "<!--ref:item:7-->"}, {"claims": {}, "items": {}, "rounds": set(), "nodes": set()}, quiet=True), 1),
        ("a wiki with no reference is refused", run({"P.md": "prose\n"}, T, quiet=True), 1),
        ("the live wiki declares at least one reference", count_refs(live_pages()) > 0, True),
        ("the live targets are non-empty", bool(targets(ROOT)["claims"]) and bool(targets(ROOT)["items"]), True),
    ]
    failures = 0
    print("WIKI REFS SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    return run(live_pages(), targets(ROOT))


if __name__ == "__main__":
    sys.exit(main())
