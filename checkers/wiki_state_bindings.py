"""A volatile quantity on a wiki page is declared and checked, or it is not there.

A number that moves when work lands is wrong on a date nobody notices, and the
human register is the surface least likely to be re-read when it moves. Nothing
here tries to decide which sentences are volatile: **detection is inverted.**
The author declares a quantity by binding it to machine state, and this compares
the declared string against what the state says today. Free prose is not
classified, and a checker that tried to would be guessing about English.

A declaration is invisible in the rendered wiki, because it is written in HTML
comments:

    <!--state:workspace:counts.foundation_claims-->180<!--/state-->
    <!--historical-->PR #31 registered no workspace claim<!--/historical-->

`FILE` names a state emission — `workspace` is `checkers/workspace_state.py
--json`, the repository's one adjudicator — and the rest is a dotted path into
it. Path segments index mappings, or lists by integer position. **Nothing is
derived here**: an aggregate a page wants to bind is a key the emitter grows,
which is why `counts` exists there and no `.length` suffix exists in this
grammar. Run this with `--sections` for the paths the live emission offers.

`historical` marks a statement about a past event, which cannot rot. Its span is
exempt from the denylist and nothing inside it is verified — so it is also the
way to say something this file has no other way to accept, and it is deliberately
awkward to overuse: three lines maximum, because it marks statements rather than
sections.

The denylist is the backstop for the forms most likely to be written without
thinking, and it is exactly four. Each earns its place; **growing this list is a
maintainer act**, not something a round does because a pattern looked risky:

- `PR #<n>` — a pull-request number dates a page to the week it was written, and
  the number keeps resolving after the claim about it stops being true.
- `<n> claims`, optionally qualified `registered`/`modern`/`legacy` — the count
  the registry exists to hold, and the one most often copied into prose.
- `<n> rounds` — a tally that changes every time a round lands.
- `<n> priorities` / `<n> priority` — the same, for the ledger that is edited
  most often.

A hit is not an error about the sentence; it is a request to say where the
number comes from. Bind it, or mark it historical.

Fenced blocks and inline code spans are skipped in every pass, so a page can
document this grammar without the examples being read as declarations.
"""
from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
WIKI = ROOT / "wiki"

HISTORICAL_MAX_LINES = 3

TOKEN = re.compile(
    r"<!--state:([^:<>]*):([^<>]*?)-->|<!--/state-->|<!--historical-->|<!--/historical-->")
LOOSE = re.compile(r"<!--\s*/?\s*(?:state|historical)\b[^>]*-->", re.I)
CODE_SPAN = re.compile(r"`[^`\n]*`")
FENCE = re.compile(r"^\s*```")

DENYLIST = (
    ("a pull-request number", re.compile(r"PR #\d+")),
    ("a claim count", re.compile(r"\d+\s*(?:registered|modern|legacy)?\s*claims")),
    ("a round tally", re.compile(r"\d+\s*rounds")),
    ("a priority tally", re.compile(r"\d+\s*priorit(?:y|ies)")),
)


def emission() -> dict:
    """The one adjudicator's output. Re-deriving it from `state/*.json` here
    would make a second judge of what the workspace currently holds."""
    out = subprocess.run([sys.executable, "-m", "checkers.workspace_state", "--json"],
                         cwd=ROOT, capture_output=True, text=True, check=True)
    return json.loads(out.stdout)


def sources() -> dict[str, dict]:
    return {"workspace": emission()}


def blank(text: str) -> str:
    """Code spans and fenced blocks, replaced by spaces. Offsets and line
    numbers survive, so every later pass reports where it looked."""
    kept: list[str] = []
    in_fence = False
    for raw in text.split("\n"):
        if FENCE.match(raw):
            in_fence = not in_fence
            kept.append(" " * len(raw))
            continue
        kept.append(" " * len(raw) if in_fence else CODE_SPAN.sub(
            lambda m: " " * len(m.group(0)), raw))
    return "\n".join(kept)


def line_of(text: str, position: int) -> int:
    return text.count("\n", 0, position) + 1


def spans(text: str) -> tuple[list[dict], list[str]]:
    """Marker spans in document order, and everything malformed or unpaired."""
    found: list[dict] = []
    problems: list[str] = []
    open_token: tuple[str, re.Match] | None = None

    for match in TOKEN.finditer(text):
        raw = match.group(0)
        if raw.startswith("<!--state:"):
            kind, opening = "state", True
        elif raw == "<!--/state-->":
            kind, opening = "state", False
        elif raw == "<!--historical-->":
            kind, opening = "historical", True
        else:
            kind, opening = "historical", False
        where = line_of(text, match.start())
        if opening:
            if open_token is not None:
                problems.append(
                    f"line {where}: {kind} marker opens inside an unclosed "
                    f"{open_token[0]} marker; markers do not nest or overlap")
                continue
            open_token = (kind, match)
        else:
            if open_token is None:
                problems.append(f"line {where}: closing {kind} marker with nothing open")
                continue
            if open_token[0] != kind:
                # The outer marker stays open so its own close still pairs. One
                # diagnostic per stray marker reads better than a cascade in
                # which every later marker is also wrong.
                problems.append(f"line {where}: closing {kind} marker inside an open "
                                f"{open_token[0]} marker; markers do not overlap")
                continue
            start = open_token[1]
            found.append({"kind": kind, "line": line_of(text, start.start()),
                          "file_name": start.group(1) if kind == "state" else None,
                          "path": start.group(2) if kind == "state" else None,
                          "value": text[start.end():match.start()],
                          "begin": start.start(), "end": match.end()})
            open_token = None

    if open_token is not None:
        problems.append(f"line {line_of(text, open_token[1].start())}: "
                        f"{open_token[0]} marker is never closed")

    strict = {m.group(0) for m in TOKEN.finditer(text)}
    for match in LOOSE.finditer(text):
        if match.group(0) not in strict:
            problems.append(f"line {line_of(text, match.start())}: malformed marker "
                            f"{match.group(0)!r}")
    return found, problems


def resolve(state: dict, path: str):
    """A dotted path into the emission. Mappings by key, lists by index."""
    node = state
    for segment in path.split("."):
        if isinstance(node, dict) and segment in node:
            node = node[segment]
        elif isinstance(node, list) and segment.lstrip("-").isdigit() \
                and -len(node) <= int(segment) < len(node):
            node = node[int(segment)]
        else:
            return None, False
    return node, True


def normalize(value: str) -> str:
    return " ".join(str(value).split())


def problems(pages: dict[str, str], state_sources: dict[str, dict]) -> list[str]:
    found: list[str] = []
    for name in sorted(pages):
        text = blank(pages[name])
        marked, malformed = spans(text)
        found += [f"{name}:{p}" for p in malformed]

        covered = bytearray(len(text))
        for span in marked:
            for index in range(span["begin"], span["end"]):
                covered[index] = 1

            if span["kind"] == "historical":
                lines = text.count("\n", span["begin"], span["end"]) + 1
                if lines > HISTORICAL_MAX_LINES:
                    found.append(
                        f"{name}:line {span['line']}: historical span covers {lines} "
                        f"lines; the tag marks a statement, not a section "
                        f"(maximum {HISTORICAL_MAX_LINES})")
                continue

            where = f"{name}:line {span['line']}"
            declared = normalize(span["value"])
            if not declared:
                found.append(f"{where}: state binding for {span['path']!r} has an "
                             "empty value")
                continue
            if span["file_name"] not in state_sources:
                found.append(f"{where}: unknown state emission "
                             f"{span['file_name']!r}; known: "
                             f"{sorted(state_sources)}")
                continue
            state = state_sources[span["file_name"]]
            value, ok = resolve(state, span["path"] or "")
            if not ok:
                found.append(f"{where}: path {span['path']!r} does not resolve in "
                             f"{span['file_name']!r}; its sections are "
                             f"{sorted(state)}")
                continue
            if normalize(value) != declared:
                found.append(f"{where}: bound value {declared!r} but "
                             f"{span['file_name']}:{span['path']} is "
                             f"{normalize(value)!r}")

        scannable = "".join(" " if covered[i] else c for i, c in enumerate(text))
        for label, pattern in DENYLIST:
            for match in pattern.finditer(scannable):
                found.append(
                    f"{name}:line {line_of(text, match.start())}: {match.group(0)!r} is "
                    f"{label} and is not declared. Bind it to machine state, or mark "
                    "it historical if it records a past event.")
    return found


def live_pages() -> dict[str, str]:
    return {p.name: p.read_text() for p in sorted(WIKI.glob("*.md"))}


def bindings(pages: dict[str, str]) -> int:
    return sum(1 for text in pages.values()
               for span in spans(blank(text))[0] if span["kind"] == "state")


def self_test() -> int:
    """The six crafted failures, and the null inputs.

    The null input is a wiki with no pages, or an emission with no sections:
    `problems` returns nothing over either, which is what a clean wiki returns,
    so `run` refuses them. A third, quieter one is a wiki with no bindings at
    all — pass 1 then checks nothing while reporting green — and the live case
    at the end of this list is what stands between that and a silent pass."""
    state = {"workspace": {"counts": {"foundation_claims": 180},
                           "foundations": [{"claim_count": 180}]}}

    def over(body: str) -> int:
        return len(problems({"Page.md": body}, state))

    bound = "<!--state:workspace:counts.foundation_claims-->180<!--/state-->"
    cases = [
        ("a correct binding passes", over(f"A {bound}-claim foundation.\n"), 0),
        ("a list index resolves",
         over("<!--state:workspace:foundations.0.claim_count-->180<!--/state-->\n"), 0),
        ("a historical span passes and is not scanned",
         over("<!--historical-->PR #31 registered no claim<!--/historical-->\n"), 0),
        # The six failure fixtures the round is required to ship.
        ("a mismatched binding is caught",
         over(bound.replace(">180<", ">179<")), 1),
        ("a dangling path is caught",
         over(bound.replace("counts.foundation_claims", "counts.no_such_key")), 1),
        ("a malformed marker is caught", over("<!--state:workspace-->180<!--/state-->\n"), 2),
        ("an unmarked denylist hit is caught", over("Filed under PR #31 last week.\n"), 1),
        ("a nested marker is caught",
         over(f"<!--historical-->{bound}<!--/historical-->\n"), 2),
        ("an oversized historical span is caught",
         over("<!--historical-->a\nb\nc\nd<!--/historical-->\n"), 1),
        # The rest of pass 1 and pass 3.
        ("an unclosed marker is caught", over("<!--historical-->hanging\n"), 1),
        ("an empty bound value is caught",
         over("<!--state:workspace:counts.foundation_claims--><!--/state-->\n"), 1),
        ("an unknown emission is caught",
         over("<!--state:elsewhere:counts.foundation_claims-->180<!--/state-->\n"), 1),
        ("a stray closing marker is caught", over("text<!--/state-->\n"), 1),
        # Each denylist pattern bites, and only where it should.
        ("a claim count is caught", over("The registry holds 3 registered claims.\n"), 1),
        ("a round tally is caught", over("Across 46 rounds so far.\n"), 1),
        ("a priority tally is caught", over("49 priorities are filed.\n"), 1),
        ("a bound claim count passes",
         over("<!--state:workspace:counts.foundation_claims-->180<!--/state--> claims.\n"), 0),
        ("prose with no quantity passes", over("The program has two research lines.\n"), 0),
        ("a fenced block is not a declaration",
         over(f"```\n{bound}\nPR #31\n```\n"), 0),
        ("a code span is not a declaration", over(f"Write `{bound}` to bind it.\n"), 0),
        # Null inputs.
        ("no pages yields nothing to check", len(problems({}, state)), 0),
        ("an empty emission yields nothing to check",
         len(problems({"Page.md": "clean prose.\n"}, {})), 0),
        ("the gate refuses no pages", run({}, state, quiet=True), 1),
        ("the gate refuses an empty emission",
         run({"Page.md": "clean prose.\n"}, {}, quiet=True), 1),
        ("the gate refuses a wiki with no bindings",
         run({"Page.md": "clean prose.\n"}, state, quiet=True), 1),
        # The live tree, so none of the above can pass over nothing.
        ("the wiki directory exists", WIKI.is_dir(), True),
        ("the live wiki has pages", len(live_pages()) > 0, True),
        ("the live wiki has at least one binding, so pass 1 is not vacuous",
         bindings(live_pages()) > 0, True),
        ("the live emission carries the counts section",
         "counts" in emission(), True),
    ]
    failures = 0
    print("WIKI STATE BINDINGS SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def run(pages: dict[str, str], state_sources: dict[str, dict],
        quiet: bool = False) -> int:
    def say(message: str) -> None:
        if not quiet:
            print(message, file=sys.stderr)

    if not pages:
        say("WIKI STATE BINDINGS FAILED: no pages under wiki/")
        return 1
    if not state_sources or not any(state_sources.values()):
        say("WIKI STATE BINDINGS FAILED: the state emission is empty, so every "
            "binding would resolve against nothing")
        return 1
    if not bindings(pages):
        # The quiet null input. With no declarations, pass 1 verifies nothing
        # and the run reports green off the denylist alone.
        say("WIKI STATE BINDINGS FAILED: no page declares a state binding. "
            "A wiki that cites no machine state either has no volatile quantity "
            "in it, which is worth saying deliberately, or has stopped declaring "
            "them.")
        return 1
    found = problems(pages, state_sources)
    if found:
        say("WIKI STATE BINDINGS FAILED:")
        for f in found:
            say(f"  - {f}")
        say("\n  wiki/CONVENTIONS.md has the grammar. A volatile quantity is bound "
            "to a path into the state emission, or marked historical if it records "
            "a past event.")
        return 1
    if not quiet:
        print(f"WIKI STATE BINDINGS: clean over {len(pages)} page(s); "
              f"{bindings(pages)} binding(s) verified against the state emission")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    if "--sections" in sys.argv:
        for name, state in sources().items():
            print(f"{name}: {', '.join(sorted(state))}")
        return 0
    return run(live_pages(), sources())


if __name__ == "__main__":
    sys.exit(main())
