"""Wiki links resolve, and links into this repository are commit-pinned.

Two failures the hosted wiki cannot show you. A link to a page that does not
exist renders as an ordinary link and 404s only when someone follows it. A link
into this repository through a branch name renders identically to a pinned one
and resolves to whatever that branch says today — so a page's evidence changes
underneath the sentence citing it, and nothing in either the page or the diff
records that it moved.

Scope:

- **Intra-wiki.** `[text](Page-Name)` and `[[Page-Name]]` must name a file in
  `wiki/`. Fragments and `.md` suffixes are stripped before resolving, and a
  space in a `[[…]]` title is read as a hyphen, which is how the hosted wiki
  maps a page title to its filename.
- **Into this repository.** A link whose path has a `blob`, `tree` or `raw`
  segment carries a ref, and that ref must be a 40-hex commit SHA. A link to the
  repository root carries no ref and is out of scope — there is nothing to pin.
- **External links are out of scope.** Whether some other host still serves a
  document is not a question this repository can answer offline, and a checker
  that reaches the network is a checker that fails on the runner's weather.

Code spans and fenced blocks are skipped: a page documenting the rule quotes the
shape it forbids, and a checker that reads its own documentation as a violation
is one that has to be worked around.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
WIKI = ROOT / "wiki"

REPOSITORY = "github.com/A-M-Berns/alignment-workspace"
COMMIT_SHA = re.compile(r"^[0-9a-f]{40}$")
REF_BEARING = ("blob", "tree", "raw")

# Files in wiki/ that are not pages. The sync job reads this tuple rather than
# carrying its own copy, so a file cannot be a page here and absent there: that
# combination passes this checker and 404s on the hosted wiki.
REPO_ONLY_FILES = ("ORIGIN.md", "CONVENTIONS.md")

INLINE_LINK = re.compile(r"\[[^]]*\]\(\s*<?([^)\s>]+)>?[^)]*\)")
WIKI_LINK = re.compile(r"\[\[([^]|]+)(?:\|[^]]*)?\]\]")
CODE_SPAN = re.compile(r"`[^`]*`")
FENCE = re.compile(r"^\s*```")


def pages(root: pathlib.Path) -> set[str]:
    """Every page name a link may resolve to: the filename without `.md`."""
    return {p.stem for p in root.glob("*.md") if p.name not in REPO_ONLY_FILES}


def targets(text: str) -> list[tuple[int, str]]:
    """Link targets outside code spans and fenced blocks, with line numbers."""
    found: list[tuple[int, str]] = []
    in_fence = False
    for number, raw in enumerate(text.splitlines(), 1):
        if FENCE.match(raw):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        line = CODE_SPAN.sub("", raw)
        found += [(number, m.group(1)) for m in INLINE_LINK.finditer(line)]
        found += [(number, m.group(1)) for m in WIKI_LINK.finditer(line)]
    return found


def repository_ref(target: str) -> str | None:
    """The ref a link into this repository resolves through, if it has one."""
    without_scheme = re.sub(r"^[a-z][a-z0-9+.-]*://", "", target)
    if not without_scheme.startswith(REPOSITORY):
        return None
    rest = without_scheme[len(REPOSITORY):].lstrip("/").split("#")[0].split("?")[0]
    parts = [p for p in rest.split("/") if p]
    for index, part in enumerate(parts[:-1]):
        if part in REF_BEARING:
            return parts[index + 1]
    return None


def problems(root: pathlib.Path) -> list[str]:
    known = pages(root)
    found: list[str] = []
    for path in sorted(root.glob("*.md")):
        for number, target in targets(path.read_text()):
            where = f"{path.name}:{number}"
            if target.startswith("#") or target.startswith("mailto:"):
                continue
            ref = repository_ref(target)
            if ref is not None:
                if not COMMIT_SHA.match(ref):
                    found.append(f"{where}: link into this repository is pinned to "
                                 f"{ref!r}, not a 40-hex commit SHA — {target}")
                continue
            if "://" in target or target.startswith("//"):
                continue
            name = target.split("#")[0].split("?")[0].lstrip("./")
            name = re.sub(r"\.md$", "", name).replace(" ", "-")
            if not name:
                continue
            if name not in known:
                found.append(f"{where}: link to page {name!r}, which does not "
                             f"exist in wiki/ — {target}")
    return found


def self_test() -> int:
    """Null-input cases, and one crafted bad fixture per rule.

    The null input is a wiki with no pages: `problems()` over it returns an
    empty list, which is indistinguishable from a clean wiki, so `main` treats
    an empty page set as a failure and that is pinned here. The two rules each
    get a fixture that must fail, because a rule that has never rejected
    anything is not known to check anything.
    """
    import shutil, tempfile
    tmp = pathlib.Path(tempfile.mkdtemp())
    (tmp / "empty").mkdir()

    def over(**files: str) -> list[str]:
        root = tmp / "case"
        shutil.rmtree(root, ignore_errors=True)
        root.mkdir()
        for name, body in files.items():
            (root / f"{name.replace('_', '-')}.md").write_text(body)
        return problems(root)

    pinned = "0123456789abcdef0123456789abcdef01234567"
    blob = f"https://{REPOSITORY}/blob"
    cases = [
        ("a dangling intra-wiki link is caught",
         len(over(Home="See [the glossary](Glossary).\n")), 1),
        ("a resolving intra-wiki link passes",
         len(over(Home="See [the glossary](Glossary).\n", Glossary="# G\n")), 0),
        ("a double-bracket link to a missing page is caught",
         len(over(Home="See [[Roadmap]].\n")), 1),
        ("a double-bracket page title with a space resolves to its hyphenated file",
         len(over(Home="See [[What Deference Requires]].\n",
                  What_Deference_Requires="# W\n")), 0),
        ("a branch-pinned repository link is caught",
         len(over(Home=f"[report]({blob}/main/AGENTS.md)\n")), 1),
        ("an abbreviated SHA is caught",
         len(over(Home=f"[report]({blob}/0123456/AGENTS.md)\n")), 1),
        ("a tree link on a branch is caught",
         len(over(Home=f"[dir](https://{REPOSITORY}/tree/main/state)\n")), 1),
        ("a commit-pinned repository link passes",
         len(over(Home=f"[report]({blob}/{pinned}/AGENTS.md)\n")), 0),
        ("a link to the repository root carries no ref and passes",
         len(over(Home=f"[repo](https://{REPOSITORY})\n")), 0),
        ("an external link is out of scope",
         len(over(Home="[paper](https://arxiv.org/abs/1609.03543)\n")), 0),
        ("a fenced block is not read as a link",
         len(over(Home=f"```\n[x]({blob}/main/AGENTS.md)\n```\n")), 0),
        ("a code span is not read as a link",
         len(over(Home=f"Never `[x]({blob}/main/AGENTS.md)`.\n")), 0),
        ("an in-page anchor is not a page reference",
         len(over(Home="[top](#top)\n")), 0),
        ("a wiki with no pages yields nothing to check, which main() must reject",
         len(problems(tmp / "empty")), 0),
        ("a repo-side-only file is not a page a link may resolve to",
         len(over(Home="[c](CONVENTIONS)\n", CONVENTIONS="# c\n")), 1),
        ("the checked wiki directory exists", WIKI.is_dir(), True),
        ("the live wiki has pages, so the run is not vacuous",
         len(pages(WIKI)) > 0, True),
        ("every repo-side-only file is present, so the exclusion is not stale",
         all((WIKI / name).is_file() for name in REPO_ONLY_FILES), True),
    ]
    shutil.rmtree(tmp)
    failures = 0
    print("WIKI LINKS SELF-TEST:")
    for label, got, want in cases:
        failures += got != want
        print(f"  {'ok' if got == want else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    if not WIKI.is_dir():
        print("WIKI LINKS FAILED: wiki/ does not exist", file=sys.stderr)
        return 1
    known = pages(WIKI)
    if not known:
        # The null input. Zero pages means zero links, which reports clean and
        # checks nothing — the same shape as a gate that has stopped matching.
        print("WIKI LINKS FAILED: no pages under wiki/", file=sys.stderr)
        return 1
    found = problems(WIKI)
    if found:
        print("WIKI LINKS FAILED:", file=sys.stderr)
        for f in found:
            print(f"  - {f}", file=sys.stderr)
        print("\n  A page link names a file in wiki/. A link into this repository "
              "is pinned to a 40-hex commit SHA, because evidence a branch name "
              "resolves to changes underneath the sentence citing it.",
              file=sys.stderr)
        return 1
    print(f"WIKI LINKS: clean over {len(known)} page(s) "
          "(links resolve; repository links are commit-pinned)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
