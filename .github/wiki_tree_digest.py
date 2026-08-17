#!/usr/bin/env python3
"""One definition of "what the hosted wiki should contain", as a digest.

Two things need it and must agree: `wiki/ORIGIN.md`, whose receipt lets a reader
tell whether the imported pages have moved since intake, and the sync job's
post-push verification, which compares the pushed remote against `wiki/`.

The digest is sha256 over one line per file, `<sha256>  <relative path>`, sorted
by path, newline-terminated. `.git/` is always excluded; anything else is named
on the command line, so what a digest covers is visible at the call site.

    python3 .github/wiki_tree_digest.py wiki --exclude ORIGIN.md CONVENTIONS.md
"""
from __future__ import annotations

import hashlib
import pathlib
import sys


def manifest(root: pathlib.Path, exclude: set[str]) -> list[str]:
    lines = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        relative = path.relative_to(root).as_posix()
        if relative.split("/")[0] == ".git" or relative in exclude:
            continue
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(f"{digest}  {relative}")
    return lines


def digest(root: pathlib.Path, exclude: set[str]) -> tuple[str, int]:
    lines = manifest(root, exclude)
    body = "".join(line + "\n" for line in lines)
    return hashlib.sha256(body.encode()).hexdigest(), len(lines)


def main(argv: list[str]) -> int:
    if not argv or argv[0].startswith("-"):
        print(__doc__, file=sys.stderr)
        return 2
    root = pathlib.Path(argv[0])
    exclude = set(argv[argv.index("--exclude") + 1:]) if "--exclude" in argv else set()
    if not root.is_dir():
        print(f"WIKI TREE DIGEST FAILED: {root} is not a directory", file=sys.stderr)
        return 1
    value, count = digest(root, exclude)
    if not count:
        # The null input. A digest over nothing is a fixed constant, and two
        # empty trees agree; reporting that as a match would verify nothing.
        print(f"WIKI TREE DIGEST FAILED: no files under {root}", file=sys.stderr)
        return 1
    print(f"{value}  {count} file(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
