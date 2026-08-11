"""Hygiene for contributor-supplied checkers.

What CI can check mechanically: no third-party imports, and a docstring is
present. What it cannot check is whether the docstring is *true* — whether the
verdict means what it says. That is exactly why a claim certified by anything
here is capped at `contributor-checked` until a maintainer reads it.
"""
from __future__ import annotations

import ast
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
CONTRIB = ROOT / "checkers" / "contrib"
# `sys.stdlib_module_names` is 3.10+; fall back so the gate runs on 3.9 too.
_NAMES = getattr(sys, "stdlib_module_names", None)
if _NAMES is None:
    import distutils.sysconfig as _sc  # noqa: F401  (3.9 fallback)
    _NAMES = frozenset(sys.builtin_module_names) | {
        "fractions", "itertools", "math", "decimal", "collections", "dataclasses",
        "typing", "pathlib", "json", "re", "os", "sys", "functools", "operator",
        "enum", "abc", "copy", "random", "statistics", "heapq", "bisect", "ast",
        "textwrap", "string", "hashlib", "unittest", "argparse", "csv", "io",
    }
STDLIB = set(_NAMES) | {"checkers"}


def main() -> int:
    problems: list[str] = []
    modules = sorted(p for p in CONTRIB.glob("*.py") if p.name != "__init__.py")
    for path in modules:
        tree = ast.parse(path.read_text(), filename=str(path))
        if not ast.get_docstring(tree):
            problems.append(f"{path.relative_to(ROOT)}: no module docstring stating "
                            "what a passing verdict means")
        for node in ast.walk(tree):
            names = []
            if isinstance(node, ast.Import):
                names = [a.name.split(".")[0] for a in node.names]
            elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                names = [node.module.split(".")[0]]
            for n in names:
                if n not in STDLIB:
                    problems.append(f"{path.relative_to(ROOT)}: third-party import "
                                    f"{n!r}; contributor checkers are stdlib-only")
        if not any(isinstance(n, ast.FunctionDef) and n.name == "check"
                   for n in tree.body):
            problems.append(f"{path.relative_to(ROOT)}: no top-level `check` function")
    if problems:
        print("CONTRIB HYGIENE FAILED:", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        return 1
    print(f"CONTRIB HYGIENE: {len(modules)} contributor checker(s), stdlib-only, "
          "each with a meaning docstring and a check function")
    return 0


if __name__ == "__main__":
    sys.exit(main())
