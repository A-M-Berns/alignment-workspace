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


def audit(modules: list[pathlib.Path], root: pathlib.Path) -> list[str]:
    problems: list[str] = []
    for path in modules:
        tree = ast.parse(path.read_text(), filename=str(path))
        if not ast.get_docstring(tree):
            problems.append(f"{path.relative_to(root)}: no module docstring stating "
                            "what a passing verdict means")
        for node in ast.walk(tree):
            names = []
            if isinstance(node, ast.Import):
                names = [a.name.split(".")[0] for a in node.names]
            elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                names = [node.module.split(".")[0]]
            for n in names:
                if n not in STDLIB:
                    problems.append(f"{path.relative_to(root)}: third-party import "
                                    f"{n!r}; contributor checkers are stdlib-only")
        if not any(isinstance(n, ast.FunctionDef) and n.name == "check"
                   for n in tree.body):
            problems.append(f"{path.relative_to(root)}: no top-level `check` function")
    return problems


def self_test() -> int:
    """Null-input cases: the gate must not pass by finding no checkers.

    There are currently zero contributor checkers, so the live run is *all*
    null input — it passes over an empty directory every time, and would go on
    passing if the audit logic were deleted. These cases exercise the logic on
    synthetic modules so the green tick means something.
    """
    import tempfile, shutil
    tmp = pathlib.Path(tempfile.mkdtemp())
    def one(name: str, body: str) -> list[str]:
        f = tmp / name
        f.write_text(body)
        return audit([f], tmp)
    good = '"""What a pass means."""\ndef check(i, p):\n    return True, "ok"\n'
    cases = [
        ("a well-formed checker passes", one("good.py", good), 0),
        ("a missing docstring is caught",
         one("nodoc.py", 'def check(i, p):\n    return True, "ok"\n'), 1),
        ("a third-party import is caught",
         one("dep.py", '"""d."""\nimport numpy\ndef check(i, p):\n    return True, ""\n'), 1),
        ("a missing check function is caught",
         one("nofn.py", '"""d."""\ndef verify(i, p):\n    return True, ""\n'), 1),
        ("a nested check function does not count",
         one("nested.py", '"""d."""\nclass C:\n    def check(self, i, p):\n        return True, ""\n'), 1),
    ]
    shutil.rmtree(tmp)
    failures = 0
    print("CONTRIB HYGIENE SELF-TEST:")
    for label, got, want in cases:
        ok = len(got) == want
        failures += not ok
        print(f"  {'ok' if ok else 'FAIL'}: {label}")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    modules = sorted(p for p in CONTRIB.glob("*.py") if p.name != "__init__.py")
    problems = audit(modules, ROOT)
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
