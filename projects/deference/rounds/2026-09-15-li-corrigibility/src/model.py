"""Load the 2026-09-09 mediated-repair-dominance model by path, as the package `mrd`.

The model's modules use relative imports, so it is registered as a package under a
name that does not collide with this round's own `src`.  Nothing in it is modified.
"""
from __future__ import annotations

import importlib
import importlib.util
import sys
from pathlib import Path

MRD = Path(__file__).resolve().parents[2] / "2026-09-09-mediated-repair-dominance" / "src"


def load():
    if "mrd" not in sys.modules:
        spec = importlib.util.spec_from_file_location(
            "mrd", MRD / "__init__.py", submodule_search_locations=[str(MRD)])
        module = importlib.util.module_from_spec(spec)
        sys.modules["mrd"] = module
        spec.loader.exec_module(module)
    return {name: importlib.import_module(f"mrd.{name}")
            for name in ("world", "shop", "fixtures", "lift", "analysis", "corrigibility")}
