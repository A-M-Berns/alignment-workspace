"""Load the mediated-repair-dominance round's `src` package under its own name, so its
relative imports resolve without colliding with this round's `src`."""

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
MRD = HERE.parent / "2026-09-09-mediated-repair-dominance"
LI = HERE.parent / "2026-09-15-li-corrigibility"


def load_package(name, root):
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(
        name, root / "src" / "__init__.py", submodule_search_locations=[str(root / "src")])
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def mrd():
    """The mediated-repair-dominance package: `.world`, `.shop`, `.lift`, `.fixtures`,
    `.analysis`."""
    import importlib
    load_package("mrd_src", MRD)
    return {k: importlib.import_module("mrd_src." + k)
            for k in ("world", "shop", "lift", "fixtures", "analysis")}
