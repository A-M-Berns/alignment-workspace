#!/usr/bin/env python3
"""faf-cleanroom mechanical trust gate (STANDARDS.md rule 3). Run it via `scripts/audit.sh`.

Three independent checks, modelled on FAF's `scripts/lean_gates.py`; none subsumes another
(see that file's docstring and `scripts/test-audit/`, which demonstrates each catching
something the others miss):

1. BLANKET AXIOM AUDIT. Every declaration defined in a module under `Cleanroom` (not an
   enumerated list) has its transitive axioms computed from the compiled environment by
   the pinned `leanprover-community/axiom-audit` tool (the same tool, tag and commit FAF
   pins). Anything outside {propext, Classical.choice, Quot.sound} fails, except `sorryAx`
   in a declaration listed in `OPEN.txt`, which is reported separately as Open.
   `native_decide` (in Lean >= 4.2x an auxiliary axiom `<decl>._native.native_decide.ax_*`;
   in older Lean `Lean.ofReduceBool`) and `Lean.trustCompiler` are named explicitly.
   Stale OPEN entries (listed, but no longer using `sorryAx`, or not existing) fail on a
   full run.
2. KERNEL REPLAY. `leanchecker` (shipped in the pinned toolchain) re-checks every
   declaration of the audited modules through the kernel. This catches declarations that
   entered the environment unchecked, which the axiom audit cannot see.
3. SOURCE LINT over `Cleanroom/**/*.lean` (comments and strings stripped first): banned
   constructs fail; `maxRecDepth` / `maxHeartbeats 0` / notation are reported; top-level
   `theorem`/`lemma`/`def`/`abbrev` without a docstring carrying `Source:` and `Kind:` lines
   are warnings (phase 1).

Usage: audit.py [Cleanroom.Module ...] [--json] [--no-replay] [--no-lint] [--no-axioms]
                [--src DIR] [--olean-dir DIR] [--open FILE]
Exit 0 = pass, 1 = a check failed, 2 = the gate itself could not run.
"""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys

LAB = pathlib.Path(__file__).resolve().parents[1]
ROOT_NS = "Cleanroom"
ALLOWED = ("propext", "Classical.choice", "Quot.sound")

TOOL_REPO = "https://github.com/leanprover-community/axiom-audit.git"
TOOL_REF = "v0.1.2"
TOOL_SHA = "46024e005996495c65ef609368e11ab39c4222e3"  # same pin as FAF's lean_gates.py
TOOL_DIR = pathlib.Path(os.environ.get("FAF_AUDIT_TOOL_DIR",
                        pathlib.Path.home() / ".cache" / "faf-cleanroom" / f"axiom-audit-{TOOL_SHA[:8]}"))

TRUST_COMPILER_AXIOMS = {"Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"}
REPLAYING = re.compile(r"^replaying (\S+)$", re.M)
PRIVATE = re.compile(r"^_private\.(?:.*?)\.0\.")
# Components Lean generates under a declaration's name (proof terms, matchers, equation
# lemmas, induction principles, native_decide aux axioms, ...). A sorryAx in such a child
# of an OPEN-listed declaration is the listed declaration's own sorry.
AUX_COMPONENT = re.compile(
    r"^(_.*|match_\d+|proof_\d+|eq_\d+|eq_def|eq_unfold|induct|induct_unfolding|"
    r"mutual_induct|fun_cases|fun_cases_unfolding|go|spec_\d+)$")


def is_native(ax: str) -> bool:
    return ax in TRUST_COMPILER_AXIOMS or "._native." in ax or "native_decide" in ax


def normalize(name: str) -> str:
    return PRIVATE.sub("", name)


# ----------------------------------------------------------------------------- OPEN.txt

def read_open(path: pathlib.Path) -> tuple[dict[str, str], list[str]]:
    """`Name  <reason>` per line; `#` starts a comment line. A missing reason is a problem."""
    entries: dict[str, str] = {}
    problems: list[str] = []
    if not path.is_file():
        return entries, problems
    for i, line in enumerate(path.read_text().splitlines(), 1):
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        parts = s.split(None, 1)
        name, reason = parts[0], (parts[1].strip(" \t-—:") if len(parts) > 1 else "")
        if not reason:
            problems.append(f"{path.name}:{i}: entry {name!r} has no reason")
        if name in entries:
            problems.append(f"{path.name}:{i}: duplicate entry {name!r}")
        entries[name] = reason
    return entries, problems


def open_owner(decl: str, entries: dict[str, str]) -> str | None:
    d = normalize(decl)
    if d in entries:
        return d
    parts = d.split(".")
    for k in range(len(parts) - 1, 0, -1):
        prefix = ".".join(parts[:k])
        if prefix in entries and all(AUX_COMPONENT.match(c) for c in parts[k:k + 1]):
            return prefix
    return None


# ------------------------------------------------------------------------------- modules

def discover(src: pathlib.Path) -> list[str]:
    mods = []
    if (src / f"{ROOT_NS}.lean").is_file():
        mods.append(ROOT_NS)
    d = src / ROOT_NS
    if d.is_dir():
        mods += [".".join(p.relative_to(src).with_suffix("").parts) for p in d.rglob("*.lean")]
    return sorted(mods)


def source_of(src: pathlib.Path, mod: str) -> pathlib.Path:
    return src / (mod.replace(".", "/") + ".lean")


def lean_path(olean_dir: pathlib.Path | None) -> tuple[str, list[str]]:
    proc = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=LAB,
                          capture_output=True, text=True)
    if proc.returncode != 0:
        return "", [f"`lake env` failed: {proc.stderr.strip()[-400:]}"]
    lp = proc.stdout.strip()
    if olean_dir:
        lp = f"{olean_dir}:{lp}"
    return lp, []


def check_oleans(src: pathlib.Path, mods: list[str], lp: str) -> list[str]:
    problems = []
    dirs = [pathlib.Path(p) for p in lp.split(":") if p]
    for m in mods:
        rel = m.replace(".", "/") + ".olean"
        hit = next((d / rel for d in dirs if (d / rel).is_file()), None)
        if hit is None:
            problems.append(f"{m}: no .olean found; run scripts/lean-build {m}")
        elif hit.stat().st_mtime < source_of(src, m).stat().st_mtime:
            problems.append(f"{m}: .olean is older than its source; run scripts/lean-build {m} "
                            "(auditing a stale build would audit old code)")
    return problems


# ---------------------------------------------------------------------------- the tool

def ensure_tool() -> tuple[pathlib.Path | None, list[str]]:
    binary = TOOL_DIR / ".lake" / "build" / "bin" / "axiom-audit"
    if not TOOL_DIR.is_dir():
        TOOL_DIR.parent.mkdir(parents=True, exist_ok=True)
        got = subprocess.run(["git", "clone", "-q", "--depth", "1", "--branch", TOOL_REF,
                              TOOL_REPO, str(TOOL_DIR)], capture_output=True, text=True)
        if got.returncode != 0:
            return None, [f"cloning axiom-audit {TOOL_REF} failed: {got.stderr.strip()[-300:]}"]
    head = subprocess.run(["git", "-C", str(TOOL_DIR), "rev-parse", "HEAD"],
                          capture_output=True, text=True).stdout.strip()
    if head != TOOL_SHA:
        return None, [f"axiom-audit checkout at {TOOL_DIR} is {head!r}, not the pinned {TOOL_SHA}"]
    dirty = subprocess.run(["git", "-C", str(TOOL_DIR), "status", "--porcelain",
                            "--untracked-files=no", "--", "*.lean"],
                           capture_output=True, text=True).stdout.strip()
    if dirty:
        return None, [f"axiom-audit sources at {TOOL_DIR} are modified: {dirty[:200]}"]
    toolchain = (LAB / "lean-toolchain").read_text()
    if not binary.is_file() or (TOOL_DIR / "lean-toolchain").read_text() != toolchain:
        (TOOL_DIR / "lean-toolchain").write_text(toolchain)
        b = subprocess.run(["lake", "build"], cwd=TOOL_DIR, capture_output=True, text=True)
        if b.returncode != 0 or not binary.is_file():
            return None, [f"building axiom-audit failed:\n{(b.stdout + b.stderr)[-1200:]}"]
    return binary, []


# ------------------------------------------------------------------------- axiom audit

def axiom_audit(mods, lp, entries, full_run) -> dict:
    res = {"ran": False, "fail": [], "open": [], "audited": 0, "axiomsUsed": [],
           "native": [], "axiom": [], "unlisted_sorry": [], "stale": []}
    binary, problems = ensure_tool()
    if problems:
        res["error"] = problems
        return res
    env = dict(os.environ, LEAN_PATH=lp)
    proc = subprocess.run([str(binary), "--root", ROOT_NS, "--modules", ",".join(mods),
                           "--json"], cwd=LAB, capture_output=True, text=True, env=env)
    try:
        report = json.loads(proc.stdout.strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        res["error"] = [f"axiom-audit printed no parseable JSON (exit {proc.returncode}): "
                        f"{(proc.stdout + proc.stderr)[-600:]}"]
        return res
    res["ran"] = True
    if "error" in report:
        res["error"] = [f"axiom-audit: {report['error']}"]
        return res
    if tuple(report.get("allowed") or ()) != ALLOWED:
        res["fail"].append(f"axiom-audit ran with allowlist {report.get('allowed')}")
    res["audited"] = report.get("audited") or 0
    res["axiomsUsed"] = report.get("axiomsUsed") or []
    if res["audited"] <= 0:
        res["fail"].append("0 declarations audited: an audit that audits nothing checks nothing")
    sorry_owners: set[str] = set()
    for v in report.get("violations") or []:
        decl, bad = v["decl"], v["axioms"]
        natives = [a for a in bad if is_native(a)]
        others = [a for a in bad if a != "sorryAx" and not is_native(a)]
        if natives:
            res["native"].append(decl)
            res["fail"].append(f"NATIVE   {decl}: trusts the compiler via {natives}")
        if others:
            res["axiom"].append(decl)
            what = "declares an axiom" if others == [decl] else f"depends on axioms {others}"
            res["fail"].append(f"AXIOM    {decl}: {what}")
        if "sorryAx" in bad:
            owner = open_owner(decl, entries)
            if owner is None:
                res["unlisted_sorry"].append(decl)
                res["fail"].append(f"SORRY    {decl}: uses sorryAx and is not listed in OPEN.txt "
                                   "(a result resting on an Open statement is itself Open)")
            else:
                sorry_owners.add(owner)
                if normalize(decl) == owner:
                    res["open"].append(decl)
    if full_run:
        for name in sorted(set(entries) - sorry_owners):
            res["stale"].append(name)
            res["fail"].append(f"STALE    OPEN.txt lists {name}, which does not use sorryAx "
                               "(proved, renamed or deleted?) — remove or fix the entry")
    return res


# ------------------------------------------------------------------------ kernel replay

def replay(mods, lp) -> dict:
    res = {"ran": False, "fail": [], "replayed": []}
    which = subprocess.run(["elan", "which", "leanchecker"], cwd=LAB, capture_output=True, text=True)
    version = (LAB / "lean-toolchain").read_text().strip().rsplit(":", 1)[-1]
    if which.returncode != 0 or version not in which.stdout:
        res["error"] = [f"leanchecker for the pinned toolchain {version} not found "
                        f"({which.stdout.strip() or which.stderr.strip()})"]
        return res
    env = dict(os.environ, LEAN_PATH=lp)
    proc = subprocess.run(["leanchecker", "-v", *mods], cwd=LAB, capture_output=True,
                          text=True, env=env)
    out = proc.stdout + proc.stderr
    res["ran"] = True
    res["replayed"] = sorted(set(REPLAYING.findall(out)))
    if proc.returncode != 0:
        tail = [l for l in out.splitlines() if l and not l.startswith("replaying ")][:8]
        res["fail"].append(f"REPLAY   leanchecker exited {proc.returncode}: " + " | ".join(tail))
    missing = [m for m in mods if m not in res["replayed"]]
    if missing:
        res["fail"].append(f"REPLAY   modules not replayed: {missing}")
    return res


# ---------------------------------------------------------------------------- source lint

def strip_code(text: str) -> str:
    """Blank out comments (nested block, doc, line) and string literals, keeping newlines."""
    out, i, n, depth = [], 0, len(text), 0
    in_str = False
    while i < n:
        c, two = text[i], text[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1; out.append("  "); i += 2; continue
            if two == "-/":
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if in_str:
            if c == "\\" and i + 1 < n:
                out.append("  "); i += 2; continue
            if c == '"':
                in_str = False
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if two == "/-":
            depth = 1; out.append("  "); i += 2; continue
        if two == "--":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if c == '"':
            in_str = True; out.append(" "); i += 1; continue
        out.append(c); i += 1
    return "".join(out)


MODS = r"(?:(?:private|protected|noncomputable|partial|nonrec|scoped|local|unsafe)\s+)*"
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
LINT_FAIL = [
    (r"\baxiom\b", "`axiom` declaration"),
    (r"\bnative_decide\b|\+native\b|\bofReduceBool\b|\bofReduceNat\b|\btrustCompiler\b",
     "native_decide / compiler trust"),
    (r"\bimplemented_by\b", "`implemented_by`"),
    (r"\bextern\b", "`@[extern]`"),
    (r"\bunsafe\b", "`unsafe`"),
    (r"\bskipKernelTC\b|set_option\s+debug\.", "`debug.*` option (e.g. skipKernelTC)"),
    (r"\bopaque\b", "`opaque` constant"),
    (r"\bmacro_rules\b|\belab_rules\b", "`macro_rules`/`elab_rules`"),
    (rf"(?m)^\s*{ATTRS}{MODS}(?:syntax|macro|elab|declare_syntax_cat|notation3?)\b(?!\s*:=)",
     None),  # classified below: notation is report-only, the rest fail
    (r"@\[\s*(?:term_elab|command_elab|tactic|macro|builtin_\w+)\b", "elaborator attribute"),
    (r"\b(?:run_cmd|run_elab|run_meta)\b", "`run_cmd`/`run_elab`/`run_meta` (environment hacking)"),
    (r"\b(?:addDeclCore|addDeclWithoutChecking|setEnv|modifyEnv|replayConsts)\b",
     "direct environment manipulation"),
]
LINT_REPORT = [
    (r"set_option\s+maxRecDepth\b", "set_option maxRecDepth"),
    (r"set_option\s+maxHeartbeats\s+0\b", "set_option maxHeartbeats 0"),
    (r"(?m)^\s*(?:(?:scoped|local)\s+)*(?:infixl?|infixr|prefix|postfix)\b", "notation"),
]
IMPORT = re.compile(r"(?m)^import\s+(\S+)")
BAD_IMPORT = re.compile(r"^(?:Scratchpad|run)(?:\.|$)|\.Scratchpad(?:\.|$)|(?:^|\.)_GateTest(?:\.|$)")
DECL = re.compile(rf"(?m)^[ \t]*{ATTRS}{MODS}(theorem|lemma|def|abbrev)\s+([^\s:({{\[]+)")


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def docstring_before(raw: str, pos: int) -> str | None:
    """The `/-- … -/` doc comment attached to the declaration whose modifiers start at `pos`
    (attributes may sit between the doc comment and the keyword)."""
    before = raw[:pos].rstrip()
    while True:  # peel attribute blocks
        m = re.search(r"@\[[^\]]*\]\s*$", before)
        if not m:
            break
        before = before[:m.start()].rstrip()
    if not before.endswith("-/"):
        return None
    start = before.rfind("/--")
    if start < 0 or before.rfind("/-!") > start:
        return None
    return before[start + 3:-2]


def lint(src: pathlib.Path, mods: list[str]) -> dict:
    res = {"fail": [], "report": [], "warn": []}
    for m in mods:
        path = source_of(src, m)
        raw = path.read_text()
        code = strip_code(raw)
        rel = f"{m.replace('.', '/')}.lean"
        for pat, what in LINT_FAIL:
            for hit in re.finditer(pat, code):
                ln = line_of(code, hit.start())
                if what is None:
                    kw = re.search(r"(syntax|macro|elab|declare_syntax_cat|notation3?)\b",
                                   hit.group(0)).group(1)
                    if kw.startswith("notation"):
                        res["report"].append(f"LINT     {rel}:{ln}: notation definition")
                    else:
                        res["fail"].append(f"LINT     {rel}:{ln}: `{kw}` definition "
                                           "(custom syntax can change what a statement means)")
                else:
                    res["fail"].append(f"LINT     {rel}:{ln}: {what}")
        for pat, what in LINT_REPORT:
            for hit in re.finditer(pat, code):
                res["report"].append(f"LINT     {rel}:{line_of(code, hit.start())}: {what}")
        for hit in IMPORT.finditer(code):
            if BAD_IMPORT.search(hit.group(1)):
                res["fail"].append(f"LINT     {rel}:{line_of(code, hit.start())}: imports "
                                   f"scratch/run/test module {hit.group(1)}")
        for hit in DECL.finditer(code):
            start = hit.start() + (len(hit.group(0)) - len(hit.group(0).lstrip()))
            doc = docstring_before(raw, start)
            name = hit.group(2)
            where = f"{rel}:{line_of(code, hit.start())}"
            if doc is None:
                res["warn"].append(f"DOC      {where}: {hit.group(1)} {name} has no docstring")
            else:
                missing = [k for k in ("Source:", "Kind:") if k not in doc]
                if missing:
                    res["warn"].append(f"DOC      {where}: {hit.group(1)} {name} docstring "
                                       f"lacks {' and '.join(missing)}")
    return res


# ----------------------------------------------------------------------------------- main

def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("modules", nargs="*")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--no-replay", action="store_true")
    ap.add_argument("--no-lint", action="store_true")
    ap.add_argument("--no-axioms", action="store_true")
    ap.add_argument("--src", type=pathlib.Path, default=LAB, help="source root (default: the lab)")
    ap.add_argument("--olean-dir", type=pathlib.Path, help="extra olean dir, searched first")
    ap.add_argument("--open", type=pathlib.Path, default=LAB / "OPEN.txt")
    a = ap.parse_args(argv)
    src = a.src.resolve()
    all_mods = discover(src)
    mods = sorted(set(a.modules)) if a.modules else all_mods
    full_run = not a.modules or set(mods) >= set(all_mods)
    out: dict = {"modules": mods, "full_run": full_run}
    errors: list[str] = []
    fails: list[str] = []

    unknown = [m for m in mods if not (m == ROOT_NS or m.startswith(ROOT_NS + "."))
               or not source_of(src, m).is_file()]
    if not mods:
        errors.append(f"no modules under {src / ROOT_NS} to audit")
    if unknown:
        errors.append(f"not Cleanroom modules with sources under {src}: {unknown}")
    entries, open_problems = read_open(a.open)
    fails += [f"OPEN.txt {p}" for p in open_problems]

    if not errors and not (a.no_axioms and a.no_replay):
        lp, e = lean_path(a.olean_dir.resolve() if a.olean_dir else None)
        errors += e
        if not e:
            stale = check_oleans(src, mods, lp)
            fails += [f"BUILD    {p}" for p in stale]
            if not stale:
                if not a.no_axioms:
                    ax = axiom_audit(mods, lp, entries, full_run)
                    out["axioms"] = ax
                    errors += ax.get("error", [])
                    fails += ax["fail"]
                if not a.no_replay:
                    rp = replay(mods, lp)
                    out["replay"] = rp
                    errors += rp.get("error", [])
                    fails += rp["fail"]
    if not errors and not a.no_lint:
        li = lint(src, mods)
        out["lint"] = li
        fails += li["fail"]

    out["errors"], out["fail"] = errors, fails
    rc = 2 if errors else (1 if fails else 0)
    out["rc"] = rc
    if a.json:
        print(json.dumps(out, indent=1))
        return rc

    print(f"faf-cleanroom audit: {len(mods)} module(s){'' if full_run else ' (subset: stale-OPEN check skipped)'}")
    if "axioms" in out and out["axioms"]["ran"]:
        ax = out["axioms"]
        print(f"  axioms : {ax['audited']} declaration(s); axioms used: {ax['axiomsUsed'] or ['none']}")
        for d in ax["open"]:
            print(f"  OPEN     {d}: {entries.get(normalize(d), '')}")
    if "replay" in out and out["replay"]["ran"]:
        print(f"  replay : {len(out['replay']['replayed'])} module(s) replayed by leanchecker")
    if "lint" in out:
        for r in out["lint"]["report"]:
            print(f"  (report) {r}")
        w = out["lint"]["warn"]
        for r in w[:40]:
            print(f"  (warn)   {r}")
        if len(w) > 40:
            print(f"  (warn)   … {len(w) - 40} more docstring warnings")
    for e in errors:
        print(f"  ERROR    {e}")
    for f in fails:
        print(f"  FAIL     {f}")
    print({0: "PASS", 1: "FAIL", 2: "ERROR (gate could not run)"}[rc])
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
