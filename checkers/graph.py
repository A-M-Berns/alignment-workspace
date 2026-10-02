"""Checker and deriver for the argument map under `graph/`.

Usage:
    python3 -m checkers.graph --root <tree> [--scope ID] [--as HANDLE] [--why]
                              [--window-dp] [--frontier K] [--lambda X]
                              [--registry CLAIMS.md] [--dry-run]
    python3 -m checkers.graph --self-test

The checker reads `graph/` (frame, policy, nodes, events, proposals), refuses
on any rule violation (printed `REFUSE <rule> <path>: <reason>`, exit 1) and
never repairs. When the tree passes it derives every number (levels, beliefs,
statuses, proof sets, costs, loads, probabilities, values, the ranking) and
writes `graph/derived.json`, `graph/tasks.md`, `graph/view.md` and
`graph/versions.json`; each generated file carries a hash of its own content
so a hand edit is detected and refused on the next run.

Numbers that are compared with a threshold or summed into a status or value
are exact `fractions.Fraction`; the information estimates (bits) are floats,
since they are advice. Choices this module makes where its specification is
silent are listed in the docstring of `derive`.

Two conventions the files depend on. The checker stops at the first refusal
(one line, exit 1) rather than collecting every violation; run it again after
each fix. A chat reference `chats/<file>.jsonl#t<n>` names the n-th line
(1-based) of that file, a JSON object whose `text` (or `content`) field holds
the turn; `verbatim` must occur in the answer turn, whitespace-normalized and
case-folded.

Streams. `REFUSE`, `WARN` and `OK` lines go to stderr. The four committed
files (`derived.json`, `versions.json`, `tasks.md`, `view.md`) are rendered
the same way whatever flags are given: the pooled default view, unscoped,
with numbers in no column. `--why`, `--as`, `--scope`, `--lambda`,
`--window-dp` and `--frontier` produce a second, personal derivation whose
task list and view go to stdout (or to `--out PATH`, which must lie outside
`graph/`); `--dry-run` writes nothing and prints that derivation (the plain
one when no such flag is given) as JSON on stdout, nothing else.
"""
from __future__ import annotations

import argparse
import copy
import datetime as _dt
import hashlib
import itertools
import json
import math
import os
import pathlib
import random
import re
import subprocess
import sys
from collections import defaultdict
from fractions import Fraction as Q

CHECKER_VERSION = "0.3"
INF = float("inf")
# `frame`: a sub-frame, a programme-shaped plan root whose children are its own roots (steps)
KINDS = {"and", "or", "leaf", "cases", "choose", "frame"}
LEAF_KINDS = {"assumption", "hypothesis", "record", "bridge", "step", "question",
              "picture", "completeness", "partition", "terminal"}
ROLES = {"plan", "risk-story", "shared-claim"}
PRESETS = {"worst-case", "probabilistic", "expected-utility"}
EVENT_KINDS = {"map-read", "trace", "pass", "estimate", "gestalt", "admit", "classify",
               "identify", "approve", "audit", "withdraw", "external", "retrospective",
               "survey", "rule", "attribution"}
ATTRIBUTION_VERDICTS = {"vouched", "disputed"}
HOWS = {"said", "approved"}
VIAS = {"chat", "obsidian", "voice"}
DIMENSIONS = {"valid", "ref", "both"}
DISCHARGES = {"definitional", "proved-in-model", "restates-conclusion", "open"}
ATTRIBUTIONS = {"author-stated", "formalizer-stated", "reconstructed"}
JUDGMENT_KINDS = {"admit", "approve", "estimate", "gestalt", "classify", "identify"}
LEVEL_KINDS = {"map-read", "trace", "pass"}
AUDIT_VERDICTS = {"agree", "disagree"}
_RULE_VERSION = re.compile(r"^\d{4}-\d{2}-\d{2}\.\d+$")
_EVENT_ID = re.compile(r"^([A-Za-z0-9_.]+)-[A-Za-z0-9_.-]+$")
FORBIDDEN_KEYS = {"level", "V", "J", "credence", "probability", "status", "weight", "w",
                  "conditional", "p", "value", "utility", "load", "cost"}
PROPOSAL_KINDS = {"merge", "split", "retarget", "sharpen", "new-root", "edge", "class", "sub-frame"}
PROPOSAL_STATUS = {"proposed", "approved", "applied", "withdrawn"}
GENERATED = ("derived.json", "versions.json", "tasks.md", "view.md")
LAYOUT_FILES = {"frame.yaml", "policy.yaml", "derived.json", "versions.json", "tasks.md",
                "view.md", "PROTOCOL.md", "README.md", "DESIGN-LOG.md"}
# Rule 13: the world model is enumerated per connected component of roots (roots joined
# by a shared proof-set element); a component above this many worlds is refused.
MAX_WORLDS_PER_COMPONENT = 1 << 15
STALE_TABLE = "leaf became a table"


class Refuse(Exception):
    def __init__(self, rule, path, reason):
        super().__init__(f"REFUSE {rule} {path}: {reason}")
        self.rule, self.path, self.reason = rule, path, reason


# ---------------------------------------------------------------- flat YAML (§2.0)
_INT = re.compile(r"^-?\d+$")
_DEC = re.compile(r"^-?\d+\.\d+$")
_FRAC = re.compile(r"^-?\d+/\d+$")
_KEY = re.compile(r'^("(?:[^"\\]|\\.)*"|[^\s:#"\[{-][^:]*?)\s*:(?:\s+(.*))?$')


def _scalar(tok):
    tok = tok.strip()
    if tok == "true":
        return True
    if tok == "false":
        return False
    if tok in ("null", "~", ""):
        return None
    if tok.startswith('"'):
        return json.loads(tok)
    if _INT.match(tok):
        return int(tok)
    if _DEC.match(tok) or _FRAC.match(tok):
        return Q(tok)
    return tok


def _strip_comment(line):
    inq, i = False, 0
    while i < len(line):
        c = line[i]
        if c == '"':
            inq = not inq
        elif c == "\\" and inq:
            i += 1
        elif c == "#" and not inq and (i == 0 or line[i - 1] in " \t"):
            return line[:i]
        i += 1
    return line


class _Flow:
    """Recursive-descent parser for the flow subset: scalars, {k: v}, [a, b]."""

    def __init__(self, s):
        self.s, self.i = s, 0

    def _ws(self):
        while self.i < len(self.s) and self.s[self.i] in " \t":
            self.i += 1

    def value(self, depth=0):
        self._ws()
        c = self.s[self.i] if self.i < len(self.s) else ""
        if c == "{":
            if depth >= 2:
                raise YamlError("a flow map nested two levels deep")
            return self._map(depth)
        if c == "[":
            if depth >= 2:
                raise YamlError("a flow list nested two levels deep")
            return self._list(depth)
        return self._scalar()

    def _scalar(self):
        self._ws()
        s, i = self.s, self.i
        if i < len(s) and s[i] == '"':
            j = i + 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            if j >= len(s):
                raise YamlError("unterminated string")
            self.i = j + 1
            return _scalar(s[i:j + 1])
        j = i
        while j < len(s) and s[j] not in ",]}:":
            j += 1
        self.i = j
        return _scalar(s[i:j])

    def _map(self, depth):
        self.i += 1
        out = {}
        while True:
            self._ws()
            if self.i >= len(self.s):
                raise YamlError("unterminated flow map")
            if self.s[self.i] == "}":
                self.i += 1
                return out
            key = self._scalar()
            self._ws()
            if self.i >= len(self.s) or self.s[self.i] != ":":
                raise YamlError("flow map entry without ':'")
            self.i += 1
            val = self.value(depth + 1)
            if isinstance(val, dict) or (isinstance(val, list) and any(isinstance(x, (dict, list)) for x in val)):
                raise YamlError("a flow map's values are scalars or [lo, hi] pairs")
            out[key] = val
            self._ws()
            if self.i < len(self.s) and self.s[self.i] == ",":
                self.i += 1

    def _list(self, depth):
        self.i += 1
        out = []
        while True:
            self._ws()
            if self.i >= len(self.s):
                raise YamlError("unterminated flow list")
            if self.s[self.i] == "]":
                self.i += 1
                return out
            val = self.value(depth + 1)
            if isinstance(val, list):
                raise YamlError("a flow list holds scalars or flow maps")
            out.append(val)
            self._ws()
            if self.i < len(self.s) and self.s[self.i] == ",":
                self.i += 1


class YamlError(Exception):
    pass


def parse_flow(s):
    if not s.lstrip().startswith(("{", "[")):
        return _scalar(s)
    p = _Flow(s)
    v = p.value()
    p._ws()
    if p.i != len(s):
        raise YamlError(f"trailing text after value: {s[p.i:]!r}")
    return v


def parse_flat_yaml(text):
    out, cur = {}, None
    for raw in text.splitlines():
        line = _strip_comment(raw).rstrip()
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        if indent == 0:
            m = _KEY.match(line)
            if not m:
                raise YamlError(f"not 'key: value': {line!r}")
            key = _scalar(m.group(1)) if m.group(1).startswith('"') else m.group(1).strip()
            if key in out:
                raise YamlError(f"duplicate key {key!r}")
            val = m.group(2)
            if val is None or not val.strip():
                out[key], cur = None, key
            else:
                out[key], cur = parse_flow(val.strip()), None
        else:
            if cur is None:
                raise YamlError(f"indented line under a scalar: {line!r}")
            s = line.strip()
            if s.startswith("- "):
                if out[cur] is None:
                    out[cur] = []
                if not isinstance(out[cur], list):
                    raise YamlError(f"list item under a map key {cur!r}")
                item = parse_flow(s[2:])
                if isinstance(item, list):
                    raise YamlError("a block list item is a scalar or a flow map")
                out[cur].append(item)
            else:
                m = _KEY.match(s)
                if not m:
                    raise YamlError(f"not 'sub: value': {line!r}")
                if out[cur] is None:
                    out[cur] = {}
                if not isinstance(out[cur], dict):
                    raise YamlError(f"map entry under a list key {cur!r}")
                sub = _scalar(m.group(1)) if m.group(1).startswith('"') else m.group(1).strip()
                val = parse_flow((m.group(2) or "").strip())
                if isinstance(val, list):
                    raise YamlError("a block map's values are scalars or flow maps")
                out[cur][sub] = val
    return out


# ---------------------------------------------------------------- loading
def normalize_statement(text):
    """Apostrophes and quotation marks deleted ("expert's" = "experts"), every other punctuation mark a space
    ("exact-introspection" = "exact introspection"), whitespace collapsed, case folded (§2)."""
    text = re.sub(r"['\"`´‘’“”]", "", text)
    text = re.sub(r"[^\w\s]", " ", text)
    return " ".join(text.split()).casefold()


def sha(content):
    return hashlib.sha256(content.encode("utf-8")).hexdigest()[:24]


def _sections(body):
    out, name = {}, None
    for line in body.splitlines():
        m = re.match(r"^## (\S.*)$", line)
        if m:
            name = m.group(1).strip()
            out[name] = []
        elif name is not None:
            out[name].append(line)
    return {k: "\n".join(v).strip() for k, v in out.items()}


def parse_node_text(text, path):
    if not text.startswith("---\n"):
        raise Refuse(12, path, "node file does not open with frontmatter")
    end = text.find("\n---", 4)
    if end < 0:
        raise Refuse(12, path, "frontmatter without closing ---")
    try:
        fm = parse_flat_yaml(text[4:end])
    except YamlError as e:
        raise Refuse(12, path, f"flat-YAML violation: {e}")
    body = text[end + 4:]
    sec = _sections(body)
    for need in ("Statement", "Source"):
        if need not in sec:
            raise Refuse(12, path, f"node file missing '## {need}'")
    node = dict(fm)
    node["_path"], node["_statement"], node["_source"] = path, sec["Statement"], sec["Source"]
    node["_notes"] = sec.get("Notes", "")
    node.setdefault("children", [])
    node.setdefault("rows", [])
    if node["children"] is None:
        node["children"] = []
    return node


class Tree:
    def __init__(self, root):
        self.root = pathlib.Path(root)
        self.graph = self.root / "graph"
        self.frame = self.policy = None
        self.nodes, self.events, self.proposals, self.chats = {}, [], [], {}
        self.versions = {}
        self.warnings = []
        self.registry = None

    def rel(self, p):
        try:
            return str(pathlib.Path(p).relative_to(self.root))
        except ValueError:
            return str(p)


def load_tree(root, registry=None):
    t = Tree(root)
    g = t.graph
    if not (g / "frame.yaml").is_file():
        raise Refuse(12, "graph/frame.yaml", "frame missing")
    if not (g / "policy.yaml").is_file():
        raise Refuse(12, "graph/policy.yaml", "policy missing")
    for name in ("frame", "policy"):
        try:
            setattr(t, name, parse_flat_yaml((g / f"{name}.yaml").read_text()))
        except YamlError as e:
            raise Refuse(12, f"graph/{name}.yaml", f"flat-YAML violation: {e}")
    for p in sorted(g.rglob("*")):
        if p.is_dir():
            continue
        r = p.relative_to(g).as_posix()
        ok = (r in LAYOUT_FILES or re.match(r"^nodes/[^/]+\.md$", r) or re.match(r"^events/[^/]+\.jsonl$", r)
              or re.match(r"^proposals/P-\d+(\.md|/[^/]+\.md)$", r))
        if not ok:
            raise Refuse(11, f"graph/{r}", "file outside the graph layout")
    if not (g / "DESIGN-LOG.md").is_file():
        raise Refuse(11, "graph/DESIGN-LOG.md", "design log missing (every design change and rollback is logged there)")
    for i, line in enumerate((g / "DESIGN-LOG.md").read_text().splitlines(), 1):
        if line.strip() and not line.startswith("#") and not re.match(
                r"^- \d{4}-\d{2}-\d{2} (change|rollback|confusion) @\S+ — .+", line):
            t.warnings.append(f"graph/DESIGN-LOG.md:{i}: malformed entry")
    for p in sorted((g / "nodes").glob("*.md")) if (g / "nodes").is_dir() else []:
        n = parse_node_text(p.read_text(), t.rel(p))
        if n.get("id") in t.nodes:
            raise Refuse(1, t.rel(p), f"duplicate node id {n.get('id')!r}")
        if not isinstance(n.get("id"), str):
            raise Refuse(2, t.rel(p), "node without an id")
        t.nodes[n["id"]] = n
    for p in sorted((g / "events").glob("*.jsonl")) if (g / "events").is_dir() else []:
        lines = [l for l in p.read_text().splitlines() if l.strip()]
        if not lines:
            raise Refuse(5, t.rel(p), "empty ledger")
        for i, line in enumerate(lines, 1):
            try:
                e = json.loads(line, parse_float=Q)
            except json.JSONDecodeError as exc:
                raise Refuse(5, f"{t.rel(p)}:{i}", f"not JSON: {exc}")
            e["_path"], e["_ledger"], e["_seq"] = f"{t.rel(p)}:{i}", p.stem, len(t.events)
            t.events.append(e)
    for p in sorted((g / "proposals").glob("P-*.md")) if (g / "proposals").is_dir() else []:
        text = p.read_text()
        end = text.find("\n---", 4)
        if not text.startswith("---\n") or end < 0:
            raise Refuse(12, t.rel(p), "proposal frontmatter without closing ---")
        try:
            fm = parse_flat_yaml(text[4:end])
        except YamlError as e:
            raise Refuse(12, t.rel(p), f"flat-YAML violation: {e}")
        sec = _sections(text[end + 4:])
        fm["_path"], fm["_change"], fm["_delta"], fm["_text"] = t.rel(p), sec.get("Change", ""), sec.get("Delta", ""), text
        t.proposals.append(fm)
    vpath = g / "versions.json"
    if vpath.is_file():
        content = vpath.read_text()
        try:
            obj = json.loads(content)
        except json.JSONDecodeError as e:
            raise Refuse(12, "graph/versions.json", f"not JSON: {e}")
        if not isinstance(obj, dict) or "generated_hash" not in obj or not hash_ok("versions.json", content):
            raise Refuse(7, "graph/versions.json", "generated_hash missing or does not match the content: edited by hand "
                         "(delete the file to let the checker regenerate it)")
        t.versions = obj.get("nodes") or {}
    cdir = t.root / "chats"
    if cdir.is_dir():
        for p in sorted(cdir.glob("*.jsonl")):
            t.chats[p.name] = [json.loads(l) for l in p.read_text().splitlines() if l.strip()]
    if registry:
        t.registry = _load_registry(registry)
    return t


def _load_registry(path):
    """Statement-of-record classes from a CLAIMS.md: `id`, `class` per entry, read leniently."""
    out, cur = {}, None
    for line in pathlib.Path(path).read_text().splitlines():
        m = re.match(r"^\s*-?\s*id:\s*(\S+)", line)
        if m:
            cur = m.group(1).strip("`'\"")
        m = re.match(r"^\s*class:\s*(\S+)", line)
        if m and cur:
            out[cur] = m.group(1).strip("`'\"")
    return out


# ---------------------------------------------------------------- helpers
def is_human(t, handle):
    h = (t.policy.get("handles") or {}).get(handle)
    return bool(h) and h.get("kind") == "human"


def is_handle(t, handle):
    return handle in (t.policy.get("handles") or {})


def classes(t):
    return {c["id"]: c for c in (t.frame.get("classes") or []) if isinstance(c, dict)}


def roots(t):
    return [r for r in (t.frame.get("roots") or []) if isinstance(r, dict)]


def valuations(t):
    """The frame's valuation nodes: `cases` nodes read as distributions over the outcome classes."""
    return [v for v in (t.frame.get("valuations") or []) if isinstance(v, str)]


def all_roots(t):
    """Every root entry with the frame it belongs to, as dicts carrying `frame`: None for the top
    frame's roots, the frame node's id for a sub-frame's. A frame node's own roots come before the
    frame node itself, so a programme's steps are derived before the programme."""
    out, seen = [], set()

    def walk(entries, frame_id):
        for r in entries:
            if not isinstance(r, dict):
                continue
            node = t.nodes.get(r.get("id"))
            if node and node.get("kind") == "frame" and r.get("id") not in seen:
                seen.add(r["id"])
                walk(node.get("roots") or [], r["id"])
            out.append(dict(r, frame=frame_id))
    walk(roots(t), None)
    return out


def plan_children(t, x):
    """The children of a frame node that are its plan roots (its steps that are plans)."""
    n = t.nodes[x]
    plans = {r.get("id") for r in (n.get("roots") or []) if isinstance(r, dict) and r.get("role") == "plan"}
    return [c for c in n["children"] if c in plans]


def target_key(target):
    if not isinstance(target, dict):
        return None
    if "node" in target:
        return ("node", target["node"])
    if "row" in target:
        return ("row", *tuple(target["row"]))
    if "pair" in target:
        return ("pair", *tuple(sorted(target["pair"])))
    if "proposal" in target:
        return ("proposal", target["proposal"])
    if "event" in target:
        return ("event", target["event"])
    return None


def said(e, field="checked"):
    return any(isinstance(c, dict) and c.get("how") == "said" for c in (e.get(field) or []))


def q(x):
    return x if isinstance(x, Q) else Q(x)


def mid(rng):
    return (q(rng[0]) + q(rng[1])) / 2


def support(t, x, seen=None):
    seen = set() if seen is None else seen
    if x in seen or x not in t.nodes:
        return seen
    seen.add(x)
    for c in t.nodes[x]["children"]:
        support(t, c, seen)
    return seen


# ---------------------------------------------------------------- lint (§3)
def lint(t):
    """Raise Refuse on the first violated rule; return nothing. Warnings go to t.warnings."""
    fr, po, nodes = t.frame, t.policy, t.nodes
    cls = classes(t)
    handles = po.get("handles") or {}
    # rule 8: frame, classes, valuation nodes (the outside option and the undescribed failure are cases nodes)
    for c in cls.values():
        if c.get("utility") is None:
            raise Refuse(8, "graph/frame.yaml", f"class {c['id']!r} has no utility; an unplaced outcome is a valuation node, not a class")
        if not is_human(t, c.get("placed_by")):
            raise Refuse(8, "graph/frame.yaml", f"class {c['id']!r} has a utility without a human placed_by")
    vals = valuations(t)
    if not roots(t):
        raise Refuse(1, "graph/frame.yaml", "frame names no roots")
    for r in roots(t):
        if r.get("id") not in nodes:
            raise Refuse(1, "graph/frame.yaml", f"root {r.get('id')!r} resolves to no node")
    for v in vals:
        if v not in nodes or nodes[v].get("kind") != "cases":
            raise Refuse(8, "graph/frame.yaml", f"valuation {v!r} is not a cases node")
        for row in nodes[v].get("rows") or []:
            if not isinstance(row, dict) or row.get("class") not in cls:
                raise Refuse(8, nodes[v]["_path"], "every row of a valuation node names a placed outcome class")
    for key in ("outside_option", "undescribed_failure"):
        if fr.get(key) not in vals:
            raise Refuse(8, "graph/frame.yaml", f"{key} names no valuation node (a cases node listed under valuations)")
    if "subframes" in fr:
        t.warnings.append("graph/frame.yaml: the key subframes is ignored; a sub-frame is a node of kind frame listed as a plan root")
    # every frame's root entries (the top frame's in frame.yaml, a sub-frame's in its node file)
    frame_nodes = {x for x, n in nodes.items() if n.get("kind") == "frame"}
    for x in frame_nodes:
        n = nodes[x]
        if not isinstance(n.get("roots"), list) or not all(isinstance(r, dict) and isinstance(r.get("id"), str) for r in n["roots"]):
            raise Refuse(2, n["_path"], "a frame node carries roots, a list of {id, role, preset, ...} like frame.yaml's")
    entries = all_roots(t)
    seen = defaultdict(list)
    for r in entries:
        seen[r.get("id")].append(r["frame"])
        where = "graph/frame.yaml" if r["frame"] is None else nodes[r["frame"]]["_path"]
        if r.get("role") not in ROLES:
            raise Refuse(2, where, f"unknown role {r.get('role')!r}")
        if r.get("preset") not in PRESETS:
            raise Refuse(2, where, f"unknown preset {r.get('preset')!r}")
        if r.get("id") not in nodes:
            raise Refuse(1, where, f"root {r.get('id')!r} resolves to no node")
        is_frame = nodes[r["id"]].get("kind") == "frame"
        if is_frame and r["role"] != "plan":
            raise Refuse(2, where, f"a frame node ({r['id']!r}) is a root only as a plan: a programme")
        if is_frame and "success_class" in r:
            raise Refuse(8, where, f"programme root {r['id']!r} takes no success_class; its value is its best step's")
        if r["role"] == "plan" and not is_frame and "success_class" not in r:
            raise Refuse(8, where, f"plan root {r.get('id')!r} lacks success_class")
        if "success_class" in r and r["success_class"] not in cls:
            raise Refuse(8, where, f"success_class {r['success_class']!r} names no class")
        if r["preset"] != "worst-case" and "budget" not in r:
            raise Refuse(8, where, f"root {r.get('id')!r} under {r['preset']} lacks budget")
    for rid, frames in seen.items():
        if len(frames) > 1:
            raise Refuse(1, "graph/frame.yaml", f"{rid!r} is a root of more than one frame")
    for x in frame_nodes:
        if x not in seen:
            raise Refuse(2, nodes[x]["_path"], "a frame node is a plan root of the top frame or of another frame")
        kids, rids = set(nodes[x]["children"]), {r["id"] for r in nodes[x]["roots"]}
        if kids != rids:
            raise Refuse(2, nodes[x]["_path"], "a frame node's children are exactly its roots")
        if not isinstance(nodes[x].get("question"), str) or not nodes[x]["question"].strip():
            raise Refuse(2, nodes[x]["_path"], "a frame node carries question")
        if "outside_option" in nodes[x] and nodes[x]["outside_option"] not in vals:
            raise Refuse(8, nodes[x]["_path"], "a sub-frame's outside_option names a valuation node of the top frame")
    # rule 1: ids and references
    ids = set(nodes)
    for p in t.proposals:
        if p.get("id") in ids:
            raise Refuse(1, p["_path"], f"id {p['id']!r} is also a node id")
        ids.add(p.get("id"))
    for e in t.events:
        if e.get("id") in ids:
            raise Refuse(1, e["_path"], f"duplicate id {e.get('id')!r}")
        ids.add(e.get("id"))
    refs = ("hypotheses", "negation_of", "refines", "committed", "supersedes", "superseded_by")
    for n in nodes.values():
        for c in n["children"]:
            if c not in nodes:
                raise Refuse(1, n["_path"], f"child {c!r} resolves to no node")
        for k in refs:
            v = n.get(k)
            for x in (v if isinstance(v, list) else [v] if v not in (None, "none") else []):
                if x not in nodes:
                    raise Refuse(1, n["_path"], f"{k} {x!r} resolves to no node")
        for row in n["rows"] or []:
            if not isinstance(row, dict) or row.get("picture") not in nodes:
                raise Refuse(1, n["_path"], f"row picture {row.get('picture') if isinstance(row, dict) else row!r} resolves to no node")
    # cycles and parentless
    state = {}

    def visit(x, stack):
        if state.get(x) == 1:
            raise Refuse(1, nodes[x]["_path"], "children form a cycle: " + " -> ".join(stack + [x]))
        if state.get(x) == 2:
            return
        state[x] = 1
        for c in nodes[x]["children"]:
            visit(c, stack + [x])
        state[x] = 2
    for x in nodes:
        visit(x, [])
    has_parent = {c for n in nodes.values() for c in n["children"]}
    root_ids = {r["id"] for r in roots(t)} | set(vals)
    parentless = {x for x in nodes if x not in has_parent and not nodes[x].get("superseded_by")}
    if parentless != root_ids:
        raise Refuse(1, "graph/frame.yaml", f"parentless nodes {sorted(parentless)} differ from the frame's roots and valuation nodes {sorted(root_ids)}")
    # rule 2 and 4 per node, rule 3, rule 12 sentences
    plan_support = set()
    for r in entries:
        if r["role"] == "plan":
            plan_support |= support(t, r["id"])
    words = [str(w).casefold() for w in (po.get("evaluative_words") or [])]
    for x, n in nodes.items():
        path = n["_path"]
        for k in n:
            if k in FORBIDDEN_KEYS:
                raise Refuse(4, path, f"node file carries the key {k!r}; levels and numbers are derived")
        for row in n["rows"] or []:
            for k in row:
                if k in FORBIDDEN_KEYS:
                    raise Refuse(4, path, f"row carries the key {k!r}")
        kind = n.get("kind")
        if kind not in KINDS:
            raise Refuse(2, path, f"unknown kind {kind!r}")
        if not is_handle(t, n.get("author")):
            raise Refuse(2, path, f"author {n.get('author')!r} is not a handle in policy.yaml")
        if n.get("size") not in ("S", "M", "L") or not n.get("size_reason"):
            raise Refuse(2, path, "size must be S, M or L with a size_reason")
        if not isinstance(n.get("version"), int) or n["version"] < 1:
            raise Refuse(2, path, "version must be a positive integer")
        kids = [nodes[c] for c in n["children"]]
        if kind == "leaf":
            if n["children"]:
                raise Refuse(2, path, "a leaf has no children")
            lk = n.get("leaf_kind")
            if lk not in LEAF_KINDS:
                raise Refuse(2, path, f"unknown leaf_kind {lk!r}")
            if lk == "hypothesis" and n.get("discharge") not in DISCHARGES:
                raise Refuse(2, path, "a hypothesis carries discharge")
            if lk == "record" and not n.get("statement_of_record"):
                raise Refuse(2, path, "a record carries statement_of_record")
            if lk in ("bridge", "assumption") and "attribution" in n and n["attribution"] not in ATTRIBUTIONS:
                raise Refuse(2, path, f"unknown attribution {n['attribution']!r}")
        else:
            if "leaf_kind" in n:
                raise Refuse(2, path, "only a leaf carries leaf_kind")
            if not n["children"]:
                raise Refuse(2, path, f"an {kind} node has children")
        if kind == "and":
            comp = [k for k in kids if k.get("leaf_kind") == "completeness"]
            if len(comp) != 1:
                raise Refuse(2, path, "an and has exactly one completeness child")
            if any(k.get("leaf_kind") == "record" for k in kids):
                br = [k for k in kids if k.get("leaf_kind") == "bridge"]
                if len(br) != 1 or "attribution" not in br[0]:
                    raise Refuse(2, path, "a formal result has exactly one bridge child with attribution")
        if kind == "cases":
            part = [k for k in kids if k.get("leaf_kind") == "partition"]
            if len(part) != 1:
                raise Refuse(2, path, "a cases node has exactly one partition child")
            rows = n["rows"] or []
            pics = {k["id"] for k in kids if k.get("leaf_kind") == "picture"}
            rowpics = [r["picture"] for r in rows]
            if set(rowpics) != pics or len(rowpics) != len(set(rowpics)):
                raise Refuse(2, path, "every row's picture is a child picture leaf and every picture child is a row")
            if len({k["id"] for k in kids}) != len(pics) + 1:
                raise Refuse(2, path, "a cases node's children are its partition leaf and its pictures")
            if sum(1 for r in rows if r.get("residual") is True) != 1:
                raise Refuse(2, path, "exactly one row is residual: true")
            for r in rows:
                if r.get("class") is not None and r["class"] not in cls and r["class"] not in vals:
                    raise Refuse(10, path, f"row class {r['class']!r} names no class or valuation node")
        if kind == "frame":
            for k in ("rows", "leaf_kind", "decided_at", "committed"):
                if n.get(k):
                    raise Refuse(2, path, f"a frame node carries no {k}")
        if kind == "choose":
            if x not in plan_support:
                raise Refuse(2, path, "a choose lies only in a plan root's support closure")
            if n.get("decided_at") not in ("commit", "runtime"):
                raise Refuse(2, path, "a choose carries decided_at (commit | runtime)")
            if n.get("committed", "none") != "none" and n["committed"] not in n["children"]:
                raise Refuse(1, path, "committed names no child")
        st = n["_statement"]
        if not re.search(r"[.?!]", st) or not st.strip():
            raise Refuse(3, path, "Statement has no sentence")
        toks = set(re.findall(r"[a-z]+", st.casefold()))
        bad = sorted(toks & set(words))
        if bad:
            raise Refuse(3, path, f"Statement uses evaluative words {bad}")
        # versions
        norm = normalize_statement(st)
        hist = t.versions.get(x) or []
        if hist:
            last = hist[-1]
            if norm != last["normalized"] and n["version"] <= last["version"]:
                raise Refuse(4, path, "Statement changed without a version bump")
            if norm == last["normalized"] and n["version"] != last["version"]:
                raise Refuse(4, path, "version bumped with an unchanged Statement")
    # rule 5, 6, 10: ledgers
    nodeset = set(nodes)
    maint = po.get("maintainer")
    if not is_human(t, maint):
        raise Refuse(5, "graph/policy.yaml", "maintainer must name a human handle (rule and survey events are the maintainer's)")
    by_ledger = defaultdict(list)
    eids = {e.get("id"): e for e in t.events}
    for e in t.events:
        path = e["_path"]
        for k in ("id", "by", "date", "rule", "via", "kind", "target", "version"):
            if k not in e:
                raise Refuse(5, path, f"event lacks {k!r}")
        if not is_handle(t, e["by"]):
            raise Refuse(5, path, f"by {e['by']!r} is not a mapped handle")
        if e["_ledger"] != e["by"].lstrip("@"):
            raise Refuse(5, path, f"ledger file is not named for {e['by']!r}")
        _lh = str(e["_ledger"])
        if not (str(e["id"]).startswith(_lh + "-") and len(str(e["id"])) > len(_lh) + 1
                and re.fullmatch(r"[A-Za-z0-9_.-]+", str(e["id"])[len(_lh) + 1:])):
            raise Refuse(5, path, f"event id {e['id']!r} must be '<handle>-<suffix>' with the handle of its ledger ({e['_ledger']}-...)")
        if not _RULE_VERSION.match(str(e["rule"])):
            raise Refuse(5, path, f"rule {e['rule']!r} is not an anchor-rules version 'YYYY-MM-DD.n'")
        if e["kind"] not in EVENT_KINDS:
            raise Refuse(2, path, f"unknown event kind {e['kind']!r}")
        if e["via"] not in VIAS:
            raise Refuse(2, path, f"unknown via {e['via']!r}")
        if e.get("dimension", "both") not in DIMENSIONS:
            raise Refuse(2, path, f"unknown dimension {e.get('dimension')!r}")
        for f in ("checked", "not_checked"):
            for c in e.get(f) or []:
                if not isinstance(c, dict) or c.get("how") not in HOWS:
                    raise Refuse(2, path, f"unknown how in {f}")
        tk = target_key(e["target"])
        if tk is None:
            raise Refuse(2, path, "unknown target form")
        if tk[0] == "node" and tk[1] not in nodeset:
            raise Refuse(1, path, f"target node {tk[1]!r} resolves to no node")
        if tk[0] == "row":
            cnode = nodes.get(tk[1])
            if not cnode or cnode.get("kind") != "cases" or tk[2] not in [r["picture"] for r in cnode["rows"]]:
                raise Refuse(1, path, f"target row {list(tk[1:])} resolves to no row")
            row = next(r for r in cnode["rows"] if r["picture"] == tk[2])
            if e["target"].get("field") == "w" and row.get("residual") is True:
                raise Refuse(10, path, "the residual row's weight is derived, not judged")
        if tk[0] == "pair" and not set(tk[1:]) <= nodeset:
            raise Refuse(1, path, f"target pair {list(tk[1:])} resolves to no nodes")
        if tk[0] == "proposal" and tk[1] not in {p.get("id") for p in t.proposals}:
            raise Refuse(1, path, f"target proposal {tk[1]!r} resolves to no proposal")
        if tk[0] == "event" and tk[1] not in eids:
            raise Refuse(1, path, f"target event {tk[1]!r} resolves to no event")
        if e["kind"] in LEVEL_KINDS and not (e.get("checked") and e.get("not_checked")):
            raise Refuse(5, path, "a level-minting event has non-empty checked and not_checked")
        if e["kind"] == "withdraw" and (tk[0] != "event" or eids[tk[1]]["by"] != e["by"]):
            raise Refuse(5, path, "withdraw names an event by the same handle")
        if e["kind"] in ("rule", "survey") and e["by"] != maint:
            raise Refuse(5, path, f"{e['kind']} is by the maintainer")
        if not is_human(t, e["by"]):
            # an AI handle may write estimates and gestalts (they count at J 0 "generated", with its reasoning in gloss);
            # it mints no level and accepts, approves, tags or identifies nothing
            if e["kind"] in LEVEL_KINDS | {"external", "retrospective", "attribution"}:
                raise Refuse(5, path, "an AI handle mints no vettedness level (levels record who has read what)")
            if e["kind"] in JUDGMENT_KINDS - {"estimate", "gestalt"}:
                raise Refuse(5, path, f"an AI handle writes no {e['kind']}: acceptance and tagging are a human's")
            if e["kind"] in ("estimate", "gestalt") and not str(e.get("gloss") or "").strip():
                raise Refuse(5, path, "an AI handle's judgment carries its reasoning in gloss")
        if e["kind"] == "gestalt" and e.get("derived") is not False:
            raise Refuse(5, path, "a gestalt carries derived: false (a holistic judgment, not a derived number)")
        if e["kind"] == "external" and not e.get("ref"):
            raise Refuse(5, path, "an external event carries ref, the pointer to the outside record")
        if e["kind"] == "audit":
            if tk[0] != "event" or not is_human(t, e["by"]):
                raise Refuse(5, path, "an audit is by a human handle and names the audited event in target.event")
            if e.get("verdict") not in AUDIT_VERDICTS:
                raise Refuse(5, path, "an audit carries verdict: agree | disagree")
        if e["kind"] == "attribution":
            # the only event that clears the attribution-unvetted flag: a human other than the node's author
            # says whether the attribution is honest (vouched) or not (disputed), pointing at what they read
            if tk[0] != "node" or not is_human(t, e["by"]):
                raise Refuse(5, path, "an attribution event is by a human handle and targets a node")
            if e["by"] == nodes[tk[1]].get("author"):
                raise Refuse(5, path, "an attribution event is by a human other than the node's author")
            if e.get("verdict") not in ATTRIBUTION_VERDICTS:
                raise Refuse(5, path, "an attribution event carries verdict: vouched | disputed")
            if not e.get("ref"):
                raise Refuse(5, path, "an attribution event carries ref, what the attribution was checked against")
        if e["kind"] == "rule" and "rows" in e:
            # a ruling on a table's weights and conditionals: the maintainer's J 8 judgments, one event for every row
            cnode = nodes.get(tk[1]) if tk[0] == "node" else None
            if not cnode or cnode.get("kind") != "cases" or not isinstance(e["rows"], dict):
                raise Refuse(5, path, "a rule with rows targets a cases node and maps its pictures to {w, p} ranges")
            rowmap = {r["picture"]: r for r in cnode["rows"]}
            for pic, fields in e["rows"].items():
                if pic not in rowmap or not isinstance(fields, dict) or not set(fields) <= {"w", "p"}:
                    raise Refuse(5, path, f"rule rows: {pic!r} is not a row of {tk[1]!r} with w and p only")
                if "w" in fields and rowmap[pic].get("residual") is True:
                    raise Refuse(10, path, "the residual row's weight is derived, not ruled")
                for f, rng in fields.items():
                    if not isinstance(rng, list) or len(rng) != 2 or not all(isinstance(v, (int, Q)) for v in rng) or not (0 <= q(rng[0]) <= q(rng[1]) <= 1):
                        raise Refuse(10, path, f"rule rows: {pic}.{f} is a range [lo, hi] inside [0, 1]")
        est = e.get("estimate")
        if isinstance(est, list):
            if len(est) != 2 or not all(isinstance(v, (int, Q)) for v in est) or not (0 <= q(est[0]) <= q(est[1]) <= 1):
                raise Refuse(10, path, "a range is [lo, hi] inside [0, 1] with lo <= hi")
        if e["kind"] == "classify" and est not in cls and est not in vals:
            raise Refuse(10, path, f"class tag {est!r} names no class or valuation node")
        if ("question" in e) != ("answer" in e):
            raise Refuse(6, path, "question and answer come together")
        if "question" in e:
            _check_turns(t, e)
        by_ledger[e["_ledger"]].append(e)
    for led, evs in by_ledger.items():
        for a, b in zip(evs, evs[1:]):
            if str(b["date"]) < str(a["date"]):
                raise Refuse(5, b["_path"], "dates within a ledger are non-decreasing")
    # rule 10: weights at midpoints (estimates and ruled weights alike)
    for x, n in nodes.items():
        if n.get("kind") == "cases":
            tot = Q(0)
            for r in n["rows"]:
                if r.get("residual"):
                    continue
                ws = [e["estimate"] for e in t.events if e["kind"] == "estimate" and target_key(e["target"]) == ("row", x, r["picture"]) and e["target"].get("field") == "w"]
                ws += [e["rows"][r["picture"]]["w"] for e in t.events if e["kind"] == "rule" and target_key(e["target"]) == ("node", x)
                       and "w" in (e.get("rows") or {}).get(r["picture"], {})]
                if ws:
                    tot += mid(ws[-1])
            if tot > 1:
                raise Refuse(10, n["_path"], f"non-residual weights' midpoints sum to {tot} > 1")
    # rule 9 and 2: proposals
    approvals = {target_key(e["target"])[1] for e in t.events if e["kind"] == "approve" and e.get("estimate") == "accept"
                 and target_key(e["target"])[0] == "proposal"}
    for p in t.proposals:
        if p.get("kind") not in PROPOSAL_KINDS:
            raise Refuse(2, p["_path"], f"unknown proposal kind {p.get('kind')!r}")
        if p.get("status") not in PROPOSAL_STATUS:
            raise Refuse(2, p["_path"], f"unknown proposal status {p.get('status')!r}")
        if p["status"] in ("approved", "applied") and p["id"] not in approvals:
            raise Refuse(9, p["_path"], f"status {p['status']} without a counted approve event")
        for op in p.get("ops") or []:
            for k in ("cases", "parent", "node", "from", "to"):
                if k in op and op[k] not in nodes:
                    raise Refuse(9, p["_path"], f"op names missing node {op[k]!r}")
            if op.get("op") == "split-row":
                cn = nodes.get(op.get("cases"))
                if not cn or op.get("row") not in [r["picture"] for r in cn.get("rows") or []]:
                    raise Refuse(9, p["_path"], f"op names missing row {op.get('row')!r}")
    # rule 11: chats changed after their commit
    cdir = t.root / "chats"
    if t.chats:
        try:
            top = subprocess.run(["git", "-C", str(t.root), "rev-parse", "--show-toplevel"], capture_output=True, text=True)
            if top.returncode != 0:
                t.warnings.append("chats/: not a git checkout; the changed-after-commit rule is unchecked")
            else:
                for name in t.chats:
                    log = subprocess.run(["git", "-C", str(t.root), "log", "--format=%H", "--", str(cdir / name)], capture_output=True, text=True)
                    if len(log.stdout.split()) > 1:
                        raise Refuse(11, f"chats/{name}", "chat file changed after the commit that added it")
        except FileNotFoundError:
            t.warnings.append("chats/: git not found; the changed-after-commit rule is unchecked")
    # rule 7: generated files
    for name in GENERATED:
        p = t.graph / name
        if p.is_file():
            if not hash_ok(name, p.read_text()):
                raise Refuse(7, f"graph/{name}", "generated_hash does not match the content: edited by hand")


def _check_turns(t, e):
    def turn(ref):
        m = re.match(r"^chats/([^#]+)#t(\d+)$", str(ref))
        if not m or m.group(1) not in t.chats:
            raise Refuse(6, e["_path"], f"{ref!r} resolves to no chat turn")
        turns = t.chats[m.group(1)]
        i = int(m.group(2))
        if not 1 <= i <= len(turns):
            raise Refuse(6, e["_path"], f"{ref!r} resolves to no chat turn")
        return m.group(1), turns[i - 1]
    f1, _ = turn(e["question"])
    f2, ans = turn(e["answer"])
    if f1 != f2:
        raise Refuse(6, e["_path"], "question and answer are turns of one file")
    text = " ".join(str(ans.get("text") or ans.get("content") or "").split()).casefold()
    if " ".join(str(e.get("verbatim", "")).split()).casefold() not in text:
        raise Refuse(6, e["_path"], "verbatim does not occur in the answer turn")


def hash_ok(name, content):
    if name.endswith(".json"):
        try:
            obj = json.loads(content)
        except json.JSONDecodeError:
            return False
        h = obj.pop("generated_hash", None)
        obj["generated_hash"] = ""
        return h == sha(json.dumps(obj, indent=1, sort_keys=True))
    m = re.search(r"\n<!-- generated_hash: ([0-9a-f]+) -->\n?$", content)
    return bool(m) and m.group(1) == sha(content[:m.start() + 1])


# ---------------------------------------------------------------- derivations (§4)
class Ctx:
    """Everything `derive` computes, keyed by node or root id; see derive.__doc__."""

    def __init__(self, t):
        self.t = t
        self.fr, self.po = t.frame, t.policy
        self.cls = classes(t)
        # every root of every frame, a sub-frame's steps before the sub-frame itself; `frame` names the frame
        self.roots = {r["id"]: r for r in all_roots(t)}
        self.frames = [x for x, n in t.nodes.items() if n.get("kind") == "frame"]
        self.rates = self.po.get("rate_table") or {}
        self.floor = sorted((int(k), q(v)) for k, v in (self.po.get("floor_table") or {}).items())
        self.est_level = int(self.fr.get("establishment_level", 8))
        self.bar = q(self.fr.get("bar", Q(1, 2)))
        self.valuations = set(valuations(t))
        self.outside = self.fr.get("outside_option")             # a valuation node: the default trajectory
        self.undescribed = self.fr.get("undescribed_failure")    # a valuation node: failure nobody has described
        self.val = {}                                            # valuation node -> {mid, lo, hi, defined}, by valuation_values()


def floor_width(C, lvl):
    if lvl < 6:
        return Q(1)
    pts = C.floor
    for (k0, w0), (k1, w1) in zip(pts, pts[1:]):
        if k0 <= lvl <= k1:
            return w0 + (w1 - w0) * Q(lvl - k0, k1 - k0)
    return pts[-1][1] if lvl >= pts[-1][0] else Q(1)


def rate(C, kind, size):
    row = C.rates.get(kind) or {}
    return q(row.get(size, 0)), f"{kind}[{size}]={row.get(size, '?')}{' prior' if row.get('prior') else ''}"


def utility(C, cid, mode="mid"):
    """Utility of a class, or the value of a valuation node (a cases node read as a distribution over
    the classes): mid, or the lo/hi end of its interval. A valuation node with no belief reads as 0 with
    the whole scale as interval; a `provisional` class or node widens its interval to the whole scale."""
    if cid in C.valuations:
        v = C.val.get(cid)
        if not v or not v["defined"]:
            return {"mid": Q(0), "lo": Q(-1), "hi": Q(1)}[mode]
        if C.t.nodes[cid].get("provisional") and mode != "mid":
            return Q(-1) if mode == "lo" else Q(1)
        return v[mode]
    c = C.cls.get(cid) or {}
    u = c.get("utility")
    if u is None:
        return {"mid": Q(0), "lo": Q(-1), "hi": Q(1)}[mode]
    if isinstance(u, list):
        return {"mid": mid(u), "lo": q(u[0]), "hi": q(u[1])}[mode]
    if c.get("provisional") and mode != "mid":
        return Q(-1) if mode == "lo" else Q(1)
    return q(u)


def valuation_values(C):
    """The value of each valuation node: Σ w·p·U(class) over its admitted rows, renormalized by Σ w·p
    (the mass the rows describe), weights at midpoints; lo and hi at the conditionals' and utilities'
    ends. With equal weights and conditional 1 on every row this is the mean of the classes' utilities.
    Undefined (no belief) when the node has no admitted row, a row lacks a weight or conditional, or the
    described mass is zero. Computed after judgments(); the rows name placed classes only (rule 8)."""
    for x in C.valuations:
        rb = row_beliefs(C, x)
        if not rb or any("no belief" in b["p"][2] or "no belief" in b["w"][2] for b in rb.values()):
            C.val[x] = {"defined": False}
            continue
        out = {"defined": True}
        for mode in ("mid", "lo", "hi"):
            num, den = Q(0), Q(0)
            for b in rb.values():
                w = b["w"][0]
                p = {"mid": b["p"][0], "lo": max(Q(0), b["p"][0] - b["p"][1] / 2), "hi": min(Q(1), b["p"][0] + b["p"][1] / 2)}[mode]
                num += w * p * utility(C, b["class"], mode)
                den += w * p
            if den == 0:
                out = {"defined": False}
                break
            out[mode] = num / den
        C.val[x] = out


def resolve_events(C):
    t = C.t
    withdrawn = {target_key(e["target"])[1] for e in t.events if e["kind"] == "withdraw"}
    C.stale_reason = {}
    for e in sorted(t.events, key=lambda e: str(e["date"])):
        tk = target_key(e["target"])
        node = tk[1] if tk[0] == "node" else tk[2] if tk[0] == "row" else None
        if e["id"] in withdrawn:
            e["_status"] = "withdrawn"
        elif node and e["version"] < t.nodes[node]["version"]:
            e["_status"] = "stale"
            C.stale_reason[e["id"]] = f"given against version {e['version']}, now {t.nodes[node]['version']}"
        elif tk[0] == "node" and e["kind"] == "estimate" and t.nodes[node].get("kind") == "cases":
            # a leaf range given before the leaf became a table: kept as a suggestion, never used (§2)
            e["_status"] = "stale"
            C.stale_reason[e["id"]] = STALE_TABLE
        else:
            e["_status"] = "counted"
    C.counted = [e for e in sorted(t.events, key=lambda e: str(e["date"])) if e["_status"] != "withdrawn"]
    # a counted rule with rows is the maintainer's judgment on every row it names: expanded into J 8
    # estimates (the ruling cited is their reason) that also admit the rows; the rule line itself stays
    for e in list(C.counted):
        if e["kind"] == "rule" and e["_status"] == "counted" and isinstance(e.get("rows"), dict):
            x = target_key(e["target"])[1]
            for pic, fields in e["rows"].items():
                for f, rng in fields.items():
                    C.counted.append({"id": e["id"], "by": e["by"], "date": e["date"], "rule": e["rule"], "via": e["via"],
                                      "kind": "estimate", "target": {"row": [x, pic], "field": f}, "version": e["version"],
                                      "estimate": rng, "reason": e.get("reason") or e.get("ref") or "ruled",
                                      "_status": "counted", "_from_rule": e["id"], "_path": e["_path"], "_ledger": e["_ledger"], "_seq": e["_seq"]})
    C.counted.sort(key=lambda e: (str(e["date"]), e.get("_seq", 0)))   # latest-wins reads ledger order within a day
    C.on_node = defaultdict(list)
    for e in C.counted:
        tk = target_key(e["target"])
        if tk[0] == "node":
            C.on_node[tk[1]].append(e)
    # audits: per auditor, how many re-performed checks agreed and disagreed (calibration data; no number moves)
    C.audits = defaultdict(lambda: {"agree": 0, "disagree": 0, "self": 0, "cross": 0})
    by_id = {e["id"]: e for e in t.events}
    for e in C.counted:
        if e["kind"] == "audit":
            a = C.audits[e["by"]]
            a[e["verdict"]] += 1
            a["self" if by_id[target_key(e["target"])[1]]["by"] == e["by"] else "cross"] += 1


def admission(C):
    t = C.t
    C.admitted, C.row_class = {}, {}
    for x, n in t.nodes.items():
        if n.get("kind") != "cases":
            continue
        for row in n["rows"]:
            key = (x, row["picture"])
            evs = [e for e in C.counted if target_key(e["target"]) == ("row",) + key]
            ok = is_human(t, t.nodes[row["picture"]].get("author")) or any(
                (e["kind"] == "admit" and e.get("estimate") == "accept" and is_human(t, e["by"])) or e.get("_from_rule") for e in evs)
            C.admitted[key] = ok
            tags = [e for e in evs if e["kind"] == "classify"]
            # a residual row's failure is valued at the frame's undescribed-failure node unless the row names a class
            C.row_class[key] = tags[-1]["estimate"] if tags else row.get("class") or (C.undescribed if row.get("residual") else None)


def levels(C):
    t = C.t
    C.V, C.flags = {}, defaultdict(set)
    maint = C.po.get("maintainer")
    for x, n in t.nodes.items():
        evs = C.on_node[x]
        for e in evs:
            if e["_status"] == "stale":
                C.flags[x].add("stale" if C.stale_reason.get(e["id"]) != STALE_TABLE else f"stale: {STALE_TABLE}")
        if any(e["_status"] == "withdrawn" and target_key(e["target"]) == ("node", x) for e in t.events):
            C.flags[x].add("withdrawn")
        V, display = {}, {}
        for dim in ("valid", "ref"):
            de = [e for e in evs if e.get("dimension", "both") in (dim, "both")]
            if n.get("leaf_kind") == "hypothesis" and n.get("discharge") == "restates-conclusion":
                V[dim] = 0
                continue
            v = 2
            if dim == "valid" and n.get("leaf_kind") == "record":
                if t.registry is None:
                    C.flags[x].add("registry unchecked")   # anchor 4 needs --registry <CLAIMS.md>; the record caps at 2
                elif t.registry.get(str(n.get("statement_of_record"))) in ("lean-proved", "enumeration-verified", "witness-checked"):
                    v = 4
            traces = [e for e in de if e["kind"] == "trace" and said(e)]
            complete = [e for e in traces if not e.get("installment") or e["installment"].get("done", 0) >= e["installment"].get("of", 1)]
            tracers = [e["by"] for e in complete if e["by"] != n.get("author") and is_human(t, e["by"])]
            pics = [p for p in support(t, x) if t.nodes[p].get("leaf_kind") == "picture" and any(
                C.admitted.get((c, p)) for c in t.nodes if (c, p) in C.admitted)]
            passes = [e for e in de if e["kind"] == "pass" and e["by"] != n.get("author") and all(
                any(p in str(c.get("item", "")) for c in e.get("checked") or []) for p in pics)]
            # anchor 14: an external record logged by a human other than the node's author (10 and above need another logger)
            externals = [e for e in de if e["kind"] == "external" and is_human(t, e["by"]) and e["by"] != n.get("author")]
            anchors = {6: any(e["kind"] == "map-read" and said(e) for e in de), 8: bool(complete),
                       10: len(set(tracers)) >= 2, 12: bool(passes),
                       14: bool(externals), 16: any(e["kind"] == "retrospective" for e in de),
                       18: any(e["kind"] == "survey" and e["by"] == maint for e in de)}
            for k in (6, 8, 10, 12, 14, 16, 18):
                if anchors[k]:
                    v = k
                else:
                    break
            V[dim] = v
            if v == 6 and traces and not complete:
                ins = traces[-1]["installment"]
                display[dim] = f"6–8 ({ins.get('done', 0)}/{ins.get('of', '?')})"
        head = min(V.values())
        weaker = "both" if V["valid"] == V["ref"] else min(V, key=V.get)
        C.V[x] = {"valid": V["valid"], "ref": V["ref"], "headline": head, "weaker": weaker,
                  "display": display.get(weaker if weaker != "both" else "valid", str(head))}
        if n.get("leaf_kind") == "bridge" or n.get("attribution") == "reconstructed":
            # cleared only by a counted `attribution` event from a human other than the author (rule 5 checks the
            # shape); the latest verdict shows: vouched clears, disputed clears and flags the dispute
            attr = [e for e in evs if e["kind"] == "attribution" and is_human(t, e["by"]) and e["by"] != n.get("author")]
            if not attr:
                C.flags[x].add("attribution unvetted")
            elif attr[-1].get("verdict") == "disputed":
                C.flags[x].add(f"attribution disputed ({attr[-1]['by']})")


def judgments(C):
    """Beliefs per (target key, field): J, midpoint, width, displayed range, signers."""
    t = C.t
    groups = defaultdict(dict)
    for e in C.counted:
        is_range_on_read = e["kind"] in LEVEL_KINDS and isinstance(e.get("estimate"), list)
        if e["kind"] not in ("estimate", "gestalt", "classify", "identify") and not is_range_on_read:
            continue
        tk = target_key(e["target"])
        if tk[0] == "node" and e["kind"] != "gestalt" and t.nodes[tk[1]].get("kind") == "cases":
            continue   # a leaf range on a table: its probability is Σ w·p (the range is kept as a suggestion only)
        field = e["target"].get("field") or {"gestalt": "gestalt", "classify": "class", "identify": "pair"}.get(e["kind"], "range")
        groups[(tk, field)][e["by"]] = e
    passed = {x for x, evs in C.on_node.items() if any(e["kind"] == "pass" and is_human(t, e["by"]) for e in evs)}
    C.bel, C.reconcile = {}, []
    for (tk, field), per in groups.items():
        if field in ("class", "pair"):
            C.bel[(tk, field)] = {"value": list(per.values())[-1].get("estimate"), "by": sorted(per)}
            continue
        node = tk[1] if tk[0] == "node" else tk[2]
        js = []
        for by, e in per.items():
            if not isinstance(e.get("estimate"), list):
                continue
            if not is_human(t, by):
                js.append((0, q(e["estimate"][0]), q(e["estimate"][1]), by))   # J 0 "generated": an AI's number
                continue
            read = any(r["kind"] in ("map-read", "trace") and r["by"] == by and said(r) for r in C.on_node[node])
            js.append((8 if (e.get("reason") or read) else 6, q(e["estimate"][0]), q(e["estimate"][1]), by))
        if not js:
            continue
        flags = set()
        # a human judgment on the quantity supersedes every AI judgment on it; the AI events stay as history
        humans, ai = [j for j in js if j[0] > 0], [j for j in js if j[0] == 0]
        use = humans or ai
        if not humans:
            flags.add("generated")
        if len(use) == 1:
            J, lo, hi, _ = use[0]
            m = (lo + hi) / 2
        else:
            lo, hi = min(j[1] for j in use), max(j[2] for j in use)
            if max(j[1] for j in use) <= min(j[2] for j in use) and all(j[0] >= 8 for j in use):
                J, m = 10, sum((j[1] + j[2]) / 2 for j in use) / len(use)
            else:
                J, m = min(j[0] for j in use), sum((j[1] + j[2]) / 2 for j in use) / len(use)
                if humans and max(j[1] for j in use) > min(j[2] for j in use):
                    flags.add("disagreement")
                    C.reconcile.append((tk, field))
        if node in passed and humans:
            J = max(J, 12)
        if J == 6:
            flags.add("unread-weighted")
        # a gestalt is a holistic judgment on the whole root: its width follows the judgment ladder alone,
        # not the root's vettedness, which measures how far the derivation below it has been checked
        lvl = J if field == "gestalt" else min(C.V[node]["headline"], J)
        width = max(floor_width(C, lvl), hi - lo) if lvl >= 6 else Q(1)
        C.bel[(tk, field)] = {"J": J, "mid": m, "width": width, "range": [max(Q(0), m - width / 2), min(Q(1), m + width / 2)],
                              "flags": sorted(flags), "by": sorted(j[3] for j in use), "level": lvl,
                              "generated": not humans, "superseded_ai": sorted(j[3] for j in ai) if humans else []}
        if J == 6:
            C.flags[node].add("unread-weighted")
        if not humans:
            C.flags[node].add("AI number")
            if tk[0] == "row":
                C.flags[tk[1]].add("AI number")   # the table the unit targets, as well as the picture


def row_beliefs(C, x):
    """Per admitted row of a cases node: w and p as (mid, width, flags); the residual weight is the remainder."""
    t = C.t
    out, tot_w, tot_width, missing = {}, Q(0), Q(0), []
    rows = [r for r in t.nodes[x]["rows"] if C.admitted[(x, r["picture"])]]
    for r in rows:
        key = ("row", x, r["picture"])
        p = C.bel.get((key, "p"))
        w = C.bel.get((key, "w"))
        out[r["picture"]] = {"p": (p["mid"], p["width"], ["AI number"] if p.get("generated") else []) if p else (Q(1, 2), Q(1), ["no belief"]),
                             "class": C.row_class[(x, r["picture"])], "residual": bool(r.get("residual"))}
        if r.get("residual"):
            continue
        if w:
            out[r["picture"]]["w"] = (w["mid"], w["width"], ["AI number"] if w.get("generated") else [])
            tot_w, tot_width = tot_w + w["mid"], tot_width + w["width"]
        else:
            missing.append(r["picture"])
    rest = max(Q(0), 1 - tot_w)
    share = rest / (len(missing) + 1)
    for pic in missing:
        out[pic]["w"] = (share, Q(1), ["no belief"])
    for r in rows:
        if r.get("residual"):
            out[r["picture"]]["w"] = (share if missing else rest, min(Q(1), tot_width), ["no belief"] if missing else [])
    return out


def statuses(C, forced=frozenset(), forced_est=frozenset()):
    """Status per node, bottom-up: (status, diagnosis). Nodes in `forced` are conceded, in `forced_est` established."""
    t = C.t
    memo = {}

    def st(x):
        if x in memo:
            return memo[x]
        n = t.nodes[x]
        kind = n.get("kind")
        res = ("open", None)
        if x in forced:
            res = ("conceded", "forced")
        elif x in forced_est:
            res = ("established", None)
        elif kind == "leaf":
            neg = n.get("negation_of")
            if n.get("leaf_kind") == "question":
                res = ("open", None)
            elif neg and st(neg)[0] == "established":
                res = ("conceded", neg)
            elif C.V[x]["headline"] >= C.est_level:
                res = ("established", None)
        elif kind == "cases":
            part = next(c for c in n["children"] if t.nodes[c].get("leaf_kind") == "partition")
            rb = row_beliefs(C, x)
            below8 = [p for p, b in rb.items() if b["p"][0] < C.bar and (C.bel.get((("row", x, p), "p")) or {}).get("J", 0) >= 8]
            below = [p for p, b in rb.items() if b["p"][0] < C.bar and (("row", x, p), "p") in C.bel]
            if st(part)[0] == "conceded":
                res = ("conceded", part)
            elif below8:
                res = ("conceded", below8[0])
            elif C.V[x]["headline"] >= C.est_level and not below:
                res = ("established", None)
        elif kind in ("and", "or", "choose", "frame"):
            kids = n["children"]
            if kind == "choose" and n.get("committed", "none") != "none":
                kids = [n["committed"]]
            if kind == "frame":
                kids = plan_children(t, x)   # a programme reads as an or over its plan steps; its shared claims enter through them
            ks = [(c, st(c)[0]) for c in kids]
            if kind == "and":
                bad = [c for c, s in ks if s == "conceded"]
                res = ("conceded", bad[0]) if bad else ("established", None) if all(s == "established" for _, s in ks) else ("open", None)
            else:
                res = ("established", None) if any(s == "established" for _, s in ks) else (
                    "conceded", ks[0][0]) if ks and all(s == "conceded" for _, s in ks) else ("open", None)
        memo[x] = res
        return res
    for x in t.nodes:
        st(x)
    return memo


def revival(C, x, status):
    """Revival minutes of a conceded node: revive at its size, or the trace of a refining picture."""
    t = C.t
    n = t.nodes[x]
    s, diag = status[x]
    if s != "conceded":
        return None
    if n.get("kind") == "cases" and diag in t.nodes:
        ref = [c for c in n["children"] if t.nodes[c].get("refines") == diag]
        if ref:
            return rate(C, "trace", t.nodes[ref[0]]["size"])
    if n.get("kind") in ("and", "or", "choose", "frame") and diag in t.nodes and diag != "forced":
        return revival(C, diag, status)
    return rate(C, "revive", n["size"])


def revive_target(C, x, status):
    """The table a conceded node's revival argues: follow the diagnosis chain to the conceding cases node
    (or the leaf conceded by its negation partner); None when the chain ends elsewhere."""
    t = C.t
    seen = set()
    while x in t.nodes and x not in seen:
        seen.add(x)
        s, diag = status[x]
        if s != "conceded":
            return None
        n = t.nodes[x]
        if n.get("kind") == "cases":
            return x
        if n.get("kind") == "leaf":
            return x
        if diag in t.nodes:
            x = diag
            continue
        return None
    return None


def elem_cost(C, x, status):
    t = C.t
    n = t.nodes[x]
    s = status[x][0]
    if s == "established":
        return Q(0), ["established"]
    if n.get("leaf_kind") == "question":
        return INF, ["question"]
    if s == "conceded":
        m, why = revival(C, x, status)
        return m, [why]
    if C.V[x]["headline"] >= 6:
        m, why = rate(C, "trace", n["size"])
        return m, [why]
    m1, w1 = rate(C, "map-read", n["size"])
    m2, w2 = rate(C, "trace", n["size"])
    return m1 + m2, [w1, w2]


def proof_alternatives(C, x, choice):
    """Every candidate proof set of x (a frozenset of leaves and cases nodes), choices at or/choose."""
    t = C.t
    n = t.nodes[x]
    kind = n.get("kind")
    if kind == "leaf":
        return [frozenset([x])]
    if kind == "cases":
        part = next(c for c in n["children"] if t.nodes[c].get("leaf_kind") == "partition")
        return [frozenset([x, part])]
    if kind == "and":
        alts = [frozenset()]
        for c in n["children"]:
            alts = [a | b for a in alts for b in proof_alternatives(C, c, choice)][:512]
        return alts
    kids = n["children"]
    if kind == "choose":
        pick = choice.get(x) or (n.get("committed") if n.get("committed", "none") != "none" else None)
        if pick:
            kids = [pick]
    if kind == "frame":
        kids = plan_children(C.t, x) or kids   # the cheapest step establishes the programme
    return [a for c in kids for a in proof_alternatives(C, c, choice)]


def proof_set(C, root, status, choice=None):
    best = None
    for alt in proof_alternatives(C, root, choice or {}):
        cost = sum((elem_cost(C, e, status)[0] for e in alt), Q(0))
        key = (cost, len(alt), sorted(alt))
        if best is None or key < best[0]:
            best = (key, alt, cost)
    return best[1], best[2]


def root_status(C, rid, status, pset):
    """Preset addition at the root: probabilistic and expected-utility budgets over the proof set's tables."""
    r = C.roots[rid]
    s, diag = status[rid]
    if s == "conceded" or r["preset"] == "worst-case":
        return s, diag, None
    loss = Q(0)
    for x in pset:
        if C.t.nodes[x].get("kind") != "cases":
            continue
        for pic, b in row_beliefs(C, x).items():
            mass = b["w"][0] * (1 - b["p"][0])
            if r["preset"] == "probabilistic":
                loss += mass
            else:
                succ = utility(C, r["success_class"]) if "success_class" in r else Q(1)
                loss += mass * (succ - utility(C, b["class"] or C.outside))
    if loss > q(r["budget"]):
        return "conceded", f"{r['preset']} budget: loss {loss} > {q(r['budget'])}", loss
    return s, diag, loss


# ---------------------------------------------------------------- worlds, value, ranking (§4 D9–D10, §5)
def components(rids, psets):
    """Connected components of roots, two roots joined when their proof sets share an element (§4)."""
    parent = {r: r for r in rids}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    owner = {}
    for r in rids:
        for x in psets[r]:
            if x in owner:
                parent[find(owner[x])] = find(r)
            else:
                owner[x] = r
    comps = defaultdict(list)
    for r in rids:
        comps[find(r)].append(r)
    return sorted((sorted(v) for v in comps.values()), key=lambda c: c[0])


def world_model(C, rids, psets, pmode="mid"):
    """Exact enumeration over the proof-set elements of the given roots (one component; rule 13 caps it)."""
    t = C.t
    variables = sorted({x for r in rids for x in psets[r]}, key=lambda x: (t.nodes[x].get("kind") == "cases", x))
    outcomes, nobelief = [], []
    for x in variables:
        n = t.nodes[x]
        if n.get("kind") == "cases":
            outs = []
            rb = row_beliefs(C, x)
            if not rb:
                # a table none of whose rows is admitted has not entered the computations: no belief, held at 1/2
                nobelief.append(x)
                outs = [(True, None, Q(1, 2)), (False, C.outside, Q(1, 2))]
            for pic, b in rb.items():
                w = b["w"][0]
                p = {"mid": b["p"][0], "lo": max(Q(0), b["p"][0] - b["p"][1] / 2), "hi": min(Q(1), b["p"][0] + b["p"][1] / 2)}[pmode]
                outs += [(True, None, w * p), (False, b["class"] or C.outside, w * (1 - p))]
                if "no belief" in b["p"][2] or "no belief" in b["w"][2]:
                    nobelief.append(x)
            outcomes.append([o for o in outs if o[2] > 0] or [(True, None, Q(1))])
        else:
            b = C.bel.get((("node", x), "range"))
            if b is None:
                nobelief.append(x)
                p = Q(1, 2)
            else:
                p = {"mid": b["mid"], "lo": b["range"][0], "hi": b["range"][1]}[pmode]
            outcomes.append([o for o in [(True, None, p), (False, None, 1 - p)] if o[2] > 0])
    count = math.prod(len(o) for o in outcomes) if outcomes else 1
    if count > MAX_WORLDS_PER_COMPONENT:
        raise Refuse(13, "graph/frame.yaml", f"component too large: the roots {', '.join(rids)} share proof-set elements and enumerate "
                     f"{count} worlds over {len(variables)} variables, above the per-component cap {MAX_WORLDS_PER_COMPONENT}; "
                     "split the component (a sub-frame) or coarsen a table")
    idx = {x: i for i, x in enumerate(variables)}
    worlds = []
    for combo in itertools.product(*outcomes):
        prob = math.prod((o[2] for o in combo), start=Q(1))
        worlds.append((combo, prob))
    return {"vars": variables, "idx": idx, "worlds": worlds, "nobelief": sorted(set(nobelief)), "count": count, "roots": list(rids)}


def holds(C, W, combo, x):
    t = C.t
    if x in W["idx"]:
        return combo[W["idx"][x]][0]
    n = t.nodes[x]
    kind = n.get("kind")
    if kind in ("leaf", "cases"):
        return False
    kids = n["children"]
    if kind == "choose" and n.get("committed", "none") != "none":
        kids = [n["committed"]]
    if kind == "frame":
        kids = plan_children(t, x)
    return (all if kind == "and" else any)(holds(C, W, combo, c) for c in kids)


def world_value(C, W, combo, rid, umode="mid"):
    """A plan's outcome in one world: its success class where it holds; where it fails, the worst class
    (lowest utility, then severity) among its failing leaves' classes, or the outside option when none is
    tagged. A programme (frame root) has no success class of its own and is not valued here: the act
    takes the best of its steps (ranking)."""
    r = C.roots[rid]
    if holds(C, W, combo, rid):
        return utility(C, r["success_class"], umode) if "success_class" in r else utility(C, C.outside, umode)
    sup = C.sup[rid]
    fails = [combo[W["idx"][x]][1] for x in W["vars"] if x in sup and not combo[W["idx"][x]][0] and combo[W["idx"][x]][1]]
    if not fails:
        return utility(C, C.outside, umode)
    worst = min(fails, key=lambda c: (utility(C, c), (C.cls.get(c) or {}).get("severity") is None, (C.cls.get(c) or {}).get("severity") or 0))
    return utility(C, worst, umode)


def root_numbers(C, rid, pset):
    """Pr and value (plan roots) with their intervals, from the root's own world model."""
    out = {}
    for pmode, umode, key in (("mid", "mid", "mid"), ("lo", "lo", "lo"), ("hi", "hi", "hi")):
        W = world_model(C, [rid], {rid: pset}, pmode)
        pr = sum((p for c, p in W["worlds"] if holds(C, W, c, rid)), Q(0))
        out.setdefault("Pr", {})[key] = pr
        if C.roots[rid]["role"] == "plan":
            out.setdefault("value", {})[key] = sum((p * world_value(C, W, c, rid, umode) for c, p in W["worlds"]), Q(0))
        if key == "mid":
            out["nobelief"] = W["nobelief"]
    return out


def refine(C, rid, status):
    """A plan's refinement path: each uncommitted choose takes the child of highest value."""
    t = C.t
    chooses = [x for x in support(t, rid) if t.nodes[x].get("kind") == "choose" and t.nodes[x].get("committed", "none") == "none"]
    best = None
    for picks in itertools.product(*[t.nodes[x]["children"] for x in chooses]):
        choice = dict(zip(chooses, picks))
        pset, cost = proof_set(C, rid, status, choice)
        nums = root_numbers(C, rid, pset)
        key = nums.get("value", nums["Pr"])["mid"]
        if best is None or key > best[0]:
            best = (key, choice, pset, cost, nums)
    return best[1], best[2], best[3], best[4]


def entropy(dist):
    tot = float(sum(dist.values()))
    return -sum((float(p) / tot) * math.log2(float(p) / tot) for p in dist.values() if p > 0) if tot else 0.0


def ranking(C, D, scope, lam, window_dp, frontier):
    """The map term and the decision term of every observation unit, enumerated per component.

    Roots are grouped into connected components (two roots joined when their proof sets share
    an element); the components are independent under `dependence: independent`, so the entropy
    of the settled-truth vector S is the sum over components and a unit's bits are computed in
    its own component alone. The decision term needs every plan: plans outside the unit's
    component enter the act as constants (their expected value), which is exact because the
    observation cannot move them. A scoped query enumerates the union of the components whose
    variables the scope node's truth depends on."""
    t = C.t
    rids = list(C.roots)
    if scope and scope not in C.sup:
        C.sup[scope] = support(t, scope)
    # a root is in scope when it contains the scope node or lies under it (a programme's steps under the programme)
    in_scope_root = lambda r: scope is None or scope == r or scope in C.sup[r] or r in C.sup[scope]
    read_error = q(C.po.get("read_error", Q(3, 10)))
    overhead = q(C.po.get("task_overhead_minutes", 0))
    outside_u = utility(C, C.outside)
    is_frame = lambda r: t.nodes[r].get("kind") == "frame"
    # options: plan roots with a defined option value, in scope; a conceded plan is not a candidate until revived (§6).
    # A programme (frame root) is not an option itself: committing to it is committing to its best step, so its
    # non-conceded steps with values are the options and the act's max runs over steps and plans alike (max is
    # associative); a sub-frame's own outside option, where it names one, is a constant option of its own.
    plan_roots = [r for r in rids if C.roots[r]["role"] == "plan" and in_scope_root(r)]
    plans_all = [r for r in plan_roots if not is_frame(r) and D["roots"][r].get("option_value") is not None]
    plans = [r for r in plans_all if D["roots"][r]["status"] != "conceded"]
    const = {r: D["roots"][r]["act_value"] for r in plans}
    sub_outside = {r: utility(C, t.nodes[r]["outside_option"]) for r in plan_roots if is_frame(r) and t.nodes[r].get("outside_option")
                   and t.nodes[r]["outside_option"] != C.outside}
    frame_of = {r: C.roots[r]["frame"] for r in rids}
    label = lambda r: r if frame_of.get(r) is None or r == C.outside else f"{frame_of[r]} → {r}"
    comps = components(rids, C.psets)
    allvars = {x for r in rids for x in C.psets[r]}
    if scope:
        need = {x for x in allvars if x in C.sup.get(scope, set()) or x == scope}
        touched = [c for c in comps if any(x in need for r in c for x in C.psets[r])]
        comps = [sorted({r for c in touched for r in c})] if touched else [[]]
    in_scope = C.sup[scope] | {scope} if scope else set(t.nodes)

    def act(weighted, comp_plans):
        """max over options of expected value under a weighted set of this component's worlds; other plans constant."""
        tot = sum((w for _, w in weighted), Q(0))
        best = (outside_u, C.outside)
        for r, v in sub_outside.items():
            if v > best[0]:
                best = (v, f"{r}'s outside option")
        for r in plans:
            v = (sum((row[3][r] * w for row, w in weighted), Q(0)) / tot) if (r in comp_plans and tot) else const[r]
            if v > best[0]:
                best = (v, r)
        return best
    V_act, cand = act([], [])
    D["act"] = {"V_act": V_act, "cand": cand, "cand_label": label(cand), "outside_value": outside_u,
                "outside_placed": utility_placed(C, C.outside), "outside_option": C.outside,
                "options": {r: D["roots"][r]["option_value"] for r in plans},
                "conceded_plans": {r: D["roots"][r]["diagnosis"] for r in plans_all if r not in plans},
                "plans_without_value": [r for r in plan_roots if not is_frame(r) and D["roots"][r].get("option_value") is None]}
    H0, units, comp_info = 0.0, [], []
    top_comp = None
    for comp in comps:
        W = world_model(C, comp, C.psets) if comp else {"vars": [], "idx": {}, "worlds": [((), Q(1))], "nobelief": [], "count": 1, "roots": []}
        comp_plans = [r for r in plans if r in comp]
        S_of = (lambda c: (holds(C, W, c, scope),)) if scope else (lambda c: tuple(holds(C, W, c, r) for r in comp))
        rows = []
        for combo, prob in W["worlds"]:
            vals = {r: (world_value(C, W, combo, r) if D["roots"][r]["value_defined"] else D["roots"][r]["option_value"]) for r in comp_plans}
            rows.append((combo, prob, S_of(combo), vals))
        base_S = defaultdict(Q)
        for row in rows:
            base_S[row[2]] += row[1]
        H0c = entropy(base_S)
        H0 += H0c
        comp_info.append({"roots": comp, "variables": len(W["vars"]), "worlds": W["count"], "H_S_bits": H0c})
        comp_units = []
        # revive units: every conceded table (or negation-conceded leaf) a conceded root's diagnosis chain ends at,
        # and every root conceded by its preset's budget alone; the unit observes the target's truth like a vet,
        # priced at the revival cost (arguing the conceding conditional back above the bar)
        revive_targets = {}
        for r in comp:
            if D["roots"][r]["status"] != "conceded":
                continue
            tgt = revive_target(C, r, C.status) if C.status[r][0] == "conceded" else r
            if tgt is not None and tgt in in_scope and (tgt in W["idx"] or tgt == r):
                revive_targets.setdefault(tgt, []).append(r)
        for x in W["vars"]:
            if x not in in_scope:
                continue
            n = t.nodes[x]
            if n.get("kind") == "cases" and C.status[x][0] == "conceded" and x not in revive_targets:
                revive_targets[x] = sorted(r for r in comp if x in C.psets[r])
        for x in sorted(set(W["vars"]) | set(revive_targets)):
            if x not in in_scope:
                continue
            n = t.nodes[x]
            if x in revive_targets:
                kinds = ["revive"]
            elif x not in W["idx"] or D["nodes"][x]["status"] != "open" or n.get("leaf_kind") == "question":
                continue
            else:
                v = C.V[x]["headline"]
                kinds = ["vet", "map-read"] if v < 6 else ["trace"] if v < C.est_level else []
            for kind in kinds:
                if kind == "vet":
                    mins = rate(C, "map-read", n["size"])[0] + rate(C, "trace", n["size"])[0]
                    why = [rate(C, "map-read", n["size"])[1], rate(C, "trace", n["size"])[1]]
                elif kind == "revive":
                    mins, w1 = revival(C, x, C.status) if C.status[x][0] == "conceded" else rate(C, "revive", n["size"])
                    why = [w1, "revive: argue the conceding conditional back above the bar; observes the table's truth"]
                else:
                    mins, w1 = rate(C, kind, n["size"])
                    why = [w1]
                obs = {}
                for row in rows:
                    truth = row[0][W["idx"][x]][0] if x in W["idx"] else holds(C, W, row[0], x)
                    for o, wgt in (((truth, Q(1)),) if kind != "map-read" else ((truth, 1 - read_error), (not truth, read_error))):
                        obs.setdefault(o, []).append((row, row[1] * wgt))
                EH, Dv = 0.0, Q(0)
                for o, weighted in obs.items():
                    po = sum((w for _, w in weighted), Q(0))
                    dist = defaultdict(Q)
                    for row, w in weighted:
                        dist[row[2]] += w
                    EH += float(po) * entropy(dist)
                    Dv += po * act(weighted, comp_plans)[0]
                bits = max(0.0, H0c - EH)
                hours = float(overhead + mins) / 60
                ai_num = "AI number" in C.flags.get(x, set())
                if ai_num:
                    why = why + ["vet this AI number: the target's judgments rest on AI handles only"]
                comp_units.append({"kind": kind, "target": x, "size": n["size"], "minutes": mins, "bits": bits, "rate": bits / hours if hours else 0.0,
                                   "D": Dv - V_act if plans else None, "why": why, "ai_number": ai_num,
                                   "bears_on": sorted(r for r in rids if x in C.psets[r] or x == r) if kind != "revive" else revive_targets[x],
                                   "component": comp})
        units += comp_units
        if comp_units and (top_comp is None or max(u["rate"] for u in comp_units) > top_comp[0]):
            top_comp = (max(u["rate"] for u in comp_units), rows, W, comp_plans)
    # a gestalt is ranked first only on a root with no derived probability and no gestalt: it is outside both terms
    # (a programme carries none; its steps do)
    gest = [{"kind": "gestalt", "target": r, "size": t.nodes[r]["size"], "minutes": rate(C, "gestalt", t.nodes[r]["size"])[0], "bits": None,
             "rate": None, "D": None, "why": ["no derived probability (a proof-set leaf carries no judgment) and no gestalt: outside both terms"],
             "bears_on": [r], "component": next((c for c in comps if r in c), [r])}
            for r in rids if D["roots"][r]["gestalt"] is None and not D["roots"][r]["Pr_defined"] and in_scope_root(r) and not is_frame(r)]
    units.sort(key=lambda u: (-(u["rate"] or 0), u["target"]))
    if lam is not None and plans:
        for u in units:
            u["score"] = (u["rate"] or 0) + float(lam) * float(u["D"]) / (float(q(C.fr.get("window_minutes", 360))) / 60)
        units.sort(key=lambda u: (-u["score"], u["target"]))
    if (window_dp or frontier) and top_comp:
        _, rows, W, comp_plans = top_comp
        window_dp_values(C, D, rows, units, lambda weighted: act(weighted, comp_plans), V_act, frontier, W)
    D["units"] = gest + units
    D["ranking"] = {"scoped": scope, "H_S_bits": H0, "ordered_by": "score" if lam is not None else "map rate",
                    "lambda": None if lam is None else float(lam)}
    D["world_model"] = {"components": comp_info, "cap_per_component": MAX_WORLDS_PER_COMPONENT, "dependence": "independent"}
    # regime and commit lines
    reorder = sum(1 for i, u in enumerate(sorted(units, key=lambda u: (-(float(u["D"]) if u["D"] is not None else 0), -(u["rate"] or 0)))) if units and u is not units[i])
    conceded_txt = "; ".join(f"{label(r)} conceded by {D['roots'][r]['diagnosis']}" for r in plans_all if r not in plans)
    novalue = D["act"]["plans_without_value"]
    ranked_index = {(u["kind"], u["target"]): i for i, u in enumerate(gest + units, 1)}
    revivals = sorted({u["target"] for u in units if u["kind"] == "revive"})
    revival_txt = "; ".join(f"revive {x}: ranked unit {ranked_index[('revive', x)]}" for x in revivals) or "no revive unit in scope"
    if not plan_roots:
        regime = "no plan in scope; the decision term is suspended; the order is the map's"
    elif not plans_all:
        regime = "no plan in scope has a value yet (no belief on every plan and step); the decision term is suspended; the order is the map's"
    elif not plans:
        regime = f"every plan in scope is conceded ({conceded_txt}); the decision term is suspended; the order is the map's"
    elif all((u["D"] or 0) == 0 for u in units):
        reason = ("one plan whose failure stories name no class below the outside option" if len(plans) == 1 and not any(
            D["roots"][r]["failure_classes_below_outside"] for r in plans) else "the leading plan leads in every world")
        regime = f"no unit can change the act ({reason}); the order is the map's"
    else:
        regime = f"the decision term would reorder {reorder} units; shown, not applied"
    maxD = max((u["D"] for u in units if u["D"] is not None), default=Q(0))
    commit_level = int(C.fr.get("commit_level", 6))
    if not plan_roots:
        commit = "commit line suspended: no plan in scope"
    elif not plans_all:
        commit = f"commit line suspended: no plan has a value yet (no belief on {', '.join(label(r) for r in novalue)}; a gestalt on a step or plan would give one)"
    elif not plans:
        commit = f"no non-conceded plan to commit to ({conceded_txt}); the outside option stands until a revival ({revival_txt})"
    elif maxD > 0:
        top = next((u for u in units if u["D"] and u["D"] > 0), units[0])
        commit = f"research first: begin with {top['kind']} {top['target']}"
    elif cand in D["roots"] and D["roots"][cand]["weakest_V"] >= commit_level:
        commit = f"commit now → {label(cand)}"
    elif cand == C.outside:
        commit = "commit now → the outside option (no plan sits above the default trajectory)"
    elif cand not in D["roots"]:
        commit = f"commit now → {cand} (no plan sits above it)"
    else:
        commit = f"no plan vetted enough to commit to; leading candidate {label(cand)}"
    if conceded_txt and plans:
        commit += f" ({conceded_txt}: not a candidate; {revival_txt})"
    D["lines"] = {"commit": commit, "regime": regime, "scoped": f"scoped: bits about {scope} only" if scope else None}


def utility_placed(C, cid):
    """Whether a class has a utility, or a valuation node a defined value (its rows all judged)."""
    if cid in C.valuations:
        return bool((C.val.get(cid) or {}).get("defined"))
    return (C.cls.get(cid) or {}).get("utility") is not None


def window_dp_values(C, D, rows, units, act, V_act, frontier, W):
    """`--window-dp`: exact adaptive schedule over the top six exact-observation units within the window;
    `--frontier K`: the greedy non-adaptive continuation at each commitment mass point (v3b §3.3)."""
    window = q(C.fr.get("window_minutes", 360))
    # the schedule runs inside one component, the one holding the top-rated unit (its worlds are `rows`)
    short = [u for u in units if u["kind"] != "map-read" and u["target"] in W["idx"]][:6]
    commitment = C.fr.get("commitment") or [{"minutes": window, "mass": 1}]

    def terminal(weighted, elapsed):
        if not frontier:
            return act(weighted)[0]
        total = Q(0)
        for cpt in commitment:
            c, mass = q(cpt.get("minutes", 0)), q(cpt.get("mass", 1))
            if c <= elapsed:
                total += mass * act(weighted)[0]
                continue
            left, chosen, used = c - elapsed, [], set()
            for _ in range(int(frontier)):
                best = None
                for u in short:
                    if u["target"] in used or u["minutes"] > left:
                        continue
                    gain = sum((act(ws)[0] * sum((w for _, w in ws), Q(0)) for ws in split(weighted, u["target"]).values()), Q(0))
                    score = gain / (u["minutes"] or Q(1))
                    if best is None or score > best[0]:
                        best = (score, u)
                if best is None:
                    break
                chosen.append(best[1]["target"])
                used.add(best[1]["target"])
                left -= best[1]["minutes"]
            groups = {(): weighted}
            for x in chosen:
                groups = {k + (o,): ws for k, g in groups.items() for o, ws in split(g, x).items()}
            tot = sum((w for _, w in weighted), Q(0)) or Q(1)
            total += mass * sum((act(ws)[0] * sum((w for _, w in ws), Q(0)) for ws in groups.values()), Q(0)) / tot
        return total

    def split(weighted, x):
        out = {}
        for row, w in weighted:
            out.setdefault(row[0][W["idx"][x]][0], []).append((row, w))
        return out

    def dp(remaining, elapsed, weighted):
        best = terminal(weighted, elapsed)
        tot = sum((w for _, w in weighted), Q(0)) or Q(1)
        for u in remaining:
            if elapsed + u["minutes"] > window:
                continue
            rest = [v for v in remaining if v is not u]
            val = sum((dp(rest, elapsed + u["minutes"], ws) * sum((w for _, w in ws), Q(0)) for ws in split(weighted, u["target"]).values()), Q(0)) / tot
            best = max(best, val)
        return best
    base = [(row, row[1]) for row in rows]
    for u in short:
        tot = Q(1)
        q_u = sum((dp([v for v in short if v is not u], u["minutes"], ws) * sum((w for _, w in ws), Q(0)) for ws in split(base, u["target"]).values()), Q(0)) / tot
        u["D_window"] = q_u - V_act
    D["ranking_window"] = {"window_minutes": window, "frontier": int(frontier or 0), "shortlist": [u["target"] for u in short],
                           "component": W["roots"], "V_idle": terminal(base, Q(0)) if frontier else None}


# ---------------------------------------------------------------- derive: the orchestrator
def derive(t, scope=None, lam=None, window_dp=False, frontier=0, today=None, with_proposals=True, as_handle=None):
    """D1–D10 and §5 over a linted tree; returns the `derived.json` object (Fractions still live).

    Choices made where the specification is silent (all reversible, all Default):
    a node with `superseded_by` may be parentless (it left its table); a row's weight or
    conditional with no judgment is held at the remaining mass or 1/2 with width 1 and flagged
    `no belief`; the row judgment's read-check looks at the picture node; pooled J 10 needs both
    ranges at J ≥ 8; anchor 12's `checked` items name each admitted picture by id; an
    uncommitted `choose` is refined by trying each child and keeping the highest root value;
    the value interval is taken at all conditionals low and all high (monotone case); a leaf
    outside every proof set is false in the world model; a gestalt stands in for an undefined
    plan value as g·U(success) + (1 − g)·U(outside); the comonotone companion is the minimum
    hold probability over the proof set; the world model is enumerated per connected component
    of roots and a component above 2^15 worlds is refused (rule 13); a conceded plan is not a
    candidate in the act until revived; a leaf range on a node that became a table is stale.
    """
    C = Ctx(t)
    resolve_events(C)
    admission(C)
    levels(C)
    judgments(C)
    valuation_values(C)
    status = statuses(C)
    C.status = status
    C.sup = {rid: support(t, rid) for rid in C.roots}
    D = {"checker_version": CHECKER_VERSION, "anchor_rules": C.po.get("anchor_rules"), "generated_hash": "",
         "nodes": {}, "judgments": {}, "roots": {}, "events": {k: sorted(e["id"] for e in t.events if e["_status"] == k)
                                                                for k in ("counted", "withdrawn", "stale")}}
    D["events"]["stale_reasons"] = dict(sorted(C.stale_reason.items()))
    D["audits"] = {h: dict(a) for h, a in sorted(C.audits.items())}
    D["valuations"] = {x: {"value": {k: utility(C, x, k) for k in ("mid", "lo", "hi")}, "defined": C.val[x]["defined"],
                           "provisional": bool(t.nodes[x].get("provisional")),
                           "role": "outside option" if x == C.outside else "undescribed failure" if x == C.undescribed else "valuation"}
                       for x in sorted(C.valuations)}
    C.psets, C.costs, C.choice = {}, {}, {}
    for rid, r in C.roots.items():
        is_frame = t.nodes[rid].get("kind") == "frame"
        if r["role"] == "plan":
            choice, pset, cost, nums = refine(C, rid, status)
        else:
            choice, (pset, cost) = {}, proof_set(C, rid, status)
            nums = root_numbers(C, rid, pset)
        C.psets[rid], C.costs[rid], C.choice[rid] = pset, cost, choice
        rs, rdiag, loss = root_status(C, rid, status, pset)
        g = C.bel.get((("node", rid), "gestalt"))
        pr_defined = not nums["nobelief"]
        value_defined = r["role"] == "plan" and pr_defined and not is_frame
        option, steps, leading = None, None, None
        if is_frame:
            # a programme: its value in the parent is its best non-conceded step's (derived or gestalt stand-in),
            # the sub-frame's own outside option when every step is conceded, undefined while no step has a value
            steps = [c for c in plan_children(t, rid)]
            live = [c for c in steps if D["roots"][c]["option_value"] is not None and D["roots"][c]["status"] != "conceded"]
            if live:
                leading = max(live, key=lambda c: (D["roots"][c]["option_value"], c))
                option = D["roots"][leading]["option_value"]
                nums["value"] = D["roots"][leading]["value"]
            elif steps and all(D["roots"][c]["status"] == "conceded" for c in steps):
                option = utility(C, t.nodes[rid].get("outside_option") or C.outside)
            if not live:
                nums["value"] = None
            if g is not None:
                g = None   # a programme carries no gestalt of its own; its steps do
        elif r["role"] == "plan":
            if value_defined:
                option = nums["value"]["mid"]
            if g is not None and (not value_defined or not (nums["value"]["lo"] <= g["mid"] <= nums["value"]["hi"])):
                succ = utility(C, r["success_class"])
                option = g["mid"] * succ + (1 - g["mid"]) * utility(C, C.outside)
        sup = C.sup[rid]
        below = sorted({C.row_class[k] or C.outside for k in C.admitted if k[0] in sup and C.admitted[k]
                        and utility(C, C.row_class[k] or C.outside) < utility(C, C.outside)})
        # the root's numbers rest on AI judgments only when any proof-set belief they use is AI-generated
        ai_only = sorted({x for x in pset if (C.bel.get((("node", x), "range")) or {}).get("generated")}
                         | {x for x in pset if t.nodes[x].get("kind") == "cases"
                            and any("AI number" in b["p"][2] or "AI number" in b.get("w", (0, 0, []))[2] for b in row_beliefs(C, x).values())}
                         | ({rid} if g is not None and g.get("generated") else set()))
        D["roots"][rid] = {"role": r["role"], "preset": r["preset"], "frame": r["frame"], "status": rs, "diagnosis": rdiag,
                           "revival": revival(C, rid, status) if rs == "conceded" and status[rid][0] == "conceded" else None,
                           "proof_set": sorted(pset), "cost": cost, "choice": choice,
                           "disproof": min((rate(C, "attack", t.nodes[x]["size"])[0] for x in pset), default=None),
                           "Pr": nums["Pr"], "Pr_defined": pr_defined, "value": nums.get("value"), "value_defined": value_defined,
                           "gestalt": None if g is None else {"mid": g["mid"], "range": g["range"], "J": g["J"], "generated": bool(g.get("generated"))},
                           "option_value": option, "nobelief": nums["nobelief"],
                           # the value the act uses for this plan: the derived expectation, or the gestalt stand-in
                           "act_value": nums["value"]["mid"] if value_defined else option,
                           "budget_loss": loss,
                           "weakest_V": min((C.V[x]["headline"] for x in pset), default=0),
                           "failure_classes_below_outside": below,
                           "comonotone_Pr": min((row_hold(C, x) for x in pset), default=Q(1)),
                           "success_class": r.get("success_class"), "budget": r.get("budget"),
                           # the proof-set elements whose numbers rest on AI judgments only (ruling 34): every display marks them
                           "ai_only": ai_only,
                           # sub-frame fields: a programme lists its steps and the step whose value it carries
                           "subframe": {"question": t.nodes[rid].get("question"), "steps": steps, "leading_step": leading,
                                        "roots": [c for c in t.nodes[rid]["children"]],
                                        "outside_option": t.nodes[rid].get("outside_option") or C.outside} if is_frame else None}
    # load, margin
    load = {}
    for x in t.nodes:
        forced = statuses(C, frozenset([x]))
        held = statuses(C, forced_est=frozenset([x]))
        # the roots whose status depends on x: conceded once x is conceded, not conceded once x is established
        load[x] = sorted(r for r in C.roots if (x in C.sup[r] or x == r) and forced[r][0] == "conceded" and held[r][0] != "conceded")
    for rid, r in C.roots.items():
        margin = None
        if r["preset"] == "worst-case" and D["roots"][rid]["status"] == "open":
            est = [x for x in C.psets[rid] if status[x][0] == "established"]
            margin = "no established leaves" if not est else ">3"
            for k in range(1, 4):
                if any(statuses(C, frozenset(sub))[rid][0] == "conceded" for sub in itertools.combinations(est, k)):
                    margin = k
                    break
        D["roots"][rid]["margin"] = margin
        D["roots"][rid]["load_bearing"] = sorted(x for x in C.psets[rid] if len(load[x]) >= 2)
    for x, n in t.nodes.items():
        s, diag = status[x]
        if n.get("kind") == "cases" and any(not C.admitted[(x, r["picture"])] for r in n["rows"]):
            C.flags[x].add("under attack")
        if s == "conceded":
            C.flags[x].add(f"conceded by {diag}")
        b = C.bel.get((("node", x), "range"))
        if n.get("kind") == "leaf" and b is None and n.get("leaf_kind") not in ("picture", "completeness", "partition", "question"):
            C.flags[x].add("no belief")
        if n.get("kind") == "cases" and (not row_beliefs(C, x) or any("no belief" in b2["p"][2] or "no belief" in b2["w"][2] for b2 in row_beliefs(C, x).values())):
            C.flags[x].add("no belief")
        if n.get("provisional"):
            C.flags[x].add("provisional")
        cost, why = elem_cost(C, x, status) if n.get("kind") in ("leaf", "cases") else (None, [])
        D["nodes"][x] = {"kind": n.get("kind"), "leaf_kind": n.get("leaf_kind"), "size": n["size"], "version": n["version"],
                         "V": C.V[x], "flags": sorted(C.flags[x]), "status": s, "diagnosis": diag,
                         "revival": revival(C, x, status) if s == "conceded" else None, "cost": cost, "cost_rows": why,
                         "load": load[x], "belief": None if b is None else {"J": b["J"], "mid": b["mid"], "width": b["width"], "range": b["range"]},
                         "rows": row_beliefs(C, x) if n.get("kind") == "cases" else None,
                         "admitted": {r["picture"]: C.admitted[(x, r["picture"])] for r in n["rows"]} if n.get("kind") == "cases" else None,
                         # leaf ranges given before this node became a table: suggestions for the residual row, never used
                         "stale_leaf_ranges": [{"event": e["id"], "by": e["by"], "range": [q(e["estimate"][0]), q(e["estimate"][1])]}
                                               for e in C.counted if e["_status"] == "stale" and C.stale_reason.get(e["id"]) == STALE_TABLE
                                               and target_key(e["target"]) == ("node", x)] if n.get("kind") == "cases" else None}
    for (tk, field), b in C.bel.items():
        D["judgments"]["/".join(map(str, tk)) + "/" + field] = b
    ranking(C, D, scope, lam, window_dp, frontier)
    D["proposals"] = proposal_deltas(C, D) if with_proposals else []
    D["units_unranked"] = unranked_units(C, D, load)
    D["audit"] = audit_line(C, today, as_handle)
    return D


def row_hold(C, x):
    n = C.t.nodes[x]
    if n.get("kind") == "cases":
        rb = row_beliefs(C, x)
        return sum((b["w"][0] * b["p"][0] for b in rb.values()), Q(0)) if rb else Q(1, 2)
    b = C.bel.get((("node", x), "range"))
    return b["mid"] if b else Q(1, 2)


def unranked_units(C, D, load):
    t = C.t
    out = []
    plan_sup = set().union(*[C.sup[r] for r, rr in C.roots.items() if rr["role"] == "plan"] or [set()])
    for x, n in t.nodes.items():
        if n.get("kind") == "cases":
            # a leaf range given before the leaf became this table is offered under the residual row, never used
            stale_ranges = [e for e in C.counted if e["_status"] == "stale" and C.stale_reason.get(e["id"]) == STALE_TABLE
                            and target_key(e["target"]) == ("node", x)]
            for r in n["rows"]:
                key = (x, r["picture"])
                if not C.admitted[key]:
                    out.append(("admit", f"{x}/{r['picture']}", x, None))
                    continue
                for f in ("w", "p"):
                    if f == "w" and r.get("residual"):
                        continue
                    if (C.bel.get((("row",) + key, f)) or {}).get("J", 0) < 8:
                        sug = None
                        if f == "p" and r.get("residual") and stale_ranges:
                            e = stale_ranges[-1]
                            sug = f"suggestion, not used: the leaf's earlier range {frange(e['estimate'])} ({e['id']}, stale: {STALE_TABLE})"
                        out.append(("estimate", f"{x}/{r['picture']}.{f}", x, sug))
                if C.row_class[key] is None and not r.get("residual"):
                    out.append(("classify", f"{x}/{r['picture']}.class", x, None))
            if len(n["rows"]) > 5:
                out.append(("re-examine", x, x, None))
        if x in plan_sup and ((n.get("kind") == "choose" and n.get("committed", "none") == "none") or (n.get("kind") == "or" and "tag" not in n)):
            out.append(("classify", x, x, None))
    for r, R in D["roots"].items():
        if R["gestalt"] is None and R["Pr_defined"] and R["subframe"] is None:
            out.append(("gestalt", r, r, "no gestalt yet: the root has a derived probability, so this is not ranked"))
    for tk, field in C.reconcile:
        node = tk[1] if tk[0] == "node" else tk[2]
        out.append(("reconcile", "/".join(map(str, tk[1:])) + "." + field, node, None))
    for p in D.get("proposals", []):
        if p["status"] == "proposed":
            out.append(("approve", p["id"], None, None))
    out.sort(key=lambda u: (-(len(load.get(u[2], [])) if u[2] else 0), u[0], u[1]))
    return [{"kind": k, "target": tg, "load": load.get(nd, []) if nd else [], "note": note} for k, tg, nd, note in out]


def audit_line(C, today, as_handle=None):
    today = today or _dt.date.today()
    share = q(C.fr.get("audit_share", Q(1, 10))) * q(C.fr.get("window_minutes", 360))
    cands = []
    for e in C.counted:
        try:
            age = (today - _dt.date.fromisoformat(str(e["date"]))).days
        except ValueError:
            continue
        if 7 <= age <= 60 and is_human(C.t, e["by"]) and e["by"] != as_handle and e["kind"] in LEVEL_KINDS | {"estimate", "gestalt"}:
            cands.append(e)
    if not cands:
        return {"minutes": share, "event": None, "text": f"audit ({fmt(share)} min of this session): no auditable event yet"}
    rng = random.Random(sha(str(today)))        # the draw is fixed for the day, whatever else is filed
    e = rng.choice(cands)
    return {"minutes": share, "event": e["id"], "by": e["by"],
            "text": f"audit ({fmt(share)} min of this session): re-perform {e['kind']} {e['id']} by {e['by']} on {json.dumps(e['target'])}; cross-audit preferred"}


# ---------------------------------------------------------------- proposals (§2.5)
def apply_ops(t, p):
    t2 = copy.deepcopy(t)
    t2.proposals = []
    for op in p.get("ops") or []:
        k = op.get("op")
        if k == "new-node":
            path = t.graph / "proposals" / op["file"]
            n = parse_node_text(path.read_text(), t.rel(path))
            t2.nodes[n["id"]] = n
        elif k == "add-child":
            t2.nodes[op["parent"]]["children"].append(op["child"])
        elif k == "remove-child":
            t2.nodes[op["parent"]]["children"].remove(op["child"])
        elif k == "retarget":
            kids = t2.nodes[op["node"]]["children"]
            kids[kids.index(op["from"])] = op["to"]
        elif k == "split-row":
            cn = t2.nodes[op["cases"]]
            old = next(r for r in cn["rows"] if r["picture"] == op["row"])
            cn["rows"].remove(old)
            cn["children"].remove(op["row"])
            t2.nodes[op["row"]]["superseded_by"] = op["into"][0]
            for new in op["into"]:
                cn["children"].append(new)
                cn["rows"].append({"picture": new, "class": old.get("class"), "observable": old.get("observable", "never")})
                t2.nodes[new].setdefault("refines", op["row"])
        elif k == "sharpen":
            n = t2.nodes[op["node"]]
            n["_statement"], n["version"] = op["statement"], n["version"] + 1
        else:
            raise Refuse(9, p["_path"], f"unknown op {k!r}")
    return t2


def proposal_deltas(C, D):
    out = []
    for p in C.t.proposals:
        try:
            t2 = apply_ops(C.t, p)
            D2 = derive(t2, with_proposals=False)
            affected = sorted(r for r in D2["roots"] if any(x in support(t2, r) for x in (p.get("targets") or [])))
            lines = []
            for r in affected:
                a, b = D["roots"].get(r, {}), D2["roots"][r]
                lines.append(f"- {r}: cost {fmt(a.get('cost'))} → {fmt(b['cost'])}; load {len([x for x in D['nodes'] if r in D['nodes'][x]['load']])} → "
                             f"{len([x for x in D2['nodes'] if r in D2['nodes'][x]['load']])}; status {a.get('status')} → {b['status']}; "
                             f"value {fmt((a.get('value') or {}).get('mid'))} → {fmt((b.get('value') or {}).get('mid'))}")
            delta = "\n".join(lines) or "- no root affected"
        except (Refuse, KeyError, ValueError, FileNotFoundError) as e:
            delta = f"- could not derive on the scratch copy: {e}"
        if p.get("_delta") and p["_delta"].strip() != delta.strip():
            raise Refuse(7, p["_path"], "## Delta does not match the checker's recomputation")
        out.append({"id": p["id"], "kind": p["kind"], "status": p["status"], "delta": delta, "path": p["_path"], "had_delta": bool(p.get("_delta"))})
    return out


# ---------------------------------------------------------------- rendering (§6)
def fmt(x):
    if x is None:
        return "—"
    if x == INF:
        return "∞"
    if isinstance(x, Q):
        return f"{x.numerator}/{x.denominator} (≈{float(x):.3f})" if x.denominator != 1 else str(x.numerator)
    if isinstance(x, float):
        return f"{x:.3f}"
    return str(x)


def frange(r):
    if not r:
        return "—"
    lo, hi = (r["lo"], r["hi"]) if isinstance(r, dict) else (r[0], r[1])
    return f"[{fmt(lo)}, {fmt(hi)}]"


def _clean(o):
    """JSON-ready copy: Fractions as "p/q", ∞ as "inf", sets sorted, keys as strings."""
    if isinstance(o, Q):
        return f"{o.numerator}/{o.denominator}"
    if isinstance(o, float) and math.isinf(o):
        return "inf"
    if isinstance(o, dict):
        return {str(k): _clean(v) for k, v in o.items()}
    if isinstance(o, (set, frozenset)):
        return sorted(_clean(v) for v in o)
    if isinstance(o, (list, tuple)):
        return [_clean(v) for v in o]
    if isinstance(o, _dt.date):
        return o.isoformat()
    return o


def dumps(D):
    return json.dumps(_clean(D), indent=1, sort_keys=True, allow_nan=False)


def prefs(t, handle, why):
    u = ((t.policy.get("users") or {}).get(handle) or {}) if handle else {}
    return {"numbers": bool(why or (u.get("show_numbers", False) if handle else False)),
            "alt": bool(u.get("alternative_calculations", False)), "handle": handle}


def outside_text(D):
    """The outside option's value from its valuation node, or 'no belief' with the point and interval it is read at."""
    name = D["act"].get("outside_option", "the outside option")
    if D["act"].get("outside_placed"):
        prov = " (provisional)" if (D.get("valuations") or {}).get(name, {}).get("provisional") else ""
        return f"{fmt(D['act']['outside_value'])} from {name}{prov}"
    return f"no belief on {name} (read as 0; interval the whole scale [-1, 1])"


def valuation_lines(D):
    """One line per valuation node: its role, value, interval and the provisional mark."""
    out = []
    for x, V in (D.get("valuations") or {}).items():
        if V["defined"]:
            out.append(f"- {x} ({V['role']}): value {fmt(V['value']['mid'])} in {frange(V['value'])}{' (provisional)' if V['provisional'] else ''}")
        else:
            out.append(f"- {x} ({V['role']}): no belief (read as 0; interval the whole scale)")
    return out


def render_tasks(t, D, pf, today):
    L = [f"# Tasks (generated {today}; regenerated by the checker, never edited)", ""]
    if pf is not POOLED:
        L.append(f"*Personal render{' for ' + pf['handle'] if pf['handle'] else ''}"
                 f"{'; scoped to ' + D['ranking']['scoped'] if D['ranking'].get('scoped') else ''}: not a committed file.*\n")
    dg = D.get("digest") or {}
    L += ["## Digest (what changed since the previous committed derivation)",
          f"- statuses flipped: {', '.join(dg.get('statuses_flipped') or []) or 'none'}",
          f"- root statuses flipped: {', '.join(dg.get('root_statuses_flipped') or []) or 'none'}",
          f"- levels moved: {', '.join(dg.get('levels_moved') or []) or 'none'}",
          f"- events counted since the previous derivation: {dg.get('events_new', 'all (first derivation)')}",
          f"- proposals awaiting approval: {', '.join(dg.get('proposals_awaiting') or []) or 'none'}", ""]
    L += ["## Lines", f"- commit line: {D['lines']['commit']}", f"- regime: {D['lines']['regime']}",
          f"- {D['audit']['text']} (the session's audit share, listed first and never ranked; the top task is ranked unit 1)"]
    if D["lines"].get("scoped"):
        L.append(f"- {D['lines']['scoped']}")
    L += ["", "## Ranked units (by map rate; D shown, not applied)" if D["ranking"]["lambda"] is None else f"## Ranked units (by rate + λ·D, λ = {D['ranking']['lambda']})",
          "Each line: `kind target (size letter of the target, ~rate-table minutes) — bears on <the roots whose proof set holds the target>`."]
    for i, u in enumerate(D["units"], 1):
        L.append(f"{i}. {u['kind']} {u['target']} ({u['size']}, ~{fmt(u['minutes'])} min) — bears on {', '.join(u['bears_on'])}"
                 + (" — vet this AI number" if u.get("ai_number") else ""))
    L += ["", "## Judgment and structure units (unranked, by load)",
          "Load is the number of roots whose status depends on the unit's node: conceded if it is conceded, not conceded if it is established."]
    L += [f"- {u['kind']} {u['target']} — load {len(u['load'])}" + (f"; {u['note']}" if u.get("note") else "") for u in D["units_unranked"]] or ["- none"]
    if pf["numbers"]:
        L += ["", "## Why", "", "| unit | minutes | bits | bits/h | D | D_window | rate rows (prior until refit) |", "|---|---|---|---|---|---|---|"]
        for u in D["units"]:
            L.append(f"| {u['kind']} {u['target']} | {fmt(u['minutes'])} | {fmt(u['bits'])} | {fmt(u['rate'])} | {fmt(u['D'])} | {fmt(u.get('D_window'))} | {'; '.join(u['why'])} |")
        comps = D.get("world_model", {}).get("components", [])
        L += ["", f"H(S) = {D['ranking']['H_S_bits']:.3f} bits over {len(comps)} component(s) "
              + "; ".join(f"[{', '.join(c['roots'])}: {c['variables']} variables, {c['worlds']} worlds]" for c in comps)
              + f"; V_act = {fmt(D['act']['V_act'])} ({D['act'].get('cand_label', D['act']['cand'])}); outside option = {outside_text(D)}", ""]
        L += valuation_lines(D) + [""]
        for r, R in D["roots"].items():
            L.append(f"- {r}{' (in ' + R['frame'] + ')' if R.get('frame') else ''}: Pr {fmt(R['Pr']['mid'])} in {frange(R['Pr'])}; value {fmt((R['value'] or {}).get('mid'))}"
                     f"{' in ' + frange(R['value']) if R['value'] else ''}; gestalt {fmt((R['gestalt'] or {}).get('mid'))}; "
                     f"no belief on: {', '.join(R['nobelief']) if R['nobelief'] else 'none'}"
                     + (f"; programme: leading step {R['subframe']['leading_step'] or 'none'}" if R.get("subframe") else ""))
    return "\n".join(L) + "\n"


def render_view(t, D, pf, today):
    L = [f"# View (generated {today}; regenerated by the checker, never edited)", ""]
    if pf["handle"]:
        L.append(f"*Personal render for {pf['handle']}: numbers {'shown' if pf['numbers'] else 'in the appendix only'}, alternative calculations {'on' if pf['alt'] else 'off'}; not a committed file.*\n")
    def root_block(r, R, level):
        best = next((u for u in D["units"] if r in u["bears_on"]), None)
        L.append(f"{'#' * level} {r}")
        L.append(f"- preset {R['preset']}; status **{R['status']}**; weakest proof-set leaf at V {R['weakest_V']} "
                 "(the least-vetted element of the cheapest way to establish the root)")
        if R.get("subframe"):
            S = R["subframe"]
            L.append(f"- a programme (sub-frame): {S['question']}")
            L.append(f"- steps: {', '.join(S['roots'])}; leading step: {S['leading_step'] or 'none has a value yet'}"
                     f"; the programme's value is its best non-conceded step's, or its outside option ({S['outside_option']}) once every step is conceded")
        if R.get("ai_only"):
            L.append(f"- rests on AI numbers (no human judgment yet): {', '.join(R['ai_only'])}")
        if pf["numbers"]:
            whole = "" if D["act"].get("outside_placed") else " (the whole scale while the outside option has no belief)"
            L.append(f"- Pr {frange(R['Pr'])}" + (f"; value {frange(R['value'])}{whole}" if R["value"] else "") + f"; gestalt {fmt((R['gestalt'] or {}).get('mid'))}"
                     + (" (AI gestalt)" if (R["gestalt"] or {}).get("generated") else ""))
            if pf["alt"]:
                L.append(f"- comonotone companion: Pr ≥ {fmt(R['comonotone_Pr'])} under full positive dependence; worst-case status {D['nodes'][r]['status']}")
        if R["status"] == "conceded":
            rev = next((u for u in D["units"] if u["kind"] == "revive" and r in u["bears_on"]), None)
            L.append(f"- diagnosis: {R['diagnosis']}; revival {fmt((R['revival'] or [None])[0])} min ({(R['revival'] or ['', ''])[1]})"
                     + (f"; ranked as revive {rev['target']}" if rev else ""))
        elif R["preset"] == "worst-case":
            L.append(f"- safety margin: {R['margin']} (established proof-set leaves whose concession would concede the root)")
        elif pf["numbers"]:
            L.append(f"- {R['preset']} budget: {'failure mass' if R['preset'] == 'probabilistic' else 'expected loss'} {fmt(R['budget_loss'])} of {fmt(R['budget'])}")
        L.append(f"- load-bearing shared leaves: {', '.join(R['load_bearing']) or 'none'}")
        L.append(f"- best next unit: {best['kind'] + ' ' + best['target'] if best else 'none'}")

    def frame_sections(frame_id, level):
        for role, head in (("plan", "Plans"), ("risk-story", "Risk stories"), ("shared-claim", "Shared claims")):
            rs = [(r, R) for r, R in D["roots"].items() if R["role"] == role and R.get("frame") == frame_id]
            if not rs:
                continue
            L.append(f"{'#' * level} {head}")
            for r, R in rs:
                root_block(r, R, level + 1)
            L.append("")
    frame_sections(None, 2)
    for r, R in D["roots"].items():
        if R.get("subframe"):
            L.append(f"## Sub-frame {r}: {R['subframe']['question']}")
            L.append("")
            frame_sections(r, 3)
    L += ["## Valuation nodes", "The outside option and the undescribed failure, each a cases node over the outcome classes; "
          "weights and conditionals are judgments like any row's.", ""]
    L += (valuation_lines(D) if pf["numbers"] else [f"- {x} ({V['role']}): {'has a value' if V['defined'] else 'no belief'}"
                                                      f"{' (provisional)' if V['provisional'] else ''}" for x, V in (D.get("valuations") or {}).items()]) + [""]
    cols = "| id | kind | V | flags | status | " + ("cost | " if pf["numbers"] else "") + "load |"
    L += ["## Nodes", "", cols, "|" + "---|" * (cols.count("|") - 1)]
    for x, N in D["nodes"].items():
        v = f"{N['V']['display']} ({N['V']['weaker']})"
        L.append(f"| {x} | {N['kind']}{'/' + N['leaf_kind'] if N['leaf_kind'] else ''} | {v} | {', '.join(N['flags'])} | {N['status']} | "
                 + (f"{fmt(N['cost'])} | " if pf["numbers"] else "") + f"{len(N['load'])} |")
    return "\n".join(L) + "\n"


def digest(prev, D):
    if not prev:
        return {}
    flips = [f"{x}: {prev['nodes'][x]['status']} → {N['status']}" for x, N in D["nodes"].items() if x in prev["nodes"] and prev["nodes"][x]["status"] != N["status"]]
    # root statuses include the preset's addition (a budget concession), which the node table does not show
    rflips = [f"root {r}: {prev['roots'][r]['status']} → {R['status']}" + (f" ({R['diagnosis']})" if R["status"] == "conceded" and R["diagnosis"] else "")
              for r, R in D["roots"].items() if r in prev.get("roots", {}) and prev["roots"][r]["status"] != R["status"]]
    moves = [f"{x}: V {prev['nodes'][x]['V']['headline']} → {N['V']['headline']}" for x, N in D["nodes"].items() if x in prev["nodes"] and prev["nodes"][x]["V"]["headline"] != N["V"]["headline"]]
    new = sorted(set(D["events"]["counted"]) - set(prev["events"]["counted"]))
    return {"statuses_flipped": flips, "root_statuses_flipped": rflips, "levels_moved": moves, "events_new": len(new),
            "proposals_awaiting": [p["id"] for p in D.get("proposals", []) if p["status"] == "proposed"]}


POOLED = {"numbers": False, "alt": False, "handle": None}   # how the committed files are always rendered


def committed_files(t, D, today):
    """The four committed files from the plain derivation: identical whatever flags the run was given."""
    prev_path = t.graph / "derived.json"
    prev = None
    if prev_path.is_file():
        try:
            prev = json.loads(prev_path.read_text())
        except json.JSONDecodeError:
            prev = None
    D["digest"] = digest(prev, D)
    D["generated_hash"] = ""
    D["generated_hash"] = sha(dumps(D))
    files = {"derived.json": dumps(D)}
    for name, fn in (("tasks.md", render_tasks), ("view.md", render_view)):
        body = fn(t, D, POOLED, today)
        files[name] = body + f"<!-- generated_hash: {sha(body)} -->\n"
    versions = dict(t.versions)
    for x, n in t.nodes.items():
        hist = versions.get(x) or []
        norm = normalize_statement(n["_statement"])
        if not hist or hist[-1]["version"] != n["version"]:
            hist = hist + [{"version": n["version"], "normalized": norm, "date": str(today)}]
            versions[x] = hist
    vobj = {"generated_hash": "", "nodes": versions}
    vobj["generated_hash"] = sha(json.dumps(vobj, indent=1, sort_keys=True))
    files["versions.json"] = json.dumps(vobj, indent=1, sort_keys=True) + "\n"
    return files


def write_outputs(t, files):
    for name, content in files.items():
        (t.graph / name).write_text(content)


def write_deltas(t, D):
    for p in D.get("proposals", []):
        if not p["had_delta"]:
            path = t.root / p["path"]
            text = path.read_text()
            text = re.sub(r"(## Delta\n)[\s\S]*$", lambda m: m.group(1) + p["delta"] + "\n", text) if "## Delta" in text else text + "\n## Delta\n" + p["delta"] + "\n"
            path.write_text(text)


def personal_render(t, D, pf, today):
    """Task list and view for one user or one scope: printed, never committed."""
    D.setdefault("digest", {})
    return render_tasks(t, D, pf, today) + "\n" + render_view(t, D, pf, today)


# ---------------------------------------------------------------- CLI and self-test
def run(argv):
    ap = argparse.ArgumentParser(prog="checkers.graph", description=__doc__.split("\n\n")[0])
    ap.add_argument("--root", default=".")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--scope")
    ap.add_argument("--as", dest="as_handle")
    ap.add_argument("--why", action="store_true")
    ap.add_argument("--window-dp", action="store_true")
    ap.add_argument("--frontier", type=int, default=0)
    ap.add_argument("--lambda", dest="lam", type=Q, default=None)
    ap.add_argument("--registry")
    ap.add_argument("--dry-run", action="store_true", help="write nothing; print the derivation as JSON on stdout")
    ap.add_argument("--print", dest="print_render", action="store_true", help="write nothing; print the task list and view on stdout")
    ap.add_argument("--out", default=None, help="write the personal render here instead of stdout (a path outside graph/)")
    ap.add_argument("--today", default=None, help="ISO date for the generated files (tests)")
    a = ap.parse_args(argv)
    if a.self_test:
        return 0 if self_test() else 1
    today = _dt.date.fromisoformat(a.today) if a.today else _dt.date.today()
    err = sys.stderr
    personal = bool(a.scope or a.as_handle or a.why or a.lam is not None or a.window_dp or a.frontier)
    try:
        t = load_tree(a.root, a.registry)
        lint(t)
        if a.scope and a.scope not in t.nodes:
            raise Refuse(1, "--scope", f"{a.scope!r} resolves to no node")
        if a.as_handle and not is_handle(t, a.as_handle):
            raise Refuse(5, "--as", f"{a.as_handle!r} is not a mapped handle")
        if a.out and pathlib.Path(a.out).resolve().is_relative_to(t.graph.resolve()):
            raise Refuse(11, "--out", "the personal render is not committed; write it outside graph/")
        D = derive(t, today=today)                      # the plain derivation: what the committed files hold
        files = committed_files(t, D, today)
        P = derive(t, a.scope, a.lam, a.window_dp, a.frontier, today, as_handle=a.as_handle) if personal else D
        if a.dry_run:
            print(dumps(P))
        elif a.print_render:
            print(personal_render(t, P, prefs(t, a.as_handle, a.why) if personal else POOLED, today), end="")
        else:
            write_outputs(t, files)
            write_deltas(t, D)
            if personal:
                text = personal_render(t, P, prefs(t, a.as_handle, a.why), today)
                if a.out:
                    pathlib.Path(a.out).write_text(text)
                else:
                    print(text, end="")
    except Refuse as e:
        print(e, file=err)
        return 1
    for w in t.warnings:
        print(f"WARN {w}", file=err)
    where = "" if not (personal or a.print_render) else (f"; personal render written to {a.out}" if a.out and not (a.dry_run or a.print_render) else "; personal derivation on stdout")
    print(f"OK {len(t.nodes)} nodes, {len(t.events)} events, {len(D['units'])} ranked units; {D['lines']['commit']}"
          f"{'; nothing written (--dry-run)' if a.dry_run else '; nothing written (--print)' if a.print_render else ''}{where}", file=err)
    return 0


def run_quiet(argv):
    """Run the CLI capturing both streams; returns (exit code, stdout, stderr). Used by the tests."""
    import contextlib
    import io
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = run(argv)
    return code, out.getvalue(), err.getvalue()


def synthetic_tree(root, **kw):
    """Write the §7 synthetic graph under `root` (two plan roots, one shared leaf, one cases
    node with a tagged row, one or, one choose, one question leaf, events across two handles).
    Keyword overrides: p_h (range), p_reason (bool), pic_h_author, drop (event ids),
    extra (event lines by ledger), shared_version (int), tweak(fn(nodes dict)), frame/policy text."""
    root = pathlib.Path(root)
    g = root / "graph"
    for d in ("nodes", "events", "proposals"):
        (g / d).mkdir(parents=True, exist_ok=True)
    (root / "chats").mkdir(exist_ok=True)
    programme = kw.get("programme", False)
    frame = kw.get("frame") or f"""question: How does the relationship between humans and AI systems go, and what can we do about it?
classes:
  - {{id: disutility-max, utility: -1, severity: 1, placed_by: "@h1"}}
  - {{id: high-conflict, utility: -0.5, severity: 2, placed_by: "@h1"}}
  - {{id: no-interesting-life, utility: 0, severity: 3, placed_by: "@h1"}}
  - {{id: earth-gone-aliens-remain, utility: 0.5, severity: 4, placed_by: "@h1"}}
  - {{id: utopia, utility: 1, severity: 5, placed_by: "@h1"}}
outside_option: default-trajectory
undescribed_failure: undescribed-failure
valuations: [default-trajectory, undescribed-failure]
bar: 0.5
establishment_level: 8
commit_level: 6
window_minutes: 360
commitment: [{{minutes: 12000, mass: 1, forced_by: placeholder}}]
audit_share: 0.1
dependence: independent
roots:
  - {{id: plan-a, role: plan, preset: worst-case, success_class: utopia}}
  - {{id: plan-b, role: plan, preset: worst-case, success_class: utopia}}
{'  - {id: prog, role: plan, preset: worst-case}' if programme else ''}
"""
    policy = kw.get("policy") or """anchor_rules: "2026-10-02.1"
floor_table: {0: 1, 6: 0.5, 8: 0.3, 10: 0.2, 12: 0.12, 14: 0.08, 16: 0.05, 18: 0.03, 20: 0}
rate_table:
  map-read: {S: 8, M: 25, L: 60, prior: true}
  trace:    {S: 25, M: 60, L: 180, prior: true}
  estimate: {S: 2, M: 5, L: 10, prior: true}
  gestalt:  {S: 2, M: 2, L: 2, prior: true}
  admit:    {S: 5, M: 10, L: 20, prior: true}
  attack:   {S: 30, M: 90, L: 240, prior: true}
  revive:   {S: 30, M: 90, L: 240, prior: true}
task_overhead_minutes: 3
read_error: 0.3
evaluative_words: [good, bad, safe, dangerous, promising, works, succeeds, should, might, probably]
reask_days: 90
time_tested_years: 3
maintainer: "@h1"
handles:
  "@h1": {kind: human, github: "h1-example"}
  "@h2": {kind: human, github: "h2-example"}
  "@ai": {kind: ai, model: "Claude Fable 5.1 (Anthropic)"}
users:
  "@h1": {audits: true, show_numbers: true, alternative_calculations: true, presentation_asked: "2026-09-20"}
  "@h2": {audits: true, show_numbers: false, alternative_calculations: false, presentation_asked: "2026-09-20"}
"""
    pa = kw.get("pic_h_author", "@h2")
    nodes = {
        "plan-a": ("and", "M", {"children": "[shared-leaf, cases-x, choose-c, plan-a.complete]"}, "Plan A reaches its stated end when its four conjuncts hold."),
        "plan-b": ("and", "M", {"children": "[shared-leaf, or-y, q-leaf, plan-b.complete]"}, "Plan B reaches its stated end when its four conjuncts hold."),
        "shared-leaf": ("leaf", "S", {"leaf_kind": "assumption", "attribution": "reconstructed"}, "The expert's estimate of each formula equals the value obtained by resolving the formula's case split."),
        "cases-x": ("cases", "S", {"children": "[cases-x.partition, pic-h, pic-r]",
                                   "rows": "\n  - {picture: pic-h, class: high-conflict, observable: never}\n  - {picture: pic-r, class: undescribed-failure, observable: never, residual: true}"},
                    "The bounded expert's estimates converge within the deployment horizon."),
        "cases-x.partition": ("leaf", "S", {"leaf_kind": "partition"}, "The pictures of cases-x are exclusive and exhaustive."),
        "pic-h": ("leaf", "S", {"leaf_kind": "picture", "author": pa}, "The expert's estimates oscillate and the operators escalate the conflict."),
        "pic-r": ("leaf", "S", {"leaf_kind": "picture", "author": "@h2"}, "The claim fails for a reason not yet described."),
        "choose-c": ("choose", "S", {"children": "[alt-1, alt-2]", "decided_at": "commit", "committed": "none"}, "One expert model is chosen at commitment."),
        "alt-1": ("leaf", "S", {"leaf_kind": "step"}, "The asymptotic-introspection expert model carries the collapse."),
        "alt-2": ("leaf", "M", {"leaf_kind": "step"}, "The exact-introspection expert model carries the collapse."),
        "plan-a.complete": ("leaf", "S", {"leaf_kind": "completeness"}, "No premise beyond the listed conjuncts is needed for plan A."),
        "or-y": ("or", "S", {"children": "[cheap-leaf, dear-leaf]"}, "Either route establishes the intermediate claim of plan B."),
        "cheap-leaf": ("leaf", "S", {"leaf_kind": "assumption"}, "The short route's lemma holds in the toy model."),
        "dear-leaf": ("leaf", "L", {"leaf_kind": "assumption"}, "The long route's theorem holds in the general model."),
        "q-leaf": ("leaf", "S", {"leaf_kind": "question"}, "What policy-level notion of trust does plan B need?"),
        "plan-b.complete": ("leaf", "S", {"leaf_kind": "completeness"}, "No premise beyond the listed conjuncts is needed for plan B."),
        # the two valuation nodes: the outside option over every class, the undescribed failure over every class but the top
        "default-trajectory": ("cases", "S", {"children": "[default-trajectory.partition, dt-disutility-max, dt-high-conflict, dt-no-interesting-life, dt-earth-gone-aliens-remain, dt-utopia]",
                                              "rows": "\n  - {picture: dt-disutility-max, class: disutility-max, observable: never}"
                                                      "\n  - {picture: dt-high-conflict, class: high-conflict, observable: never}"
                                                      "\n  - {picture: dt-no-interesting-life, class: no-interesting-life, observable: never, residual: true}"
                                                      "\n  - {picture: dt-earth-gone-aliens-remain, class: earth-gone-aliens-remain, observable: never}"
                                                      "\n  - {picture: dt-utopia, class: utopia, observable: never}",
                                              "provisional": "true"},
                               "Default-trajectory AI development with no additional safety work lands in one of the named outcome classes."),
        "default-trajectory.partition": ("leaf", "S", {"leaf_kind": "partition"}, "The pictures of default-trajectory are exclusive and exhaustive."),
        "dt-disutility-max": ("leaf", "S", {"leaf_kind": "picture"}, "Under the default trajectory the future is run by a disutility maximizer."),
        "dt-high-conflict": ("leaf", "S", {"leaf_kind": "picture"}, "Under the default trajectory the future is a high-conflict one full of suffering."),
        "dt-no-interesting-life": ("leaf", "S", {"leaf_kind": "picture"}, "Under the default trajectory all interesting life in the reachable universe is eliminated."),
        "dt-earth-gone-aliens-remain": ("leaf", "S", {"leaf_kind": "picture"}, "Under the default trajectory every descendant of Earth is eliminated and interesting aliens remain."),
        "dt-utopia": ("leaf", "S", {"leaf_kind": "picture"}, "Under the default trajectory the future is a utopia to within physical constraints."),
        "undescribed-failure": ("cases", "S", {"children": "[undescribed-failure.partition, uf-disutility-max, uf-high-conflict, uf-no-interesting-life, uf-earth-gone-aliens-remain]",
                                               "rows": "\n  - {picture: uf-disutility-max, class: disutility-max, observable: never}"
                                                       "\n  - {picture: uf-high-conflict, class: high-conflict, observable: never}"
                                                       "\n  - {picture: uf-no-interesting-life, class: no-interesting-life, observable: never, residual: true}"
                                                       "\n  - {picture: uf-earth-gone-aliens-remain, class: earth-gone-aliens-remain, observable: never}",
                                               "provisional": "true"},
                                "A failure of a plan that no filed story describes lands in one of the named outcome classes below utopia."),
        "undescribed-failure.partition": ("leaf", "S", {"leaf_kind": "partition"}, "The pictures of undescribed-failure are exclusive and exhaustive."),
        "uf-disutility-max": ("leaf", "S", {"leaf_kind": "picture"}, "The undescribed failure leaves the future to a disutility maximizer."),
        "uf-high-conflict": ("leaf", "S", {"leaf_kind": "picture"}, "The undescribed failure leaves a high-conflict future full of suffering."),
        "uf-no-interesting-life": ("leaf", "S", {"leaf_kind": "picture"}, "The undescribed failure eliminates all interesting life in the reachable universe."),
        "uf-earth-gone-aliens-remain": ("leaf", "S", {"leaf_kind": "picture"}, "The undescribed failure eliminates every descendant of Earth while interesting aliens remain."),
    }
    if programme:
        # a programme: a frame node as a plan root whose children are its own roots (two plan steps and a shared claim)
        nodes.update({
            "prog": ("frame", "L", {"children": "[step-1, step-2, sc-1]", "question": '"Does the programme reach a bounded analogue of the collapse?"',
                                    "roots": "\n  - {id: step-1, role: plan, preset: worst-case, success_class: utopia}"
                                             "\n  - {id: step-2, role: plan, preset: worst-case, success_class: utopia}"
                                             "\n  - {id: sc-1, role: shared-claim, preset: worst-case}"},
                     "The programme reaches a bounded analogue of the collapse through one of its steps."),
            "step-1": ("leaf", "M", {"leaf_kind": "step"}, "The finite-time step of the programme carries the collapse."),
            "step-2": ("leaf", "L", {"leaf_kind": "step"}, "The legitimacy step of the programme carries the collapse."),
            "sc-1": ("leaf", "S", {"leaf_kind": "assumption"}, "The programme's shared assumption about the teaching channel holds."),
        })
    if kw.get("tweak"):
        kw["tweak"](nodes)
    for nid, (kind, size, extra, st) in nodes.items():
        fm = [f"id: {nid}", f"kind: {kind}"]
        fm += [f"{k}: {v}" for k, v in extra.items() if k != "author"]
        fm += [f'author: "{extra.get("author", "@ai")}"', f"size: {size}", "size_reason: illustrative",
               f"version: {kw.get('shared_version', 1) if nid == 'shared-leaf' else 1}"]
        (g / "nodes" / f"{nid}.md").write_text("---\n" + "\n".join(fm) + "\n---\n## Statement\n" + st + "\n## Source\nillustrative\n## Notes\n\n")
    ph = kw.get("p_h", ["0.5", "0.7"])
    reason = ', "reason": "the conditional follows from the toy bound"' if kw.get("p_reason", True) else ""
    base = '"date": "2026-09-20", "rule": "2026-10-02.1", "via": "chat", "version": 1'
    chk = '"checked": [{"item": "statement factual", "how": "said"}], "not_checked": [{"item": "second source", "how": "said"}]'
    ev = {"h1": [
        f'{{"id": "h1-1", "by": "@h1", {base}, "kind": "map-read", "target": {{"node": "shared-leaf"}}, {chk}, "estimate": [0.6, 0.8]}}',
        f'{{"id": "h1-2", "by": "@h1", {base}, "kind": "trace", "target": {{"node": "shared-leaf"}}, {chk}}}',
        f'{{"id": "h1-3", "by": "@h1", {base}, "kind": "map-read", "target": {{"node": "cheap-leaf"}}, {chk}, "estimate": [0.85, 0.95]}}',
        f'{{"id": "h1-4", "by": "@h1", {base}, "kind": "trace", "target": {{"node": "cheap-leaf"}}, {chk}}}',
        f'{{"id": "h1-5", "by": "@h1", {base}, "kind": "estimate", "target": {{"node": "plan-a.complete"}}, "estimate": [0.9, 1], "reason": "the list is short"}}',
        f'{{"id": "h1-6", "by": "@h1", {base}, "kind": "estimate", "target": {{"node": "alt-1"}}, "estimate": [0.9, 1], "reason": "the toy proof carries"}}',
        f'{{"id": "h1-14", "by": "@h1", {base}, "kind": "estimate", "target": {{"node": "cases-x.partition"}}, "estimate": [1, 1], "reason": "residual row present"}}',
        # the maintainer's rulings on the two valuation nodes: equal weights, conditional 1 on every row
        f'{{"id": "h1-r1", "by": "@h1", {base}, "kind": "rule", "target": {{"node": "default-trajectory"}}, "ref": "ruling 32", '
        '"reason": "equal probability on each of the named outcome classes", "rows": {"dt-disutility-max": {"w": [0.2, 0.2], "p": [1, 1]}, '
        '"dt-high-conflict": {"w": [0.2, 0.2], "p": [1, 1]}, "dt-no-interesting-life": {"p": [1, 1]}, '
        '"dt-earth-gone-aliens-remain": {"w": [0.2, 0.2], "p": [1, 1]}, "dt-utopia": {"w": [0.2, 0.2], "p": [1, 1]}}}',
        f'{{"id": "h1-r2", "by": "@h1", {base}, "kind": "rule", "target": {{"node": "undescribed-failure"}}, "ref": "ruling 32", '
        '"reason": "equal probability on each named class below utopia, since it is a failure", "rows": {"uf-disutility-max": {"w": [0.25, 0.25], "p": [1, 1]}, '
        '"uf-high-conflict": {"w": [0.25, 0.25], "p": [1, 1]}, "uf-no-interesting-life": {"p": [1, 1]}, '
        '"uf-earth-gone-aliens-remain": {"w": [0.25, 0.25], "p": [1, 1]}}}',
    ] + ([
        f'{{"id": "h1-s1", "by": "@h1", {base}, "kind": "estimate", "target": {{"node": "step-1"}}, "estimate": {json.dumps(kw.get("prog_p", [0.3, 0.5]))}, "reason": "the rates exist in the toy"}}',
        f'{{"id": "h1-s2", "by": "@h1", {base}, "kind": "estimate", "target": {{"node": "step-2"}}, "estimate": [0.1, 0.3], "reason": "the schematic theory is young"}}',
    ] if programme else []), "h2": [
        f'{{"id": "h2-7", "by": "@h2", {base}, "kind": "map-read", "target": {{"node": "plan-b.complete"}}, {chk}, "estimate": [1, 1]}}',
        f'{{"id": "h2-8", "by": "@h2", {base}, "kind": "trace", "target": {{"node": "plan-b.complete"}}, {chk}}}',
        f'{{"id": "h2-9", "by": "@h2", {base}, "kind": "estimate", "target": {{"node": "q-leaf"}}, "estimate": [0.85, 0.95], "reason": "the notion is nearly fixed"}}',
        f'{{"id": "h2-10", "by": "@h2", {base}, "kind": "estimate", "target": {{"node": "alt-2"}}, "estimate": [0.5, 0.7], "reason": "exactness is strong"}}',
        f'{{"id": "h2-11", "by": "@h2", {base}, "kind": "estimate", "target": {{"row": ["cases-x", "pic-h"], "field": "w"}}, "estimate": [0.2, 0.4], "reason": "oscillation is the common failure"}}',
        f'{{"id": "h2-12", "by": "@h2", {base}, "kind": "estimate", "target": {{"row": ["cases-x", "pic-h"], "field": "p"}}, "estimate": [{ph[0]}, {ph[1]}]{reason}}}',
        f'{{"id": "h2-13", "by": "@h2", {base}, "kind": "estimate", "target": {{"row": ["cases-x", "pic-r"], "field": "p"}}, "estimate": [0.85, 0.95], "reason": "the residual is thin"}}',
    ]}
    drop = set(kw.get("drop", ()))
    extra = kw.get("extra") or {}
    for led in sorted(set(ev) | set(extra)):
        lines = [l for l in ev.get(led, []) if json.loads(l)["id"] not in drop] + list(extra.get(led, []))
        (g / "events" / f"{led}.jsonl").write_text("\n".join(lines) + "\n")
    (g / "frame.yaml").write_text(frame)
    (g / "policy.yaml").write_text(policy)
    (g / "DESIGN-LOG.md").write_text("# Design log\n\n- 2026-10-02 change @ai — synthetic graph written for the checker's tests\n")
    return root


def self_test():
    """Null inputs must fail; the synthetic graph must derive the §7 facts."""
    import tempfile
    ok = True

    def expect_fail(name, root, rule=None):
        nonlocal ok
        code, out, err = run_quiet(["--root", str(root), "--dry-run"])
        good = code != 0 and (rule is None or f"REFUSE {rule} " in err)
        ok &= good
        print(f"  {'PASS' if good else 'FAIL'}  null input: {name} -> {err.strip().splitlines()[0] if err.strip() else '(no output)'}")
    with tempfile.TemporaryDirectory() as d:
        d = pathlib.Path(d)
        (d / "empty").mkdir()
        expect_fail("empty tree", d / "empty", 12)
        (d / "noframe" / "graph").mkdir(parents=True)
        (d / "noframe" / "graph" / "policy.yaml").write_text("maintainer: \"@h1\"\n")
        expect_fail("missing frame", d / "noframe", 12)
        synthetic_tree(d / "emptyledger")
        (d / "emptyledger" / "graph" / "events" / "h3.jsonl").write_text("\n")
        expect_fail("empty ledger", d / "emptyledger", 5)
        synthetic_tree(d / "template")
        for p in (d / "template" / "graph" / "nodes").glob("*.md"):
            p.unlink()
        expect_fail("untouched template (frame roots resolve to nothing)", d / "template", 1)
        synthetic_tree(d / "syn")
        code, out, err = run_quiet(["--root", str(d / "syn"), "--today", "2026-10-02"])
        D = json.loads((d / "syn" / "graph" / "derived.json").read_text()) if code == 0 else {}
        checks = [("synthetic derives", code == 0),
                  ("stdout is empty and OK is on stderr", out == "" and "OK " in err),
                  ("or-y established, choose-c open, cases-x open, plan-a open", code == 0 and D["nodes"]["or-y"]["status"] == "established"
                   and D["nodes"]["choose-c"]["status"] == "open" and D["nodes"]["cases-x"]["status"] == "open" and D["roots"]["plan-a"]["status"] == "open"),
                  ("residual weight is the remainder 7/10", code == 0 and D["nodes"]["cases-x"]["rows"]["pic-r"]["w"][0] == "7/10"),
                  ("plan-b cost is infinite through the question leaf", code == 0 and D["roots"]["plan-b"]["cost"] == "inf"),
                  ("the outside option is the default-trajectory node's value 0 and the undescribed failure is -1/4",
                   code == 0 and D["act"]["outside_value"] == "0/1" and D["act"]["outside_placed"] and D["valuations"]["undescribed-failure"]["value"]["mid"] == "-1/4"),
                  ("vet cases-x has D > 0 and every unit on another target D = 0", code == 0 and any(
                      Q(u["D"]) > 0 for u in D["units"] if u["kind"] == "vet" and u["target"] == "cases-x") and all(
                      Q(u["D"]) == 0 for u in D["units"] if u["target"] != "cases-x")),
                  ("generated files round-trip", run_quiet(["--root", str(d / "syn"), "--today", "2026-10-02"])[0] == 0)]
        for name, good in checks:
            ok &= bool(good)
            print(f"  {'PASS' if good else 'FAIL'}  synthetic: {name}")
    print("self-test", "PASS" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    sys.exit(run(sys.argv[1:]))
