"""Checker and deriver for the argument map under `graph/`.

Usage:
    python3 -m checkers.graph --root <tree> [--scope ID | --scope X@valid] [--as HANDLE] [--why]
                              [--all] [--window-dp] [--frontier K] [--lambda X]
                              [--registry CLAIMS.md] [--dry-run | --print] [--out PATH]
    python3 -m checkers.graph --self-test

What 0.4 reads beyond 0.3. Node fields: `given: Y` or `given: Y@valid` on a claim leaf or a
table row (a conditional table: the judgment splits into `if-holds` / `if-fails`, or
`p-if-holds` / `p-if-fails` on a row; `class_given` names the failure class per side);
`X@valid` (an `and` read with its assumption and hypothesis leaves held true);
`improves` and `reality` (an improvement claim: an improvement leaf, an `or` over routes
with one `residual: true` route, or a `cases` table of diagnoses), `refinement_of`; leaf
kinds `route`, `improvement`, `task` (with `action`, `who`, optional `work`, `files`) and
`want` (with `want: true`, a human `owner`, optional `filed_from: quote`, a root of role
`want`); `owner` on every frame (frame.yaml included) and `opened: false` on a line not
opened; `work: [{kind, ref}]` pointers (priorities, open, round; `private` is retired and warns); `tag:
choose-one` on an `or` read as a choice. Event kinds `revise` (a human's revision pass)
and `priority` (a want owner's word: high, medium, low, none). Levels count only at the
Statement version they were given against. Inference is exact recursion with cutset
conditioning per formula (rule 13 caps one formula's cutset at MAX_CUTSET_WORLDS
assignments); an `or` reads as a disjunction for belief. The ranking weights each goal's
bits by stake × promise^e in the verdict model and adds the units `improve`, `do`,
`spell-out`, `connect`, ranked `admit`, `re-examine` (and the `reread` price for a revised
node); `tasks.md` prints each unit's path from the top frame, its goals and signals, an
agent-work section and a goal table; `--all` prints every unit, `--why` the numbers.
The 2026-10-05b fix stage: a one-leaf shared claim or risk story is no goal (it counts
through the goals reading it), nor is a root of a frame not opened outside --scope; a shared
claim's stake is scaled by how much of its container's entropy it settles; a structure-suspect
goal gains `suspicion_weight`; `registries` in policy.yaml are read by every derivation; the
digest compares with the derivation at git HEAD; a research section gathers research units.
The 2026-10-20 cleanup: an AI handle writes no estimate or gestalt on a want, its rows or
its fields; a want's promise reads no derived number and the ranking asks for no gestalt on
it; a Source naming private material and a `private` work pointer warn.

The checker reads `graph/` (frame, policy, nodes, events, proposals), refuses
on any rule violation (printed `REFUSE <rule> <path>: <reason>`, exit 1) and
never repairs. When the tree passes it derives every number (levels, beliefs,
statuses, proof sets, costs, loads, probabilities, values, the ranking) and
writes `graph/derived.json`, `graph/tasks.md`, `graph/view.md`,
`graph/versions.json` and the structure-only `graph/index.json`; each generated
file carries a hash of its own content so a hand edit is detected and refused on
the next run. `derived.json` and `index.json` are not committed (ruling F3,
2026-10-23): `.gitignore` excludes them, CI keeps them as artifacts and publishes
the derivation of `main` to the branch `derived`; `versions.json` records each
one's derivation hash so a stale or foreign derivation shows against the commit. Where the tree holds item nodes, the plain run also renders
`PRIORITIES.md` from them (`checkers/priorities_render.py`).

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

Streams. `REFUSE`, `WARN`, `DIGEST` and `OK` lines go to stderr. The generated
files (`derived.json`, `versions.json`, `tasks.md`, `view.md`, `index.json`) are rendered
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
import difflib
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

CHECKER_VERSION = "0.4"
INF = float("inf")
# `frame`: a sub-frame, a programme-shaped plan root whose children are its own roots (steps)
KINDS = {"and", "or", "leaf", "cases", "choose", "frame"}
LEAF_KINDS = {"assumption", "hypothesis", "record", "bridge", "step", "question",
              "picture", "completeness", "partition", "terminal",
              "route", "improvement", "task", "want"}       # route, improvement; task, want
# leaves no check on themselves establishes: a question, a route or improvement claim (realised only through a refinement),
# a task or a want (established by an external event)
NO_CHECK_LEAVES = {"question", "route", "improvement", "task", "want"}
EXACT_KINDS = {"vet", "trace", "revive"}                                            # units observing with error 0 (--window-dp)
RESEARCH_KINDS = {"improve", "do", "re-examine", "spell-out", "connect", "revive"}   # gathered in tasks.md's research section
ROLES = {"plan", "risk-story", "shared-claim", "want"}
PRIORITY_WORDS = {"high": Q(1), "medium": Q(1, 2), "low": Q(1, 4), "none": Q(0)}   # a want's weight; unset reads as medium
WHO = {"human", "agent", "either"}
ACTION_LEAVES = {"task", "question", "step", "hypothesis", "route", "improvement"}   # leaves that may carry action and who
WORK_KINDS = {"priorities", "open", "round", "private", "decision", "foundation"}   # decision: a DECISIONS.md anchor; foundation: an id of state/foundations.json
FILED_FROM = {"quote", "wiki"}     # quote: a want from its owner's public words; wiki: a frame an agent drafted from a wiki page (owner has not confirmed)
_ITEM_ID = re.compile(r"^(\d+|[A-Z]\d+)$")
_DECISION_LINE = re.compile(r"<!-- decision: ([^;\s]+); touches: ([^;]*?)(; status: open)? -->")
PRESETS = {"worst-case", "probabilistic", "expected-utility"}
EVENT_KINDS = {"map-read", "trace", "pass", "estimate", "gestalt", "admit", "classify",
               "identify", "approve", "audit", "withdraw", "external", "retrospective",
               "survey", "rule", "attribution", "revise", "priority"}
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
GENERATED = ("derived.json", "versions.json", "tasks.md", "view.md", "index.json")   # index.json: the structure-only index (M8, 2026-10-22)
UNCOMMITTED = ("derived.json", "index.json")     # written on the plain run, excluded by .gitignore, published to the branch `derived` (F3, 2026-10-23)
DERIVATION_HASH_SKIPS = ("digest", "generated_hash", "audit")    # the derivation hash versions.json records leaves out the digest and the day's audit draw
LAYOUT_FILES = {"frame.yaml", "policy.yaml", "derived.json", "versions.json", "tasks.md",
                "view.md", "PROTOCOL.md", "README.md", "DESIGN-LOG.md",
                "MAP-AS-CANONICAL.md", "SURVEY.md", "index.json"}   # the 2026-10-22 round's two documents and its structure-only index
STALE_TABLE = "leaf became a table"


# rule 10: policy keys read by the ranking, each with its range; (key, lo, hi) with hi None for no upper end
POLICY_RANGES = [("promise_exponent", 0, 2), ("stake_floor", 0, 1), ("others_wants_weight", 0, 1), ("verdict_c", 0, 1),
                 ("verdict_record_floor", 0, 1), ("improve_error", 0, Q(1, 2)), ("do_error", 0, Q(1, 2)),
                 ("structure_suspect_odds", 1, None), ("gestalt_mix", 0, 1), ("also_for_share", 0, 1), ("suspicion_weight", 0, 1)]
INT_POLICY = {"ai_conjunct_threshold": 2, "path_max": 3, "tasks_shown": 1}


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
    node["_item"] = sec.get("Item")          # an item node's transcribed entry (PRIORITIES.md is rendered from it)
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
        self.decisions = {}       # DECISIONS.md anchors: {anchor: {date, title, status, touches}}
        self.rounds = {}          # state/rounds.json: {id or path: record}
        self.foundations = set()  # state/foundations.json ids

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
    t.decisions = load_decisions(t.root / "DECISIONS.md")
    rpath = t.root / "state" / "rounds.json"
    if rpath.is_file():
        try:
            for r in json.loads(rpath.read_text()).get("rounds") or []:
                t.rounds[r["id"]] = r
                if r.get("path"):
                    t.rounds[str(r["path"]).rstrip("/")] = r
        except (json.JSONDecodeError, KeyError, TypeError):
            t.warnings.append("state/rounds.json: not readable; round pointers are checked against directories only")
    fpath = t.root / "state" / "foundations.json"
    if fpath.is_file():
        try:
            t.foundations = {f["id"] for f in json.loads(fpath.read_text()).get("foundations") or []}
        except (json.JSONDecodeError, KeyError, TypeError):
            t.warnings.append("state/foundations.json: not readable; foundation pointers resolve to nothing")
    # the claims registries every derivation reads (`registries:` in policy.yaml, paths from the repository root), plus one a
    # personal run names with --registry; a listed registry that is no file is refused (rule 10), never skipped
    regs = t.policy.get("registries")
    if regs is not None:
        if not isinstance(regs, list) or not all(isinstance(r, str) and r for r in regs):
            raise Refuse(10, "graph/policy.yaml", "registries is a list of CLAIMS.md paths from the repository root")
        for r in regs:
            if not (t.root / r).is_file():
                raise Refuse(10, "graph/policy.yaml", f"registries names {r!r}, which is no file of the repository")
            t.registry = {**(t.registry or {}), **_load_registry(t.root / r)}
    if registry:
        t.registry = {**(t.registry or {}), **_load_registry(registry)}
    return t


def load_decisions(path):
    """The anchors of DECISIONS.md: one machine line per entry, `<!-- decision: <anchor>; touches: <kind:ref, ...>[; status: open] -->`,
    the line after a settled entry's heading or the last line of a queued bullet (ruling M7, 2026-10-22)."""
    out = {}
    if not pathlib.Path(path).is_file():
        return out
    text = pathlib.Path(path).read_text()
    heading = None
    for i, line in enumerate(text.splitlines(), 1):
        m = re.match(r"^### (\d{4}-\d{2}-\d{2}) — (.+)$", line)
        if m:
            heading = (m.group(1), m.group(2).strip())
        d = _DECISION_LINE.search(line)
        if d:
            touches = [x.strip() for x in d.group(2).split(",") if x.strip() and x.strip() != "none"]
            status = "open" if d.group(3) else "settled"
            out[d.group(1)] = {"anchor": d.group(1), "date": heading[0] if heading and status == "settled" else None,
                               "title": heading[1] if heading and status == "settled" else None, "status": status,
                               "touches": [{"kind": x.split(":", 1)[0], "ref": x.split(":", 1)[1]} for x in touches if ":" in x], "line": i}
            if status == "open":
                heading = None
    return out


def _load_registry(path):
    """Statement-of-record classes from a CLAIMS.md. The repository's schema: `### <id>` and one fenced `json` block with
    `class` and `statement_of_record` ({kind: lean, declaration: <fully qualified name>}); each entry is found by its id,
    its declaration, and the declaration's last component where no other entry shares it. The older `id:` / `class:`
    lines are read too."""
    text = pathlib.Path(path).read_text()
    out, last = {}, defaultdict(set)
    for m in re.finditer(r"^### (\S+)[^\n]*\n+```json\n(.*?)\n```", text, re.M | re.S):
        try:
            obj = json.loads(m.group(2))
        except json.JSONDecodeError:
            continue
        cls = obj.get("class")
        if not isinstance(cls, str):
            continue
        out[m.group(1)] = cls
        sor = obj.get("statement_of_record")
        decl = sor.get("declaration") if isinstance(sor, dict) else sor if isinstance(sor, str) else None
        if decl:
            out[decl] = cls
            last[decl.split(".")[-1]].add((decl, cls))
    for short, ds in last.items():
        if len(ds) == 1 and short not in out:
            out[short] = next(iter(ds))[1]
    cur = None
    for line in text.splitlines():
        m = re.match(r"^\s*-?\s*id:\s*(\S+)", line)
        if m:
            cur = m.group(1).strip("`'\"")
        m = re.match(r"^\s*class:\s*(\S+)", line)
        if m and cur and cur not in out:
            out[cur] = m.group(1).strip("`'\"")
    return out


# ---------------------------------------------------------------- helpers
def is_human(t, handle):
    h = (t.policy.get("handles") or {}).get(handle)
    return bool(h) and h.get("kind") == "human"


def is_handle(t, handle):
    return handle in (t.policy.get("handles") or {})


def owners_of(x):
    """A frame's owners: `owner` is one human handle or a list of them (ruling M5, 2026-10-22); a want's is one."""
    o = (x or {}).get("owner")
    if o is None or o == "":
        return []
    return [str(h) for h in o] if isinstance(o, list) else [str(o)]


def all_human(t, handles):
    return bool(handles) and all(isinstance(h, str) and is_human(t, h) for h in handles)


def maintainers(t):
    """The maintainer handles: `maintainer` in policy.yaml is one human handle or a list of them (ruling M1, 2026-10-22)."""
    m = t.policy.get("maintainer")
    if m is None or m == "":
        return []
    return [str(h) for h in m] if isinstance(m, list) else [str(m)]


def narratives_of(x):
    """A node's or the frame's narrative pages: `narrative` is one `wiki/<Page>.md` path or a list of them (2026-10-22)."""
    n = (x or {}).get("narrative")
    if n is None or n == "":
        return []
    return [str(v) for v in n] if isinstance(n, list) else [str(n)]


def classes(t):
    return {c["id"]: c for c in (t.frame.get("classes") or []) if isinstance(c, dict)}


def roots(t):
    return [r for r in (t.frame.get("roots") or []) if isinstance(r, dict)]


def valuations(t):
    """The frame's valuation nodes: `cases` nodes read as distributions over the outcome classes."""
    return [v for v in (t.frame.get("valuations") or []) if isinstance(v, str)]


def all_roots(t, unique=True):
    """Every root entry with the frame it belongs to, as dicts carrying `frame`: None for the top
    frame's roots, the frame node's id for a sub-frame's. A frame node's own roots come before the
    frame node itself, so a programme's steps are derived before the programme. A node may be a root
    of several frames (a shared root, 2026-10-22): with `unique` the first entry in the frame tree's
    order is kept as its home and carries every frame in `frames`; without, every entry is returned."""
    out, seen = [], set()

    def walk(entries, frame_id):
        for r in entries:
            if not isinstance(r, dict):
                continue
            node = t.nodes.get(r.get("id"))
            if node and node.get("kind") == "frame" and r.get("id") not in seen:
                seen.add(r["id"])
                walk(node.get("roots") or [], r["id"])
            e = dict(r, frame=frame_id)
            if e.get("role") == "want" and "preset" not in e:
                e["preset"], e["_implied_preset"] = "worst-case", True   # a want takes the worst-case status rule
            out.append(e)
    walk(roots(t), None)
    if not unique:
        return out
    first, order = {}, []
    for e in out:
        if e["id"] in first:
            first[e["id"]]["frames"].append(e["frame"])
        else:
            e["frames"] = [e["frame"]]
            first[e["id"]] = e
            order.append(e["id"])
    return [first[i] for i in order]


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


GIVEN_LEAF_KINDS = {"assumption", "hypothesis", "bridge", "step", "question", "route", "improvement", "task", "want"}
GIVEN_FIELDS = {"if-holds", "if-fails"}
GIVEN_ROW_FIELDS = {"p-if-holds", "p-if-fails"}


def _check_given_parent(t, path, g, vals):
    """A given parent is a claim: a leaf (not a picture, partition or completeness leaf), an and, an or or a cases node;
    never a frame, a choose or a valuation node. `Y@valid` names an and-shaped argument."""
    base = given_base(g)
    bn = t.nodes[base]
    k = bn.get("kind")
    if k in ("frame", "choose") or base in vals or (k == "leaf" and bn.get("leaf_kind") in ("picture", "partition", "completeness")):
        what = "a valuation node" if base in vals else f"a {bn.get('leaf_kind') or k}"
        raise Refuse(2, path, f"given {g!r} names {what}; a given parent is a claim leaf, an and, an or or a cases node")
    if str(g).endswith("@valid") and k != "and":
        raise Refuse(2, path, f"given {g!r}: @valid names an and-shaped argument (its assumption and hypothesis leaves held true), not a {k}")


def _check_narrative(t, path, x):
    """`narrative` names one or more pages under wiki/ that exist (a protocol extension of 2026-10-22; a missing page is refused)."""
    for page in narratives_of(x):
        if not re.match(r"^wiki/[^/]+\.md$", page) or not (t.root / page).is_file():
            raise Refuse(2, path, f"narrative {page!r} is not a page under wiki/ of this repository")


def given_base(name):
    """A given target with its `@valid` suffix stripped."""
    name = str(name)
    return name[:-len("@valid")] if name.endswith("@valid") else name


def reads(clos, x):
    """Whether a closure reads x: x itself, or the implication `x@valid` (x's truth implies its validity, so x bears on it)."""
    return x in clos or f"{x}@valid" in clos


def given_targets(n):
    """The given targets a node file names: its own `given` and its rows'."""
    out = [n["given"]] if n.get("given") not in (None, "") else []
    out += [r["given"] for r in n.get("rows") or [] if isinstance(r, dict) and r.get("given") not in (None, "")]
    return out


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
    # rule 10: policy values in range (rate rows are minutes; each new key is checked where it is read)
    for kind, row in (po.get("rate_table") or {}).items():
        if not isinstance(row, dict):
            raise Refuse(10, "graph/policy.yaml", f"rate_table.{kind} is a row {{S, M, L, prior}}")
        for size in ("S", "M", "L"):
            v = row.get(size)
            if not isinstance(v, (int, Q)) or isinstance(v, bool) or v < 0:
                raise Refuse(10, "graph/policy.yaml", f"rate_table.{kind}.{size} is a number of minutes, at least 0 (got {v!r})")
    for key, lo, hi in POLICY_RANGES:
        if key in po:
            v = po[key]
            if not isinstance(v, (int, Q)) or isinstance(v, bool) or not (q(lo) <= q(v) and (hi is None or q(v) <= q(hi))):
                raise Refuse(10, "graph/policy.yaml", f"{key} is a number in [{lo}, {'∞' if hi is None else hi}] (got {v!r})")
    for key in INT_POLICY:
        if key in po and (not isinstance(po[key], int) or isinstance(po[key], bool) or po[key] < INT_POLICY[key]):
            raise Refuse(10, "graph/policy.yaml", f"{key} is an integer, at least {INT_POLICY[key]} (got {po[key]!r})")
    # rule 8: frame, classes, valuation nodes (the outside option and the undescribed failure are cases nodes)
    for c in cls.values():
        if c.get("utility") is None:
            raise Refuse(8, "graph/frame.yaml", f"class {c['id']!r} has no utility; an unplaced outcome is a valuation node, not a class")
        if not is_human(t, c.get("placed_by")):
            raise Refuse(8, "graph/frame.yaml", f"class {c['id']!r} has a utility without a human placed_by")
    vals = valuations(t)
    if not roots(t):
        raise Refuse(1, "graph/frame.yaml", "frame names no roots")
    if not all_human(t, owners_of(fr)):
        raise Refuse(2, "graph/frame.yaml", f"the top frame carries owner, a human handle or a list of them (the people whose question it poses), not {fr.get('owner')!r}")
    _check_narrative(t, "graph/frame.yaml", fr)
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
    entries = all_roots(t, unique=False)
    seen = defaultdict(list)
    for r in entries:
        seen[r.get("id")].append(r)
        where = "graph/frame.yaml" if r["frame"] is None else nodes[r["frame"]]["_path"]
        if r.get("role") not in ROLES:
            raise Refuse(2, where, f"unknown role {r.get('role')!r}")
        if r["role"] == "want":
            if not r.get("_implied_preset") or "success_class" in r or "budget" in r:
                raise Refuse(2, where, f"want root {r.get('id')!r} carries no preset, success_class or budget: a want takes the worst-case "
                             "status rule and has no value of its own")
            if r.get("id") in nodes and nodes[r["id"]].get("want") is not True:
                raise Refuse(2, where, f"root {r['id']!r} has role want but its node carries no want: true")
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
    for rid, rs in seen.items():
        if len(rs) > 1:
            # a shared root (2026-10-22): one node listed by several frames that read it, filed once; a want sits in one frame
            # (its placement is its owner's word) and the entries agree on role
            frames = [r["frame"] for r in rs]
            if len(set(frames)) < len(frames):
                raise Refuse(1, "graph/frame.yaml", f"{rid!r} is listed twice as a root of one frame")
            if rs[0].get("role") == "want":
                raise Refuse(1, "graph/frame.yaml", f"want {rid!r} is a root of more than one frame; a want's placement is its owner's word")
            if len({r.get("role") for r in rs}) > 1:
                raise Refuse(1, "graph/frame.yaml", f"{rid!r} is a root of several frames with different roles ({', '.join(str(r.get('role')) for r in rs)})")
    entries = all_roots(t)
    for x in frame_nodes:
        if nodes[x].get("superseded_by"):
            # a retired frame (ruling F4, 2026-10-23): its roots moved to the frame that supersedes it; the file stays as an alias
            if nodes[x]["children"] or nodes[x]["roots"]:
                raise Refuse(2, nodes[x]["_path"], "a retired frame (superseded_by) holds no roots and no children: they moved to the frame that supersedes it")
            continue
        if x not in seen:
            raise Refuse(2, nodes[x]["_path"], "a frame node is a plan root of the top frame or of another frame")
        kids, rids = set(nodes[x]["children"]), {r["id"] for r in nodes[x]["roots"]}
        if kids != rids:
            raise Refuse(2, nodes[x]["_path"], "a frame node's children are exactly its roots")
        if not isinstance(nodes[x].get("question"), str) or not nodes[x]["question"].strip():
            raise Refuse(2, nodes[x]["_path"], "a frame node carries question")
        if not all_human(t, owners_of(nodes[x])):
            raise Refuse(2, nodes[x]["_path"], f"a frame carries owner, a human handle or a list of them (the people whose question it poses), not {nodes[x].get('owner')!r}")
        if nodes[x].get("opened") is False and any(r.get("role") == "plan" for r in nodes[x]["roots"]):
            raise Refuse(2, nodes[x]["_path"], "a frame with opened: false records a line not opened: shared claims and risk stories only, no plan roots")
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
    refs = ("hypotheses", "negation_of", "refines", "committed", "supersedes", "superseded_by", "improves", "refinement_of")
    for n in nodes.values():
        for c in n["children"]:
            if c not in nodes:
                raise Refuse(1, n["_path"], f"child {c!r} resolves to no node")
        for k in refs:
            v = n.get(k)
            if k == "hypotheses" and v is not None:
                # ruling F1 (2026-10-23): a record whose hypotheses nobody has filed by reading says `unread`; the word and a list never mix
                if v == "unread":
                    continue
                if not isinstance(v, list) or "unread" in v:
                    raise Refuse(2, n["_path"], "a record's hypotheses are a list of hypothesis-leaf ids or the word unread, never both")
            for x in (v if isinstance(v, list) else [v] if v not in (None, "none") else []):
                if x not in nodes:
                    raise Refuse(1, n["_path"], f"{k} {x!r} resolves to no node")
        for row in n["rows"] or []:
            if not isinstance(row, dict) or row.get("picture") not in nodes:
                raise Refuse(1, n["_path"], f"row picture {row.get('picture') if isinstance(row, dict) else row!r} resolves to no node")
        for g in given_targets(n):
            if given_base(g) not in nodes:
                raise Refuse(1, n["_path"], f"given {g!r} resolves to no node")
    # cycles over children and given edges (a row's given edge leaves its table; `@valid` stripped)
    state = {}
    succ = {x: list(n["children"]) + [given_base(g) for g in given_targets(n)] for x, n in nodes.items()}

    def visit(x, stack):
        if state.get(x) == 1:
            raise Refuse(1, nodes[x]["_path"], "children and given edges form a cycle: " + " -> ".join(stack + [x]))
        if state.get(x) == 2:
            return
        state[x] = 1
        for c in succ[x]:
            visit(c, stack + [x])
        state[x] = 2
    for x in nodes:
        visit(x, [])
    # attachment (rule 1 as amended): a node is attached when it is a root of some frame or a valuation node, a
    # child of an attached node, or the given parent of an attached node or of a row of an attached table
    has_parent = {c for n in nodes.values() for c in n["children"]}
    root_ids = {r["id"] for r in roots(t)} | set(vals)
    named = sorted(x for x in root_ids if x in has_parent)
    if named:
        raise Refuse(1, "graph/frame.yaml", f"top-frame roots or valuation nodes {named} are named in a children list; a root has no parent")
    attached, stack = set(root_ids), list(root_ids)
    while stack:
        for c in succ[stack.pop()]:
            if c not in attached:
                attached.add(c)
                stack.append(c)
    loose = sorted(x for x in nodes if x not in attached and not nodes[x].get("superseded_by"))
    if loose:
        raise Refuse(1, "graph/frame.yaml", f"nodes attached to nothing: {loose} (a node is a frame root, a valuation node, a child "
                     "of an attached node, or the given parent of one)")
    # rule 2 and 4 per node, rule 3, rule 12 sentences
    plan_support = set()
    step_supports = []            # the supports of the plan roots refine() evaluates one by one (programmes excluded)
    for r in entries:
        if r["role"] == "plan":
            sp = support(t, r["id"])
            plan_support |= sp
            if t.nodes.get(r["id"], {}).get("kind") != "frame":
                step_supports.append((r["id"], sp))
    words = [str(w).casefold() for w in (po.get("evaluative_words") or [])]
    prio_path = t.root / "PRIORITIES.md"
    prio_items = set(re.findall(r"^### (\d+)\.", prio_path.read_text(), re.M)) if prio_path.is_file() else set()
    item_nodes = {}
    for x, n in nodes.items():
        if "item" in n:
            if str(n["item"]) in item_nodes:
                raise Refuse(1, n["_path"], f"item {n['item']!r} is also {item_nodes[str(n['item'])]}; one node per item")
            item_nodes[str(n["item"])] = x
    pointed_decisions = set()
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
            if not n["children"] and kind != "frame":     # a frame may be unspelled: roots [] and children []
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
        # owned wants, task leaves, actions and work pointers
        if n.get("want") is True:
            if not is_human(t, n.get("owner")):
                raise Refuse(2, path, f"a want carries owner, a human handle (whoever wants it), not {n.get('owner')!r}")
            if not x.startswith("want-"):
                raise Refuse(2, path, "a want's id begins want-")
            if kind not in ("leaf", "and", "or", "cases") or (kind == "leaf" and n.get("leaf_kind") != "want"):
                raise Refuse(2, path, "a want is a want leaf while unspelled, or an and, or or cases node once spelled out")
            if not any(r["id"] == x and r["role"] == "want" for r in entries):
                raise Refuse(2, path, "a want is a root, role want, of the frame its filer places it under")
        elif n.get("leaf_kind") == "want":
            raise Refuse(2, path, "a want leaf carries want: true and an owner")
        if "filed_from" in n and n.get("filed_from") not in FILED_FROM:
            raise Refuse(2, path, "filed_from is quote (a want filed from its owner's quoted words) or wiki (a frame an agent drafted from a wiki page)")
        if n.get("filed_from") == "wiki" and kind != "frame":
            raise Refuse(2, path, "filed_from: wiki marks a frame drafted from a wiki page; a want is filed_from: quote")
        _check_narrative(t, path, n)
        if "item" in n:
            # an item node (ruling M6, 2026-10-22): the transcription of one PRIORITIES.md entry, rendered back by checkers/priorities_render.py
            if not isinstance(n["item"], str) or not _ITEM_ID.match(n["item"]):
                raise Refuse(2, path, f"item is the entry's number as a string (\"77\", \"Q1\", \"F3\"), not {n['item']!r}")
            if not x.startswith("item-"):
                raise Refuse(2, path, "an item node's id begins item-")
            for f in ("title", "section"):
                if not isinstance(n.get(f), str) or not n[f].strip():
                    raise Refuse(2, path, f"an item node carries {f}")
            if not isinstance(n.get("maintainer_order"), int) or isinstance(n.get("maintainer_order"), bool):
                raise Refuse(2, path, "an item node carries maintainer_order, an integer (the hand ordering, transcribed)")
            if n.get("dispatchable") not in (True, False):
                raise Refuse(2, path, "an item node carries dispatchable: true or false")
            if n.get("item_status") not in ("open", "closed"):
                raise Refuse(2, path, "an item node carries item_status: open or closed")
            if n.get("_item") is None or not n["_item"].strip():
                raise Refuse(12, path, "an item node carries a '## Item' section with the entry's text")
        elif x.startswith("item-") and "." not in x:
            raise Refuse(2, path, "a node id beginning item- is an item node and carries item (its leaves are item-<n>.<part>)")
        if n.get("leaf_kind") == "task" and (not isinstance(n.get("action"), str) or not n["action"].strip() or "who" not in n):
            raise Refuse(2, path, "a task leaf carries action (one imperative sentence) and who (human, agent or either)")
        if "action" in n or "who" in n:
            if kind != "leaf" or n.get("leaf_kind") not in ACTION_LEAVES or (n.get("leaf_kind") == "hypothesis" and n.get("discharge") != "open"):
                raise Refuse(2, path, "action and who sit on a task leaf or on the open leaf whose settlement the work is "
                             "(a question, step, route, improvement leaf or an open hypothesis)")
            if n.get("who") not in WHO or not isinstance(n.get("action"), str) or not n["action"].strip():
                raise Refuse(2, path, f"action is one imperative sentence and who one of {', '.join(sorted(WHO))} (got who {n.get('who')!r})")
        if "work" in n:
            if not isinstance(n["work"], list) or not all(isinstance(w, dict) and w.get("kind") in WORK_KINDS and w.get("ref") not in (None, "") for w in n["work"]):
                raise Refuse(2, path, f"work is a list of {{kind, ref}} with kind one of {', '.join(sorted(WORK_KINDS))}")
            for w in n["work"]:
                if w["kind"] == "priorities" and not (isinstance(w["ref"], int) and not isinstance(w["ref"], bool)):
                    raise Refuse(2, path, f"work kind priorities refs an integer item number of PRIORITIES.md, not {w['ref']!r}")
                if w["kind"] == "priorities":
                    if item_nodes and str(w["ref"]) not in item_nodes:
                        raise Refuse(1, path, f"work order PRIORITIES #{w['ref']} names no item node (a node carrying item: \"{w['ref']}\")")
                    if not item_nodes and str(w["ref"]) not in prio_items:
                        t.warnings.append(f"{path}: work order PRIORITIES #{w['ref']} has no '### {w['ref']}.' heading in PRIORITIES.md")
                    if "item" in n and str(w["ref"]) == n["item"]:
                        t.warnings.append(f"{path}: an item node's work pointer to its own item is redundant with its item field")
                if w["kind"] == "round" and not (t.root / str(w["ref"])).is_dir() and str(w["ref"]).rstrip("/") not in t.rounds:
                    t.warnings.append(f"{path}: round {w['ref']} is neither a directory of the repository nor a round of state/rounds.json")
                if w["kind"] == "decision":
                    # a pointer to a maintainers' ruling (ruling M7): its ref is the anchor of a DECISIONS.md entry
                    if str(w["ref"]) not in t.decisions:
                        raise Refuse(1, path, f"decision {w['ref']!r} resolves to no anchor of DECISIONS.md")
                    pointed_decisions.add(str(w["ref"]))
                if w["kind"] == "foundation" and str(w["ref"]) not in t.foundations:
                    raise Refuse(1, path, f"foundation {w['ref']!r} resolves to no id of state/foundations.json")
                if w["kind"] == "private":
                    # the public map cites only what a public reader can open (2026-10-20); a warning until the staged
                    # nodes have dropped the kind, then a refusal
                    t.warnings.append(f"{path}: work pointer kind private: the map cites only what a public reader can open")
        if re.search(r"(?<![\w-])private(?![\w-])", n.get("_source") or "", re.I):   # not inside a node id
            t.warnings.append(f"{path}: the Source names private material: the map cites only what a public reader can open")
        # conditional tables: `given` on a claim leaf or a row, naming a claim; `class_given` only beside a `given`
        if n.get("given") not in (None, ""):
            if kind != "leaf" or n.get("leaf_kind") not in GIVEN_LEAF_KINDS:
                raise Refuse(2, path, f"given on a {n.get('leaf_kind') or kind}: only a claim leaf ({', '.join(sorted(GIVEN_LEAF_KINDS))}) or a table row carries given")
        for g in given_targets(n):
            _check_given_parent(t, path, g, vals)
        if n.get("class_given") is not None and n.get("given") in (None, ""):
            raise Refuse(2, path, "class_given without given: the failure class per side needs the edge it is read across")
        for r in n["rows"] or []:
            if r.get("class_given") is not None and r.get("given") in (None, ""):
                raise Refuse(2, path, f"row {r.get('picture')}: class_given without given")
        for cg in [n.get("class_given")] + [r.get("class_given") for r in n["rows"] or []]:
            if cg is None:
                continue
            if not isinstance(cg, dict) or not set(cg) <= {"holds", "fails"}:
                raise Refuse(2, path, "class_given is {holds: <class>, fails: <class>}")
            for side, c in cg.items():
                if c is not None and c not in cls and c not in vals:
                    raise Refuse(10, path, f"class_given {side}: {c!r} names no class or valuation node")
        if kind == "frame":
            for k in ("rows", "leaf_kind", "decided_at", "committed"):
                if n.get(k):
                    raise Refuse(2, path, f"a frame node carries no {k}")
        if (kind == "choose" and n.get("committed", "none") == "none") or (kind == "or" and n.get("tag") == "choose-one"):
            # a choice point is refined per plan; two plans sharing one would be evaluated under one plan's pick (Default
            # until a semantics for shared choices is ruled: refuse, never repair)
            sharing = [rid for rid, sp in step_supports if x in sp]
            if len(sharing) > 1:
                raise Refuse(2, path, f"a choice point ({'uncommitted choose' if kind == 'choose' else 'choose-one or'}) lies in the support of "
                             f"two plan roots ({', '.join(sharing)}); commit it, tag it either-suffices, or file one choice point per plan")
        if kind == "choose":
            if x not in plan_support:
                raise Refuse(2, path, "a choose lies only in a plan root's support closure")
            if n.get("decided_at") not in ("commit", "runtime"):
                raise Refuse(2, path, "a choose carries decided_at (commit | runtime)")
            if n.get("committed", "none") != "none" and n["committed"] not in n["children"]:
                raise Refuse(1, path, "committed names no child")
        # improvement claims: `improves` and `reality` together, on an improvement leaf, an or or a cases node
        if ("improves" in n) != ("reality" in n):
            raise Refuse(2, path, "improves and reality come together (the claim X improved until it reflects R well)")
        if "improves" in n:
            if kind == "frame":
                raise Refuse(2, path, "improves on a frame: an improvement claim is a claim (an improvement leaf, an or over routes, or a cases table)")
            if not (kind in ("or", "cases") or (kind == "leaf" and n.get("leaf_kind") == "improvement")):
                raise Refuse(2, path, f"improves on a {n.get('leaf_kind') or kind}: an improvement claim is an improvement leaf, an or over routes, or a cases table")
            if not isinstance(n.get("reality"), str) or not n["reality"].strip():
                raise Refuse(2, path, "reality is a noun phrase naming the system the improved claim is to hold for")
            if normalize_statement(n["reality"]) not in normalize_statement(n["_statement"]):
                raise Refuse(3, path, f"an improvement claim's Statement names its reality phrase ({n['reality']!r}): "
                             "\"<X> can be improved until it reflects <R> well.\"")
            if kind == "or":
                res = [c for c in n["children"] if nodes[c].get("residual") is True]
                if len(res) != 1 or nodes[res[0]].get("leaf_kind") != "route":
                    raise Refuse(2, path, "an improvement or has exactly one residual route child (a route leaf with residual: true)")
        if kind == "leaf" and n.get("leaf_kind") == "improvement" and "improves" not in n:
            raise Refuse(2, path, "an improvement leaf carries improves (and reality)")
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
    unpointed = [a for a in t.decisions if a not in pointed_decisions]
    if unpointed:
        # one line, not one per entry: the index (graph/index.json, `decisions[].pointed_by`) lists every anchor
        t.warnings.append(f"DECISIONS.md: {len(unpointed)} of {len(t.decisions)} decision anchors have no node pointing at them "
                          f"(first: {', '.join(unpointed[:3])}; every anchor's pointers are in graph/index.json)")
    for a, d in t.decisions.items():
        for tch in d["touches"]:
            if tch["kind"] == "node" and tch["ref"] not in nodes:
                t.warnings.append(f"DECISIONS.md:{d['line']}: touches node {tch['ref']!r}, which is no node")
            if tch["kind"] == "item" and item_nodes and tch["ref"] not in item_nodes:
                t.warnings.append(f"DECISIONS.md:{d['line']}: touches item {tch['ref']!r}, which has no item node")
    improvement_ors = {x for x, n in nodes.items() if "improves" in n and n.get("kind") == "or"}
    in_improvement = set().union(*[support(t, x) for x, n in nodes.items() if "improves" in n] or [set()])
    for x, n in nodes.items():
        if n.get("residual") is True and not (n.get("leaf_kind") == "route" and any(x in nodes[o]["children"] for o in improvement_ors)):
            raise Refuse(2, n["_path"], "residual: true marks the residual route, a route leaf that is a child of an improvement or")
        if n.get("leaf_kind") == "route" and x not in in_improvement:
            raise Refuse(2, n["_path"], "a route leaf lies in the support of an improvement claim (one way to improve it)")
    # the edges from X: a route or improvement claim conditions on X's validity, X, or a claim in X's refinement family
    for x, n in nodes.items():
        if "improves" not in n:
            continue
        X = n["improves"]
        family = {X}
        y = X
        while nodes.get(y, {}).get("refinement_of") and nodes[y]["refinement_of"] not in family:
            y = nodes[y]["refinement_of"]
            family.add(y)
        grown = True
        while grown:
            grown = False
            for z, m in nodes.items():
                if z not in family and m.get("refinement_of") in family:
                    family.add(z)
                    grown = True
        for y in [x] + [c for c in support(t, x) if nodes[c].get("leaf_kind") == "route"]:
            g_ = nodes[y].get("given")
            if g_ not in (None, "") and given_base(g_) not in family:
                t.warnings.append(f"{nodes[y]['_path']}: given {g_} is outside the improved claim's family ({X}, its refinements); "
                                  "a route conditions on X@valid, X or a refinement of X")
    # rule 5, 6, 10: ledgers
    nodeset = set(nodes)
    maints = maintainers(t)
    if not all_human(t, maints):
        raise Refuse(5, "graph/policy.yaml", "maintainer names a human handle or a list of them (rule and survey events are the maintainers')")
    by_ledger = defaultdict(list)
    eids = {e.get("id"): e for e in t.events}
    goal_ids = static_goals(t)
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
        fld = e["target"].get("field") if isinstance(e["target"], dict) else None
        if tk[0] == "node" and fld in GIVEN_FIELDS | {"class-if-holds", "class-if-fails"} and nodes[tk[1]].get("given") in (None, ""):
            raise Refuse(1, path, f"target {tk[1]!r} field {fld}: the node carries no given edge")
        if tk[0] == "row" and fld in GIVEN_ROW_FIELDS | {"class-if-holds", "class-if-fails"} and row.get("given") in (None, ""):
            raise Refuse(1, path, f"target row {list(tk[1:])} field {fld}: the row carries no given edge")
        if tk[0] == "pair" and not set(tk[1:]) <= nodeset:
            raise Refuse(1, path, f"target pair {list(tk[1:])} resolves to no nodes")
        if tk[0] == "proposal" and tk[1] not in {p.get("id") for p in t.proposals}:
            raise Refuse(1, path, f"target proposal {tk[1]!r} resolves to no proposal")
        if tk[0] == "event" and tk[1] not in eids:
            raise Refuse(1, path, f"target event {tk[1]!r} resolves to no event")
        vnode = tk[1] if tk[0] == "node" else tk[2] if tk[0] == "row" else None
        if vnode and isinstance(e.get("version"), int) and e["version"] > nodes[vnode]["version"]:
            raise Refuse(5, path, f"version {e['version']} is above {vnode}'s current version {nodes[vnode]['version']}")
        if e["kind"] == "priority":
            # a want's owner says how much they want it: high, medium, low or none; read by priorities(), not judgments()
            if not is_human(t, e["by"]):
                raise Refuse(5, path, "a priority is a want owner's word; an AI handle writes none")
            if tk[0] != "node" or nodes[tk[1]].get("want") is not True:
                raise Refuse(5, path, "a priority targets a want (a node with want: true)")
            if e["by"] != nodes[tk[1]].get("owner"):
                raise Refuse(5, path, f"a priority on {tk[1]!r} is its owner's ({nodes[tk[1]].get('owner')}) word, not {e['by']}'s")
            if e.get("estimate") not in PRIORITY_WORDS:
                raise Refuse(5, path, f"a priority's estimate is one of {', '.join(PRIORITY_WORDS)}, not {e.get('estimate')!r}")
        if e["kind"] == "revise":
            # a human's revision pass: it produced `version` of the node from an earlier version or a superseded node
            if not is_human(t, e["by"]):
                raise Refuse(5, path, "a revise records a human's revision pass; an AI's redraft is a version bump with no event")
            if tk[0] != "node":
                raise Refuse(5, path, "a revise targets a node")
            fr = e.get("from")
            if not isinstance(fr, dict) or ("version" in fr) == ("node" in fr):
                raise Refuse(5, path, "a revise carries from: {version: n} or from: {node: <old id>}")
            if "version" in fr and not (isinstance(fr["version"], int) and fr["version"] < e["version"]):
                raise Refuse(5, path, f"from.version {fr.get('version')!r} must be below the revise's version {e['version']}")
            if "node" in fr and (fr["node"] not in nodes or nodes[fr["node"]].get("superseded_by") != tk[1]):
                raise Refuse(5, path, f"from.node {fr.get('node')!r} carries no superseded_by naming {tk[1]!r}")
            known = {h["version"] for h in (t.versions.get(tk[1]) or [])} | {nodes[tk[1]]["version"]}
            if e["version"] not in known:
                raise Refuse(5, path, f"version {e['version']} of {tk[1]!r} is in neither versions.json nor the node file")
        if e["kind"] in LEVEL_KINDS and not (e.get("checked") and e.get("not_checked")):
            raise Refuse(5, path, "a level-minting event has non-empty checked and not_checked")
        if e["kind"] == "withdraw" and (tk[0] != "event" or eids[tk[1]]["by"] != e["by"]):
            raise Refuse(5, path, "withdraw names an event by the same handle")
        if e["kind"] in ("rule", "survey") and e["by"] not in maints:
            raise Refuse(5, path, f"{e['kind']} is by a maintainer ({', '.join(maints)})")
        if not is_human(t, e["by"]):
            # an AI handle may write estimates and gestalts (they count at J 0 "generated", with its reasoning in gloss);
            # it mints no level and accepts, approves, tags or identifies nothing
            if e["kind"] in LEVEL_KINDS | {"external", "retrospective", "attribution"}:
                raise Refuse(5, path, "an AI handle mints no vettedness level (levels record who has read what)")
            if e["kind"] in JUDGMENT_KINDS - {"estimate", "gestalt"}:
                raise Refuse(5, path, f"an AI handle writes no {e['kind']}: acceptance and tagging are a human's")
            if e["kind"] in ("estimate", "gestalt") and not str(e.get("gloss") or "").strip():
                raise Refuse(5, path, "an AI handle's judgment carries its reasoning in gloss")
            # a want carries its owner's priority, not a forecast: no AI number on it, its rows or its fields
            if e["kind"] in ("estimate", "gestalt") and vnode and nodes[vnode].get("want") is True:
                raise Refuse(5, path, f"an AI handle writes no {e['kind']} on a want ({vnode!r}): a want carries its owner's priority word, "
                                      "not an AI forecast that it will be met")
        if e["kind"] == "gestalt" and e.get("derived") is not False:
            raise Refuse(5, path, "a gestalt carries derived: false (a holistic judgment, not a derived number)")
        if e["kind"] == "gestalt" and (tk[0] != "node" or tk[1] not in goal_ids):
            raise Refuse(5, path, f"a gestalt targets a goal (a frame root, an improvement claim, a route, a refinement or a want), not {tk[1] if len(tk) > 1 else tk!r}")
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
                if isinstance(fields, dict) and "given" in fields:
                    raise Refuse(2, path, f"rule rows: {pic!r} carries given; an edge is structure in the node file, not a ruling")
                if pic in rowmap and isinstance(fields, dict) and rowmap[pic].get("given") not in (None, "") and "p" in fields:
                    raise Refuse(5, path, f"rule rows: {pic!r} is a given row; a ruling names p-if-holds and p-if-fails, not p")
                allowed = {"w", "p-if-holds", "p-if-fails"} if pic in rowmap and rowmap[pic].get("given") not in (None, "") else {"w", "p"}
                if pic not in rowmap or not isinstance(fields, dict) or not set(fields) <= allowed:
                    raise Refuse(5, path, f"rule rows: {pic!r} is not a row of {tk[1]!r} with {' and '.join(sorted(allowed))} only")
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
    # rule 7: generated files (the two that are not committed are checked on disk when present, F3)
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
        self.frames = [x for x, n in t.nodes.items() if n.get("kind") == "frame" and not n.get("superseded_by")]
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
            tags = [e for e in evs if e["kind"] == "classify" and e["target"].get("field") in (None, "class")]
            # a residual row's failure is valued at the frame's undescribed-failure node unless the row names a class
            C.row_class[key] = tags[-1]["estimate"] if tags else row.get("class") or (C.undescribed if row.get("residual") else None)


LEVELISH_KINDS = {"map-read", "trace", "pass", "external", "retrospective", "survey"}   # the kinds levels() reads for anchors


def _level_of(C, x, evs):
    """Headline level of a node from a set of level events (valid and ref dimensions, anchors 2–18)."""
    t, n = C.t, C.t.nodes[x]
    maints = maintainers(C.t)
    V, display = {}, {}
    for dim in ("valid", "ref"):
        de = [e for e in evs if e.get("dimension", "both") in (dim, "both")]
        if n.get("leaf_kind") == "hypothesis" and n.get("discharge") == "restates-conclusion":
            V[dim] = 0
            continue
        v = 2
        if dim == "valid" and n.get("leaf_kind") == "record":
            sor_cls = None if t.registry is None else t.registry.get(str(n.get("statement_of_record")))
            if t.registry is None:
                C.flags[x].add("registry unchecked")   # anchor 4 needs a claims registry (policy.yaml `registries`); the record caps at 2
            elif sor_cls in ("lean-proved", "enumeration-verified", "witness-checked"):
                v = 4
            elif sor_cls is None:
                C.flags[x].add("not in a claims registry")   # the record caps at 2 until its declaration is registered
            else:
                C.flags[x].add(f"registry class {sor_cls}")
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
                   18: any(e["kind"] == "survey" and e["by"] in maints for e in de)}
        for k in (6, 8, 10, 12, 14, 16, 18):
            if anchors[k]:
                v = k
            else:
                break
        V[dim] = v
        if v == 6 and traces and not complete:
            ins = traces[-1]["installment"]
            display[dim] = f"6–8 ({ins.get('done', 0)}/{ins.get('of', '?')})"
    return V, display


def levels(C):
    """Levels per node. A level-minting event counts toward the headline only at the Statement version it was given
    against (research produces new drafts, so what vetting outputs is seldom itself vetted); the best level earned at an older
    version is kept as V_prior and shown as "read at vk"."""
    t = C.t
    C.V, C.flags = {}, defaultdict(set)
    for x, n in t.nodes.items():
        evs = C.on_node[x]
        for e in evs:
            if e["_status"] == "stale":
                C.flags[x].add("stale" if C.stale_reason.get(e["id"]) != STALE_TABLE else f"stale: {STALE_TABLE}")
        if any(e["_status"] == "withdrawn" and target_key(e["target"]) == ("node", x) for e in t.events):
            C.flags[x].add("withdrawn")
        cur = [e for e in evs if e["kind"] not in LEVELISH_KINDS or e["version"] == n["version"]]
        V, display = _level_of(C, x, cur)
        head = min(V.values())
        weaker = "both" if V["valid"] == V["ref"] else min(V, key=V.get)
        prior = None
        for k in sorted({e["version"] for e in evs if e["kind"] in LEVELISH_KINDS and e["version"] < n["version"]}):
            Vk, _ = _level_of(C, x, [e for e in evs if e["kind"] in LEVELISH_KINDS and e["version"] == k])
            hk = min(Vk.values())
            if hk > head and (prior is None or hk >= prior["level"]):
                prior = {"level": hk, "version": k}
        C.V[x] = {"valid": V["valid"], "ref": V["ref"], "headline": head, "weaker": weaker,
                  "display": display.get(weaker if weaker != "both" else "valid", str(head)), "V_prior": prior}
        if prior:
            C.V[x]["display"] += f" · read at v{prior['version']}: {prior['level']}"
            C.flags[x].add(f"revised since read (v{prior['version']} → v{n['version']})")
        rev = [e for e in evs if e["kind"] == "revise" and e["version"] == n["version"]]
        for e in rev:
            C.flags[x].add(f"human-revised ({e['by']}, v{e['version']})")
        level_now = any(e["kind"] in LEVELISH_KINDS and e["version"] == n["version"] for e in evs)
        C.V[x]["draft"] = ("read" if level_now else "human-revised" if rev else "ai" if not is_human(t, n.get("author")) else "human-authored")
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
        if field in ("class", "pair", "class-if-holds", "class-if-fails"):
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


def priorities(C):
    """Each want's priority word: the latest `priority` event by its owner; unset reads as medium (1/2)."""
    t = C.t
    C.priority = {}
    for x, n in t.nodes.items():
        if n.get("want") is not True:
            continue
        evs = [e for e in C.on_node[x] if e["kind"] == "priority" and e["by"] == n.get("owner")]
        C.priority[x] = evs[-1]["estimate"] if evs else None
        if C.priority[x] == "none":
            C.flags[x].add("disowned by owner")
        if n.get("filed_from") == "quote" and not evs:
            C.flags[x].add("owner has not confirmed")


def priority_value(C, x):
    return PRIORITY_WORDS.get(C.priority.get(x) or "medium")


def structural_paths(C):
    """Every node's structural paths: one {frames, root, chain} per root whose support holds it, frames the
    chain from the top frame to the frame listing that root, chain the shortest children chain (ties by id). A walk."""
    t = C.t

    def fchain(r):
        f = C.roots[r]["frame"]
        return [] if f is None else fchain(f) + [f]
    out = defaultdict(list)
    for r in C.roots:
        frames = ["top"] + fchain(r)
        chains, level = {r: [r]}, [r]
        while level:
            nxt = []
            for x in sorted(level, key=lambda y: chains[y]):
                for c in t.nodes[x]["children"]:
                    if c not in chains:
                        chains[c] = chains[x] + [c]
                        nxt.append(c)
            level = nxt
        for x, ch in chains.items():
            out[x].append({"frames": frames, "root": r, "chain": ch})
    for x in out:
        out[x].sort(key=lambda p: (len(p["chain"]), -len(p["frames"]), p["root"]))   # nearest root first, then the deepest frame
    return out


def row_beliefs(C, x, proposed=False, admitted=None):
    """Per admitted row of a cases node (every row, drafted ones too, when `proposed`): w and p as (mid, width,
    flags); the residual weight is the remainder."""
    t = C.t
    adm = C.admitted if admitted is None else admitted
    out, tot_w, tot_width, missing = {}, Q(0), Q(0), []
    rows = [r for r in t.nodes[x]["rows"] if proposed or adm[(x, r["picture"])]]
    for r in rows:
        key = ("row", x, r["picture"])
        p = C.bel.get((key, "p"))
        w = C.bel.get((key, "w"))
        if r.get("given") not in (None, ""):
            # a given row: its displayed conditional is the mixture of its two sides at the parent's displayed mid
            a, b = C.bel.get((key, "p-if-holds")) or p, C.bel.get((key, "p-if-fails")) or p
            p = None
            if a and b and getattr(C, "E", None) is not None:
                pY = C.E.prob((C.E.target_key(r["given"]),), {}, "mid")
                p = {"mid": a["mid"] * pY + b["mid"] * (1 - pY), "width": max(a["width"], b["width"]),
                     "generated": a.get("generated") or b.get("generated")}
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
            lk = n.get("leaf_kind")
            if lk == "question":
                res = ("open", None)
            elif neg and st(neg)[0] == "established":
                res = ("conceded", neg)
            elif lk in NO_CHECK_LEAVES:
                # a route or improvement leaf is realised only through a refinement; a task or a want is established by an
                # external event (a human points at the commit or file that delivered it, or at the state of affairs)
                if lk in ("task", "want") and any(e["kind"] == "external" and is_human(t, e["by"]) and e["version"] == n["version"]
                                                  for e in C.on_node[x]):
                    res = ("established", None)
            elif C.V[x]["headline"] >= C.est_level:
                res = ("established", None)
        elif kind == "cases":
            part = next(c for c in n["children"] if t.nodes[c].get("leaf_kind") == "partition")
            rb = row_beliefs(C, x)
            rowmap = {r["picture"]: r for r in n["rows"]}
            below8, below = [], []
            for pic, b in rb.items():
                key = ("row", x, pic)
                plain = C.bel.get((key, "p"))
                if rowmap[pic].get("given") not in (None, ""):
                    # the bar test on a given row: the conditional on the side the parent's status settles, else the
                    # mixture at the parent's displayed mid; it concedes only when every judgment it uses is at J 8 or above
                    tg = str(rowmap[pic]["given"])
                    ys = st(given_base(tg))[0]
                    a = C.bel.get((key, "p-if-holds")) or plain
                    bb = C.bel.get((key, "p-if-fails")) or plain
                    if ys == "established" and a:
                        eff, used = a["mid"], [a]
                    elif ys == "conceded" and bb and not tg.endswith("@valid"):
                        eff, used = bb["mid"], [bb]
                    else:
                        eff, used = b["p"][0], [j for j in (a, bb) if j]
                    judged = bool(a and bb) or (ys == "established" and bool(a)) or (ys == "conceded" and bool(bb))
                else:
                    eff, used, judged = b["p"][0], [plain] if plain else [], bool(plain)
                if eff < C.bar and judged:
                    below.append(pic)
                    if all(j.get("J", 0) >= 8 for j in used):
                        below8.append(pic)
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
    if n.get("leaf_kind") in ("route", "improvement"):
        return INF, ["established only through a realised refinement"]
    if n.get("leaf_kind") in ("task", "want"):
        return INF, ["established by an external event"]
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
    if best is None:
        return frozenset(), INF      # a frame with no plan steps yet (unspelled, or a line not opened) has no proof set
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


# ---------------------------------------------------------------- inference (§4): exact recursion with cutset conditioning
# A formula is a node, `X@valid` or a conjunction of nodes. Its sub-DAG runs over `children` and `given` edges
# (an `or` reaches every child, a `choose` its committed or refined child, a frame its plan steps). Variables are
# leaves and `cases` nodes, as before. The variables reached from the formula by two or more distinct edge paths
# form the cutset; a node reached twice whose whole closure is reached only through it collapses to the single
# binary holds(Y), weighted by its own probability. Under each cutset assignment the rest is a forest of
# independent variables, so one upward pass gives the formula's probability and one downward pass the joint
# mass P(x, formula) of every node x in it. Exact under `dependence: independent`; Fractions for every displayed
# number, floats only in the ranking's forecast (pmode "verdict").
OR_READING = "disjunction"  # "cheapest": the landed reading (an `or` counts its proof-set child only), kept for the oracle
MAX_CUTSET_WORLDS = 1 << 15    # rule 13: assignments of one formula's cutset
TRUE_K, FALSE_K, ROOT_K = ("T",), ("F",), ("R",)


def _prod(xs, one):
    out = one
    for x in xs:
        out = out * x
    return out


def h2(p):
    p = float(p)
    return 0.0 if p <= 0 or p >= 1 else -(p * math.log2(p) + (1 - p) * math.log2(1 - p))


class _Dag:
    """The analysed sub-DAG of one formula: post-order, kids, path counts, cutset items, collapsed nodes."""
    __slots__ = ("phi", "extras", "label", "post", "kids", "count", "items", "itemset", "collapsed", "inside",
                 "dyn", "evalpost", "dyntopo", "stattopo", "fixed", "nodes", "vars")


class Infer:
    def __init__(self, C, or_mode=None, admitted=None):
        self.C, self.t = C, C.t
        self.or_mode = or_mode or OR_READING
        self.admitted = C.admitted if admitted is None else admitted
        self.choice = {}            # choose, `choose-one` or and frame id -> the child the evaluation follows
        self._spec, self._dags, self._evals, self._fac, self._rows = {}, {}, {}, {}, {}
        self._sup, self._forceable, self._picks = {}, {}, {}
        self.largest = {}           # formula label -> (assignments, cutset item ids)

    # ---- structure
    def set_choice(self, choice):
        choice = dict(choice)
        if choice != self.choice:
            self.choice = choice
            self._spec = {}

    def sup(self, x):
        s = self._sup.get(x)
        if s is None:
            s = self._sup[x] = frozenset(support(self.t, x))
        return s

    def forceable(self, x):
        """The leaves X@valid holds true: every assumption and hypothesis leaf in X's support."""
        s = self._forceable.get(x)
        if s is None:
            s = self._forceable[x] = frozenset(y for y in self.sup(x) if self.t.nodes[y].get("kind") == "leaf"
                                                and self.t.nodes[y].get("leaf_kind") in ("assumption", "hypothesis"))
        return s

    def key_of(self, x, ctx=None):
        n = self.t.nodes[x]
        if n.get("kind") in ("leaf", "cases"):
            if ctx is not None and n.get("kind") == "leaf" and n.get("leaf_kind") in ("assumption", "hypothesis"):
                return TRUE_K
            return ("v", x)
        if ctx is not None and not (self.forceable(ctx) & self.sup(x)):
            ctx = None
        return ("n", x, ctx)

    def target_key(self, name):
        """A node id, or `X@valid`: X evaluated with its assumption and hypothesis leaves held true."""
        name = str(name)
        if name.endswith("@valid"):
            x = name[:-len("@valid")]
            return ("n", x, x) if self.forceable(x) else self.key_of(x, None)
        return self.key_of(name, None)

    def pick(self, x):
        """The child a choice point follows: committed, refined, the leading step of a frame, else the most probable."""
        n = self.t.nodes[x]
        if n.get("kind") == "choose" and n.get("committed", "none") != "none":
            return n["committed"]
        if x in self.choice:
            return self.choice[x]
        if x in self._picks:
            return self._picks[x]
        kids = plan_children(self.t, x) if n.get("kind") == "frame" else n["children"]
        best = None
        for c in kids:
            p = self.prob((self.key_of(c),), {}, "mid")
            if best is None or p > best[0]:
                best = (p, c)
        self._picks[x] = best[1] if best else None
        return self._picks[x]

    def spec_of(self, key):
        s = self._spec.get(key)
        if s is not None:
            return s
        t = self.t
        if key in (TRUE_K, FALSE_K):
            s = ("const", ())
        elif key[0] == "v":
            x = key[1]
            n = t.nodes[x]
            if n.get("kind") == "leaf":
                s = ("leaf", (self.target_key(n["given"]),) if n.get("given") else ())
            else:
                kids = []
                for r in n.get("rows") or []:
                    if r.get("given"):
                        k = self.target_key(r["given"])
                        if k not in kids:
                            kids.append(k)
                s = ("cases", tuple(kids))
        else:
            x, ctx = key[1], key[2]
            n = t.nodes[x]
            kind = n.get("kind")
            if kind == "and":
                s = ("and", tuple(self.key_of(c, ctx) for c in n["children"]))
            elif kind == "or":
                if self.or_mode == "disjunction" and n.get("tag") == "choose-one":
                    p = self.pick(x)
                    s = ("id", (self.key_of(p, ctx),)) if p else ("or", ())
                else:
                    s = ("or", tuple(self.key_of(c, ctx) for c in n["children"]))
            elif kind == "choose":
                p = self.pick(x)
                s = ("id", (self.key_of(p, ctx),)) if p else ("or", ())
            elif kind == "frame":
                steps = plan_children(t, x)
                if self.or_mode == "cheapest" or not steps:
                    s = ("or", tuple(self.key_of(c) for c in steps))
                else:
                    s = ("id", (self.key_of(self.pick(x)),))
            else:
                s = ("or", ())
        self._spec[key] = s
        return s

    def label_of(self, key):
        if key[0] == "v":
            return key[1]
        if key[0] == "n":
            return key[1] + ("@valid" if key[2] == key[1] else f"[in {key[2]}@valid]" if key[2] else "")
        return {"T": "true", "F": "false", "R": "root"}[key[0]]

    def dag(self, phi, extras=()):
        phi = tuple(dict.fromkeys(phi))
        extras = tuple(k for k in dict.fromkeys(extras) if k not in phi)
        sig = (phi, extras, self.or_mode, tuple(sorted(self.choice.items())))
        d = self._dags.get(sig)
        if d is not None:
            return d
        d = _Dag()
        d.phi, d.extras = phi, extras
        d.label = " ∧ ".join(self.label_of(k) for k in phi) or "true"

        def children(k):
            return phi + extras if k == ROOT_K else self.spec_of(k)[1]
        visited, post, stack = {ROOT_K}, [], [(ROOT_K, iter(children(ROOT_K)))]
        while stack:
            k, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                post.append(k)
                stack.pop()
                continue
            if nxt not in visited:
                visited.add(nxt)
                stack.append((nxt, iter(children(nxt))))
        kids = {k: tuple(dict.fromkeys(children(k))) for k in post}
        parents = defaultdict(set)
        for k in post:
            for c in kids[k]:
                parents[c].add(k)
        topo = post[::-1]
        count = {ROOT_K: 1}
        for k in topo:
            for c in kids[k]:
                count[c] = min(2, count.get(c, 0) + count[k])
        items, collapsed, inside = [], set(), set()
        for k in topo:
            if k == ROOT_K or count[k] < 2 or k in inside or k in (TRUE_K, FALSE_K):
                continue
            if k[0] == "v" and not kids[k]:
                items.append(k)
                continue
            cl, st = {k}, [k]
            while st:
                for c in kids[st.pop()]:
                    if c not in cl and c not in (TRUE_K, FALSE_K):
                        cl.add(c)
                        st.append(c)
            if all(parents[m] <= cl for m in cl if m != k):
                items.append(k)
                collapsed.add(k)
                inside |= cl - {k}
            elif k[0] == "v":
                items.append(k)
        if (1 << len(items)) > MAX_CUTSET_WORLDS:
            raise Refuse(13, "graph/frame.yaml", f"cutset too large: the formula {d.label} reaches {len(items)} shared variables "
                         f"({', '.join(sorted(self.label_of(k) for k in items))}) by two or more paths, {1 << len(items)} assignments, above the "
                         f"per-formula cap {MAX_CUTSET_WORLDS}; remedies: coarsen a table, make a conjunct shared across several of the "
                         "formula's children its own shared-claim root, or move part of it into a sub-frame")
        d.post, d.kids, d.count, d.items, d.itemset, d.collapsed, d.inside = post, kids, count, items, set(items), collapsed, inside
        d.nodes = [k for k in post if k not in (ROOT_K, TRUE_K, FALSE_K)]
        d.vars = sorted({k[1] for k in d.nodes if k[0] == "v"})
        evalpost = [k for k in post if k not in inside]
        dyn = set(items) | {ROOT_K}
        for k in evalpost:
            if k not in dyn and any(c in dyn for c in kids[k]):
                dyn.add(k)
        d.dyn = dyn
        d.evalpost = evalpost
        d.dyntopo = [k for k in evalpost[::-1] if k in dyn and k not in d.itemset and count[k] < 2]
        d.stattopo = [k for k in evalpost[::-1] if k not in dyn and count[k] < 2]
        d.fixed = [k for k in evalpost if k != ROOT_K and count[k] >= 2 and k not in (TRUE_K, FALSE_K)]
        n_assign = 1 << len(items)
        if items and n_assign >= self.largest.get(d.label, (0,))[0]:
            self.largest[d.label] = (n_assign, sorted(self.label_of(k) for k in items))
        self._dags[sig] = d
        return d

    def closure(self, phi_keys):
        """Node ids in a formula's closure: every key of its sub-DAG, plus the partition leaf of each table in it."""
        d = self.dag(tuple(phi_keys))
        out = set()
        for k in d.nodes:
            # a node inside an `X@valid` copy is not the literal node (its truth differs), so it is named by its label
            out.add(k[1] if k[0] == "v" or k[2] is None else self.label_of(k))
            if k[0] == "v" and self.t.nodes[k[1]].get("kind") == "cases":
                out |= {c for c in self.t.nodes[k[1]]["children"] if self.t.nodes[c].get("leaf_kind") == "partition"}
        return out

    def live_closure(self, phi_keys):
        """The closure without the evidence parents no number reads: a `given` edge whose child carries no conditional of its
        own (a leaf with neither if-holds nor if-fails, a row with neither p-if-holds nor p-if-fails) falls back to the plain
        range on both sides, so the parent cannot move the child's number and its lack of a belief blanks nothing."""
        C, t = self.C, self.t
        seen, stack, out = set(), list(phi_keys), set()
        while stack:
            k = stack.pop()
            if k in seen or k in (TRUE_K, FALSE_K):
                continue
            seen.add(k)
            out.add(k[1] if k[0] == "v" or k[2] is None else self.label_of(k))
            kids = list(self.spec_of(k)[1])
            if k[0] == "v":
                n = t.nodes[k[1]]
                if n.get("kind") == "leaf":
                    live = any(C.bel.get((("node", k[1]), f)) for f in ("if-holds", "if-fails"))
                    kids = kids if live else []
                else:
                    out |= {c for c in n["children"] if t.nodes[c].get("leaf_kind") == "partition"}
                    kids = [self.target_key(r["given"]) for r in n.get("rows") or [] if r.get("given")
                            and any(C.bel.get((("row", k[1], r["picture"]), f)) for f in ("p-if-holds", "p-if-fails"))]
            stack.extend(kids)
        return out

    # ---- factors
    def shrink(self, b, x):
        """The verdict model: a judged probability pulled toward 1/2 by its level's floor, inside the ranking only."""
        C = self.C
        p = float(b["mid"])
        c = float(q(C.po.get("verdict_c", Q(1, 5))))
        n = self.t.nodes.get(x) or {}
        if n.get("leaf_kind") == "record" and C.V.get(x, {}).get("valid", 0) >= 4:
            fl = float(q(C.po.get("verdict_record_floor", Q(3, 20))))
        else:
            fl = float(floor_width(C, b.get("level", 0)))
        return 0.5 + (1 - c * fl) * (p - 0.5)

    def _bel_p(self, b, pmode, x):
        if b is None:
            return 0.5 if pmode == "verdict" else Q(1, 2)
        if pmode == "verdict":
            return self.shrink(b, x)
        return {"mid": b["mid"], "lo": b["range"][0], "hi": b["range"][1]}[pmode]

    def leaf_beliefs(self, x):
        """(plain, if-holds, if-fails) beliefs of a leaf; a side without its own judgment falls back to the plain range."""
        C = self.C
        plain = C.bel.get((("node", x), "range"))
        if not self.t.nodes[x].get("given"):
            return plain, plain, plain
        a = C.bel.get((("node", x), "if-holds")) or plain
        b = C.bel.get((("node", x), "if-fails")) or plain
        return plain, a, b

    def lp(self, x, side, pmode):
        k = (x, side, pmode)
        v = self._fac.get(k)
        if v is None:
            plain, a, b = self.leaf_beliefs(x)
            v = self._fac[k] = self._bel_p(plain if side is None else a if side else b, pmode, x)
        return v

    def leaf_class(self, x, side):
        n = self.t.nodes[x]
        cg = n.get("class_given") if isinstance(n.get("class_given"), dict) else {}
        if side is None:
            return None
        tag = self.C.bel.get((("node", x), "class-if-holds" if side else "class-if-fails"))
        if tag:
            return tag["value"]
        return cg.get("holds" if side else "fails")

    def rows(self, x, pmode):
        """Rows of a table for evaluation: (picture, w, p if parent holds, p if it fails, parent key, class if it holds,
        class if it fails). Displayed modes read the admitted rows; the verdict model reads the drafted rows too.
        None: no row has entered (held at 1/2, failing to the outside option)."""
        k = (x, pmode)
        if k in self._rows:
            return self._rows[k]
        C = self.C
        rb = row_beliefs(C, x, proposed=(pmode == "verdict"), admitted=self.admitted)
        out = []
        n = self.t.nodes[x]
        rowmap = {r["picture"]: r for r in n.get("rows") or []}
        for pic, b in rb.items():
            r = rowmap[pic]
            w = float(b["w"][0]) if pmode == "verdict" else b["w"][0]
            ps = []
            for field in (("p-if-holds", "p-if-fails") if r.get("given") else ("p", "p")):
                bel = C.bel.get((("row", x, pic), field)) or C.bel.get((("row", x, pic), "p"))
                ps.append(self._bel_p(bel, pmode, pic) if bel else {"verdict": 0.5, "mid": Q(1, 2), "lo": Q(0), "hi": Q(1)}[pmode])
            cls = b["class"]
            cg = r.get("class_given") if isinstance(r.get("class_given"), dict) else {}
            tags = [C.bel.get((("row", x, pic), f)) for f in ("class-if-holds", "class-if-fails")]
            cT = (tags[0] or {}).get("value") or cg.get("holds") or cls
            cF = (tags[1] or {}).get("value") or cg.get("fails") or cls
            out.append((pic, w, ps[0], ps[1], self.target_key(r["given"]) if r.get("given") else None, cT, cF))
        self._rows[k] = out or None
        return self._rows[k]

    def var_classes(self, x, pmode):
        n = self.t.nodes[x]
        if n.get("kind") == "leaf":
            return {c for c in (self.leaf_class(x, True), self.leaf_class(x, False)) if c} if n.get("given") else set()
        rows = self.rows(x, pmode)
        if rows is None:
            return {self.C.outside}
        return {c for r in rows for c in (r[5], r[6]) if c}

    def no_belief(self, x):
        """Whether a variable's number rests on a placeholder (a leaf or table side with no judgment)."""
        n = self.t.nodes[x]
        if n.get("kind") == "cases":
            rb = row_beliefs(self.C, x, admitted=self.admitted)
            return not rb or any("no belief" in b["p"][2] or "no belief" in b["w"][2] for b in rb.values())
        plain, a, b = self.leaf_beliefs(x)
        return a is None or b is None

    # ---- evaluation
    def local(self, key, kids, pairs, force, pmode):
        one, zero = (1.0, 0.0) if pmode == "verdict" else (Q(1), Q(0))
        if key == ROOT_K:
            nphi = len(kids[0])
            ts = [h + f for h, f in pairs]
            h = _prod([p[0] for p in pairs[:nphi]], one) * _prod(ts[nphi:], one)
            return h, _prod(ts, one) - h
        if key == TRUE_K:
            return one, zero
        if key == FALSE_K:
            return zero, one
        func = self.spec_of(key)[0]
        if func == "and":
            h = _prod([p[0] for p in pairs], one)
            return h, _prod([p[0] + p[1] for p in pairs], one) - h
        if func == "or":
            f = _prod([p[1] for p in pairs], one)
            return _prod([p[0] + p[1] for p in pairs], one) - f, f
        if func == "id":
            return pairs[0]
        x = key[1]
        spec = force.get(x) if force else None
        truth, excl = spec if spec else (None, None)
        if truth == "off":
            return zero, _prod([p[0] + p[1] for p in pairs], one)
        aT = truth is not False
        aF = truth is not True
        if func == "leaf":
            if not pairs:
                p = self.lp(x, None, pmode)
                return (p if aT else zero), ((one - p) if aF else zero)
            hY, fY = pairs[0]
            a, b = self.lp(x, True, pmode), self.lp(x, False, pmode)
            okT = aF and not (excl and self.leaf_class(x, True) in excl)
            okF = aF and not (excl and self.leaf_class(x, False) in excl)
            h = (hY * a + fY * b) if aT else zero
            f = (hY * (one - a) if okT else zero) + (fY * (one - b) if okF else zero)
            return h, f
        # cases
        rows = self.rows(x, pmode)
        ts = [p[0] + p[1] for p in pairs]
        allt = _prod(ts, one)
        if rows is None:
            half = 0.5 if pmode == "verdict" else Q(1, 2)
            okF = aF and not (excl and self.C.outside in excl)
            return (half * allt if aT else zero), (half * allt if okF else zero)
        idx = {k: i for i, k in enumerate(kids)}
        H = F = zero
        for pic, w, pT, pF, pk, cT, cF in rows:
            okT = aF and not (excl and cT in excl)
            okF = aF and not (excl and cF in excl)
            if pk is None:
                H += w * pT * allt
                if okT:
                    F += w * (one - pT) * allt
                continue
            j = idx[pk]
            rest = _prod([ts[i] for i in range(len(ts)) if i != j], one)
            hj, fj = pairs[j]
            H += w * (hj * pT + fj * pF) * rest
            F += w * ((hj * (one - pT) if okT else zero) + (fj * (one - pF) if okF else zero)) * rest
        return (H if aT else zero), F

    def evaluate(self, d, force, pmode, joints=False):
        """(P(formula ∧ R), P(R), joints) where R is the restriction `force` puts on the formula's variables; joints maps
        every key of the sub-DAG to (P(key holds ∧ formula ∧ R), P(key holds ∧ R))."""
        fsig = tuple(sorted((v, force[v]) for v in d.vars if v in force)) if force else ()
        mk = (id(d), fsig, pmode, joints)
        hit = self._evals.get(mk) or (self._evals.get((id(d), fsig, pmode, True)) if not joints else None)
        if hit is not None:
            return hit
        one, zero = (1.0, 0.0) if pmode == "verdict" else (Q(1), Q(0))
        kids = d.kids
        sub = {y: self.evaluate(self.dag((y,)), force, pmode, joints) for y in d.collapsed}
        pairs = {}
        for k in d.evalpost:
            if k not in d.dyn:
                pairs[k] = self.local(k, kids[k] if k != ROOT_K else (d.phi, d.extras), [pairs[c] for c in kids[k]], force, pmode)
        vals = []
        for k in d.items:
            if k in d.collapsed:
                h, t = sub[k][0], sub[k][1]
                vals.append([v for v, m in ((True, h), (False, t - h)) if m != 0])
            else:
                spec = force.get(k[1]) if force else None
                tr = spec[0] if spec else None
                vals.append([True] if tr is True else [False] if tr in (False, "off") else [True, False])
        dynpost = [k for k in d.evalpost if k in d.dyn and k not in d.itemset]
        tot_h, tot_t = zero, zero
        J = defaultdict(lambda: [zero, zero])
        acc = {}

        def kids_arg(k):
            return (d.phi, d.extras) if k == ROOT_K else kids[k]
        for combo in itertools.product(*vals):
            for k, v in zip(d.items, combo):
                pairs[k] = (one, zero) if v else (zero, one)
            for k in dynpost:
                pairs[k] = self.local(k, kids_arg(k), [pairs[c] for c in kids[k]], force, pmode)
            w = one
            for k, v in zip(d.items, combo):
                if k in d.collapsed:
                    w = w * (sub[k][0] if v else sub[k][1] - sub[k][0])
                else:
                    m = self.local(k, kids[k], [pairs[c] for c in kids[k]], force, pmode)
                    w = w * (m[0] if v else m[1])
                if w == 0:
                    break
            if w == 0:
                continue
            hR, fR = pairs[ROOT_K]
            tR = hR + fR
            tot_h += w * hR
            tot_t += w * tR
            if not joints:
                continue
            for k in d.fixed:
                if pairs[k][0] != 0:
                    j = J[k]
                    j[0] += w * hR * pairs[k][0]
                    j[1] += w * tR * pairs[k][0]
            G = {ROOT_K: (one, zero, one, one)}
            for k in d.dyntopo:
                g = G.get(k)
                if g is None:
                    continue
                if k != ROOT_K:
                    j = J[k]
                    j[0] += w * pairs[k][0] * g[0]
                    j[1] += w * pairs[k][0] * g[2]
                self._push(k, kids_arg(k), kids[k], pairs, force, pmode, g, d, G, acc, w, one, zero)
        if joints:
            for k in d.stattopo:
                g = acc.get(k)
                if g is None:
                    continue
                if k != ROOT_K:
                    j = J[k]
                    j[0] += pairs[k][0] * g[0]
                    j[1] += pairs[k][0] * g[2]
                self._push(k, kids_arg(k), kids[k], pairs, force, pmode, g, d, None, acc, one, one, zero)
            for y in d.collapsed:
                hY, tY, JY = sub[y]
                j0, j1 = J[y] if y in J else (zero, zero)
                for x, (a0, a1) in JY.items():
                    c1 = a0 / hY if hY else zero
                    c0 = (a1 - a0) / (tY - hY) if tY != hY else zero
                    J[x] = [c1 * j0 + c0 * (tot_h - j0), c1 * j1 + c0 * (tot_t - j1)]
            Jout = {k: tuple(v) for k, v in J.items()}
        res = (tot_h, tot_t, Jout if joints else None)
        self._evals[mk] = res
        return res

    def _push(self, k, karg, kk, pairs, force, pmode, g, d, G, acc, w, one, zero):
        """Downward step: the outside masses of k's tree children from k's (columns: formula, true). For `and` and `or`
        the partials come from prefix and suffix products (linear in the number of children); other nodes recompute."""
        base = [pairs[c] for c in kk]
        func = self.spec_of(k)[0] if k not in (ROOT_K, TRUE_K, FALSE_K) else None
        fast = func in ("and", "or") and len(kk) > 3
        if fast:
            m = len(base)
            sel = 0 if func == "and" else 1                 # and: products of h; or: products of f
            pre_s, pre_t, suf_s, suf_t = [one] * (m + 1), [one] * (m + 1), [one] * (m + 1), [one] * (m + 1)
            for j in range(m):
                pre_s[j + 1] = pre_s[j] * base[j][sel]
                pre_t[j + 1] = pre_t[j] * (base[j][0] + base[j][1])
            for j in range(m - 1, -1, -1):
                suf_s[j] = suf_s[j + 1] * base[j][sel]
                suf_t[j] = suf_t[j + 1] * (base[j][0] + base[j][1])
        for i, c in enumerate(kk):
            if c in d.inside or d.count.get(c, 0) >= 2 or c in (TRUE_K, FALSE_K):
                continue
            if fast:
                os_, ot = pre_s[i] * suf_s[i + 1], pre_t[i] * suf_t[i + 1]
                if func == "and":       # c holds: h = Πh_others, f = Πt_others − Πh_others; c fails: h = 0, f = Πt_others
                    hT, fT, hF, fF = os_, ot - os_, zero, ot
                else:                   # c holds: h = Πt_others, f = 0; c fails: h = Πt_others − Πf_others, f = Πf_others
                    hT, fT, hF, fF = ot, zero, ot - os_, os_
            else:
                pT = base[:]
                pT[i] = (one, zero)
                hT, fT = self.local(k, karg, pT, force, pmode)
                pF = base[:]
                pF[i] = (zero, one)
                hF, fF = self.local(k, karg, pF, force, pmode)
            gc = (g[0] * hT + g[1] * fT, g[0] * hF + g[1] * fF, g[2] * hT + g[3] * fT, g[2] * hF + g[3] * fF)
            if G is not None and c in d.dyn:
                G[c] = gc
            else:
                a = acc.get(c)
                acc[c] = tuple(w * x for x in gc) if a is None else tuple(a[i2] + w * gc[i2] for i2 in range(4))

    # ---- queries
    def prob(self, phi, force=None, pmode="mid"):
        return self.evaluate(self.dag(tuple(phi)), force or {}, pmode)[0]

    def plan_value(self, rid, base=None, pmode="mid", umode="mid", joints=False, phi=None):
        """A plan's value by class-wise forcing (§4): P(success) at its class, P(fails with worst class c) at c from the
        exclusion passes, the rest at the outside option. Returns (value joint with `base`, passes, classes, success utility)."""
        C = self.C
        base = base or {}
        rk = phi or self.key_of(rid)
        d = self.dag((rk,))
        sup = self.sup(rid)
        bearing = [v for v in d.vars if v in sup and (base.get(v) or (None,))[0] != "off"]
        cls = sorted({c for v in bearing for c in self.var_classes(v, "mid" if pmode != "verdict" else "verdict")},
                     key=lambda c: (utility(C, c), (C.cls.get(c) or {}).get("severity") is None, (C.cls.get(c) or {}).get("severity") or 0))
        passes = []
        for i in range(len(cls) + 1):
            S = frozenset(cls[:i])
            f = dict(base)
            if S:
                for v in bearing:
                    f[v] = ((base.get(v) or (None, None))[0], S)
            passes.append(self.evaluate(d, f, pmode, joints))
        succ = utility(C, C.roots[rid]["success_class"], umode)
        out_u = utility(C, C.outside, umode)
        val = succ * passes[0][0]
        for i, c in enumerate(cls, 1):
            val += utility(C, c, umode) * ((passes[i - 1][1] - passes[i - 1][0]) - (passes[i][1] - passes[i][0]))
        val += out_u * (passes[-1][1] - passes[-1][0])
        return val, passes, cls, succ

    def plan_ev(self, rid, base=None):
        """E(value · [k holds]) and P(k holds) for every key k of a plan's sub-DAG, at midpoints, from the joint masses."""
        C = self.C
        val, passes, cls, succ = self.plan_value(rid, base, "mid", "mid", joints=True)
        out_u = utility(C, C.outside)
        us = [utility(C, c) for c in cls]
        EV, P = {}, {}
        for k in passes[0][2]:
            js = [p[2].get(k, (Q(0), Q(0))) for p in passes]
            ev = succ * js[0][0]
            for i, u in enumerate(us, 1):
                ev += u * ((js[i - 1][1] - js[i - 1][0]) - (js[i][1] - js[i][0]))
            ev += out_u * (js[-1][1] - js[-1][0])
            EV[k], P[k] = ev, js[0][1]
        return val, EV, P


def root_base(C, rid, pset):
    """The landed reading (OR_READING "cheapest"): every closure variable outside the root's proof set is absent."""
    E = C.E
    if E.or_mode != "cheapest":
        return {}
    return {v: ("off", None) for v in E.dag((E.key_of(rid),)).vars if v not in pset}


def root_numbers(C, rid, pset):
    """Pr and value (plan roots) with their intervals, by exact recursion over the root's closure (§4)."""
    E = C.E
    rk = E.key_of(rid)
    base = root_base(C, rid, pset)
    out = {"Pr": {}}
    plan = C.roots[rid]["role"] == "plan" and C.t.nodes[rid].get("kind") != "frame"
    for mode in ("mid", "lo", "hi"):
        out["Pr"][mode] = E.prob((rk,), base, mode)
        if plan:
            out.setdefault("value", {})[mode] = E.plan_value(rid, base, mode, mode)[0]
    vs = pset if E.or_mode == "cheapest" else E.live_closure((rk,))
    out["nobelief"] = sorted(x for x in vs if C.t.nodes.get(x, {}).get("kind") in ("leaf", "cases") and E.no_belief(x))
    if C.t.nodes[rid].get("kind") == "frame" and not plan_children(C.t, rid):
        out["nobelief"] = [rid]      # unspelled or not opened: no probability until a plan step is filed
    return out


def refine(C, rid, status):
    """A plan's refinement path: each uncommitted choose (and, for belief, each `choose-one` or) takes the child of
    highest value; the evaluation then follows those children."""
    t, E = C.t, C.E
    points = [x for x in sorted(E.sup(rid)) if (t.nodes[x].get("kind") == "choose" and t.nodes[x].get("committed", "none") == "none")
              or (E.or_mode == "disjunction" and t.nodes[x].get("kind") == "or" and t.nodes[x].get("tag") == "choose-one")]
    keep = dict(E.choice)
    best = None
    for picks in itertools.product(*[t.nodes[x]["children"] for x in points]):
        choice = dict(zip(points, picks))
        E.set_choice({**keep, **choice})
        pset, cost = proof_set(C, rid, status, {x: c for x, c in choice.items() if t.nodes[x].get("kind") == "choose"})
        nums = root_numbers(C, rid, pset)
        key = nums.get("value", nums["Pr"])["mid"]
        if best is None or key > best[0]:
            best = (key, choice, pset, cost, nums)
    merged = dict(keep)
    for x, c in best[1].items():
        merged.setdefault(x, c)
    E.set_choice(merged)
    return best[1], best[2], best[3], best[4]


def entropy(dist):
    tot = float(sum(dist.values()))
    return -sum((float(p) / tot) * math.log2(float(p) / tot) for p in dist.values() if p > 0) if tot else 0.0


def obs_bits(pg, px, pxg, e):
    """Bits a noisy observation of x's truth (error e) carries about g's truth, from the joint masses (floats)."""
    pg, px, pxg, e = float(pg), float(px), float(pxg), float(e)
    a, b, c = pxg, px - pxg, pg - pxg
    dd = 1 - px - pg + pxg
    eh = 0.0
    for wg, wn in (((1 - e) * a + e * c, (1 - e) * b + e * dd), (e * a + (1 - e) * c, e * b + (1 - e) * dd)):
        tot = wg + wn
        if tot > 1e-15:
            eh += tot * h2(wg / tot)
    return max(0.0, h2(pg) - eh)


STAKE_OVERRIDE = None    # tests only: a number every goal's stake is read as (the weighted-bits regression against the unweighted mid bits)


def static_goals(t):
    """The goal set by structure: every non-frame root of every frame, every improvement claim, every child of an
    improvement `or` (the residual route included) except task leaves, every node carrying refinement_of."""
    out = {r["id"] for r in all_roots(t) if t.nodes.get(r["id"], {}).get("kind") != "frame"}
    for x, n in t.nodes.items():
        if "improves" in n:
            out.add(x)
            if n.get("kind") == "or":
                out |= {c for c in n["children"] if t.nodes[c].get("leaf_kind") != "task"}
        if n.get("refinement_of"):
            out.add(x)
    return out


def has_judgment(C, x):
    """Whether a variable carries any judgment of its own (a leaf range or conditional, a row's weight or conditional)."""
    n = C.t.nodes[x]
    if n.get("kind") == "leaf":
        return any(C.E.leaf_beliefs(x))
    return any((("row", x, r["picture"]), f) in C.bel for r in n.get("rows") or [] for f in ("w", "p", "p-if-holds", "p-if-fails"))


def judgments_ai_only(C, x):
    """Whether every judgment a variable carries is an AI handle's (J 0)."""
    n = C.t.nodes[x]
    if n.get("kind") == "leaf":
        bs = [b for b in C.E.leaf_beliefs(x) if b]
    else:
        bs = [C.bel[k] for r in n.get("rows") or [] for f in ("w", "p", "p-if-holds", "p-if-fails")
              for k in [(("row", x, r["picture"]), f)] if k in C.bel]
    return bool(bs) and all(b.get("generated") for b in bs)


def bare_claim(t, C, x):
    """A shared-claim or risk-story root that is one leaf with no edge of its own: a sentence, not an argument. It is no
    goal in its own right (Default, 2026-10-05b fix stage): its bits count through the goals that read
    it, and one nothing reads is offered to `connect` instead of being ranked for its own entropy."""
    n = t.nodes.get(x) or {}
    return (C.roots.get(x, {}).get("role") in ("shared-claim", "risk-story") and n.get("kind") == "leaf" and not given_targets(n))


def closed_roots(C):
    """The roots under a frame that is not opened (`opened: false`), at any depth: they rank only under --scope."""
    t = C.t
    memo = {}

    def closed(f):
        if f is None:
            return False
        if f not in memo:
            memo[f] = t.nodes[f].get("opened") is False or closed(C.roots.get(f, {}).get("frame"))
        return memo[f]
    return {r for r, rr in C.roots.items() if closed(rr.get("frame")) or (t.nodes[r].get("kind") == "frame" and closed(r))}


def goal_info(C, D, scope, as_handle=None):
    """The goals in scope with their weights (as amended by the 2026-10-05b fix stage): w_g = stake_g · (π̂_g^e + s·[g
    structure suspect]), the verdict-model joints of each goal's pass, and what --why prints about each."""
    t, E = C.t, C.E
    po = C.po
    e_exp = float(q(po.get("promise_exponent", 1)))
    floor = q(po.get("stake_floor", Q(1, 4)))
    others = q(po.get("others_wants_weight", Q(1, 2)))
    susp_w = float(q(po.get("suspicion_weight", Q(1, 2))))
    suspect_odds = q(po.get("structure_suspect_odds", 4))
    static = static_goals(t)
    closed = closed_roots(C) if not scope else set()

    def under_closed(g, seen=()):
        if g in C.roots:
            return g in closed
        if g in seen:
            return False
        rs = [r for r in C.roots if g in E.sup(r)]
        if rs:
            return all(r in closed for r in rs)
        n = t.nodes[g]
        fam = n.get("improves") or n.get("refinement_of")
        return bool(fam) and fam in t.nodes and under_closed(fam, seen + (g,))
    gids = [g for g in C.roots if g in static] + sorted(g for g in static if g not in C.roots)
    gids = [g for g in gids if not bare_claim(t, C, g) and not under_closed(g)]
    sbase = given_base(scope) if scope else None
    sclos = (set(support(t, sbase)) | E.closure((E.target_key(scope),)) | {sbase}) if scope else None
    info = {}
    for g in gids:
        gk = E.key_of(g)
        clos = E.closure((gk,))
        if scope and not (g == sbase or reads(clos, sbase) or g in sclos):
            continue
        n = t.nodes[g]
        role = C.roots.get(g, {}).get("role")
        kind = ("want" if role == "want" else "plan" if role == "plan" else "improvement" if "improves" in n else
                "route" if any("improves" in t.nodes[o] and t.nodes[o].get("kind") == "or" and g in t.nodes[o]["children"] for o in t.nodes)
                else "refinement" if n.get("refinement_of") else role)
        d = E.dag((gk,))
        h, tt, J = E.evaluate(d, root_base(C, g, C.psets[g]) if g in C.roots else {}, "verdict", joints=True)
        blanks = sorted(x for x in E.live_closure((gk,)) if t.nodes.get(x, {}).get("kind") in ("leaf", "cases") and E.no_belief(x))
        info[g] = {"id": g, "kind": kind, "role": role, "key": gk, "closure": clos, "J": J, "P_forecast": h / tt if tt else 0.5,
                   "closure_size": len(clos), "cutset_size": len(d.items), "blanks": blanks}
    # stakes: plans by their utility span, wants by their owner's word, the rest by what reads them
    contains = {g: [h for h in info if h != g and reads(info[h]["closure"], g)] for g in info}

    def sensitivity(g, h):
        """The share of h's entropy that g's truth settles: I(T_g; T_h) / H(T_h) from h's own joints (0 when h is settled)."""
        Ih = info[h]
        hh = h2(Ih["P_forecast"])
        j = Ih["J"].get(E.key_of(g)) or Ih["J"].get(("n", g, g))
        if j is None or hh < 1e-9:
            return 0.0
        return min(1.0, obs_bits(Ih["P_forecast"], j[1], j[0], 0) / hh)

    def family(x):
        """x and its refinements: the claim an improvement serves, in every version filed."""
        return {x} | {y for y, m in t.nodes.items() if m.get("refinement_of") == x}
    stake, rule, src = {}, {}, {}
    out_u = utility(C, C.outside)
    for g, I in info.items():
        if I["kind"] == "plan":
            R = D["roots"].get(g) or {}
            succ = utility(C, C.roots[g]["success_class"])
            pr = (R.get("Pr") or {}).get("mid")
            if R.get("value_defined") and pr is not None and pr < 1:
                # the expected utility of the plan's failure (each failure story's mass at its class, the rest at the outside
                # option): a residual row of small mass moves it a little, never a jump at the first admitted row
                u_fail = (R["value"]["mid"] - succ * pr) / (1 - pr)
                rule[g] = "plan: (U(success) − E[U | failure])/2"
            else:
                u_fail = out_u
                rule[g] = "plan: (U(success) − U(outside))/2 (no derived failure mass)"
            stake[g] = max(Q(0), (succ - min(u_fail, out_u)) / 2)
        elif I["kind"] == "want":
            v = priority_value(C, g)
            if as_handle and t.nodes[g].get("owner") != as_handle:
                v, rule[g] = others * v, f"another owner's want at {others} × priority"
            else:
                rule[g] = f"want: priority {C.priority.get(g) or 'unset (medium)'}"
            stake[g] = v
    rest = [g for g in info if info[g]["kind"] not in ("plan", "want")]
    for g in rest:
        stake[g], rule[g], src[g] = floor, "floor (read by no goal that carries a stake above it)", None
    holders = lambda x: [h for h in contains.get(x, []) if info[h]["kind"] in ("plan", "want")] + ([x] if x in info and info[x]["kind"] in ("plan", "want") else [])
    # a fixed point: stakes only rise from the floor, and an `X@valid` reading lets a container have the smaller closure
    changed = True
    while changed:
        changed = False
        for g in rest:
            I, n = info[g], t.nodes[g]
            cands = []        # (stake, source, rule)
            if I["kind"] in ("risk-story", "shared-claim"):
                for h in contains[g]:
                    sv = sensitivity(g, h)
                    if sv > 0:
                        cands.append((stake[h] * Q(sv).limit_denominator(10 ** 6), h, f"from {h} × sensitivity {sv:.2f}"))
            else:
                # improvement claims, routes and refinements serve a claim: they take the stake of the plans and wants that
                # read the claim's family (unscaled: the improved version matters to them whatever the literal one's truth)
                fam = set()
                if "improves" in n:
                    fam = family(n["improves"])
                elif n.get("refinement_of"):
                    fam = family(n["refinement_of"])
                for h in holders(g):
                    cands.append((stake[h], h, f"read by {h}"))
                verb = "improves" if "improves" in n else "refines"
                for x in sorted(fam):
                    for h in holders(x):
                        cands.append((stake[h], h, f"{verb} {x}, itself a {info[h]['kind']}" if h == x else
                                      f"{verb} {n.get('improves') or n.get('refinement_of')}, whose family ({x}) {h} reads"))
                for o in (o for o in info if info[o]["kind"] == "improvement" and t.nodes[o].get("kind") == "or" and g in t.nodes[o]["children"]):
                    cands.append((stake[o], o, f"a route of {o}"))
            best = max(cands, key=lambda c: (c[0], c[1]), default=None)
            if best is not None and best[0] > stake[g]:
                stake[g], src[g], rule[g] = best[0], best[1], best[2]
                changed = True
    for g, I in info.items():
        if STAKE_OVERRIDE is not None:
            stake[g], rule[g] = q(STAKE_OVERRIDE), "override (tests)"
        gb = C.bel.get((("node", g), "gestalt"))
        vars_ = [x for x in I["closure"] if t.nodes.get(x, {}).get("kind") in ("leaf", "cases")]
        if gb:
            pi, src_, ai = E.shrink(gb, g), "gestalt", bool(gb.get("generated"))
        elif I["kind"] == "want":
            # a want carries its owner's priority, not a forecast: its promise reads no derived number
            pi, src_, ai = 0.5, "a want: priority, not forecast", False
        elif any(has_judgment(C, x) for x in vars_):
            pi, src_ = I["P_forecast"], "derived"
            ai = all(judgments_ai_only(C, x) for x in vars_ if has_judgment(C, x))
        else:
            pi, src_, ai = 0.5, "none", False
        # suspicion (the ideas most in need of a human reader rank early too): a goal whose derived
        # number and gestalt sit structure_suspect_odds apart gains a summand beside its promise, smaller than promise by Default
        odds_ratio = None
        if gb and t.nodes[g].get("kind") in ("and", "or", "cases"):
            pd, pgs = I["P_forecast"], E.shrink(gb, g)
            odds = lambda p: max(p, 1e-12) / max(1 - p, 1e-12)
            odds_ratio = max(odds(pd), odds(pgs)) / min(odds(pd), odds(pgs))
        suspect = odds_ratio is not None and Q(odds_ratio) >= suspect_odds
        I.update({"stake": stake[g], "stake_rule": rule[g], "stake_from": src.get(g), "pi": pi, "pi_source": src_, "rests_on_ai": ai,
                  "odds_ratio": odds_ratio, "suspect": suspect,
                  "H_bits": h2(I["P_forecast"]),
                  "w": float(stake[g]) * ((pi ** e_exp if e_exp else 1.0) + (susp_w if suspect else 0.0)),
                  "P": (D["roots"][g]["Pr"]["mid"] if g in D["roots"] and D["roots"][g].get("Pr_defined") else
                        E.prob((I["key"],), {}, "mid") if g not in D["roots"] else None)})
    return info


def nested_count(info, goals):
    """The largest number of the given goals lying on one chain of nested goals (each in the next one's closure)."""
    goals = sorted((g for g in goals if g in info), key=lambda g: -len(info[g]["closure"]))
    best = {}
    for i, g in enumerate(goals):
        best[g] = 1 + max((best[h] for h in goals[:i] if g in info[h]["closure"]), default=0)
    return max(best.values(), default=0)


def ranking(C, D, scope, lam, window_dp, frontier, as_handle=None):
    """The map term and the decision term of every observation unit (§4, §6).

    The map term is a sum over goals (in this version the non-frame roots of every frame in scope, each
    with weight 1): a unit's bits are Σ_g [H(T_g) − E_o H(T_g | o)], each read in closed form from the
    joint masses P(x, g) of g's own pass. The decision term takes, per plan, the joint masses of value
    and the target from the plan's class-wise passes, so neither costs an enumeration per unit."""
    t, E = C.t, C.E
    rids = list(C.roots)
    sbase = given_base(scope) if scope else None          # `--scope X@valid` scopes to X's roots and the implication's closure
    if scope and sbase not in C.sup:
        C.sup[sbase] = support(t, sbase)
    # a root is in scope when it contains the scope node or lies under it (a programme's steps under the programme)
    in_scope_root = lambda r: scope is None or sbase == r or sbase in C.sup[r] or r in C.sup[sbase]
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

    def best_of(vals):
        best = (outside_u, C.outside)
        for r, v in sub_outside.items():
            if v > best[0]:
                best = (v, f"{r}'s outside option")
        for r in plans:
            v = vals.get(r, const[r])
            if v > best[0]:
                best = (v, r)
        return best
    V_act, cand = best_of({})
    D["act"] = {"V_act": V_act, "cand": cand, "cand_label": label(cand), "outside_value": outside_u,
                "outside_placed": utility_placed(C, C.outside), "outside_option": C.outside,
                "options": {r: D["roots"][r]["option_value"] for r in plans},
                "conceded_plans": {r: D["roots"][r]["diagnosis"] for r in plans_all if r not in plans},
                "plans_without_value": [r for r in plan_roots if not is_frame(r) and D["roots"][r].get("option_value") is None]}
    cheapest = E.or_mode == "cheapest"
    # each root's closure (the landed reading: its proof set)
    rclos = {r: (set(C.psets[r]) if cheapest else E.closure((E.key_of(r),))) for r in rids}
    GI = goal_info(C, D, scope, as_handle)
    goals = list(GI)
    if cheapest:
        for gid in goals:
            if gid in rclos:
                GI[gid]["closure"] = rclos[gid]
    in_scope = (set(C.sup[sbase]) | E.closure((E.target_key(scope),)) | {sbase}) if scope else set(t.nodes)
    cand_vars = {x for gid in goals for x in GI[gid]["closure"] if t.nodes.get(x, {}).get("kind") in ("leaf", "cases")}
    revive_targets = {}
    for r in rids:
        if not in_scope_root(r) or D["roots"][r]["status"] != "conceded":
            continue
        tgt = revive_target(C, r, C.status) if C.status[r][0] == "conceded" else r
        if tgt is not None and tgt in in_scope and (tgt in cand_vars or tgt == r):
            revive_targets.setdefault(tgt, []).append(r)
    revive_targets = {x: sorted(rs) for x, rs in revive_targets.items()}
    for x in sorted(cand_vars):
        if x in in_scope and t.nodes[x].get("kind") == "cases" and C.status[x][0] == "conceded" and x not in revive_targets:
            revive_targets[x] = sorted(r for r in rids if x in rclos[r])
    # the decision term's joint masses, once per plan
    EVs = {}
    for r in plans:
        if D["roots"][r]["value_defined"]:
            val, EV, P = E.plan_ev(r, root_base(C, r, C.psets[r]))
            EVs[r] = (val, EV, P)

    def key_for(x):
        return E.key_of(x)

    def bits_for(x, e, prior=None):
        """Per goal x informs: (goal, bits, weighted bits) of a noisy observation of x's truth, from the goal's own joints.
        A goal that reads x only as the implication `x@valid` has no joint with x's own truth: an observation of x carries
        no bits about it (Default), while the goal still counts x in its scope and `informs`, and observations of x's
        leaves inside the implication carry bits about it as usual."""
        xk = key_for(x)
        out = []
        for gid in goals:
            Gg = GI[gid]
            pg = Gg["P_forecast"]
            if x == gid:
                pp = pg if prior is None else prior
                b = obs_bits(pp, pp, pp, e)
            else:
                j = Gg["J"].get(xk)
                if j is None or x not in Gg["closure"]:
                    continue
                if prior is not None and j[1] > 0 and j[1] < 1:
                    # an observation of an internal goal read at a mixed prior keeps P(goal | x) and P(goal | not x)
                    a1, a0 = j[0] / j[1], (pg - j[0]) / (1 - j[1])
                    b = obs_bits(prior * a1 + (1 - prior) * a0, prior, prior * a1, e)
                else:
                    b = obs_bits(pg, j[1], j[0], e)
            out.append((gid, b, Gg["w"] * b))
        return out

    def D_for(x, e):
        if not plans:
            return None
        xk = key_for(x)
        e = q(e)
        inside = [r for r in EVs if xk in EVs[r][1]]
        if not inside:
            return Q(0)
        px = EVs[inside[0]][2][xk]
        Dv = Q(0)
        for o in (True, False):
            po = (1 - e) * px + e * (1 - px) if o else e * px + (1 - e) * (1 - px)
            if po == 0:
                continue
            vals = {}
            for r in inside:
                val, EV, _ = EVs[r]
                ev1 = EV[xk]
                evo = (1 - e) * ev1 + e * (val - ev1) if o else e * ev1 + (1 - e) * (val - ev1)
                vals[r] = evo / po
            Dv += po * best_of(vals)[0]
        return Dv - V_act

    improve_e = q(C.po.get("improve_error", read_error))
    do_e = q(C.po.get("do_error", read_error))
    mix = float(q(C.po.get("gestalt_mix", Q(1, 2))))
    e_exp = float(q(C.po.get("promise_exponent", 1)))
    units = []

    def bears(x):
        return sorted(r for r in rids if x in rclos[r] or x == r)

    def add(kind, x, mins, why, e, prior=None, extra=None, bearing=None, per=None):
        n = t.nodes[x]
        per = bits_for(x, e, prior) if per is None else per
        bits = sum(b for _, b, _ in per)
        wbits = sum(wb for _, _, wb in per)
        hours = float(overhead + mins) / 60
        ai_num = "AI number" in C.flags.get(x, set())
        if ai_num:
            why = why + ["vet this AI number: the target's judgments rest on AI handles only"]
        Dv = (Q(0) if plans else None) if n.get("kind") == "frame" else D_for(x, e)
        u = unit_record(kind, x, n["size"], mins, bits, wbits, hours, Dv, why, ai_num, bearing or bears(x), per, GI)
        u["section"] = "main"
        u.update(extra or {})
        units.append(u)
        return u

    def attached(w):
        """A want is attached when another goal contains it or shares a node with its closure."""
        cw = GI[w]["closure"] if w in GI else E.closure((E.key_of(w),))
        return any(h != w and (w in GI[h]["closure"] or (cw - {w}) & GI[h]["closure"]) for h in GI)
    for x in sorted(cand_vars | set(revive_targets)):
        if x not in in_scope:
            continue
        n = t.nodes[x]
        lk = n.get("leaf_kind")
        if x in revive_targets:
            mins, w1 = revival(C, x, C.status) if C.status[x][0] == "conceded" else rate(C, "revive", n["size"])
            add("revive", x, mins, [w1, "revive: argue the conceding conditional back above the bar; observes the table's truth"], Q(0),
                bearing=revive_targets[x])
            continue
        if x not in cand_vars or D["nodes"][x]["status"] != "open":
            continue
        prior = C.V[x].get("V_prior")
        reread = bool(prior and prior["level"] >= 6)   # a re-read of a node a human read at an older version
        kinds = []
        if lk not in NO_CHECK_LEAVES:
            v = C.V[x]["headline"]
            kinds = ["vet", "map-read"] if v < 6 else ["trace"] if v < C.est_level else []
        if lk in ("step", "question", "route", "improvement") and "action" not in n:
            kinds.append("improve")
        if "action" in n:
            kinds.append("do")
        if lk == "improvement" or (n.get("want") is True and n.get("kind") == "leaf"):
            kinds = [k for k in kinds if k != "map-read"] + ["spell-out"]     # it replaces the map-read while there are no children
        if n.get("want") is True and not attached(x):
            kinds.append("connect")
        if n.get("kind") == "cases" and any(not C.admitted[(x, r["picture"])] for r in n["rows"]):
            kinds.append("admit")
        for kind in kinds:
            read_row = rate(C, "reread" if reread else "map-read", n["size"])
            extra = None
            if kind == "vet":
                mins = read_row[0] + rate(C, "trace", n["size"])[0]
                why, e = [read_row[1], rate(C, "trace", n["size"])[1]], Q(0)
            elif kind == "map-read":
                mins, why, e = read_row[0], [read_row[1]], read_error
            elif kind == "trace":
                mins, w1 = rate(C, "trace", n["size"])
                why, e = [w1], Q(0)
            elif kind == "improve":
                mins, w1 = rate(C, "improve", n["size"])
                why, e = [w1, "improve: relax an assumption, change the formalism, take an informal direction, or critique and redraft; "
                          "the output is a draft an agent files and the list then ranks for checking"], improve_e
                extra = {"text": f"relax an assumption, change the formalism, take an informal direction, or critique and redraft {x}"}
            elif kind == "do":
                mins, w1 = rate(C, "do", n["size"])
                txt = n["action"] + "".join(f" ({work_text(w)})" for w in n.get("work") or [])
                why, e = [w1, "do: the work itself; its output is a draft"], do_e
                extra = {"text": txt, "who": n.get("who"), "section": "agent" if n.get("who") == "agent" else "main"}
            elif kind in ("spell-out", "connect"):
                mins, w1 = rate(C, "spell-out", n["size"])
                why, e = [w1, ("spell-out: an agent drafts sub-goals and tasks from the repository's own activity; you say which parts stand"
                               if kind == "spell-out" else "connect: an agent proposes edges to the rest of the map (and, for a want "
                               "at the top frame, a sub-frame to move it to); you confirm one or say leave it unattached")], read_error
            else:   # admit, ranked: read the rows of a table with proposed rows and say which enter
                mins, w1 = rate(C, "map-read", n["size"])
                why, e = [w1, f"admit {x}: read the rows and say which enter (the one-word quick admit is in the unranked block)"], read_error
                # an unadmitted table is held at 1/2 with no belief, and that propagates to every root reading it, through
                # children or a judged given edge: say how many roots its admission would give a derived number
                blank = [r for r, R in D["roots"].items() if x in (R.get("nobelief") or [])]
                if blank:
                    extra = {"signals": [f"blanks {len(blank)} root{'s' if len(blank) != 1 else ''} ({', '.join(blank[:3])}"
                                         f"{', …' if len(blank) > 3 else ''})"]}
            if reread and kind in ("vet", "map-read"):
                why = why + [reread_prompt(C, x, prior)]
            add(kind, x, mins, why, e, extra=extra)
    # units on internal targets: connect on a spelled-out want nothing reaches, re-examine (read an argument whole) on
    # every goal of kind and, or or cases carrying both a derived probability and a gestalt, spell-out on an unspelled frame
    for gid, I in GI.items():
        n = t.nodes[gid]
        if n.get("want") is True and n.get("kind") != "leaf" and not attached(gid):
            mins, w1 = rate(C, "spell-out", n["size"])
            add("connect", gid, mins, [w1, "connect: the want has children but no edge to the rest of the map; an agent proposes edges"], read_error)
        gb = C.bel.get((("node", gid), "gestalt"))
        if n.get("kind") in ("and", "or", "cases") and gb:
            # offered even where a leaf of the argument carries no belief (held at 1/2): reading the argument whole is how
            # that leaf gets a number, and the signal says so
            pd, pgs = I["P_forecast"], E.shrink(gb, gid)
            prior_mix = mix * pd + (1 - mix) * pgs
            ratio = I["odds_ratio"]
            mins, w1 = rate(C, "trace", n["size"])
            sig = ([f"structure suspect: derived {float(I['P'] if I['P'] is not None else pd):.2f} against gestalt {float(gb['mid']):.2f}"]
                   if I["suspect"] else [])
            if I["blanks"]:
                sig.append(f"no belief on {', '.join(I['blanks'][:3])}{' …' if len(I['blanks']) > 3 else ''}; the read also prices "
                           f"{'it' if len(I['blanks']) == 1 else 'them'}")
            add("re-examine", gid, mins, [w1, "re-examine: read the analysis as a whole and say whether it holds, or file the structure that "
                                          "reconciles the derived number with the gestalt"], read_error, prior=prior_mix,
                extra={"signals": sig, "odds_ratio": ratio})
    for x, n in t.nodes.items():
        if n.get("kind") == "frame" and not n["children"] and n.get("opened") is not False and not n.get("superseded_by") and (not scope or x in in_scope or x == sbase):
            # an unspelled frame: a read of an agent's draft, valued as a binary stand-in at 1/2 with a plan's stake
            stake_f = (max(utility(C, c) for c in C.cls) - outside_u) / 2 if C.cls else Q(1, 2)
            w = float(stake_f) * (0.5 ** e_exp if e_exp else 1.0)
            b = obs_bits(0.5, 0.5, 0.5, read_error)
            mins, w1 = rate(C, "spell-out", n["size"])
            add("spell-out", x, mins, [w1, "spell-out: an agent drafts the frame's plans and tasks from the repository's own activity; you say which parts stand"],
                read_error, per=[(x, b, w * b)], bearing=[x])
    # a gestalt is ranked first only on a root with no derived probability and no gestalt: it is outside both terms
    # (a programme carries none; its steps do; a want is asked for none, since it carries its owner's priority, not a forecast)
    gest = [{"kind": "gestalt", "target": r, "size": t.nodes[r]["size"], "minutes": rate(C, "gestalt", t.nodes[r]["size"])[0], "bits": None,
             "wbits": None, "rate": None, "D": None, "why": ["no derived probability (a closure leaf carries no judgment) and no gestalt: outside both terms"],
             "bears_on": [r], "for": [], "nested_for": 0, "section": "main"}
            for r in goals if C.bel.get((("node", r), "gestalt")) is None and t.nodes[r].get("want") is not True
            and (not D["roots"][r]["Pr_defined"] if r in D["roots"] else bool(GI[r]["blanks"]))]
    units.sort(key=lambda u: (-(u["rate"] or 0), u["target"]))
    if lam is not None and plans:
        for u in units:
            u["score"] = (u["rate"] or 0) + float(lam) * float(u["D"]) / (float(q(C.fr.get("window_minutes", 360))) / 60)
        units.sort(key=lambda u: (-u["score"], u["target"]))
    if (window_dp or frontier) and plans:
        window_dp_values(C, D, units, plans, const, EVs, best_of, V_act, frontier, rclos)
    for x in D["nodes"]:
        # the goals whose inference reaches the node through children or given edges, and their summed weight
        inf = sorted(gid for gid in goals if x == gid or reads(GI[gid]["closure"], x))
        D["nodes"][x]["informs"] = inf
        D["nodes"][x]["informs_weighted"] = sum(GI[g]["w"] for g in inf)
    D["units"] = gest + units
    D["ranking"] = {"scoped": scope, "weighted_bits": sum(GI[g]["w"] * GI[g]["H_bits"] for g in goals),
                    "promise_exponent": float(q(C.po.get("promise_exponent", 1))),
                    "ordered_by": "score" if lam is not None else "map rate", "lambda": None if lam is None else float(lam),
                    "goals": goals}
    D["goals"] = [{"id": g, "kind": I["kind"], "role": I["role"], "home_root": home_root(C, g, GI), "stake": I["stake"],
                   "stake_rule": I["stake_rule"], "pi": I["pi"], "pi_source": I["pi_source"], "rests_on_ai": I["rests_on_ai"],
                   "P": I["P"], "P_forecast": I["P_forecast"], "H_bits": I["H_bits"], "weight": I["w"],
                   "closure_size": I["closure_size"], "cutset_size": I["cutset_size"], "stake_from": I["stake_from"],
                   "suspect": I["suspect"], "odds_ratio": I["odds_ratio"], "blanks": I["blanks"]} for g, I in GI.items()]
    C.GI = GI
    D["goal_order"] = goal_order(C, GI)
    cands = [(GI[g]["w"] if g in GI else 0.0, g) for g, n in t.nodes.items()
             if (n.get("kind") == "frame" and not n["children"] and n.get("opened") is not False and not n.get("superseded_by")) or (n.get("want") is True and not n["children"])]
    D["spell_out"] = {"count": len(cands), "top": [g for _, g in sorted(cands, key=lambda c: (-c[0], c[1]))[:3]]}
    D["agent_top"] = [f"do {u['target']}" for u in units if u.get("section") == "agent"][:5]
    rank = 0
    for u in D["units"]:
        u["path"] = unit_path(C, u, GI)
        u["path_line"] = path_text(C, u["path"], GI)
        u["signals"] = unit_signals(C, D, u, GI)
        if u.get("section", "main") == "main":
            rank += 1
            u["rank"] = rank           # the unit's place in the main list, as tasks.md numbers it (`--all` prints every one)
    big = sorted(E.largest.items(), key=lambda kv: (-kv[1][0], kv[0]))[:5]
    D["inference"] = {"cap": MAX_CUTSET_WORLDS, "dependence": C.fr.get("dependence", "independent"), "or_reading": E.or_mode,
                      "largest": [{"phi": k, "cutset": v[1], "assignments": v[0]} for k, v in big]}
    # regime and commit lines
    reorder = sum(1 for i, u in enumerate(sorted(units, key=lambda u: (-(float(u["D"]) if u["D"] is not None else 0), -(u["rate"] or 0)))) if units and u is not units[i])
    conceded_txt = "; ".join(f"{label(r)} conceded by {D['roots'][r]['diagnosis']}" for r in plans_all if r not in plans)
    novalue = D["act"]["plans_without_value"]
    ranked_index = {(u["kind"], u["target"]): i for i, u in enumerate([u for u in gest + units if u.get("section", "main") == "main"], 1)}
    revivals = sorted({u["target"] for u in units if u["kind"] == "revive"})
    revival_txt = "; ".join(f"revive {x}: ranked unit {ranked_index[('revive', x)]}" for x in revivals) or "no revive unit in scope"
    if not plan_roots:
        regime = "no plan in scope; the decision term is suspended; the order is the map's"
    elif not plans_all and not novalue:
        regime = "no plan step in scope (only programmes); the decision term is suspended; the order is the map's"
    elif not plans_all:
        regime = "no plan in scope has a value yet (no belief on every plan and step); the decision term is suspended; the order is the map's"
    elif not plans:
        regime = f"every plan in scope is conceded ({conceded_txt}); the decision term is suspended; the order is the map's"
    elif all((u["D"] or 0) == 0 for u in units):
        reason = ("one plan whose failure stories name no class below the outside option" if len(plans) == 1 and not any(
            D["roots"][r]["failure_classes_below_outside"] for r in plans) else "the leading plan leads in every world")
        regime = f"no unit can change the act ({reason}); the order is the map's"
    else:
        maxD0 = max((u["D"] for u in units if u["D"] is not None), default=Q(0))
        regime = f"the decision term would reorder {reorder} units (largest D {float(maxD0):.2g}); shown, not applied"
    maxD = max((u["D"] for u in units if u["D"] is not None), default=Q(0))
    commit_level = int(C.fr.get("commit_level", 6))
    if not plan_roots:
        commit = "suspended: no plan in scope"
    elif not plans_all and not novalue:
        commit = "suspended: no plan step in scope (the plan roots in scope are programmes, valued through their steps)"
    elif not plans_all:
        commit = f"suspended: no plan has a value yet (no belief on {', '.join(label(r) for r in novalue)}; a gestalt on a step or plan would give one)"
    elif not plans:
        commit = f"no non-conceded plan to commit to ({conceded_txt}); the outside option stands until a revival ({revival_txt})"
    elif maxD > 0:
        human = [u for u in units if u.get("section", "main") == "main"] or units
        top = next((u for u in human if u["D"] and u["D"] > 0), next((u for u in units if u["D"] and u["D"] > 0), units[0]))
        rk = ranked_index.get((top["kind"], top["target"]))
        commit = (f"research first: the decision term (printed, not applied) favours {top['kind']} {top['target']}"
                  f"{f' (ranked unit {rk})' if rk else ' (Agent work)'}, D {float(top['D']):.2g}")
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
    # what the act rests on: the leading option, its value, whether that value is AI-only, and a gestalt that disagrees
    act_txt = None
    if plans and cand in D["roots"]:
        R = D["roots"][cand]
        bits_ = [f"the act's leading option is {label(cand)} at value {float(V_act):.3f}"]
        if R.get("ai_only"):
            bits_.append("resting on AI numbers only")
        gg = R.get("gestalt")
        if gg and R.get("Pr_defined") and abs(float(gg["mid"]) - float(R["Pr"]["mid"])) >= 0.2:
            bits_.append(f"derived P {float(R['Pr']['mid']):.3f} against its gestalt {float(gg['mid']):.2f}")
        act_txt = "; ".join(bits_)
    elif plans:
        act_txt = f"the act's leading option is {label(cand)} at value {float(V_act):.3f}"
    D["lines"] = {"commit": commit, "regime": regime, "act": act_txt,
                  "scoped": f"scoped: bits about the goals under {scope} only" if scope else None}


def reread_prompt(C, x, prior):
    """What a re-read after a revision asks: the items checked at the older version and the Statement's diff."""
    t = C.t
    checked = sorted({str(c.get("item")) for e in C.on_node[x] if e["kind"] in LEVEL_KINDS and e["version"] == prior["version"]
                      for c in e.get("checked") or [] if isinstance(c, dict)})
    hist = {h["version"]: h["normalized"] for h in t.versions.get(x) or []}
    old, new = hist.get(prior["version"], ""), normalize_statement(t.nodes[x]["_statement"])
    diff = [w for w in difflib.ndiff(old.split(), new.split()) if w[:1] in "+-"]
    return (f"re-read: at v{prior['version']} you checked {', '.join(checked) or 'nothing listed'}; "
            f"the Statement changed in: {' '.join(diff) or 'no recorded wording (versions.json has no earlier text)'}")


def unit_record(kind, x, size, mins, bits, wbits, hours, Dv, why, ai_num, bears_on, per, GI):
    """A ranked unit: its weighted bits per goal (`for`, largest share first), how many of those goals nest, D beside."""
    tot = sum(wb for _, _, wb in per)
    fl = sorted(({"goal": g, "bits": b, "wbits": wb, "share": (wb / tot if tot else 0.0)} for g, b, wb in per if b > 0),
                key=lambda f: (-f["wbits"], f["goal"]))
    return {"kind": kind, "target": x, "size": size, "minutes": mins, "bits": bits, "wbits": wbits,
            "rate": wbits / hours if hours else 0.0, "D": Dv, "why": why, "ai_number": ai_num, "bears_on": bears_on,
            "for": fl, "nested_for": nested_count(GI, [f["goal"] for f in fl])}


def _hops(C, a, b, given_ok):
    """The shortest chain from a down to b over children (→) and, where allowed, given edges (⇢); ties by id."""
    t = C.t
    if a == b:
        return []
    prev, level = {a: None}, [a]
    while level and b not in prev:
        nxt = []
        for x in sorted(level):
            n = t.nodes[x]
            succ = [(c, "→") for c in n["children"]]
            if given_ok:
                succ += [(given_base(g), "⇢") for g in given_targets(n)]
            for c, edge in sorted(succ, key=lambda s: (s[0], s[1])):
                if c not in prev and c in t.nodes:
                    prev[c] = (x, edge)
                    nxt.append(c)
        level = nxt
    if b not in prev:
        return None
    out, y = [], b
    while prev[y] is not None:
        x, edge = prev[y]
        out.append({"id": y, "edge": edge})
        y = x
    return out[::-1]


def unit_path(C, u, GI):
    """A unit's path: the top frame and the frame chain of its top-share goal's home root, the root, the
    nodes down to the goal, then down to the target (support chain if the target is in the goal's support, else over
    children and given edges). Each element is {id, edge}, edge the hop into it: → support or frame, ⇢ evidence."""
    t = C.t
    x = u["target"]
    g = u["for"][0]["goal"] if u.get("for") else (x if x in GI else None)
    r = home_root(C, g, GI) if g else (x if x in C.roots else None)
    if r is None:
        # no goal carries the unit's bits (a partition leaf, say): its own structural path, else the evidence hop alone
        ps = C.paths.get(x) or []
        if ps:
            p0 = ps[0]
            return ([{"id": "top", "edge": None}] + [{"id": f, "edge": "→"} for f in p0["frames"][1:]]
                    + [{"id": c, "edge": "→"} for c in p0["chain"]])
        return [{"id": "top", "edge": None}, {"id": x, "edge": "⇢"}]
    own = next((p for p in C.paths.get(r, []) if p["root"] == r), None)
    frames = own["frames"] if own else ["top"]
    seq = [{"id": "top", "edge": None}] + [{"id": f, "edge": "→"} for f in frames[1:]] + [{"id": r, "edge": "→"}]
    if g and g != r:
        seq += _hops(C, r, g, True) or [{"id": g, "edge": "⇢"}]
    if g and x != g:
        down = _hops(C, g, x, False) if x in support(t, g) else None
        seq += down if down is not None else (_hops(C, g, x, True) or [{"id": x, "edge": "⇢"}])
    return seq


def path_text(C, path, GI, full=False):
    """The printed path: frames, goals, `cases` roots, the target's parent and the target print; a run of other nodes
    prints as `…`; above `path_max` printed nodes the first four and the last three stay. An elided evidence hop keeps ⇢."""
    t = C.t
    if full:
        return "".join((f" {p['edge']} " if p["edge"] else "") + p["id"] for p in path)
    n = len(path)
    keep = []
    for i, p in enumerate(path):
        node = t.nodes.get(p["id"], {})
        if p["id"] == "top" or i >= n - 2 or node.get("kind") == "frame" or p["id"] in GI or (node.get("kind") == "cases" and p["id"] in C.roots):
            keep.append(i)
    toks = []                       # (edge into the token, text)
    last = None
    for i in keep:
        if last is not None and i > last + 1:
            hop_in = path[last + 1]["edge"]
            later = "⇢" if any(path[j]["edge"] == "⇢" for j in range(last + 2, i + 1)) else "→"
            toks += [(hop_in, "…"), (later, path[i]["id"])]
        else:
            toks.append((path[i]["edge"], path[i]["id"]))
        last = i
    pm = int(C.po.get("path_max", 8))
    real = [k for k, (_, s) in enumerate(toks) if s != "…"]
    if len(real) > pm and len(real) > 7:
        head, tail = toks[:real[3] + 1], toks[real[-3]:]
        mid = toks[real[3] + 1:real[-3]]
        ev = "⇢" if any(e == "⇢" for e, _ in mid + tail[:1]) else "→"
        toks = head + [(mid[0][0] if mid else "→", "…"), (ev, tail[0][1])] + tail[1:]
    return "".join((f" {e} " if e else "") + s for e, s in toks)


def unit_signals(C, D, u, GI):
    """A unit's signals, in priority order; the renderer hoists one that every printed line carries."""
    t = C.t
    x = u["target"]
    n = t.nodes.get(x, {})
    N = D["nodes"].get(x, {})
    g = u["for"][0]["goal"] if u.get("for") else None
    out = []
    pr = (N.get("V") or {}).get("V_prior")
    if pr:
        out.append(f"read at v{pr['version']}, now v{n.get('version')}")
    out += list(u.get("signals") or [])
    if "attribution unvetted" in (N.get("flags") or []):
        out.append("attribution unvetted")
    if u.get("ai_number"):
        out.append("vet this AI number")
    if g and GI.get(g, {}).get("rests_on_ai"):
        out.append("promise rests on AI judgment")
    if g and t.nodes.get(g, {}).get("filed_from") == "quote" and not (D["nodes"].get(g, {}).get("want") or {}).get("confirmed", True):
        out.append("owner has not confirmed")
    if n.get("leaf_kind") == "record" and (N.get("V") or {}).get("valid", 0) >= 4:
        out.append("kernel-checked record")
    if "hypotheses unread" in (N.get("flags") or []):
        out.append("hypotheses unread")
    for w in n.get("work") or []:
        out.append({"priorities": f"work order #{w['ref']}", "open": "open statement", "round": "round", "private": "private source",
                    "decision": "decision", "foundation": "foundation"}[w["kind"]])
    if u["kind"] in ("do", "improve") and any(not (t.root / str(f)).exists() for f in n.get("files") or []):
        out.append("files outside the repository")   # a path the public reader cannot open (outside this repository)
    if u["kind"] in ("vet", "trace", "re-examine") and N.get("source_private_only") and "private source" not in out:
        out.append("private source only")       # the trace opens the Source, which names nothing in this repository
    st = GI.get(g, {}).get("stake_from") if g else None
    if st and t.nodes.get(st, {}).get("want") is True and not (D["nodes"].get(st, {}).get("want") or {}).get("confirmed", True):
        out.append(f"stake from {st} (owner has not confirmed)")
    return out


def home_root(C, g, GI):
    """The root a goal hangs under: itself if a root, else the root reaching it by the shortest chain over children
    and given edges (ties: the larger weight, then the id)."""
    if g in C.roots:
        return g
    cache = C.__dict__.setdefault("_home", {})
    if g in cache:
        return cache[g]
    cache[g] = _home_root(C, g, GI)
    return cache[g]


def _home_root(C, g, GI):
    t = C.t
    best = None
    for r in C.roots:
        dist, level = {r: 0}, [r]
        while level and g not in dist:
            nxt = []
            for x in level:
                for c in list(t.nodes[x]["children"]) + [given_base(y) for y in given_targets(t.nodes[x])]:
                    if c not in dist:
                        dist[c] = dist[x] + 1
                        nxt.append(c)
            level = nxt
        if g in dist:
            key = (dist[g], -(GI.get(r, {}).get("w") or 0), r)
            if best is None or key < best[0]:
                best = (key, r)
    return best[1] if best else None


def utility_placed(C, cid):
    """Whether a class has a utility, or a valuation node a defined value (its rows all judged)."""
    if cid in C.valuations:
        return bool((C.val.get(cid) or {}).get("defined"))
    return (C.cls.get(cid) or {}).get("utility") is not None


def window_dp_values(C, D, units, plans, const, EVs, best_of, V_act, frontier, rclos):
    """`--window-dp`: exact adaptive schedule over the top six exact-observation units within the window, each
    observation a forced target (2^K joint assignments at most); `--frontier K`: the greedy non-adaptive
    continuation at each commitment mass point (v3b §3.3)."""
    E, t = C.E, C.t
    window = q(C.fr.get("window_minutes", 360))
    # exact observations only (error 0: vet, trace, revive): a forced branch is what such a unit observes; a noisy unit
    # (map-read, improve, do, spell-out, connect, admit, re-examine) would have its D_window overstated
    short = [u for u in units if u["kind"] in EXACT_KINDS and t.nodes[u["target"]].get("kind") in ("leaf", "cases")][:6]
    commitment = C.fr.get("commitment") or [{"minutes": window, "mass": 1}]
    tkeys = {u["target"]: E.key_of(u["target"]) for u in short}
    dvars = {r: set(E.dag((E.key_of(r),)).vars) for r in plans}
    pj, ac, memo = {}, {}, {}

    def fkey(force):
        return tuple(sorted(force.items()))

    def pjoint(force):
        k = fkey(force)
        if k not in pj:
            pj[k] = E.evaluate(E.dag((), tuple(tkeys[x] for x in force)), {x: (v, None) for x, v in force.items()}, "mid")[0] if force else Q(1)
        return pj[k]

    def act(force):
        k = fkey(force)
        if k not in ac:
            vals = {}
            for r in plans:
                fr = {x: (v, None) for x, v in force.items() if x in dvars[r]}
                if fr and r in EVs:
                    base = {**root_base(C, r, C.psets[r]), **fr}
                    val, passes, _, _ = E.plan_value(r, base, "mid", "mid")
                    vals[r] = val / passes[0][1] if passes[0][1] else const[r]
            ac[k] = best_of(vals)[0]
        return ac[k]

    def split(force, x):
        p_now = pjoint(force)
        out = []
        for o in (True, False):
            f2 = dict(force)
            f2[x] = o
            p2 = pjoint(f2)
            if p2 > 0 and p_now > 0:
                out.append((p2 / p_now, f2))
        return out

    def terminal(force, elapsed):
        if not frontier:
            return act(force)
        total = Q(0)
        for cpt in commitment:
            c, mass = q(cpt.get("minutes", 0)), q(cpt.get("mass", 1))
            if c <= elapsed:
                total += mass * act(force)
                continue
            left, chosen, used = c - elapsed, [], set(force)
            for _ in range(int(frontier)):
                best = None
                for u in short:
                    if u["target"] in used or u["minutes"] > left:
                        continue
                    gain = sum((p * act(f2) for p, f2 in split(force, u["target"])), Q(0))
                    score = gain / (u["minutes"] or Q(1))
                    if best is None or score > best[0]:
                        best = (score, u)
                if best is None:
                    break
                chosen.append(best[1]["target"])
                used.add(best[1]["target"])
                left -= best[1]["minutes"]
            groups = [(Q(1), force)]
            for x in chosen:
                groups = [(p * p2, f2) for p, f in groups for p2, f2 in split(f, x)]
            total += mass * sum((p * act(f) for p, f in groups), Q(0))
        return total

    def dp(remaining, elapsed, force):
        k = (tuple(u["target"] for u in remaining), elapsed, fkey(force))
        if k in memo:
            return memo[k]
        best = terminal(force, elapsed)
        for u in remaining:
            if elapsed + u["minutes"] > window:
                continue
            rest = [v for v in remaining if v is not u]
            val = sum((p * dp(rest, elapsed + u["minutes"], f2) for p, f2 in split(force, u["target"])), Q(0))
            best = max(best, val)
        memo[k] = best
        return best
    for u in short:
        q_u = sum((p * dp([v for v in short if v is not u], u["minutes"], f2) for p, f2 in split({}, u["target"])), Q(0))
        u["D_window"] = q_u - V_act
    D["ranking_window"] = {"window_minutes": window, "frontier": int(frontier or 0), "shortlist": [u["target"] for u in short],
                           "component": sorted({r for r in C.roots if any(u["target"] in rclos.get(r, ()) for u in short)}),
                           "V_idle": terminal({}, Q(0)) if frontier else None}


# ---------------------------------------------------------------- derive: the orchestrator
def derive(t, scope=None, lam=None, window_dp=False, frontier=0, today=None, with_proposals=True, as_handle=None, ctx_out=None):
    """D1–D10 and §5 over a linted tree; returns the `derived.json` object (Fractions still live).

    Choices made where the specification is silent (all reversible, all Default):
    a node with `superseded_by` may be parentless (it left its table); a row's weight or
    conditional with no judgment is held at the remaining mass or 1/2 with width 1 and flagged
    `no belief`; the row judgment's read-check looks at the picture node; pooled J 10 needs both
    ranges at J ≥ 8; anchor 12's `checked` items name each admitted picture by id; an
    uncommitted `choose` is refined by trying each child and keeping the highest root value;
    the value interval is taken at all conditionals low and all high (monotone case); a
    gestalt stands in for an undefined plan value as g·U(success) + (1 − g)·U(outside); the
    comonotone companion is the minimum hold probability over the proof set; every root's
    numbers come from exact recursion over its closure with cutset conditioning, and one
    formula whose cutset exceeds MAX_CUTSET_WORLDS assignments is refused (rule 13); a
    conceded plan is not a candidate in the act until revived; a leaf range on a node that
    became a table is stale. The Defaults of 0.4 (the `or` reading, conditional tables,
    `X@valid`, improvement claims, levels at their version, owners, wants, tasks, the goal set
    and its weights, the units and the display) are named where each is computed.
    """
    C = Ctx(t)
    if ctx_out is not None:
        ctx_out.append(C)      # tests read the context (the engine, beliefs, proof sets) through this
    resolve_events(C)
    admission(C)
    levels(C)
    judgments(C)
    priorities(C)
    valuation_values(C)
    C.E = Infer(C)
    status = statuses(C)
    C.status = status
    C.sup = {rid: support(t, rid) for rid in C.roots}
    D = {"checker_version": CHECKER_VERSION, "anchor_rules": C.po.get("anchor_rules"), "generated_hash": "",
         "nodes": {}, "judgments": {}, "roots": {}, "events": {k: sorted(e["id"] for e in t.events if e["_status"] == k)
                                                                for k in ("counted", "withdrawn", "stale")}}
    D["events"]["stale_reasons"] = dict(sorted(C.stale_reason.items()))
    D["audits"] = {h: dict(a) for h, a in sorted(C.audits.items())}
    revs = defaultdict(int)
    for e in C.counted:
        if e["kind"] == "revise":
            revs[e["by"]] += 1
    D["revisions"] = dict(sorted(revs.items()))       # human revision passes per handle, beside the audits
    D["valuations"] = {x: {"value": {k: utility(C, x, k) for k in ("mid", "lo", "hi")}, "defined": C.val[x]["defined"],
                           "provisional": bool(t.nodes[x].get("provisional")),
                           "role": "outside option" if x == C.outside else "undescribed failure" if x == C.undescribed else "valuation"}
                       for x in sorted(C.valuations)}
    C.psets, C.costs, C.choice = {}, {}, {}
    for rid, r in C.roots.items():
        is_frame = t.nodes[rid].get("kind") == "frame"
        if is_frame:
            # the programme's belief follows its leading step (its best non-conceded step by value), set before its numbers
            live = [c for c in plan_children(t, rid) if D["roots"][c]["option_value"] is not None and D["roots"][c]["status"] != "conceded"]
            if live:
                C.E.set_choice({**C.E.choice, rid: max(live, key=lambda c: (D["roots"][c]["option_value"], c))})
        if r["role"] == "plan" and not is_frame:
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
        below = {C.row_class[k] or C.outside for k in C.admitted if k[0] in sup and C.admitted[k]}
        below |= {c for v in C.E.dag((C.E.key_of(rid),)).vars if v in sup for c in C.E.var_classes(v, "mid")}   # class_given sides
        below = sorted(c for c in below if utility(C, c) < utility(C, C.outside))
        # the root's numbers rest on AI judgments only when any proof-set belief they use is AI-generated
        ai_only = sorted({x for x in pset if (C.bel.get((("node", x), "range")) or {}).get("generated")}
                         | {x for x in pset if t.nodes[x].get("kind") == "cases"
                            and any("AI number" in b["p"][2] or "AI number" in b.get("w", (0, 0, []))[2] for b in row_beliefs(C, x).values())}
                         | ({rid} if g is not None and g.get("generated") else set()))
        D["roots"][rid] = {"role": r["role"], "preset": r["preset"], "frame": r["frame"], "frames": r.get("frames") or [r["frame"]], "status": rs, "diagnosis": rdiag,
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
    given_flags(C, status)
    paths = C.paths = structural_paths(C)
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
        if n.get("superseded_by"):
            C.flags[x].add(f"superseded by {n['superseded_by']}")      # it stays wherever a parent still lists it
        if (n.get("leaf_kind") == "record" and n.get("hypotheses") == "unread") or (n.get("kind") == "and" and any(
                t.nodes[c].get("leaf_kind") == "record" and t.nodes[c].get("hypotheses") == "unread" for c in n["children"])):
            C.flags[x].add("hypotheses unread")        # ruling F1 (2026-10-23): the record's Source carries the signature; a reader files the leaves
        if n.get("refinement_of"):
            C.flags[x].add(f"refinement of {n['refinement_of']}")
        if "improves" in n:
            C.flags[x].add(f"improvement claim on {n['improves']} (reality: {n['reality']})")
        if n.get("kind") == "frame" and n.get("opened") is False:
            C.flags[x].add("not opened; see Notes")
        elif n.get("kind") == "frame" and not n["children"] and not n.get("superseded_by"):
            C.flags[x].add("unspelled")
        if n.get("kind") == "frame" and n.get("filed_from") == "wiki":
            # a frame an agent drafted from a wiki page (ruling M3): the owner confirms by removing filed_from from the file
            C.flags[x].add("owner has not confirmed (drafted from " + ", ".join(narratives_of(n)) + ")" if narratives_of(n) else "owner has not confirmed (drafted from the wiki)")
        cost, why = elem_cost(C, x, status) if n.get("kind") in ("leaf", "cases") else (None, [])
        D["nodes"][x] = {"kind": n.get("kind"), "leaf_kind": n.get("leaf_kind"), "size": n["size"], "version": n["version"],
                         "V": {k: v for k, v in C.V[x].items() if k != "draft"}, "draft": C.V[x]["draft"],
                         "flags": sorted(C.flags[x]), "status": s, "diagnosis": diag,
                         "revival": revival(C, x, status) if s == "conceded" else None, "cost": cost, "cost_rows": why,
                         "load": load[x], "belief": None if b is None else {"J": b["J"], "mid": b["mid"], "width": b["width"], "range": b["range"]},
                         "rows": row_beliefs(C, x) if n.get("kind") == "cases" else None,
                         "admitted": {r["picture"]: C.admitted[(x, r["picture"])] for r in n["rows"]} if n.get("kind") == "cases" else None,
                         # leaf ranges given before this node became a table: suggestions for the residual row, never used
                         "stale_leaf_ranges": [{"event": e["id"], "by": e["by"], "range": [q(e["estimate"][0]), q(e["estimate"][1])]}
                                               for e in C.counted if e["_status"] == "stale" and C.stale_reason.get(e["id"]) == STALE_TABLE
                                               and target_key(e["target"]) == ("node", x)] if n.get("kind") == "cases" else None}
        D["nodes"][x]["paths"] = paths.get(x, [])
        D["nodes"][x]["source_private_only"] = source_private_only(t, n)
        for k in ("action", "who", "work", "files", "owner", "filed_from", "refinement_of", "improves", "reality"):
            if k in n:
                D["nodes"][x][k] = n[k]
        if n.get("want") is True:
            D["nodes"][x]["want"] = {"owner": n.get("owner"), "priority": C.priority.get(x), "weight": priority_value(C, x),
                                     "confirmed": not (n.get("filed_from") == "quote" and not any(
                                         e["kind"] == "priority" for e in C.on_node[x])),
                                     "attachment": want_attachment(C, x)}
        if n.get("kind") == "frame":
            D["nodes"][x]["frame"] = {"owner": ", ".join(owners_of(n)), "owners": owners_of(n), "unspelled": not n["children"] and n.get("opened") is not False,
                                      "opened": n.get("opened") is not False, "confirmed": n.get("filed_from") != "wiki",
                                      "narrative": narratives_of(n)}
        elif narratives_of(n):
            D["nodes"][x]["narrative"] = narratives_of(n)
        if n.get("kind") == "and" and C.E.forceable(x):
            # the argument as an implication (its assumption and hypothesis leaves held true) beside its literal reading
            D["nodes"][x]["valid_Pr"] = {m: C.E.prob((C.E.target_key(x + "@valid"),), {}, m) for m in ("mid", "lo", "hi")}
            D["nodes"][x]["literal_Pr"] = {m: C.E.prob((C.E.key_of(x),), {}, m) for m in ("mid", "lo", "hi")}
    for (tk, field), b in C.bel.items():
        D["judgments"]["/".join(map(str, tk)) + "/" + field] = b
    ranking(C, D, scope, lam, window_dp, frontier, as_handle)
    D["proposals"] = proposal_deltas(C, D) if with_proposals else []
    D["units_unranked"] = unranked_units(C, D, load)
    D["audit"] = audit_line(C, today, as_handle)
    return D


_PATH_TOKEN = re.compile(r"(?<![\w/.-])((?:[\w.-]+/)+[\w.-]*)")


def source_private_only(t, n):
    """Whether a node's Source names private material and nothing a public reader can open (the 'private source' signal, extended
    by the 2026-10-05b fix stage from work pointers to Sources): it says 'private', and carries no URL and no path that
    exists in this tree. A Source with no path at all (a bibliographic citation) is not flagged."""
    src = n.get("_source") or ""
    if "private" not in src.lower() or re.search(r"https?://", src):
        return False
    for tok in _PATH_TOKEN.findall(src):
        tok = tok.rstrip(".,;:)`'\"")
        if tok and not tok.startswith("research/") and (t.root / tok).exists():
            return False
    return True


def want_attachment(C, x):
    """How a want connects to the map: its children, its given edge, the nodes given it; [] while unattached."""
    t = C.t
    n = t.nodes[x]
    edges = [f"→ {c}" for c in n["children"]]
    if n.get("given") not in (None, ""):
        edges.append(f"⇢ {n['given']} (given)")
    edges += [f"{y} ⇢ (given {x})" for y, m in t.nodes.items() if x in [given_base(g) for g in given_targets(m)]]
    return edges


def given_flags(C, status):
    """Flags of the conditional tables: on a node with a given edge (a leaf, or the table a given row belongs to),
    which parent it reads, that parent's settled status, whether both conditionals carry their own judgments; on every
    root whose closure holds a judged edge with P(X | not Y) above P(X | Y), that its interval is not a bound."""
    t, E = C.t, C.E
    negative = set()
    for x, n in t.nodes.items():
        sides = []
        if n.get("given") not in (None, ""):
            sides.append((n["given"], (("node", x), "if-holds"), (("node", x), "if-fails")))
        for r in n.get("rows") or []:
            if r.get("given") not in (None, ""):
                sides.append((r["given"], (("row", x, r["picture"]), "p-if-holds"), (("row", x, r["picture"]), "p-if-fails")))
        for g, ka, kb in sides:
            C.flags[x].add(f"given {g}")
            ys = status[given_base(g)][0]
            if ys in ("conceded", "established"):
                C.flags[x].add(f"given: {g} {ys}")
            a, b = C.bel.get(ka), C.bel.get(kb)
            if not (a and b):
                C.flags[x].add("given: conditionals not judged")
            elif b["mid"] > a["mid"]:
                negative.add(x)
    if negative:
        for r in C.roots:
            if negative & E.closure((E.key_of(r),)):
                C.flags[r].add("interval not a bound (negative evidential edge)")


def row_hold(C, x):
    n = C.t.nodes[x]
    if n.get("kind") == "cases":
        rb = row_beliefs(C, x)
        return sum((b["w"][0] * b["p"][0] for b in rb.values()), Q(0)) if rb else Q(1, 2)
    b = C.bel.get((("node", x), "range"))
    return b["mid"] if b else Q(1, 2)


def unranked_units(C, D, load):
    """The unranked block, in this order: (1) `priority` for every want whose owner has not given a word; (2) a
    gestalt first on goals multiplying `ai_conjunct_threshold` or more AI-only conjuncts; (3) promise gestalts on goals
    whose promise rests on AI judgment and that carry the largest share of a unit in the top ten; (4) the landed
    "no gestalt yet" gestalts; (5) estimates, by the target's weighted informs, each pointing at the read that would
    supersede it; (6) classify, the quick admit of each table with proposed rows, reconcile, approve, structural
    re-examine. Every line names the goal it is under."""
    t, E = C.t, C.E
    GI = getattr(C, "GI", {}) or {}
    po = C.po
    main = [u for u in D["units"] if u.get("section", "main") == "main"]
    rank_of = {}
    for i, u in enumerate(main, 1):
        rank_of.setdefault(u["target"], i)
    iw = lambda x: (D["nodes"].get(x) or {}).get("informs_weighted") or 0.0
    informs = lambda x: (D["nodes"].get(x) or {}).get("informs") or []

    def under(x):
        if x in GI:
            return x
        gs = [g for g in informs(x) if g in GI]
        return max(gs, key=lambda g: (GI[g]["w"], g)) if gs else None
    blocks = {i: [] for i in range(1, 7)}

    def item(b, kind, target, node, note=None, order=0.0, **more):
        blocks[b].append((order, kind, str(target), dict({"kind": kind, "target": target, "node": node, "note": note,
                                                         "load": load.get(node, []) if node else [], "informs": informs(node) if node else [],
                                                         "under": under(node) if node else None}, **more)))
    # (1) the owners' words
    for x, n in t.nodes.items():
        if n.get("want") is True and C.priority.get(x) is None:
            clos = GI[x]["closure"] if x in GI else {x}
            note = ("confirm or disown: say high, medium, low or none (filed from your quoted words; unset reads as medium)"
                    if n.get("filed_from") == "quote" else "say high, medium, low or none; unset reads as medium")
            note += f"; source: {first_words(n.get('_source') or '', 30)}"
            item(1, "priority", x, x, note, -sum(iw(y) for y in clos), owner=n.get("owner"))

    def ai_only(x):
        vs = [y for y in (GI[x]["closure"] if x in GI else E.closure((E.key_of(x),))) if t.nodes.get(y, {}).get("kind") in ("leaf", "cases")]
        judged = [y for y in vs if has_judgment(C, y)]
        return bool(judged) and all(judgments_ai_only(C, y) for y in judged)
    human_gestalt = lambda g: bool(C.bel.get((("node", g), "gestalt"))) and not C.bel[(("node", g), "gestalt")].get("generated")
    thr = int(po.get("ai_conjunct_threshold", 3))
    # a want is asked for no gestalt: it carries its owner's priority, not a forecast
    done = {g for g in GI if t.nodes[g].get("want") is True}
    # (2) a derived number that multiplies k unread guesses: the holistic number first
    for g, I in GI.items():
        n = t.nodes[g]
        if n.get("kind") != "and" or human_gestalt(g) or g in done:
            continue
        k = sum(1 for c in n["children"] if ai_only(c))
        if k >= thr:
            item(2, "gestalt", g, g, f"the derived number multiplies {k} unread guesses; your holistic number for {g} (about two minutes) sets its promise",
                 -I["w"])
            done.add(g)
    # (3) promise gestalts where the promise rests on AI judgment and weights a unit in the top ten
    top10 = [u for u in main if u.get("for")][:10]
    tops = defaultdict(list)
    for i, u in enumerate(main, 1):
        if u in top10:
            tops[u["for"][0]["goal"]].append(i)
    for g, ranks in tops.items():
        if g in GI and g not in done and GI[g]["rests_on_ai"] and not human_gestalt(g):
            item(3, "gestalt", g, g, f"your holistic number for {g}, about two minutes, sets its promise; it weights units {', '.join(map(str, ranks))}",
                 -GI[g]["w"])
            done.add(g)
    # (4) no gestalt yet: the goal has a derived probability, so its gestalt is not ranked
    for g, I in GI.items():
        if g in done or C.bel.get((("node", g), "gestalt")) or (g in D["roots"] and D["roots"][g].get("subframe")):
            continue
        defined = D["roots"][g]["Pr_defined"] if g in D["roots"] else not I["blanks"]
        if defined:
            item(4, "gestalt", g, g, "no gestalt yet: the goal has a derived probability, so this is not ranked", -I["w"])
    plan_sup = set().union(*[C.sup[r] for r, rr in C.roots.items() if rr["role"] == "plan"] or [set()])
    for x, n in t.nodes.items():
        if n.get("kind") == "cases":
            # (5) a leaf range given before the leaf became this table is offered under the residual row, never used
            stale_ranges = [e for e in C.counted if e["_status"] == "stale" and C.stale_reason.get(e["id"]) == STALE_TABLE
                            and target_key(e["target"]) == ("node", x)]
            proposed = [r["picture"] for r in n["rows"] if not C.admitted[(x, r["picture"])]]
            for r in n["rows"]:
                key = (x, r["picture"])
                if not C.admitted[key]:
                    continue
                for f in (("w", "p-if-holds", "p-if-fails") if r.get("given") else ("w", "p")):
                    if f == "w" and r.get("residual"):
                        continue
                    if (C.bel.get((("row",) + key, f)) or {}).get("J", 0) < 8:
                        sug = None
                        if f == "p" and r.get("residual") and stale_ranges:
                            e = stale_ranges[-1]
                            sug = f"suggestion, not used: the leaf's earlier range {frange(e['estimate'])} ({e['id']}, stale: {STALE_TABLE})"
                        rd = rank_of.get(x) or rank_of.get(r["picture"])
                        if rd:
                            sug = (sug + "; " if sug else "") + f"or read first: ranked unit {rd}"
                        item(5, "estimate", f"{x}/{r['picture']}.{f}", x, sug, -iw(x))
                if C.row_class[key] is None and not r.get("residual"):
                    item(6, "classify", f"{x}/{r['picture']}.class", x)
            if proposed:
                # the one-word quick admit (collect-first), stating what it would move: displayed mids with and
                # without the table's proposed rows admitted, computed on a copy of the admission map
                adm2 = dict(C.admitted)
                for pic in proposed:
                    adm2[(x, pic)] = True
                E2 = Infer(C, admitted=adm2)
                E2.set_choice(E.choice)
                moves = []
                for gid in sorted((gg for gg in informs(x) if gg in GI), key=lambda gg: (-GI[gg]["w"], gg))[:3]:
                    k = E.key_of(gid)
                    a, b2 = E.prob((k,), {}, "mid"), E2.prob((k,), {}, "mid")
                    moves.append(f"{gid} from {float(a):.2g} to {float(b2):.2g}")
                item(6, "admit", x, x, f"admit {x} unread: {len(proposed)} proposed row{'s' if len(proposed) != 1 else ''} (one word; minutes under --why)"
                     + (f" — moves {', '.join(moves)}" if moves else ""), 0.0, rows=proposed, minutes=rate(C, "admit", n["size"])[0])
            if len(n["rows"]) > 5:
                item(6, "re-examine", x, x, "structural: a table past five rows may want coarsening")
        if x in plan_sup and n.get("kind") == "choose" and n.get("committed", "none") == "none":
            item(6, "classify", x, x)
        elif x in plan_sup and n.get("kind") == "or" and "tag" not in n and "improves" not in n:
            # an improvement `or` reads as either-suffices and needs no tag; elsewhere the tag is structure, set in the file
            item(6, "tag", x, x, "say whether the plan takes one of these children (tag: choose-one) or any one suffices "
                 "(tag: either-suffices); the tag is set in the node file, not by an event")
    for x in sorted(t.nodes):
        if bare_claim(t, C, x) and not informs(x):
            item(6, "connect", x, x, "a single claim no goal reads: file it as a part, picture or given parent of the argument it "
                 "bears on, or say it stands alone (it is ranked through the goals that read it, and nothing reads it yet)")
    for tk, field in C.reconcile:
        node = tk[1] if tk[0] == "node" else tk[2]
        item(6, "reconcile", "/".join(map(str, tk[1:])) + "." + field, node)
    for p in D.get("proposals", []):
        if p["status"] == "proposed":
            item(6, "approve", p["id"], None)
    out = []
    for b in range(1, 7):
        out += [x[3] for x in sorted(blocks[b], key=lambda x: (x[0], x[1], x[2]))]
    return out


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


def prefs(t, handle, why, all_units=False):
    u = ((t.policy.get("users") or {}).get(handle) or {}) if handle else {}
    return {"numbers": bool(why or (u.get("show_numbers", False) if handle else False)),
            "alt": bool(u.get("alternative_calculations", False)), "handle": handle, "all": bool(all_units)}


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
    GI = {g["id"]: g for g in D.get("goals") or []}
    full = lambda path: "".join((f" {p['edge']} " if p["edge"] else "") + p["id"] for p in path)
    po = t.policy
    shown = len(D["units"]) if pf.get("all") else int(po.get("tasks_shown", 40))
    also = q(po.get("also_for_share", Q(1, 5)))
    # the digest (what changed since the previous derivation) is in derived.json and on the DIGEST line, not here: since
    # ruling F3 (2026-10-23) its comparison is whatever derivation is at hand, and a committed file reads nothing that varies
    L += ["## Spell-out and agent work",
          f"- spell-out candidates (unspelled frames and childless wants): {D['spell_out']['count']}"
          + (f"; heaviest {', '.join(D['spell_out']['top'])}" if D["spell_out"]["top"] else ""),
          f"- agent work the map wants most: {', '.join(D['agent_top']) or 'none'}",
          f"- proposals awaiting approval: {', '.join(p['id'] for p in D.get('proposals', []) if p['status'] == 'proposed') or 'none'}", ""]
    L += ["## Lines", f"- commit line: {D['lines']['commit']}", f"- regime: {D['lines']['regime']}"]
    if D["lines"].get("act"):
        L.append(f"- act: {D['lines']['act']}")
    L.append(f"- {D['audit']['text']} (the session's audit share, listed first and never ranked; the list's top task is ranked unit 1, "
             "the commit line is about which plan to commit to)")
    if D["lines"].get("scoped"):
        L.append(f"- {D['lines']['scoped']}")
    main = [u for u in D["units"] if u.get("section", "main") == "main"]
    agent = [u for u in D["units"] if u.get("section") == "agent"]
    printed = main[:shown]
    # the hoist rule: a signal every printed ranked line would carry is said once in the header and dropped from the lines
    common = set.intersection(*[set(u.get("signals") or []) for u in printed]) if printed else set()

    def line(i, u):
        fl = u.get("for") or []
        head = f"{i}. {u['kind']} {u['target']} ({u['size']})"
        more = [f["goal"] for f in fl[1:] if Q(f["share"]) >= also][:2]
        if fl and fl[0]["goal"] != u["target"]:
            head += f" — for {fl[0]['goal']}"         # a unit for its own target says nothing here: the path carries its place
            if more:
                head += f"; also {', '.join(more)}"
        elif more:
            head += f" — also for {', '.join(more)}"
        sig = [s for s in u.get("signals") or [] if s not in common][:2]
        if sig:
            head += " — " + "; ".join(sig)
        if pf["numbers"]:
            sh = [f for f in fl[:3] if f["share"] >= 0.005]
            head += f" — {fmt(u['minutes'])} min" + (f"; shares {', '.join(f'{f['goal']} {100 * f['share']:.0f}%' for f in sh)}" if sh else "")
        out = [head, f"   path: {full(u['path']) if pf['numbers'] else u['path_line']}"]
        if u.get("text"):
            out.append(f"   {u['text']}")
        return out
    per_kind = defaultdict(list)
    for i, u in enumerate(main, 1):
        if u["kind"] in RESEARCH_KINDS and len(per_kind[u["kind"]]) < 3:
            per_kind[u["kind"]].append((i, u))
    research = sorted((iu for v in per_kind.values() for iu in v), key=lambda iu: iu[0])
    L += ["", "## Research and whole-argument units",
          "The three best-ranked units of each kind that produces new structure or reads an argument whole (improve, a human's do, "
          "re-examine, spell-out, connect, revive), each numbered by its rank in the list below; the order is the list's, this "
          "section only gathers them (signals hoisted below are dropped here too)."]
    L += sum((line(i, u) for i, u in research), []) or ["- none"]
    L += ["", "## Ranked units (by map rate; D under --why, never applied)" if D["ranking"]["lambda"] is None else f"## Ranked units (by rate + λ·D, λ = {D['ranking']['lambda']})",
          "The order: what each unit's result would tell about the goals it informs, in bits, each goal weighted by its stake "
          "(the plan, want or claim it serves) times its promise (how likely it looks, plus a summand where its derived number "
          "and its gestalt disagree), per hour of the unit's work (PROTOCOL §6).",
          "Each unit: `n. kind target (size)[ — for <the goal carrying the largest share of its weighted bits, where that is not the "
          "target itself>][; also <goals at a fifth or more>][ — signals]`, then its path from the top frame (→ part of, ⇢ evidence "
          "for; the chain shown is the shortest), then the work itself where the unit names one."]
    if common:
        named = [f"*{s}*" for s in sorted(common)]
        extra = " (every number is an AI's, J 0)" if "vet this AI number" in common else ""
        L.append(f"Hoisted from every line: {' and '.join(named)}{extra}; a line names a signal only where it sets the unit apart.")
    for i, u in enumerate(printed, 1):
        L += line(i, u)
    if len(main) > len(printed):
        L.append(f"- … {len(main) - len(printed)} more ranked units in `derived.json` (`--all` prints them)")
    L += ["", "## Agent work", "Work an agent can do without a human; the map's ordering, not `PRIORITIES.md`'s."]
    L += sum((line(i, u) for i, u in enumerate(agent[:20], 1)), []) or ["- none"]
    L += ["", "## By goal", "The goals in the frame tree's order (the agenda's outline): kind and role, the best ranked unit and its rank, "
          "the count of units, and the Statement's first clause. A rank past the printed list is in `derived.json` (each unit's "
          "`rank`), and `--all` prints every ranked unit."]
    rank_of = {}
    for i, u in enumerate(main, 1):
        for f in u.get("for") or []:
            rank_of.setdefault(f["goal"], (i, u))
    count = defaultdict(int)
    for u in D["units"]:
        for f in u.get("for") or []:
            count[f["goal"]] += 1
    for g, depth in D.get("goal_order") or []:
        if g not in GI:
            Fr = (D["nodes"].get(g) or {}).get("frame") or {}
            L.append(f"{'  ' * depth}- {g} (frame, owner {Fr.get('owner')}{'; unspelled' if Fr.get('unspelled') else ''}"
                     f"{'; not opened' if Fr and not Fr.get('opened') else ''}{'; owner has not confirmed' if Fr and not Fr.get('confirmed', True) else ''}): {t.nodes[g].get('question')}")
            continue
        G = GI[g]
        best = rank_of.get(g)
        L.append(f"{'  ' * depth}- {g} ({goal_role(t, D, g, G)}) — best unit: {f'{best[0]}. {best[1]['kind']} {best[1]['target']}' if best else 'none ranked'}; "
                 f"{count[g]} unit(s); {first_clause(t.nodes[g]['_statement'])}"
                 + (f" — weight {G['weight']:.3f} (stake {fmt(q(G['stake']))} · promise {G['pi']:.3f}), forecast {G['P_forecast']:.3f}, {G['H_bits']:.3f} bits" if pf["numbers"] else ""))
    unr = D["units_unranked"]
    L += ["", "## Judgment and structure units (unranked)",
          "In order: the owners' priority words, gestalts that set a goal's promise, estimates (each points at the read that "
          "supersedes it), then classification, quick admission, reconciliation, approval and structural re-examination. "
          "`informs k goals` counts the goals whose inference reaches the unit's node."]
    # the owners' priority words: in the pooled file one line per owner; under --as that owner, one line per want
    shown_unr, grouped = [], defaultdict(list)
    for u in unr:
        if u["kind"] == "priority" and pf.get("handle") != u.get("owner") and not pf.get("all"):
            if u.get("owner") not in grouped:
                shown_unr.append({"kind": "priority-group", "owner": u.get("owner")})
            grouped[u.get("owner")].append(u)
        else:
            shown_unr.append(u)

    def unr_line(u):
        if u["kind"] == "priority-group":
            ws = grouped[u["owner"]]
            return (f"- priority — {len(ws)} want{'s' if len(ws) != 1 else ''} of {u['owner']} await a priority word (high, medium, low or "
                    f"none; unset reads as medium), first {', '.join(w['target'] for w in ws[:3])}; `--as {u['owner']}` lists each with its source")
        k = len(u.get("informs") or [])
        return (f"- {u['kind']} {u['target']} — informs {k} goal{'s' if k != 1 else ''}" + (f"; {u['note']}" if u.get("note") else "")
                + (f" — under {u['under']}" if u.get("under") else ""))
    L += [unr_line(u) for u in shown_unr[:shown]] or ["- none"]
    if len(shown_unr) > shown:
        L.append(f"- … {len(shown_unr) - shown} more unranked units in `derived.json` (`--all` prints them)")
    if pf["numbers"]:
        L += ["", "## Why", "", "```",
              "score(u) = Σ_{g ∈ G, x informs g}  w_g · Δbits_u(g)  /  hours(u)",
              f"  w_g     = stake_g · (π̂_g ^ e + s · [g structure suspect])          (e = promise_exponent = {po.get('promise_exponent', 1)}, "
              f"s = suspicion_weight = {po.get('suspicion_weight', '1/2')})",
              "  goals   : frame roots (not a one-leaf shared claim or risk story: it counts through the goals that read it), improvement",
              "            claims, routes, refinements, wants; none under a frame that is not opened unless --scope",
              "  stake   : plan (U(success_class) − E[U | failure])/2 | want: owner's priority | improvement claim, route, refinement:",
              "            largest stake of the plans and wants reading it or its claim's family (unscaled) | risk story, shared claim:",
              f"            largest stake of a goal reading it × the share of that goal's entropy its truth settles | floor {po.get('stake_floor', '1/4')}",
              f"  π̂      : gestalt on g (verdict-shrunk) if logged, else derived P(g) in the verdict model (c = {po.get('verdict_c', 0.2)}), else 1/2",
              "  Δbits   : H(T_g) − E_o H(T_g | o), in the verdict model; o = the unit's observation of its target",
              f"  hours   : (task_overhead_minutes {po.get('task_overhead_minutes', 0)} + rate_table[kind][size]) / 60",
              "  D       : printed beside, not added", "```", "",
              "| goal | kind | home root | stake | rule | π̂ | source | AI only | P | forecast | H bits | weight | closure | cutset |",
              "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
        for G in D.get("goals") or []:
            L.append(f"| {G['id']} | {G['kind']} | {G['home_root']} | {fmt(q(G['stake']))} | {G['stake_rule']} | {G['pi']:.3f} | {G['pi_source']} | "
                     f"{'yes' if G['rests_on_ai'] else 'no'} | {fmt(G['P']) if G['P'] is not None else '—'} | {G['P_forecast']:.3f} | {G['H_bits']:.3f} | "
                     f"{G['weight']:.3f} | {G['closure_size']} | {G['cutset_size']} |")
        L += ["", "| rank | unit | minutes | weighted bits | bits/h | D | D_window | for (goal, weighted bits, share) | nested | signals | rate rows (prior until refit) | path |",
              "|---|---|---|---|---|---|---|---|---|---|---|---|"]
        for u in D["units"]:
            fl = "; ".join(f"{f['goal']} {f['wbits']:.4f} {100 * f['share']:.0f}%" for f in (u.get("for") or [])[:3] if f["share"] >= 0.005)
            L.append(f"| {u.get('rank') or u.get('section', '')} | {u['kind']} {u['target']} | {fmt(u['minutes'])} | {fmt(u.get('wbits'))} | {fmt(u['rate'])} | "
                     f"{fmt(u['D'])} | {fmt(u.get('D_window'))} | {fl} | {u.get('nested_for', 0)} | {'; '.join(u.get('signals') or [])} | "
                     f"{'; '.join(u['why'])} | {full(u['path'])} |")
        inf = D.get("inference", {})
        L += ["", f"weighted bits in scope = {D['ranking']['weighted_bits']:.3f} over {len(D['ranking'].get('goals') or [])} goal(s); "
              f"largest cutsets (cap {inf.get('cap')} assignments per formula): "
              + ("; ".join(f"[{c['phi']}: {', '.join(c['cutset'])}; {c['assignments']} assignments]" for c in inf.get("largest") or []) or "none (every formula is a tree)")
              + f"; V_act = {fmt(D['act']['V_act'])} ({D['act'].get('cand_label', D['act']['cand'])}); outside option = {outside_text(D)}", ""]
        L += valuation_lines(D) + [""]
        for r, R in D["roots"].items():
            L.append(f"- {r}{' (in ' + R['frame'] + ')' if R.get('frame') else ''}: Pr {fmt(R['Pr']['mid'])} in {frange(R['Pr'])}; value {fmt((R['value'] or {}).get('mid'))}"
                     f"{' in ' + frange(R['value']) if R['value'] else ''}; gestalt {fmt((R['gestalt'] or {}).get('mid'))}; "
                     f"no belief on: {', '.join(R['nobelief']) if R['nobelief'] else 'none'}"
                     + (f"; programme: leading step {R['subframe']['leading_step'] or 'none'}" if R.get("subframe") else ""))
    return "\n".join(L) + "\n"


def first_clause(st):
    """A Statement's first clause: to the first comma outside brackets, at most thirty words; a clause under five words
    gives way to the Statement's first thirty words."""
    text = " ".join(st.split())
    depth, cut = 0, len(text)
    for i, ch in enumerate(text):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            cut = i
            break
    clause = text[:cut]
    if len(clause.split()) < 5:
        return first_words(text, 30)
    return first_words(clause, 30)


def first_words(text, k):
    w = " ".join(str(text).split()).split()
    return " ".join(w[:k]) + ("…" if len(w) > k else "")


def goal_role(t, D, g, G):
    """How the goal table names a goal's kind and place (plan of F; want of @h; route under I; shared claim of F)."""
    fr = (D["roots"].get(g) or {}).get("frame") or "top"
    k = G["kind"]
    if k == "want":
        return f"want of {t.nodes[g].get('owner')}"
    if k == "route":
        par = next((x for x, n in t.nodes.items() if g in n["children"] and "improves" in n), None)
        return f"route under {par}"
    if k == "refinement":
        return f"refinement of {t.nodes[g].get('refinement_of')}"
    if k == "improvement":
        return f"improvement claim on {t.nodes[g].get('improves')}" + (f", shared claim of {fr}" if g in D["roots"] else "")
    return f"{k.replace('-', ' ')} of {fr}"


def goal_order(C, GI):
    """The goals in the frame tree's order: depth-first, roots in file order, each non-root goal after its home root."""
    t = C.t
    under = defaultdict(list)
    for g in GI:
        if g not in C.roots:
            hr = home_root(C, g, GI)
            if hr:
                under[hr].append(g)
    out, seen = [], set()

    def walk(entries, depth):
        for r in entries:
            rid = r.get("id")
            if rid in seen:
                continue
            seen.add(rid)
            if rid in GI:
                out.append((rid, depth))
            elif t.nodes.get(rid, {}).get("kind") == "frame":
                out.append((rid, depth))           # a frame prints as an outline row (it is no goal)
            for g in sorted(under.get(rid, []), key=lambda g: (len(_hops(C, rid, g, True) or []), g)):
                if g not in seen:
                    seen.add(g)
                    out.append((g, depth + 1))
            if t.nodes.get(rid, {}).get("kind") == "frame":
                walk(t.nodes[rid].get("roots") or [], depth + 1)
    walk(roots(t), 0)
    out += [(g, 0) for g in GI if g not in seen]
    return out


def render_view(t, D, pf, today):
    L = [f"# View (generated {today}; regenerated by the checker, never edited)", "",
         f"Top frame (owner {', '.join(owners_of(t.frame))}): {t.frame.get('question')}", "",
         "How to read a root's block: the *weakest proof-set leaf* is the least-vetted element of the cheapest way to establish "
         "the root; a *safety margin* counts the established proof-set leaves whose concession would concede the root; *informs* "
         "counts the goals whose inference reaches the node (a programme informs through its steps). Sub-frames follow the top "
         "frame in the frame tree's order, each heading naming the frame it sits in.", ""]
    if pf["handle"]:
        L.append(f"*Personal render for {pf['handle']}: numbers {'shown' if pf['numbers'] else 'in the appendix only'}, alternative calculations {'on' if pf['alt'] else 'off'}; not a committed file.*\n")
    def root_block(r, R, level):
        best = next((u for u in D["units"] if r in u["bears_on"]), None)
        L.append(f"{'#' * level} {r}")
        L.append(f"- preset {R['preset']}; status **{R['status']}**; weakest proof-set leaf at V {R['weakest_V']}")
        if R.get("subframe"):
            S = R["subframe"]
            L.append(f"- a programme (sub-frame): {S['question']}")
            L.append(f"- steps: {', '.join(S['roots'])}; leading step: {S['leading_step'] or 'none has a value yet'}"
                     f"; the programme's value is its best non-conceded step's, or its outside option ({S['outside_option']}) once every step is conceded")
        if R.get("ai_only"):
            L.append(f"- rests on AI numbers (no human judgment yet): {', '.join(R['ai_only'])}")
        if pf["numbers"] and D["nodes"][r].get("want"):
            g_ = R["gestalt"] or {}
            L.append("- no probability shown: a want carries its owner's priority, not a forecast"
                     + (f"; a human's gestalt {fmt(g_.get('mid'))}" if g_ else ""))
        elif pf["numbers"]:
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
            L.append(f"- safety margin: {R['margin']}")
        elif pf["numbers"]:
            L.append(f"- {R['preset']} budget: {'failure mass' if R['preset'] == 'probabilistic' else 'expected loss'} {fmt(R['budget_loss'])} of {fmt(R['budget'])}")
        L.append(f"- load-bearing shared leaves: {', '.join(R['load_bearing']) or 'none'}")
        N = D["nodes"][r]
        if N.get("want"):
            W = N["want"]
            L.append(f"- a want of {W['owner']}; priority {W['priority'] or 'unset (reads as medium)'}"
                     + ("; owner has not confirmed" if not W["confirmed"] else "")
                     + f"; attachment: {'; '.join(W['attachment']) or 'unattached'}")
            mine = [u for u in D["units"] if u["target"] == r or r in u.get("bears_on", [])]
            L.append(f"- its units: {', '.join(u['kind'] + ' ' + u['target'] for u in mine[:5]) or 'none ranked'}")
        if N.get("frame"):
            Fr = N["frame"]
            L.append(f"- frame owner {Fr['owner']}" + ("; unspelled (no roots yet)" if Fr["unspelled"] else "")
                     + ("; not opened; see Notes" if not Fr["opened"] else "")
                     + ("; owner has not confirmed (drafted from the wiki)" if not Fr.get("confirmed", True) else ""))
        if len(R.get("frames") or []) > 1:
            L.append("- also a root of: " + ", ".join(f or "the top frame" for f in R["frames"][1:]))
        k = len(N.get("informs") or [])
        if R.get("subframe"):
            L.append("- a programme: informs through its steps" + (f" ({k} goal{'s' if k != 1 else ''})" if k else ""))
        else:
            L.append(f"- informs {k} goal{'s' if k != 1 else ''}" + ("" if k else " (a single claim no goal reads: offered to connect)"
                                                                     if N.get("kind") == "leaf" and R["role"] in ("shared-claim", "risk-story") else ""))
        G = next((g for g in D.get("goals") or [] if g["id"] == r), None)
        if G and pf["numbers"]:
            L.append(f"- weight {G['weight']:.3f} (stake {fmt(q(G['stake']))} · promise {G['pi']:.3f}, {G['pi_source']})")
        L.append(f"- best next unit: {best['kind'] + ' ' + best['target'] if best else 'none'}")

    def frame_sections(frame_id, level):
        for role, head in (("plan", "Plans"), ("risk-story", "Risk stories"), ("shared-claim", "Shared claims"), ("want", "Wants")):
            rs = [(r, R) for r, R in D["roots"].items() if R["role"] == role and R.get("frame") == frame_id]
            if not rs:
                continue
            L.append(f"{'#' * level} {head}")
            for r, R in rs:
                root_block(r, R, level + 1)
            L.append("")
    frame_sections(None, 2)
    # sub-frames in the frame tree's order (pre-order, roots in file order), parents before children
    order, seenf = [], set()

    def fwalk(frame_id):
        for rid, RR in D["roots"].items():
            if RR.get("subframe") and RR.get("frame") == frame_id and rid not in seenf:
                seenf.add(rid)
                order.append(rid)
                fwalk(rid)
    fwalk(None)
    order += [rid for rid, RR in D["roots"].items() if RR.get("subframe") and rid not in seenf]
    for r in order:
        R = D["roots"][r]
        if R.get("subframe"):
            Fr = D["nodes"][r].get("frame") or {}
            L.append(f"## Sub-frame {r} (in {R.get('frame') or 'the top frame'}): {R['subframe']['question']}")
            L.append(f"Owner {Fr.get('owner')}" + ("; unspelled: no roots yet (its unit is spell-out)" if Fr.get("unspelled") else "")
                     + ("; not opened; see Notes" if Fr and not Fr.get("opened") else ""))
            L.append("")
            frame_sections(r, 3)
    work = [(x, N) for x, N in D["nodes"].items() if N.get("action") or N.get("work")]
    if work:
        L += ["## Tasks and work pointers", "Task leaves and actioned claims (the work to do, who does it) and pointers to the "
              "repository's own work orders, open statements and rounds.", ""]
        for x, N in work:
            bits = []
            if N.get("action"):
                bits.append(f"{N['action']} (who: {N.get('who')})")
            for w in N.get("work") or []:
                bits.append(work_text(w))
            if N.get("files"):
                bits.append("files: " + ", ".join(map(str, N["files"])))
            L.append(f"- {x}: " + "; ".join(bits))
        L.append("")
    impl = [(x, N) for x, N in D["nodes"].items() if N.get("valid_Pr")]
    if impl:
        L += ["## Arguments as implications", "Each `and` with assumption or hypothesis leaves, read with those leaves held true "
              "(`X@valid`, a legal given target) beside its literal reading.", ""]
        for x, N in impl:
            L.append(f"- {x}: as an implication P({x}@valid) = {fmt(N['valid_Pr']['mid'])}; literally P({x}) = {fmt(N['literal_Pr']['mid'])}"
                     if pf["numbers"] else f"- {x}: as an implication ({x}@valid) and literally; the numbers print under --why")
        L.append("")
    L += ["## Valuation nodes", "The outside option and the undescribed failure, each a cases node over the outcome classes; "
          "weights and conditionals are judgments like any row's.", ""]
    L += (valuation_lines(D) if pf["numbers"] else [f"- {x} ({V['role']}): {'has a value' if V['defined'] else 'no belief'}"
                                                      f"{' (provisional)' if V['provisional'] else ''}" for x, V in (D.get("valuations") or {}).items()]) + [""]
    cols = "| id | kind | V | flags | status | " + ("cost | " if pf["numbers"] else "") + "load | informs |"
    L += ["## Nodes", "", cols, "|" + "---|" * (cols.count("|") - 1)]
    for x, N in D["nodes"].items():
        v = f"{N['V']['display']} ({N['V']['weaker']})"
        L.append(f"| {x} | {N['kind']}{'/' + N['leaf_kind'] if N['leaf_kind'] else ''} | {v} | {', '.join(N['flags'])} | {N['status']} | "
                 + (f"{fmt(N['cost'])} | " if pf["numbers"] else "") + f"{len(N['load'])} | {len(N.get('informs') or []) or '0 (informs no goal)'} |")
    return "\n".join(L) + "\n"


def work_text(w):
    """How a work pointer prints."""
    return {"priorities": f"work order: PRIORITIES #{w['ref']}", "open": f"open statement: `{w['ref']}`",
            "round": f"round: {w['ref']}", "private": f"private source: {w['ref']}",
            "decision": f"decision: {w['ref']}", "foundation": f"foundation: {w['ref']}"}[w["kind"]]


def derivation_hash(D):
    """The hash versions.json records for derived.json: the derivation without its digest, its own hash and the day's audit draw."""
    return sha(dumps({k: v for k, v in D.items() if k not in DERIVATION_HASH_SKIPS}))


def index_hash(idx):
    return sha(json.dumps({k: v for k, v in idx.items() if k not in ("generated", "generated_hash")}, indent=1, sort_keys=True))


def digest(prev, D, source=None):
    if not prev:
        return {}
    flips = [f"{x}: {prev['nodes'][x]['status']} → {N['status']}" for x, N in D["nodes"].items() if x in prev["nodes"] and prev["nodes"][x]["status"] != N["status"]]
    # root statuses include the preset's addition (a budget concession), which the node table does not show
    rflips = [f"root {r}: {prev['roots'][r]['status']} → {R['status']}" + (f" ({R['diagnosis']})" if R["status"] == "conceded" and R["diagnosis"] else "")
              for r, R in D["roots"].items() if r in prev.get("roots", {}) and prev["roots"][r]["status"] != R["status"]]
    moves = [f"{x}: V {prev['nodes'][x]['V']['headline']} → {N['V']['headline']}" for x, N in D["nodes"].items() if x in prev["nodes"] and prev["nodes"][x]["V"]["headline"] != N["V"]["headline"]]
    new = sorted(set(D["events"]["counted"]) - set(prev["events"]["counted"]))
    revised = sorted(f"{x} (v{N['version']})" for x, N in D["nodes"].items() if any(f.startswith("human-revised") for f in N["flags"])
                     and not any(f.startswith("human-revised") for f in (prev["nodes"].get(x) or {}).get("flags", [])))
    wants_new = sorted(x for x, N in D["nodes"].items() if N.get("want") and not (prev["nodes"].get(x) or {}).get("want"))
    return {"compared_with": source, "statuses_flipped": flips, "root_statuses_flipped": rflips, "levels_moved": moves, "events_new": len(new),
            "revisions": revised, "wants_new": wants_new,
            "proposals_awaiting": [p["id"] for p in D.get("proposals", []) if p["status"] == "proposed"]}


def digest_line(dg):
    """One stderr line: what the digest compared with and what moved."""
    if not dg:
        return "DIGEST no previous derivation to compare with (neither the branch derived nor a derived.json on disk that versions.json records)"
    return (f"DIGEST compared with {dg['compared_with']}: {len(dg['statuses_flipped'])} status(es) flipped, {len(dg['root_statuses_flipped'])} root status(es) flipped, "
            f"{len(dg['levels_moved'])} level(s) moved, {dg['events_new']} event(s) counted since, {len(dg['revisions'])} revision(s), "
            f"{len(dg['wants_new'])} want(s) filed since, {len(dg['proposals_awaiting'])} proposal(s) awaiting")


POOLED = {"numbers": False, "alt": False, "handle": None, "all": False}   # how the committed files are always rendered


def _git_show(t, spec):
    try:
        r = subprocess.run(["git", "-C", str(t.root), "show", spec], capture_output=True, text=True, timeout=30)
        if r.returncode == 0 and r.stdout.strip():
            return r.stdout
    except (OSError, subprocess.SubprocessError):
        pass
    return None


def previous_derivation(t):
    """The previous derivation the digest compares with, and its name (ruling F3, 2026-10-23: `derived.json` is not committed).
    In order: the branch `derived` (`derived:graph/derived.json`, then `origin/derived:…`), the derivation of `main` CI publishes;
    else the `graph/derived.json` on disk, when the `versions.json` at HEAD (outside a git checkout, the one on disk) records its
    derivation hash, so a file left by a run on another tree is never mistaken for the previous derivation; else nothing.
    The committed files never read the result: the digest lives in `derived.json` and in the DIGEST line."""
    for spec, name in (("derived:graph/derived.json", "the branch derived"), ("origin/derived:graph/derived.json", "the branch origin/derived")):
        text = _git_show(t, spec)
        if text:
            try:
                return json.loads(text), name
            except json.JSONDecodeError:
                continue
    prev_path = t.graph / "derived.json"
    if prev_path.is_file():
        try:
            prev = json.loads(prev_path.read_text())
        except json.JSONDecodeError:
            return None, None
        recorded = None
        head = _git_show(t, "HEAD:./graph/versions.json")
        where = "HEAD"
        if head is None and (t.graph / "versions.json").is_file():
            head, where = (t.graph / "versions.json").read_text(), "disk"
        if head:
            try:
                recorded = (json.loads(head).get("generated") or {}).get("derived.json")
            except json.JSONDecodeError:
                recorded = None
        if recorded and recorded == derivation_hash(prev):
            return prev, f"graph/derived.json on disk (the derivation versions.json at {where} records)"
    return None, None


def committed_files(t, D, today):
    """The four committed files from the plain derivation: identical whatever flags the run was given."""
    prev, source = previous_derivation(t)
    D["digest"] = digest(prev, D, source)
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
    idx = _clean(structure_index(t, today))          # Fractions in human events print as "p/q", as in derived.json
    idx["generated_hash"] = ""
    idx["generated_hash"] = sha(json.dumps(idx, indent=1, sort_keys=True))
    files["index.json"] = json.dumps(idx, indent=1, sort_keys=True) + "\n"
    # versions.json records the derivation hash of the two files that are not committed (F3): a derivation on disk or on the
    # branch `derived` is checked against the commit it claims to come from, and a changed derivation shows in the diff
    vobj = {"generated": {"derived.json": derivation_hash(D), "index.json": index_hash(idx)}, "generated_hash": "", "nodes": versions}
    vobj["generated_hash"] = sha(json.dumps(vobj, indent=1, sort_keys=True))
    files["versions.json"] = json.dumps(vobj, indent=1, sort_keys=True) + "\n"
    return files


def structure_index(t, today):
    """The structure-only index (ruling M8, 2026-10-22; schema in graph/MAP-AS-CANONICAL.md §6.1): every node with its kind,
    fields, Statement, Source, Notes, narrative, pointers and edges, every frame with its roots and owners, the handles, the
    decision anchors and rounds the map points at, the narratives, and every event of every human ledger; no derived number,
    level, status or rank. Every id is the id a URL carries."""
    fr = t.frame
    nodes = {}
    skip = {"id", "kind", "leaf_kind", "author", "size", "size_reason", "version", "children", "rows", "given", "work", "narrative",
            "question", "owner", "roots", "_path", "_statement", "_source", "_notes", "_item"}
    in_frames = defaultdict(list)
    for r in all_roots(t):
        for f in r.get("frames") or [r["frame"]]:
            in_frames[r["id"]].append({"frame": f or "top", "role": r.get("role")})
    # formal results (ruling F2, 2026-10-23): the record child, its hypotheses (a list or "unread"), the registry id the record
    # carries, and the items the result answers through its priorities pointers; `claims` maps a registry id to its node
    formal, answered_by, claims = {}, defaultdict(list), {}
    for x, n in sorted(t.nodes.items()):
        recs = [c for c in n["children"] if t.nodes.get(c, {}).get("leaf_kind") == "record"]
        if n.get("kind") == "and" and recs:
            rec = t.nodes[recs[0]]
            answers = sorted({str(w.get("ref")) for w in n.get("work") or [] if w.get("kind") == "priorities"}, key=lambda s: (len(s), s))
            rid = rec.get("registry_id") or (x if t.registry and x in t.registry else None)
            formal[x] = {"record": recs[0], "hypotheses": rec.get("hypotheses") if rec.get("hypotheses") is not None else [],
                         "registry_id": rid, "answers": answers}
            if n.get("superseded_by"):
                continue            # a deprecated alias (a result merged under its claim, F5): it answers nothing twice and resolves no id
            for a in answers:
                answered_by[a].append(x)
            if rid:
                claims.setdefault(rid, x)
    for x, n in sorted(t.nodes.items()):
        rec = {"kind": n.get("kind"), "leaf_kind": n.get("leaf_kind"), "author": n.get("author"), "size": n.get("size"), "version": n.get("version"),
               "statement": n["_statement"], "source": n["_source"], "notes": n.get("_notes") or "", "narrative": narratives_of(n),
               "children": list(n["children"]), "given": n.get("given"), "work": list(n.get("work") or []),
               "rows": [{"picture": r.get("picture"), "class": r.get("class"), "given": r.get("given"), "residual": bool(r.get("residual"))}
                        for r in n.get("rows") or [] if isinstance(r, dict)],
               "fields": {k: v for k, v in n.items() if k not in skip}, "in_frames": in_frames.get(x, [])}
        if n.get("kind") == "frame":
            rec["frame"] = {"question": n.get("question"), "owners": owners_of(n), "roots": [{"id": r.get("id"), "role": r.get("role")} for r in n.get("roots") or []],
                            "opened": n.get("opened") is not False, "filed_from": n.get("filed_from")}
        if n.get("_item"):
            rec["item_body"] = n["_item"]
        if n.get("leaf_kind") == "record":
            rec["hypotheses"] = n.get("hypotheses") if n.get("hypotheses") is not None else []
            rec["registry_id"] = n.get("registry_id")
        if x in formal:
            rec["formal_result"] = formal[x]
        nodes[x] = rec
    rounds_pointed, decisions_pointed, narratives = defaultdict(list), defaultdict(list), defaultdict(list)
    for x, n in t.nodes.items():
        for w in n.get("work") or []:
            if w.get("kind") == "round":
                r = t.rounds.get(str(w.get("ref")).rstrip("/"))
                rounds_pointed[r["id"] if r else str(w.get("ref"))].append(x)
            if w.get("kind") == "decision":
                decisions_pointed[str(w.get("ref"))].append(x)
        for page in narratives_of(n):
            narratives[page].append(x)
    for page in narratives_of(fr):
        narratives[page].append("top")
    handles = t.policy.get("handles") or {}
    events = [e for e in t.events if is_human(t, e.get("by"))]
    return {"schema": "graph-index/2", "generated": str(today), "generated_hash": "",
            "frame": {"question": fr.get("question"), "owners": owners_of(fr), "narrative": narratives_of(fr),
                      "classes": [c.get("id") for c in fr.get("classes") or [] if isinstance(c, dict)], "valuations": valuations(t),
                      "outside_option": fr.get("outside_option"), "undescribed_failure": fr.get("undescribed_failure"),
                      "roots": [{"id": r.get("id"), "role": r.get("role")} for r in roots(t)]},
            "handles": {h: {k: v for k, v in (spec or {}).items()} for h, spec in handles.items()},
            "maintainers": maintainers(t),
            "nodes": nodes,
            "items": {str(n["item"]): {"node": x, "answered_by": sorted(answered_by.get(str(n["item"]), []))}
                      for x, n in sorted(t.nodes.items()) if "item" in n},
            "claims": claims,
            "decisions": [{"anchor": a, "date": d["date"], "title": d["title"], "status": d["status"], "touches": d["touches"],
                           "pointed_by": sorted(decisions_pointed.get(a, []))} for a, d in sorted(t.decisions.items(), key=lambda kv: kv[1]["line"])],
            "rounds": [{"id": r["id"], "path": r.get("path"), "pointed_by": sorted(rounds_pointed.get(r["id"], []))}
                       for r in sorted({v["id"]: v for v in t.rounds.values()}.values(), key=lambda r: (str(r.get("date")), r["id"]))],
            "narratives": {page: sorted(set(xs)) for page, xs in sorted(narratives.items())},
            "events": [{k: v for k, v in e.items() if not k.startswith("_")} for e in events]}


def write_outputs(t, files):
    for name, content in files.items():
        (t.graph / name).write_text(content)
    # PRIORITIES.md is a render of the item nodes (ruling M6): written on the plain run beside the committed files
    if any("item" in n for n in t.nodes.values()) and (t.root / "state" / "priorities_sections.md").is_file():
        from checkers import priorities_render
        (t.root / "PRIORITIES.md").write_text(priorities_render.render(t.root))


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
    ap.add_argument("--root", default=".", help="the tree whose graph/ is checked (default: the current directory)")
    ap.add_argument("--self-test", action="store_true", help="run every refusal's null input and the synthetic graph's facts")
    ap.add_argument("--scope", help="rank inside one node's goals (a node id, or X@valid); a personal render")
    ap.add_argument("--as", dest="as_handle", help="render for one handle (its presentation settings, its wants at full weight)")
    ap.add_argument("--why", action="store_true", help="print the numbers: minutes, weighted bits, D, the goals table, full paths")
    ap.add_argument("--window-dp", action="store_true", help="exact adaptive schedule over the top six exact-observation units")
    ap.add_argument("--frontier", type=int, default=0, help="greedy continuation of K units at each commitment point")
    ap.add_argument("--lambda", dest="lam", type=Q, default=None, help="order by rate + λ·D instead of the map rate")
    ap.add_argument("--registry", help="one more CLAIMS.md beside policy.yaml's registries, for a personal render (the committed files ignore it)")
    ap.add_argument("--all", dest="all_units", action="store_true", help="print every ranked and unranked unit, not the first tasks_shown")
    ap.add_argument("--dry-run", action="store_true", help="write nothing; print the derivation as JSON on stdout")
    ap.add_argument("--print", dest="print_render", action="store_true", help="write nothing; print the task list and view on stdout")
    ap.add_argument("--out", default=None, help="write the personal render here instead of stdout (a path outside graph/)")
    ap.add_argument("--today", default=None, help="ISO date for the generated files (tests)")
    a = ap.parse_args(argv)
    if a.self_test:
        return 0 if self_test() else 1
    today = _dt.date.fromisoformat(a.today) if a.today else _dt.date.today()
    err = sys.stderr
    personal = bool(a.scope or a.as_handle or a.why or a.lam is not None or a.window_dp or a.frontier or a.all_units or a.registry)
    try:
        # the committed files read only the registries policy.yaml lists; an extra --registry changes the personal render alone
        t = load_tree(a.root)
        lint(t)
        tp = t
        if a.registry:
            tp = load_tree(a.root, a.registry)
            lint(tp)
        if a.scope and given_base(a.scope) not in t.nodes:
            raise Refuse(1, "--scope", f"{a.scope!r} resolves to no node")
        if a.scope and a.scope.endswith("@valid") and t.nodes[given_base(a.scope)].get("kind") != "and":
            raise Refuse(2, "--scope", f"{a.scope!r}: @valid names an and-shaped argument")
        if a.as_handle and not is_handle(t, a.as_handle):
            raise Refuse(5, "--as", f"{a.as_handle!r} is not a mapped handle")
        if a.out and pathlib.Path(a.out).resolve().is_relative_to(t.graph.resolve()):
            raise Refuse(11, "--out", "the personal render is not committed; write it outside graph/")
        D = derive(t, today=today)                      # the plain derivation: what the committed files hold
        files = committed_files(t, D, today)
        P = derive(tp, a.scope, a.lam, a.window_dp, a.frontier, today, as_handle=a.as_handle) if personal else D
        if a.dry_run:
            print(dumps(P))
        elif a.print_render:
            print(personal_render(tp, P, prefs(tp, a.as_handle, a.why, a.all_units) if personal else POOLED, today), end="")
        else:
            write_outputs(t, files)
            write_deltas(t, D)
            if personal:
                text = personal_render(tp, P, prefs(tp, a.as_handle, a.why, a.all_units), today)
                if a.out:
                    pathlib.Path(a.out).write_text(text)
                else:
                    print(text, end="")
    except Refuse as e:
        print(e, file=err)
        return 1
    for w in t.warnings:
        print(f"WARN {w}", file=err)
    print(digest_line(D.get("digest") or {}), file=err)
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
owner: "@h1"
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
  reread:   {S: 4, M: 10, L: 20, prior: true}
  improve:  {S: 60, M: 180, L: 480, prior: true}
  do:       {S: 45, M: 240, L: 960, prior: true}
  spell-out: {S: 8, M: 25, L: 60, prior: true}
task_overhead_minutes: 3
read_error: 0.3
promise_exponent: 1
stake_floor: 0.25
others_wants_weight: 0.5
verdict_c: 0.2
verdict_record_floor: 0.15
improve_error: 0.3
do_error: 0.3
structure_suspect_odds: 4
gestalt_mix: 0.5
ai_conjunct_threshold: 3
path_max: 8
also_for_share: 0.2
tasks_shown: 40
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
            "prog": ("frame", "L", {"children": "[step-1, step-2, sc-1]", "question": '"Does the programme reach a bounded analogue of the collapse?"', "owner": '"@h1"',
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
        # the long route's own number: an `or` reads as a disjunction for belief, so both routes need one
        f'{{"id": "h2-15", "by": "@h2", {base}, "kind": "estimate", "target": {{"node": "dear-leaf"}}, "estimate": [0.3, 0.5], "reason": "the general model is far off"}}',
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


def _null_shared_eight(nodes):
    """Null input for rule 13: plan-b gains two conjuncts that share all eight of their leaves."""
    leaves = [f"l{i}" for i in range(1, 9)]
    nodes["plan-b"] = ("and", "M", {"children": "[shared-leaf, or-y, q-leaf, k1, k2, plan-b.complete]"}, nodes["plan-b"][3])
    for k in ("k1", "k2"):
        nodes[k] = ("and", "S", {"children": "[" + ", ".join(leaves + [k + ".complete"]) + "]"}, f"The conjunct {k} of plan B holds.")
        nodes[k + ".complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, f"No premise beyond the listed leaves is needed for {k}.")
    for x in leaves:
        nodes[x] = ("leaf", "S", {"leaf_kind": "assumption"}, f"The shared premise {x} of plan B holds.")


def _null_improve(variant):
    """Tweaks for the improvement claims' null inputs: or-y becomes an improvement claim on cheap-leaf in the given variant."""
    def tweak(nodes):
        st = "Plan B's intermediate claim can be improved until it reflects the toy model well."
        kids = "[cheap-leaf, dear-leaf, or-y.residual]"
        if variant == "no-residual":
            kids = "[cheap-leaf, dear-leaf]"
        if variant == "no-reality":
            st = "X can be improved."
        reality = {"no-reality": '"a trained agent"', "empty-reality": '""'}.get(variant, '"the toy model"')
        nodes["or-y"] = ("or", "S", {"children": kids, "improves": "cheap-leaf", "reality": reality}, st)
        if variant != "no-residual":
            nodes["or-y.residual"] = ("leaf", "S", {"leaf_kind": "route", "residual": "true"}, "Some refinement not yet described goes through.")
        if variant == "route-under-and":
            nodes["or-y"] = ("or", "S", {"children": "[cheap-leaf, dear-leaf]"}, "Either route establishes the intermediate claim of plan B.")
            del nodes["or-y.residual"]
            nodes["plan-b"] = ("and", "M", {"children": "[shared-leaf, or-y, q-leaf, r-loose, plan-b.complete]"}, nodes["plan-b"][3])
            nodes["r-loose"] = ("leaf", "S", {"leaf_kind": "route"}, "A route nobody's improvement claim lists goes through.")
    return tweak


_PLAN_B_ROOT = "  - {id: plan-b, role: plan, preset: worst-case, success_class: utopia}\n"


def _want_root(extra=""):
    """Edit for synthetic_tree: the top frame gains the want root want-x (see `_with_want`)."""
    return ("frame.yaml", _PLAN_B_ROOT, _PLAN_B_ROOT + "  - {id: want-x, role: want" + extra + "}\n")


def _with_want(nodes):
    """Tweak: a want leaf of @h1's, filed from a quotation."""
    nodes["want-x"] = ("leaf", "S", {"leaf_kind": "want", "want": "true", "owner": '"@h1"', "filed_from": "quote"},
                       "The toy collapse is written up with its proof kernel-checked.")


def _with_task(nodes):
    """Tweak: plan-b gains a task leaf t-1 (no action: the null input adds the variants by edit)."""
    nodes["plan-b"] = ("and", "M", {"children": "[shared-leaf, or-y, q-leaf, t-1, plan-b.complete]"}, nodes["plan-b"][3])
    nodes["t-1"] = ("leaf", "S", {"leaf_kind": "task", "who": "agent"}, "A document lists the trust principles by axis.")


def _priority(by, target, word, i):
    return f'{{"id": "{by[1:]}-p{i}", "by": "{by}", {_NB}, "kind": "priority", "target": {{"node": "{target}"}}, "estimate": "{word}"}}'


def _null_loose(nodes):
    """Tweak: a leaf no children list names, nobody is given and no frame names as a root."""
    nodes["loose-leaf"] = ("leaf", "S", {"leaf_kind": "assumption"}, "A premise attached to nothing holds.")


def _null_plain_want_root(nodes):
    """Tweak: a leaf without want: true, later named as a root with role want."""
    nodes["w-plain"] = ("leaf", "S", {"leaf_kind": "assumption"}, "A premise filed as a want without being one holds.")


def _null_named_want(nodes):
    """Tweak: a want whose id lacks the want- prefix."""
    nodes["wish-x"] = ("leaf", "S", {"leaf_kind": "want", "want": "true", "owner": '"@h1"'}, "The toy collapse is published.")


def _alt2(field_lines):
    """Edit: lines added to alt-2's frontmatter."""
    return ("nodes/alt-2.md", "leaf_kind: step\n", "leaf_kind: step\n" + field_lines)


# Null inputs that must be refused, as (name, rule, synthetic_tree keywords); `edits` is a list of
# (path under graph/, old text, new text) applied after the tree is written. Each new refusal adds its line here.
_NB = '"date": "2026-09-20", "rule": "2026-10-02.1", "via": "chat", "version": 1'
_PIC_H_ROW = "{picture: pic-h, class: high-conflict, observable: never}"
NULL_INPUTS = [
    # conditional tables
    ("given names no node", 1, {"edits": [("nodes/alt-2.md", "leaf_kind: step\n", "leaf_kind: step\ngiven: nonexistent\n")]}),
    # the 2026-10-05b fix stage: three refusals of 0.4 that had no null input, and the two it adds
    ("a rate-table row that is not a {S, M, L} map", 10, {"edits": [("policy.yaml", "  spell-out: {S: 8, M: 25, L: 60, prior: true}", "  spell-out: 8")]}),
    ("a row's class_given without given", 2, {"edits": [("nodes/cases-x.md", _PIC_H_ROW, _PIC_H_ROW[:-1] + ", class_given: high-conflict}")]}),
    ("a rule's row naming a field other than w and p", 5, {"extra": {"h1": [f'{{"id": "h1-n9", "by": "@h1", {_NB}, "kind": "rule", "target": {{"node": "cases-x"}}, '
                                                                        '"ref": "x", "rows": {"pic-h": {"q": [0.5, 0.5]}}}']}}),
    ("a choice point in the support of two plan roots", 2, {"edits": [("nodes/plan-b.md", "[shared-leaf, or-y", "[shared-leaf, choose-c, or-y")]}),
    ("suspicion_weight above 1", 10, {"edits": [("policy.yaml", "also_for_share: 0.2\n", "also_for_share: 0.2\nsuspicion_weight: 2\n")]}),
    ("registries naming no file", 10, {"edits": [("policy.yaml", "also_for_share: 0.2\n", "also_for_share: 0.2\nregistries: [projects/none/CLAIMS.md]\n")]}),
    ("a leaf given its own ancestor (a cycle over children and given)", 1,
     {"edits": [("nodes/shared-leaf.md", "leaf_kind: assumption\n", "leaf_kind: assumption\ngiven: plan-a\n")]}),
    ("given on a picture leaf", 2, {"edits": [("nodes/pic-h.md", "leaf_kind: picture\n", "leaf_kind: picture\ngiven: shared-leaf\n")]}),
    ("given names a valuation node", 2, {"edits": [("nodes/alt-2.md", "leaf_kind: step\n", "leaf_kind: step\ngiven: default-trajectory\n")]}),
    ("class_given on a leaf without given", 2, {"edits": [("nodes/alt-2.md", "leaf_kind: step\n", "leaf_kind: step\nclass_given: {fails: high-conflict}\n")]}),
    ("an if-holds estimate on a leaf without given", 1, {"extra": {"h1": [
        f'{{"id": "h1-n1", "by": "@h1", {_NB}, "kind": "estimate", "target": {{"node": "alt-2", "field": "if-holds"}}, "estimate": [0.5, 0.5], "reason": "x"}}']}}),
    ("class_given naming no class", 10, {"edits": [("nodes/alt-2.md", "leaf_kind: step\n", "leaf_kind: step\ngiven: shared-leaf\nclass_given: {holds: no-such-class}\n")]}),
    ("a rule setting p on a given row", 5, {"edits": [("nodes/cases-x.md", _PIC_H_ROW, _PIC_H_ROW[:-1] + ", given: shared-leaf}")],
                                            "extra": {"h1": [f'{{"id": "h1-n2", "by": "@h1", {_NB}, "kind": "rule", "target": {{"node": "cases-x"}}, '
                                                             '"ref": "x", "rows": {"pic-h": {"p": [0.5, 0.5]}}}']}}),
    ("a rule's row carrying given", 2, {"extra": {"h1": [f'{{"id": "h1-n7", "by": "@h1", {_NB}, "kind": "rule", "target": {{"node": "cases-x"}}, '
                                                       '"ref": "x", "rows": {"pic-h": {"given": "shared-leaf"}}}']}}),
    ("a p-if-holds estimate on a row without given", 1, {"extra": {"h1": [
        f'{{"id": "h1-n8", "by": "@h1", {_NB}, "kind": "estimate", "target": {{"row": ["cases-x", "pic-h"], "field": "p-if-holds"}}, "estimate": [0.5, 0.5], "reason": "x"}}']}}),
    ("class_given that is not a map of holds and fails", 2, {"edits": [_alt2("given: shared-leaf\nclass_given: {either: high-conflict}\n")]}),
    ("a node attached to nothing", 1, {"tweak": _null_loose}),
    ("a top-frame root named in a children list", 1, {"edits": [("nodes/plan-a.md", "[shared-leaf, cases-x", "[plan-b, shared-leaf, cases-x")]}),
    # validity as an implication
    ("--scope X@valid on a leaf", 2, {"args": ("--scope", "shared-leaf@valid")}),
    ("@valid on a leaf", 2, {"edits": [("nodes/alt-2.md", "leaf_kind: step\n", "leaf_kind: step\ngiven: shared-leaf@valid\n")]}),
    ("improves without reality", 2, {"edits": [_alt2("improves: cheap-leaf\n")]}),
    ("improves on a step leaf", 2, {"edits": [_alt2('improves: cheap-leaf\nreality: "the toy model"\n')]}),
    ("an improvement leaf without improves", 2, {"edits": [("nodes/alt-2.md", "leaf_kind: step\n", "leaf_kind: improvement\n")]}),
    ("residual: true on a leaf that is no route", 2, {"edits": [("nodes/cheap-leaf.md", "leaf_kind: assumption\n", "leaf_kind: assumption\nresidual: true\n")]}),
    ("an improvement claim with an empty reality phrase", 2, {"tweak": _null_improve("empty-reality")}),
    # revision-aware levels
    ("a revise on a row", 5, {"extra": {"h1": [
        f'{{"id": "h1-n9", "by": "@h1", {_NB}, "kind": "revise", "target": {{"row": ["cases-x", "pic-h"]}}, "from": {{"version": 0}}}}']}}),
    ("a revise without from", 5, {"extra": {"h1": [f'{{"id": "h1-n10", "by": "@h1", {_NB}, "kind": "revise", "target": {{"node": "alt-2"}}}}']}}),
    ("a revise to a version neither versions.json nor the node file knows", 5, {"shared_version": 2, "extra": {"h1": [
        f'{{"id": "h1-n11", "by": "@h1", {_NB}, "kind": "revise", "target": {{"node": "shared-leaf"}}, "from": {{"version": 0}}}}']}}),
    ("a revise by an AI handle", 5, {"extra": {"ai": [
        f'{{"id": "ai-n1", "by": "@ai", {_NB}, "kind": "revise", "target": {{"node": "alt-2"}}, "from": {{"version": 1}}, "gloss": "x"}}']}}),
    ("a revise whose from.version is not below its version", 5, {"extra": {"h1": [
        f'{{"id": "h1-n3", "by": "@h1", {_NB}, "kind": "revise", "target": {{"node": "alt-2"}}, "from": {{"version": 1}}}}']}}),
    ("a revise from a node that is not superseded by the target", 5, {"extra": {"h1": [
        f'{{"id": "h1-n4", "by": "@h1", {_NB}, "kind": "revise", "target": {{"node": "alt-2"}}, "from": {{"node": "alt-1"}}}}']}}),
    ("an event whose version is above its node's", 5, {"extra": {"h1": [
        f'{{"id": "h1-n5", "by": "@h1", "date": "2026-09-20", "rule": "2026-10-02.1", "via": "chat", "version": 2, "kind": "estimate", '
        '"target": {"node": "alt-2"}, "estimate": [0.5, 0.5], "reason": "x"}']}}),
    ("a rate row below zero minutes", 10, {"edits": [("policy.yaml", "reread:   {S: 4", "reread:   {S: -1")]}),
    # owners, frames, wants, priorities, tasks
    ("a frame owned by an AI handle", 2, {"programme": True, "edits": [("nodes/prog.md", 'owner: "@h1"', 'owner: "@ai"')]}),
    # 2026-10-23: a record's hypotheses are a list or the word unread, never both; a retired frame holds nothing
    ("a record whose hypotheses mix ids with unread", 2, {"edits": [("nodes/alt-2.md", "leaf_kind: step\n", "leaf_kind: record\nstatement_of_record: x\nhypotheses: [shared-leaf, unread]\n")]}),
    ("a retired frame still holding its roots", 2, {"programme": True, "edits": [("nodes/prog.md", 'owner: "@h1"', 'owner: "@h1"\nsuperseded_by: plan-a')]}),
    ("a frame with opened: false and a plan root", 2, {"programme": True, "edits": [("nodes/prog.md", "kind: frame\n", "kind: frame\nopened: false\n")]}),
    ("a frame with roots: [] and non-empty children", 2, {"programme": True, "edits": [
        ("nodes/prog.md", "roots: \n  - {id: step-1, role: plan, preset: worst-case, success_class: utopia}\n  - {id: step-2, role: plan, preset: worst-case, success_class: utopia}\n  - {id: sc-1, role: shared-claim, preset: worst-case}", "roots: []")]}),
    ("a priority by an AI handle", 5, {"tweak": _with_want, "edits": [_want_root()], "extra": {"ai": [_priority("@ai", "want-x", "high", 1)]}}),
    ("a priority by a human who is not the want's owner", 5, {"tweak": _with_want, "edits": [_want_root()], "extra": {"h2": [_priority("@h2", "want-x", "high", 1)]}}),
    ("a gestalt by an AI handle on a want", 5, {"tweak": _with_want, "edits": [_want_root()], "extra": {"ai": [
        f'{{"id": "ai-w1", "by": "@ai", {_NB}, "kind": "gestalt", "target": {{"node": "want-x"}}, "estimate": [0.4, 0.4], "derived": false, "gloss": "x"}}']}}),
    ("a priority on a plain leaf", 5,{"extra": {"h1": [_priority("@h1", "alt-2", "high", 1)]}}),
    ("a priority outside the four words", 5, {"tweak": _with_want, "edits": [_want_root()], "extra": {"h1": [_priority("@h1", "want-x", "urgent", 1)]}}),
    ("a task leaf without action", 2, {"tweak": _with_task}),
    ("who outside human, agent, either", 2, {"tweak": _with_task, "edits": [("nodes/t-1.md", "who: agent\n", 'who: robot\naction: "Write the list."\n')]}),
    ("a want root with success_class", 2, {"tweak": _with_want, "edits": [_want_root(", success_class: utopia")]}),
    ("the top frame without an owner", 2, {"edits": [("frame.yaml", 'owner: "@h1"\n', "")]}),
    ("a want without an owner", 2, {"tweak": _with_want, "edits": [_want_root(), ("nodes/want-x.md", 'owner: "@h1"\n', "")]}),
    ("a want whose id lacks the want- prefix", 2, {"tweak": _null_named_want, "edits": [("frame.yaml", _PLAN_B_ROOT, _PLAN_B_ROOT + "  - {id: wish-x, role: want}\n")]}),
    ("a want filed as a step leaf", 2, {"tweak": _with_want, "edits": [_want_root(), ("nodes/want-x.md", "leaf_kind: want\n", "leaf_kind: step\n")]}),
    ("a want that is no root", 2, {"tweak": _with_want, "edits": [_alt2("given: want-x\n")]}),
    ("a want leaf without want: true", 2, {"edits": [("nodes/alt-2.md", "leaf_kind: step\n", "leaf_kind: want\n")]}),
    ("filed_from other than quote", 2, {"edits": [_alt2("filed_from: memory\n")]}),
    ("action on an assumption leaf", 2, {"edits": [("nodes/shared-leaf.md", "leaf_kind: assumption\n", 'leaf_kind: assumption\naction: "Check it."\nwho: human\n')]}),
    ("a work pointer of an unknown kind", 2, {"edits": [_alt2("work: [{kind: nonsense, ref: x}]\n")]}),
    ("a priorities work pointer that is not an item number", 2, {"edits": [_alt2("work: [{kind: priorities, ref: abc}]\n")]}),
    ("role want on a node without want: true", 2, {"tweak": _null_plain_want_root, "edits": [("frame.yaml", _PLAN_B_ROOT, _PLAN_B_ROOT + "  - {id: w-plain, role: want}\n")]}),
    # the ranking's policy keys and gestalts
    ("promise_exponent above 2", 10, {"edits": [("policy.yaml", "promise_exponent: 1", "promise_exponent: 5/2")]}),
    ("stake_floor above 1", 10, {"edits": [("policy.yaml", "stake_floor: 0.25", "stake_floor: 2")]}),
    ("others_wants_weight below 0", 10, {"edits": [("policy.yaml", "others_wants_weight: 0.5", "others_wants_weight: -1")]}),
    ("verdict_c above 1", 10, {"edits": [("policy.yaml", "verdict_c: 0.2", "verdict_c: 3/2")]}),
    ("verdict_record_floor above 1", 10, {"edits": [("policy.yaml", "verdict_record_floor: 0.15", "verdict_record_floor: 2")]}),
    ("a gestalt on a leaf that is no goal", 5, {"extra": {"h1": [
        f'{{"id": "h1-n6", "by": "@h1", {_NB}, "kind": "gestalt", "target": {{"node": "alt-2"}}, "estimate": [0.5, 0.5], "derived": false, "reason": "x"}}']}}),
    # the units' policy keys
    ("improve_error above 1/2", 10, {"edits": [("policy.yaml", "improve_error: 0.3", "improve_error: 3/5")]}),
    ("do_error above 1/2", 10, {"edits": [("policy.yaml", "do_error: 0.3", "do_error: 3/5")]}),
    ("structure_suspect_odds below 1", 10, {"edits": [("policy.yaml", "structure_suspect_odds: 4", "structure_suspect_odds: 1/2")]}),
    ("gestalt_mix above 1", 10, {"edits": [("policy.yaml", "gestalt_mix: 0.5", "gestalt_mix: 2")]}),
    ("ai_conjunct_threshold below 2", 10, {"edits": [("policy.yaml", "ai_conjunct_threshold: 3", "ai_conjunct_threshold: 1")]}),
    # display
    ("path_max below 3", 10, {"edits": [("policy.yaml", "path_max: 8", "path_max: 2")]}),
    ("also_for_share above 1", 10, {"edits": [("policy.yaml", "also_for_share: 0.2", "also_for_share: 2")]}),
    ("tasks_shown below 1", 10, {"edits": [("policy.yaml", "tasks_shown: 40", "tasks_shown: 0")]}),
    # the 2026-10-22 map-as-canonical round: narratives, decision and foundation pointers, shared roots, owners, item nodes
    ("a narrative naming no wiki page", 2, {"edits": [_alt2("narrative: wiki/No-Such-Page.md\n")]}),
    ("a narrative outside wiki/", 2, {"programme": True, "edits": [("nodes/prog.md", "kind: frame\n", "kind: frame\nnarrative: AGENTS.md\n")]}),
    ("a decision pointer to no anchor", 1, {"edits": [_alt2("work: [{kind: decision, ref: 2026-01-01--nothing}]\n")]}),
    ("a foundation pointer to no foundation", 1, {"edits": [_alt2("work: [{kind: foundation, ref: no.such-foundation}]\n")]}),
    ("a want that is a root of two frames", 1, {"programme": True, "tweak": _with_want, "edits": [_want_root(), ("nodes/prog.md", "children: [step-1, step-2, sc-1]", "children: [step-1, step-2, sc-1, want-x]"),
                                                                                                    ("nodes/prog.md", "  - {id: sc-1, role: shared-claim, preset: worst-case}", "  - {id: sc-1, role: shared-claim, preset: worst-case}\n  - {id: want-x, role: want}")]}),
    ("a shared root with two roles", 1, {"programme": True, "edits": [("nodes/prog.md", "children: [step-1, step-2, sc-1]", "children: [step-1, step-2, sc-1, plan-b]"),
                                                                     ("nodes/prog.md", "  - {id: sc-1, role: shared-claim, preset: worst-case}", "  - {id: sc-1, role: shared-claim, preset: worst-case}\n  - {id: plan-b, role: shared-claim, preset: worst-case}")]}),
    ("a frame owner list holding an AI handle", 2, {"programme": True, "edits": [("nodes/prog.md", 'owner: "@h1"', 'owner: ["@h1", "@ai"]')]}),
    ("a maintainer list holding an AI handle", 5, {"edits": [("policy.yaml", 'maintainer: "@h1"', 'maintainer: ["@h1", "@ai"]')]}),
    ("filed_from: wiki on a leaf", 2, {"edits": [_alt2("filed_from: wiki\n")]}),
    ("an item node without its fields", 2, {"edits": [_alt2('item: "7"\n')]}),
    ("a node id beginning item- without item", 2, {"edits": [("nodes/alt-2.md", "id: alt-2\n", "id: item-2\n"), ("nodes/choose-c.md", "[alt-1, alt-2]", "[alt-1, item-2]")]}),
    # improvement claims
    ("improves names no node", 1, {"edits": [("nodes/alt-2.md", "leaf_kind: step\n", 'leaf_kind: step\nimproves: nonexistent\nreality: "a trained agent"\n')]}),
    ("an improvement or with no residual route", 2, {"tweak": _null_improve("no-residual")}),
    ("a route leaf under a plain and", 2, {"tweak": _null_improve("route-under-and")}),
    ("improves on a frame", 2, {"programme": True, "edits": [("nodes/prog.md", "kind: frame\n", 'kind: frame\nimproves: plan-a\nreality: "a trained agent"\n')]}),
    ("an improvement claim whose Statement omits its reality phrase", 3, {"tweak": _null_improve("no-reality")}),
]


def self_test():
    """Null inputs must fail; the synthetic graph must derive the §7 facts."""
    import tempfile
    ok = True

    def expect_fail(name, root, rule=None, args=()):
        nonlocal ok
        code, out, err = run_quiet(["--root", str(root), "--dry-run", *args])
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
        global MAX_CUTSET_WORLDS
        saved_cap = MAX_CUTSET_WORLDS
        try:
            MAX_CUTSET_WORLDS = 1 << 4
            synthetic_tree(d / "cap", tweak=_null_shared_eight)
            expect_fail("an and whose eight leaves each sit under two conjuncts, cap lowered to 2^4", d / "cap", 13)
        finally:
            MAX_CUTSET_WORLDS = saved_cap
        for i, (name, rule, kw) in enumerate(NULL_INPUTS):
            root = d / f"null{i}"
            edits = kw.pop("edits", ())
            args = kw.pop("args", ())
            synthetic_tree(root, **kw)
            for rel, old, new in edits:
                f = root / "graph" / rel
                text = f.read_text()
                if old not in text:
                    ok = False
                    print(f"  FAIL  null input: {name} -> the edit's anchor {old!r} is not in {rel}")
                    break
                f.write_text(text.replace(old, new, 1))
            else:
                expect_fail(name, root, rule, args)
            kw["edits"] = edits
            if args:
                kw["args"] = args
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
