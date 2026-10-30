"""What the site reads: the structure-only index, the derivation (for the ranking page only), the state files, the
registries, the decision entries, the wiki source, the policy and the human ledgers. Standard library only; the
checkers' own parsers are imported for the registries and the flat YAML."""
from __future__ import annotations

import datetime as _dt
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

DECISION_LINE = re.compile(r"<!-- decision: ([^;\s]+); touches: ([^;]*?)(; status: open)? -->")
SETTLED_HEAD = re.compile(r"^### (\d{4}-\d{2}-\d{2}) — (.*)$")
QUEUE_HEAD = re.compile(r"^- \*\*(.+?)\*\*\s*(.*)$")


class BuildError(Exception):
    pass


def git(*args: str) -> str:
    try:
        r = subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError):
        return ""
    return r.stdout.strip() if r.returncode == 0 else ""


def ensure_index() -> None:
    """The plain checker run writes graph/index.json and graph/derived.json when they are absent (ruling S2)."""
    if (ROOT / "graph" / "index.json").is_file() and (ROOT / "graph" / "derived.json").is_file():
        return
    r = subprocess.run([sys.executable, "-m", "checkers.graph", "--root", "."], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        raise BuildError("the plain checker run failed, so there is no index to build from:\n" + r.stderr[-2000:])


def load_decisions(text: str) -> dict:
    """{anchor: {date, title, status, touches, body}} from DECISIONS.md: a settled entry is a `### date — title`
    heading followed by its anchor line and its prose up to the next heading; a queued entry is a `- **title**`
    bullet followed by its continuation lines and its anchor line."""
    out: dict = {}
    lines = text.split("\n")
    i, n = 0, len(lines)
    while i < n:
        m = SETTLED_HEAD.match(lines[i])
        if m and i + 1 < n and DECISION_LINE.search(lines[i + 1]):
            d = DECISION_LINE.search(lines[i + 1])
            j = i + 2
            body = []
            while j < n and not lines[j].startswith("### ") and not lines[j].startswith("## "):
                body.append(lines[j])
                j += 1
            out[d.group(1)] = {"date": m.group(1), "title": m.group(2).strip(), "status": "open" if d.group(3) else "settled",
                               "touches": _touches(d.group(2)), "body": "\n".join(body).strip("\n"), "line": i + 1}
            i = j
            continue
        m = QUEUE_HEAD.match(lines[i])
        if not m and lines[i].startswith("- **"):
            # a bold title that closes on a later line
            joined, k = lines[i], i
            while "**" not in joined[4:] and k + 1 < n and lines[k + 1].startswith("  "):
                k += 1
                joined += " " + lines[k].strip()
            m = QUEUE_HEAD.match(joined)
        if m:
            j = i + 1
            body = [lines[i]]
            anchor = None
            while j < n and (lines[j].startswith("  ") or lines[j].strip() == ""):
                d = DECISION_LINE.search(lines[j])
                if d:
                    anchor = d
                else:
                    body.append(lines[j])
                if lines[j].strip() == "" and j + 1 < n and not lines[j + 1].startswith("  "):
                    j += 1
                    break
                j += 1
            if anchor:
                out[anchor.group(1)] = {"date": None, "title": m.group(1).strip(), "status": "open" if anchor.group(3) else "settled",
                                        "touches": _touches(anchor.group(2)), "body": "\n".join(body).strip("\n"), "line": i + 1}
            i = j
            continue
        i += 1
    return out


def _touches(s: str) -> list[dict]:
    return [{"kind": x.split(":", 1)[0], "ref": x.split(":", 1)[1]} for x in (t.strip() for t in s.split(",")) if ":" in x and x != "none"]


def last_changed(paths: list[str]) -> str | None:
    """The latest commit date over the given repository paths (ISO date), or None outside a checkout."""
    paths = [p for p in paths if (ROOT / p).exists()]
    if not paths:
        return None
    out = git("log", "-1", "--format=%cs", "--", *paths)
    return out or None


class Repo:
    def __init__(self) -> None:
        ensure_index()
        self.index = json.loads((ROOT / "graph" / "index.json").read_text())
        if self.index.get("schema") != "graph-index/3":
            raise BuildError(f"the index is schema {self.index.get('schema')!r}; the site reads graph-index/3")
        self.derived = json.loads((ROOT / "graph" / "derived.json").read_text())
        self.nodes = self.index["nodes"]
        self.rounds = {r["id"]: r for r in json.loads((ROOT / "state" / "rounds.json").read_text())["rounds"]}
        self.round_pointed = {r["id"]: r.get("pointed_by") or [] for r in self.index["rounds"]}
        self.projects = {p["id"]: p for p in json.loads((ROOT / "state" / "projects.json").read_text())["projects"]}
        fpath = ROOT / "state" / "foundations.json"
        self.foundations = {f["id"]: f for f in json.loads(fpath.read_text()).get("foundations", [])} if fpath.is_file() else {}
        from checkers import registry
        from checkers import graph as g
        self.registry: dict = {}
        for path in sorted(ROOT.glob("projects/*/CLAIMS.md")):
            for e in registry.parse(path):
                e = dict(e)
                e["registry"] = path.relative_to(ROOT).as_posix()
                self.registry[e["id"]] = e
        self.policy = g.parse_flat_yaml((ROOT / "graph" / "policy.yaml").read_text())
        self.handles = self.index.get("handles") or {}
        self.decisions = load_decisions((ROOT / "DECISIONS.md").read_text())
        for d in self.index["decisions"]:
            if d["anchor"] not in self.decisions:
                raise BuildError(f"decision anchor {d['anchor']!r} is in the index but its entry was not found in DECISIONS.md")
            self.decisions[d["anchor"]]["pointed_by"] = d.get("pointed_by") or []
        self.wiki = {p.stem: p.read_text() for p in sorted((ROOT / "wiki").glob("*.md"))}
        self.events = []
        for p in sorted((ROOT / "graph" / "events").glob("*.jsonl")):
            for line in p.read_text().splitlines():
                if line.strip():
                    e = json.loads(line)
                    e["_ledger"] = p.name
                    self.events.append(e)
        self.human = {h for h, spec in self.handles.items() if (spec or {}).get("kind") == "human"}
        self.events_by_node: dict[str, list] = {}
        for e in self.events:
            t = e.get("target") or {}
            x = t.get("node") or (t.get("row") or [None])[0]
            if x:
                self.events_by_node.setdefault(x, []).append(e)
        self.items = self.index["items"]                     # number -> {node, bearing}
        self.item_of_node = {v["node"]: k for k, v in self.items.items()}
        self.claims = self.index["claims"]                   # registry id -> node
        self.commit = git("rev-parse", "HEAD") or "uncommitted"
        self.commit_date = git("log", "-1", "--format=%cs") or _dt.date.today().isoformat()
        self.narratives = self.index.get("narratives") or {}
        ppath = ROOT / "state" / "prs.json"
        self.prs = {str(p["number"]): p for p in json.loads(ppath.read_text())["prs"]} if ppath.is_file() else {}
        # parents by edge kind
        self.parents: dict[str, list[tuple[str, str]]] = {}
        for x, N in self.nodes.items():
            for c in N["children"]:
                self.parents.setdefault(c, []).append((x, "part"))
            if N.get("given"):
                base = str(N["given"]).split("@")[0]
                self.parents.setdefault(x, []).append((base, "given"))
            for r in N.get("rows") or []:
                if r.get("given"):
                    self.parents.setdefault(x, []).append((str(r["given"]).split("@")[0], "given"))
        self.held_by: dict[str, list[str]] = {}
        self.root_of: dict[str, list[tuple[str, str]]] = {}
        for x, N in self.nodes.items():
            for f in N.get("in_frames") or []:
                if f.get("membership") == "holds":
                    self.held_by.setdefault(x, []).append(f["frame"])
                else:
                    self.root_of.setdefault(x, []).append((f["frame"], f.get("role")))
        self.frame_parent: dict[str, str | None] = {}
        for x, N in self.nodes.items():
            if N.get("frame"):
                roots = [f for f, role in self.root_of.get(x, [])]
                self.frame_parent[x] = roots[0] if roots else None

    # ---- helpers the pages use
    def human_events(self, x: str) -> list:
        return [e for e in self.events_by_node.get(x, []) if e.get("by") in self.human]

    def drafted(self, x: str) -> bool:
        """AI-drafted: an AI author and no human event on it."""
        N = self.nodes[x]
        return (N.get("author") or "") not in self.human and not self.human_events(x)

    def formal_result(self, x: str) -> dict | None:
        return self.nodes[x].get("formal_result")

    def record_entry(self, x: str) -> dict | None:
        """The registry entry of a formal result node, by its registry id."""
        F = self.formal_result(x)
        if F and F.get("registry_id"):
            return self.registry.get(F["registry_id"])
        return None

    def frame_chain(self, frame_id: str) -> list[str]:
        """The frames above a frame, top first, the frame itself last."""
        chain, seen = [], set()
        f: str | None = frame_id
        while f and f != "top" and f not in seen:
            chain.append(f)
            seen.add(f)
            f = self.frame_parent.get(f)
        return list(reversed(chain))

    def lean_path(self, declaration: str) -> str | None:
        """The Lean file a fully qualified declaration lives in, by its module prefix."""
        parts = declaration.split(".")
        for k in range(len(parts) - 1, 0, -1):
            cand = ROOT / "lean" / pathlib.Path(*parts[:k]).with_suffix(".lean")
            if cand.is_file():
                return cand.relative_to(ROOT).as_posix()
        return None
