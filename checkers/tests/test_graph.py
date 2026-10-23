"""Tests for `checkers.graph`: one refusal test per rule of the specification's §3 (rules 1–13), the
synthetic graph's derivations (§7), the streams and flag-independence of the generated files, and the
fixtures under `graph/` when they exist (including the filing of a new table on the shipped fixture).

Run from the tree's root: `python3 -m unittest discover -s checkers/tests -t .` (or through `tests/run.py`).
The checker runs on one tree at a time; nothing here is parallel.
"""
from __future__ import annotations

import itertools
import json
import math
import os
import pathlib
import shutil
import sys
from collections import defaultdict
import tempfile
import time
import unittest
from fractions import Fraction as Q

HERE = pathlib.Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'checkers' / 'graph.py').is_file())
sys.path.insert(0, str(ROOT))
from checkers import graph as g  # noqa: E402

TODAY = "2026-10-02"
BASE = '"date": "2026-09-21", "rule": "2026-10-02.1", "via": "chat", "version": 1'
CHK = '"checked": [{"item": "statement factual", "how": "said"}], "not_checked": [{"item": "second source", "how": "said"}]'
# goals of the shipped graph left without AI numbers because their readings are a person's choice (Decided 2026-10-20:
# no AI forecast of a named person's actions), so a gestalt unit on them stays ranked for a human
UNJUDGED_BY_POLICY = set()


def run(root, *flags):
    """(exit code, stdout, stderr): REFUSE/WARN/OK are on stderr, JSON or a personal render on stdout."""
    return g.run_quiet(["--root", str(root), "--today", TODAY, *flags])


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.root = pathlib.Path(self.tmp) / "t"

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def tree(self, **kw):
        g.synthetic_tree(self.root, **kw)
        return self.root

    def derived(self, *flags):
        """Run and return the committed derived.json (flag-independent)."""
        code, out, err = run(self.root, *flags)
        self.assertEqual(code, 0, err)
        return json.loads((self.root / "graph" / "derived.json").read_text())

    def derived_dry(self, *flags):
        """Run with --dry-run and return the derivation printed on stdout (the personal one under flags)."""
        code, out, err = run(self.root, "--dry-run", *flags)
        self.assertEqual(code, 0, err)
        return json.loads(out)

    def refused(self, rule, *flags):
        code, out, err = run(self.root, *flags)
        self.assertNotEqual(code, 0, "expected a refusal; the checker said: " + err)
        self.assertIn(f"REFUSE {rule} ", err, err)
        return err

    def edit(self, rel, old, new):
        p = self.root / rel
        text = p.read_text()
        self.assertIn(old, text)
        p.write_text(text.replace(old, new))

    def append(self, rel, text):
        p = self.root / rel
        p.write_text(p.read_text() + text)


_SUP_CACHE = {}       # (context id, node) -> support set, for the oracle's per-world loops


# ---------------------------------------------------------------- the oracle: the landed world-model enumerator
# A copy of the checker's 0.3 enumeration (`world_model`, `holds`, `world_value`, `root_numbers`), used only by the
# tests as the reference the recursion must match exactly. Generalised in two places the recursion needs and the
# 0.3 code had no use for: a variable's factor may read its `given` parent's truth in the world, and a formula
# may be `X@valid`. Under `variables` = a root's proof set it is the 0.3 computation exactly.
def oracle_holds(C, W, combo, x, valid=None):
    t = C.t
    if isinstance(x, str) and x.endswith("@valid"):
        return oracle_holds(C, W, combo, x[:-len("@valid")], valid=x[:-len("@valid")])
    n = t.nodes[x]
    if valid is not None and n.get("kind") == "leaf" and n.get("leaf_kind") in ("assumption", "hypothesis"):
        key = (id(C), valid)
        if key not in _SUP_CACHE:
            _SUP_CACHE[key] = g.support(t, valid)
        if x in _SUP_CACHE[key]:
            return True
    if x in W["idx"]:
        return combo[W["idx"][x]][0]
    kind = n.get("kind")
    if kind in ("leaf", "cases"):
        return False
    kids = n["children"]
    if kind == "choose" and n.get("committed", "none") != "none":
        kids = [n["committed"]]
    if kind == "frame":
        kids = g.plan_children(t, x)
    return (all if kind == "and" else any)(oracle_holds(C, W, combo, c, valid) for c in kids)


def _oracle_p(b, pmode):
    if b is None:
        return Q(1, 2)
    return {"mid": b["mid"], "lo": b["range"][0], "hi": b["range"][1]}[pmode]


def oracle_world(C, variables, pmode="mid"):
    """Every world over `variables` with its probability; a factor reads its given parent's truth in the world."""
    t = C.t
    variables = sorted(variables, key=lambda x: (t.nodes[x].get("kind") == "cases", x))
    outcomes = []
    for x in variables:
        n = t.nodes[x]
        if n.get("kind") == "cases":
            rb = g.row_beliefs(C, x)
            outs = [(True, None, None), (False, C.outside, None)] if not rb else []
            for pic in rb:
                outs += [(True, None, pic), (False, "row", pic)]
            outcomes.append(outs)
        else:
            b = C.bel.get((("node", x), "range"))
            if not n.get("given") and b is not None and _oracle_p(b, pmode) in (0, 1):
                outcomes.append([(_oracle_p(b, pmode) == 1, None, None)])     # a certain leaf has one outcome
            else:
                outcomes.append([(True, None, None), (False, None, None)])
    idx = {x: i for i, x in enumerate(variables)}
    W = {"vars": variables, "idx": idx}
    worlds = []
    RB = {x: g.row_beliefs(C, x) for x in variables if t.nodes[x].get("kind") == "cases"}
    for combo in itertools.product(*outcomes):
        prob = Q(1)
        for x, o in zip(variables, combo):
            n = t.nodes[x]
            if n.get("kind") == "cases":
                rb = RB[x]
                if not rb:
                    prob *= Q(1, 2)
                    continue
                row = next(r for r in n["rows"] if r["picture"] == o[2])
                b = rb[o[2]]
                if row.get("given"):
                    side = oracle_holds(C, W, combo, row["given"])
                    bel = C.bel.get((("row", x, o[2]), "p-if-holds" if side else "p-if-fails")) or C.bel.get((("row", x, o[2]), "p"))
                    pr = _oracle_p(bel, pmode) if bel else {"mid": Q(1, 2), "lo": Q(0), "hi": Q(1)}[pmode]
                else:
                    pr = {"mid": b["p"][0], "lo": max(Q(0), b["p"][0] - b["p"][1] / 2), "hi": min(Q(1), b["p"][0] + b["p"][1] / 2)}[pmode]
                prob *= b["w"][0] * (pr if o[0] else 1 - pr)
            else:
                plain = C.bel.get((("node", x), "range"))
                if n.get("given"):
                    side = oracle_holds(C, W, combo, n["given"])
                    bel = C.bel.get((("node", x), "if-holds" if side else "if-fails")) or plain
                else:
                    bel = plain
                pr = _oracle_p(bel, pmode)
                prob *= pr if o[0] else 1 - pr
        if prob > 0:
            worlds.append((combo, prob))
    return W, worlds


def oracle_class(C, W, combo, x):
    """The failure class of a failing variable in a world (a row's class, a class_given side), or None."""
    t = C.t
    o = combo[W["idx"][x]]
    n = t.nodes[x]
    if n.get("kind") == "cases":
        if o[2] is None:
            return o[1]
        row = next(r for r in n["rows"] if r["picture"] == o[2])
        cls = C.row_class[(x, o[2])]
        cg = row.get("class_given") if isinstance(row.get("class_given"), dict) else {}
        if row.get("given") and cg:
            side = oracle_holds(C, W, combo, row["given"])
            return cg.get("holds" if side else "fails") or cls
        return cls
    cg = n.get("class_given") if isinstance(n.get("class_given"), dict) else {}
    if n.get("given") and cg:
        return cg.get("holds" if oracle_holds(C, W, combo, n["given"]) else "fails")
    return None


def oracle_value(C, W, combo, rid, umode="mid"):
    r = C.roots[rid]
    if oracle_holds(C, W, combo, rid):
        return g.utility(C, r["success_class"], umode)
    key = (id(C), rid)
    if key not in _SUP_CACHE:
        _SUP_CACHE[key] = g.support(C.t, rid)
    sup = _SUP_CACHE[key]
    fails = [oracle_class(C, W, combo, x) for x in W["vars"] if x in sup and not combo[W["idx"][x]][0]]
    fails = [c for c in fails if c]
    if not fails:
        return g.utility(C, C.outside, umode)
    worst = min(fails, key=lambda c: (g.utility(C, c), (C.cls.get(c) or {}).get("severity") is None, (C.cls.get(c) or {}).get("severity") or 0))
    return g.utility(C, worst, umode)


def enumerate_oracle(C, rid, variables, formula=None, modes=("mid", "lo", "hi")):
    """Pr (of `formula`, default the root) and value (plan roots) at the given modes, by enumeration over `variables`."""
    out = {"Pr": {}, "value": {}}
    for mode in modes:
        W, worlds = oracle_world(C, variables, mode)
        out["Pr"][mode] = sum((p for c, p in worlds if oracle_holds(C, W, c, formula or rid)), Q(0))
        if C.roots.get(rid, {}).get("role") == "plan" and C.t.nodes[rid].get("kind") != "frame":
            out["value"][mode] = sum((p * oracle_value(C, W, c, rid, mode) for c, p in worlds), Q(0))
    return out


def oracle_bits_and_D(C, D, rid, x, e=Q(0)):
    """Bits about one root's truth and D (one plan against the outside option) of a noisy observation of x, by enumeration."""
    W, worlds = oracle_world(C, C.psets[rid] if C.E.or_mode == "cheapest" else C.E.closure((C.E.key_of(rid),)))
    obs = {}
    for c, p in worlds:
        tr = c[W["idx"][x]][0] if x in W["idx"] else oracle_holds(C, W, c, x)
        for o, wgt in ((tr, 1 - e), (not tr, e)):
            if wgt:
                obs.setdefault(o, []).append((c, p * wgt))
    h2 = lambda p: 0.0 if p <= 0 or p >= 1 else -(p * math.log2(p) + (1 - p) * math.log2(1 - p))
    pg = float(sum((p for c, p in worlds if oracle_holds(C, W, c, rid)), Q(0)))
    eh, Dv = 0.0, Q(0)
    out_u = g.utility(C, C.outside)
    V0 = max(out_u, sum((p * oracle_value(C, W, c, rid) for c, p in worlds), Q(0)))
    for o, ws in obs.items():
        po = sum((w for _, w in ws), Q(0))
        hg = sum((w for c, w in ws if oracle_holds(C, W, c, rid)), Q(0))
        eh += float(po) * h2(float(hg / po))
        Dv += po * max(out_u, sum((w * oracle_value(C, W, c, rid) for c, w in ws), Q(0)) / po)
    return max(0.0, h2(pg) - eh), Dv - V0


def context(root, today=TODAY):
    """The derivation context (beliefs, proof sets, the engine) of a tree, through derive's test hook."""
    t = g.load_tree(root)
    g.lint(t)
    out = []
    D = g.derive(t, today=g._dt.date.fromisoformat(today), ctx_out=out)
    return out[0], D


class Refusals(Base):
    def test_rule1_unresolved_child(self):
        self.tree()
        self.edit("graph/nodes/plan-a.md", "[shared-leaf, cases-x", "[ghost, cases-x")
        self.refused(1)

    def test_rule1_parentless_not_a_root(self):
        self.tree()
        self.edit("graph/nodes/plan-b.md", "or-y, ", "")
        self.refused(1)

    def test_rule1_duplicate_event_id_across_ledgers(self):
        self.tree(extra={"h2": [f'{{"id": "h1-1", "by": "@h2", {BASE}, "kind": "estimate", "target": {{"node": "alt-2"}}, "estimate": [0.1, 0.2]}}']})
        self.refused(1)   # the id is taken (and would also break rule 5's prefix)

    def test_rule2_unknown_kind(self):
        self.tree()
        self.edit("graph/nodes/cases-x.md", "kind: cases", "kind: table")
        self.refused(2)

    def test_rule2_and_without_completeness(self):
        self.tree()
        self.edit("graph/nodes/plan-a.complete.md", "leaf_kind: completeness", "leaf_kind: step")
        self.refused(2)

    def test_rule2_task_kinds_are_not_event_kinds(self):
        for kind in ("re-examine", "reconcile", "vet"):
            self.tree(extra={"h1": [f'{{"id": "h1-40", "by": "@h1", {BASE}, "kind": "{kind}", "target": {{"node": "alt-2"}}}}']})
            self.assertIn("unknown event kind", self.refused(2))

    def test_rule3_evaluative_word(self):
        self.tree()
        self.edit("graph/nodes/alt-1.md", "carries the collapse.", "probably carries the collapse.")
        self.refused(3)

    def test_rule4_typed_level(self):
        self.tree()
        self.edit("graph/nodes/shared-leaf.md", "size: S\n", "size: S\ncredence: 0.5\n")
        self.refused(4)

    def test_rule4_statement_changed_without_bump(self):
        self.tree()
        self.derived()
        self.edit("graph/nodes/alt-2.md", "exact-introspection expert model", "exact-introspection expert")
        self.refused(4)

    def test_rule4_punctuation_only_change_needs_no_bump(self):
        self.tree()
        self.derived()
        self.edit("graph/nodes/alt-2.md", "The exact-introspection expert model carries", "The exact-introspection expert model, carries")
        self.edit("graph/nodes/shared-leaf.md", "The expert's estimate", "The experts estimate")
        self.edit("graph/nodes/alt-1.md", "The asymptotic-introspection expert", "The asymptotic introspection expert")
        self.assertEqual(run(self.root)[0], 0)
        self.edit("graph/nodes/alt-2.md", "version: 1\n", "version: 2\n")
        self.assertIn("unchanged Statement", self.refused(4))

    def test_rule5_missing_field_and_what_an_ai_handle_may_not_write(self):
        self.tree()
        self.edit("graph/events/h1.jsonl", '"rule": "2026-10-02.1", "via": "chat", "version": 1, "kind": "map-read", "target": {"node": "shared-leaf"}',
                  '"via": "chat", "version": 1, "kind": "map-read", "target": {"node": "shared-leaf"}')
        self.refused(5)
        # an AI estimate without its reasoning in gloss is refused; so is any level-minting event, acceptance or tag by an AI
        self.tree(extra={"ai": [f'{{"id": "ai-30", "by": "@ai", {BASE}, "kind": "estimate", "target": {{"node": "alt-2"}}, "estimate": [0.1, 0.2]}}']})
        self.assertIn("gloss", self.refused(5))
        self.tree(extra={"ai": [f'{{"id": "ai-31", "by": "@ai", {BASE}, "kind": "map-read", "target": {{"node": "alt-2"}}, {CHK}}}']})
        self.assertIn("mints no vettedness level", self.refused(5))
        self.tree(extra={"ai": [f'{{"id": "ai-32", "by": "@ai", {BASE}, "kind": "external", "target": {{"node": "alt-2"}}, "ref": "x"}}']})
        self.assertIn("mints no vettedness level", self.refused(5))
        self.tree(pic_h_author="@ai", extra={"ai": [f'{{"id": "ai-33", "by": "@ai", {BASE}, "kind": "admit", "target": {{"row": ["cases-x", "pic-h"]}}, "estimate": "accept"}}']})
        self.assertIn("writes no admit", self.refused(5))
        self.tree(extra={"ai": [f'{{"id": "ai-34", "by": "@ai", {BASE}, "kind": "classify", "target": {{"row": ["cases-x", "pic-r"], "field": "class"}}, "estimate": "high-conflict"}}']})
        self.assertIn("writes no classify", self.refused(5))

    def test_ai_judgments_count_at_j0_until_a_human_supersedes_them(self):
        # ruling 34: an AI estimate counts at J 0 "generated" (width 1), flags the node, and marks the units and roots that rest on it
        ai = f'{{"id": "ai-40", "by": "@ai", {BASE}, "kind": "estimate", "target": {{"node": "alt-2"}}, "estimate": [0.6, 0.8], "gloss": "the exactness assumption is strong but the proof carries it"}}'
        self.tree(drop={"h2-10"}, extra={"ai": [ai]})
        D = self.derived()
        B = D["judgments"]["node/alt-2/range"]
        self.assertEqual((B["J"], Q(B["mid"]), Q(B["width"]), B["generated"], B["by"]), (0, Q(7, 10), Q(1), True, ["@ai"]))
        self.assertIn("generated", B["flags"])
        self.assertIn("AI number", D["nodes"]["alt-2"]["flags"])
        # a human judgment on the same quantity supersedes the AI's; the AI event stays counted as history
        self.tree(extra={"ai": [ai]})                                       # h2-10 ([0.5, 0.7], J 8) present again
        D = self.derived()
        B = D["judgments"]["node/alt-2/range"]
        self.assertEqual((B["J"], Q(B["mid"]), B["generated"], B["by"], B["superseded_ai"]), (8, Q(3, 5), False, ["@h2"], ["@ai"]))
        self.assertIn("ai-40", D["events"]["counted"])
        self.assertNotIn("AI number", D["nodes"]["alt-2"]["flags"])
        # an AI conditional below the bar concedes nothing (status needs J 8), and the number is marked wherever it feeds
        ai_p = f'{{"id": "ai-41", "by": "@ai", {BASE}, "kind": "estimate", "target": {{"row": ["cases-x", "pic-h"], "field": "p"}}, "estimate": [0.1, 0.3], "gloss": "oscillation looks likely to break convergence"}}'
        self.tree(drop={"h2-12"}, extra={"ai": [ai_p]})
        D = self.derived()
        self.assertEqual(D["nodes"]["cases-x"]["status"], "open")
        self.assertEqual(D["nodes"]["cases-x"]["rows"]["pic-h"]["p"][2], ["AI number"])
        self.assertTrue(D["roots"]["plan-a"]["Pr_defined"])                  # the AI number counts: no "no belief"
        self.assertEqual(D["roots"]["plan-a"]["ai_only"], ["cases-x"])
        self.assertEqual(D["roots"]["plan-b"]["ai_only"], [])
        u = next(u for u in D["units"] if u["kind"] == "vet" and u["target"] == "cases-x")
        self.assertTrue(u["ai_number"])
        self.assertIn("vet cases-x (S) — for plan-a — vet this AI number", (self.root / "graph" / "tasks.md").read_text())   # the line format
        self.assertIn("rests on AI numbers (no human judgment yet): cases-x", (self.root / "graph" / "view.md").read_text())
        # an AI gestalt stands in like any gestalt, at J 0, and is marked
        ai_g = f'{{"id": "ai-42", "by": "@ai", {BASE}, "kind": "gestalt", "target": {{"node": "plan-b"}}, "estimate": [0.2, 0.4], "derived": false, "gloss": "a question leaf still blocks the plan"}}'
        self.tree(drop={"h2-9"}, extra={"ai": [ai_g]})                       # plan-b's derived probability is undefined
        D = self.derived()
        G = D["roots"]["plan-b"]["gestalt"]
        self.assertEqual((G["J"], Q(G["mid"]), G["generated"]), (0, Q(3, 10), True))
        self.assertEqual(Q(D["roots"]["plan-b"]["option_value"]), Q(3, 10))
        self.assertIn("plan-b", D["roots"]["plan-b"]["ai_only"])
        self.assertFalse([u for u in D["units"] if u["kind"] == "gestalt" and u["target"] == "plan-b"])
        self.assertIn("(AI gestalt)", run(self.root, "--why")[1])

    def test_rule5_event_id_carries_the_ledgers_handle(self):
        self.tree(extra={"h1": [f'{{"id": "h2-99", "by": "@h1", {BASE}, "kind": "estimate", "target": {{"node": "alt-2"}}, "estimate": [0.1, 0.2], "reason": "x"}}']})
        self.assertIn("'<handle>-<suffix>'", self.refused(5))
        self.tree(extra={"h1": [f'{{"id": "e-099", "by": "@h1", {BASE}, "kind": "estimate", "target": {{"node": "alt-2"}}, "estimate": [0.1, 0.2], "reason": "x"}}']})
        self.refused(5)

    def test_rule5_rule_version_format(self):
        self.tree(extra={"h1": ['{"id": "h1-41", "by": "@h1", "date": "2026-09-21", "rule": "v1", "via": "chat", "version": 1, "kind": "estimate", "target": {"node": "alt-2"}, "estimate": [0.1, 0.2], "reason": "x"}']})
        self.assertIn("anchor-rules version", self.refused(5))

    def test_rule5_gestalt_carries_derived_false(self):
        self.tree(extra={"h1": [f'{{"id": "h1-42", "by": "@h1", {BASE}, "kind": "gestalt", "target": {{"node": "plan-a"}}, "estimate": [0.1, 0.3], "reason": "x"}}']})
        self.assertIn("derived: false", self.refused(5))
        self.tree(extra={"h1": [f'{{"id": "h1-42", "by": "@h1", {BASE}, "kind": "gestalt", "target": {{"node": "plan-a"}}, "estimate": [0.1, 0.3], "reason": "x", "derived": false}}']})
        self.assertEqual(run(self.root)[0], 0)

    def test_rule5_external_carries_ref(self):
        self.tree(extra={"h2": [f'{{"id": "h2-43", "by": "@h2", {BASE}, "kind": "external", "target": {{"node": "shared-leaf"}}}}']})
        self.assertIn("carries ref", self.refused(5))

    def test_rule5_audit_shape(self):
        self.tree(extra={"h2": [f'{{"id": "h2-44", "by": "@h2", {BASE}, "kind": "audit", "target": {{"event": "h1-1"}}}}']})
        self.assertIn("verdict", self.refused(5))
        self.tree(extra={"h2": [f'{{"id": "h2-44", "by": "@h2", {BASE}, "kind": "audit", "target": {{"node": "shared-leaf"}}, "verdict": "agree"}}']})
        self.refused(5)

    def test_rule5_maintainer_required(self):
        self.tree()
        self.edit("graph/policy.yaml", 'maintainer: "@h1"\n', "")
        self.assertIn("maintainer", self.refused(5))

    def test_rule6_unresolved_turns(self):
        self.tree()
        self.edit("graph/events/h1.jsonl", '"reason": "the list is short"}', '"reason": "the list is short", "question": "chats/s-1.jsonl#t1", "answer": "chats/s-1.jsonl#t2", "verbatim": "nine in ten"}')
        self.refused(6)

    def test_rule7_hand_edit(self):
        self.tree()
        self.derived()
        p = self.root / "graph" / "tasks.md"
        p.write_text(p.read_text().replace("## Lines", "## Lines\n- a hand-written line"))
        self.refused(7)

    def test_rule7_versions_json_hand_edit(self):
        self.tree()
        self.derived()
        p = self.root / "graph" / "versions.json"
        self.assertIn("generated_hash", json.loads(p.read_text()))
        p.write_text(p.read_text().replace("carries the collapse", "carries the collapse edited"))
        self.assertIn("versions.json", self.refused(7))

    def test_rule8_plan_without_success_class(self):
        self.tree()
        self.edit("graph/frame.yaml", "{id: plan-a, role: plan, preset: worst-case, success_class: utopia}", "{id: plan-a, role: plan, preset: worst-case}")
        self.refused(8)

    def test_rule9_approved_without_approve(self):
        self.tree()
        (self.root / "graph" / "proposals" / "P-1.md").write_text(
            "---\nid: P-1\nkind: edge\nauthor: \"@ai\"\nstatus: approved\ntargets: [plan-b]\nops:\n  - {op: add-child, parent: plan-b, child: alt-2}\n---\n## Change\nIllustrative.\n## Delta\n")
        self.refused(9)

    def test_rule10_range_outside_unit_interval(self):
        self.tree()
        self.edit("graph/events/h2.jsonl", '"estimate": [0.85, 0.95], "reason": "the notion', '"estimate": [0.85, 1.2], "reason": "the notion')
        self.refused(10)

    def test_rule11_design_log_missing(self):
        self.tree()
        (self.root / "graph" / "DESIGN-LOG.md").unlink()
        self.refused(11)

    def test_rule11_personal_render_not_under_graph(self):
        self.tree()
        self.refused(11, "--why", "--out", str(self.root / "graph" / "mine.md"))

    def test_rule12_frontmatter_unclosed(self):
        self.tree()
        self.edit("graph/nodes/alt-2.md", "version: 1\n---\n", "version: 1\n")
        self.refused(12)

    def test_rule13_cutset_too_large(self):
        # one formula whose closure reaches a variable by two paths pays for it in its cutset; the cap is per formula
        def share(nodes):
            nodes["or-y"] = ("or", "S", {"children": "[cheap-leaf, dear-leaf, shared-leaf]"}, nodes["or-y"][3])
        self.tree(tweak=share)
        saved = g.MAX_CUTSET_WORLDS
        try:
            g.MAX_CUTSET_WORLDS = 1
            err = self.refused(13)
            self.assertIn("cutset too large", err)
            self.assertIn("plan-b", err)          # names the formula
            self.assertIn("shared-leaf", err)     # its cutset
            self.assertIn("2 assignments", err)   # and the count
        finally:
            g.MAX_CUTSET_WORLDS = saved
        D = self.derived()
        big = D["inference"]["largest"]
        self.assertEqual((big[0]["phi"], big[0]["cutset"], big[0]["assignments"]), ("plan-b", ["shared-leaf"], 2))
        self.assertEqual(D["inference"]["cap"], 1 << 15)

    def test_null_inputs_fail_in_self_test(self):
        code, out, err = g.run_quiet(["--self-test"])
        self.assertEqual(code, 0, out + err)


def make_table(nodes):
    """Tweak for synthetic_tree: alt-1 (a leaf with a range, h1-6) becomes a two-row table."""
    nodes["alt-1"] = ("cases", "S", {"children": "[alt-1.partition, pic-z, pic-zr]",
                                     "rows": "\n  - {picture: pic-z, class: null, observable: never}\n  - {picture: pic-zr, class: undescribed-failure, observable: never, residual: true}"},
                      "The asymptotic-introspection expert model carries the collapse.")
    nodes["alt-1.partition"] = ("leaf", "S", {"leaf_kind": "partition"}, "The pictures of alt-1 are exclusive and exhaustive.")
    nodes["pic-z"] = ("leaf", "S", {"leaf_kind": "picture", "author": "@h2"}, "The expert's introspection fails to converge in the deployment horizon.")
    nodes["pic-zr"] = ("leaf", "S", {"leaf_kind": "picture", "author": "@h2"}, "The claim fails for a reason not yet described.")


def concede_steps(nodes):
    """Tweak for synthetic_tree(programme=True): both plan steps become two-row tables (events in STEP_TABLE_EVENTS concede them)."""
    for s, size in (("step-1", "M"), ("step-2", "L")):
        nodes[s] = ("cases", size, {"children": f"[{s}.partition, pic-{s[-2:].replace('-', 's')}, pic-{s[-2:].replace('-', 's')}r]",
                                    "rows": f"\n  - {{picture: pic-{s[-2:].replace('-', 's')}, class: null, observable: never}}"
                                            f"\n  - {{picture: pic-{s[-2:].replace('-', 's')}r, class: undescribed-failure, observable: never, residual: true}}"},
                    nodes[s][3])
        nodes[f"{s}.partition"] = ("leaf", "S", {"leaf_kind": "partition"}, f"The pictures of {s} are exclusive and exhaustive.")
        p = f"pic-{s[-2:].replace('-', 's')}"
        nodes[p] = ("leaf", "S", {"leaf_kind": "picture", "author": "@h2"}, "The step's bound fails to transfer in the bounded setting.")
        nodes[p + "r"] = ("leaf", "S", {"leaf_kind": "picture", "author": "@h2"}, "The step fails for a reason not yet described.")


STEP_TABLE_EVENTS = [
    f'{{"id": "h2-7{i}{j}", "by": "@h2", {BASE}, "kind": "estimate", "target": {{"row": ["step-{i}", "pic-s{i}{r}"], "field": "{f}"}}, "estimate": {rng}, "reason": "the toy bound"}}'
    for i in (1, 2) for j, (r, f, rng) in enumerate((("", "w", "[0.6, 0.8]"), ("", "p", "[0.1, 0.3]"), ("r", "p", "[0.9, 1]")))
] + [f'{{"id": "h2-7{i}9", "by": "@h2", {BASE}, "kind": "estimate", "target": {{"node": "step-{i}.partition"}}, "estimate": [1, 1], "reason": "a residual row is present"}}' for i in (1, 2)]


class Synthetic(Base):
    def test_statuses_under_d6(self):
        self.tree()
        D = self.derived()
        N = D["nodes"]
        self.assertEqual(N["or-y"]["status"], "established")          # cheap-leaf established suffices
        self.assertEqual(N["choose-c"]["status"], "open")
        self.assertEqual(N["cases-x"]["status"], "open")
        self.assertEqual(N["shared-leaf"]["status"], "established")
        self.assertEqual(D["roots"]["plan-a"]["status"], "open")
        self.assertEqual(N["q-leaf"]["status"], "open")

    def test_j6_conditional_concedes_nothing_j8_concedes(self):
        self.tree(p_h=["0.2", "0.4"], p_reason=False)
        D = self.derived()
        self.assertEqual(D["nodes"]["cases-x"]["status"], "open")
        self.assertIn("unread-weighted", D["nodes"]["pic-h"]["flags"])
        self.tree(p_h=["0.2", "0.4"], p_reason=True)
        D = self.derived()
        self.assertEqual(D["nodes"]["cases-x"]["status"], "conceded")
        self.assertEqual(D["nodes"]["cases-x"]["diagnosis"], "pic-h")
        self.assertIn("conceded by pic-h", D["nodes"]["cases-x"]["flags"])
        self.assertEqual(D["nodes"]["cases-x"]["load"], ["plan-a"])
        self.assertEqual(D["roots"]["plan-a"]["status"], "conceded")
        self.assertEqual(D["roots"]["plan-b"]["status"], "open")
        self.assertIn("plan-a", D["roots"])                           # a conceded root stays in the graph

    def test_load_counts_only_roots_the_node_supports(self):
        self.tree(p_h=["0.2", "0.4"], p_reason=True)                  # plan-a conceded through cases-x
        D = self.derived()
        self.assertEqual(D["nodes"]["q-leaf"]["load"], ["plan-b"])    # plan-a is conceded anyway but does not contain q-leaf
        self.assertEqual(D["nodes"]["cases-x"]["load"], ["plan-a"])
        self.assertEqual(D["nodes"]["alt-2"]["load"], [])              # the other branch of a choose carries nothing
        self.assertEqual(D["nodes"]["shared-leaf"]["load"], ["plan-b"])   # plan-a is conceded whether or not shared-leaf holds

    def test_residual_weight_is_the_remainder(self):
        D = (self.tree(), self.derived())[1]
        rows = D["nodes"]["cases-x"]["rows"]
        self.assertEqual(rows["pic-h"]["w"][0], "3/10")
        self.assertEqual(rows["pic-r"]["w"][0], "7/10")

    def test_proof_set_shared_once_cheapest_or_child(self):
        D = (self.tree(), self.derived())[1]
        self.assertEqual(D["roots"]["plan-b"]["proof_set"], ["cheap-leaf", "plan-b.complete", "q-leaf", "shared-leaf"])
        self.assertIn("shared-leaf", D["roots"]["plan-a"]["proof_set"])
        self.assertEqual(D["roots"]["plan-a"]["choice"], {"choose-c": "alt-1"})
        self.assertEqual(D["nodes"]["shared-leaf"]["load"], ["plan-a", "plan-b"])

    def test_question_leaf_infinite_cost_no_unit(self):
        D = (self.tree(), self.derived())[1]
        self.assertEqual(D["roots"]["plan-b"]["cost"], "inf")
        self.assertEqual(D["nodes"]["q-leaf"]["cost"], "inf")
        # a question gets `improve` (the landed skip of question leaves goes), and no vet, map-read or trace
        self.assertEqual([u["kind"] for u in D["units"] if u["target"] == "q-leaf"], ["improve"])

    def test_withdraw_drops_v_and_flags(self):
        self.tree(drop={"h1-2"})
        self.assertEqual(self.derived()["nodes"]["shared-leaf"]["V"]["headline"], 6)
        self.tree(drop={"h1-2"}, extra={"h1": [f'{{"id": "h1-21", "by": "@h1", {BASE}, "kind": "withdraw", "target": {{"event": "h1-1"}}}}']})
        D = self.derived()
        self.assertEqual(D["nodes"]["shared-leaf"]["V"]["headline"], 2)
        self.assertIn("withdrawn", D["nodes"]["shared-leaf"]["flags"])
        self.assertIn("h1-1", D["events"]["withdrawn"])

    def test_proposed_picture_enters_nothing_until_admit(self):
        self.tree(pic_h_author="@ai")
        D = self.derived()
        self.assertFalse(D["nodes"]["cases-x"]["admitted"]["pic-h"])
        self.assertNotIn("pic-h", D["nodes"]["cases-x"]["rows"])
        self.assertIn("under attack", D["nodes"]["cases-x"]["flags"])
        quick = next(u for u in D["units_unranked"] if u["kind"] == "admit" and u["target"] == "cases-x")   # one quick line per table
        self.assertEqual(quick["rows"], ["pic-h"])
        self.assertIn(("admit", "cases-x"), [(u["kind"], u["target"]) for u in D["units"]])                # and a ranked read of the rows
        self.tree(pic_h_author="@ai", extra={"h1": [f'{{"id": "h1-22", "by": "@h1", {BASE}, "kind": "admit", "target": {{"row": ["cases-x", "pic-h"]}}, "estimate": "accept"}}']})
        D = self.derived()
        self.assertTrue(D["nodes"]["cases-x"]["admitted"]["pic-h"])
        self.assertIn("pic-h", D["nodes"]["cases-x"]["rows"])

    def test_stale_level_event_does_not_count(self):
        # a map-read at v1 on a node now at v2 no longer counts toward the headline; it shows as "read at v1: 6"
        self.tree(shared_version=2, drop={"h1-2"})
        D = self.derived()
        V = D["nodes"]["shared-leaf"]["V"]
        self.assertEqual((V["headline"], V["V_prior"]), (2, {"level": 6, "version": 1}))
        self.assertEqual(V["display"], "2 · read at v1: 6")
        self.assertIn("revised since read (v1 → v2)", D["nodes"]["shared-leaf"]["flags"])
        # a range given at v1 still counts, flagged stale, its floor read at the current level
        self.assertIn("stale", D["nodes"]["shared-leaf"]["flags"])
        self.assertIn("h1-1", D["events"]["stale"])
        self.assertIn("version 1, now 2", D["events"]["stale_reasons"]["h1-1"])
        self.assertEqual(Q(D["judgments"]["node/shared-leaf/range"]["mid"]), Q(7, 10))
        self.assertEqual(Q(D["judgments"]["node/shared-leaf/range"]["width"]), Q(1))      # the current level (2) sets the floor

    def test_revise_and_draft(self):
        self.tree(shared_version=2)
        D = self.derived()
        self.assertEqual(D["nodes"]["shared-leaf"]["draft"], "ai")                        # authored by an AI, no event at v2
        rev = f'{{"id": "h1-80", "by": "@h1", "date": "2026-09-21", "rule": "2026-10-02.1", "via": "chat", "version": 2, "kind": "revise", "target": {{"node": "shared-leaf"}}, "from": {{"version": 1}}, "verbatim": "split the case analysis", "gloss": "rewrote the case split", "minutes": 20}}'
        self.append("graph/events/h1.jsonl", rev + "\n")
        D = self.derived()
        self.assertIn("human-revised (@h1, v2)", D["nodes"]["shared-leaf"]["flags"])
        self.assertEqual(D["revisions"], {"@h1": 1})
        self.assertEqual(D["nodes"]["shared-leaf"]["draft"], "human-revised")
        self.assertEqual(D["nodes"]["shared-leaf"]["V"]["headline"], 2)                    # a revise mints no level
        self.assertIn("shared-leaf (v2)", D["digest"]["revisions"])
        read = f'{{"id": "h1-81", "by": "@h1", "date": "2026-09-22", "rule": "2026-10-02.1", "via": "chat", "version": 2, "kind": "map-read", "target": {{"node": "shared-leaf"}}, {CHK}}}'
        self.append("graph/events/h1.jsonl", read + "\n")
        D = self.derived()
        self.assertEqual((D["nodes"]["shared-leaf"]["draft"], D["nodes"]["shared-leaf"]["V"]["headline"]), ("read", 6))

    def test_reread_is_priced_from_its_own_row(self):
        self.tree(shared_version=2, drop={"h1-2"})
        D = self.derived()
        units = {u["kind"]: u for u in D["units"] if u["target"] == "shared-leaf"}
        self.assertEqual(Q(units["map-read"]["minutes"]), Q(4))                           # reread[S]
        self.assertEqual(Q(units["vet"]["minutes"]), Q(4 + 25))
        self.assertTrue(any(w.startswith("re-read: at v1 you checked statement factual") for w in units["map-read"]["why"]))
        self.root = pathlib.Path(self.tmp) / "fresh"
        self.tree(drop={"h1-1", "h1-2"})                                                  # never read: the ordinary map-read row
        D = self.derived()
        units = {u["kind"]: u for u in D["units"] if u["target"] == "shared-leaf"}
        self.assertEqual(Q(units["map-read"]["minutes"]), Q(8))

    def test_leaf_range_is_stale_once_the_leaf_is_a_table(self):
        self.tree(tweak=make_table)
        D = self.derived()
        self.assertIn("h1-6", D["events"]["stale"])
        self.assertEqual(D["events"]["stale_reasons"]["h1-6"], "leaf became a table")
        self.assertIn("stale: leaf became a table", D["nodes"]["alt-1"]["flags"])
        self.assertEqual(D["nodes"]["alt-1"]["kind"], "cases")
        self.assertIsNone(D["nodes"]["alt-1"]["belief"])             # the range is not a belief on the table
        self.assertEqual(D["nodes"]["alt-1"]["stale_leaf_ranges"][0]["event"], "h1-6")
        sug = [u for u in D["units_unranked"] if u["target"] == "alt-1/pic-zr.p"]
        self.assertTrue(sug and "suggestion, not used" in sug[0]["note"] and "h1-6" in sug[0]["note"], sug)
        self.assertIn("suggestion, not used", (self.root / "graph" / "tasks.md").read_text())

    def test_attribution_flag_cleared_only_by_an_attribution_event(self):
        self.tree()
        D = self.derived()
        self.assertIn("attribution unvetted", D["nodes"]["shared-leaf"]["flags"])   # reconstructed; nobody has vouched for it
        # neither an external record nor a said "attribution honest" item clears the flag any more
        self.tree(extra={"h2": [f'{{"id": "h2-50", "by": "@h2", {BASE}, "kind": "external", "target": {{"node": "shared-leaf"}}, "ref": "doi:10.1/x"}}']})
        self.assertIn("attribution unvetted", self.derived()["nodes"]["shared-leaf"]["flags"])
        said_attr = f'{{"id": "h2-51", "by": "@h2", {BASE}, "kind": "map-read", "target": {{"node": "shared-leaf"}}, "checked": [{{"item": "attribution honest", "how": "said"}}], "not_checked": [{{"item": "second source", "how": "said"}}]}}'
        self.tree(extra={"h2": [said_attr]})
        self.assertIn("attribution unvetted", self.derived()["nodes"]["shared-leaf"]["flags"])
        # an attribution event by a non-author human with a verdict and a ref clears it; disputed also flags the dispute
        vouch = f'{{"id": "h2-52", "by": "@h2", {BASE}, "kind": "attribution", "target": {{"node": "shared-leaf"}}, "verdict": "vouched", "ref": "mart-implies-value.md, Remark"}}'
        self.tree(extra={"h2": [vouch]})
        D = self.derived()
        self.assertNotIn("attribution unvetted", D["nodes"]["shared-leaf"]["flags"])
        self.assertFalse([f for f in D["nodes"]["shared-leaf"]["flags"] if f.startswith("attribution")])
        self.assertEqual(D["nodes"]["shared-leaf"]["V"]["headline"], 8)          # an attribution event moves no level
        dispute = vouch.replace("h2-52", "h2-53").replace("vouched", "disputed")
        self.tree(extra={"h2": [dispute]})
        D = self.derived()
        self.assertNotIn("attribution unvetted", D["nodes"]["shared-leaf"]["flags"])
        self.assertIn("attribution disputed (@h2)", D["nodes"]["shared-leaf"]["flags"])

    def test_rule5_attribution_event_shape(self):
        base = f'"by": "@h2", {BASE}, "kind": "attribution", "target": {{"node": "shared-leaf"}}'
        self.tree(extra={"h2": [f'{{"id": "h2-54", {base}, "ref": "x"}}']})
        self.assertIn("verdict", self.refused(5))
        self.tree(extra={"h2": [f'{{"id": "h2-54", {base}, "verdict": "vouched"}}']})
        self.assertIn("ref", self.refused(5))
        self.tree(extra={"h2": [f'{{"id": "h2-54", {base}, "verdict": "maybe", "ref": "x"}}']})
        self.refused(5)
        # pic-r is authored by @h2: the author cannot vouch for their own attribution
        self.tree(extra={"h2": [f'{{"id": "h2-54", "by": "@h2", {BASE}, "kind": "attribution", "target": {{"node": "pic-r"}}, "verdict": "vouched", "ref": "x"}}']})
        self.assertIn("other than the node's author", self.refused(5))
        self.tree(extra={"ai": [f'{{"id": "ai-54", "by": "@ai", {BASE}, "kind": "attribution", "target": {{"node": "shared-leaf"}}, "verdict": "vouched", "ref": "x"}}']})
        self.refused(5)

    def test_gestalt_width_follows_the_judgment_ladder_alone(self):
        # plan-a is at V 2 (no event on the root itself); a reasoned gestalt is J 8, so its width is the J 8 floor 0.3, not 1
        self.tree(extra={"h1": [f'{{"id": "h1-60", "by": "@h1", {BASE}, "kind": "gestalt", "target": {{"node": "plan-a"}}, "estimate": [0.1, 0.3], "reason": "four open conjuncts", "derived": false}}']})
        D = self.derived()
        self.assertEqual(D["nodes"]["plan-a"]["V"]["headline"], 2)
        G = D["roots"]["plan-a"]["gestalt"]
        self.assertEqual((G["J"], Q(G["range"][0]), Q(G["range"][1])), (8, Q(1, 20), Q(7, 20)))
        self.assertEqual(Q(D["judgments"]["node/plan-a/gestalt"]["width"]), Q(3, 10))
        # a leaf range on the same footing (node at V 2, J 8) keeps the vettedness floor: width 1
        self.assertEqual(Q(D["judgments"]["node/alt-2/range"]["width"]), Q(1))

    def test_valuation_nodes_value_the_outside_option_and_the_residual(self):
        D = (self.tree(), self.derived())[1]
        V = D["valuations"]
        self.assertEqual((V["default-trajectory"]["role"], Q(V["default-trajectory"]["value"]["mid"])), ("outside option", Q(0)))
        self.assertEqual((V["undescribed-failure"]["role"], Q(V["undescribed-failure"]["value"]["mid"])), ("undescribed failure", Q(-1, 4)))
        self.assertTrue(V["default-trajectory"]["provisional"] and V["undescribed-failure"]["provisional"])
        self.assertEqual((Q(D["act"]["outside_value"]), D["act"]["outside_placed"], D["act"]["outside_option"]), (Q(0), True, "default-trajectory"))
        rows = D["nodes"]["default-trajectory"]["rows"]
        self.assertEqual({p: Q(r["w"][0]) for p, r in rows.items()}, {p: Q(1, 5) for p in rows})   # equal weights, the residual the remainder
        self.assertTrue(all(D["nodes"]["default-trajectory"]["admitted"].values()))                # the ruling admits the rows it weights
        self.assertEqual(D["judgments"]["row/default-trajectory/dt-utopia/w"]["J"], 8)
        self.assertIn("provisional", D["nodes"]["default-trajectory"]["flags"])
        self.assertIn("from default-trajectory (provisional)", run(self.root, "--why")[1])
        # the residual row of a table is valued at the undescribed-failure node: pic-r's class
        self.assertEqual(D["nodes"]["cases-x"]["rows"]["pic-r"]["class"], "undescribed-failure")
        # no ruling: the outside option has no belief, reads as 0 with the whole scale, and the view says so
        self.tree(drop={"h1-r1"})
        D = self.derived()
        self.assertFalse(D["valuations"]["default-trajectory"]["defined"])
        self.assertEqual((Q(D["act"]["outside_value"]), D["act"]["outside_placed"]), (Q(0), False))
        self.assertIn("no belief", D["nodes"]["default-trajectory"]["flags"])
        self.assertIn("no belief on default-trajectory", run(self.root, "--why")[1])
        # a later weight estimate by the maintainer supersedes the ruling's for that row (latest wins per signer)
        self.tree(extra={"h1": [f'{{"id": "h1-61", "by": "@h1", {BASE}, "kind": "estimate", "target": {{"row": ["default-trajectory", "dt-utopia"], "field": "w"}}, "estimate": [0, 0], "reason": "no utopia by default"}}']})
        D = self.derived()
        self.assertEqual(Q(D["nodes"]["default-trajectory"]["rows"]["dt-utopia"]["w"][0]), Q(0))
        self.assertEqual(Q(D["act"]["outside_value"]), Q(-1, 5))   # weights 1/5, 1/5, 2/5 (the residual's remainder), 1/5, 0: mean −1/5

    def test_programme_is_valued_as_its_best_step_and_its_steps_are_units_in_the_parent(self):
        self.tree(programme=True)
        D = self.derived()
        P = D["roots"]["prog"]
        self.assertEqual((D["nodes"]["prog"]["kind"], P["role"], P["frame"], P["status"]), ("frame", "plan", None, "open"))
        self.assertEqual((P["subframe"]["steps"], P["subframe"]["roots"], P["subframe"]["leading_step"]), (["step-1", "step-2"], ["step-1", "step-2", "sc-1"], "step-1"))
        self.assertEqual((D["roots"]["step-1"]["frame"], D["roots"]["sc-1"]["frame"]), ("prog", "prog"))
        self.assertEqual(Q(P["option_value"]), Q(2, 5))                    # step-1: 0.4·U(utopia) + 0.6·U(outside) = 0.4, above step-2's 0.2
        self.assertEqual(P["value"], D["roots"]["step-1"]["value"])
        self.assertEqual(P["proof_set"], ["step-1"])                        # the cheapest plan step establishes the programme
        self.assertIsNone(P["gestalt"])
        self.assertEqual(D["act"]["cand"], "plan-b")                        # 0.567 beats the programme's 0.4
        u = next(u for u in D["units"] if u["kind"] == "vet" and u["target"] == "step-1")
        self.assertEqual(u["bears_on"], ["prog", "step-1"])                 # the step is a unit in the parent's list
        self.assertGreater(Q(u["D"]), 0)                                    # establishing it would make the programme the act
        self.assertFalse([u for u in D["units"] if u["target"] == "sc-1" and u["kind"] != "gestalt" and "prog" in u["bears_on"]])  # a shared claim is not a step
        view = (self.root / "graph" / "view.md").read_text()
        self.assertIn("## Sub-frame prog (in the top frame):", view)
        self.assertIn("leading step: step-1", view)
        # a step that beats every plan makes the programme the leading candidate, named through its step
        self.tree(programme=True, prog_p=[0.8, 0.9])
        D = self.derived()
        self.assertEqual((D["act"]["cand"], D["act"]["cand_label"]), ("step-1", "prog → step-1"))
        self.assertTrue(D["lines"]["commit"].startswith("research first: the decision term (printed, not applied) favours"), D["lines"]["commit"])
        # only the steps can change the act (a step known to hold beats every plan); plan-a's and plan-b's units cannot
        self.assertTrue(all(Q(u["D"]) == 0 for u in D["units"] if u["target"] not in ("step-1", "step-2") and u["D"] is not None), D["units"])
        self.assertTrue(all(Q(u["D"]) > 0 for u in D["units"] if u["kind"] == "vet" and u["target"] in ("step-1", "step-2")))
        # scoped to the programme, the options are its steps only
        S = self.derived_dry("--scope", "prog")
        self.assertEqual(set(S["act"]["options"]), {"step-1", "step-2"})
        self.assertTrue(all(u["target"] in {"step-1", "step-2", "sc-1", "prog"} for u in S["units"]))

    def test_programme_without_step_values_has_no_option(self):
        self.tree(programme=True, drop={"h1-s1", "h1-s2"})
        D = self.derived()
        self.assertIsNone(D["roots"]["prog"]["option_value"])
        self.assertIsNone(D["roots"]["prog"]["subframe"]["leading_step"])
        self.assertNotIn("prog", D["act"]["options"])
        gest = [u["target"] for u in D["units"] if u["kind"] == "gestalt"]
        self.assertEqual(set(gest), {"step-1", "step-2"})                   # the steps' gestalts are ranked first; the programme carries none
        self.assertEqual(gest, [u["target"] for u in D["units"][:2]])      # (sc-1, a one-leaf shared claim, is no goal of its own)
        S = self.derived_dry("--scope", "prog")
        self.assertTrue(S["lines"]["commit"].startswith("suspended: no plan has a value yet"), S["lines"]["commit"])
        self.assertIn("prog → step-1", S["lines"]["commit"])
        self.assertIn("no plan in scope has a value yet", S["lines"]["regime"])

    def test_programme_with_every_step_conceded_is_worth_its_outside_option(self):
        self.tree(programme=True, tweak=concede_steps, extra={"h2": STEP_TABLE_EVENTS})
        D = self.derived()
        P = D["roots"]["prog"]
        self.assertEqual((D["roots"]["step-1"]["status"], D["roots"]["step-2"]["status"], P["status"], P["diagnosis"]), ("conceded", "conceded", "conceded", "step-1"))
        self.assertEqual(Q(P["option_value"]), Q(D["act"]["outside_value"]))
        self.assertEqual(P["subframe"]["outside_option"], "default-trajectory")
        self.assertNotIn("step-1", D["act"]["options"])
        rev = {u["target"]: u for u in D["units"] if u["kind"] == "revive"}
        self.assertEqual(set(rev), {"step-1", "step-2"})
        self.assertEqual(rev["step-1"]["bears_on"], ["prog", "step-1"])
        self.assertEqual(Q(rev["step-1"]["minutes"]), Q(90))                # revive[M]: no refining picture
        self.assertIn("prog → step-1 conceded by pic-s1", D["lines"]["commit"])
        self.assertIn("revive step-1: ranked unit", D["lines"]["commit"])

    def test_revive_unit_for_a_conceded_table(self):
        self.tree(p_h=["0.2", "0.4"], p_reason=True)                       # cases-x conceded at J 8, so plan-a is conceded
        D = self.derived()
        rev = [u for u in D["units"] if u["kind"] == "revive"]
        self.assertEqual([(u["target"], u["bears_on"]) for u in rev], [("cases-x", ["plan-a"])])
        self.assertEqual(Q(rev[0]["minutes"]), Q(30))                       # revive[S]
        self.assertGreater(rev[0]["bits"], 0)                               # it observes the table's truth, like a vet
        self.assertFalse([u for u in D["units"] if u["target"] == "cases-x" and u["kind"] != "revive"])
        n = D["units"].index(rev[0]) + 1
        self.assertIn(f"not a candidate; revive cases-x: ranked unit {n})", D["lines"]["commit"])
        self.assertIn("revive cases-x (S) — for plan-a", (self.root / "graph" / "tasks.md").read_text())                 # the line format
        # every plan conceded: "until a revival" points at the unit
        self.edit("graph/nodes/plan-b.md", "[shared-leaf, or-y, q-leaf, plan-b.complete]", "[shared-leaf, or-y, q-leaf, cases-x, plan-b.complete]")
        D = self.derived()
        rev = next(u for u in D["units"] if u["kind"] == "revive")
        self.assertEqual(rev["bears_on"], ["plan-a", "plan-b"])
        self.assertTrue(D["lines"]["commit"].endswith(f"the outside option stands until a revival (revive cases-x: ranked unit {D['units'].index(rev) + 1})"), D["lines"]["commit"])
        self.assertIn("ranked as revive cases-x", (self.root / "graph" / "view.md").read_text())
        # a root conceded by its preset's budget alone gets a revive unit on the root
        self.tree(p_h=["0.2", "0.4"], p_reason=False)
        self.edit("graph/frame.yaml", "{id: plan-a, role: plan, preset: worst-case, success_class: utopia}",
                  "{id: plan-a, role: plan, preset: probabilistic, budget: 0.1, success_class: utopia}")
        D = self.derived()
        self.assertTrue(D["roots"]["plan-a"]["diagnosis"].startswith("probabilistic budget"))
        rev = [u for u in D["units"] if u["kind"] == "revive"]
        self.assertEqual([(u["target"], u["bears_on"], Q(u["minutes"])) for u in rev], [("plan-a", ["plan-a"], Q(90))])

    def test_rule2_frame_node_shapes(self):
        self.tree(programme=True)
        self.edit("graph/nodes/prog.md", "children: [step-1, step-2, sc-1]", "children: [step-1, step-2]")
        self.assertIn("exactly its roots", self.refused(2))
        self.tree(programme=True)
        self.edit("graph/frame.yaml", "{id: prog, role: plan, preset: worst-case}", "{id: prog, role: plan, preset: worst-case, success_class: utopia}")
        self.assertIn("no success_class", self.refused(8))
        self.tree(programme=True)
        self.edit("graph/frame.yaml", "{id: prog, role: plan, preset: worst-case}", "{id: prog, role: shared-claim, preset: worst-case}")
        self.assertIn("only as a plan", self.refused(2))
        self.tree(programme=True)
        # a step listed as a top-frame root too: a shared root is allowed (2026-10-22), but a top-frame root has no parent
        self.edit("graph/frame.yaml", "  - {id: prog, role: plan, preset: worst-case}", "  - {id: prog, role: plan, preset: worst-case}\n  - {id: step-1, role: plan, preset: worst-case, success_class: utopia}")
        self.assertIn("named in a children list", self.refused(1))

    def test_rule8_valuation_shapes(self):
        self.tree()
        self.edit("graph/frame.yaml", "outside_option: default-trajectory", "outside_option: utopia")
        self.assertIn("valuation node", self.refused(8))
        self.tree()
        self.edit("graph/frame.yaml", "utility: 1, severity: 5", "utility: null, severity: 5")
        self.assertIn("valuation node, not a class", self.refused(8))
        self.tree()
        self.edit("graph/nodes/default-trajectory.md", "class: utopia", "class: null")
        self.assertIn("placed outcome class", self.refused(8))
        self.tree()
        self.edit("graph/frame.yaml", "valuations: [default-trajectory, undescribed-failure]", "valuations: [default-trajectory]")
        self.assertIn("undescribed_failure", self.refused(8))
        # a rule with rows that weights the residual row, or names a non-row, is refused
        self.tree(extra={"h1": [f'{{"id": "h1-r3", "by": "@h1", {BASE}, "kind": "rule", "target": {{"node": "default-trajectory"}}, "rows": {{"dt-no-interesting-life": {{"w": [0.2, 0.2]}}}}}}']})
        self.assertIn("residual row", self.refused(10))
        self.tree(extra={"h1": [f'{{"id": "h1-r3", "by": "@h1", {BASE}, "kind": "rule", "target": {{"node": "default-trajectory"}}, "rows": {{"ghost": {{"w": [0.2, 0.2]}}}}}}']})
        self.refused(5)

    def test_audit_event_is_counted_as_calibration_data(self):
        self.tree(extra={"h2": [f'{{"id": "h2-52", "by": "@h2", {BASE}, "kind": "audit", "target": {{"event": "h1-1"}}, "verdict": "agree"}}',
                                f'{{"id": "h2-53", "by": "@h2", {BASE}, "kind": "audit", "target": {{"event": "h2-7"}}, "verdict": "disagree"}}']})
        D = self.derived()
        self.assertEqual(D["audits"]["@h2"], {"agree": 1, "disagree": 1, "self": 1, "cross": 1})
        self.assertEqual(D["nodes"]["shared-leaf"]["V"]["headline"], 8)   # an audit moves no level

    def test_pr_and_expected_utility_exact(self):
        D = (self.tree(), self.derived())[1]
        pr_a = Q(7, 10) * Q(81, 100) * Q(19, 20) * Q(19, 20)
        self.assertEqual(Q(D["roots"]["plan-a"]["Pr"]["mid"]), pr_a)
        # pic-h's failure mass goes to high-conflict (−1/2); the residual row's to the undescribed-failure node (−1/4, ruling 32)
        self.assertEqual(Q(D["roots"]["plan-a"]["value"]["mid"]), pr_a + Q(3, 10) * Q(4, 10) * Q(-1, 2) + Q(7, 10) * Q(1, 10) * Q(-1, 4))
        pr_b = Q(7, 10) * (1 - Q(1, 10) * Q(6, 10)) * Q(9, 10)          # or-y: 1 − (1 − 0.9)(1 − 0.4), a disjunction
        self.assertEqual(Q(D["roots"]["plan-b"]["Pr"]["mid"]), pr_b)
        # C2: the plan whose only failure story is untagged sits above the outside option by Pr · (U(utopia) − U(outside))
        self.assertEqual(Q(D["roots"]["plan-b"]["value"]["mid"]) - Q(D["act"]["outside_value"]), pr_b * (Q(1) - Q(0)))
        self.assertEqual(D["act"]["cand"], "plan-b")
        self.assertTrue(D["act"]["outside_placed"])                   # the default trajectory is the ruled valuation node's mean, 0
        self.assertEqual(D["roots"]["plan-a"]["failure_classes_below_outside"], ["high-conflict", "undescribed-failure"])

    def test_c1_only_the_tagged_leaf_moves_the_act(self):
        D = (self.tree(), self.derived())[1]
        for u in D["units"]:
            if u["target"] == "cases-x" and u["kind"] == "vet":
                self.assertGreater(Q(u["D"]), 0)
            elif u["target"] != "cases-x":
                self.assertEqual(Q(u["D"]), 0, u)
        self.assertTrue(D["lines"]["commit"].startswith("research first: the decision term (printed, not applied) favours vet cases-x"))

    def test_map_term_is_a_sum_over_goals(self):
        D = (self.tree(), self.derived())[1]
        goals = D["ranking"]["goals"]
        self.assertEqual(goals, ["plan-a", "plan-b"])                       # the non-frame roots of every frame
        h2 = lambda p: 0.0 if p in (0, 1) else -(p * math.log2(p) + (1 - p) * math.log2(1 - p))
        G = {x["id"]: x for x in D["goals"]}
        self.assertAlmostEqual(D["ranking"]["weighted_bits"], sum(G[r]["weight"] * h2(G[r]["P_forecast"]) for r in goals))
        # a unit's weighted bits are the sum of its per-goal weighted bits; its rate divides them by its hours
        for u in D["units"]:
            if u["bits"] is not None:
                self.assertAlmostEqual(u["bits"], sum(f["bits"] for f in u["for"]))
                self.assertAlmostEqual(u["wbits"], sum(f["wbits"] for f in u["for"]))
                self.assertTrue(u["bits"] >= 0)
        self.assertEqual(D["inference"]["largest"], [])                      # no formula here shares a variable inside itself

    def test_conceded_plan_is_not_a_candidate(self):
        self.tree(p_h=["0.2", "0.4"], p_reason=True)                  # cases-x conceded at J 8, so plan-a is conceded
        D = self.derived()
        self.assertEqual(D["roots"]["plan-a"]["status"], "conceded")
        self.assertEqual(D["act"]["cand"], "plan-b")
        self.assertEqual(D["act"]["conceded_plans"], {"plan-a": "cases-x"})   # the root's diagnosis is its conceding child
        self.assertIn("plan-a conceded by cases-x: not a candidate", D["lines"]["commit"])
        self.assertTrue(D["lines"]["commit"].startswith("no plan vetted enough to commit to; leading candidate plan-b"))
        # every plan conceded: the commit line says so and the decision term is suspended
        self.edit("graph/nodes/plan-b.md", "[shared-leaf, or-y, q-leaf, plan-b.complete]", "[shared-leaf, or-y, q-leaf, cases-x, plan-b.complete]")
        D = self.derived()
        self.assertTrue(D["lines"]["commit"].startswith("no non-conceded plan to commit to"))
        self.assertIn("every plan in scope is conceded", D["lines"]["regime"])
        self.assertTrue(all(u["D"] is None for u in D["units"]))

    def test_gestalt_ranked_only_without_a_derived_probability(self):
        D = (self.tree(), self.derived())[1]
        self.assertFalse([u for u in D["units"] if u["kind"] == "gestalt"])             # both plans have derived probabilities
        notes = {u["target"]: u["note"] for u in D["units_unranked"] if u["kind"] == "gestalt"}
        self.assertEqual(set(notes), {"plan-a", "plan-b"})
        self.assertTrue(all(n.startswith("no gestalt yet") for n in notes.values()))
        self.assertIn("no gestalt yet", (self.root / "graph" / "tasks.md").read_text())
        self.tree(drop={"h2-9"})                                        # q-leaf loses its range: plan-b's probability is undefined
        D = self.derived()
        self.assertFalse(D["roots"]["plan-b"]["Pr_defined"])
        self.assertEqual((D["units"][0]["kind"], D["units"][0]["target"]), ("gestalt", "plan-b"))
        self.assertNotIn("plan-b", {u["target"] for u in D["units_unranked"] if u["kind"] == "gestalt"})

    def test_margin_only_on_open_worst_case_roots(self):
        self.tree()
        self.edit("graph/frame.yaml", "{id: plan-b, role: plan, preset: worst-case, success_class: utopia}",
                  "{id: plan-b, role: plan, preset: probabilistic, budget: 0.9, success_class: utopia}")
        D = self.derived()
        self.assertIsNone(D["roots"]["plan-b"]["margin"])
        self.assertIsNotNone(D["roots"]["plan-a"]["margin"])
        self.assertIsNotNone(D["roots"]["plan-b"]["budget_loss"])
        view = (self.root / "graph" / "view.md").read_text()
        sec_a = view.split("### plan-a")[1].split("###")[0]
        sec_b = view.split("### plan-b")[1].split("###")[0]
        self.assertIn("safety margin", sec_a)
        self.assertNotIn("safety margin", sec_b)
        self.assertNotIn("None", sec_b)

    def test_digest_has_one_shape_without_a_previous_derivation(self):
        # ruling G1 (2026-10-23): a fresh tree has nothing to compare with; the keys are all there, the lists empty, the counts zero
        self.tree()
        code, out, err = run(self.root)
        self.assertEqual(code, 0, err)
        D = json.loads((self.root / "graph" / "derived.json").read_text())
        self.assertEqual(tuple(sorted(D["digest"])), tuple(sorted(g.DIGEST_KEYS)))
        self.assertEqual(D["digest"], {"compared_with": None, "statuses_flipped": [], "root_statuses_flipped": [], "levels_moved": [],
                                       "events_new": 0, "revisions": [], "wants_new": [], "proposals_awaiting": []})
        self.assertTrue(err.startswith("DIGEST no previous derivation"), err)
        D = self.derived()                                             # the second run compares with the first, by the same keys
        self.assertEqual(tuple(sorted(D["digest"])), tuple(sorted(g.DIGEST_KEYS)))
        self.assertTrue(D["digest"]["compared_with"].startswith("graph/derived.json on disk"))

    def test_digest_reports_node_and_root_flips(self):
        self.tree(p_h=["0.2", "0.4"], p_reason=False)
        self.derived()
        self.tree(p_h=["0.2", "0.4"], p_reason=True)                  # the same tree with a reason on the conditional
        D = self.derived()
        self.assertIn("cases-x: open → conceded", D["digest"]["statuses_flipped"])
        self.assertIn("root plan-a: open → conceded (cases-x)", D["digest"]["root_statuses_flipped"])
        self.assertEqual(D["digest"]["events_new"], 0)
        # a flip through a preset budget alone (no node changes status)
        self.tree(p_h=["0.2", "0.4"], p_reason=False)
        self.edit("graph/frame.yaml", "{id: plan-a, role: plan, preset: worst-case, success_class: utopia}",
                  "{id: plan-a, role: plan, preset: probabilistic, budget: 0.5, success_class: utopia}")
        self.derived()
        self.edit("graph/frame.yaml", "budget: 0.5", "budget: 0.1")
        D = self.derived()
        self.assertEqual(D["digest"]["statuses_flipped"], [])
        self.assertTrue(any(f.startswith("root plan-a: open → conceded (probabilistic budget") for f in D["digest"]["root_statuses_flipped"]), D["digest"])

    def test_scope_removes_the_other_roots_bits(self):
        self.tree()
        full = self.derived()
        scoped = self.derived_dry("--scope", "plan-a")
        sup = {"plan-a", "shared-leaf", "cases-x", "cases-x.partition", "pic-h", "pic-r", "choose-c", "alt-1", "alt-2", "plan-a.complete"}
        self.assertTrue(all(u["target"] in sup for u in scoped["units"]))
        self.assertEqual(scoped["lines"]["scoped"], "scoped: bits about the goals under plan-a only")
        self.assertEqual(scoped["ranking"]["goals"], ["plan-a"])
        self.assertNotEqual(full["ranking"]["weighted_bits"], scoped["ranking"]["weighted_bits"])

    def test_streams(self):
        self.tree()
        code, out, err = run(self.root)
        self.assertEqual((code, out), (0, ""))                         # a plain run prints nothing on stdout
        lines = err.strip().splitlines()                               # the DIGEST line names what it compared with (F3, 2026-10-23)
        self.assertTrue(lines[0].startswith("DIGEST ") and lines[-1].startswith("OK ") and len(lines) == 2, err)
        code, out, err = run(self.root, "--dry-run")
        self.assertEqual(code, 0, err)
        self.assertEqual(json.loads(out)["checker_version"], g.CHECKER_VERSION)   # stdout is the JSON alone
        self.assertIn("nothing written (--dry-run)", err)
        (self.root / "graph" / "tasks.md").unlink()
        code, out, err = run(self.root, "--print")
        self.assertEqual(code, 0, err)
        self.assertIn("## Ranked units", out)                          # the task list without writing anything
        self.assertFalse((self.root / "graph" / "tasks.md").exists())
        self.assertIn("nothing written (--print)", err)

    def test_generated_files_are_flag_independent(self):
        self.tree()
        self.derived()
        self.derived()                                                 # a second plain run: the digest now has a like-for-like previous
        snap = {n: (self.root / "graph" / n).read_text() for n in g.GENERATED}
        for flags in (("--why",), ("--as", "@h1"), ("--as", "@h2", "--why"), ("--scope", "plan-a"), ("--lambda", "1"), ("--window-dp", "--frontier", "2")):
            code, out, err = run(self.root, *flags)
            self.assertEqual(code, 0, err)
            self.assertTrue(out, flags)                                # the personal render is on stdout
            self.assertIn("not a committed file", out)
            for n in g.GENERATED:
                self.assertEqual((self.root / "graph" / n).read_text(), snap[n], (flags, n))
        self.assertNotIn("## Why", snap["tasks.md"])                   # the committed list is the pooled default
        out = run(self.root, "--why")[1]
        self.assertIn("## Why", out)
        out = run(self.root, "--as", "@h1")[1]
        self.assertIn("comonotone companion", out)                     # h1's alternative_calculations
        out = run(self.root, "--as", "@h2")[1]
        self.assertNotIn("## Why", out)                                # h2 hides numbers
        out = run(self.root, "--lambda", "1")[1]
        self.assertIn("λ", out)
        code, out, err = run(self.root, "--why", "--out", str(self.root / "mine.md"))
        self.assertEqual((code, out), (0, ""))
        self.assertIn("## Why", (self.root / "mine.md").read_text())
        self.assertIn("mine.md", err)

    def test_window_dp_frontier_lambda_flags(self):
        self.tree()
        D = self.derived_dry("--window-dp", "--frontier", "2")
        short = [u for u in D["units"] if "D_window" in u]
        self.assertTrue(short)
        self.assertEqual(D["ranking_window"]["frontier"], 2)
        # the roots whose closure holds a shortlisted target
        self.assertEqual(D["ranking_window"]["component"],
                         sorted({r for u in D["units"] if u["target"] in D["ranking_window"]["shortlist"] for r in u["bears_on"]}))
        D = self.derived_dry("--lambda", "1")
        self.assertEqual(D["ranking"]["ordered_by"], "score")

    def test_proposal_delta_written_then_checked(self):
        self.tree()
        pdir = self.root / "graph" / "proposals"
        (pdir / "P-1").mkdir()
        (pdir / "P-1" / "new-leaf.md").write_text("---\nid: new-leaf\nkind: leaf\nleaf_kind: step\nauthor: \"@ai\"\nsize: S\nsize_reason: illustrative\nversion: 1\n---\n## Statement\nA further lemma holds.\n## Source\nillustrative\n")
        (pdir / "P-1.md").write_text("---\nid: P-1\nkind: edge\nauthor: \"@ai\"\nstatus: proposed\ntargets: [plan-b]\nops:\n  - {op: new-node, file: P-1/new-leaf.md}\n  - {op: add-child, parent: plan-b, child: new-leaf}\n---\n## Change\nAdds a conjunct to plan B.\n## Delta\n")
        D = self.derived()
        text = (pdir / "P-1.md").read_text()
        self.assertIn("- plan-b: cost", text)
        self.assertIn(("approve", "P-1"), [(u["kind"], u["target"]) for u in D["units_unranked"]])
        self.assertEqual(run(self.root)[0], 0)
        (pdir / "P-1.md").write_text(text.replace("- plan-b: cost", "- plan-b: cost 0 → 0; edited"))
        self.refused(7)


import contextlib


@contextlib.contextmanager
def reading(mode):
    """Pin the `or` reading for one test: "cheapest" is the landed one the oracle regression compares with."""
    saved = g.OR_READING
    g.OR_READING = mode
    try:
        yield
    finally:
        g.OR_READING = saved


def add_leaf_b(nodes):
    """Tweak: plan-b gains a conjunct b-leaf of its own (no other root reaches it)."""
    nodes["plan-b"] = ("and", "M", {"children": "[shared-leaf, or-y, q-leaf, b-leaf, plan-b.complete]"}, nodes["plan-b"][3])
    nodes["b-leaf"] = ("leaf", "S", {"leaf_kind": "assumption"}, "The second plan's own premise holds.")


B_LEAF_EVENT = f'{{"id": "h1-70", "by": "@h1", {BASE}, "kind": "estimate", "target": {{"node": "b-leaf"}}, "estimate": [0.4, 0.6], "reason": "even odds"}}'


def two_tags(nodes):
    """Tweak: alt-1 becomes a table whose row fails to disutility-max, beside cases-x's high-conflict row."""
    make_table(nodes)
    nodes["alt-1"] = ("cases", "S", {"children": "[alt-1.partition, pic-z, pic-zr]",
                                     "rows": "\n  - {picture: pic-z, class: disutility-max, observable: never}\n  - {picture: pic-zr, class: undescribed-failure, observable: never, residual: true}"},
                      "The asymptotic-introspection expert model carries the collapse.")
    nodes["choose-c"] = ("choose", "S", {"children": "[alt-1, alt-2]", "decided_at": "commit", "committed": "alt-1"}, nodes["choose-c"][3])


TWO_TAG_EVENTS = [f'{{"id": "h2-8{i}", "by": "@h2", {BASE}, "kind": "estimate", "target": {tg}, "estimate": {rng}, "reason": "illustrative"}}'
                  for i, (tg, rng) in enumerate(((json.dumps({"row": ["alt-1", "pic-z"], "field": "w"}), "[0.3, 0.5]"),
                                                 (json.dumps({"row": ["alt-1", "pic-z"], "field": "p"}), "[0.5, 0.7]"),
                                                 (json.dumps({"row": ["alt-1", "pic-zr"], "field": "p"}), "[0.9, 1]"),
                                                 (json.dumps({"node": "alt-1.partition"}), "[1, 1]")))]


class Inference(Base):
    """the exact recursion with cutset conditioning, against the oracle (the 0.3 enumerator)."""

    ORACLE_MAX_VARS = 12     # the oracle enumerates 2^|vs| worlds per root; the shipped graph's formal results reach 25 leaves (2026-10-22)

    def check_roots(self, C, D, modes=("mid", "lo", "hi"), cap=None):
        skipped = 0
        for rid in C.roots:
            if C.t.nodes[rid].get("kind") == "frame":
                continue
            vs = C.psets[rid] if C.E.or_mode == "cheapest" else {x for x in C.E.closure((C.E.key_of(rid),)) if C.t.nodes.get(x, {}).get("kind") in ("leaf", "cases")}
            if cap is not None and len(vs) > cap:
                skipped += 1          # the recursion is checked against the oracle on every smaller root and on the synthetic trees
                continue
            O = enumerate_oracle(C, rid, vs, modes=modes)
            for mode in modes:
                self.assertEqual(D["roots"][rid]["Pr"][mode], O["Pr"][mode], (rid, mode))
                if O["value"]:
                    self.assertEqual(D["roots"][rid]["value"][mode], O["value"][mode], (rid, mode))
        return skipped

    def test_oracle_regression_landed_reading(self):
        # (a) every root's Pr and value at the three modes equal the oracle's exactly, with the landed cheapest-child reading
        with reading("cheapest"):
            for i, kw in enumerate(({}, {"programme": True}, {"tweak": two_tags, "extra": {"h2": TWO_TAG_EVENTS}})):
                self.root = pathlib.Path(self.tmp) / f"t{i}"
                self.tree(**kw)
                self.check_roots(*context(self.root))
            if (ROOT / "graph" / "frame.yaml").is_file():
                skipped = self.check_roots(*context(ROOT), cap=self.ORACLE_MAX_VARS)
                print(f"\n  oracle regression on the shipped graph: {skipped} root(s) above {self.ORACLE_MAX_VARS} variables left to the recursion")

    def test_a_leaf_under_two_conjuncts_counts_once(self):
        # (b) shared-leaf is a conjunct of plan-b and a child of its or: the recursion conditions on it once
        def share(nodes):
            nodes["or-y"] = ("or", "S", {"children": "[cheap-leaf, dear-leaf, shared-leaf]"}, nodes["or-y"][3])
        for mode in ("cheapest", "disjunction"):
            with reading(mode):
                self.tree(tweak=share)
                C, D = context(self.root)
                self.check_roots(C, D)
                self.assertEqual(D["roots"]["plan-b"]["Pr"]["mid"], Q(7, 10) * Q(9, 10) * Q(1) if mode == "cheapest" else D["roots"]["plan-b"]["Pr"]["mid"])
                self.assertEqual(D["inference"]["largest"][0]["cutset"], ["shared-leaf"])

    def test_failure_classes_take_the_worse(self):
        # (c) two tagged tables of different classes, both failing in some world: the value takes the worse class
        for mode in ("cheapest", "disjunction"):
            with reading(mode):
                self.tree(tweak=two_tags, extra={"h2": TWO_TAG_EVENTS})
                C, D = context(self.root)
                self.check_roots(C, D)
                self.assertIn("alt-1", D["roots"]["plan-a"]["proof_set"])                  # both tables are in the plan

    def test_D_on_one_plan_equals_the_landed_D(self):
        # (d) one plan: every unit's D equals the oracle's; a unit on a node in no plan's closure has D = 0
        with reading("cheapest"):
            self.tree(tweak=add_leaf_b, extra={"h1": [B_LEAF_EVENT]})
            self.edit("graph/frame.yaml", "{id: plan-b, role: plan, preset: worst-case, success_class: utopia}", "{id: plan-b, role: shared-claim, preset: worst-case}")
            C, D = context(self.root)
            seen = set()
            for u in D["units"]:
                if u["bits"] is None:
                    continue
                if "plan-a" in u["bears_on"]:
                    _, Dv = oracle_bits_and_D(C, D, "plan-a", u["target"], unit_error(u))
                    self.assertEqual(u["D"], Dv, u)
                    seen.add("a")
                else:
                    self.assertEqual(u["D"], 0, u)
                    seen.add("b")
            self.assertEqual(seen, {"a", "b"})
            self.assertIn("b-leaf", {u["target"] for u in D["units"]})

    def test_per_goal_bits_equal_the_landed_bits_without_sharing(self):
        # (g) roots that share no variables: the landed joint entropy factorises, so per-goal bits equal it
        with reading("cheapest"):
            self.tree()
            self.edit("graph/nodes/plan-b.md", "[shared-leaf, or-y, q-leaf, plan-b.complete]", "[or-y, q-leaf, plan-b.complete]")
            self.edit("graph/policy.yaml", "verdict_c: 0.2", "verdict_c: 0")      # the verdict model's forecast without suspicion is the displayed mid
            C, D = context(self.root)
            for u in D["units"]:
                if u["bits"] is None:
                    continue
                (r,) = [r for r in u["bears_on"] if r in ("plan-a", "plan-b")]
                b, _ = oracle_bits_and_D(C, D, r, u["target"], unit_error(u))
                self.assertAlmostEqual(u["bits"], b, places=12)

    def test_or_reads_as_a_disjunction_for_belief(self):
        # (e) an `or` over two independent leaves at 1/2 shows 3/4 and keeps the cheaper child as its proof set;
        # `tag: choose-one` shows the better child
        def halves(nodes):
            nodes["plan-b"] = ("and", "M", {"children": "[or-y, q-leaf, plan-b.complete]"}, nodes["plan-b"][3])
        ev = [f'{{"id": "h1-7{i}", "by": "@h1", {BASE}, "kind": "estimate", "target": {{"node": "{x}"}}, "estimate": {r}, "reason": "even"}}'
              for i, (x, r) in enumerate((("cheap-leaf", "[0.5, 0.5]"), ("dear-leaf", "[0.5, 0.5]")))]
        self.tree(tweak=halves, drop={"h1-3", "h1-4", "h2-15"}, extra={"h1": ev})
        C, D = context(self.root)
        self.assertEqual(D["roots"]["plan-b"]["Pr"]["mid"], Q(3, 4) * Q(9, 10))
        self.assertEqual(D["roots"]["plan-b"]["proof_set"], ["cheap-leaf", "plan-b.complete", "q-leaf"])
        self.check_roots(C, D)
        with reading("cheapest"):
            C, D = context(self.root)
            self.assertEqual(D["roots"]["plan-b"]["Pr"]["mid"], Q(1, 2) * Q(9, 10))   # the landed reading counts the cheapest child only
        self.edit("graph/nodes/or-y.md", "kind: or\n", "kind: or\ntag: choose-one\n")
        self.edit("graph/events/h1.jsonl", '"target": {"node": "dear-leaf"}, "estimate": [0.5, 0.5]', '"target": {"node": "dear-leaf"}, "estimate": [0.7, 0.7]')
        C, D = context(self.root)
        self.assertEqual(D["roots"]["plan-b"]["Pr"]["mid"], Q(7, 10) * Q(9, 10))     # the better child, chosen by the plan's value
        self.assertEqual(D["roots"]["plan-b"]["choice"], {"or-y": "dear-leaf"})
        self.assertEqual(D["roots"]["plan-b"]["proof_set"], ["cheap-leaf", "plan-b.complete", "q-leaf"])   # establishment still takes the cheapest

    def test_D_from_joint_masses_equals_forced_passes(self):
        # (i) a shared conjunct (shared-leaf, now open at V 6) under two plans: D read from the plans' joint masses
        # equals D computed with the target forced, one pass per outcome per plan
        for mode in ("cheapest", "disjunction"):
            with reading(mode):
                self.tree(drop={"h1-2"})
                C, D = context(self.root)
                E = C.E
                plans = [r for r in D["act"]["options"]]
                units = [u for u in D["units"] if u["D"] is not None]
                self.assertTrue(any(u["target"] == "shared-leaf" for u in units))
                for u in units:
                    x, e = u["target"], unit_error(u)
                    Dv, V0 = Q(0), D["act"]["V_act"]
                    px = E.prob((E.key_of(x),), {}, "mid")
                    for o in (True, False):
                        po = (1 - e) * px + e * (1 - px) if o else e * px + (1 - e) * (1 - px)
                        best = D["act"]["outside_value"]
                        for r in plans:
                            base = g.root_base(C, r, C.psets[r])
                            if x in E.dag((E.key_of(r),)).vars and D["roots"][r]["value_defined"]:
                                v1 = E.plan_value(r, {**base, x: (True, None)})[0]
                                v0 = E.plan_value(r, {**base, x: (False, None)})[0]
                                ev = ((1 - e) * v1 + e * v0) if o else (e * v1 + (1 - e) * v0)
                                v = ev / po
                            else:
                                v = D["roots"][r]["act_value"]
                            best = max(best, v)
                        Dv += po * best
                    self.assertEqual(u["D"], Dv - V0, u)


def given_tree(extra_nodes, plan_b_extra=()):
    """Tweak factory: plan-b gains conjuncts `plan_b_extra`; `extra_nodes` maps id -> (kind, size, fields, statement)."""
    def tweak(nodes):
        kids = ["shared-leaf", "or-y", "q-leaf", *plan_b_extra, "plan-b.complete"]
        nodes["plan-b"] = ("and", "M", {"children": "[" + ", ".join(kids) + "]"}, nodes["plan-b"][3])
        nodes.update(extra_nodes)
    return tweak


def ev(i, target, rng, by="h1", **more):
    tail = "".join(f', "{k}": {json.dumps(v)}' for k, v in more.items())
    return f'{{"id": "{by}-9{i:02d}", "by": "@{by}", {BASE}, "kind": "estimate", "target": {json.dumps(target)}, "estimate": {rng}, "reason": "illustrative"{tail}}}'


Y_LEAF = {"y-leaf": ("leaf", "S", {"leaf_kind": "assumption"}, "The evidence premise Y holds.")}


class Conditional(Base):
    """`given` edges (conditional tables)."""

    def ctx(self):
        return context(self.root)

    def test_affine_conditional_exact(self):
        # Y at 2/5; X ⇢ Y with P(X | Y) = 9/10, P(X | not Y) = 1/5: P(X) = 12/25 exactly
        nodes = dict(Y_LEAF, **{"x-leaf": ("leaf", "S", {"leaf_kind": "assumption", "given": "y-leaf"}, "The claim X holds.")})
        self.tree(tweak=given_tree(nodes, ["x-leaf"]), extra={"h1": [ev(1, {"node": "y-leaf"}, "[0.4, 0.4]"),
                                                                   ev(2, {"node": "x-leaf", "field": "if-holds"}, "[0.9, 0.9]"),
                                                                   ev(3, {"node": "x-leaf", "field": "if-fails"}, "[0.2, 0.2]")]})
        C, D = self.ctx()
        self.assertEqual(C.E.prob((("v", "x-leaf"),)), Q(12, 25))
        Inference.check_roots(self, C, D)
        self.assertIn("given y-leaf", D["nodes"]["x-leaf"]["flags"])
        self.assertNotIn("given: conditionals not judged", D["nodes"]["x-leaf"]["flags"])
        self.assertEqual(D["nodes"]["y-leaf"]["informs"], ["plan-b"])                  # informs through the given edge
        self.assertEqual(D["nodes"]["y-leaf"]["load"], [])                             # no status crosses the edge
        self.assertNotIn("y-leaf", D["roots"]["plan-b"]["proof_set"])
        self.assertIn("y-leaf", {u["target"] for u in D["units"]})                     # the parent is a unit target (it informs)

    def test_two_leaves_given_one_parent_are_dependent(self):
        nodes = dict(Y_LEAF, **{x: ("leaf", "S", {"leaf_kind": "assumption", "given": "y-leaf"}, f"The claim {x} holds.") for x in ("x1", "x2")})
        evs = [ev(1, {"node": "y-leaf"}, "[0.4, 0.4]"), ev(2, {"node": "x1", "field": "if-holds"}, "[0.9, 0.9]"),
               ev(3, {"node": "x1", "field": "if-fails"}, "[0.2, 0.2]"), ev(4, {"node": "x2", "field": "if-holds"}, "[0.8, 0.8]"),
               ev(5, {"node": "x2", "field": "if-fails"}, "[0.1, 0.1]")]
        self.tree(tweak=given_tree(nodes, ["x1", "x2"]), extra={"h1": evs})
        C, D = self.ctx()
        joint = Q(2, 5) * Q(9, 10) * Q(8, 10) + Q(3, 5) * Q(2, 10) * Q(1, 10)
        self.assertEqual(C.E.prob((("v", "x1"), ("v", "x2"))), joint)
        self.assertNotEqual(joint, C.E.prob((("v", "x1"),)) * C.E.prob((("v", "x2"),)))
        Inference.check_roots(self, C, D)
        self.assertEqual(D["inference"]["largest"][0]["cutset"], ["y-leaf"])           # the shared parent collapses to its truth

    def test_parent_conceded_leaves_the_child_open_and_proof_sets_unchanged(self):
        nodes = {"x-leaf": ("leaf", "S", {"leaf_kind": "assumption", "given": "cases-x"}, "The claim X holds.")}
        evs = [ev(2, {"node": "x-leaf", "field": "if-holds"}, "[0.9, 0.9]"), ev(3, {"node": "x-leaf", "field": "if-fails"}, "[0.2, 0.2]")]
        self.tree(tweak=given_tree(nodes, ["x-leaf"]), p_h=["0.2", "0.4"], p_reason=True, extra={"h1": evs})
        C, D = self.ctx()
        self.assertEqual(D["nodes"]["cases-x"]["status"], "conceded")
        self.assertEqual(D["nodes"]["x-leaf"]["status"], "open")
        self.assertIn("given: cases-x conceded", D["nodes"]["x-leaf"]["flags"])
        self.assertEqual(D["roots"]["plan-b"]["status"], "open")
        with_edge = (D["roots"]["plan-b"]["proof_set"], D["roots"]["plan-b"]["cost"], D["nodes"]["x-leaf"]["load"], D["nodes"]["cases-x"]["load"])
        self.root = pathlib.Path(self.tmp) / "no-edge"
        nodes = {"x-leaf": ("leaf", "S", {"leaf_kind": "assumption"}, "The claim X holds.")}
        self.tree(tweak=given_tree(nodes, ["x-leaf"]), p_h=["0.2", "0.4"], p_reason=True, extra={"h1": [ev(2, {"node": "x-leaf"}, "[0.9, 0.9]")]})
        C, D = self.ctx()
        self.assertEqual(with_edge, (D["roots"]["plan-b"]["proof_set"], D["roots"]["plan-b"]["cost"], D["nodes"]["x-leaf"]["load"], D["nodes"]["cases-x"]["load"]))

    def test_plain_range_is_the_fallback(self):
        # adding an edge to a judged node changes no number until the conditionals are judged
        nodes = dict(Y_LEAF, **{"x-leaf": ("leaf", "S", {"leaf_kind": "assumption"}, "The claim X holds.")})
        evs = [ev(1, {"node": "y-leaf"}, "[0.4, 0.4]"), ev(2, {"node": "x-leaf"}, "[0.6, 0.6]")]
        self.tree(tweak=given_tree(nodes, ["x-leaf", "y-leaf"]), extra={"h1": evs})
        before = self.ctx()[1]["roots"]
        self.edit("graph/nodes/plan-b.md", "x-leaf, y-leaf, ", "x-leaf, ")
        self.edit("graph/nodes/x-leaf.md", "leaf_kind: assumption\n", "leaf_kind: assumption\ngiven: y-leaf\n")
        C, D = self.ctx()
        self.assertEqual(C.E.prob((("v", "x-leaf"),)), Q(3, 5))
        self.assertIn("given: conditionals not judged", D["nodes"]["x-leaf"]["flags"])
        self.assertEqual(D["roots"]["plan-a"]["Pr"], before["plan-a"]["Pr"])
        self.assertEqual(D["roots"]["plan-b"]["Pr"]["mid"], before["plan-b"]["Pr"]["mid"] / Q(2, 5))   # y-leaf left the conjunction

    def test_given_row_bar_test_both_ways(self):
        # pic-h's row is given shared-leaf (established, V 8): the bar test reads P(row | shared-leaf holds)
        def tw(nodes):
            nodes["cases-x"] = ("cases", "S", {"children": "[cases-x.partition, pic-h, pic-r]",
                                               "rows": "\n  - {picture: pic-h, class: high-conflict, observable: never, given: shared-leaf}\n  - {picture: pic-r, class: undescribed-failure, observable: never, residual: true}"},
                                nodes["cases-x"][3])
        for a, b, want in (("[0.2, 0.4]", "[0.8, 0.9]", "conceded"), ("[0.6, 0.8]", "[0.1, 0.2]", "open")):
            self.tree(tweak=tw, drop={"h2-12"}, extra={"h2": [ev(1, {"row": ["cases-x", "pic-h"], "field": "p-if-holds"}, a, by="h2"),
                                                              ev(2, {"row": ["cases-x", "pic-h"], "field": "p-if-fails"}, b, by="h2")]})
            C, D = self.ctx()
            self.assertEqual(D["nodes"]["cases-x"]["status"], want, (a, b))
            self.assertIn("given shared-leaf", D["nodes"]["cases-x"]["flags"])
            self.assertIn("given: shared-leaf established", D["nodes"]["cases-x"]["flags"])
            Inference.check_roots(self, C, D)

    def test_attached_only_as_a_given_parent(self):
        nodes = dict(Y_LEAF, **{"x-leaf": ("leaf", "S", {"leaf_kind": "assumption", "given": "y-leaf"}, "The claim X holds.")})
        self.tree(tweak=given_tree(nodes, ["x-leaf"]), extra={"h1": [ev(1, {"node": "y-leaf"}, "[0.4, 0.4]")]})
        self.derived()
        self.edit("graph/nodes/x-leaf.md", "given: y-leaf\n", "")
        err = self.refused(1)
        self.assertIn("attached to nothing", err)
        self.assertIn("y-leaf", err)

    def test_class_given_names_the_failure_class_where_the_parent_fails(self):
        nodes = dict(Y_LEAF, **{"x-leaf": ("leaf", "S", {"leaf_kind": "assumption", "given": "y-leaf", "class_given": "{fails: high-conflict}"}, "The claim X holds.")})
        evs = [ev(1, {"node": "y-leaf"}, "[0.4, 0.4]"), ev(2, {"node": "x-leaf", "field": "if-holds"}, "[0.9, 0.9]"),
               ev(3, {"node": "x-leaf", "field": "if-fails"}, "[0.2, 0.2]")]
        self.tree(tweak=given_tree(nodes, ["x-leaf"]), extra={"h1": evs})
        C, D = self.ctx()
        Inference.check_roots(self, C, D)                         # value equal to the oracle extended to given edges
        tagged = Q(D["roots"]["plan-b"]["value"]["mid"])
        self.edit("graph/nodes/x-leaf.md", "class_given: {fails: high-conflict}\n", "")
        self.assertLess(tagged, Q(self.derived()["roots"]["plan-b"]["value"]["mid"]))
        self.assertIn("high-conflict", D["roots"]["plan-b"]["failure_classes_below_outside"])

    def test_negative_edge_flags_the_root(self):
        nodes = dict(Y_LEAF, **{"x-leaf": ("leaf", "S", {"leaf_kind": "assumption", "given": "y-leaf"}, "The claim X holds.")})
        evs = [ev(1, {"node": "y-leaf"}, "[0.4, 0.4]"), ev(2, {"node": "x-leaf", "field": "if-holds"}, "[0.2, 0.2]"),
               ev(3, {"node": "x-leaf", "field": "if-fails"}, "[0.9, 0.9]")]
        self.tree(tweak=given_tree(nodes, ["x-leaf"]), extra={"h1": evs})
        D = self.derived()
        self.assertIn("interval not a bound (negative evidential edge)", D["nodes"]["plan-b"]["flags"])
        self.assertNotIn("interval not a bound (negative evidential edge)", D["nodes"]["plan-a"]["flags"])

    def test_scope_adds_the_closure(self):
        nodes = dict(Y_LEAF, **{"x-leaf": ("leaf", "S", {"leaf_kind": "assumption", "given": "y-leaf"}, "The claim X holds.")})
        self.tree(tweak=given_tree(nodes, ["x-leaf"]), extra={"h1": [ev(1, {"node": "y-leaf"}, "[0.4, 0.4]")]})
        S = self.derived_dry("--scope", "plan-b")
        self.assertIn("y-leaf", {u["target"] for u in S["units"]})


RESULT = {
    "res": ("and", "M", {"children": "[res.record, res.bridge, res.h, res.complete]"}, "The toy result holds in its setting."),
    "res.record": ("leaf", "S", {"leaf_kind": "record", "statement_of_record": "toy_result"}, "The formal statement toy_result is proved."),
    "res.bridge": ("leaf", "S", {"leaf_kind": "bridge", "attribution": "formalizer-stated"}, "The formal statement says what the claim says."),
    "res.h": ("leaf", "S", {"leaf_kind": "hypothesis", "discharge": "open"}, "The setting's hypothesis holds of the deployed system."),
    "res.complete": ("leaf", "S", {"leaf_kind": "completeness"}, "No premise beyond the listed ones is needed for the toy result."),
}
RESULT_EVENTS = [ev(1, {"node": "res.record"}, "[0.9, 0.9]"), ev(2, {"node": "res.bridge"}, "[0.8, 0.8]"),
                 ev(3, {"node": "res.h"}, "[0.1, 0.1]"), ev(4, {"node": "res.complete"}, "[0.95, 0.95]")]


class Validity(Base):
    """`X@valid`, X with its assumption and hypothesis leaves held true."""

    def test_implication_and_literal(self):
        self.tree(tweak=given_tree(RESULT, ["res"]), extra={"h1": RESULT_EVENTS})
        C, D = context(self.root)
        imp = Q(9, 10) * Q(8, 10) * Q(95, 100)
        self.assertEqual(D["nodes"]["res"]["valid_Pr"]["mid"], imp)
        self.assertEqual(D["nodes"]["res"]["literal_Pr"]["mid"], imp * Q(1, 10))
        self.assertIn("as an implication P(res@valid)", run(self.root, "--why")[1])
        self.assertIn("as an implication (res@valid) and literally", (self.root / "graph" / "view.md").read_text())

    def test_record_hypotheses_unread(self):
        """ruling F1 (2026-10-23): a record may say `hypotheses: unread`; the result is then record, bridge and completeness,
        flagged in derived.json, index.json and the view; a list mixing ids with the word is refused."""
        nodes = dict(RESULT, **{"res": ("and", "M", {"children": "[res.record, res.bridge, res.complete]"}, RESULT["res"][3]),
                                "res.record": ("leaf", "S", {"leaf_kind": "record", "statement_of_record": "toy_result", "hypotheses": "unread",
                                                             "registry_id": "toy.result"}, RESULT["res.record"][3])})
        del nodes["res.h"]
        self.tree(tweak=given_tree(nodes, ["res"]), extra={"h1": [e for e in RESULT_EVENTS if "res.h" not in e]})
        D = self.derived()
        self.assertIn("hypotheses unread", D["nodes"]["res.record"]["flags"])
        self.assertIn("hypotheses unread", D["nodes"]["res"]["flags"])
        idx = json.loads((self.root / "graph" / "index.json").read_text())
        self.assertEqual(idx["schema"], "graph-index/3")
        self.assertEqual(idx["nodes"]["res.record"]["hypotheses"], "unread")
        self.assertEqual(idx["nodes"]["res"]["formal_result"], {"record": "res.record", "hypotheses": "unread", "registry_id": "toy.result", "bears_on": []})
        self.assertEqual(idx["claims"], {"toy.result": "res"})
        self.assertIn("hypotheses unread", (self.root / "graph" / "view.md").read_text())
        self.edit("graph/nodes/res.record.md", "hypotheses: unread", "hypotheses: [res.bridge, unread]")
        self.assertIn("never both", self.refused(2))
        self.edit("graph/nodes/res.record.md", "hypotheses: [res.bridge, unread]", "hypotheses: [nonexistent]")
        self.assertIn("resolves to no node", self.refused(1))

    def test_forcing_leaves_a_table_alone(self):
        nodes = {"res2": ("and", "M", {"children": "[res.h, cases-x, res2.complete]"}, "The second argument holds."),
                 "res.h": RESULT["res.h"],
                 "res2.complete": ("leaf", "S", {"leaf_kind": "completeness"}, "No premise beyond the listed ones is needed for res2.")}
        self.tree(tweak=given_tree(nodes, ["res2"]), extra={"h1": [ev(3, {"node": "res.h"}, "[0.1, 0.1]"), ev(5, {"node": "res2.complete"}, "[1, 1]")]})
        C, D = context(self.root)
        self.assertEqual(D["nodes"]["res2"]["valid_Pr"]["mid"], C.E.prob((("v", "cases-x"),)))
        self.assertEqual(D["nodes"]["res2"]["valid_Pr"]["mid"], Q(81, 100))

    def test_a_leaf_given_the_implication_reads_it(self):
        nodes = dict(RESULT, **{"y-leaf": ("leaf", "S", {"leaf_kind": "step", "given": "res@valid"}, "The step built on the toy result holds.")})
        evs = RESULT_EVENTS + [ev(6, {"node": "y-leaf", "field": "if-holds"}, "[1, 1]"), ev(7, {"node": "y-leaf", "field": "if-fails"}, "[0, 0]")]
        self.tree(tweak=given_tree(nodes, ["y-leaf"]), extra={"h1": evs})
        C, D = context(self.root)
        self.assertEqual(C.E.prob((("v", "y-leaf"),)), Q(9, 10) * Q(8, 10) * Q(95, 100))
        self.assertIn("given res@valid", D["nodes"]["y-leaf"]["flags"])
        S = self.derived_dry("--scope", "res@valid")
        self.assertTrue({u["target"] for u in S["units"]} <= {"res", "res.record", "res.bridge", "res.h", "res.complete"})

    def test_literal_and_implication_in_one_closure_match_the_oracle(self):
        # the literal toy and a route given its validity sit in one goal; they share every unforced variable,
        # so neither collapses and the number equals the oracle's exactly
        nodes = dict(RESULT, **{"route-1": ("leaf", "S", {"leaf_kind": "step", "given": "res@valid"}, "The refinement of the toy result goes through.")})
        evs = RESULT_EVENTS + [ev(6, {"node": "route-1", "field": "if-holds"}, "[0.7, 0.7]"), ev(7, {"node": "route-1", "field": "if-fails"}, "[0.1, 0.1]")]
        self.tree(tweak=given_tree(nodes, ["res", "route-1"]), extra={"h1": evs})
        C, D = context(self.root)
        Inference.check_roots(self, C, D)
        rest = D["roots"]["plan-b"]["Pr"]["mid"] / C.E.prob((("n", "res", None), ("v", "route-1")))
        naive = C.E.prob((("n", "res", None),)) * C.E.prob((("v", "route-1"),))
        self.assertNotEqual(C.E.prob((("n", "res", None), ("v", "route-1"))), naive)
        self.assertEqual(C.E.prob((("n", "res", None), ("v", "route-1"))), Q(9, 10) * Q(8, 10) * Q(95, 100) * Q(1, 10) * Q(7, 10))
        self.assertTrue(rest > 0)


def improvable(extra_children=(), routes=("route-a", "route-b")):
    """Tweak: the toy result `res` gains an improvement or `res.improvable` over routes given res@valid, a shared-claim root."""
    def tweak(nodes):
        nodes.update(RESULT)
        kids = list(routes) + list(extra_children) + ["res.residual"]
        nodes["res.improvable"] = ("or", "M", {"children": "[" + ", ".join(kids) + "]", "improves": "res", "reality": '"a trained agent"'},
                                   "The toy result can be improved until it reflects a trained agent well.")
        for r in routes:
            nodes[r] = ("leaf", "S", {"leaf_kind": "route", "given": "res@valid"}, f"The direction {r} carries the toy result to a trained agent.")
        nodes["res.residual"] = ("leaf", "S", {"leaf_kind": "route", "residual": "true", "given": "res@valid"}, "A refinement not yet described goes through.")
    return tweak


IMPROVABLE_ROOT = ("  - {id: plan-b, role: plan, preset: worst-case, success_class: utopia}\n",
                   "  - {id: plan-b, role: plan, preset: worst-case, success_class: utopia}\n  - {id: res.improvable, role: shared-claim, preset: worst-case}\n")
ROUTE_EVENTS = RESULT_EVENTS + [ev(11, {"node": "route-a"}, "[0.5, 0.5]"), ev(12, {"node": "route-b"}, "[0.5, 0.5]"), ev(13, {"node": "res.residual"}, "[0, 0]")]


class Improvement(Base):
    """improvement claims."""

    def build(self, **kw):
        self.tree(**kw)
        self.edit("graph/frame.yaml", *IMPROVABLE_ROOT)

    def test_routes_read_as_a_disjunction_and_never_establish_by_a_check(self):
        read = [f'{{"id": "h1-9{i}", "by": "@h1", {BASE}, "kind": "{k}", "target": {{"node": "route-a"}}, {CHK}}}' for i, k in ((50, "map-read"), (51, "trace"))]
        self.build(tweak=improvable(), extra={"h1": ROUTE_EVENTS + read})
        C, D = context(self.root)
        self.assertEqual(D["roots"]["res.improvable"]["Pr"]["mid"], Q(3, 4))
        self.assertEqual(D["nodes"]["route-a"]["V"]["headline"], 8)
        self.assertEqual(D["nodes"]["route-a"]["status"], "open")                     # a route is realised only through a refinement
        self.assertEqual(D["nodes"]["route-a"]["cost"], g.INF)
        self.assertIn("established only through a realised refinement", D["nodes"]["route-a"]["cost_rows"])
        self.assertIn("improvement claim on res (reality: a trained agent)", D["nodes"]["res.improvable"]["flags"])
        Inference.check_roots(self, C, D)

    def test_a_realised_literal_child_establishes_the_claim(self):
        lit = {"res-for-agents": ("leaf", "S", {"leaf_kind": "assumption", "author": "@h2"}, "The toy result's conclusion holds for a trained agent.")}
        read = [f'{{"id": "h1-9{i}", "by": "@h1", {BASE}, "kind": "{k}", "target": {{"node": "res-for-agents"}}, {CHK}}}' for i, k in ((52, "map-read"), (53, "trace"))]

        def tw(nodes):
            improvable(extra_children=["res-for-agents"])(nodes)
            nodes.update(lit)
        self.build(tweak=tw, extra={"h1": ROUTE_EVENTS + read})
        D = self.derived()
        self.assertEqual(D["nodes"]["res-for-agents"]["status"], "established")
        self.assertEqual(D["nodes"]["res.improvable"]["status"], "established")

    def test_diagnosis_table_is_a_mixture(self):
        def tw(nodes):
            nodes.update(RESULT)
            nodes["res.improvable"] = ("cases", "M", {"children": "[res.improvable.partition, pic-gap-a, pic-gap-r]", "improves": "res", "reality": '"a trained agent"',
                                                      "rows": "\n  - {picture: pic-gap-a, class: null, observable: never}\n  - {picture: pic-gap-r, class: undescribed-failure, observable: never, residual: true}"},
                                       "The toy result can be improved until it reflects a trained agent well.")
            nodes["res.improvable.partition"] = ("leaf", "S", {"leaf_kind": "partition", "author": "@h2"}, "The diagnoses are exclusive and exhaustive.")
            nodes["pic-gap-a"] = ("leaf", "S", {"leaf_kind": "picture", "author": "@h2"}, "The binding gap is the exact-introspection assumption.")
            nodes["pic-gap-r"] = ("leaf", "S", {"leaf_kind": "picture", "author": "@h2"}, "The binding gap is something not yet described.")
            nodes["res.h"] = ("leaf", "S", {"leaf_kind": "hypothesis", "discharge": "open", "given": "res.improvable"}, RESULT["res.h"][3])
        evs = [ev(21, {"row": ["res.improvable", "pic-gap-a"], "field": "w"}, "[0.6, 0.6]"), ev(22, {"row": ["res.improvable", "pic-gap-a"], "field": "p"}, "[0.5, 0.5]"),
               ev(23, {"row": ["res.improvable", "pic-gap-r"], "field": "p"}, "[0.2, 0.2]"), ev(24, {"node": "res.improvable.partition"}, "[1, 1]")]
        self.tree(tweak=tw, extra={"h1": evs + RESULT_EVENTS})
        self.edit("graph/frame.yaml", *IMPROVABLE_ROOT)
        self.edit("graph/nodes/plan-b.md", "[shared-leaf, or-y, q-leaf, plan-b.complete]", "[shared-leaf, or-y, q-leaf, res, plan-b.complete]")
        D = self.derived()
        self.assertEqual(Q(D["roots"]["res.improvable"]["Pr"]["mid"]), Q(6, 10) * Q(5, 10) + Q(4, 10) * Q(2, 10))

    def test_foreign_given_warns(self):
        def tw(nodes):
            improvable()(nodes)
            nodes["route-b"] = ("leaf", "S", {"leaf_kind": "route", "given": "shared-leaf"}, "The direction route-b carries the toy result to a trained agent.")
        self.build(tweak=tw, extra={"h1": ROUTE_EVENTS})
        code, out, err = run(self.root)
        self.assertEqual(code, 0, err)
        self.assertIn("WARN graph/nodes/route-b.md: given shared-leaf is outside the improved claim's family", err)
        self.build(tweak=improvable(), extra={"h1": ROUTE_EVENTS})
        self.assertNotIn("WARN", run(self.root)[2])

    def test_superseded_node_stays_where_listed(self):
        self.tree()
        before = self.derived()["roots"]["plan-b"]["Pr"]
        self.edit("graph/nodes/cheap-leaf.md", "leaf_kind: assumption\n", "leaf_kind: assumption\nsuperseded_by: dear-leaf\n")
        D = self.derived()
        self.assertEqual(D["roots"]["plan-b"]["Pr"], before)
        self.assertIn("superseded by dear-leaf", D["nodes"]["cheap-leaf"]["flags"])
        self.assertIn("superseded by dear-leaf", (self.root / "graph" / "view.md").read_text())


def two_deep(nodes):
    """Tweak for synthetic_tree(programme=True): prog gains a sub-frame prog2 over a step step-3 (frames two deep)."""
    nodes["prog"] = ("frame", "L", {"children": "[step-1, step-2, sc-1, prog2]", "question": '"Does the programme reach a bounded analogue of the collapse?"', "owner": '"@h1"',
                                    "roots": "\n  - {id: step-1, role: plan, preset: worst-case, success_class: utopia}"
                                             "\n  - {id: step-2, role: plan, preset: worst-case, success_class: utopia}"
                                             "\n  - {id: sc-1, role: shared-claim, preset: worst-case}"
                                             "\n  - {id: prog2, role: plan, preset: worst-case}"}, nodes["prog"][3])
    nodes["prog2"] = ("frame", "M", {"children": "[step-3]", "question": '"Does the inner line reach it?"', "owner": '"@h1"',
                                     "roots": "\n  - {id: step-3, role: plan, preset: worst-case, success_class: utopia}"}, "The inner line reaches it through its step.")
    nodes["step-3"] = ("leaf", "M", {"leaf_kind": "step"}, "The inner step of the programme carries the collapse.")


class Goals(Base):
    """owners, unspelled and not-opened frames, wants, priorities, task leaves, work pointers, structural paths."""

    def test_frames_need_a_human_owner(self):
        self.tree()
        self.edit("graph/frame.yaml", 'owner: "@h1"\n', "")
        self.assertIn("top frame carries owner", self.refused(2))
        self.tree(programme=True)
        self.edit("graph/nodes/prog.md", 'owner: "@h1"\n', "")
        self.assertIn("a frame carries owner", self.refused(2))

    def test_unspelled_and_not_opened_frames(self):
        self.tree(programme=True, drop={"h1-s1", "h1-s2"})
        self.edit("graph/nodes/prog.md", "children: [step-1, step-2, sc-1]", "children: []")
        self.edit("graph/nodes/prog.md", "roots: \n  - {id: step-1, role: plan, preset: worst-case, success_class: utopia}\n  - {id: step-2, role: plan, preset: worst-case, success_class: utopia}\n  - {id: sc-1, role: shared-claim, preset: worst-case}", "roots: []")
        for x in ("step-1", "step-2", "sc-1"):
            (self.root / "graph" / "nodes" / f"{x}.md").unlink()
        D = self.derived()
        P = D["roots"]["prog"]
        self.assertTrue(D["nodes"]["prog"]["frame"]["unspelled"])
        self.assertIn("unspelled", D["nodes"]["prog"]["flags"])
        self.assertIsNone(P["option_value"])
        self.assertIsNone(P["value"])
        self.assertFalse(P["Pr_defined"])
        self.assertNotIn("prog", D["act"]["options"])
        self.assertIn("unspelled: no roots yet", (self.root / "graph" / "view.md").read_text())
        self.edit("graph/nodes/prog.md", "kind: frame\n", "kind: frame\nopened: false\n")
        D = self.derived()
        self.assertIn("not opened; see Notes", D["nodes"]["prog"]["flags"])
        self.assertFalse(D["nodes"]["prog"]["frame"]["unspelled"])

    def test_held_nodes_are_attached_and_no_goals(self):
        # ruling G2 (2026-10-23): a frame holds what it is about; a held node is attached by membership, is no root and no
        # goal, enters no unit of the frame, and is listed as held in derived.json, the index and the view
        def held(nodes):
            nodes["held-1"] = ("leaf", "S", {"leaf_kind": "assumption"}, "A premise the programme is about holds.")
            nodes["prog"] = ("frame", "L", {**nodes["prog"][2], "holds": "[held-1]"}, nodes["prog"][3])
        self.tree(programme=True, tweak=held, drop={"h1-s1", "h1-s2"})
        D = self.derived()
        self.assertEqual(D["held"], {"prog": ["held-1"]})
        self.assertEqual(D["nodes"]["held-1"]["held_by"], ["prog"])
        self.assertIn("held by prog", D["nodes"]["held-1"]["flags"])
        self.assertNotIn("held-1", D["roots"])
        self.assertNotIn("held-1", D["ranking"]["goals"])
        self.assertFalse([u for u in D["units"] if u["target"] == "held-1" or "held-1" in u.get("bears_on", [])])
        self.assertEqual(D["nodes"]["prog"]["frame"]["holds"], ["held-1"])
        self.assertEqual(D["roots"]["prog"]["subframe"]["holds"], ["held-1"])
        self.assertFalse(D["nodes"]["prog"]["frame"]["unspelled"])
        idx = json.loads((self.root / "graph" / "index.json").read_text())
        self.assertEqual(idx["schema"], "graph-index/3")
        self.assertEqual(idx["nodes"]["held-1"]["in_frames"], [{"frame": "prog", "role": None, "membership": "holds"}])
        self.assertEqual(idx["nodes"]["sc-1"]["in_frames"], [{"frame": "prog", "role": "shared-claim", "membership": "root"}])
        self.assertEqual(idx["nodes"]["prog"]["frame"]["holds"], ["held-1"])
        self.assertNotIn("holds", idx["nodes"]["prog"]["fields"])
        view = (self.root / "graph" / "view.md").read_text()
        self.assertIn("### Held", view)
        self.assertIn("- held-1 (leaf/assumption)", view)
        # --scope naming the held node ranks it there, and only there
        S = self.derived_dry("--scope", "held-1")
        self.assertEqual(S["ranking"]["goals"], ["held-1"])
        self.assertEqual(next(gl for gl in S["goals"] if gl["id"] == "held-1")["kind"], "held")
        # a frame with roots [] and a non-empty holds is spelled, with nothing yet a goal: no unspelled flag, no spell-out unit
        self.edit("graph/nodes/prog.md", "children: [step-1, step-2, sc-1]", "children: []")
        self.edit("graph/nodes/prog.md", "roots: \n  - {id: step-1, role: plan, preset: worst-case, success_class: utopia}\n  - {id: step-2, role: plan, preset: worst-case, success_class: utopia}\n  - {id: sc-1, role: shared-claim, preset: worst-case}", "roots: []")
        for x in ("step-1", "step-2", "sc-1"):
            (self.root / "graph" / "nodes" / f"{x}.md").unlink()
        D = self.derived()
        self.assertFalse(D["nodes"]["prog"]["frame"]["unspelled"])
        self.assertIn("spelled; nothing yet a goal (1 held)", D["nodes"]["prog"]["flags"])
        self.assertNotIn("unspelled", D["nodes"]["prog"]["flags"])
        self.assertFalse([u for u in D["units"] if u["target"] == "prog"])
        self.assertEqual(D["spell_out"]["count"], 0)
        self.assertIn("spelled, nothing yet a goal", (self.root / "graph" / "view.md").read_text())

    def test_unconfirmed_want_weighs_nothing(self):
        # ruling G4 (2026-10-23): a want filed from its owner's quoted words weighs 0 until the owner gives a word; the word then
        # gives its weight; a want the owner filed in a session (no filed_from) keeps the Default medium
        self.tree(tweak=g._with_want)
        self.edit("graph/" + g._want_root()[0], *g._want_root()[1:])
        D = self.derived()
        self.assertEqual(Q(D["nodes"]["want-x"]["want"]["weight"]), Q(0))
        self.assertIn("owner has not confirmed", D["nodes"]["want-x"]["flags"])
        self.assertEqual(Q(next(gl for gl in D["goals"] if gl["id"] == "want-x")["stake"]), Q(0))                     # listed as a goal, at no weight
        self.assertTrue(any(u["kind"] == "priority" and u["target"] == "want-x" and u["note"].startswith("confirm or disown") for u in D["units_unranked"]))
        self.append("graph/events/h1.jsonl", g._priority("@h1", "want-x", "low", 1) + "\n")
        D = self.derived()
        self.assertEqual(Q(D["nodes"]["want-x"]["want"]["weight"]), Q(1, 4))
        self.assertEqual(Q(next(gl for gl in D["goals"] if gl["id"] == "want-x")["stake"]), Q(1, 4))
        self.assertNotIn("owner has not confirmed", D["nodes"]["want-x"]["flags"])
        # the owner's own filing keeps the Default
        self.tree(tweak=g._with_want)
        self.edit("graph/" + g._want_root()[0], *g._want_root()[1:])
        self.edit("graph/nodes/want-x.md", "filed_from: quote\n", "")
        D = self.derived()
        self.assertEqual(Q(D["nodes"]["want-x"]["want"]["weight"]), Q(1, 2))
        self.assertTrue(D["nodes"]["want-x"]["want"]["confirmed"])

    def test_want_leaf_root(self):
        # with no number on it at all, the want derives, ranks by its owner's word and gets its spell-out unit
        self.tree(tweak=g._with_want)
        self.edit("graph/" + g._want_root()[0], *g._want_root()[1:])
        D = self.derived()
        R = D["roots"]["want-x"]
        self.assertEqual((R["role"], R["preset"], R["status"]), ("want", "worst-case", "open"))
        self.assertIsNone(R["gestalt"])
        self.assertTrue(any(u["target"] == "want-x" for u in D["units"]))
        # a human's gestalt on a want stands (only an AI handle's is refused)
        g_h = f'{{"id": "h2-60", "by": "@h2", {BASE}, "kind": "gestalt", "target": {{"node": "want-x"}}, "estimate": [0.3, 0.5], "derived": false, "reason": "x"}}'
        self.append("graph/events/h2.jsonl", g_h + "\n")
        D = self.derived()
        R = D["roots"]["want-x"]
        self.assertEqual(Q(R["gestalt"]["mid"]), Q(2, 5))
        self.assertIsNone(R["value"])
        self.assertNotIn("want-x", D["act"]["options"])
        self.assertIn("owner has not confirmed", D["nodes"]["want-x"]["flags"])
        W = D["nodes"]["want-x"]["want"]
        self.assertEqual((W["owner"], W["priority"], Q(W["weight"]), W["confirmed"], W["attachment"]), ("@h1", None, Q(0), False, []))   # G4: quoted, unconfirmed
        view = (self.root / "graph" / "view.md").read_text()
        self.assertIn("a want of @h1; priority unset (owner has not confirmed: weight 0); owner has not confirmed; attachment: unattached", view)
        # the owner's word: confirmed, weight set; `none` disowns at weight 0; an external event establishes the want
        self.append("graph/events/h1.jsonl", g._priority("@h1", "want-x", "high", 1) + "\n")
        D = self.derived()
        self.assertEqual((D["nodes"]["want-x"]["want"]["priority"], Q(D["nodes"]["want-x"]["want"]["weight"])), ("high", Q(1)))
        self.assertNotIn("owner has not confirmed", D["nodes"]["want-x"]["flags"])
        self.append("graph/events/h1.jsonl", g._priority("@h1", "want-x", "none", 2) + "\n")
        D = self.derived()
        self.assertEqual(Q(D["nodes"]["want-x"]["want"]["weight"]), Q(0))
        self.assertIn("disowned by owner", D["nodes"]["want-x"]["flags"])
        self.append("graph/events/h2.jsonl", f'{{"id": "h2-61", "by": "@h2", {BASE}, "kind": "external", "target": {{"node": "want-x"}}, "ref": "doi:10.1/x"}}\n')
        self.assertEqual(self.derived()["roots"]["want-x"]["status"], "established")

    def test_ai_numbers_on_a_want_are_refused(self):
        for kind, more in (("gestalt", ', "derived": false'), ("estimate", "")):
            e = f'{{"id": "ai-61", "by": "@ai", {BASE}, "kind": "{kind}", "target": {{"node": "want-x"}}, "estimate": [0.3, 0.5]{more}, "gloss": "x"}}'
            self.tree(tweak=g._with_want, extra={"ai": [e]})
            self.edit("graph/" + g._want_root()[0], *g._want_root()[1:])
            self.assertIn(f"an AI handle writes no {kind} on a want", self.refused(5))

    def test_want_with_an_explicit_preset_is_refused(self):
        self.tree(tweak=g._with_want)
        self.edit("graph/" + g._want_root()[0], *g._want_root(", preset: probabilistic, budget: 0.5")[1:])
        self.assertIn("carries no preset", self.refused(2))

    def test_task_leaf_established_only_by_an_external_event(self):
        def tw(nodes):
            g._with_task(nodes)
            nodes["t-1"] = ("leaf", "S", {"leaf_kind": "task", "who": "agent", "action": '"Write the list of trust principles by axis."',
                                          "work": "[{kind: priorities, ref: 9999}, {kind: open, ref: Workspace.Deference.trust_axis}]", "files": "[docs/x.md]"},
                            "A document lists the trust principles by axis.")
        read = [f'{{"id": "h1-6{i}", "by": "@h1", {BASE}, "kind": "{k}", "target": {{"node": "t-1"}}, {CHK}}}' for i, k in ((5, "map-read"), (6, "trace"))]
        self.tree(tweak=tw, extra={"h1": read})
        (self.root / "PRIORITIES.md").write_text("# Priorities\n\n### 1. Something — **[open]**\n")
        code, out, err = run(self.root)
        self.assertEqual(code, 0, err)
        self.assertIn("work order PRIORITIES #9999 has no '### 9999.' heading", err)
        D = json.loads((self.root / "graph" / "derived.json").read_text())
        self.assertEqual((D["nodes"]["t-1"]["V"]["headline"], D["nodes"]["t-1"]["status"]), (8, "open"))
        self.assertEqual(D["nodes"]["t-1"]["action"], "Write the list of trust principles by axis.")
        view = (self.root / "graph" / "view.md").read_text()
        self.assertIn("- t-1: Write the list of trust principles by axis. (who: agent); work order: PRIORITIES #9999; open statement: `Workspace.Deference.trust_axis`; files: docs/x.md", view)
        self.append("graph/events/h1.jsonl", f'{{"id": "h1-67", "by": "@h1", {BASE}, "kind": "external", "target": {{"node": "t-1"}}, "ref": "commit abc123"}}\n')
        self.assertEqual(self.derived()["nodes"]["t-1"]["status"], "established")

    def test_structural_paths(self):
        self.tree(programme=True, tweak=two_deep, extra={"h1": [ev(30, {"node": "step-3"}, "[0.2, 0.4]")]})
        D = self.derived()
        P = D["nodes"]["step-3"]["paths"]
        self.assertEqual(P[0], {"frames": ["top", "prog", "prog2"], "root": "step-3", "chain": ["step-3"]})
        self.assertIn({"frames": ["top", "prog"], "root": "prog2", "chain": ["prog2", "step-3"]}, P)
        self.assertIn({"frames": ["top"], "root": "prog", "chain": ["prog", "prog2", "step-3"]}, P)
        sh = D["nodes"]["shared-leaf"]["paths"]
        self.assertEqual([(p["root"], p["chain"]) for p in sh], [("plan-a", ["plan-a", "shared-leaf"]), ("plan-b", ["plan-b", "shared-leaf"])])


NOISY = {"map-read", "improve", "do", "spell-out", "connect", "admit", "re-examine"}   # units observing through read_error (0.3)


def unit_error(u):
    return Q(3, 10) if u["kind"] in NOISY else Q(0)


def ai_est(i, target, rng, gloss="an AI reading"):
    return f'{{"id": "ai-9{i:02d}", "by": "@ai", {BASE}, "kind": "estimate", "target": {json.dumps(target)}, "estimate": {rng}, "gloss": "{gloss}"}}'


def ai_gestalt(i, target, rng):
    return f'{{"id": "ai-8{i:02d}", "by": "@ai", {BASE}, "kind": "gestalt", "target": {json.dumps(target)}, "estimate": {rng}, "derived": false, "gloss": "a holistic AI reading"}}'


@contextlib.contextmanager
def stake_override(v):
    saved = g.STAKE_OVERRIDE
    g.STAKE_OVERRIDE = v
    try:
        yield
    finally:
        g.STAKE_OVERRIDE = saved


class Objective(Base):
    """weighted bits about goals: stake × promise^e, the verdict model."""

    def goals(self, D):
        return {x["id"]: x for x in D["goals"]}

    def test_regression_to_unweighted_bits(self):
        # (a) e = 0, c = 0, no wants, stake 1, goals the roots: every unit's weighted bits equal its unweighted mid bits
        self.tree(drop={"h1-2"})
        self.edit("graph/policy.yaml", "promise_exponent: 1", "promise_exponent: 0")
        self.edit("graph/policy.yaml", "verdict_c: 0.2", "verdict_c: 0")
        with stake_override(1):
            C, D = context(self.root)
        E = C.E
        self.assertEqual(D["ranking"]["goals"], ["plan-a", "plan-b"])
        for u in D["units"]:
            if u["bits"] is None:
                continue
            e = unit_error(u)
            want = 0.0
            for r in ("plan-a", "plan-b"):
                h, tt, J = E.evaluate(E.dag((E.key_of(r),)), {}, "mid", joints=True)
                j = J.get(E.key_of(u["target"]))
                if j is not None:
                    want += g.obs_bits(h, j[1], j[0], e)
            self.assertAlmostEqual(u["wbits"], want, places=12)

    def test_stake_rules(self):
        # (b) an untagged utopia plan 1/2; a plan whose table names high-conflict 3/4; a route under an improvement claim a
        # want at high contains 1; a root nothing contains the floor
        def tw(nodes):
            improvable()(nodes)
            g._with_want(nodes)
            nodes["want-x"] = ("leaf", "S", {"leaf_kind": "want", "want": "true", "owner": '"@h1"', "filed_from": "quote", "given": "res.improvable"},
                               "The toy collapse is written up with its proof kernel-checked.")
            nodes["risk-z"] = ("leaf", "S", {"leaf_kind": "assumption"}, "A risk nobody's plan cites obtains.")
        self.tree(tweak=tw, extra={"h1": [g._priority("@h1", "want-x", "high", 1)] + ROUTE_EVENTS + [ev(40, {"node": "risk-z"}, "[0.5, 0.5]")]})
        self.edit("graph/frame.yaml", *IMPROVABLE_ROOT)
        self.edit("graph/" + g._want_root()[0], *g._want_root()[1:])
        self.edit("graph/frame.yaml", g._PLAN_B_ROOT, g._PLAN_B_ROOT + "  - {id: risk-z, role: risk-story, preset: worst-case}\n")
        D = self.derived()
        G = self.goals(D)
        self.assertEqual(Q(G["plan-b"]["stake"]), Q(1, 2))
        # plan-a's table names high-conflict: its stake is (U(utopia) − E[U | failure])/2, between 1/2 and 3/4, moving with
        # the failure's mass rather than jumping to 3/4 at the first admitted row
        R = D["roots"]["plan-a"]
        pr, val = Q(R["Pr"]["mid"]), Q(R["value"]["mid"])
        self.assertEqual(Q(G["plan-a"]["stake"]), (1 - min(Q(0), (val - pr) / (1 - pr))) / 2)
        self.assertTrue(Q(1, 2) < Q(G["plan-a"]["stake"]) < Q(3, 4))
        self.assertEqual(Q(G["want-x"]["stake"]), Q(1))
        self.assertEqual((G["route-a"]["kind"], Q(G["route-a"]["stake"])), ("route", Q(1)))
        self.assertEqual((Q(G["res.improvable"]["stake"]), G["res.improvable"]["stake_from"]), (Q(1), "want-x"))
        # risk-z is one leaf nothing reads: no goal of its own, offered to connect in the unranked block
        self.assertNotIn("risk-z", G)
        self.assertIn(("connect", "risk-z"), [(u["kind"], u["target"]) for u in D["units_unranked"]])
        self.assertEqual(G["route-a"]["home_root"], "res.improvable")

    def test_promise_and_exponent(self):
        # (c) a gestalt sets the promise at its shrunk value; without one, the shrunk derived probability; e scales it
        self.tree(extra={"ai": [ai_gestalt(1, {"node": "plan-b"}, "[0.9, 0.9]")]})
        D = self.derived()
        G = self.goals(D)
        self.assertAlmostEqual(G["plan-b"]["pi"], 0.5 + 0.8 * 0.4)             # J 0: ρ = 1 − 0.2 · 1
        self.assertEqual(G["plan-b"]["pi_source"], "gestalt")
        self.assertTrue(G["plan-b"]["rests_on_ai"])
        self.assertEqual(G["plan-a"]["pi_source"], "derived")
        self.assertAlmostEqual(G["plan-a"]["pi"], G["plan-a"]["P_forecast"])
        # the gestalt 0.9 sits far from plan-b's derived number, so the suspicion summand (Default 1/2) joins the promise
        s_ = 0.5 if G["plan-b"]["suspect"] else 0.0
        self.assertTrue(G["plan-b"]["suspect"])
        self.assertAlmostEqual(G["plan-b"]["weight"], 0.5 * (G["plan-b"]["pi"] + s_))
        self.edit("graph/policy.yaml", "promise_exponent: 1", "promise_exponent: 2")
        G2 = self.goals(self.derived())
        self.assertAlmostEqual(G2["plan-b"]["weight"], 0.5 * (G["plan-b"]["pi"] ** 2 + s_))
        self.edit("graph/policy.yaml", "promise_exponent: 2", "promise_exponent: 0")
        G0 = self.goals(self.derived())
        self.assertAlmostEqual(G0["plan-b"]["weight"], 0.5 * (1 + s_))
        self.edit("graph/policy.yaml", "also_for_share: 0.2\n", "also_for_share: 0.2\nsuspicion_weight: 0\n")
        Gs = self.goals(self.derived())
        self.assertAlmostEqual(Gs["plan-b"]["weight"], 0.5)

    def test_verdict_model(self):
        # (d) an unread AI leaf at 0.985 forecasts at 0.888 while its displayed mid stays 0.985; a proposed table enters the
        # forecast at its drafted rows and the display at 1/2
        self.tree(drop={"h2-10"}, extra={"ai": [ai_est(1, {"node": "alt-2"}, "[0.985, 0.985]")]})
        C, D = context(self.root)
        self.assertEqual(D["judgments"]["node/alt-2/range"]["mid"], Q(985, 1000))
        self.assertAlmostEqual(C.E.lp("alt-2", None, "verdict"), 0.888)
        def tw(nodes):
            nodes["pic-r"] = ("leaf", "S", {"leaf_kind": "picture", "author": "@ai"}, nodes["pic-r"][3])
        self.tree(tweak=tw, pic_h_author="@ai")
        C, D = context(self.root)
        self.assertEqual(C.E.prob((("v", "cases-x"),), {}, "mid"), Q(1, 2))
        v = C.E.prob((("v", "cases-x"),), {}, "verdict")
        rho = 1 - 0.2 * float(g.floor_width(C, D["judgments"]["row/cases-x/pic-h/p"]["level"]))
        self.assertAlmostEqual(v, 0.3 * (0.5 + rho * 0.1) + 0.7 * (0.5 + rho * 0.4))
        self.assertNotAlmostEqual(v, 0.5)

    def test_a_shared_leaf_carries_both_goals(self):
        # (e) shared-leaf, open again, informs both plans; its unit's weighted bits are the sum over the two
        self.tree(drop={"h1-2"})
        D = self.derived()
        u = next(u for u in D["units"] if u["target"] == "shared-leaf" and u["kind"] == "trace")
        self.assertEqual(sorted(f["goal"] for f in u["for"]), ["plan-a", "plan-b"])
        self.assertAlmostEqual(u["wbits"], sum(f["wbits"] for f in u["for"]))
        self.assertAlmostEqual(sum(f["share"] for f in u["for"]), 1.0)
        self.assertEqual(D["nodes"]["shared-leaf"]["informs"], ["plan-a", "plan-b"])
        G = self.goals(D)
        self.assertAlmostEqual(D["nodes"]["shared-leaf"]["informs_weighted"], G["plan-a"]["weight"] + G["plan-b"]["weight"])

    def test_personal_weights(self):
        # (f) --as @h weighs h's wants in full and another owner's at half; the committed files stay pooled
        self.tree(tweak=g._with_want)
        self.edit("graph/" + g._want_root()[0], *g._want_root()[1:])
        self.append("graph/events/h1.jsonl", g._priority("@h1", "want-x", "medium", 1) + "\n")   # confirmed: a quoted want unconfirmed weighs 0 (G4)
        self.derived()
        self.derived()                                  # a second plain run: the digest now has a like-for-like previous
        snap = {n: (self.root / "graph" / n).read_text() for n in g.GENERATED}
        own = self.goals(self.derived_dry("--as", "@h1"))["want-x"]
        other = self.goals(self.derived_dry("--as", "@h2"))["want-x"]
        self.assertEqual((Q(own["stake"]), Q(other["stake"])), (Q(1, 2), Q(1, 4)))
        for flags in (("--as", "@h1"), ("--as", "@h2")):
            self.assertEqual(run(self.root, *flags)[0], 0)
            for n in g.GENERATED:
                self.assertEqual((self.root / "graph" / n).read_text(), snap[n], (flags, n))

    def test_nested_counting_is_reported(self):
        # (g) the same four leaves filed flat (one goal) and nested (four goals in one chain): the ratio of a leaf unit's
        # score between the two filings is reported, not asserted (Q22)
        leaves = {f"n{i}": ("leaf", "S", {"leaf_kind": "assumption"}, f"The nested premise n{i} holds.") for i in range(1, 5)}
        def flat(nodes):
            nodes.update(leaves)
            nodes["flat"] = ("and", "S", {"children": "[n1, n2, n3, n4, flat.complete]"}, "The flat claim holds.")
            nodes["flat.complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, "No premise beyond the four is needed.")
        def nested(nodes):
            nodes.update(leaves)
            nodes["flat"] = ("and", "S", {"children": "[n1, mid-1, flat.complete]", "refinement_of": "plan-b"}, "The flat claim holds.")
            nodes["mid-1"] = ("and", "S", {"children": "[n2, mid-2, mid-1.complete]", "refinement_of": "plan-b"}, "The first nested claim holds.")
            nodes["mid-2"] = ("and", "S", {"children": "[n3, n4, mid-2.complete]", "refinement_of": "plan-b"}, "The second nested claim holds.")
            nodes["flat.complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, "No premise beyond the four is needed.")
            for m in ("mid-1", "mid-2"):
                nodes[m + ".complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, f"No premise beyond the listed ones is needed for {m}.")
        evs = [ev(50 + i, {"node": f"n{i}"}, "[0.7, 0.7]") for i in range(1, 5)] + [ev(55, {"node": "flat.complete"}, "[1, 1]"),
               ev(56, {"node": "mid-1.complete"}, "[1, 1]"), ev(57, {"node": "mid-2.complete"}, "[1, 1]")]
        out = {}
        for name, tw in (("flat", flat), ("nested", nested)):
            self.root = pathlib.Path(self.tmp) / name
            self.tree(tweak=tw, extra={"h1": evs if name == "nested" else evs[:5]})
            self.edit("graph/frame.yaml", g._PLAN_B_ROOT, g._PLAN_B_ROOT + "  - {id: flat, role: shared-claim, preset: worst-case}\n")
            D = self.derived()
            u = next(u for u in D["units"] if u["target"] == "n4" and u["kind"] == "vet")
            out[name] = (u["rate"], u["nested_for"])
        ratio = out["nested"][0] / out["flat"][0]
        type(self).nested_ratio = ratio
        print(f"\n  nested counting (Q22): vet n4 scores {ratio:.3f}× flat when filed as four nested goals (nested_for {out['nested'][1]})")
        self.assertEqual(out["flat"][1], 1)
        self.assertGreaterEqual(out["nested"][1], 2)


def right_reasons(nodes):
    """The right-reasons fixture: a sub-frame F holding a literal toy X, a scoped
    refinement X2 with an AI gestalt, an improvement claim I on X, a plan step S and a want W given I; beside F a risk
    story at the floor. Every number is an AI estimate (J 0) except the want's conditional table, its owner's."""
    nodes["sub-f"] = ("frame", "L", {"children": "[toy-x, toy-x2, toy-x.improvable, step-s, want-w]", "question": '"Does the toy extend?"', "owner": '"@h1"',
                                     "roots": "\n  - {id: toy-x, role: shared-claim, preset: worst-case}"
                                              "\n  - {id: toy-x2, role: shared-claim, preset: worst-case}"
                                              "\n  - {id: toy-x.improvable, role: shared-claim, preset: worst-case}"
                                              "\n  - {id: step-s, role: plan, preset: worst-case, success_class: utopia}"
                                              "\n  - {id: want-w, role: want}"}, "The toy line extends to bounded agents.")
    nodes["toy-x"] = ("and", "M", {"children": "[toy-x.record, toy-x.bridge, toy-x.h, toy-x.complete]"}, "The toy collapse holds in its setting.")
    nodes["toy-x.record"] = ("leaf", "S", {"leaf_kind": "record", "statement_of_record": "toy_collapse"}, "The formal statement toy_collapse is proved.")
    nodes["toy-x.bridge"] = ("leaf", "S", {"leaf_kind": "bridge", "attribution": "formalizer-stated"}, "The formal statement says what the toy claim says.")
    nodes["toy-x.h"] = ("leaf", "S", {"leaf_kind": "hypothesis", "discharge": "open"}, "The expert's estimates are exactly known to it.")
    nodes["toy-x.complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, "No premise beyond the listed ones is needed for the toy collapse.")
    nodes["toy-x2"] = ("and", "M", {"children": "[x2-a, x2-b, x2-c, x2-assume, toy-x2.complete]", "refinement_of": "toy-x"},
                       "The scoped collapse holds for experts whose estimates are asymptotically known.")
    for x in ("x2-a", "x2-b", "x2-c"):
        nodes[x] = ("leaf", "S", {"leaf_kind": "step"}, f"The scoped collapse's lemma {x} holds.")
    nodes["x2-assume"] = ("leaf", "S", {"leaf_kind": "assumption"}, "The expert's estimates converge.")
    nodes["toy-x2.complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, "No premise beyond the listed ones is needed for the scoped collapse.")
    nodes["toy-x.improvable"] = ("or", "M", {"children": "[route-x2, toy-x.residual]", "improves": "toy-x", "reality": '"a trained agent"'},
                                 "The toy collapse can be improved until it reflects a trained agent well.")
    nodes["route-x2"] = ("leaf", "S", {"leaf_kind": "route", "given": "toy-x2@valid"}, "The scoped statement's route carries the toy to a trained agent.")
    nodes["toy-x.residual"] = ("leaf", "S", {"leaf_kind": "route", "residual": "true", "given": "toy-x@valid"}, "A refinement not yet described carries it.")
    nodes["step-s"] = ("leaf", "M", {"leaf_kind": "step", "given": "toy-x2@valid"}, "The bounded-agent step built on the scoped collapse holds.")
    nodes["want-w"] = ("leaf", "S", {"leaf_kind": "want", "want": "true", "owner": '"@h1"', "given": "toy-x.improvable"},
                       "The toy collapse is written up with its proof kernel-checked.")
    nodes["risk-u"] = ("leaf", "S", {"leaf_kind": "assumption"}, "An unrelated risk obtains.")


RR_ROOTS = ("  - {id: plan-b, role: plan, preset: worst-case, success_class: utopia}\n",
            "  - {id: plan-b, role: plan, preset: worst-case, success_class: utopia}\n  - {id: sub-f, role: plan, preset: worst-case}\n"
            "  - {id: risk-u, role: risk-story, preset: worst-case}\n")


def rr_events(x2_gestalt="[0.6, 0.6]"):
    evs = [(("node", "toy-x.record"), "[0.9, 0.95]"), (("node", "toy-x.bridge"), "[0.8, 0.9]"), (("node", "toy-x.h"), "[0.02, 0.08]"),
           (("node", "toy-x.complete"), "[0.05, 0.15]"), (("node", "x2-a"), "[0.5, 0.8]"), (("node", "x2-b"), "[0.5, 0.8]"),
           (("node", "x2-c"), "[0.5, 0.8]"), (("node", "x2-assume"), "[0.6, 0.7]"), (("node", "toy-x2.complete"), "[0.85, 0.95]"),
           (("node", "route-x2", "if-holds"), "[0.6, 0.7]"), (("node", "route-x2", "if-fails"), "[0.1, 0.2]"),
           (("node", "toy-x.residual"), "[0.1, 0.1]"), (("node", "step-s", "if-holds"), "[0.7, 0.8]"), (("node", "step-s", "if-fails"), "[0.1, 0.2]"),
           (("node", "risk-u"), "[0.5, 0.5]")]
    out = []
    for i, (tg, rng) in enumerate(evs):
        target = {"node": tg[1]} if len(tg) == 2 else {"node": tg[1], "field": tg[2]}
        out.append(ai_est(10 + i, target, rng))
    out.append(ai_gestalt(1, {"node": "toy-x2"}, x2_gestalt))
    return out


# the want's conditional table is its owner's: an AI handle writes no number on a want
RR_WANT = [ev(60, {"node": "want-w", "field": "if-holds"}, "[0.8, 0.9]"), ev(61, {"node": "want-w", "field": "if-fails"}, "[0.2, 0.3]")]


class Units(Base):
    """research, drafting, admission and suspicion units."""

    def units_on(self, D, x):
        return sorted(u["kind"] for u in D["units"] if u["target"] == x)

    def test_improve_do_and_their_targets(self):
        def tw(nodes):
            improvable()(nodes)
            g._with_task(nodes)
            nodes["t-1"] = ("leaf", "S", {"leaf_kind": "task", "who": "agent", "action": '"Write the list of trust principles by axis."'},
                            "A document lists the trust principles by axis.")
            nodes["t-2"] = ("leaf", "S", {"leaf_kind": "task", "who": "human", "action": '"Decide which statement to publish."'},
                            "A decision names the statement to publish.")
            nodes["plan-b"] = ("and", "M", {"children": "[shared-leaf, or-y, q-leaf, t-1, t-2, plan-b.complete]"}, nodes["plan-b"][3])
        self.tree(tweak=tw, extra={"h1": ROUTE_EVENTS + [ev(60, {"node": "t-1"}, "[0.8, 0.8]"), ev(61, {"node": "t-2"}, "[0.9, 0.9]")]})
        self.edit("graph/frame.yaml", *IMPROVABLE_ROOT)
        D = self.derived()
        self.assertEqual(self.units_on(D, "q-leaf"), ["improve"])                     # a question: improve, no vet
        self.assertEqual(self.units_on(D, "alt-1"), ["improve", "map-read", "vet"])   # a step keeps vet and map-read beside improve
        self.assertIn("improve", self.units_on(D, "route-a"))
        self.assertEqual(self.units_on(D, "route-a"), ["improve"])                    # a route: improve only
        self.assertNotIn("improve", self.units_on(D, "cheap-leaf") + self.units_on(D, "shared-leaf") + self.units_on(D, "res.h"))
        self.assertEqual(self.units_on(D, "t-1"), ["do"])                             # a task leaf: do and nothing else
        t1 = next(u for u in D["units"] if u["target"] == "t-1")
        t2 = next(u for u in D["units"] if u["target"] == "t-2")
        self.assertEqual((t1["section"], t2["section"]), ("agent", "main"))
        self.assertEqual(t1["text"], "Write the list of trust principles by axis.")
        self.assertEqual(Q(t1["minutes"]), Q(45))

    def test_step_keeps_vet_beside_improve(self):
        self.tree()
        D = self.derived()
        self.assertEqual(self.units_on(D, "alt-2"), [])                              # not in the closure (the choice took alt-1)
        self.assertEqual(self.units_on(D, "alt-1"), ["improve", "map-read", "vet"])
        self.assertNotIn("improve", self.units_on(D, "cases-x"))

    def test_spell_out_and_connect_on_wants(self):
        self.tree(tweak=g._with_want)
        self.edit("graph/" + g._want_root()[0], *g._want_root()[1:])
        D = self.derived()
        self.assertEqual(self.units_on(D, "want-x"), ["connect", "spell-out"])   # no map-read: spell-out replaces it; no gestalt on a want
        self.assertEqual(next(u for u in D["units"] if u["target"] == "want-x" and u["kind"] == "spell-out")["minutes"], "8/1")
        self.assertEqual(D["units_unranked"][0]["kind"], "priority")
        self.assertTrue(D["units_unranked"][0]["note"].startswith("confirm or disown"))
        # attached by a given edge: no connect
        self.edit("graph/nodes/want-x.md", "leaf_kind: want\n", "leaf_kind: want\ngiven: cases-x\n")
        D = self.derived()
        self.assertEqual(self.units_on(D, "want-x"), ["spell-out"])

    def test_spell_out_on_frames(self):
        def empty(nodes):
            nodes["prog"] = ("frame", "L", {"children": "[]", "question": '"Does the programme reach a bounded analogue?"', "owner": '"@h1"', "roots": "[]"}, nodes["prog"][3])
            for x in ("step-1", "step-2", "sc-1"):
                del nodes[x]
        self.tree(programme=True, tweak=empty, drop={"h1-s1", "h1-s2"})
        D = self.derived()
        u = next(u for u in D["units"] if u["target"] == "prog")
        self.assertEqual(u["kind"], "spell-out")
        self.assertGreater(u["wbits"], 0)
        self.edit("graph/nodes/prog.md", "kind: frame\n", "kind: frame\nopened: false\n")
        D = self.derived()
        self.assertFalse([u for u in D["units"] if u["target"] == "prog"])

    def test_ranked_admit_and_the_quick_line(self):
        self.tree(pic_h_author="@ai")
        C, D = context(self.root)
        self.assertIn("admit", self.units_on(D, "cases-x"))
        quick = next(u for u in D["units_unranked"] if u["kind"] == "admit")
        self.assertEqual((quick["target"], quick["rows"]), ("cases-x", ["pic-h"]))
        before = D["roots"]["plan-a"]["Pr"]["mid"]
        self.append("graph/events/h1.jsonl", f'{{"id": "h1-95", "by": "@h1", {BASE}, "kind": "admit", "target": {{"row": ["cases-x", "pic-h"]}}, "estimate": "accept"}}\n')
        C2, D2 = context(self.root)
        after = D2["roots"]["plan-a"]["Pr"]["mid"]
        self.assertNotEqual(before, after)
        self.assertIn(f"plan-a from {float(before):.2g} to {float(after):.2g}", quick["note"])
        self.assertNotIn("admit", self.units_on(D2, "cases-x"))

    def test_re_examine_and_structure_suspect(self):
        for gest, want in (("[0.5, 0.5]", True), ("[0.5, 0.5]", None)):
            pass
        def rows(p):
            return [ev(70, {"node": "alt-1"}, "[0.9, 1]")]
        # derived 0.01 against gestalt 0.5: suspect; derived 0.3 against 0.5: not
        for lo, flagged in (("0.01", True), ("0.3", False)):
            def tw(nodes):
                nodes["plan-b"] = ("and", "M", {"children": "[gl, plan-b.complete]"}, nodes["plan-b"][3])
                nodes["gl"] = ("leaf", "S", {"leaf_kind": "assumption"}, "The single premise of plan B holds.")
                for x in ("shared-leaf", "or-y", "cheap-leaf", "dear-leaf", "q-leaf"):
                    pass
            self.root = pathlib.Path(self.tmp) / f"rx{lo}"
            self.tree(extra={"h1": [ev(71, {"node": "plan-b.complete"}, "[1, 1]")],
                             "ai": [ai_gestalt(2, {"node": "plan-b"}, "[0.5, 0.5]"), ai_est(3, {"node": "q-leaf"}, f"[{lo}, {lo}]")]}, drop={"h2-9"})
            D = self.derived()
            rx = [u for u in D["units"] if u["kind"] == "re-examine"]
            self.assertEqual([u["target"] for u in rx], ["plan-b"])                   # an and goal with a gestalt; none on a leaf
            self.assertEqual(any(s.startswith("structure suspect: derived") for s in rx[0]["signals"]), flagged, (lo, rx[0]))

    def test_ai_conjunct_gestalt_line(self):
        def tw(nodes):
            nodes["plan-b"] = ("and", "M", {"children": "[c1, c2, c3, plan-b.complete]"}, nodes["plan-b"][3])
            for x in ("c1", "c2", "c3"):
                nodes[x] = ("leaf", "S", {"leaf_kind": "assumption"}, f"The premise {x} of plan B holds.")
            for x in ("or-y", "cheap-leaf", "dear-leaf", "q-leaf"):
                del nodes[x]
            g._with_want(nodes)
        evs = [ai_est(20 + i, {"node": x}, "[0.5, 0.7]") for i, x in enumerate(("c1", "c2", "c3"))]
        self.tree(tweak=tw, drop={"h1-3", "h1-4", "h2-9", "h2-15"}, extra={"ai": evs})
        self.edit("graph/" + g._want_root()[0], *g._want_root()[1:])
        D = self.derived()
        self.assertEqual([u["kind"] for u in D["units_unranked"][:2]], ["priority", "gestalt"])
        self.assertEqual(D["units_unranked"][1]["target"], "plan-b")
        self.assertIn("multiplies 3 unread guesses", D["units_unranked"][1]["note"])
        self.append("graph/events/h1.jsonl", f'{{"id": "h1-96", "by": "@h1", {BASE}, "kind": "gestalt", "target": {{"node": "plan-b"}}, "estimate": [0.3, 0.4], "derived": false, "reason": "the three premises are linked"}}\n')
        D = self.derived()
        self.assertFalse([u for u in D["units_unranked"] if u["kind"] == "gestalt" and u["target"] == "plan-b"])

    def test_no_goal_no_unit(self):
        self.tree()
        D = self.derived()
        self.assertEqual(D["nodes"]["alt-2"]["informs"], [])
        self.assertFalse([u for u in D["units"] if u["target"] == "alt-2"])
        self.assertIn("| alt-2 | leaf/step |", (self.root / "graph" / "view.md").read_text())
        row = next(l for l in (self.root / "graph" / "view.md").read_text().splitlines() if l.startswith("| alt-2 |"))
        self.assertIn("informs no goal", row)

    def test_right_reasons_no_ids(self):
        self.tree(tweak=right_reasons, extra={"ai": rr_events(), "h1": RR_WANT})
        self.edit("graph/frame.yaml", *RR_ROOTS)
        # with the suspicion summand on, toy-x2 (derived far below its gestalt 0.6) is suspect and its own weight rises
        G1 = {x["id"]: x for x in self.derived()["goals"]}
        self.assertTrue(G1["toy-x2"]["suspect"])
        # the centrality property below is about promise and stake, so it is checked with the summand off
        self.edit("graph/policy.yaml", "also_for_share: 0.2\n", "also_for_share: 0.2\nsuspicion_weight: 0\n")
        D = self.derived()
        x2 = {"x2-a", "x2-b", "x2-c", "x2-assume", "toy-x2.complete"}
        xonly = {"toy-x.record", "toy-x.bridge", "toy-x.h", "toy-x.complete"}
        main = [u for u in D["units"] if u.get("section", "main") == "main"]
        rank = {(u["kind"], u["target"]): i for i, u in enumerate(main)}
        worst_x2 = max(i for (k, x), i in rank.items() if x in x2)
        best_xonly = min(i for (k, x), i in rank.items() if x in xonly)
        self.assertLess(worst_x2, best_xonly, [(u["kind"], u["target"]) for u in main])
        top = next(u for u in main if u["target"] in x2)
        goals = {f["goal"]: f for f in top["for"]}
        self.assertIn("toy-x2", goals)
        self.assertTrue({"toy-x.improvable", "step-s", "want-w"} & set(goals))
        self.assertGreaterEqual(sum(f["wbits"] for gg, f in goals.items() if gg != "toy-x2"), top["wbits"] / 5)
        self.assertEqual(D["units_unranked"][0]["kind"], "priority")
        self.assertEqual(D["units_unranked"][0]["target"], "want-w")
        type(self).rr_top = top
        rates = {u["target"]: u["rate"] for u in main if u["target"] in x2 and u["kind"] == "vet"}
        via_w = {u["target"] for u in main if u["target"] in x2 and u["kind"] == "vet" and any(f["goal"] == "want-w" for f in u["for"])}
        self.assertTrue(via_w)
        for word, cmp, weak in (("high", self.assertGreater, self.assertGreaterEqual), ("low", self.assertLess, self.assertLessEqual)):
            self.root = pathlib.Path(self.tmp) / f"rr-{word}"
            self.tree(tweak=right_reasons, extra={"ai": rr_events(), "h1": [g._priority("@h1", "want-w", word, 1)] + RR_WANT})
            self.edit("graph/frame.yaml", *RR_ROOTS)
            self.edit("graph/policy.yaml", "also_for_share: 0.2\n", "also_for_share: 0.2\nsuspicion_weight: 0\n")
            D2 = self.derived()
            for u in D2["units"]:
                if u["target"] in rates and u["kind"] == "vet":
                    # strictly where the unit's bits reach the want; never the other way elsewhere (x2-assume is held true in
                    # the scoped claim's validity, so it informs the scoped claim alone)
                    (cmp if u["target"] in via_w else weak)(u["rate"], rates[u["target"]], (word, u["target"]))
        self.root = pathlib.Path(self.tmp) / "rr-gestalt"
        self.tree(tweak=right_reasons, extra={"ai": rr_events("[0.1, 0.1]"), "h1": RR_WANT})
        self.edit("graph/frame.yaml", *RR_ROOTS)
        self.edit("graph/policy.yaml", "also_for_share: 0.2\n", "also_for_share: 0.2\nsuspicion_weight: 0\n")
        D3 = self.derived()
        for u in D3["units"]:
            if u["target"] in rates and u["kind"] == "vet":
                self.assertLess(u["rate"], rates[u["target"]], u["target"])


def ranked_lines(text):
    """The ranked list's numbered lines and the path line under each, from a rendered tasks.md section."""
    sec = text.split("## Ranked units")[1].split("## Agent work")[0].splitlines()
    out = []
    for i, l in enumerate(sec):
        if l[:1].isdigit() and ". " in l:
            out.append((l, sec[i + 1] if i + 1 < len(sec) else ""))
    return out


class Display(Base):
    """paths on every line, signals and the hoist rule, agent work, the goal table, numbers only under --why."""

    def tasks(self):
        return (self.root / "graph" / "tasks.md").read_text()

    def test_every_ranked_line_has_a_path_from_top(self):
        self.tree(programme=True, tweak=two_deep, extra={"h1": [ev(30, {"node": "step-3"}, "[0.2, 0.4]")]})
        self.derived()
        lines = ranked_lines(self.tasks())
        self.assertTrue(lines)
        for head, path in lines:
            self.assertTrue(path.startswith("   path: top"), (head, path))
        D = self.derived()
        for u in D["units"]:
            self.assertEqual(u["path"][0], {"id": "top", "edge": None})
        u = next(u for u in D["units"] if u["target"] == "step-3" and u["kind"] == "vet")
        self.assertEqual(u["path_line"], "top → prog → prog2 → step-3")          # every frame between top and the goal

    def test_evidence_hop_and_shortest_chain(self):
        nodes = dict(Y_LEAF, **{"x-leaf": ("leaf", "S", {"leaf_kind": "assumption", "given": "y-leaf"}, "The claim X holds.")})
        evs = [ev(1, {"node": "y-leaf"}, "[0.4, 0.4]"), ev(2, {"node": "x-leaf", "field": "if-holds"}, "[0.9, 0.9]"),
               ev(3, {"node": "x-leaf", "field": "if-fails"}, "[0.2, 0.2]")]
        def tw(nodes_):
            given_tree(nodes, ["x-leaf"])(nodes_)
            nodes_["or-y"] = ("or", "S", {"children": "[cheap-leaf, dear-leaf, shared-leaf]"}, nodes_["or-y"][3])
        self.tree(tweak=tw, drop={"h1-2"}, extra={"h1": evs})
        D = self.derived()
        u = next(u for u in D["units"] if u["target"] == "y-leaf" and u["kind"] == "vet")
        self.assertEqual(u["path_line"], "top → plan-b → x-leaf ⇢ y-leaf")
        self.assertIn("   path: top → plan-b → x-leaf ⇢ y-leaf", self.tasks())
        # shared-leaf sits under plan-b directly and under its or: the shorter chain is shown
        C, D2 = context(self.root)
        self.assertEqual(g._hops(C, "plan-b", "shared-leaf", False), [{"id": "shared-leaf", "edge": "→"}])
        u = next(u for u in D["units"] if u["target"] == "shared-leaf" and u["kind"] == "trace")
        self.assertIn(u["path_line"], ("top → plan-a → shared-leaf", "top → plan-b → shared-leaf"))

    def test_elision_at_path_max(self):
        def tw(nodes):
            chain = [f"r{i}" for i in range(1, 9)]
            nodes["plan-b"] = ("and", "M", {"children": "[shared-leaf, or-y, q-leaf, r1, plan-b.complete]"}, nodes["plan-b"][3])
            for i, r in enumerate(chain):
                kid = chain[i + 1] if i + 1 < len(chain) else "z-leaf"
                nodes[r] = ("and", "S", {"children": f"[{kid}, {r}.complete]", "refinement_of": "plan-b"}, f"The refinement {r} holds.")
                nodes[r + ".complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, f"No premise beyond the listed one is needed for {r}.")
            nodes["z-leaf"] = ("leaf", "S", {"leaf_kind": "assumption"}, "The innermost premise holds.")
        evs = [ev(40, {"node": "z-leaf"}, "[0.5, 0.5]")] + [ev(41 + i, {"node": f"r{i + 1}.complete"}, "[1, 1]") for i in range(8)]
        self.tree(tweak=tw, extra={"h1": evs})
        D = self.derived()
        u = next(u for u in D["units"] if u["target"] == "z-leaf" and u["kind"] == "vet")
        printed = [t_ for t_ in u["path_line"].replace("⇢", "→").split(" → ")]
        self.assertIn("…", printed)
        self.assertEqual(len([t_ for t_ in printed if t_ != "…"]), 7, u["path_line"])
        self.assertTrue(u["path_line"].startswith("top → plan-b → r1 → r2 → …"), u["path_line"])
        self.assertTrue(u["path_line"].endswith("→ z-leaf"), u["path_line"])
        self.assertGreater(len(u["path"]), 7)                                     # derived.json keeps the whole path

    def test_also_for_at_the_share_threshold(self):
        self.tree(drop={"h1-2"})
        self.derived()
        line = next(h for h, _ in ranked_lines(self.tasks()) if " trace shared-leaf " in h)
        self.assertRegex(line, r"— for plan-[ab]; also plan-[ab]")
        self.edit("graph/policy.yaml", "also_for_share: 0.2", "also_for_share: 1")
        self.derived()
        line = next(h for h, _ in ranked_lines(self.tasks()) if " trace shared-leaf " in h)
        self.assertNotIn("; also", line)

    def test_agent_work_by_goal_and_all(self):
        def tw(nodes):
            g._with_task(nodes)
            nodes["t-1"] = ("leaf", "S", {"leaf_kind": "task", "who": "agent", "action": '"Write the list of trust principles by axis."'},
                            "A document lists the trust principles by axis.")
        self.tree(programme=True, tweak=tw, extra={"h1": [ev(60, {"node": "t-1"}, "[0.8, 0.8]")]})
        D = self.derived()
        text = self.tasks()
        agent = text.split("## Agent work")[1].split("## By goal")[0]
        self.assertIn("1. do t-1 (S) — for plan-b", agent)
        self.assertIn("Write the list of trust principles by axis.", agent)
        self.assertNotIn("do t-1", text.split("## Ranked units")[1].split("## Agent work")[0])
        self.assertIn("do t-1", D["agent_top"])
        table = text.split("## By goal")[1].split("## Judgment")[0]
        order = [l.strip().split(" ")[1] for l in table.splitlines() if l.strip().startswith("- ")]
        self.assertEqual(order, [g_ for g_, _ in D["goal_order"]])
        # sc-1 is a one-leaf shared claim: no goal of its own (fix stage), so the outline lists the plans and steps only
        self.assertEqual(order, ["plan-a", "plan-b", "prog", "step-1", "step-2"])
        self.assertNotIn("sc-1", [g_ for g_, _ in D["goal_order"]])
        self.assertIn("  - step-1 (plan of prog)", table)
        # tasks_shown limits the committed list; --all prints every unit
        self.edit("graph/policy.yaml", "tasks_shown: 40", "tasks_shown: 1")
        D = self.derived()
        main = [u for u in D["units"] if u.get("section", "main") == "main"]
        self.assertEqual(len(ranked_lines(self.tasks())), 1)
        self.assertIn(f"… {len(main) - 1} more ranked units", self.tasks())
        out = run(self.root, "--all")[1]
        self.assertEqual(len(ranked_lines(out.split("# View")[0])), len(main))

    def test_minutes_only_under_why(self):
        self.tree()
        self.derived()
        head = ranked_lines(self.tasks())[0][0]
        self.assertNotIn("min", head)
        out = run(self.root, "--why")[1]
        self.assertRegex(ranked_lines(out.split("# View")[0])[0][0], r"— \d+ min")
        self.assertIn("score(u) = Σ_{g ∈ G, x informs g}", out)
        self.assertIn("| goal | kind | home root | stake |", out)

    def test_right_reasons_paths(self):
        self.tree(tweak=right_reasons, extra={"ai": rr_events(), "h1": RR_WANT})
        self.edit("graph/frame.yaml", *RR_ROOTS)
        D = self.derived()
        x2 = {"x2-a", "x2-b", "x2-c", "x2-assume", "toy-x2.complete"}
        main = [u for u in D["units"] if u.get("section", "main") == "main"]
        top = next(u for u in main if u["target"] in x2)
        self.assertIn("sub-f", top["path_line"])                                  # the line names the sub-frame
        self.assertTrue(top["path_line"].startswith("top → sub-f"))
        # a unit whose top-share goal reaches the target by an evidence edge prints ⇢
        for u in main:
            g0 = u["for"][0]["goal"] if u.get("for") else None
            if g0 and u["target"] in x2 and g0 in ("step-s", "route-x2", "toy-x.improvable", "want-w"):
                self.assertIn("⇢", u["path_line"], u)


def big_goal(nodes, private=12, root_id="big"):
    """The goal that pays for sharing inside itself: an `and` over six conjuncts sharing twelve leaves, each leaf
    under two conjuncts, three of the shared leaves given another shared leaf, and `private` own leaves per conjunct."""
    shared = [f"{root_id}-s{i}" for i in range(12)]
    conj = [f"{root_id}-c{j}" for j in range(6)]
    nodes[root_id] = ("and", "M", {"children": "[" + ", ".join(conj + [root_id + ".complete"]) + "]"}, "The large goal holds.")
    nodes[root_id + ".complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, "No conjunct beyond the six is needed for the large goal.")
    for j, c in enumerate(conj):
        mine = [shared[i] for i in range(12) if i % 6 == j or (i + 1) % 6 == j]
        own = [f"{c}-p{k}" for k in range(private)]
        nodes[c] = ("and", "S", {"children": "[" + ", ".join(mine + own + [c + ".complete"]) + "]"}, f"The conjunct {c} holds.")
        nodes[c + ".complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, f"No premise beyond the listed ones is needed for {c}.")
        for x in own:
            nodes[x] = ("leaf", "S", {"leaf_kind": "assumption"}, f"The own premise {x} holds.")
    for i, x in enumerate(shared):
        extra = {"leaf_kind": "assumption"}
        if 3 <= i < 6:
            extra["given"] = shared[i - 3]                    # three given edges inside the goal
        nodes[x] = ("leaf", "S", extra, f"The shared premise {x} holds.")
    return shared, conj


def big_goal_events(prefix, shared, conj, private):
    out = []
    n = [0]

    def add(target, rng):
        n[0] += 1
        out.append(f'{{"id": "ai-{prefix}{n[0]:04d}", "by": "@ai", {BASE}, "kind": "estimate", "target": {json.dumps(target)}, "estimate": {rng}, "gloss": "scale fixture"}}')
    for i, x in enumerate(shared):
        if 3 <= i < 6:
            add({"node": x, "field": "if-holds"}, "[0.8, 0.9]")
            add({"node": x, "field": "if-fails"}, "[0.3, 0.4]")
        else:
            add({"node": x}, "[0.6, 0.9]")
    for c in conj:
        add({"node": c + ".complete"}, "[1, 1]")
        for k in range(private):
            add({"node": f"{c}-p{k}"}, "[0.85, 0.99]")
    add({"node": "big.complete" if prefix == "b" else prefix + ".complete"}, "[1, 1]")
    return out


def scale_tree(root):
    """A generated tree: about 400 nodes in four levels of nested frames, about 60 goals, 20 shared claims each under
    three goals, 30 given edges, 10 proposed tables, 20 task leaves, and the large goal of `big_goal`."""
    adds, roots_top, events = {}, [], []
    frames = ["f1", "f2", "f3", "f4"]
    shared = [f"shc{i}" for i in range(20)]
    goals_by_frame = {"top": [f"gt{i}" for i in range(14)], **{f: [f"g{f}-{i}" for i in range(11)] for f in frames}}
    all_goals = [gid for gs in goals_by_frame.values() for gid in gs]
    sh_of = defaultdict(list)
    for k, sc in enumerate(shared):
        for j in range(3):
            sh_of[all_goals[(k * 3 + j) % len(all_goals)]].append(sc)
    n_ev = [0]

    def est(target, rng):
        n_ev[0] += 1
        events.append(f'{{"id": "ai-s{n_ev[0]:04d}", "by": "@ai", {BASE}, "kind": "estimate", "target": {json.dumps(target)}, "estimate": {rng}, "gloss": "scale fixture"}}')
    for sc in shared:
        adds[sc] = ("leaf", "S", {"leaf_kind": "assumption"}, f"The shared claim {sc} holds.")
        est({"node": sc}, "[0.5, 0.8]")
    given_left, tables, tasks = 30, 0, 0
    for gi, gid in enumerate(all_goals):
        kids = [f"{gid}-a"] + sh_of[gid]
        adds[f"{gid}-a"] = ("leaf", "S", {"leaf_kind": "step"}, f"The own step of {gid} holds.")
        if given_left > 0:
            # an own leaf given a shared claim the goal does not hold as a conjunct
            target = next(sc for sc in shared if sc not in sh_of[gid])
            adds[f"{gid}-e"] = ("leaf", "S", {"leaf_kind": "assumption", "given": target}, f"The evidence premise of {gid} holds.")
            kids.append(f"{gid}-e")
            est({"node": f"{gid}-e", "field": "if-holds"}, "[0.7, 0.9]")
            est({"node": f"{gid}-e", "field": "if-fails"}, "[0.2, 0.4]")
            given_left -= 1
        if tables < 10 and gi % 3 == 1:
            tb = f"{gid}-tb"
            adds[tb] = ("cases", "S", {"children": f"[{tb}.partition, pic-{tb}, pic-{tb}r]",
                                       "rows": f"\n  - {{picture: pic-{tb}, class: high-conflict, observable: never}}\n  - {{picture: pic-{tb}r, class: undescribed-failure, observable: never, residual: true}}"},
                        f"The table claim of {gid} holds.")
            adds[f"{tb}.partition"] = ("leaf", "S", {"leaf_kind": "partition"}, f"The pictures of {tb} are exclusive and exhaustive.")
            adds[f"pic-{tb}"] = ("leaf", "S", {"leaf_kind": "picture"}, f"A failure picture of {tb} obtains.")
            adds[f"pic-{tb}r"] = ("leaf", "S", {"leaf_kind": "picture"}, f"The claim {tb} fails for a reason not yet described.")
            est({"row": [tb, f"pic-{tb}"], "field": "w"}, "[0.2, 0.3]")
            est({"row": [tb, f"pic-{tb}"], "field": "p"}, "[0.3, 0.5]")
            est({"row": [tb, f"pic-{tb}r"], "field": "p"}, "[0.8, 0.9]")
            est({"node": f"{tb}.partition"}, "[1, 1]")
            kids.append(tb)
            tables += 1
        if tasks < 20 and gi % 3 == 2:
            alt = f"{gid}-alt"
            adds[alt] = ("or", "S", {"children": f"[{alt}-t1, {alt}-t2]"}, f"One of the two deliverables of {gid} exists.")
            for t_ in ("t1", "t2"):
                adds[f"{alt}-{t_}"] = ("leaf", "S", {"leaf_kind": "task", "who": "agent" if t_ == "t1" else "human",
                                                     "action": f'"Produce the deliverable {t_} of {gid}."'}, f"The deliverable {t_} of {gid} exists.")
                est({"node": f"{alt}-{t_}"}, "[0.5, 0.7]")
            kids.append(alt)
            tasks += 2
        adds[gid] = ("and", "S", {"children": "[" + ", ".join(kids + [gid + ".complete"]) + "]"}, f"The goal {gid} holds.")
        adds[gid + ".complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, f"No premise beyond the listed ones is needed for {gid}.")
        est({"node": f"{gid}-a"}, "[0.5, 0.9]")
        est({"node": gid + ".complete"}, "[0.8, 0.95]")
    shared_b, conj_b = big_goal(adds)
    events += big_goal_events("b", shared_b, conj_b, 12)

    def entries(gs):
        out = []
        for i, gid in enumerate(gs):
            role = "plan" if i % 2 == 0 else "shared-claim"
            out.append(f"  - {{id: {gid}, role: {role}, preset: worst-case{', success_class: utopia' if role == 'plan' else ''}}}")
        return out
    for i, f in enumerate(frames):
        inner = goals_by_frame[f] + ([frames[i + 1]] if i + 1 < len(frames) else [])
        rs = entries(goals_by_frame[f]) + ([f"  - {{id: {frames[i + 1]}, role: plan, preset: worst-case}}"] if i + 1 < len(frames) else [])
        adds[f] = ("frame", "L", {"children": "[" + ", ".join(inner) + "]", "question": f'"Does the line {f} reach its end?"', "owner": '"@h1"',
                                  "roots": "\n" + "\n".join(rs)}, f"The line {f} reaches its end through one of its plans.")
    top_entries = entries(goals_by_frame["top"]) + ["  - {id: big, role: plan, preset: worst-case, success_class: utopia}",
                                                    "  - {id: f1, role: plan, preset: worst-case}"]

    def tweak(nodes):
        nodes.update(adds)
    g.synthetic_tree(root, tweak=tweak, extra={"ai": events})
    fy = root / "graph" / "frame.yaml"
    fy.write_text(fy.read_text().replace(g._PLAN_B_ROOT, g._PLAN_B_ROOT + "\n".join(top_entries) + "\n"))
    return root


class Scale(Base):
    """the cap at scale and the performance budget."""

    def test_scale(self):
        import resource
        root = scale_tree(self.root)
        n_nodes = len(list((root / "graph" / "nodes").glob("*.md")))
        import subprocess
        t0 = time.perf_counter()
        # the scale derivation runs in a child process, so its peak memory is its own and not the high-water mark of every
        # fixture this process derived before it (the shipped graph's derivations dominate that mark since 2026-10-22)
        proc = subprocess.run([sys.executable, "-m", "checkers.graph", "--root", str(root), "--dry-run", "--today", TODAY],
                              cwd=ROOT, capture_output=True, text=True)
        elapsed = time.perf_counter() - t0
        code, out, err = proc.returncode, proc.stdout, proc.stderr
        self.assertEqual(code, 0, err)
        # ru_maxrss is kilobytes on Linux and bytes on macOS; the bound is in megabytes either way
        rss_mb = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / (1024 * 1024 if sys.platform == "darwin" else 1024)
        D = json.loads(out)
        big = [c for c in D["inference"]["largest"] if c["phi"] == "big"]
        self.assertEqual(big[0]["assignments"], 1 << 12, D["inference"]["largest"])
        on_big = [u for u in D["units"] if any(f["goal"] == "big" for f in u.get("for") or [])]
        frames_depth = max(len(p["frames"]) for N in D["nodes"].values() for p in N.get("paths") or [])
        type(self).scale_record = {"nodes": n_nodes, "goals": len(D["goals"]), "units": len(D["units"]), "units_on_big": len(on_big),
                                   "seconds": round(elapsed, 2), "peak_rss_mb": round(rss_mb, 1), "frame_depth": frames_depth,
                                   "given": sum(1 for p_ in (root / "graph" / "nodes").glob("*.md") if "\ngiven:" in p_.read_text())}
        print(f"\n  scale fixture: {type(self).scale_record}")
        self.assertGreaterEqual(n_nodes, 380)
        self.assertGreaterEqual(len(D["goals"]), 55)
        self.assertGreaterEqual(len(on_big), 150)
        self.assertGreaterEqual(frames_depth, 5)                         # top and four nested frames
        self.assertLess(elapsed, 30)
        self.assertLess(rss_mb, 500)

    def test_twelve_leaf_instance_matches_the_oracle(self):
        def tw(nodes):
            big_goal(nodes, private=0)
            nodes["plan-b"] = ("and", "M", {"children": "[big, plan-b.complete]"}, nodes["plan-b"][3])
            for x in ("shared-leaf", "or-y", "cheap-leaf", "dear-leaf", "q-leaf"):
                nodes.pop(x, None)
            nodes["plan-a"] = ("and", "M", {"children": "[cases-x, choose-c, plan-a.complete]"}, nodes["plan-a"][3])
        shared, conj = big_goal({}, private=0)          # the names only
        evs = big_goal_events("b", shared, conj, 0)
        self.tree(tweak=tw, drop={"h1-1", "h1-2", "h1-3", "h1-4", "h2-9", "h2-15"}, extra={"ai": evs})
        C, D = context(self.root)
        self.assertEqual([c["assignments"] for c in D["inference"]["largest"] if c["phi"] == "plan-b"], [1 << 12])
        Inference.check_roots(self, C, D, modes=("mid",))      # at the midpoint the oracle enumerates the 4096 worlds exactly


A2_TABLE = {
    "nodes/a2-monotone-in-resources.md": """---
id: a2-monotone-in-resources
kind: cases
children: [a2-monotone-in-resources.partition, pic-B-bounded-objective, pic-N-a2-residual]
rows:
  - {picture: pic-B-bounded-objective, class: null, observable: never}
  - {picture: pic-N-a2-residual, class: undescribed-failure, observable: never, residual: true}
attribution: reconstructed
author: "@smithy-verity"
size: S
size_reason: one paper section
version: 1
---
## Statement
The objective's attainment is monotone in resources and in the system's
continued operation.

## Source
Reconstructed from Omohundro 2008, sections 5 and 6 (self-protection;
acquiring resources and using them efficiently); the paper does not state it
in this form.

## Notes
Became a cases node when the bounded-objective picture was filed (test copy).
""",
    "nodes/a2-monotone-in-resources.partition.md": """---
id: a2-monotone-in-resources.partition
kind: leaf
leaf_kind: partition
author: "@tester"
size: S
size_reason: two rows to compare
version: 1
---
## Statement
The pictures under a2-monotone-in-resources, a bounded or satisficing
objective and the residual, are exclusive and exhaustive.

## Source
The residual row makes the list exhaustive by construction.
""",
    "nodes/pic-B-bounded-objective.md": """---
id: pic-B-bounded-objective
kind: leaf
leaf_kind: picture
author: "@tester"
size: S
size_reason: one definition and one worked example
version: 1
---
## Statement
The system's objective is bounded or satisficing: beyond a finite target
level of attainment, additional resources and additional operating time do
not raise the objective's attainment.

## Source
Taylor 2016, Quantilizers, section 1; the reading as a counterexample to
monotone attainment is the filing contributor's.
""",
    "nodes/pic-N-a2-residual.md": """---
id: pic-N-a2-residual
kind: leaf
leaf_kind: picture
author: "@tester"
size: S
size_reason: every objective outside the bounded picture
version: 1
---
## Statement
The system's objective is not bounded or satisficing: it is an unbounded
maximization objective or an objective of a kind not yet described.

## Source
The residual of the table; no source.
""",
    "events/tester.jsonl": "\n".join([
        # a leaf range given before the leaf became this table: stale, kept as a suggestion under the residual row
        '{"id": "tester-000", "by": "@tester", "date": "2026-10-01", "rule": "2026-10-02.1", "via": "chat", "kind": "estimate", "target": {"node": "a2-monotone-in-resources"}, "version": 1, "estimate": [0.9, 1], "reason": "free disposal: a maximizer declines resources it has no use for", "gloss": "test copy; given on the leaf"}',
        '{"id": "tester-001", "by": "@tester", "date": "2026-10-02", "rule": "2026-10-02.1", "via": "chat", "kind": "estimate", "target": {"row": ["a2-monotone-in-resources", "pic-B-bounded-objective"], "field": "w"}, "version": 1, "estimate": [0.2, 0.4], "reason": "bounded and satisficing objectives are a minority of proposed designs", "gloss": "test copy"}',
        '{"id": "tester-002", "by": "@tester", "date": "2026-10-02", "rule": "2026-10-02.1", "via": "chat", "kind": "estimate", "target": {"row": ["a2-monotone-in-resources", "pic-B-bounded-objective"], "field": "p"}, "version": 1, "estimate": [0.1, 0.3], "reason": "once the target level is reached, more resources do not raise attainment", "gloss": "test copy; below the bar with a reason"}',
        '{"id": "tester-003", "by": "@tester", "date": "2026-10-02", "rule": "2026-10-02.1", "via": "chat", "kind": "estimate", "target": {"row": ["a2-monotone-in-resources", "pic-N-a2-residual"], "field": "p"}, "version": 1, "estimate": [0.9, 1], "reason": "for an unbounded maximizer free disposal makes attainment weakly monotone", "gloss": "test copy"}',
        '{"id": "tester-004", "by": "@tester", "date": "2026-10-02", "rule": "2026-10-02.1", "via": "chat", "kind": "estimate", "target": {"node": "a2-monotone-in-resources.partition"}, "version": 1, "estimate": [1, 1], "reason": "a residual row is present", "gloss": "test copy; a point judgment by construction"}',
    ]) + "\n",
}


CLAIMS_SCHEMA = """# Claims registry (test)

### toy.collapse

```json
{"class": "lean-proved", "statement_of_record": {"kind": "lean", "declaration": "Workspace.Toy.toy_collapse"}}
```

### toy.other

```json
{"class": "conjectured", "statement_of_record": {"kind": "lean", "declaration": "Workspace.Toy.Other.other_claim"}}
```
"""


class FixStage(Base):
    """The 2026-10-05b fix stage (graph/DESIGN-LOG.md)."""

    def test_scope_reaches_goals_reading_the_implication(self):
        # F2: step-s and route-x2 read toy-x2 only as toy-x2@valid; --scope toy-x2 counts them in scope, and informs too
        self.tree(tweak=right_reasons, extra={"ai": rr_events(), "h1": RR_WANT})
        self.edit("graph/frame.yaml", *RR_ROOTS)
        S = self.derived_dry("--scope", "toy-x2")
        self.assertTrue({"step-s", "route-x2", "toy-x2"} <= set(S["ranking"]["goals"]), S["ranking"]["goals"])
        D = self.derived()
        self.assertIn("step-s", D["nodes"]["toy-x2"]["informs"])

    def test_given_to_an_unjudged_parent_blanks_nothing_under_the_fallback(self):
        # F3: a leaf with only a plain range falls back on both sides, so its unjudged given parent cannot move it
        def tw(nodes):
            nodes.update(Y_LEAF)
            k, sz, extra, st = nodes["cheap-leaf"]
            nodes["cheap-leaf"] = (k, sz, dict(extra, given="y-leaf"), st)
        self.tree(tweak=tw)
        D = self.derived()
        self.assertTrue(D["roots"]["plan-b"]["Pr_defined"], D["roots"]["plan-b"]["nobelief"])
        self.assertNotIn("y-leaf", D["roots"]["plan-b"]["nobelief"])
        # once the leaf carries a conditional of its own, the parent's missing belief blanks the root
        self.append("graph/events/h1.jsonl", ev(70, {"node": "cheap-leaf", "field": "if-holds"}, "[0.9, 0.95]") + "\n")
        D = self.derived()
        self.assertIn("y-leaf", D["roots"]["plan-b"]["nobelief"])

    def test_untagged_or_is_a_tag_item_and_improvement_ors_need_none(self):
        # F5: no classify event can set an or's tag, so the item says to set it in the file; an improvement or needs none
        self.tree(tweak=improvable(), extra={"h1": ROUTE_EVENTS})
        self.edit("graph/frame.yaml", *IMPROVABLE_ROOT)
        D = self.derived()
        items = [(u["kind"], u["target"]) for u in D["units_unranked"]]
        self.assertIn(("tag", "or-y"), items)
        self.assertNotIn(("classify", "or-y"), items)
        self.assertFalse([i for i in items if i[1] == "res.improvable" and i[0] in ("tag", "classify")])

    def test_private_only_source_signal(self):
        # a vet's trace opens the Source; a Source naming only private material says so on the line
        self.tree()
        self.edit("graph/nodes/dear-leaf.md", "## Source\nillustrative", "## Source\nresearch/notes/x.md (private, outside this repository)")
        D = self.derived()
        u = next(u for u in D["units"] if u["target"] == "dear-leaf" and u["kind"] == "vet")
        self.assertIn("private source only", u["signals"])
        self.assertTrue(D["nodes"]["dear-leaf"]["source_private_only"])
        # a public path that exists in the tree clears it
        self.edit("graph/nodes/dear-leaf.md", "research/notes/x.md (private", "graph/policy.yaml and research/notes/x.md (private")
        D = self.derived()
        self.assertFalse(D["nodes"]["dear-leaf"]["source_private_only"])

    def test_private_citations_warn(self):
        # 2026-10-20: the public map cites only what a public reader can open; a Source naming private material and a
        # private work pointer each warn (refusals once the staged nodes are clean)
        self.tree()
        self.assertNotIn("WARN", run(self.root)[2])
        self.edit("graph/nodes/dear-leaf.md", "## Source\nillustrative", "## Source\nresearch/notes/x.md (private, outside this repository)")
        self.assertIn("WARN graph/nodes/dear-leaf.md: the Source names private material", run(self.root)[2])
        self.edit("graph/nodes/dear-leaf.md", "research/notes/x.md (private, outside this repository)", "illustrative")
        self.edit("graph/nodes/dear-leaf.md", "leaf_kind: assumption\n", "leaf_kind: assumption\nwork: [{kind: private, ref: notes/x.md}]\n")
        self.assertIn("WARN graph/nodes/dear-leaf.md: work pointer kind private", run(self.root)[2])

    def test_registry_schema_and_policy_key(self):
        # newcomer review: the registries are a derivation input in policy.yaml, read in the repository's CLAIMS.md schema
        reg = pathlib.Path(self.tmp) / "CLAIMS.md"
        reg.write_text(CLAIMS_SCHEMA)
        r = g._load_registry(reg)
        self.assertEqual(r["toy.collapse"], "lean-proved")
        self.assertEqual(r["Workspace.Toy.toy_collapse"], "lean-proved")
        self.assertEqual(r["toy_collapse"], "lean-proved")                   # the last component, unique
        self.assertEqual(r["other_claim"], "conjectured")
        self.tree(tweak=right_reasons, extra={"ai": rr_events(), "h1": RR_WANT})
        self.edit("graph/frame.yaml", *RR_ROOTS)
        D = self.derived()
        self.assertIn("registry unchecked", D["nodes"]["toy-x.record"]["flags"])
        (self.root / "projects" / "toy").mkdir(parents=True)
        (self.root / "projects" / "toy" / "CLAIMS.md").write_text(CLAIMS_SCHEMA)
        self.edit("graph/policy.yaml", "also_for_share: 0.2\n", "also_for_share: 0.2\nregistries: [projects/toy/CLAIMS.md]\n")
        D = self.derived()
        self.assertNotIn("registry unchecked", D["nodes"]["toy-x.record"]["flags"])
        self.assertGreaterEqual(D["nodes"]["toy-x.record"]["V"]["valid"], 4)
        snap = (self.root / "graph" / "view.md").read_text()
        # an extra --registry is a personal input: the committed files stay as the policy's registries make them
        other = pathlib.Path(self.tmp) / "OTHER.md"
        other.write_text(CLAIMS_SCHEMA.replace("lean-proved", "conjectured"))
        code, out, err = run(self.root, "--registry", str(other), "--print")
        self.assertEqual(code, 0, err)
        self.assertEqual((self.root / "graph" / "view.md").read_text(), snap)

    def test_first_clause_respects_brackets(self):
        self.assertEqual(g.first_clause("The geometric account of DDB §4 (cuts, frames), extended to logical inductors, holds."),
                         "The geometric account of DDB §4 (cuts, frames)")
        self.assertEqual(g.first_clause("For [0, 1], the bound holds for every trader."),
                         "For [0, 1], the bound holds for every trader.")      # a clause under five words gives way to the sentence

    def test_pooled_priority_lines_group_per_owner(self):
        # newcomer review: the pooled file prints one line per owner; --as that owner lists each want with its source
        self.tree(tweak=g._with_want)
        self.edit("graph/" + g._want_root()[0], *g._want_root()[1:])
        self.derived()
        text = (self.root / "graph" / "tasks.md").read_text()
        unr = text.split("## Judgment and structure units (unranked)")[1]
        self.assertIn("- priority — 1 want of @h1 await a priority word", unr)
        self.assertNotIn("- priority want-x", unr)
        code, out, err = run(self.root, "--as", "@h1", "--print")
        self.assertEqual(code, 0, err)
        mine = out.split("## Judgment and structure units (unranked)")[1]
        self.assertIn("- priority want-x", mine)
        self.assertIn("source: illustrative", mine)

    def test_research_section_and_rank(self):
        self.tree(tweak=improvable(), extra={"h1": ROUTE_EVENTS})
        self.edit("graph/frame.yaml", *IMPROVABLE_ROOT)
        D = self.derived()
        main = [u for u in D["units"] if u.get("section", "main") == "main"]
        self.assertEqual([u["rank"] for u in main], list(range(1, len(main) + 1)))
        text = (self.root / "graph" / "tasks.md").read_text()
        sec = text.split("## Research and whole-argument units")[1].split("## Ranked units")[0]
        res = [u for u in main if u["kind"] in g.RESEARCH_KINDS]
        self.assertTrue(res)
        self.assertIn(f"{res[0]['rank']}. {res[0]['kind']} {res[0]['target']} (", sec)

    def test_frame_not_opened_keeps_its_roots_out_of_the_list(self):
        # the roots of a frame that is not opened rank only under --scope
        def tw(nodes):
            nodes["closed-f"] = ("frame", "L", {"children": "[cl-and]", "question": '"Is the closed line worth opening?"', "owner": '"@h1"',
                                                "opened": "false", "roots": "\n  - {id: cl-and, role: shared-claim, preset: worst-case}"},
                                 "The closed line is not opened for now.")
            nodes["cl-and"] = ("and", "S", {"children": "[cl-a, cl-b, cl-and.complete]"}, "The closed line's argument holds.")
            nodes["cl-a"] = ("leaf", "S", {"leaf_kind": "assumption"}, "The closed line's first premise holds.")
            nodes["cl-b"] = ("leaf", "S", {"leaf_kind": "assumption"}, "The closed line's second premise holds.")
            nodes["cl-and.complete"] = ("leaf", "S", {"leaf_kind": "completeness"}, "No premise beyond the listed two is needed.")
        evs = [ai_est(70, {"node": "cl-a"}, "[0.5, 0.7]"), ai_est(71, {"node": "cl-b"}, "[0.5, 0.7]"), ai_est(72, {"node": "cl-and.complete"}, "[0.8, 0.9]")]
        self.tree(tweak=tw, extra={"ai": evs})
        self.edit("graph/frame.yaml", g._PLAN_B_ROOT, g._PLAN_B_ROOT + "  - {id: closed-f, role: plan, preset: worst-case}\n")
        D = self.derived()
        self.assertNotIn("cl-and", D["ranking"]["goals"])
        self.assertFalse([u for u in D["units"] if u["target"] in ("cl-a", "cl-b", "cl-and")])
        S = self.derived_dry("--scope", "closed-f")
        self.assertIn("cl-and", S["ranking"]["goals"])

    def test_reexamine_offered_where_a_leaf_has_no_belief(self):
        # the whole-argument read is offered on a goal with a gestalt even where a leaf has no number
        self.tree(tweak=right_reasons, extra={"ai": rr_events(), "h1": RR_WANT}, drop=set())
        self.edit("graph/frame.yaml", *RR_ROOTS)
        self.append("graph/events/ai.jsonl", ai_gestalt(60, {"node": "toy-x"}, "[0.3, 0.3]") + "\n")
        led = (self.root / "graph" / "events" / "ai.jsonl")
        led.write_text("\n".join(l for l in led.read_text().splitlines() if '"toy-x.h"' not in l) + "\n")
        D = self.derived()
        u = next((u for u in D["units"] if u["kind"] == "re-examine" and u["target"] == "toy-x"), None)
        self.assertIsNotNone(u, [(x["kind"], x["target"]) for x in D["units"]])
        self.assertTrue(any(s_.startswith("no belief on toy-x.h") for s_ in u["signals"]), u["signals"])

    def test_commit_line_names_its_rank(self):
        self.tree()
        D = self.derived()
        c = D["lines"]["commit"]
        if c.startswith("research first"):
            self.assertRegex(c, r"\(ranked unit \d+\)|\(Agent work\)")
        self.assertIn("act", D["lines"])


@unittest.skipUnless((ROOT / "graph" / "frame.yaml").is_file(), "no fixture under graph/ yet")
class Fixtures(unittest.TestCase):
    """Reads whatever `graph/` contains, on a scratch copy; records the ranking in FIXTURE-NOTES.md."""

    @classmethod
    def copy_fixture(cls, name):
        root = pathlib.Path(cls.tmp) / name
        root.mkdir()
        shutil.copytree(ROOT / "graph", root / "graph")
        if (ROOT / "chats").is_dir():
            shutil.copytree(ROOT / "chats", root / "chats")
        # work pointers name PRIORITIES.md items and round directories: the copy carries the file and stubs of the rounds
        if (ROOT / "PRIORITIES.md").is_file():
            shutil.copy(ROOT / "PRIORITIES.md", root / "PRIORITIES.md")
        for reg in ROOT.glob("projects/*/CLAIMS.md"):                  # the claims registries policy.yaml lists
            (root / reg.relative_to(ROOT)).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(reg, root / reg.relative_to(ROOT))
        # narratives name wiki pages, decision pointers name DECISIONS.md anchors, round and foundation pointers read the
        # state, and the item nodes render PRIORITIES.md from the sections file (2026-10-22)
        if (ROOT / "wiki").is_dir():
            shutil.copytree(ROOT / "wiki", root / "wiki")
        for rel in ("DECISIONS.md", "state/rounds.json", "state/foundations.json", "state/priorities_sections.md"):
            if (ROOT / rel).is_file():
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(ROOT / rel, root / rel)
        for f in (ROOT / "graph" / "nodes").glob("*.md"):
            n = g.parse_node_text(f.read_text(), f.name)
            for w in n.get("work") or []:
                if isinstance(w, dict) and w.get("kind") == "round" and (ROOT / str(w.get("ref"))).is_dir():
                    (root / str(w["ref"])).mkdir(parents=True, exist_ok=True)
        for gen in g.GENERATED:
            p = root / "graph" / gen
            if p.is_file() and (gen in g.UNCOMMITTED or not g.hash_ok(gen, p.read_text())):
                p.unlink()          # a derived.json a prior run left behind is no fixture: a test that needs one writes it (G1)
        return root

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp()
        cls.root = cls.copy_fixture("fx")
        code, out, err = run(cls.root)
        assert code == 0, err
        cls.D = json.loads((cls.root / "graph" / "derived.json").read_text())
        cls.why = run(cls.root, "--why")[1]
        notes = [f"# Fixture notes (written by tests/test_graph.py on {TODAY}; the ranking as derived, for the record)", "",
                 f"- {cls.D['lines']['commit']}", f"- {cls.D['lines']['regime']}",
                 "- inference: " + ("; ".join(f"[{c['phi']}: cutset {', '.join(c['cutset'])}, {c['assignments']} assignments]"
                                              for c in cls.D["inference"]["largest"]) or "every formula a tree") + f" (cap {cls.D['inference']['cap']} per formula)", ""]
        notes += [f"{i}. {u['kind']} {u['target']} ({u['size']}, ~{u['minutes']} min; bits {u['bits'] if u['bits'] is None else round(u['bits'], 3)}; D {u['D']})"
                  for i, u in enumerate(cls.D["units"], 1)]
        notes += [""] + [f"- unranked: {u['kind']} {u['target']} (load {len(u['load'])}{'; ' + u['note'] if u.get('note') else ''})" for u in cls.D["units_unranked"]]
        notes += [""] + [f"- {r}{' (in ' + R['frame'] + ')' if R['frame'] else ''}: {R['status']}; Pr {R['Pr']['mid'] if R['Pr_defined'] else 'no belief'}; "
                         f"value {(R['value'] or {}).get('mid') if R['value_defined'] or R.get('subframe') else 'no belief'}; gestalt {(R['gestalt'] or {}).get('mid')}; cost {R['cost']}"
                         + (f"; programme over {', '.join(R['subframe']['roots'])}" if R.get("subframe") else "")
                         for r, R in cls.D["roots"].items()]
        notes += [""] + [f"- valuation {x} ({V['role']}): {V['value']['mid'] if V['defined'] else 'no belief'}{' (provisional)' if V['provisional'] else ''}"
                         for x, V in cls.D["valuations"].items()]
        cls.notes = notes

    @classmethod
    def tearDownClass(cls):
        (pathlib.Path(os.environ["GRAPH_FIXTURE_NOTES"]) if os.environ.get("GRAPH_FIXTURE_NOTES") else pathlib.Path(tempfile.gettempdir()) / "graph-fixture-notes.md").write_text("\n".join(cls.notes) + "\n")
        shutil.rmtree(cls.tmp)

    def test_deference_programme_is_a_sub_frame(self):
        D = self.D
        prog = "deference-toward-bounded-agents"
        if prog not in D["roots"]:
            self.skipTest("fixture 1 not present")
        P = D["roots"][prog]
        # the sub-frame sits at the top frame as landed, or under the trust line the 2026-10-05b round moves it to
        self.assertEqual((D["nodes"][prog]["kind"], P["role"]), ("frame", "plan"))
        self.assertIn(P["frame"], ("legitimacy", "deference-and-trust"))   # a shared root of both lines; its home is the first in the frame tree's order
        landed = {"tt-mart-repair-via-bounds-transfer", "step-asymptotic-to-finite-time", "step-legitimacy-conditioned-trust"}
        steps = set(P["subframe"]["steps"])
        self.assertTrue(steps and steps <= landed, steps)                      # the round re-roles the repair lemma as a shared claim
        self.assertTrue(landed | {"policy-level-total-trust"} <= set(P["subframe"]["roots"]))
        for s in landed | {"policy-level-total-trust"}:
            self.assertEqual(D["roots"][s]["frame"], prog)                     # the steps are roots of the sub-frame
        self.assertEqual(D["roots"]["policy-level-total-trust"]["role"], "shared-claim")
        self.assertEqual(D["roots"]["policy-level-total-trust"]["cost"], "inf")  # a question: infinite cost, no vet unit
        # a question: research units only (improve, and do where the 2026-10-05b round gave it an action), never a check
        kinds = {u["kind"] for u in D["units"] if u["target"] == "policy-level-total-trust" and u["kind"] != "gestalt"}
        self.assertTrue(kinds and kinds <= {"improve", "do"}, kinds)
        # the AI fill (ruling 34) gives every step a value, so the programme has one and a leading step
        self.assertIsNotNone(P["option_value"])
        self.assertIn(P["subframe"]["leading_step"], steps)
        self.assertTrue(P.get("ai_only"), "the programme's value rests on AI numbers only and must say so")
        self.assertEqual(P["subframe"]["outside_option"], "default-trajectory")
        self.assertEqual(D["roots"]["li-deference-collapse"]["frame"], "deference-and-trust")   # a shared claim, not a step
        u = next(u for u in D["units"] if u["kind"] in ("vet", "map-read", "trace") and u["target"] == P["subframe"]["leading_step"])
        self.assertIn(prog, u["bears_on"])                                      # a step's unit ranks in the parent's list
        view = (self.root / "graph" / "view.md").read_text()
        self.assertIn(f"## Sub-frame {prog} (in ", view)
        self.assertIn("leading step: ", view)
        self.assertIn("rests on AI numbers", view)

    def test_starting_graph_carries_structure_and_the_two_rulings_only(self):
        D = self.D
        # human events: the maintainer's two rulings only; every other counted event is the AI fill
        self.assertEqual([e for e in D["events"]["counted"] if not e.startswith("smithy-verity-")],
                         ["anson-001", "anson-002"])
        self.assertTrue([e for e in D["events"]["counted"] if e.startswith("smithy-verity-")])
        # nothing is withdrawn; an AI number goes stale only where the 2026-10-05b round revised a node (a new version, or a
        # leaf that became a table), never for another reason
        self.assertEqual(D["events"]["withdrawn"], [])
        for e, why in D["events"]["stale_reasons"].items():
            self.assertTrue(why == "leaf became a table" or why.startswith("given against version"), (e, why))
        pol = g.parse_flat_yaml((self.root / "graph" / "policy.yaml").read_text())
        self.assertEqual(set(pol["handles"]), {"@anson", "@abram", "@smithy-verity", "@smithy-verity-opus55"})
        self.assertNotIn("illustrative", (self.root / "graph" / "policy.yaml").read_text())
        for r, R in D["roots"].items():
            self.assertEqual(R["status"], "open", r)                           # no human judgment yet, so nothing concedes
            if R["gestalt"] is not None:                                        # every number is the AI's, at J 0 (ruling 34)
                self.assertEqual((R["gestalt"]["J"], R["gestalt"].get("generated")), (0, True), r)
        for x in ("tt-implies-mart-gap-bets", "a1-fixed-objective-maximizer"):
            N = D["nodes"][x]                                                   # tables are proposed until a human admits a row
            self.assertFalse(any(N["admitted"].values()), x)
            self.assertIn("under attack", N["flags"])
            self.assertIn("no belief", N["flags"])
        self.assertTrue({u["target"].split("/")[0] for u in D["units_unranked"] if u["kind"] == "admit"}
                        >= {"tt-implies-mart-gap-bets", "a1-fixed-objective-maximizer"})
        # after the AI fill a gestalt unit is ranked only on a goal left without numbers: a goal whose readings are a
        # person's choice (Decided 2026-10-20), or a root the map-as-canonical round filed as structure alone (2026-10-22:
        # every formal result and docket is at level 0 with no judgment until someone gives one)
        judged = {e["target"].get("node") for e in (json.loads(l) for p in (self.root / "graph" / "events").glob("*.jsonl")
                                                   for l in p.read_text().splitlines() if l.strip()) if e["kind"] in ("estimate", "gestalt")}
        unjudged = {g for g in D["ranking"]["goals"] if g not in judged} | UNJUDGED_BY_POLICY
        # a formal result whose hypotheses are unread is structure alone too (2026-10-23), the claims merged under F5 included
        unjudged |= {x for x, N in D["nodes"].items() if "hypotheses unread" in N["flags"]}
        self.assertEqual({u["target"] for u in D["units"] if u["kind"] == "gestalt"} - unjudged, set())
        first = next(u for u in D["units"] if u["target"] not in unjudged)
        self.assertNotIn(first["kind"], ("gestalt", "revive"), first)
        self.assertNotIn("suspended", D["lines"]["commit"])
        self.assertFalse([u for u in D["units"] if u["kind"] == "revive"])
        self.assertIn("no belief on:", self.why)

    def test_outside_option_and_residual_are_valuation_nodes(self):
        D = self.D
        V = D["valuations"]
        self.assertEqual(set(V), {"default-trajectory", "undescribed-failure"})
        self.assertEqual((Q(V["default-trajectory"]["value"]["mid"]), V["default-trajectory"]["role"], V["default-trajectory"]["provisional"]), (Q(0), "outside option", True))
        self.assertEqual((Q(V["undescribed-failure"]["value"]["mid"]), V["undescribed-failure"]["role"], V["undescribed-failure"]["provisional"]), (Q(-1, 4), "undescribed failure", True))
        self.assertEqual((Q(D["act"]["outside_value"]), D["act"]["outside_placed"], D["act"]["outside_option"]), (Q(0), True, "default-trajectory"))
        for x, n in (("default-trajectory", 5), ("undescribed-failure", 4)):
            N = D["nodes"][x]
            self.assertTrue(all(N["admitted"].values()))                        # the ruling admits the rows it weights
            self.assertEqual({Q(r["w"][0]) for r in N["rows"].values()}, {Q(1, n)})
            self.assertEqual({Q(r["p"][0]) for r in N["rows"].values()}, {Q(1)})
            self.assertIn("provisional", N["flags"])
            self.assertFalse([u for u in D["units"] if u["target"] == x])     # a valuation node is in no proof set
        self.assertIn("from default-trajectory (provisional)", self.why)
        self.assertIn("## Valuation nodes", (self.root / "graph" / "view.md").read_text())

    def test_instrumental_convergence_cluster(self):
        D = self.D
        if "instrumental-convergence" not in D["roots"]:
            self.skipTest("fixture 2 not present")
        N = D["nodes"]["a1-fixed-objective-maximizer"]
        self.assertEqual(N["kind"], "cases")
        self.assertTrue(any(p.startswith("pic-T") for p in N["admitted"]))
        self.assertEqual(D["nodes"]["ic-informal"]["status"], "open")
        # a1 carries the anti-naturality root; the or root instrumental-convergence keeps its theorem route when a1 falls
        self.assertIn("corrigibility-anti-natural", D["nodes"]["a1-fixed-objective-maximizer"]["load"])
        for r in ("instrumental-convergence", "corrigibility-anti-natural"):
            # both roots carry an AI gestalt and a derived probability, so no gestalt unit is ranked (Default of 2026-10-02)
            self.assertNotIn(("gestalt", r), [(u["kind"], u["target"]) for u in D["units"]])
            self.assertTrue(D["roots"][r].get("ai_only"))
        code, out, err = run(self.root, "--scope", "instrumental-convergence", "--dry-run")
        self.assertEqual(code, 0, err)
        S = json.loads(out)                                            # stdout is the JSON alone
        self.assertIn("instrumental-convergence", S["ranking"]["goals"])
        if not any(R["role"] == "plan" and "instrumental-convergence" in (S["nodes"].get("instrumental-convergence") or {}).get("informs", [])
                   for R in S["roots"].values()) and S["ranking"]["goals"] == ["instrumental-convergence"]:
            self.assertEqual(S["lines"]["commit"], "suspended: no plan in scope")
            self.assertIn("no plan in scope;", S["lines"]["regime"])
            self.assertTrue(all(u["D"] is None for u in S["units"]))

    def test_plain_run_is_clean_and_idempotent(self):
        code, out, err = run(self.root)
        self.assertEqual((code, out), (0, ""))
        lines = [l for l in err.strip().splitlines() if l]
        # one OK line; the one WARN the shipped graph carries is the summary of decision anchors no node points at (2026-10-22)
        # … and the DIGEST line names what the digest compared with (F3, 2026-10-23)
        self.assertEqual([l for l in lines if not l.startswith(("WARN DECISIONS.md: ", "DIGEST "))], [lines[-1]], err)
        self.assertTrue(any(l.startswith("DIGEST ") for l in lines), err)
        self.assertTrue(lines[-1].startswith("OK "))
        snap = {n: (self.root / "graph" / n).read_text() for n in g.GENERATED}
        code, out, err = run(self.root, "--why", "--as", "@anson")
        self.assertEqual(code, 0, err)
        for n in g.GENERATED:
            self.assertEqual((self.root / "graph" / n).read_text(), snap[n], n)

    def test_index_schema_three_on_the_fixture(self):
        """ruling F2 (2026-10-23): the index inverts the registry join; every registry-built result points at its item, and
        every record the round filed from a signature says its hypotheses are unread (ruling F1); ruling G3 (the second
        follow-up): a result bears on an item (`items[].bearing`, `formal_result.bears_on`) and closes nothing."""
        idx = json.loads((self.root / "graph" / "index.json").read_text())
        self.assertEqual(idx["schema"], "graph-index/3")
        formal = {x: N["formal_result"] for x, N in idx["nodes"].items() if "formal_result" in N}
        self.assertGreater(len(formal), 200)
        for item, rec in idx["items"].items():
            self.assertEqual(set(rec), {"node", "bearing"})
            for r in rec["bearing"]:
                self.assertIn(item, formal[r]["bears_on"])
            # bearing changes no status: the item node's item_status is the file's word, whatever bears on it
            self.assertIn(idx["nodes"][rec["node"]]["fields"].get("item_status"), ("open", "closed"))
        for x, F in formal.items():
            if idx["nodes"][x]["fields"].get("superseded_by"):
                continue                                                # a deprecated alias (F5) bears on nothing twice
            for a in F["bears_on"]:
                self.assertIn(x, idx["items"][a]["bearing"])
            if F["registry_id"]:
                self.assertEqual(idx["claims"][F["registry_id"]], x)
        unread = [x for x, F in formal.items() if F["hypotheses"] == "unread"]
        self.assertGreater(len(unread), 150)
        self.assertTrue(all(len(idx["nodes"][x]["children"]) == 3 for x in unread), "an unread result is record, bridge and completeness")
        self.assertIn("hypotheses unread", self.D["nodes"][unread[0]]["flags"])
        # the render shows the registered answers beside the item (one line under the heading)
        text = (self.root / "PRIORITIES.md").read_text()
        self.assertIn("*Registered results bearing on this item:* ", text)
        self.assertNotIn("Registered answers", text)
        # ruling F4: the two pre-existing frames are retired aliases, their roots moved; ruling F5: a merged claim resolves its registry id
        self.assertNotIn("normativity-line", idx["nodes"]["normativity"]["children"])
        self.assertEqual(idx["nodes"]["normativity-line"]["fields"].get("superseded_by"), "normativity")
        self.assertEqual(idx["nodes"]["normativity-line"]["children"], [])
        for rid, x in idx["claims"].items():
            self.assertEqual(idx["nodes"][x]["formal_result"]["registry_id"], rid)

    def test_hoist_rule_on_the_fixture(self):
        """every ranked line of the shipped fixture rests on AI numbers only, so the tag is said once in the header;
        one human judgment brings it back to the lines that still rest on AI only."""
        text = (self.root / "graph" / "tasks.md").read_text()
        ranked = text.split("## Ranked units")[1].split("## Agent work")[0]
        lines = [l for l in ranked.splitlines() if l[:1].isdigit()]
        self.assertTrue(lines)
        # a gestalt unit on a goal left without AI numbers (UNJUDGED_BY_POLICY), or a unit on a want (a want carries no AI
        # number, 2026-10-20), rests on no AI number, so nothing is hoisted and every other line says the tag itself
        wants = {x for x, N in self.D["nodes"].items() if N.get("want")}
        # a gestalt unit on a goal without numbers rests on no AI number either (the formal results filed as structure alone),
        # nor does a spell-out on an unspelled frame (an agent's draft read at a stand-in 1/2; in the printed forty since the
        # held results left the goal set, 2026-10-23)
        bare = [l for l in lines if any(f"gestalt {x} (" in l for x in UNJUDGED_BY_POLICY)
                or any(f" {x} (" in l for x in wants) or l.split(". ", 1)[1].startswith(("gestalt ", "spell-out "))]
        if bare:
            self.assertNotIn("Hoisted from every line:", ranked)
            self.assertFalse([l for l in lines if l not in bare and "vet this AI number" not in l])
        else:
            self.assertFalse([l for l in lines if "vet this AI number" in l])
            self.assertIn("Hoisted from every line:", ranked)
            self.assertIn("*vet this AI number*", ranked)
        root = self.copy_fixture("fx-human")
        pol = root / "graph" / "policy.yaml"
        pol.write_text(pol.read_text().replace('  "@smithy-verity":', '  "@tester": {kind: human, github: "tester-example"}\n  "@smithy-verity":'))
        # a leaf with no AI gestalt of its own, checked by a ranked line of the main list (not Agent work)
        top = next(u["target"] for u in self.D["units"] if u.get("section", "main") == "main" and u["kind"] in ("vet", "map-read", "trace")
                   and u["target"] not in self.D["roots"] and self.D["nodes"][u["target"]]["kind"] == "leaf"
                   and not any(f.startswith("given") for f in self.D["nodes"][u["target"]]["flags"]))   # a plain range supersedes it
        (root / "graph" / "events" / "tester.jsonl").write_text(
            f'{{"id": "tester-001", "by": "@tester", "date": "2026-10-05", "rule": "2026-10-02.1", "via": "chat", "version": {self.D["nodes"][top]["version"]}, "kind": "estimate", '
            f'"target": {{"node": "{top}"}}, "estimate": [0.6, 0.8], "reason": "test copy"}}\n')
        # the human estimate can move its unit out of the printed forty, so the check reads every ranked line (--all)
        code, out, err = run(root, "--all", "--print")
        self.assertEqual(code, 0, err)
        ranked = out.split("## Ranked units")[1].split("## Agent work")[0]
        lines = [l for l in ranked.splitlines() if l[:1].isdigit()]
        self.assertNotIn("*vet this AI number*", ranked.split("\n1. ")[0])
        self.assertTrue([l for l in lines if "vet this AI number" in l])
        self.assertFalse([l for l in lines if f" {top} (" in l and "vet this AI number" in l])

    def test_table_filed_on_the_fixture_passes(self):
        """The review's case: a two-row table on a2 (plus one new contributor) files without touching the cap."""
        D0 = self.D
        if "a2-monotone-in-resources" not in D0["nodes"] or D0["nodes"]["a2-monotone-in-resources"]["kind"] != "leaf":
            self.skipTest("a2 is not a leaf in this fixture")
        root = self.copy_fixture("fx-table")
        code, out, err = run(root)                                     # the fixture's own first derivation, the digest's previous (G1)
        self.assertEqual(code, 0, err)
        self.assertTrue((root / "graph" / "derived.json").is_file())
        for rel, text in A2_TABLE.items():
            (root / "graph" / rel).write_text(text)
        pol = root / "graph" / "policy.yaml"
        pol.write_text(pol.read_text().replace('  "@smithy-verity":', '  "@tester": {kind: human, github: "tester-example"}\n  "@smithy-verity":'))
        t0 = time.perf_counter()
        code, out, err = run(root)
        elapsed = time.perf_counter() - t0
        self.assertEqual(code, 0, err)
        D = json.loads((root / "graph" / "derived.json").read_text())
        comps = D["inference"]["largest"]
        self.assertTrue(all(c["assignments"] <= D["inference"]["cap"] for c in comps))
        self.assertEqual(D["nodes"]["a2-monotone-in-resources"]["status"], "conceded")
        self.assertEqual(D["nodes"]["a2-monotone-in-resources"]["diagnosis"], "pic-B-bounded-objective")
        self.assertEqual(D["nodes"]["ic-informal"]["status"], "conceded")             # the informal route falls with a2
        self.assertIn("stale: leaf became a table", D["nodes"]["a2-monotone-in-resources"]["flags"])
        stale = [e for e, why in D["events"]["stale_reasons"].items() if why == "leaf became a table"]
        self.assertIn("tester-000", stale)                                     # the AI's earlier estimate on a2 goes stale too
        self.assertTrue(all(D["events"]["targets"][e] == "a2-monotone-in-resources" for e in stale) if "targets" in D["events"] else True)
        self.assertTrue(D["digest"]["compared_with"].startswith("graph/derived.json on disk"), D["digest"]["compared_with"])
        self.assertIn("a2-monotone-in-resources: open → conceded", D["digest"]["statuses_flipped"])
        self.assertEqual(D["events"]["counted"][:2], ["anson-001", "anson-002"])
        type(self).notes += ["", "## The table case (a two-row table on a2, filed by a new contributor on a scratch copy)",
                             f"- passes in {elapsed:.2f} s; largest cutsets: " + ("; ".join(f"[{c['phi']}: {c['assignments']} assignments]" for c in comps) or "none"),
                             f"- a2: {D['nodes']['a2-monotone-in-resources']['status']} by {D['nodes']['a2-monotone-in-resources']['diagnosis']}; ic-informal: {D['nodes']['ic-informal']['status']}; "
                             f"instrumental-convergence: {D['roots']['instrumental-convergence']['status']} ({D['roots']['instrumental-convergence']['diagnosis']})",
                             f"- stale leaf range(s) kept as suggestions: {', '.join(stale)}"]


if __name__ == "__main__":
    unittest.main(verbosity=2)
