"""Tests for `checkers.graph`: one refusal test per rule of the specification's §3 (rules 1–13), the
synthetic graph's derivations (§7), the streams and flag-independence of the generated files, and the
fixtures under `graph/` when they exist (including the filing of a new table on the shipped fixture).

Run from the tree's root: `python3 -m unittest discover -s tests` or `python3 tests/test_graph.py`.
The checker runs on one tree at a time; nothing here is parallel.
"""
from __future__ import annotations

import json
import os
import pathlib
import shutil
import sys
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
        self.assertIn("vet cases-x (S, ~33 min) — bears on plan-a — vet this AI number", (self.root / "graph" / "tasks.md").read_text())
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

    def test_rule13_component_too_large(self):
        self.tree()
        saved = g.MAX_WORLDS_PER_COMPONENT
        try:
            g.MAX_WORLDS_PER_COMPONENT = 4
            err = self.refused(13)
            self.assertIn("component too large", err)
            self.assertIn("plan-a", err)          # names the roots of the component
            self.assertIn("worlds", err)          # and the count
        finally:
            g.MAX_WORLDS_PER_COMPONENT = saved
        self.assertEqual(run(self.root)[0], 0)

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
        self.assertFalse([u for u in D["units"] if u["target"] == "q-leaf"])

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
        self.assertIn(("admit", "cases-x/pic-h"), [(u["kind"], u["target"]) for u in D["units_unranked"]])
        self.tree(pic_h_author="@ai", extra={"h1": [f'{{"id": "h1-22", "by": "@h1", {BASE}, "kind": "admit", "target": {{"row": ["cases-x", "pic-h"]}}, "estimate": "accept"}}']})
        D = self.derived()
        self.assertTrue(D["nodes"]["cases-x"]["admitted"]["pic-h"])
        self.assertIn("pic-h", D["nodes"]["cases-x"]["rows"])

    def test_stale_event_keeps_its_level(self):
        self.tree(shared_version=2)
        D = self.derived()
        self.assertEqual(D["nodes"]["shared-leaf"]["V"]["headline"], 8)
        self.assertIn("stale", D["nodes"]["shared-leaf"]["flags"])
        self.assertIn("h1-1", D["events"]["stale"])
        self.assertIn("version 1, now 2", D["events"]["stale_reasons"]["h1-1"])

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
        self.assertIn("## Sub-frame prog:", view)
        self.assertIn("leading step: step-1", view)
        # a step that beats every plan makes the programme the leading candidate, named through its step
        self.tree(programme=True, prog_p=[0.8, 0.9])
        D = self.derived()
        self.assertEqual((D["act"]["cand"], D["act"]["cand_label"]), ("step-1", "prog → step-1"))
        self.assertTrue(D["lines"]["commit"].startswith("research first: begin with"), D["lines"]["commit"])
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
        self.assertEqual(set(gest), {"step-1", "step-2", "sc-1"})           # the steps' gestalts are ranked first; the programme carries none
        self.assertEqual(gest, [u["target"] for u in D["units"][:3]])
        S = self.derived_dry("--scope", "prog")
        self.assertTrue(S["lines"]["commit"].startswith("commit line suspended: no plan has a value yet"), S["lines"]["commit"])
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
        self.assertIn(f"revive cases-x (S, ~30 min)", (self.root / "graph" / "tasks.md").read_text())
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
        self.edit("graph/frame.yaml", "  - {id: prog, role: plan, preset: worst-case}", "  - {id: prog, role: plan, preset: worst-case}\n  - {id: step-1, role: plan, preset: worst-case, success_class: utopia}")
        self.assertIn("more than one frame", self.refused(1))

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
        pr_b = Q(7, 10) * Q(9, 10) * Q(9, 10)
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
        self.assertTrue(D["lines"]["commit"].startswith("research first: begin with vet cases-x"))

    def test_components_are_independent_and_summed(self):
        D = (self.tree(), self.derived())[1]
        comps = D["world_model"]["components"]
        self.assertEqual([c["roots"] for c in comps], [["plan-a", "plan-b"]])   # the shared leaf joins the two plans
        self.assertTrue(all(c["worlds"] <= D["world_model"]["cap_per_component"] for c in comps))
        self.assertAlmostEqual(sum(c["H_S_bits"] for c in comps), D["ranking"]["H_S_bits"])
        # cut the shared leaf out of plan-b: two components, and the entropy is still the sum
        self.edit("graph/nodes/plan-b.md", "[shared-leaf, or-y, q-leaf, plan-b.complete]", "[or-y, q-leaf, plan-b.complete]")
        D = self.derived()
        comps = D["world_model"]["components"]
        self.assertEqual([c["roots"] for c in comps], [["plan-a"], ["plan-b"]])
        self.assertAlmostEqual(sum(c["H_S_bits"] for c in comps), D["ranking"]["H_S_bits"])
        self.assertTrue(all(u["bits"] >= 0 for u in D["units"] if u["bits"] is not None))

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
        self.assertEqual(scoped["lines"]["scoped"], "scoped: bits about plan-a only")
        self.assertNotEqual(full["ranking"]["H_S_bits"], scoped["ranking"]["H_S_bits"])

    def test_streams(self):
        self.tree()
        code, out, err = run(self.root)
        self.assertEqual((code, out), (0, ""))                         # a plain run prints nothing on stdout
        self.assertTrue(err.startswith("OK "), err)
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
        self.assertEqual(D["ranking_window"]["component"], ["plan-a", "plan-b"])
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
        for gen in g.GENERATED:
            p = root / "graph" / gen
            if p.is_file() and not g.hash_ok(gen, p.read_text()):
                p.unlink()
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
                 "- world model: " + "; ".join(f"[{', '.join(c['roots'])}: {c['variables']} variables, {c['worlds']} worlds]"
                                              for c in cls.D["world_model"]["components"]) + f" (cap {cls.D['world_model']['cap_per_component']} per component)", ""]
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
        self.assertEqual((D["nodes"][prog]["kind"], P["role"], P["frame"]), ("frame", "plan", None))
        steps = {"tt-mart-repair-via-bounds-transfer", "step-asymptotic-to-finite-time", "step-legitimacy-conditioned-trust"}
        self.assertEqual(set(P["subframe"]["steps"]), steps)
        self.assertEqual(set(P["subframe"]["roots"]), steps | {"policy-level-total-trust"})
        for s in steps | {"policy-level-total-trust"}:
            self.assertEqual(D["roots"][s]["frame"], prog)                     # the steps are roots of the sub-frame
        self.assertEqual(D["roots"]["policy-level-total-trust"]["role"], "shared-claim")
        self.assertEqual(D["roots"]["policy-level-total-trust"]["cost"], "inf")  # a question: infinite cost, no vet unit
        self.assertFalse([u for u in D["units"] if u["target"] == "policy-level-total-trust" and u["kind"] != "gestalt"])
        # the AI fill (ruling 34) gives every step a value, so the programme has one and a leading step
        self.assertIsNotNone(P["option_value"])
        self.assertIn(P["subframe"]["leading_step"], steps)
        self.assertTrue(P.get("ai_only"), "the programme's value rests on AI numbers only and must say so")
        self.assertEqual(P["subframe"]["outside_option"], "default-trajectory")
        self.assertEqual(D["roots"]["li-deference-collapse"]["frame"], None)   # the toy result stays a shared claim of the top frame
        u = next(u for u in D["units"] if u["kind"] == "vet" and u["target"] == "tt-mart-repair-via-bounds-transfer")
        self.assertIn(prog, u["bears_on"])                                      # a step's unit ranks in the parent's list
        view = (self.root / "graph" / "view.md").read_text()
        self.assertIn(f"## Sub-frame {prog}:", view)
        self.assertIn("leading step: ", view)
        self.assertIn("rests on AI numbers", view)

    def test_starting_graph_carries_structure_and_the_two_rulings_only(self):
        D = self.D
        # human events: the maintainer's two rulings only; every other counted event is the AI fill
        self.assertEqual([e for e in D["events"]["counted"] if not e.startswith("smithy-verity-")],
                         ["maintainer-001", "maintainer-002"])
        self.assertTrue([e for e in D["events"]["counted"] if e.startswith("smithy-verity-")])
        self.assertEqual(D["events"]["withdrawn"] + D["events"]["stale"], [])
        pol = g.parse_flat_yaml((self.root / "graph" / "policy.yaml").read_text())
        self.assertEqual(set(pol["handles"]), {"@maintainer", "@smithy-verity"})
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
        self.assertEqual({u["target"].split("/")[0] for u in D["units_unranked"] if u["kind"] == "admit"},
                         {"tt-implies-mart-gap-bets", "a1-fixed-objective-maximizer"})
        # after the AI fill (ruling 34) no gestalt unit is ranked: every root carries an AI gestalt or a derived probability
        self.assertEqual([u for u in D["units"] if u["kind"] == "gestalt"], [])
        self.assertIn(D["units"][0]["kind"], ("vet", "map-read"), D["units"][0])
        self.assertTrue(D["lines"]["commit"].startswith("research first"), D["lines"]["commit"])
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
        self.assertEqual(D["nodes"]["a1-fixed-objective-maximizer"]["load"], ["corrigibility-anti-natural"])
        for r in ("instrumental-convergence", "corrigibility-anti-natural"):
            # both roots carry an AI gestalt and a derived probability, so no gestalt unit is ranked (Default of 2026-10-02)
            self.assertNotIn(("gestalt", r), [(u["kind"], u["target"]) for u in D["units"]])
            self.assertTrue(D["roots"][r].get("ai_only"))
        code, out, err = run(self.root, "--scope", "instrumental-convergence", "--dry-run")
        self.assertEqual(code, 0, err)
        S = json.loads(out)                                            # stdout is the JSON alone
        self.assertEqual(S["lines"]["commit"], "commit line suspended: no plan in scope")
        self.assertIn("no plan in scope;", S["lines"]["regime"])
        self.assertTrue(all(u["D"] is None for u in S["units"]))
        self.assertEqual(len(S["world_model"]["components"]), 1)

    def test_plain_run_is_clean_and_idempotent(self):
        code, out, err = run(self.root)
        self.assertEqual((code, out), (0, ""))
        lines = [l for l in err.strip().splitlines() if l]
        self.assertEqual(len(lines), 1, err)                           # one OK line, no WARN
        self.assertTrue(lines[0].startswith("OK "))
        snap = {n: (self.root / "graph" / n).read_text() for n in g.GENERATED}
        code, out, err = run(self.root, "--why", "--as", "@maintainer")
        self.assertEqual(code, 0, err)
        for n in g.GENERATED:
            self.assertEqual((self.root / "graph" / n).read_text(), snap[n], n)

    def test_table_filed_on_the_fixture_passes(self):
        """The review's case: a two-row table on a2 (plus one new contributor) files without touching the cap."""
        D0 = self.D
        if "a2-monotone-in-resources" not in D0["nodes"] or D0["nodes"]["a2-monotone-in-resources"]["kind"] != "leaf":
            self.skipTest("a2 is not a leaf in this fixture")
        root = self.copy_fixture("fx-table")
        for rel, text in A2_TABLE.items():
            (root / "graph" / rel).write_text(text)
        pol = root / "graph" / "policy.yaml"
        pol.write_text(pol.read_text().replace('  "@smithy-verity":', '  "@tester": {kind: human, github: "tester-example"}\n  "@smithy-verity":'))
        t0 = time.perf_counter()
        code, out, err = run(root)
        elapsed = time.perf_counter() - t0
        self.assertEqual(code, 0, err)
        D = json.loads((root / "graph" / "derived.json").read_text())
        comps = D["world_model"]["components"]
        self.assertTrue(all(c["worlds"] <= D["world_model"]["cap_per_component"] for c in comps))
        self.assertEqual(D["nodes"]["a2-monotone-in-resources"]["status"], "conceded")
        self.assertEqual(D["nodes"]["a2-monotone-in-resources"]["diagnosis"], "pic-B-bounded-objective")
        self.assertEqual(D["nodes"]["ic-informal"]["status"], "conceded")             # the informal route falls with a2
        self.assertIn("stale: leaf became a table", D["nodes"]["a2-monotone-in-resources"]["flags"])
        stale = [e for e, why in D["events"]["stale_reasons"].items() if why == "leaf became a table"]
        self.assertIn("tester-000", stale)                                     # the AI's earlier estimate on a2 goes stale too
        self.assertTrue(all(D["events"]["targets"][e] == "a2-monotone-in-resources" for e in stale) if "targets" in D["events"] else True)
        self.assertIn("a2-monotone-in-resources: open → conceded", D["digest"]["statuses_flipped"])
        self.assertEqual(D["events"]["counted"][:2], ["maintainer-001", "maintainer-002"])
        type(self).notes += ["", "## The table case (a two-row table on a2, filed by a new contributor on a scratch copy)",
                             f"- passes in {elapsed:.2f} s; components: " + "; ".join(f"[{', '.join(c['roots'])}: {c['variables']} variables, {c['worlds']} worlds]" for c in comps),
                             f"- a2: {D['nodes']['a2-monotone-in-resources']['status']} by {D['nodes']['a2-monotone-in-resources']['diagnosis']}; ic-informal: {D['nodes']['ic-informal']['status']}; "
                             f"instrumental-convergence: {D['roots']['instrumental-convergence']['status']} ({D['roots']['instrumental-convergence']['diagnosis']})",
                             f"- stale leaf range(s) kept as suggestions: {', '.join(stale)}"]


if __name__ == "__main__":
    unittest.main(verbosity=2)
