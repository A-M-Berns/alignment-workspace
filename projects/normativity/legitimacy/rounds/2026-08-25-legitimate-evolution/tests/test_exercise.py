"""Proper Exercise: the separations, and what survives an opaque permission.

Grounded Replay is frozen. Nothing here imports into `replay.py`, and
`test_replay.py` still checks that the kernel names no semantic identifier.
"""
from __future__ import annotations

import ast
import inspect
import unittest

import replay as rp
import office as of
import exercise as ex


def last_accepted(f) -> bool:
    return (len(f.trace) - 1) in rp.accepted(f)


class TestTheSeparations(unittest.TestCase):
    """§1. Grounded authority against proper exercise."""

    CASES = (
        ("A in scope", of.fiscal_in_scope, True),
        ("B out of scope", of.fiscal_out_of_scope, False),
        ("E self expansion", of.self_expansion, False),
        ("F constitutional widening", of.constitutional_widening, True),
    )

    def test_the_canonical_pair(self):
        for name, make, expect in self.CASES:
            with self.subTest(name):
                self.assertEqual(last_accepted(of.build(make())), expect)

    def test_grounded_replay_alone_says_nothing_against_overreach(self):
        """Both arms satisfy the kernel's premises; only permission separates them."""
        for make in (of.fiscal_in_scope, of.fiscal_out_of_scope):
            f = of.build(make())
            self.assertEqual(rp.violations(f), {})
            self.assertEqual(rp.thm_grounded_replay(f), ())
        good, bad = of.build(of.fiscal_in_scope()), of.build(of.fiscal_out_of_scope())
        self.assertEqual(good.trace[0].grounds, bad.trace[0].grounds)
        self.assertNotEqual(rp.accepted(good), rp.accepted(bad))


class TestDelegation(unittest.TestCase):
    """§12. Four cases, and no subset rule is assumed."""

    def test_narrower_and_equal_pass(self):
        for kind in ("narrower", "equal"):
            self.assertTrue(last_accepted(of.build(of.delegation(kind))), kind)

    def test_broader_and_incomparable_fail_without_meta_authority(self):
        for kind in ("broader", "incomparable"):
            self.assertFalse(last_accepted(of.build(of.delegation(kind))), kind)

    def test_broader_passes_with_authority_over_authority(self):
        self.assertTrue(last_accepted(of.build(of.constitutional_widening())))

    def test_the_difference_is_permission_not_structure(self):
        """The kernel accepts both shapes; the constitution's own token decides."""
        narrow = of.build(of.delegation("narrower"))
        wide = of.build(of.constitutional_widening())
        self.assertEqual(rp.violations(narrow), {})
        self.assertEqual(rp.violations(wide), {})
        self.assertEqual(ex.widening_edits(narrow, of.capability), ())
        self.assertNotEqual(ex.widening_edits(wide, of.capability), ())


class TestAuthorityOverAuthority(unittest.TestCase):
    """§§5, 18, 19. Amendment and replacement, with no special case."""

    def test_self_amendment_is_judged_under_the_old_rule(self):
        f = of.build(of.self_amendment(True))
        self.assertTrue(last_accepted(f))
        self.assertEqual(of.names(f, rp.live(f)), {"w:rule-R2"})

    def test_an_act_citing_the_rule_it_creates_is_refused(self):
        f = of.build(of.self_amendment(False))
        self.assertFalse(last_accepted(f))
        self.assertTrue(f.trace[0].grounds & f.issued(0))
        self.assertEqual(of.names(f, rp.live(f)), {"w:rule-R"})

    def test_total_replacement_is_permitted_by_the_prior_rule(self):
        f = of.build(of.constitutional_replacement())
        self.assertTrue(last_accepted(f))
        self.assertEqual(of.names(f, rp.live(f)), {"w:assembly", "w:tribunal"})

    def test_no_scope_conservativity_is_imposed(self):
        """The successors' capabilities are unrelated to the predecessors'."""
        f = of.build(of.constitutional_replacement())
        before, after = ex.reach_trace(f, of.capability)
        self.assertNotEqual(before & after, before)
        self.assertNotEqual(after - before, frozenset())

    def test_authority_transforming_edits_need_no_second_ontology(self):
        """They are ordinary edits whose issued content happens to be authority."""
        f = of.build(of.constitutional_widening())
        self.assertEqual(len(f.trace[0].issues), 1)
        self.assertTrue(isinstance(f.trace[0].issues[0], of.Warrant))
        self.assertEqual(rp.violations(f), {})


class TestJointAuthority(unittest.TestCase):
    """§13. Support plus a predicate already handles it."""

    def test_two_of_three_passes_and_one_does_not(self):
        self.assertTrue(last_accepted(of.build(of.threshold(2))))
        self.assertFalse(last_accepted(of.build(of.threshold(1))))

    def test_no_authority_algebra_was_needed(self):
        """The edit names the members it invoked; the predicate counts them."""
        f = of.build(of.threshold(2))
        self.assertEqual(len(f.trace[0].grounds), 2)
        src = inspect.getsource(rp)
        for word in ("quorum", "threshold", "vote"):
            self.assertNotIn(word, src)


class TestNegativeConditions(unittest.TestCase):
    """§14. A fact the permission read is not an ancestor."""

    def test_a_live_veto_refuses_the_measure(self):
        self.assertFalse(last_accepted(of.build(of.veto(True))))
        self.assertTrue(last_accepted(of.build(of.veto(False))))

    def test_the_veto_is_not_in_the_grounding_tree(self):
        f = of.build(of.veto(False))
        measure = [o for t in rp.accepted(f) for o in f.issued(t)
                   if of.names(f, {o}) == {"n:measure"}][0]
        mentioned = of.names(f, ex.tree_mentions(f, measure))
        self.assertEqual(mentioned, {"n:measure", "w:board"})
        self.assertNotIn("n:veto", mentioned)

    def test_the_hereditary_and_the_local_are_different_fields(self):
        f = of.build(of.veto(False))
        e = f.trace[-1]
        self.assertEqual(e.grounds, {o for o in f.base
                                     if of.names(f, {o}) == {"w:board"}})
        self.assertNotIn("veto", str(e.declared))


class TestExPostRationalisation(unittest.TestCase):
    """§§10, 11. Grounds live on the edit, so the route is the actual one."""

    def test_an_unused_valid_basis_does_not_save_the_act(self):
        f = of.build(of.ex_post_rationalisation())
        self.assertFalse(last_accepted(f))
        safety = [o for o in f.base if of.names(f, {o}) == {"w:safety"}][0]
        self.assertIn(safety, f.authorities(rp.live(f)))
        self.assertNotIn(safety, f.trace[0].grounds)

    def test_a_basis_that_would_have_worked_is_available(self):
        """So the refusal is about the route taken, not about the edit's content."""
        f = of.build(of.ex_post_rationalisation())
        e = f.trace[0]
        safety = [o for o in f.base if of.names(f, {o}) == {"w:safety"}][0]
        alt = rp.Edit(grounds=frozenset({safety}), issues=e.issues,
                      declared=e.declared, label="right-basis")
        g = rp.Frame(f.base, (alt,), f.auth, f.valid)
        object.__setattr__(g, "content", f.content)
        self.assertTrue(g.valid(f.base, alt))

    def test_invoking_the_other_basis_is_a_different_edit(self):
        """At a different position, issuing different occurrences."""
        f = of.build(of.ex_post_rationalisation())
        self.assertEqual(rp.admitted(f), f.base)
        self.assertEqual(rp.cor_no_laundering(f), ())


class TestWhatSurvivesAnOpaquePermission(unittest.TestCase):
    """§15. Be ruthless about what is actually earned."""

    FRAMES = ("fiscal_in_scope", "fiscal_out_of_scope", "self_expansion",
              "constitutional_widening", "constitutional_replacement",
              "threshold", "ex_post_rationalisation")

    def frames(self):
        for c in of.EXERCISE_CONSTITUTIONS:
            yield of.build(c)

    def test_e1_change_is_mediated(self):
        for f in self.frames():
            self.assertEqual(ex.thm_mediated_change(f, of.capability), ())

    def test_e2_no_jurisdictional_self_ratification(self):
        for f in self.frames():
            self.assertEqual(
                ex.thm_no_jurisdictional_self_ratification(f), ())

    def test_e2_holds_for_any_capability_assignment(self):
        """It never inspects `Cap`, so an arbitrary one changes nothing."""
        f = of.build(of.self_amendment(True))
        for cap in (of.capability, lambda c: frozenset({"anything"}),
                    lambda c: frozenset()):
            self.assertEqual(
                ex.thm_no_jurisdictional_self_ratification(f), ())
            self.assertEqual(ex.thm_mediated_change(f, cap), ())

    def test_e4_no_widening_gives_monotone_reach(self):
        for make in (of.fiscal_in_scope, lambda: of.delegation("narrower"),
                     lambda: of.delegation("equal")):
            f = of.build(make())
            self.assertEqual(ex.widening_edits(f, of.capability), ())
            self.assertEqual(ex.gained(f, of.capability), ())

    def test_e4_is_conditional_and_the_hypothesis_is_declinable(self):
        """A constitution that licenses widening simply declines it."""
        f = of.build(of.constitutional_widening())
        self.assertNotEqual(ex.widening_edits(f, of.capability), ())
        self.assertEqual([d for _, d in ex.gained(f, of.capability)],
                         [("d:safety",)])

    def test_escalation_needs_a_base_that_is_not_plenary(self):
        """Otherwise reach is already everything and nothing can grow it."""
        plenary = of.build(of.fiscal_in_scope())
        self.assertEqual(ex.gained(plenary, of.capability), ())
        r = ex.reach_trace(plenary, of.capability)
        self.assertEqual(r[0], r[-1])
        self.assertTrue(of.SAFETY <= r[0])

    def test_e3_is_not_a_theorem(self):
        """Availability is not the check. A permission may decline to read it.

        The decisive pairing: `self_expansion` and `blind_permit` are the **same
        gazette**, satisfy the same kernel premises, and differ only in whether
        the permission relation reads what the act puts in force. One is refused
        and one escalates. So no theorem quantifying over permission relations
        can rule escalation out.
        """
        strict = of.build(of.self_expansion())
        blind = of.build(of.blind_permit())
        self.assertEqual(strict.base, blind.base)
        self.assertEqual(
            [(e.grounds, e.dispose, e.issues, e.declared) for e in strict.trace],
            [(e.grounds, e.dispose, e.issues, e.declared) for e in blind.trace])

        self.assertTrue(ex.capability_is_available(blind, of.capability))
        self.assertFalse(last_accepted(strict))
        self.assertTrue(last_accepted(blind))
        self.assertEqual(ex.gained(strict, of.capability), ())
        self.assertNotEqual(ex.gained(blind, of.capability), ())

        held = of.capability(blind.content[
            [o for o in blind.base if of.names(blind, {o}) == {"w:fiscal"}][0]])
        self.assertNotIn(of.AMEND, held)

    def test_the_escalation_is_invisible_to_the_kernel(self):
        """Which is the point: it is a defect of the semantics, not the replay."""
        f = of.build(of.blind_permit())
        self.assertEqual(rp.violations(f), {})
        self.assertEqual(rp.thm_grounded_replay(f), ())
        self.assertEqual(rp.cor_no_self_ratification(f), ())


class TestTheKernelIsUntouched(unittest.TestCase):
    """§7 and §20. Proper Exercise decorates; it does not extend."""

    def test_the_kernel_does_not_import_the_analysis(self):
        tree = ast.parse(inspect.getsource(rp))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported |= {n.name.split(".")[0] for n in node.names}
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertNotIn("exercise", imported)
        self.assertNotIn("office", imported)

    def test_the_kernel_has_no_capability_notion(self):
        for word in ("cap", "scope", "domain", "jurisdiction", "reach"):
            self.assertNotIn(word, rp.Frame.__dataclass_fields__)
            self.assertNotIn(word, rp.Edit.__dataclass_fields__)

    def test_every_exercise_frame_satisfies_the_kernel_premises(self):
        for c in of.EXERCISE_CONSTITUTIONS + (of.blind_permit(),):
            f = of.build(c)
            self.assertEqual(rp.violations(f), {})
            self.assertEqual(rp.fresh_by_construction(f), ())
            self.assertEqual(rp.thm_grounded_replay(f), ())
            self.assertEqual(rp.cor_persistence(f), ())


if __name__ == "__main__":
    unittest.main()
