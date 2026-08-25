"""Gate A: the five finite examples are the source's, and the departures are named."""
from __future__ import annotations

import unittest
from fractions import Fraction

import carroll_cases as cc
import drmdp


class TestTable3(unittest.TestCase):
    """The index sets and initial pairs, row by row."""

    def test_conspiracy_influence(self):
        m = cc.conspiracy_influence()
        self.assertEqual(m.states, (cc.S0,))
        self.assertEqual(set(m.thetas), {cc.TH_NATURAL, cc.TH_INFLUENCED})
        self.assertEqual(set(m.actions), {cc.NOOP, cc.INFLUENCE})
        self.assertEqual((m.s0, m.theta0), (cc.S0, cc.TH_NATURAL))

    def test_writers_curse(self):
        m = cc.writers_curse()
        self.assertEqual(set(m.states), {cc.S_NO_POETRY, cc.S_POETRY})
        self.assertEqual(set(m.thetas), {cc.TH_AMBITIOUS, cc.TH_UNHAPPY})
        self.assertEqual(set(m.actions), {cc.NOOP, cc.INFLUENCE})
        self.assertEqual((m.s0, m.theta0), (cc.S_NO_POETRY, cc.TH_AMBITIOUS))

    def test_clickbait(self):
        m = cc.clickbait()
        self.assertEqual(m.states, (cc.S0,))
        self.assertEqual(set(m.thetas), {cc.TH_NORMAL, cc.TH_DISILLUSIONED})
        self.assertEqual(set(m.actions), {cc.NEWS, cc.CLICKBAIT})
        self.assertEqual((m.s0, m.theta0), (cc.S0, cc.TH_NORMAL))
        self.assertEqual(cc.NOOP_ACTION["Clickbait"], cc.NEWS)

    def test_trainer(self):
        m = cc.ai_personal_trainer()
        self.assertEqual(m.states, (cc.S0,))
        self.assertEqual(set(m.thetas), {cc.TH_TIRED, cc.TH_ENERGIZED})
        self.assertEqual((m.s0, m.theta0), (cc.S0, cc.TH_TIRED))

    def test_dehydration(self):
        m = cc.dehydration()
        self.assertEqual(set(m.states), {1, 2, 3})
        self.assertEqual(set(m.thetas), {2, 3, 4})
        self.assertEqual(set(m.actions), {cc.NOOP, cc.A3, cc.A4})
        self.assertEqual((m.s0, m.theta0), (1, 2))


class TestFigures(unittest.TestCase):
    """The transition and reward rules the figures supply."""

    def test_figure_1_transitions(self):
        m = cc.conspiracy_influence()
        self.assertEqual(m.T(cc.S0, cc.TH_NATURAL, cc.NOOP),
                         (((cc.S0, cc.TH_NATURAL), Fraction(1)),))
        self.assertEqual(m.T(cc.S0, cc.TH_NATURAL, cc.INFLUENCE),
                         (((cc.S0, cc.TH_INFLUENCED), Fraction(1)),))
        self.assertEqual(m.T(cc.S0, cc.TH_INFLUENCED, cc.NOOP),
                         (((cc.S0, cc.TH_NATURAL), Fraction(1)),))
        self.assertEqual(m.T(cc.S0, cc.TH_INFLUENCED, cc.INFLUENCE),
                         (((cc.S0, cc.TH_INFLUENCED), Fraction(1)),))

    def test_figure_1_rewards(self):
        m = cc.conspiracy_influence()
        self.assertEqual(m.R(cc.TH_NATURAL, cc.S0, cc.NOOP, cc.S0), 10)
        self.assertEqual(m.R(cc.TH_NATURAL, cc.S0, cc.INFLUENCE, cc.S0), -100)
        self.assertEqual(m.R(cc.TH_INFLUENCED, cc.S0, cc.NOOP, cc.S0), -100)
        self.assertEqual(m.R(cc.TH_INFLUENCED, cc.S0, cc.INFLUENCE, cc.S0), 100)

    def test_figure_2_rewards(self):
        m = cc.writers_curse()
        self.assertEqual(m.R(cc.TH_AMBITIOUS, cc.S_POETRY, cc.NOOP, cc.S_POETRY), 1)
        self.assertEqual(m.R(cc.TH_AMBITIOUS, cc.S_NO_POETRY, cc.NOOP, cc.S_POETRY),
                         Fraction(1, 2))
        self.assertEqual(m.R(cc.TH_UNHAPPY, cc.S_POETRY, cc.NOOP, cc.S_POETRY), -10)
        self.assertEqual(m.R(cc.TH_UNHAPPY, cc.S_NO_POETRY, cc.NOOP, cc.S_POETRY),
                         Fraction(1, 2))

    def test_figure_4_rewards(self):
        m = cc.clickbait()
        self.assertEqual(m.R(cc.TH_NORMAL, cc.S0, cc.CLICKBAIT, cc.S0), 2)
        self.assertEqual(m.R(cc.TH_NORMAL, cc.S0, cc.NEWS, cc.S0), 1)
        self.assertEqual(m.R(cc.TH_DISILLUSIONED, cc.S0, cc.CLICKBAIT, cc.S0), 0)
        self.assertEqual(m.R(cc.TH_DISILLUSIONED, cc.S0, cc.NEWS, cc.S0),
                         Fraction(1, 2))

    def test_figure_6_is_figure_1_with_other_labels(self):
        """Appendix A.8's own claim, checked rather than assumed."""
        bob, diana = cc.conspiracy_influence(), cc.ai_personal_trainer()
        self.assertEqual(drmdp.canonical(bob), drmdp.canonical(diana))
        self.assertNotEqual(bob, diana)          # the labels do differ

    def test_figure_8_rewards(self):
        m = cc.dehydration()
        for th in m.thetas:
            for s in m.states:
                self.assertEqual(m.R(th, s, cc.NOOP, s),
                                 -abs(th - s) - (th - 2) ** 2)
        self.assertEqual(m.R(2, 2, cc.NOOP, 2), 0)     # the source's own value
        self.assertEqual(m.R(3, 2, cc.NOOP, 2), -2)    # Appendix B.1 states -5

    def test_figure_8_branching(self):
        m = cc.dehydration()
        self.assertEqual(m.T(1, 2, cc.A3), (((2, 3), Fraction(1)),))
        self.assertEqual(m.T(1, 2, cc.A4), (((3, 4), Fraction(1)),))
        self.assertEqual(m.T(1, 2, cc.NOOP), (((1, 2), Fraction(1)),))
        for a in m.actions:                            # the drawn self-loops
            self.assertEqual(m.T(2, 3, a), (((2, 3), Fraction(1)),))
            self.assertEqual(m.T(3, 4, a), (((3, 4), Fraction(1)),))

    def test_figure_8_privileged_box(self):
        """The figure's own optimal-policy box, recomputed."""
        import objectives as ob
        m = cc.dehydration()
        H = cc.HORIZON["Dehydration"]
        for th, act in ((2, cc.A3), (3, cc.A4), (4, cc.A4)):
            best = ob.argmax(m, H, ob.u_privileged(th), cc.NOOP)
            paper = ob.materialise(m, H, lambda s, t, i, h, a=act: a)
            self.assertTrue(any(ob.key(paper) == ob.key(p) for p in best),
                            f"figure 8's pi*_[theta={th}] is not optimal")


class TestNoNormativeContent(unittest.TestCase):
    """The constructors contain no judgement, and every departure is declared."""

    def test_departures_are_listed(self):
        names = {d[0] for d in cc.DEPARTURES}
        self.assertIn("WritersCurse", names)
        self.assertIn("Dehydration", names)
        self.assertTrue(all(len(text) > 40 for _, text in cc.DEPARTURES))

    def test_every_case_names_its_source(self):
        self.assertEqual(set(cc.SOURCE), set(cc.CASES))
        for case, where in cc.SOURCE.items():
            self.assertIn("Table 3", where)
            self.assertTrue("Figure" in where)

    def test_the_reference_layer_imports_nothing_normative(self):
        """`drmdp` and `carroll_cases` cannot reach the legitimacy layer."""
        import ast
        import pathlib
        src = pathlib.Path(__file__).resolve().parents[1] / "src"
        forbidden = {"ri_core", "standing", "enrichment", "legitimacy",
                     "fixtures", "old_interface", "variations"}
        for name in ("drmdp.py", "carroll_cases.py", "objectives.py"):
            tree = ast.parse((src / name).read_text())
            imported = set()
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    imported.update(a.name.split(".")[0] for a in node.names)
                elif isinstance(node, ast.ImportFrom) and node.module:
                    imported.add(node.module.split(".")[0])
            self.assertFalse(imported & forbidden,
                             f"{name} imports {imported & forbidden}")

    def test_no_normative_word_is_an_element_label(self):
        """No state, parameterization or action is named by a judgement."""
        banned = ("legitimate", "illegitimate", "manipulat", "consent",
                  "authoris", "authoriz", "good", "bad", "acceptable")
        for build in cc.CASES.values():
            m = build()
            for label in tuple(m.states) + tuple(m.thetas) + tuple(m.actions):
                for word in banned:
                    self.assertNotIn(word, str(label).lower())


if __name__ == "__main__":
    unittest.main()
