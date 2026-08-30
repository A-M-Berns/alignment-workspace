from pathlib import Path
import importlib.util
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("progress_toy", ROOT / "src" / "toy.py")
TOY = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(TOY)


class ProgressToyTests(unittest.TestCase):
    def test_revision_defeat_and_carry_are_explicit(self):
        result = TOY.run(256)
        transition = result["transition"]
        self.assertEqual(transition["event"], "evaluator_revision")
        self.assertEqual(len(transition["defeated"]), 1)
        self.assertEqual(len(transition["carried"]), 2)
        self.assertEqual(len(transition["fresh_licenses"]), 2)

    def test_region_is_nonempty_and_margins_hold(self):
        v = TOY.VALUE
        self.assertGreaterEqual(v["mitigate"] - v["repeat"], TOY.Q(1, 3))
        self.assertGreaterEqual(v["investigate"] - v["ignore"], TOY.Q(1, 4))
        self.assertTrue(all(TOY.Q(0) <= x <= TOY.Q(1) for x in v.values()))

    def test_fairness_error_regret_and_defects(self):
        small = TOY.run(64)
        large = TOY.run(1024)
        self.assertEqual(large["action_weight"], large["inquiry_weight"])
        self.assertLess(large["action_defect_ratio"], small["action_defect_ratio"])
        self.assertLess(large["inquiry_defect_ratio"], small["inquiry_defect_ratio"])
        self.assertLess(large["weighted_tau_ratio"], small["weighted_tau_ratio"])
        self.assertLess(large["action_regret_ratio"], small["action_regret_ratio"])
        self.assertLess(large["inquiry_regret_ratio"], small["inquiry_regret_ratio"])
        self.assertEqual(large["projection_liability"], TOY.Q(0))


if __name__ == "__main__":
    unittest.main()

