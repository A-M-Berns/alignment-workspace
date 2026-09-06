import unittest
from fractions import Fraction as Q

from src import fixtures
from src.mediation import (all_conducts, best_prediction, best_value, deficit, mediated,
                           override_split, prediction_error, preserving_prep_names, repair,
                           value)

EPISODES = {
    "committed": fixtures.committed,
    "override": fixtures.override_after_full_update,
    "foreclosing": fixtures.foreclosing,
    "mild": fixtures.mild_disagreement,
}


class Mediation(unittest.TestCase):
    def test_deficit_splits_exactly_into_acc_and_override_terms(self):
        """deficit(π) = acc_deficit + gap + regret for every conduct of every episode,
        and acc_deficit ≤ 2B·eps_acc ≤ 2B·eps_pred."""
        for name, make in EPISODES.items():
            ep = make()
            for c in all_conducts(ep):
                pred = best_prediction(ep, c.prep)
                s = override_split(ep, c, pred)
                self.assertEqual(deficit(ep, c), s["acc_deficit"] + s["gap"] + s["regret"], name)
                self.assertLessEqual(s["acc_deficit"], 2 * ep.bound * s["eps_acc"])
                self.assertLessEqual(s["eps_acc"], prediction_error(ep, c.prep, pred))

    def test_B_decomposition_over_non_foreclosing_conducts(self):
        """(B): sup over non-foreclosing conducts of value − best mediated value
        ≤ 2B·eps_pred + eps_ST + r_P with eps_ST, r_P the worst selected gap and
        principal regret over the same class."""
        for name, make in EPISODES.items():
            ep = make()
            preserving = preserving_prep_names(ep)
            conducts = list(all_conducts(ep, preserving))
            best_med = best_value(ep, [c for c in conducts if mediated(ep, c)])
            eps_pred = max(prediction_error(ep, c.prep, best_prediction(ep, c.prep)) for c in conducts)
            splits = [override_split(ep, c, best_prediction(ep, c.prep)) for c in conducts]
            eps_st = max(s["gap"] for s in splits)
            r_p = max(s["regret"] for s in splits)
            delta = max(value(ep, c) for c in conducts) - best_med
            self.assertLessEqual(delta, 2 * ep.bound * eps_pred + eps_st + r_p, name)
            # the principal maximises its own grade, so its regret is never positive
            self.assertLessEqual(r_p, Q(0), name)

    def test_committed_episode_acceleration_bound_attained(self):
        ep = fixtures.committed()
        conducts = [c for c in all_conducts(ep, ["commit-d0", "commit-d1", "hedge"])]
        best_med = best_value(ep, [c for c in conducts if mediated(ep, c)])
        self.assertEqual(best_med, Q(1, 2))
        best_pre = max(value(ep, c) for c in conducts)
        self.assertEqual(best_pre, Q(1))
        eps_pred = min(prediction_error(ep, c.prep, best_prediction(ep, c.prep)) for c in conducts)
        self.assertEqual(eps_pred, Q(1, 4))
        self.assertEqual(best_pre - best_med, 2 * ep.bound * eps_pred)

    def test_override_episode_is_pure_selected_gap(self):
        """Control 1 in the mediation register: perfect prediction, opposite values."""
        ep = fixtures.override_after_full_update()
        pre = [c for c in all_conducts(ep) if c.channel[("c0", "d0")] == "d1"][0]
        s = override_split(ep, pre, best_prediction(ep, pre.prep))
        self.assertEqual(prediction_error(ep, pre.prep, best_prediction(ep, pre.prep)), Q(0))
        self.assertEqual(s["acc_deficit"], Q(0))
        self.assertEqual(s["regret"], Q(-1))
        self.assertEqual(s["gap"], Q(3))          # X − Y = 2 − (−1)
        self.assertEqual(deficit(ep, pre), Q(2))  # = 2B, the unconditional bound

    def test_foreclosure_premium_is_phi_C_on_mediated_conducts(self):
        """Control 4: Δ over admissible (preserving) conducts is 0; Φ_C with the
        repair 'replace the preparation by the best preserving one' equals the old
        foreclosure premium, 1/2; and (C) holds with equality."""
        ep = fixtures.foreclosing()
        preserving = preserving_prep_names(ep)
        all_med = [c for c in all_conducts(ep) if mediated(ep, c)]
        pres_med = [c for c in all_conducts(ep, preserving) if mediated(ep, c)]
        best_pres = best_value(ep, pres_med)
        premium = best_value(ep, all_med) - best_pres
        self.assertEqual(premium, Q(1, 2))
        delta_C = max(value(ep, c) for c in all_conducts(ep, preserving)) - best_pres
        self.assertEqual(delta_C, Q(0))
        phi_C = max(max(value(ep, c) - best_pres, Q(0)) for c in all_conducts(ep))
        self.assertEqual(phi_C, premium)
        delta_phys = max(value(ep, c) for c in all_conducts(ep)) - best_pres
        self.assertLessEqual(delta_phys, delta_C + phi_C)
        self.assertEqual(delta_phys, delta_C + phi_C)

    def test_repair_of_a_foreclosing_conduct_costs_nothing(self):
        ep = fixtures.foreclosing()
        seize = [c for c in all_conducts(ep, ["seize"]) if mediated(ep, c)][0]
        self.assertEqual(deficit(ep, seize), Q(0))
        self.assertEqual(value(ep, seize), Q(1))


if __name__ == "__main__":
    unittest.main()
