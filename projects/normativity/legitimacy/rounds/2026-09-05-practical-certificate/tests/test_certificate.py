from fractions import Fraction as F
import unittest

from src.certificate import (
    ColumnEdge,
    adequate_set_route_constants,
    anchored_loss,
    box_feasible,
    column_progress_terms,
    disjoint_bundle_minimax,
    displayed_suboptimality,
    farkas_infeasibility_certificate,
    honest_column,
    one_sided_radius,
    practical_cert_holds,
    proxy_route_constants,
    randomized_regret,
    sup_distance_to_box,
    two_sided_radius,
    union_bound_condition_holds,
    value_route_constants,
    value_route_minimal_eps_resp,
    zero_defect_adequacy_certificate,
)

# Shared three-response fixture: response `a` is adequate for e1, `b` for e2, `c` for
# neither.  Losses are 0/1 so D = 1 and Λ_e(Π) = Π(Q \ A_e).
MENU = ("a", "b", "c")
LOSS = {
    "e1": {"a": F(0), "b": F(1), "c": F(1)},
    "e2": {"a": F(1), "b": F(0), "c": F(1)},
}
ADEQ = {"e1": frozenset({"a"}), "e2": frozenset({"b"})}
DELTA_A = {"a": F(1), "b": F(0), "c": F(0)}
DELTA_B = {"a": F(0), "b": F(1), "c": F(0)}
HALF_AB = {"a": F(1, 2), "b": F(1, 2), "c": F(0)}


class Factorizations(unittest.TestCase):
    def test_value_route_constants_match_realization_round(self):
        self.assertEqual(value_route_constants(F(3, 2), F(1, 20), F(1, 10), F(1, 50)),
                         (F(3), F(8, 25)))

    def test_value_route_end_to_end_instance(self):
        # displayed values within 1/20 of the authenticated ones; the adapter is
        # exactly optimal in displayed values, so η = 0 and regret ≤ 2·(1/20)
        true = {"a": F(1), "b": F(1, 2), "c": F(0)}
        displayed = {"a": F(19, 20), "b": F(11, 20), "c": F(1, 20)}
        self.assertEqual(two_sided_radius(displayed, true), F(1, 20))
        self.assertEqual(displayed_suboptimality(DELTA_A, displayed), 0)
        self.assertEqual(randomized_regret(DELTA_A, true), 0)
        self.assertLessEqual(randomized_regret(DELTA_A, true), 2 * F(1, 20))

    def test_adequate_set_route_constants_and_lean_witness_instance(self):
        # the Lean inhabitation witness: A = {a}, Π = (1/2, 1/2, 0), κ = 0, θ = 1/2, d = 0
        M, eps = adequate_set_route_constants(F(1), F(0), F(1, 2), F(0))
        self.assertEqual((M, eps), (F(0), F(1, 2)))
        self.assertEqual(anchored_loss(HALF_AB, LOSS["e1"]), F(1, 2))
        self.assertTrue(practical_cert_holds(anchored_loss(HALF_AB, LOSS["e1"]), M, F(0), eps))

    def test_proxy_form_is_equivalent_to_the_certificate(self):
        # any certificate (M, ε) is the proxy route with g := M d + ε, L = 1, C = M, ε₀ = ε
        for M, eps in [(F(2), F(1, 3)), (F(0), F(0)), (F(7, 4), F(5))]:
            self.assertEqual(proxy_route_constants(F(1), M, eps, F(0)), (M, eps))
        # and the value route is the proxy route with C = 1, ε₀ = ζ, L ↦ 2L, ε^resp ↦ Lη + ε^resp
        L, zeta, eta, eps_resp = F(3, 2), F(1, 20), F(1, 10), F(1, 50)
        self.assertEqual(proxy_route_constants(2 * L, F(1), zeta, L * eta + eps_resp),
                         value_route_constants(L, zeta, eta, eps_resp))
        # and the adequate-set route is the proxy route with L = D, C = κ, ε₀ = 0 when the
        # region pins the inadequacy coordinate, ε^resp = ε^ad + Dθ
        D, kappa, theta, eps_ad = F(1), F(1), F(1, 4), F(1, 8)
        self.assertEqual(proxy_route_constants(D, kappa, F(0), eps_ad + D * theta),
                         adequate_set_route_constants(D, kappa, theta, eps_ad))


class Necessity(unittest.TestCase):
    def test_adequate_set_route_needs_each_retained_control(self):
        # No off-adequate coupling: at d = theta = 0, the all-b response has unit loss.
        self.assertEqual(anchored_loss(DELTA_B, LOSS["e1"]), F(1))
        self.assertFalse(practical_cert_holds(F(1), F(1), F(0), F(0)))

        # No finite off-set loss bound: fixed failure mass 1/10 carries arbitrarily
        # large expected loss while d, kappa, and theta remain fixed.
        pi = {"a": F(9, 10), "b": F(1, 10)}
        for off_loss in [F(10), F(100), F(1000)]:
            lam = {"a": F(0), "b": off_loss}
            self.assertEqual(anchored_loss(pi, lam), off_loss / 10)

        # Calling a response adequate does no work without the epsilon_ad loss bound.
        mislabelled_adequate_loss = {"a": F(7), "b": F(0), "c": F(0)}
        self.assertEqual(anchored_loss(DELTA_A, mislabelled_adequate_loss), F(7))

    def test_anchor_index_cannot_be_erased(self):
        # The same response receipt has opposite evaluations under two immutable anchors.
        self.assertEqual(anchored_loss(DELTA_A, LOSS["e1"]), F(0))
        self.assertEqual(anchored_loss(DELTA_A, LOSS["e2"]), F(1))

    def test_one_sided_calibration_suffices_and_is_strictly_weaker(self):
        true = {"a": F(1), "b": F(1, 2), "c": F(1, 2)}
        displayed = {"a": F(9, 10), "b": F(1, 2), "c": F(0)}  # c underestimated by 1/2
        r_two = two_sided_radius(displayed, true)
        r_one = one_sided_radius(displayed, true)
        self.assertEqual(r_two, F(1, 2))
        self.assertEqual(r_one, F(1, 10))
        regret = randomized_regret(DELTA_A, true)
        eta = displayed_suboptimality(DELTA_A, displayed)
        self.assertEqual((regret, eta), (F(0), F(0)))
        self.assertLessEqual(regret, 2 * r_one + eta)
        # the two-sided bound is the whole loss range D = 1 here: vacuous
        self.assertEqual(2 * r_two + eta, F(1))

    def test_value_soundness_is_not_used(self):
        # V_a = [2/5, 3/5], v*_a = 7/10 ∉ V; directed ambiguity ζ = sup_{u∈V}|u − v*| = 3/10.
        rows = [("V_a", F(2, 5), F(3, 5))]
        v_star = F(7, 10)
        zeta = max(abs(F(2, 5) - v_star), abs(F(3, 5) - v_star))
        self.assertEqual(zeta, F(3, 10))
        self.assertFalse(F(2, 5) <= v_star <= F(3, 5))
        for b in [F(0), F(1, 5), F(2, 5), F(1, 2), F(3, 5), F(9, 10), F(1)]:
            d = sup_distance_to_box({"V_a": b}, rows)
            self.assertLessEqual(abs(b - v_star), d + zeta)
        # tight at b = 1/5
        self.assertEqual(abs(F(1, 5) - v_star), sup_distance_to_box({"V_a": F(1, 5)}, rows) + zeta)

    def test_value_route_is_vacuous_on_a_forbidden_optimum(self):
        # rights-like obligation: response f is value-optimal and forbidden
        true = {"f": F(1), "g": F(0)}
        loss = {"f": F(1), "g": F(0)}
        for L in [F(0), F(1), F(10), F(1000)]:
            self.assertEqual(value_route_minimal_eps_resp(loss, true, L), F(1))  # = D
        # adequate-set route: region pins the "response is f" coordinate to 0; a
        # constraint-respecting adapter Π(b) = (b_f, 1 − b_f) has Λ = b_f = d(b)
        rows = [("phi_f", F(0), F(0))]
        M, eps = adequate_set_route_constants(F(1), F(1), F(0), F(0))
        self.assertEqual((M, eps), (F(1), F(0)))
        for b_f in [F(0), F(1, 4), F(1, 2), F(1)]:
            pi = {"f": b_f, "g": 1 - b_f}
            d = sup_distance_to_box({"phi_f": b_f}, rows)
            self.assertEqual(anchored_loss(pi, loss), d)
            self.assertTrue(practical_cert_holds(anchored_loss(pi, loss), M, d, eps))

    def test_routes_are_incomparable_in_constants(self):
        # regret-dominated obligation with loss range D = 10: value route (L = 1, ζ = 1/2,
        # η = 0) gives (2, 1); adequate-set route with the optimum pinned gives (10, 0).
        value = value_route_constants(F(1), F(1, 2), F(0), F(0))
        adequate = adequate_set_route_constants(F(10), F(1), F(0), F(0))
        self.assertEqual(value, (F(2), F(1)))
        self.assertEqual(adequate, (F(10), F(0)))
        bound = lambda c, d: c[0] * d + c[1]
        self.assertLess(bound(adequate, F(1, 20)), bound(value, F(1, 20)))
        self.assertLess(bound(value, F(1, 5)), bound(adequate, F(1, 5)))
        self.assertEqual(bound(value, F(1, 8)), bound(adequate, F(1, 8)))  # crossing


class JointCompatibility(unittest.TestCase):
    def test_region_feasible_but_no_common_adequate_response(self):
        # both indicator rows are individually sound realizations and jointly feasible
        rows = [("ind_e1", F(1), F(1)), ("ind_e2", F(1), F(1))]
        self.assertTrue(box_feasible(rows))
        # each edge is separately certifiable with ε = 0
        self.assertTrue(zero_defect_adequacy_certificate(DELTA_A, {"e1": LOSS["e1"]}, {"e1": F(0)}))
        self.assertTrue(zero_defect_adequacy_certificate(DELTA_B, {"e2": LOSS["e2"]}, {"e2": F(0)}))
        # no common distribution reaches ε < 1/2 on both: dual certificate w = (1/2, 1/2)
        for eps in [F(0), F(1, 4), F(49, 100)]:
            self.assertTrue(farkas_infeasibility_certificate(
                {"e1": F(1, 2), "e2": F(1, 2)}, ADEQ, {"e1": eps, "e2": eps}, MENU))
        # the even split attains 1/2 on both, which is the minimax value
        self.assertTrue(zero_defect_adequacy_certificate(HALF_AB, LOSS, {"e1": F(1, 2), "e2": F(1, 2)}))
        self.assertEqual(disjoint_bundle_minimax(2, F(1)), (F(1, 2), F(1, 2)))

    def test_practical_compatibility_does_not_need_region_feasibility(self):
        rows = [("phi", F(3, 5), F(1)), ("phi", F(0), F(2, 5))]
        self.assertFalse(box_feasible(rows))
        losses = {"e1": LOSS["e1"], "e2": LOSS["e1"]}
        self.assertTrue(zero_defect_adequacy_certificate(DELTA_A, losses, {"e1": F(0), "e2": F(0)}))

    def test_union_bound_is_necessary_not_sufficient(self):
        adequate = {"e1": frozenset({"x"}), "e2": frozenset({"y"}), "e3": frozenset({"z"})}
        theta = {e: F(1, 2) for e in adequate}
        self.assertTrue(union_bound_condition_holds(adequate, theta))
        self.assertTrue(farkas_infeasibility_certificate(
            {e: F(1, 3) for e in adequate}, adequate, theta, ("x", "y", "z")))
        # tightening any one slack below 1/2 already fails the union bound on a pair
        theta["e1"] = F(2, 5)
        self.assertFalse(union_bound_condition_holds(adequate, theta))

    def test_mixture_strictly_beats_deterministic_common_response(self):
        eps = {"e1": F(1, 2), "e2": F(1, 2)}
        for det in [DELTA_A, DELTA_B, {"a": F(0), "b": F(0), "c": F(1)}]:
            self.assertFalse(zero_defect_adequacy_certificate(det, LOSS, eps))
        self.assertTrue(zero_defect_adequacy_certificate(HALF_AB, LOSS, eps))

    def test_disjoint_bundle_minimax_is_attained(self):
        self.assertEqual(disjoint_bundle_minimax(3, F(1)), (F(2, 3), F(2, 3)))
        self.assertEqual(disjoint_bundle_minimax(4, F(3)), (F(9, 4), F(9, 4)))

    def test_shared_value_coordinates_force_ambiguity_to_cover_disagreement(self):
        v1 = {"a": F(1), "b": F(0)}
        v2 = {"a": F(0), "b": F(1)}
        disagreement = max(abs(v1[q] - v2[q]) for q in v1)
        for b in [{"a": F(1, 2), "b": F(1, 2)}, {"a": F(3, 4), "b": F(1, 4)}, {"a": F(1), "b": F(0)}]:
            self.assertGreaterEqual(two_sided_radius(b, v1) + two_sided_radius(b, v2), disagreement)
        # any deterministic response has regret 1 for one exposure; the even mix has 1/2 for both
        self.assertEqual(randomized_regret({"a": F(1), "b": F(0)}, v2), F(1))
        self.assertEqual(randomized_regret({"a": F(1, 2), "b": F(1, 2)}, v1), F(1, 2))


class Accounting(unittest.TestCase):
    MASS = {"e1": F(1, 2), "e2": F(1, 2)}

    def test_charging_two_edges_to_one_response_breaks_the_progress_inequality(self):
        dishonest = [ColumnEdge("e1", F(1, 2), F(1), F(0)), ColumnEdge("e2", F(1, 2), F(1), F(0))]
        with self.assertRaises(ValueError):
            honest_column(DELTA_A, F(0), LOSS, dishonest)
        realized, claimed = column_progress_terms(self.MASS, DELTA_A, LOSS, dishonest, F(0), F(1))
        self.assertEqual((realized, claimed), (F(1, 2), F(0)))
        self.assertGreater(realized, claimed)

    def test_residual_outcome_is_honest(self):
        edges = [ColumnEdge("e1", F(1, 2), F(1), F(0))]
        self.assertEqual(honest_column(DELTA_A, F(0), LOSS, edges), (F(0), F(0)))
        realized, claimed = column_progress_terms(self.MASS, DELTA_A, LOSS, edges, F(0), F(1))
        self.assertEqual((realized, claimed), (F(1, 2), F(1, 2)))

    def test_common_response_outcome_is_honest_with_its_own_constants(self):
        edges = [ColumnEdge("e1", F(1, 2), F(0), F(1, 2)), ColumnEdge("e2", F(1, 2), F(0), F(1, 2))]
        self.assertEqual(honest_column(HALF_AB, F(0), LOSS, edges), (F(1, 2), F(1, 2)))
        realized, claimed = column_progress_terms(self.MASS, HALF_AB, LOSS, edges, F(0), F(1))
        self.assertEqual((realized, claimed), (F(1, 2), F(1, 2)))

    def test_distinct_service_contexts_are_two_columns(self):
        col1 = [ColumnEdge("e1", F(1, 2), F(1), F(0))]
        col2 = [ColumnEdge("e2", F(1, 2), F(1), F(0))]
        self.assertEqual(honest_column(DELTA_A, F(0), LOSS, col1), (F(0), F(0)))
        self.assertEqual(honest_column(DELTA_B, F(0), LOSS, col2), (F(0), F(0)))
        # the same edges against the other occurrence's response are refused
        with self.assertRaises(ValueError):
            honest_column(DELTA_B, F(0), LOSS, col1)


if __name__ == "__main__":
    unittest.main()
