import Cleanroom.Corrigibility.LegitNegPricing.Thinning
import Cleanroom.Corrigibility.LegitNegPricing.Scoring
import Cleanroom.Corrigibility.LegitNegPricing.Conservativity
import Cleanroom.Corrigibility.LegitNegPricing.Ratifiability
import Cleanroom.Corrigibility.LegitNegPricing.Steering

/-!
# Audit round 1 (adversarial) — second probe file for `legit-neg-pricing`

Not imported by the library. Elaborated with `scripts/lean-check`. Companion to `Vacuity.lean`
(P1–P7, written earlier in this audit and re-verified here). Each probe is evidence for a line of
`legit-neg-pricing-audit-r1-adversarial.md`; none is a counterexample to a proved theorem.

* **A1** — the scoring class of B1 (`thin_P2_of_selected`) has a real boundary: under `S2` the
  thinned action's `P2` *does* move with `ε` (`3/10` against `3/5` at `ε = 1/2`), so the
  docstring's exclusion of S2 is not a hedge but a fact (B10).
* **A2** — `H_conservative_of_allLeg`'s second hypothesis (`0 ≤ u` on `a`'s void terminals) cannot
  be dropped either: with `u(b, a₁) = −1` cdot strictly prefers `a₁` while `H` strictly prefers
  the fully legitimate `a₀`. Together with `V6_witness` (for the first hypothesis) the package is
  tight in both directions.
* **A3** — `C5_T2`'s strict gap `κ' < κ` is load-bearing: at `κ' = κ` a keeping option worth `0`
  ties a voiding option graded `1`.
* **A4** — on B16's fourth table row at `p = δ + 1/400`, where `B16_rows` shows the pure
  ratifiable set is empty, the credence `(1/201, 200/201)` is `MixedRatifiable`: the mixed
  fixed-point predicate of record is inhabited exactly where the pure one is not (a fact the
  sources do not state; recorded as a finding).
* **A5** — B16's third table row stated *on the toy* (cdot's verdict either side of the closed-form
  threshold `1/20`): the shape `B16_rows` should have, three lines from `B16_P1`.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial2

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

/-! ## A1: S2 is genuinely outside B1's scoring class -/

/-- On B1's own instance (`ε = 1/2`, `η = 1/10`), `P2` under `S2` of `thin+` is `3/10` in the
thinned problem against `3/5` in the base problem: thinning is *not* invisible to conditioning
when the evaluators score the bet. -/
theorem A1_thin_S2_not_invariant :
    (thinInstance (1/2) (1/10) (by norm_num) (by norm_num)).P2
        (thinInstance (1/2) (1/10) (by norm_num) (by norm_num)).S2 2 = some (3/10)
    ∧ (thinBase (1/10)).P2 (thinBase (1/10)).S2 2 = some (3/5) := by
  constructor
  · have hPL : (thinInstance (1/2) (1/10) (by norm_num) (by norm_num)).PL 2 = 1/2 := by
      rw [thinInstance, thin_PL_of_selected _ _ _ _ _ _ 2 (by decide), thinBase_PL]; norm_num
    rw [P2_S2_eq _ _ (by rw [hPL]; norm_num)]
    congr 1
    unfold Problem.H Problem.W EU
    simp [thinInstance, thin, thinBase, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num
  · rw [P2_S2_eq _ _ (by rw [thinBase_PL]; norm_num)]
    congr 1
    unfold Problem.H Problem.W EU
    simp [thinBase, Fin.sum_univ_two]
    norm_num

/-! ## A2: B6's floor hypothesis cannot be dropped -/

/-- `toyB 0 (−1) (1/2) 1 (1/2)`: `a₀` is legitimate everywhere, the void terminal `(b, a₁)` is
worth `−1 < 0`, cdot strictly prefers `a₁` (`1/2 > 1/4`) and `H` strictly prefers `a₀`
(`1/4 > 0`) — the conclusion of `H_conservative_of_allLeg` fails without its `0 ≤ u` hypothesis. -/
theorem A2_B6_needs_floor :
    let P := toyB 0 (-1) (1/2) 1 (1/2) (by norm_num) (by norm_num)
    (∀ s, P.leg s 0 = true)
    ∧ P.P1 (S1 P.u) 0 < P.P1 (S1 P.u) 1
    ∧ P.H 1 < P.H 0
    ∧ P.u 1 1 < 0 := by
  intro P
  refine ⟨fun s => by fin_cases s <;> rfl, ?_, ?_, ?_⟩
  · simp only [P, toyB_P1_S1_zero, toyB_P1_S1_one]; norm_num
  · simp only [P, toyB_H_zero, toyB_H_one]; norm_num
  · simp [P]

/-! ## A3: C5's strict gap is load-bearing -/

/-- One state; `a₀` legitimate and worth `0`, `a₁` void and graded `1`: at `κ' = κ` the two
`P4b` values tie, so `C5_T2` needs `κ' < κ` strictly (and its `V ≥ 0` range only at `V = 0`). -/
theorem A3_C5_gap_load_bearing (κ : ℚ) :
    let Q : Problem (Fin 1) (Fin 2) :=
      { prior := fun _ => 1
        prior_nonneg := fun _ => by norm_num
        prior_sum := by simp
        leg := fun _ a => decide (a = 0)
        u := fun _ a => ![0, 1] a }
    Q.leg 0 0 = true ∧ Q.leg 0 1 = false ∧ Q.u 0 0 = 0 ∧ Q.u 0 1 = 1
    ∧ Q.P4b (S1 Q.u) κ κ (S1 Q.u) 1 = Q.P4b (S1 Q.u) κ κ (S1 Q.u) 0 := by
  intro Q
  refine ⟨by simp [Q], by simp [Q], by simp [Q], by simp [Q], ?_⟩
  simp [Q, Problem.P4b]

/-! ## A4: a mixed fixed point where the pure ratifiable set is empty -/

/-- B16's fourth row (`v = 1/2, w = 9/10, δ = 1/10, π_b = 1/2`) at `p = δ + 1/400`: the pure
ratifiable set is empty (`B16_rows`), yet `(1/201, 200/201)` is mixed-ratifiable — the forecast
menu ties at `907/2010`. -/
theorem A4_mixed_fixed_point_on_empty_row :
    let P := toyB (1/2) (9/10) (1 - 1/10) 1 (1/2) (by norm_num) (by norm_num)
    let V := hybridV P (1/10 + 1/400)
    P.ratifiable V = ∅ ∧ MixedRatifiable P V ![1/201, 200/201] := by
  intro P V
  refine ⟨B16_rows.2.2.2.2, ?_⟩
  refine ⟨fun a => by fin_cases a <;> norm_num, by simp [Fin.sum_univ_two]; norm_num, ?_⟩
  rw [Fin.forall_fin_two]
  simp only [mem_argmax, Fin.forall_fin_two, Fin.sum_univ_two, P, V, toyB_R2scores_hybrid_zero,
    toyB_R2scores_hybrid_one, toyB_H_zero, toyB_H_one]
  norm_num

/-! ## A5: a B16 table row stated on the toy -/

/-- Row 3 (`v = 1/20, w = −1, δ = 1/10, π_b = 1/2`): cdot picks `a₀` at `p = 1/20 + 1/100`, `a₁` at
`p = 1/20 − 1/100`, and ties at `p = 1/20` — `B16_P1` instantiated, which is what `B16_rows`'s
"rows" could be. -/
theorem A5_B16_row3_on_the_toy :
    let P := toyB (1/20) (-1) (1 - 1/10) 1 (1/2) (by norm_num) (by norm_num)
    argmax (P.P1 (hybridV P (1/20 + 1/100))) = {0}
    ∧ argmax (P.P1 (hybridV P (1/20 - 1/100))) = {1}
    ∧ argmax (P.P1 (hybridV P (1/20))) = univ := by
  intro P
  exact ⟨(B16_P1 (1/20) (-1) (1/10) (1/2) (1/20 + 1/100) (by norm_num) (by norm_num)).1.2
      (by norm_num),
    (B16_P1 (1/20) (-1) (1/10) (1/2) (1/20 - 1/100) (by norm_num) (by norm_num)).2.1.2
      (by norm_num),
    (B16_P1 (1/20) (-1) (1/10) (1/2) (1/20) (by norm_num) (by norm_num)).2.2.2 (by norm_num)⟩

end Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial2

/-! ## Axioms used by the probes -/

#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial2.A1_thin_S2_not_invariant
#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial2.A2_B6_needs_floor
#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial2.A3_C5_gap_load_bearing
#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial2.A4_mixed_fixed_point_on_empty_row
#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial2.A5_B16_row3_on_the_toy
