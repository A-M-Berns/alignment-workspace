import Cleanroom.Bli.UdtBliSist.SymWitness

/-!
# Audit round 2 (adversarial) probe: the pinned-Ask model has a non-degenerate inhabitant, and
its sign depends on `ρ`

The ledger (row `sist_identity_const`, `sist_hpoint`) ships `Sist3.hPoint` as the only inhabitant
of `H_point` and says "no non-degenerate inhabitant of `H_point` is shipped — the tent and `Sym2`
both fail it". `Sym2` fails it only when `Ask₂` has mass (`Sym2.not_hPoint` needs `0 < w 1`).
With `w 1 = 0` the two-ask-table family inhabits `H_point` **non-degenerately**: `Ask₂` is still in
the carrier, Omega's pick still lands on it half the time in the Rec branch, and the two Ask points
are still correlated at `ρ` — which is exactly the situation the pinned-Ask display
`V·μ(Rec)·ρ̄^Rec > c·μ(Ask)` is about. On it `sist_hpoint` reads
`EU Ask₁ give − EU Ask₁ refuse = V·w(Rec)·(1+ρ)/2 − c·w(Ask₁) + w(Other)·Δr₀`, and at the
source's masses `(49/100, 0, 49/100, 2/100)`, `(100, 10)` the **sign flips with `ρ`**: refuse at
`ρ = −9/10` (`−49/20`), pay at `ρ = 0` (`98/5`). So the pinned-Ask model's verdict is
`ρ`-dependent while the symmetric model's is not (`Sym2.sign`) — the content of finding F2, which
the package states but never exhibits. Not imported by the library.
-/

namespace Cleanroom.Bli.UdtBliSist.Sym2

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable (w : Fin 4 → ℚ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) (ρ : ℚ) (hρ : |ρ| ≤ 1)
  (c V : ℚ) (r₀ : Bool → ℚ)

/-- With `Ask₂` of mass zero the family satisfies `H_point` at `Ask₁` (the only other Ask table in
the carrier, `Ask₂`, has state mass `w 1 = 0`). -/
theorem hPoint_of_w1_zero (h1 : w 1 = 0) :
    HPoint (symData w hw hw1 ρ hρ c V r₀).toPrior askP fAsk := by
  intro T hT hne
  rcases eq_four T with rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · have h := stateMass_eq w hw hw1 ρ hρ c V r₀ 1
    rw [fourState_one] at h
    rw [h, h1]
  · exact absurd hT not_askP_fRec
  · exact absurd hT not_askP_fOther

/-- The unit Rec term of the family is `w 2 · (1 + ρ)/2`: in the Rec branch Omega's pick lands on
`Ask₁` (bracket `1`) and on `Ask₂` (bracket `ρ`), each with mass `w 2 / 2`. No equal-mass
hypothesis is needed. -/
theorem recTerm_unit_eq :
    recTerm (symData w hw hw1 ρ hρ c V r₀) askP recP symJ fAsk (fun _ => 1) =
      w 2 * ((1 + ρ) / 2) := by
  have hδ1 := pointCorr_ask w hw hw1 ρ hρ c V r₀
  have hδ2 := pointCorr_both w hw hw1 ρ hρ c V r₀
  unfold recTerm
  rw [sum_base, Fintype.sum_prod_type]
  simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, Fin.sum_univ_four, fourState_zero, fourState_one,
    fourState_two, fourState_three, askP_fAsk, askP_fBoth, not_askP_fRec, not_askP_fOther,
    recP_fRec, not_recP_fOther, symJ, Bool.false_eq_true, ↓reduceIte, hδ1, hδ2]
  ring

/-- **The pinned-Ask verdict on the family** (`sist_hpoint` instantiated with `H_point` derived):
`EU Ask₁ give − EU Ask₁ refuse = V·(w 2·(1+ρ)/2) − c·(w 0 + w 1) + w 3·Δr₀`. -/
theorem hpoint_verdict (h1 : w 1 = 0) :
    (symPrior w hw hw1 ρ hρ c V r₀).EU fAsk true - (symPrior w hw hw1 ρ hρ c V r₀).EU fAsk false =
      V * (w 2 * ((1 + ρ) / 2)) - c * (w 0 + w 1) + w 3 * (r₀ true - r₀ false) := by
  unfold symPrior
  rw [sist_hpoint (symData w hw hw1 ρ hρ c V r₀) askP recP symJ fAsk (fun _ b => r₀ b) V c
    (shaped w hw hw1 ρ hρ c V r₀) (by rw [massOf_point]; norm_num) (by rw [massOf_point]; norm_num)
    (hPoint_of_w1_zero w hw hw1 ρ hρ c V r₀ h1) askP_fAsk,
    recTerm_unit_eq, askMass_eq, resTerm_eq]

/-- The masses `(49/100, 0, 49/100, 2/100)`: the source's `49/49/2` with `Ask₂` present but null. -/
def wPin : Fin 4 → ℚ
  | 0 => 49 / 100
  | 1 => 0
  | 2 => 49 / 100
  | 3 => 2 / 100

lemma wPin_nonneg : ∀ s, 0 ≤ wPin s := by intro s; fin_cases s <;> norm_num [wPin]

lemma wPin_sum : ∑ s, wPin s = 1 := by rw [Fin.sum_univ_four]; norm_num [wPin]

lemma negNine_abs : |(-(9 / 10) : ℚ)| ≤ 1 := by
  rw [abs_of_nonpos (by norm_num)]; norm_num

lemma zero_abs : |(0 : ℚ)| ≤ 1 := by simp

/-- **The pinned-Ask sign depends on `ρ`**: at `(49/100, 0, 49/100, 2/100)`, `(100, 10)`, zero
residual, `H_point` holds and `H_unif` fails at both correlations; at `ρ = −9/10` the difference is
`−49/20` and the one-step rule refuses; at `ρ = 0` it is `98/5` and the one-step rule pays. -/
theorem pinned_sign_depends_on_rho :
    HPoint (symPrior wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0))
        askP fAsk ∧
      ¬ HUnif (symPrior wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0))
        askP fAsk ∧
      (symPrior wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0)).EU fAsk true -
          (symPrior wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0)).EU fAsk false =
        -(49 / 20) ∧
      (symPrior wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0)).IsOneStepChoice
        fAsk false ∧
      ¬ (symPrior wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0)).IsOneStepChoice
        fAsk true ∧
      (symPrior wPin wPin_nonneg wPin_sum 0 zero_abs 10 100 (fun _ => 0)).EU fAsk true -
          (symPrior wPin wPin_nonneg wPin_sum 0 zero_abs 10 100 (fun _ => 0)).EU fAsk false =
        98 / 5 ∧
      (symPrior wPin wPin_nonneg wPin_sum 0 zero_abs 10 100 (fun _ => 0)).IsOneStepChoice fAsk true ∧
      (symPrior wPin wPin_nonneg wPin_sum 0 zero_abs 10 100 (fun _ => 0)).EU fAsk false <
        (symPrior wPin wPin_nonneg wPin_sum 0 zero_abs 10 100 (fun _ => 0)).EU fAsk true := by
  have h1 : wPin 1 = 0 := rfl
  have hneg := hpoint_verdict wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0) h1
  have hzero := hpoint_verdict wPin wPin_nonneg wPin_sum 0 zero_abs 10 100 (fun _ => 0) h1
  have hneg' : (symPrior wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0)).EU fAsk true -
      (symPrior wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0)).EU fAsk false =
        -(49 / 20) := by
    rw [hneg]; simp only [wPin]; norm_num
  have hzero' : (symPrior wPin wPin_nonneg wPin_sum 0 zero_abs 10 100 (fun _ => 0)).EU fAsk true -
      (symPrior wPin wPin_nonneg wPin_sum 0 zero_abs 10 100 (fun _ => 0)).EU fAsk false = 98 / 5 := by
    rw [hzero]; simp only [wPin]; norm_num
  refine ⟨hPoint_of_w1_zero wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0) h1,
    not_hUnif wPin wPin_nonneg wPin_sum (-(9 / 10)) negNine_abs 10 100 (fun _ => 0)
      (by norm_num [wPin]) (by norm_num),
    hneg', fun b => ?_, fun h => ?_, hzero', fun b => ?_, by linarith⟩
  · cases b
    · exact le_rfl
    · linarith
  · have := h false
    linarith
  · cases b
    · linarith
    · exact le_rfl

end Cleanroom.Bli.UdtBliSist.Sym2
