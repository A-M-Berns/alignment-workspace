import Cleanroom.Decision.DpEdtUdtFair.Step1

/-!
# Step 2 of FR-11: the support condition passes to `ε → 0` as weak inequalities (T3)

* `value_tremble_eq` — **the polynomial-limit lemma** (mandate representation decision 6): for
  every finite tree `T` and procedure `C`, `V_T(C^ε) = V_T(C) + ε · R(ε)` with `|R| ≤ M` on
  `[0, 1]`, by structural recursion (the tremble weight `(1−ε)C(d)(a) + ε/|A_d|` is affine in
  `ε` at every node). Over any linearly ordered field; no topology.
* `nonneg_of_nonneg_near_zero` — the corollary: a quantity `f₀ + ε R(ε)` that is `≥ 0` on
  `(0, ε₀)` has `f₀ ≥ 0`.
* `FairClass.Q_le_Q_of_eventTremble` — **FR-11 Step 2**: on `𝔉`, event-tremble-EDT-consistency
  gives, at every queried `d` and every supported `a`, `Q_C(d, b) ≤ Q_C(d, a)` for every `b`.
  Only the weak inequalities survive the limit (FR-11: "argmax can shrink in the limit"); the
  argmax itself is not claimed.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ### The polynomial-limit lemma -/

section poly

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- `|x − y| ≤ 1` for `x, y ∈ [0, 1]`.
Source: none: infrastructure
Kind: L -/
theorem abs_sub_le_one_of_unit {x y : K} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |x - y| ≤ 1 :=
  abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- **The polynomial-limit lemma**: `V_T(C^ε) = V_T(C) + ε · R(ε)` with `|R(ε)| ≤ M` on `[0, 1]`,
for every finite tree and procedure, by structural recursion (at a decision node
`C^ε(d)(a) = C(d)(a) + ε (|A_d|⁻¹ − C(d)(a))`).
Source: `fair-repair.md` FR-11 Step 2 ("Leaf probabilities are polynomials in `ε`; let `ε → 0`");
mandate representation decision 6
Kind: P
Fidelity: exact (the remainder form is what the limit step needs; no topology) -/
theorem value_tremble_eq [∀ d, Nonempty (acts d)] (C : Proc ι acts K) :
    (T : Tree Ω ι acts K) →
      ∃ (R : K → K) (M : K), (∀ ε, 0 ≤ ε → ε ≤ 1 → |R ε| ≤ M) ∧
        ∀ ε (h0 : 0 ≤ ε) (h1 : ε ≤ 1), value (tremble C ε h0 h1) T = value C T + ε * R ε
  | leaf ω r => ⟨fun _ => 0, 0, fun _ _ _ => by simp, fun ε _ _ => by simp [DpLocalOpt.value_leaf]⟩
  | chance n β child => by
      choose R M hM hR using fun i => value_tremble_eq C (child i)
      refine ⟨fun ε => ∑ i, β.w i * R i ε, ∑ i, M i, fun ε h0 h1 => ?_, fun ε h0 h1 => ?_⟩
      · calc |∑ i, β.w i * R i ε| ≤ ∑ i, |β.w i * R i ε| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, M i := Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_of_nonneg (β.nonneg i)]
              calc β.w i * |R i ε| ≤ 1 * M i :=
                    mul_le_mul (β.w_le_one i) (hM i ε h0 h1) (abs_nonneg _) zero_le_one
                _ = M i := one_mul _
      · rw [DpLocalOpt.value_chance, DpLocalOpt.value_chance]
        simp only [hR _ ε h0 h1, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
  | decision d child => by
      choose R M hM hR using fun a => value_tremble_eq C (child a)
      set n : K := (Fintype.card (acts d) : K)⁻¹ with hn
      have hn0 : 0 ≤ n := inv_nonneg.mpr (Nat.cast_nonneg _)
      have hn1 : n ≤ 1 := by
        rw [hn]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)
      refine ⟨fun ε => ∑ a, ((n - (C d).w a) * value C (child a) + (C d).w a * R a ε +
          ε * ((n - (C d).w a) * R a ε)),
        ∑ a, (|value C (child a)| + 2 * M a), fun ε h0 h1 => ?_, fun ε h0 h1 => ?_⟩
      · calc |∑ a, ((n - (C d).w a) * value C (child a) + (C d).w a * R a ε +
                ε * ((n - (C d).w a) * R a ε))|
            ≤ ∑ a, |(n - (C d).w a) * value C (child a) + (C d).w a * R a ε +
                ε * ((n - (C d).w a) * R a ε)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a, (|value C (child a)| + 2 * M a) := Finset.sum_le_sum fun a _ => by
              have hw0 := (C d).nonneg a
              have hw1 := (C d).w_le_one a
              have hd1 : |n - (C d).w a| ≤ 1 := abs_sub_le_one_of_unit hn0 hn1 hw0 hw1
              have hRa := hM a ε h0 h1
              have hM0 : 0 ≤ M a := (abs_nonneg _).trans hRa
              calc |(n - (C d).w a) * value C (child a) + (C d).w a * R a ε +
                      ε * ((n - (C d).w a) * R a ε)|
                  ≤ |(n - (C d).w a) * value C (child a)| + |(C d).w a * R a ε| +
                      |ε * ((n - (C d).w a) * R a ε)| := by
                    refine (abs_add_three _ _ _).trans ?_
                    exact le_rfl
                _ ≤ 1 * |value C (child a)| + 1 * M a + 1 * (1 * M a) := by
                    gcongr
                    · rw [abs_mul]
                      exact mul_le_mul hd1 le_rfl (abs_nonneg _) zero_le_one
                    · rw [abs_mul, abs_of_nonneg hw0]
                      exact mul_le_mul hw1 hRa (abs_nonneg _) zero_le_one
                    · rw [abs_mul, abs_of_nonneg h0, abs_mul]
                      exact mul_le_mul h1 (mul_le_mul hd1 hRa (abs_nonneg _) zero_le_one)
                        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
                _ = |value C (child a)| + 2 * M a := by ring
      · rw [DpLocalOpt.value_decision, DpLocalOpt.value_decision]
        simp only [hR _ ε h0 h1, tremble_w, ← hn]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring

omit [Fintype Ω] [DecidableEq Ω] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  [DecidableEq ι] in
/-- **Weak inequalities survive the limit**: if `f₀ + ε R(ε) ≥ 0` for every `ε ∈ (0, ε₀) ∩ (0, 1]`
and `|R| ≤ M` on `[0, 1]`, then `f₀ ≥ 0`. Over any linearly ordered field.
Source: `fair-repair.md` FR-11 Step 2 ("Weak inequalities survive"); mandate representation
decision 6 (corollary)
Kind: P
Fidelity: exact -/
theorem nonneg_of_nonneg_near_zero {f₀ M : K} {R : K → K}
    (hM : ∀ ε, 0 ≤ ε → ε ≤ 1 → |R ε| ≤ M) {ε₀ : K} (hε₀ : 0 < ε₀)
    (h : ∀ ε, 0 < ε → ε ≤ 1 → ε < ε₀ → 0 ≤ f₀ + ε * R ε) : 0 ≤ f₀ := by
  by_contra hneg
  push Not at hneg
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl zero_le_one)
  set ε := min (min (ε₀ / 2) 1) (-f₀ / (2 * (M + 1))) with hε
  have hεpos : 0 < ε :=
    lt_min (lt_min (by linarith) one_pos) (div_pos (by linarith) (by linarith))
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hεε₀ : ε < ε₀ := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hεM : ε * (M + 1) ≤ -f₀ / 2 := by
    have : ε ≤ -f₀ / (2 * (M + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  have hf := h ε hεpos hε1 hεε₀
  have hR : ε * R ε ≤ ε * M :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM ε hεpos.le hε1)) hεpos.le
  have hMM : ε * M ≤ ε * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  linarith

end poly

/-! ### Step 2 on `𝔉` -/

section step2

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- **FR-11 Step 2 (the limit passage)**: on `𝔉`, if `C` is event-tremble-EDT-consistent (D2)
then at every queried `d` and every supported `a` (`C(d)(a) > 0`), `Q_C(d, b) ≤ Q_C(d, a)` for
every `b`. Route: D2 at `ε` (its guard and escape clause discharged by `FairClass.nuPoly_obs_ne_zero`
and `fairClass_escape_never_fires`) compares `𝔼_ε[r ∣ b ∧ O_d] ≤ 𝔼_ε[r ∣ a ∧ O_d]`, Step 1 reads
both as `Q_{C^ε}(d, ·)`, the polynomial-limit lemma writes `Q_{C^ε}(d, a) − Q_{C^ε}(d, b)` as
`(Q_C(d, a) − Q_C(d, b)) + ε R(ε)`, and `nonneg_of_nonneg_near_zero` passes to `ε = 0`. Only weak
inequalities are claimed.
Source: `fair-repair.md` FR-11 Step 2 ("what survives is `Q_C(d, a*) ≥ Q_C(d, a)` for every
`a* ∈ supp C(d)` and every `a`"); `adversary-repair.md` Claim A Step 2
Kind: P
Fidelity: exact
Hyps: (a) `FairClass`, (a) `EventTrembleEdtConsistent` (`dp-calibration`'s D2, unchanged) -/
theorem FairClass.Q_le_Q_of_eventTremble [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C : Proc ι acts K}
    (hC : EventTrembleEdtConsistent obs actEv C B) {d : ι} (hd : d ∈ queried B) (a : acts d)
    (ha : 0 < (C d).w a) (b : acts d) : Q C B d b ≤ Q C B d a := by
  obtain ⟨ε₀, hε₀, hD2⟩ := hC
  obtain ⟨Ra, Ma, hMa, hRa⟩ := value_tremble_eq C (refChildren B d a)
  obtain ⟨Rb, Mb, hMb, hRb⟩ := value_tremble_eq C (refChildren B d b)
  have key : ∀ ε, 0 < ε → ε ≤ 1 → ε < ε₀ →
      0 ≤ (Q C B d a - Q C B d b) + ε * (Ra ε - Rb ε) := by
    intro ε h0 h1 hlt
    have hfull := tremble_fullSupport C ε h0 h1
    obtain ⟨-, hle⟩ := hD2 ε h0 h1 hlt d hd (h.nuPoly_obs_ne_zero C hd)
      (fairClass_escape_never_fires h C ε h0 h1 hd) a ha
    have hb := hle b (h.nu_actEv_inter_obs_pos hfull hd b)
    rw [h.condExp_eq_Q hfull hd a (hfull d a), h.condExp_eq_Q hfull hd b (hfull d b)] at hb
    unfold Q at hb ⊢
    rw [hRa ε h0.le h1, hRb ε h0.le h1] at hb
    linarith
  have := nonneg_of_nonneg_near_zero (R := fun ε => Ra ε - Rb ε) (M := Ma + Mb)
    (fun ε h0 h1 => (abs_sub _ _).trans (add_le_add (hMa ε h0 h1) (hMb ε h0 h1))) hε₀ key
  linarith

end step2

end Cleanroom.Decision.DpEdtUdtFair
