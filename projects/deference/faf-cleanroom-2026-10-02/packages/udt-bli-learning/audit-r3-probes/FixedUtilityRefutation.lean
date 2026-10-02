import Cleanroom.Bli.UdtBliLearning.EpsCorrWitness

/-!
# Audit r3 (adversarial) probe · FixedUtilityRefutation: the exact asymptotic clause is false
even when the utility is held fixed and only the belief law varies

`EpsCorrWitness.not_exactAsymptoticClause` refutes `ExactAsymptoticClause witIndex 1 twoTables
Bool 2` with the family `xPrior n = vPrior (1/(2(n+1))) (1/(n+1))`, whose **utility** `vU g_n b_n`
changes with `n` (the base law `tfMass`, state map and points are constant). A sequence of
`FiniteBLIPrior`s in which the utility moves is not a *belief*-state sequence of one agent facing
one environment; the question this probe answers is whether the refutation is an artifact of that
freedom (STANDARDS §3: "impossibility results get a check that the impossibility isn't an artifact
of the encoding").

It is not. Here the utility `yU` is one fixed function of the world, and only the prior over a
hidden coordinate `h` moves: worlds are `(state, pp·T1, pp·T2, h)`, the law is uniform on the
first three coordinates and puts mass `p` on `h = true`;

`yU ω = [state = T1] · (if pp·T1 then 0 else [h]) + [state = T2] · (if pp·T1 then 2[h] else 0)`.

Computed for every `p ∈ [0, 1]`: branch probabilities all `1/2`; `homeEU T1 = (0, p)` (own gap `p`);
`condEU T2 T1 = (2p, 0)` (cross correlation `2p`); `condEU T1 T2 · = p/2`; `EU T1 = (p, p/2)`. So
with `p_n = 1/(n+2) → 0`: every hypothesis of the clause holds (`ε_n = 2p_n → 0`, `M = 2`,
`ρ = 1/2`, positive points, `CorrBounded` at both realized tables) while `pay` at `T1` is a
one-step choice and not an updateful one at every `n`. The refutation stands with the utility
fixed; the shipped family's moving utility is a convenience, not the mechanism.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning.AuditR3

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

/-- Worlds: `(state, pp·T1, pp·T2, hidden)`. -/
abbrev Ω4 : Type := Fin 2 × Bool × Bool × Bool

/-- The base law: uniform on `(state, pp·T1, pp·T2)`, mass `p` on `hidden = true`. -/
def yMass (p : ℚ) : Ω4 → ℚ := fun ω => (1 / 8) * (if ω.2.2.2 then p else 1 - p)

/-- The points: coordinate 1 at `T1`, coordinate 2 at `T2` (as `tfPP`). -/
def yPP (ω : Ω4) : Policy twoTables Bool := fun T => if T = T1 then ω.2.1 else ω.2.2.1

/-- **The fixed utility** (no parameter): `T1`'s branch pays `1` for `refuse` when the hidden
coordinate is true; `T2`'s branch pays `2` when `T1`'s point is `pay` and the hidden coordinate is
true. -/
def yU : Ω4 → ℚ := fun ω =>
  if ω.1 = 0 then (if ω.2.1 then 0 else (if ω.2.2.2 then 1 else 0))
  else (if ω.2.1 then (if ω.2.2.2 then 2 else 0) else 0)

lemma yMass_nonneg (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (ω : Ω4) : 0 ≤ yMass p ω := by
  unfold yMass
  split_ifs
  · exact mul_nonneg (by norm_num) h0
  · exact mul_nonneg (by norm_num) (by linarith)

lemma yMass_sum (p : ℚ) : ∑ ω : Ω4, yMass p ω = 1 := by
  simp [yMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
  ring

/-- The prior with hidden-coordinate mass `p`: the utility `yU` does not depend on `p`. -/
def yPrior (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior Ω4 (yMass p) (yMass_nonneg p h0 h1) (yMass_sum p) (fun ω => twoState ω.1) two_zeroOne
    yPP yU

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1)

/-- The utility of `yPrior p` is `yU`, for every `p` — fixed along the family. -/
theorem yPrior_U : (yPrior p h0 h1).U = yU := rfl

lemma y_ppMass (T : ↥twoTables) (a : Bool) : (yPrior p h0 h1).ppMass T a = 1 / 2 := by
  change massOf (yMass p) (fun ω : Ω4 => yPP ω T = a) = 1 / 2
  rcases eq_T1_or_T2 T with rfl | rfl <;>
  · unfold massOf yMass yPP
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    cases a <;> simp [T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec] <;> ring

lemma y_jointMass (T' T : ↥twoTables) (a : Bool) : (yPrior p h0 h1).jointMass T' T a = 1 / 4 := by
  change massOf (yMass p) (fun ω : Ω4 => twoState ω.1 = T' ∧ yPP ω T = a) = 1 / 4
  rcases eq_T1_or_T2 T with rfl | rfl <;> rcases eq_T1_or_T2 T' with rfl | rfl <;>
  · unfold massOf yMass yPP
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    cases a <;> simp [twoState_zero, twoState_one, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec,
      mAsk_ne_mRec] <;> ring

lemma y_branchProb (T' T : ↥twoTables) (a : Bool) : (yPrior p h0 h1).branchProb T' T a = 1 / 2 := by
  unfold FiniteBLIPrior.branchProb
  rw [y_jointMass, y_ppMass]
  norm_num

/-- `T2`'s value given `T1`'s point: `2p` for `pay`, `0` for `refuse` — the cross correlation. -/
lemma y_condEU_T2_T1 :
    (yPrior p h0 h1).condEU T2 T1 true = 2 * p ∧ (yPrior p h0 h1).condEU T2 T1 false = 0 := by
  constructor <;>
  · change condExp (yMass p) yU (fun ω : Ω4 => twoState ω.1 = T2 ∧ yPP ω T1 = _) = _
    unfold condExp massOf integralOf yMass yPP yU
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    simp [twoState_zero, twoState_one, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    try ring_nf
    try field_simp
    try ring

/-- `T1`'s value given `T2`'s point: `p/2` either way. -/
lemma y_condEU_T1_T2 (a : Bool) : (yPrior p h0 h1).condEU T1 T2 a = p / 2 := by
  cases a <;>
  · change condExp (yMass p) yU (fun ω : Ω4 => twoState ω.1 = T1 ∧ yPP ω T2 = _) = _
    unfold condExp massOf integralOf yMass yPP yU
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    simp [twoState_zero, twoState_one, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    try ring_nf
    try field_simp
    try ring

/-- Home values at `T1`: `pay ↦ 0`, `refuse ↦ p` — the own gap `p`. -/
lemma y_homeEU_T1 :
    (yPrior p h0 h1).homeEU T1 true = 0 ∧ (yPrior p h0 h1).homeEU T1 false = p := by
  constructor <;>
  · change condExp (yMass p) yU (fun ω : Ω4 => twoState ω.1 = T1 ∧ yPP ω T1 = _) = _
    unfold condExp massOf integralOf yMass yPP yU
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    simp [twoState_zero, twoState_one, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    try ring_nf
    try field_simp
    try ring

/-- Home values at `T2`: `p` either way (a tie). -/
lemma y_homeEU_T2 (a : Bool) : (yPrior p h0 h1).homeEU T2 a = p := by
  cases a <;>
  · change condExp (yMass p) yU (fun ω : Ω4 => twoState ω.1 = T2 ∧ yPP ω T2 = _) = _
    unfold condExp massOf integralOf yMass yPP yU
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    simp [twoState_zero, twoState_one, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    try ring_nf
    try field_simp
    try ring

/-- One-step values at `T1`: `pay ↦ p`, `refuse ↦ p/2`. -/
lemma y_EU_T1 : (yPrior p h0 h1).EU T1 true = p ∧ (yPrior p h0 h1).EU T1 false = p / 2 := by
  constructor <;>
  · change condExp (yMass p) yU (fun ω : Ω4 => yPP ω T1 = _) = _
    unfold condExp massOf integralOf yMass yPP yU
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
    simp [twoState_zero, twoState_one, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]
    try ring_nf
    try field_simp
    try ring

/-- `CorrBounded (yPrior p) T (2p)` at both tables. -/
lemma y_corrBounded (T : ↥twoTables) : CorrBounded (yPrior p h0 h1) T (2 * p) := by
  refine ⟨fun T' c d => ?_, fun T' c d hne _ _ => ?_⟩
  · rw [y_branchProb, y_branchProb]; simp; linarith
  · rcases eq_T1_or_T2 T with rfl | rfl <;> rcases eq_T1_or_T2 T' with rfl | rfl
    · exact absurd rfl hne
    · obtain ⟨hp, hr⟩ := y_condEU_T2_T1 p h0 h1
      cases c <;> cases d <;> simp only [hp, hr]
      · simp; linarith
      · rw [zero_sub, abs_neg, abs_of_nonneg (by linarith)]
      · rw [sub_zero, abs_of_nonneg (by linarith)]
      · simp; linarith
    · rw [y_condEU_T1_T2, y_condEU_T1_T2]; simp; linarith
    · exact absurd rfl hne

lemma y_U_bound (ω : Ω4) : |(yPrior p h0 h1).U ω| ≤ 2 := by
  show |yU ω| ≤ 2
  unfold yU
  split_ifs <;> norm_num

/-- For `0 < p`: `pay` is a one-step choice at `T1` and not an updateful one. -/
lemma y_pay_oneStep_not_updateful (hp : 0 < p) :
    (yPrior p h0 h1).IsOneStepChoice T1 true ∧ ¬ (yPrior p h0 h1).IsUpdatefulChoice T1 true := by
  obtain ⟨e1, e0⟩ := y_EU_T1 p h0 h1
  obtain ⟨g1, g0⟩ := y_homeEU_T1 p h0 h1
  constructor
  · intro b; cases b
    · rw [e0, e1]; linarith
    · exact le_rfl
  · intro h; have := h false; rw [g1, g0] at this; linarith

/-! ## The family with the fixed utility: `p_n = 1/(n+2)` -/

lemma pn_nonneg (n : ℕ) : (0 : ℚ) ≤ 1 / ((n : ℚ) + 2) := by positivity

lemma pn_le_one (n : ℕ) : 1 / ((n : ℚ) + 2) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]

lemma pn_pos (n : ℕ) : (0 : ℚ) < 1 / ((n : ℚ) + 2) := by positivity

/-- **The fixed-utility family**: the same `yU` at every `n`; only the hidden coordinate's mass
`1/(n+2)` moves. -/
def zPrior (n : ℕ) : FiniteBLIPrior witIndex 1 twoTables Bool :=
  yPrior (1 / ((n : ℚ) + 2)) (pn_nonneg n) (pn_le_one n)

/-- The utility is literally the same function at every stage. -/
theorem zPrior_U_fixed (n n' : ℕ) : (zPrior n).U = (zPrior n').U := rfl

/-- The state map and the points are the same at every stage. -/
theorem zPrior_state_pp_fixed (n n' : ℕ) :
    (zPrior n).state = (zPrior n').state ∧ (zPrior n).pp = (zPrior n').pp := ⟨rfl, rfl⟩

lemma lim_two_inv : ∀ η : ℚ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 * (1 / ((n : ℚ) + 2)) ≤ η := by
  intro η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / η)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℚ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℚ) < (n : ℚ) + 2 := by positivity
  rw [mul_one_div, div_le_iff₀ hpos]
  have h : 2 / η < (n : ℚ) + 2 := by linarith
  rw [div_lt_iff₀ hη] at h
  linarith

/-- The hypothesis package of `ExactAsymptoticClause` on the fixed-utility family. -/
theorem z_package :
    (∀ n : ℕ, (0 : ℚ) ≤ 2 * (1 / ((n : ℚ) + 2))) ∧
    (∀ η : ℚ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 * (1 / ((n : ℚ) + 2)) ≤ η) ∧
    (∀ n (k : Fin 2) c, 0 < (zPrior n).ppMass (twoState k) c) ∧
    (∀ n (k : Fin 2), CorrBounded (zPrior n) (twoState k) (2 * (1 / ((n : ℚ) + 2)))) ∧
    (∀ n ω, |(zPrior n).U ω| ≤ 2) ∧
    (∀ n (k : Fin 2) a, (zPrior n).IsOneStepChoice (twoState k) a →
      (1 : ℚ) / 2 ≤ (zPrior n).branchProb (twoState k) (twoState k) a) := by
  refine ⟨fun n => by positivity, lim_two_inv, fun n k c => ?_, fun n k => ?_, fun n ω => ?_,
    fun n k a _ => ?_⟩
  · show 0 < (yPrior _ _ _).ppMass _ _; rw [y_ppMass]; norm_num
  · exact y_corrBounded _ _ _ _
  · exact y_U_bound _ _ _ ω
  · show (1 : ℚ) / 2 ≤ (yPrior _ _ _).branchProb _ _ _; rw [y_branchProb]

/-- **The exact asymptotic clause is false with the utility held fixed**: on `zPrior` every
hypothesis holds and `pay` at `T1` is one-step but never updateful. -/
theorem fixedU_not_exactAsymptoticClause : ¬ ExactAsymptoticClause witIndex 1 twoTables Bool 2 := by
  intro h
  obtain ⟨hε0, hlim, hpol, hcorr, hU, hρa⟩ := z_package
  obtain ⟨N, hN⟩ := h zPrior twoState (fun n => 2 * (1 / ((n : ℚ) + 2))) 2 (1 / 2) (by norm_num)
    (by norm_num) hε0 hlim hpol hcorr hU hρa
  obtain ⟨hone, hnot⟩ := y_pay_oneStep_not_updateful _ (pn_nonneg N) (pn_le_one N) (pn_pos N)
  exact hnot (hN N le_rfl 0 true hone)

end Cleanroom.Bli.UdtBliLearning.AuditR3
