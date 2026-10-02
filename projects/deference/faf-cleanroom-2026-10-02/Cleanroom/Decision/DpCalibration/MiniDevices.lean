import Cleanroom.Decision.DpCalibration.Miniature

/-!
# D2 is empty on the miniature; D4 approves exactly the tie (T16(b))

* `tremble_procQ` — the tremble of a one-point mixture is the mixture `q_ε = (1−ε)q + ε/2`.
* `miniature_not_eventTremble` — **D2 (event-tremble-EDT-consistency) holds for no `procQ q`** on
  the miniature: `v_ε(a) − v_ε(b) = 2 − 3q_ε`; for `q = 1` (`δ_a`) the difference is
  `−1 + 3ε/2 < 0` at every small `ε`, for `q = 0` (`δ_b`) it is `2 − 3ε/2 > 0`, and a mixed support
  needs a tie at *every* small `ε`, which happens at no `q` (two distinct `ε` force `q = ½`, where
  there is no tie) — the faithful `∀ ε₀, ¬ ∀ ε < ε₀` form (dp-cf-001).
* `limitVal_mini` — the tremble-limit act values are `2(1−q)` and `q` at *every* `q ∈ [0, 1]`
  (defined at the boundary too, where the strict values are not).
* `miniature_adviceEdt_iff` — **D4 approves exactly `q = 2/3`**: uniqueness for the tremble-limit
  evaluator, the reading on which Remark 4.3 is right (CA-13′).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ## Trembles of one-point mixtures -/

/-- The trembled mixture `q_ε := (1 − ε) q + ε/2` is in `[0, 1]`. Source: none: infrastructure.
Kind: L -/
theorem qeps_mem (q ε : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    0 ≤ (1 - ε) * q + ε / 2 ∧ (1 - ε) * q + ε / 2 ≤ 1 := by
  constructor <;> nlinarith

/-- **The tremble of `procQ q` is `procQ q_ε`**, `q_ε = (1−ε)q + ε/2` (`|A_d| = 2`).
Source: `calibration.md` CA-14′ (`q_ε = (1−ε)q + ε/2`)
Kind: L -/
theorem tremble_procQ (q ε : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    tremble (procQ q hq0 hq1) ε h0 h1 =
      procQ ((1 - ε) * q + ε / 2) (qeps_mem q ε hq0 hq1 h0 h1).1 (qeps_mem q ε hq0 hq1 h0 h1).2 := by
  funext u; cases u
  apply FinDistr.ext'
  intro a
  cases a <;> simp [tremble_w, procQ, Act2.univ_eq, Fintype.card] <;> ring

/-- `q_ε ∈ (0, 1)` for `ε ∈ (0, 1)`. Source: none: infrastructure. Kind: L -/
theorem qeps_interior (q ε : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : 0 < ε) (h1 : ε < 1) :
    0 < (1 - ε) * q + ε / 2 ∧ (1 - ε) * q + ε / 2 < 1 := by
  constructor <;> nlinarith

/-- The strict act values of `procQ r` on the miniature as `condExp`, for interior `r`.
Source: `calibration.md` CA-14′ (`v_ε(a) = 2(1 − q_ε)`, `v_ε(b) = q_ε`)
Kind: L -/
theorem miniature_condExp (r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    condExp (procQ r h0.le h1.le) miniature (miniActEv () .a ∩ miniObs ()) = 2 * (1 - r) ∧
    condExp (procQ r h0.le h1.le) miniature (miniActEv () .b ∩ miniObs ()) = r := by
  simp only [condExp, miniObs, Finset.inter_univ, miniature_nu_live, miniature_paySum_live_a,
    miniature_paySum_live_b, procQ, FinDistr.act2_a, FinDistr.act2_b]
  have : (1 - r) ≠ 0 := by linarith
  constructor <;> field_simp

/-- `d = ()` is queried on the miniature. Source: none: infrastructure. Kind: L -/
theorem miniature_queried : () ∈ queried miniature := by
  unfold miniature; simp [queried_decision]

/-- `nuPoly ⊤ ≠ 0` on the miniature. Source: none: infrastructure. Kind: L -/
theorem miniature_nuPoly_obs_ne_zero (C : Proc Unit (fun _ => Act2) ℚ) :
    nuPoly C miniature (miniObs ()) ≠ 0 := by
  rw [nuPoly_ne_zero_iff]
  refine ⟨⟨.a, .a, ()⟩, by simp [miniObs], ?_⟩
  unfold miniature; simp [chanceWeight]

/-- **D2 is empty on the miniature** (CA-14′, DY-2): no `procQ q` is event-tremble-EDT-consistent.
Given any `ε₀ > 0`, some `ε < ε₀` violates the condition: for `δ_a` and `δ_b` every small `ε`
does (`v_ε(a) − v_ε(b) = 2 − 3q_ε` has the wrong sign), and a mixed `q` would need `q_ε = 2/3` at
two distinct `ε`, forcing `q = ½`, where `q_ε = ½ ≠ 2/3`.
Source: `cf-workflow/phase2-notes/repair/calibration.md` CA-14′; `dynamic.md` DY-2 ("no procedure
is fixed-form tremble-EDT-consistent on v2's own miniature")
Kind: P
Fidelity: exact (the faithful `∀ ε₀, ¬ ∀ ε < ε₀` form; N− in the sense that the device is
*empty*, which is the finding)
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem miniature_not_eventTremble (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ¬ EventTrembleEdtConsistent miniObs miniActEv (procQ q hq0 hq1) miniature := by
  rintro ⟨ε₀, hε₀, hD2⟩
  -- the comparison at a given `ε`, for `a` in the support and `b` any act
  have key : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε < 1), ε < ε₀ → ∀ a, 0 < (procQ q hq0 hq1 ()).w a →
      ∀ b, condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) miniature
          (miniActEv () b ∩ miniObs ()) ≤
        condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) miniature
          (miniActEv () a ∩ miniObs ()) := by
    intro ε h0 h1 hlt a ha b
    -- both action events are realized within `O = ⊤` under every interior tremble, so
    -- Definition 18's escape clause does not fire on the miniature
    have hlive : ∀ b, 0 < nu (tremble (procQ q hq0 hq1) ε h0.le h1.le) miniature
        (miniActEv () b ∩ miniObs ()) := by
      intro b
      rw [tremble_procQ, miniObs, Finset.inter_univ, miniature_nu_live]
      obtain ⟨hi0, hi1⟩ := qeps_interior q ε hq0 hq1 h0 h1
      cases b <;> simp [procQ] <;> linarith
    obtain ⟨-, hcmp⟩ := hD2 ε h0 h1.le hlt () miniature_queried
      (miniature_nuPoly_obs_ne_zero _) ⟨.a, hlive .a⟩ a ha
    exact hcmp b (hlive b)
  -- the values at `ε`
  have vals : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε < 1),
      condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) miniature
          (miniActEv () .a ∩ miniObs ()) = 2 * (1 - ((1 - ε) * q + ε / 2)) ∧
      condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) miniature
          (miniActEv () .b ∩ miniObs ()) = (1 - ε) * q + ε / 2 := by
    intro ε h0 h1
    rw [tremble_procQ]
    obtain ⟨hi0, hi1⟩ := qeps_interior q ε hq0 hq1 h0 h1
    exact miniature_condExp _ hi0 hi1
  -- two small trembles
  set ε₁ : ℚ := min ε₀ 1 / 2 with hε₁
  set ε₂ : ℚ := min ε₀ 1 / 4 with hε₂
  have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
  have hmin1 : min ε₀ 1 ≤ 1 := min_le_right _ _
  have hmin2 : min ε₀ 1 ≤ ε₀ := min_le_left _ _
  have h10 : 0 < ε₁ := by rw [hε₁]; linarith
  have h11 : ε₁ < 1 := by rw [hε₁]; linarith
  have h1lt : ε₁ < ε₀ := by rw [hε₁]; linarith
  have h20 : 0 < ε₂ := by rw [hε₂]; linarith
  have h21 : ε₂ < 1 := by rw [hε₂]; linarith
  have h2lt : ε₂ < ε₀ := by rw [hε₂]; linarith
  have hne : ε₁ ≠ ε₂ := by rw [hε₁, hε₂]; intro h; linarith
  obtain ⟨va1, vb1⟩ := vals ε₁ h10 h11
  obtain ⟨va2, vb2⟩ := vals ε₂ h20 h21
  rcases (lt_or_eq_of_le hq0) with hpos | hzero
  · rcases (lt_or_eq_of_le hq1) with hlt1 | hone
    · -- mixed support: ties at both `ε₁` and `ε₂`
      have ha1 := key ε₁ h10 h11 h1lt .a (by simp [procQ, hpos]) .b
      have hb1 := key ε₁ h10 h11 h1lt .b (by simp [procQ]; linarith) .a
      have ha2 := key ε₂ h20 h21 h2lt .a (by simp [procQ, hpos]) .b
      have hb2 := key ε₂ h20 h21 h2lt .b (by simp [procQ]; linarith) .a
      rw [va1, vb1] at ha1 hb1
      rw [va2, vb2] at ha2 hb2
      have t1 : (1 - ε₁) * q + ε₁ / 2 = 2 / 3 := by linarith
      have t2 : (1 - ε₂) * q + ε₂ / 2 = 2 / 3 := by linarith
      have hq : q = 1 / 2 := by
        have : (ε₂ - ε₁) * (q - 1 / 2) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (by linarith : ε₁ = ε₂) hne
        · linarith
      rw [hq] at t1
      linarith
    · -- `q = 1`, support `{a}`: needs `q_ε ≤ 2/3`, but `q_ε = 1 − ε/2 > 2/3`
      subst hone
      have ha1 := key ε₁ h10 h11 h1lt .a (by simp [procQ]) .b
      rw [va1, vb1] at ha1
      linarith
  · -- `q = 0`, support `{b}`: needs `q_ε ≥ 2/3`, but `q_ε = ε/2 < 2/3`
    subst hzero
    have hb1 := key ε₁ h10 h11 h1lt .b (by simp [procQ]) .a
    rw [va1, vb1] at hb1
    linarith

/-- Every procedure on a one-point `Act2` tree is a `procQ`. Source: none: infrastructure.
Kind: L -/
theorem eq_procQ (C : Proc Unit (fun _ => Act2) ℚ) :
    C = procQ ((C ()).w .a) ((C ()).nonneg _)
      (by have := (C ()).sum_one; rw [Act2.sum_univ] at this; linarith [(C ()).nonneg .b]) := by
  have hsum := (C ()).sum_one
  rw [Act2.sum_univ] at hsum
  funext d
  cases d
  apply FinDistr.ext'
  intro a
  cases a
  · rfl
  · show (C ()).w .b = 1 - (C ()).w .a
    linarith

/-- **D2 is empty on the miniature, for every procedure** (the "no procedure" form findings F5
asserts): every `Proc Unit (fun _ => Act2) ℚ` is a `procQ`.
Source: `cf-workflow/phase2-notes/repair/calibration.md` CA-14′; `dynamic.md` DY-2
Kind: P
Fidelity: exact
Hyps: none -/
theorem miniature_not_eventTremble_all (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ EventTrembleEdtConsistent miniObs miniActEv C miniature := by
  rw [eq_procQ C]
  exact miniature_not_eventTremble _ _ _

/-! ## The tremble-limit act values -/

/-- `∑_a trembleW C d a = 1`: the tremble weights sum to one identically in `ε`.
Source: none: infrastructure. Kind: L -/
theorem sum_trembleW {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, Nonempty (acts d)]
    (C : Proc ι acts K) (d : ι) : ∑ a, trembleW C d a = 1 := by
  unfold trembleW
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum, ← map_sum, (C d).sum_one,
    Finset.sum_sub_distrib, (C d).sum_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (acts d) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_inv_cancel₀ this, sub_self, map_zero, zero_mul, add_zero, Polynomial.C_1]

/-- The order of a polynomial from its coefficients. Source: none: infrastructure. Kind: L -/
theorem natTrailingDegree_eq_of_coeff {K : Type} [Field K] (p : Polynomial K) (k : ℕ)
    (hlow : ∀ j < k, p.coeff j = 0) (hk : p.coeff k ≠ 0) : p.natTrailingDegree = k := by
  have hne : p ≠ 0 := fun h => hk (by rw [h, Polynomial.coeff_zero])
  exact le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hk)
    (Polynomial.le_natTrailingDegree hne hlow)

/-- `trembleW (procQ q) a` as an explicit affine polynomial. Source: none: infrastructure.
Kind: L -/
theorem trembleW_procQ (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    trembleW (procQ q h0 h1) () .a = Polynomial.C q + Polynomial.C (1/2 - q) * Polynomial.X ∧
    trembleW (procQ q h0 h1) () .b =
      Polynomial.C (1 - q) + Polynomial.C (q - 1/2) * Polynomial.X := by
  have hc : (Fintype.card Act2 : ℚ) = 2 := by
    rw [Fintype.card, Act2.univ_eq, Finset.card_pair (by decide)]; norm_num
  simp only [trembleW, procQ, FinDistr.act2_a, FinDistr.act2_b, hc]
  constructor
  · rw [show ((2 : ℚ)⁻¹ - q) = 1 / 2 - q by norm_num]
  · rw [show ((2 : ℚ)⁻¹ - (1 - q)) = q - 1 / 2 by ring]

/-- `nuPoly` as an indicator sum over all leaves. Source: none: infrastructure. Kind: L -/
theorem nuPoly_eq_sum {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Ω ι : Type} [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] [∀ d, Nonempty (acts d)] (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (X : Finset Ω) :
    nuPoly C B X = ∑ ℓ, if world B ℓ ∈ X then leafLawPoly C B ℓ else 0 := by
  unfold nuPoly worldEv; rw [Finset.sum_filter]

/-- `payPoly` as an indicator sum over all leaves. Source: none: infrastructure. Kind: L -/
theorem payPoly_eq_sum {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Ω ι : Type} [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] [∀ d, Nonempty (acts d)] (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (X : Finset Ω) :
    payPoly C B X =
      ∑ ℓ, if world B ℓ ∈ X then leafLawPoly C B ℓ * Polynomial.C (payoff B ℓ) else 0 := by
  unfold payPoly worldEv; rw [Finset.sum_filter]

/-- `nuPoly` of a live-draw event on the miniature is the tremble weight of that act.
Source: none: infrastructure. Kind: L -/
theorem nuPoly_mini_live (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    nuPoly C miniature (miniActEv () a) = trembleW C () a := by
  have hs : trembleW C () .a + trembleW C () .b = 1 := by
    have h1 := (C ()).sum_one
    rw [Act2.sum_univ] at h1
    have hc : (Fintype.card Act2 : ℚ) = 2 := by
      rw [Fintype.card, Act2.univ_eq, Finset.card_pair (by decide)]; norm_num
    simp only [trembleW, hc]
    ext n
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_one]
    rcases n with _ | _ | n
    · simp; linarith
    · simp; linarith
    · simp
  rw [nuPoly_eq_sum, miniature_sum]
  simp only [Act2.sum_univ]
  simp only [miniature, miniActEv, world_decision, world_leaf, leafLawPoly, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases a
  · simp
    linear_combination (trembleW C () Act2.a) * hs
  · simp
    linear_combination (trembleW C () Act2.b) * hs

/-- `payPoly` of the live-`a` event: `2 · trembleW b · trembleW a`. Source: none: infrastructure.
Kind: L -/
theorem payPoly_mini_live_a (C : Proc Unit (fun _ => Act2) ℚ) :
    payPoly C miniature (miniActEv () .a) =
      Polynomial.C 2 * (trembleW C () .b * trembleW C () .a) := by
  rw [payPoly_eq_sum, miniature_sum]
  simp only [Act2.sum_univ]
  simp only [miniature, miniActEv, world_decision, world_leaf, payoff_decision, payoff_leaf,
    leafLawPoly, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [miniPay]
  ring

/-- `payPoly` of the live-`b` event: `trembleW a · trembleW b`. Source: none: infrastructure.
Kind: L -/
theorem payPoly_mini_live_b (C : Proc Unit (fun _ => Act2) ℚ) :
    payPoly C miniature (miniActEv () .b) = trembleW C () .a * trembleW C () .b := by
  rw [payPoly_eq_sum, miniature_sum]
  simp only [Act2.sum_univ]
  simp only [miniature, miniActEv, world_decision, world_leaf, payoff_decision, payoff_leaf,
    leafLawPoly, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [miniPay]

/-- Coefficients `0` and `1` of an affine polynomial `C a + C b * X`. Source: none: infrastructure.
Kind: L -/
theorem coeff_affine (a b : ℚ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).coeff 0 = a ∧
    (Polynomial.C a + Polynomial.C b * Polynomial.X).coeff 1 = b := by
  constructor <;> simp [Polynomial.coeff_add, Polynomial.coeff_C]

/-- **The tremble-limit act values on the miniature are `2(1−q)` and `q` at every
`q ∈ [0, 1]`** — the D4 values, defined at the boundary where the strict values are not
(at `q = 1` the act `b` has limit probability `0` but limit value `1`).
Source: `calibration.md` CA-13′ ("D4: `2(1−q)` and `q` defined at every `q`")
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem limitVal_mini (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    limitVal (procQ q h0 h1) miniature (miniActEv () .a ∩ miniObs ()) = 2 * (1 - q) ∧
    limitVal (procQ q h0 h1) miniature (miniActEv () .b ∩ miniObs ()) = q := by
  obtain ⟨hta, htb⟩ := trembleW_procQ q h0 h1
  simp only [limitVal, miniObs, Finset.inter_univ, nuPoly_mini_live, payPoly_mini_live_a,
    payPoly_mini_live_b, hta, htb]
  constructor
  · rcases (lt_or_eq_of_le h0) with hpos | hzero
    · -- order 0
      have hdeg : (Polynomial.C q + Polynomial.C (1/2 - q) * Polynomial.X).natTrailingDegree = 0 :=
        natTrailingDegree_eq_of_coeff _ 0 (fun j hj => absurd hj (Nat.not_lt_zero j))
          (by rw [(coeff_affine q _).1]; exact hpos.ne')
      rw [hdeg, (coeff_affine q _).1, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero,
        Polynomial.coeff_C_zero, (coeff_affine (1 - q) _).1, (coeff_affine q _).1]
      field_simp
    · -- `q = 0`: order 1
      subst hzero
      have e : Polynomial.C (0 : ℚ) + Polynomial.C (1/2 - 0) * Polynomial.X =
          Polynomial.C (1/2 : ℚ) * Polynomial.X := by simp
      rw [e]
      have hdeg : (Polynomial.C (1/2 : ℚ) * Polynomial.X).natTrailingDegree = 1 :=
        natTrailingDegree_eq_of_coeff _ 1
          (fun j hj => by
            have : j = 0 := by omega
            subst this; simp)
          (by simp)
      rw [hdeg]
      have e2 : Polynomial.C (2 : ℚ) * ((Polynomial.C (1 - 0) + Polynomial.C (0 - 1/2) * Polynomial.X) *
          (Polynomial.C (1/2 : ℚ) * Polynomial.X)) =
          (Polynomial.C (2 : ℚ) * (Polynomial.C (1 - 0) + Polynomial.C (0 - 1/2) * Polynomial.X) *
            Polynomial.C (1/2 : ℚ)) * Polynomial.X := by ring
      rw [e2, Polynomial.coeff_mul_X, Polynomial.coeff_C_mul_X, Polynomial.mul_coeff_zero,
        Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, Polynomial.coeff_C_zero,
        (coeff_affine (1 - 0) _).1]
      norm_num
  · rcases (lt_or_eq_of_le h1) with hlt | hone
    · -- order 0
      have hdeg : (Polynomial.C (1 - q) + Polynomial.C (q - 1/2) * Polynomial.X).natTrailingDegree
          = 0 :=
        natTrailingDegree_eq_of_coeff _ 0 (fun j hj => absurd hj (Nat.not_lt_zero j))
          (by rw [(coeff_affine (1 - q) _).1]; linarith)
      rw [hdeg, (coeff_affine (1 - q) _).1, Polynomial.mul_coeff_zero,
        (coeff_affine q _).1, (coeff_affine (1 - q) _).1]
      have : (1 - q) ≠ 0 := by linarith
      field_simp
    · -- `q = 1`: order 1
      subst hone
      have e : Polynomial.C (1 - 1 : ℚ) + Polynomial.C (1 - 1/2) * Polynomial.X =
          Polynomial.C (1/2 : ℚ) * Polynomial.X := by norm_num
      rw [e]
      have hdeg : (Polynomial.C (1/2 : ℚ) * Polynomial.X).natTrailingDegree = 1 :=
        natTrailingDegree_eq_of_coeff _ 1
          (fun j hj => by
            have : j = 0 := by omega
            subst this; simp)
          (by simp)
      rw [hdeg]
      have e2 : (Polynomial.C (1 : ℚ) + Polynomial.C (1/2 - 1) * Polynomial.X) *
          (Polynomial.C (1/2 : ℚ) * Polynomial.X) =
          ((Polynomial.C (1 : ℚ) + Polynomial.C (1/2 - 1) * Polynomial.X) * Polynomial.C (1/2 : ℚ)) *
            Polynomial.X := by ring
      rw [e2, Polynomial.coeff_mul_X, Polynomial.coeff_C_mul_X, Polynomial.mul_coeff_zero,
        Polynomial.coeff_C_zero, (coeff_affine 1 _).1]
      norm_num

/-- `nuPoly` of a live-draw event on the miniature is non-zero (realized). Source: none:
infrastructure. Kind: L -/
theorem nuPoly_mini_live_ne_zero (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    nuPoly C miniature (miniActEv () a ∩ miniObs ()) ≠ 0 := by
  rw [miniObs, Finset.inter_univ, nuPoly_mini_live]
  exact trembleW_ne_zero C () a

/-- **D4 approves exactly `q = 2/3` on the miniature**: the advice-stance evaluator, with the
tremble-limit values `2(1−q)` and `q` defined at every `q`, approves `procQ q` iff `q = 2/3` —
uniqueness holds for the tremble-limit evaluator (CA-13′'s second half; closes T15(b)).
Source: `calibration.md` CA-13′ ("Uniqueness (`q = 2/3`) holds when the act values are read as
tremble limits (D4)"); CA-14′ ("D4 = {2/3}")
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem miniature_adviceEdt_iff (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    AdviceEdt miniObs miniActEv (procQ q h0 h1) miniature ↔ q = 2 / 3 := by
  obtain ⟨hva, hvb⟩ := limitVal_mini q h0 h1
  constructor
  · intro h
    have hq := h () miniature_queried (miniature_nuPoly_obs_ne_zero _)
      ⟨.a, nuPoly_mini_live_ne_zero _ _⟩
    rcases (lt_or_eq_of_le h0) with hpos | hzero
    · have ha := (hq .a (by simp [procQ, hpos])).2 .b (nuPoly_mini_live_ne_zero _ _)
      rw [hva, hvb] at ha
      rcases (lt_or_eq_of_le h1) with hlt | hone
      · have hb := (hq .b (by simp [procQ]; linarith)).2 .a (nuPoly_mini_live_ne_zero _ _)
        rw [hva, hvb] at hb
        linarith
      · subst hone; linarith
    · subst hzero
      have hb := (hq .b (by simp [procQ])).2 .a (nuPoly_mini_live_ne_zero _ _)
      rw [hva, hvb] at hb
      linarith
  · rintro rfl
    intro d _ _ _ a _
    cases d
    refine ⟨nuPoly_mini_live_ne_zero _ _, fun b _ => ?_⟩
    cases a <;> cases b <;> simp only [hva, hvb] <;> norm_num

end Cleanroom.Decision.DpCalibration
