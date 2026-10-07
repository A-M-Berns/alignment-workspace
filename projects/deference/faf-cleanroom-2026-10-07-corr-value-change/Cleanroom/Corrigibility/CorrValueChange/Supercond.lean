import Cleanroom.Corrigibility.CorrValueChange.Update
import Cleanroom.Corrigibility.CorrValueChange.Model

/-!
# corr-value-change — radical probabilism and superconditioning, finite (T12 (b), (c), (e), (f), (g), (h))

Source: [[value-change-as-epistemic-update]] §6.2–6.5. A single transition `P₀ → Q` on a finite
`W`; an update law `(π_i, Q_i)`; extensions `(Ω', P')` with a projection to `W`. The bounded-density
condition `Q ≤ k P₀`, the two-outcome (M)-update, the single and random superconditioning
theorems with the note's constructions, the independent extension, and the Dutch book of §6.3.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W I : Type} [Fintype W] [Fintype I] [DecidableEq W] [DecidableEq I]

/-! ## (b) Bounded density and the two-outcome update -/

/-- **Bounded density**: `Q ≤ k P₀` pointwise for some `k ≥ 1`.
Source: [[value-change-as-epistemic-update]] §6.2 ("`Q ≤ k P_0` for some `k ≥ 1`")
Kind: D
Fidelity: exact -/
def BoundedDensity (P₀ Q : Prob W) : Prop := ∃ k : ℝ, 1 ≤ k ∧ ∀ w, Q.p w ≤ k * P₀.p w

/-- **Absolute continuity** (the rule (Z) for a single pair): `P₀(w) = 0 ⇒ Q(w) = 0`.
Source: [[value-change-as-epistemic-update]] §6.2 ((Z))
Kind: D
Fidelity: exact -/
def AbsCont (P₀ Q : Prob W) : Prop := ∀ w, P₀.p w = 0 → Q.p w = 0

/-- **On a finite algebra bounded density is absolute continuity** (the note's "On a finite
algebra that is the same as (Z)"; the refinement matters only on infinite algebras).
Source: [[value-change-as-epistemic-update]] §6.2; mandate Known issues (§6.2)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem boundedDensity_iff_absCont (P₀ Q : Prob W) : BoundedDensity P₀ Q ↔ AbsCont P₀ Q := by
  constructor
  · rintro ⟨k, _, hk⟩ w hw
    have := hk w; rw [hw, mul_zero] at this
    exact le_antisymm this (Q.nonneg w)
  · intro h
    refine ⟨(∑ w, Q.p w / P₀.p w) + 1, by
      have : 0 ≤ ∑ w, Q.p w / P₀.p w := sum_nonneg fun w _ => div_nonneg (Q.nonneg w) (P₀.nonneg w)
      linarith, fun w => ?_⟩
    rcases (P₀.nonneg w).lt_or_eq with hpos | hzero
    · have h1 : Q.p w / P₀.p w ≤ ∑ w', Q.p w' / P₀.p w' :=
        single_le_sum (f := fun w' => Q.p w' / P₀.p w')
          (fun w' _ => div_nonneg (Q.nonneg w') (P₀.nonneg w')) (mem_univ w)
      have h2 : Q.p w / P₀.p w ≤ (∑ w', Q.p w' / P₀.p w') + 1 := by linarith
      rw [div_le_iff₀ hpos] at h2
      exact h2
    · rw [h w hzero.symm, ← hzero, mul_zero]

/-- A **two-outcome update satisfying (M)** in which `Q` occurs with positive probability:
`P₀ = π₁ Q + (1 − π₁) R` for a probability `R` and `0 < π₁ ≤ 1`.
Source: [[value-change-as-epistemic-update]] §6.2 ("a two-outcome update satisfying (M) in which
`Q` occurs with probability `1/k`")
Kind: D
Fidelity: exact -/
def TwoOutcomeM (P₀ Q : Prob W) : Prop :=
  ∃ (π₁ : ℝ) (R : Prob W), 0 < π₁ ∧ π₁ ≤ 1 ∧ ∀ w, P₀.p w = π₁ * Q.p w + (1 - π₁) * R.p w

/-- **T12(b), bounded density iff a two-outcome (M)-update**: `Q ≤ k P₀` for some `k ≥ 1` iff `Q`
is a positive-probability outcome of some two-outcome update satisfying (M). ⇒ with the note's
`R := (P₀ − Q/k)/(1 − 1/k)` (and `k = 1` forcing `Q = P₀`); ⇐ with `k = 1/π₁`.
Source: [[value-change-as-epistemic-update]] §6.2 (Abram's parenthetical, "with one refinement")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem boundedDensity_iff_twoOutcomeM (P₀ Q : Prob W) : BoundedDensity P₀ Q ↔ TwoOutcomeM P₀ Q := by
  constructor
  · rintro ⟨k, hk1, hk⟩
    rcases hk1.lt_or_eq with hk1 | hk1
    · -- `k > 1`: the note's `R`
      have hk0 : 0 < k := by linarith
      have hden : 0 < 1 - 1 / k := by
        rw [sub_pos, div_lt_one hk0]; exact hk1
      refine ⟨1 / k, ⟨fun w => (P₀.p w - Q.p w / k) / (1 - 1 / k), fun w => ?_, ?_⟩,
        by positivity, by rw [div_le_one hk0]; exact hk1.le, fun w => ?_⟩
      · apply div_nonneg _ hden.le
        have := hk w
        rw [sub_nonneg, div_le_iff₀ hk0]; linarith
      · rw [← sum_div, sum_sub_distrib, P₀.sum_one, ← sum_div, Q.sum_one]
        field_simp
      · simp only
        field_simp
        ring
    · -- `k = 1`: `Q ≤ P₀` pointwise with both summing to one forces `Q = P₀`
      subst hk1
      have heq : ∀ w, Q.p w = P₀.p w := by
        intro w
        by_contra hne
        have hlt : Q.p w < P₀.p w := lt_of_le_of_ne (by simpa using hk w) hne
        have : ∑ w, Q.p w < ∑ w, P₀.p w :=
          sum_lt_sum (fun w _ => by simpa using hk w) ⟨w, mem_univ w, hlt⟩
        rw [Q.sum_one, P₀.sum_one] at this
        exact lt_irrefl _ this
      exact ⟨1, P₀, one_pos, le_rfl, fun w => by rw [heq]; ring⟩
  · rintro ⟨π₁, R, hπ0, hπ1, h⟩
    refine ⟨1 / π₁, by rw [le_div_iff₀ hπ0]; linarith, fun w => ?_⟩
    have := h w
    have hR := R.nonneg w
    rw [this, div_mul_eq_mul_div, le_div_iff₀ hπ0]
    nlinarith

/-! ## (c), (g) The random case: reflection, the superconditioned joint, the independent joint -/

/-- An **update law**: outcome probabilities `π_i ≥ 0` summing to one and installed states `Q_i`.
Source: [[value-change-as-epistemic-update]] §6.2 ("the time-1 credence `P_1` takes value `Q_i`
with probability `π_i`")
Kind: D
Fidelity: exact -/
structure Law (W I : Type) [Fintype W] [Fintype I] where
  /-- outcome probabilities -/
  π : I → ℝ
  /-- nonnegative -/
  π_nonneg : ∀ i, 0 ≤ π i
  /-- summing to one -/
  π_sum : ∑ i, π i = 1
  /-- the installed states -/
  Q : Installed W I

/-- **(M) for a law and a prior**: `P₀ = ∑_i π_i Q_i`.
Source: [[value-change-as-epistemic-update]] §6.2 ((M))
Kind: D
Fidelity: exact -/
def LawMartingale (P₀ : Prob W) (ℓ : Law W I) : Prop := ∀ w, P₀.p w = ∑ i, ℓ.π i * ℓ.Q.Q i w

/-- **The superconditioned joint** `P'(w, i) = π_i Q_i(w)` (Diaconis–Zabell's construction for the
random case).
Source: [[value-change-as-epistemic-update]] §6.4 ("sufficiency is the construction
`P'(A × {i}) := π_i Q_i(A)`")
Kind: D
Fidelity: exact -/
def superJoint (ℓ : Law W I) : Joint W I where
  P := fun w i => ℓ.π i * ℓ.Q.Q i w
  nonneg := fun w i => mul_nonneg (ℓ.π_nonneg i) (ℓ.Q.nonneg i w)
  sum_one := by
    rw [sum_comm]
    simp_rw [← mul_sum, ℓ.Q.sum_one, mul_one]
    exact ℓ.π_sum

/-- **The independent joint** `P''(w, i) = π_i P₀(w)`.
Source: [[value-change-as-epistemic-update]] §6.5 ("the *independent* joint
`P''(A × {i}) := π_i P_0(A)`")
Kind: D
Fidelity: exact -/
def indepJoint (P₀ : Prob W) (ℓ : Law W I) : Joint W I where
  P := fun w i => ℓ.π i * P₀.p w
  nonneg := fun w i => mul_nonneg (ℓ.π_nonneg i) (P₀.nonneg w)
  sum_one := by
    rw [sum_comm]
    simp_rw [← mul_sum, P₀.sum_one, mul_one]
    exact ℓ.π_sum

/-- The superconditioned joint has outcome probabilities `π_i`.
Source: [[value-change-as-epistemic-update]] §6.4
Kind: L
Fidelity: exact -/
theorem superJoint_π (ℓ : Law W I) (i : I) : (superJoint ℓ).π i = ℓ.π i := by
  unfold Joint.π superJoint; simp only; rw [← mul_sum, ℓ.Q.sum_one, mul_one]

/-- **T12(g) ⇐, the superconditioned joint reflects by construction**: `P'(· ∣ E_i) = Q_i`.
Source: [[value-change-as-epistemic-update]] §6.4 ("in the extension, Reflection holds *by
construction*")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem superJoint_reflection (ℓ : Law W I) : Reflection (superJoint ℓ) ℓ.Q := by
  intro i _ w; rw [superJoint_π]; rfl

/-- **T12(g) ⇐, its marginal is `P₀` under (M)**: the superconditioned joint is an extension of
`P₀` with the given law, iff (M).
Source: [[value-change-as-epistemic-update]] §6.4
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem superJoint_marg_iff (P₀ : Prob W) (ℓ : Law W I) :
    (∀ w, (superJoint ℓ).marg w = P₀.p w) ↔ LawMartingale P₀ ℓ := by
  unfold Joint.marg superJoint LawMartingale
  simp only
  constructor <;> intro h w <;> exact (h w).symm

/-- **T12(g) ⇒ on `W × I`, a reflective joint with marginal `P₀` forces (M)** (the law of total
probability): if a joint `J` on `W × I` has marginal `P₀`, outcome probabilities `π_i`, and
`P(· ∣ E_i) = Q_i`, then `P₀ = ∑_i π_i Q_i`. This is the note's own extension `(Ω × I, P')`; for
an arbitrary finite extension carrying a partition see `lawMartingale_of_extension`.
Source: [[value-change-as-epistemic-update]] §6.4 ("Necessity is the law of total probability")
Kind: P
Fidelity: exact
Hyps: (a) `hmarg`, `hπ`, `hR : Reflection J ℓ.Q` -/
theorem lawMartingale_of_reflection (P₀ : Prob W) (ℓ : Law W I) (J : Joint W I)
    (hmarg : ∀ w, J.marg w = P₀.p w) (hπ : ∀ i, J.π i = ℓ.π i) (hR : Reflection J ℓ.Q) :
    LawMartingale P₀ ℓ := by
  intro w
  rw [← hmarg w, reflection_imp_martingale hR w]
  refine sum_congr rfl fun i _ => ?_
  rw [hπ i]

/-- **T12(c), (R) ⇒ (M)** for a general joint (restated from `Update.lean`).
Source: [[value-change-as-epistemic-update]] §6.3 ("Summing (R) over `i` gives (M)")
Kind: P
Fidelity: exact -/
theorem R_imp_M {J : Joint W I} {Q : Installed W I} (h : Reflection J Q) : Martingale J Q :=
  reflection_imp_martingale h

/-- **T12(h), the independent extension is also conservative**: `P''` has marginal `P₀` and outcome
probabilities `π_i` — the same marginal and the same law as the superconditioned joint — and it is
reflective iff every `Q_i` with `π_i > 0` equals `P₀` (so for the coin it is not).
Source: [[value-change-as-epistemic-update]] §6.5 ("is also a conservative extension with the same
marginal and the same law")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem indepJoint_conservative (P₀ : Prob W) (ℓ : Law W I) :
    (∀ w, (indepJoint P₀ ℓ).marg w = P₀.p w) ∧ (∀ i, (indepJoint P₀ ℓ).π i = ℓ.π i) ∧
    (Reflection (indepJoint P₀ ℓ) ℓ.Q ↔ ∀ i, 0 < ℓ.π i → ∀ w, ℓ.Q.Q i w = P₀.p w) := by
  have hπ : ∀ i, (indepJoint P₀ ℓ).π i = ℓ.π i := by
    intro i; unfold Joint.π indepJoint; simp only; rw [← mul_sum, P₀.sum_one, mul_one]
  refine ⟨fun w => ?_, hπ, ?_⟩
  · unfold Joint.marg indepJoint; simp only; rw [← sum_mul, ℓ.π_sum, one_mul]
  · unfold Reflection
    simp_rw [hπ]
    constructor
    · intro h i hi w
      have := h i hi w
      simp only [indepJoint] at this
      exact (mul_left_cancel₀ hi.ne' this).symm
    · intro h i hi w
      simp only [indepJoint]; rw [h i hi w]

/-! ## (f) Superconditioning, single transition, general extensions -/

/-- **An extension** of `P₀`: a finite space `Ω'`, a probability `P'` on it and a projection
`p : Ω' → W` whose pushforward is `P₀`.
Source: [[value-change-as-epistemic-update]] §6.4 ("there is `(Ω', P')` extending `(Ω, P_0)`")
Kind: D
Fidelity: exact (finite extensions) -/
structure Extension (P₀ : Prob W) where
  /-- the extended space -/
  Ω' : Type
  /-- finite -/
  fin : Fintype Ω'
  /-- decidable equality -/
  dec : DecidableEq Ω'
  /-- the extended probability -/
  P' : Prob Ω'
  /-- the projection -/
  proj : Ω' → W
  /-- pushforward is `P₀` -/
  push : ∀ w, ∑ ω' ∈ (Finset.univ (α := Ω')).filter (fun ω' => proj ω' = w), P'.p ω' = P₀.p w

attribute [instance] Extension.fin Extension.dec

/-- `Q` **is a conditioning in the extension** on the event `E`: `P'(E) > 0` and
`Q(w) · P'(E) = P'({proj = w} ∩ E)` for every `w`.
Source: [[value-change-as-epistemic-update]] §6.4 ("`P'(· ∣ E)|_Ω = Q`")
Kind: D
Fidelity: exact -/
def Extension.IsConditioning {P₀ : Prob W} (X : Extension P₀) (Q : Prob W) (E : Finset X.Ω') : Prop :=
  0 < X.P'.mass E ∧ ∀ w, Q.p w * X.P'.mass E =
    ∑ ω' ∈ (Finset.univ (α := X.Ω')).filter (fun ω' => X.proj ω' = w ∧ ω' ∈ E), X.P'.p ω'

/-- **T12(f) ⇒, necessity**: if `Q = P'(· ∣ E)` on `W` for some extension, then `Q ≤ k P₀` with
`k = 1/P'(E)`.
Source: [[value-change-as-epistemic-update]] §6.4 ("Necessity: `Q(A) = P'(A ∩ E)/P'(E) ≤
P_0(A)/P'(E)`")
Kind: P
Fidelity: exact
Hyps: (a) `X.IsConditioning Q E` -/
theorem boundedDensity_of_conditioning (P₀ Q : Prob W) (X : Extension P₀) (E : Finset X.Ω')
    (h : X.IsConditioning Q E) : BoundedDensity P₀ Q := by
  obtain ⟨hE, hQ⟩ := h
  have hE1 : X.P'.mass E ≤ 1 := by rw [← X.P'.mass_univ]; exact X.P'.mass_mono (subset_univ E)
  refine ⟨1 / X.P'.mass E, by rw [le_div_iff₀ hE]; linarith, fun w => ?_⟩
  have hsub : ∑ ω' ∈ (univ : Finset X.Ω').filter (fun ω' => X.proj ω' = w ∧ ω' ∈ E), X.P'.p ω' ≤
      ∑ ω' ∈ (univ : Finset X.Ω').filter (fun ω' => X.proj ω' = w), X.P'.p ω' := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro ω'; simp only [mem_filter, mem_univ, true_and]; exact fun h => h.1
    · intro ω' _ _; exact X.P'.nonneg ω'
  rw [X.push w] at hsub
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hE, hQ w]
  exact hsub

/-- The installed state `Q_i` of an installed family, as a probability on `W`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Installed.state (Q : Installed W I) (i : I) : Prob W :=
  ⟨Q.Q i, Q.nonneg i, Q.sum_one i⟩

/-- **T12(g) ⇒ for an arbitrary finite extension**: if `(Ω', P')` extends `P₀` and carries a
partition `(E_i)_i` (pairwise disjoint, covering) with `P'(E_i) = π_i` and
`P'(· ∣ E_i)|_W = Q_i` on every non-null `E_i`, then `P₀ = ∑_i π_i Q_i` (the law of total
probability). `lawMartingale_of_reflection` is the case `Ω' = W × I`, `E_i = W × {i}`; here the
extension is any finite one, which is how the note's "any extension that makes the update a
conditioning" reads.
Source: [[value-change-as-epistemic-update]] §6.4 ("Necessity is the law of total probability")
Kind: P
Fidelity: exact (finite extensions)
Hyps: (a) `hdisj`, `hcover`, `hπ`, `hcond` -/
theorem lawMartingale_of_extension (P₀ : Prob W) (ℓ : Law W I) (X : Extension P₀)
    (E : I → Finset X.Ω') (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (hcover : ∀ ω', ∃ i, ω' ∈ E i) (hπ : ∀ i, ℓ.π i = X.P'.mass (E i))
    (hcond : ∀ i, 0 < X.P'.mass (E i) → X.IsConditioning (ℓ.Q.state i) (E i)) :
    LawMartingale P₀ ℓ := by
  intro w
  have hsplit : P₀.p w = ∑ i, ∑ ω' ∈ (univ : Finset X.Ω').filter
      (fun ω' => X.proj ω' = w ∧ ω' ∈ E i), X.P'.p ω' := by
    rw [← X.push w]
    have hff : ∀ i, (univ : Finset X.Ω').filter (fun ω' => X.proj ω' = w ∧ ω' ∈ E i) =
        ((univ : Finset X.Ω').filter (fun ω' => X.proj ω' = w)).filter (fun ω' => ω' ∈ E i) := by
      intro i; rw [filter_filter]
    simp_rw [hff, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun ω' _ => ?_
    obtain ⟨i₀, hi₀⟩ := hcover ω'
    rw [sum_eq_single i₀]
    · simp [hi₀]
    · intro j _ hj
      have : ω' ∉ E j := Finset.disjoint_left.1 (hdisj i₀ j (Ne.symm hj)) hi₀
      simp [this]
    · intro h; exact absurd (mem_univ i₀) h
  rw [hsplit]
  refine sum_congr rfl fun i _ => ?_
  rcases (X.P'.mass_nonneg (E i)).lt_or_eq with hpos | hzero
  · obtain ⟨_, hQ⟩ := hcond i hpos
    rw [← hQ w, hπ i, mul_comm]
    rfl
  · rw [hπ i, ← hzero, zero_mul]
    apply sum_eq_zero
    intro ω' hω'
    simp only [mem_filter, mem_univ, true_and] at hω'
    have hle : X.P'.p ω' ≤ X.P'.mass (E i) := by
      unfold Prob.mass; exact single_le_sum (fun x _ => X.P'.nonneg x) hω'.2
    rw [← hzero] at hle
    exact le_antisymm hle (X.P'.nonneg ω')

/-- A joint on `W × I` as a probability on the product type.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Joint.toProb (J : Joint W I) : Prob (W × I) where
  p := fun x => J.P x.1 x.2
  nonneg := fun x => J.nonneg x.1 x.2
  sum_one := by rw [Fintype.sum_prod_type]; exact J.sum_one

/-- The cells `E_i = W × {i}` of the outcome partition on `W × I`.
Source: [[value-change-as-epistemic-update]] §6.4 ("`P'(A × {i})`")
Kind: D
Fidelity: exact -/
def superPartition (i : I) : Finset (W × I) := univ.filter fun x => x.2 = i

/-- **The superconditioned joint as a finite extension of `P₀`**, under (M): `Ω' = W × I`,
`P'(w, i) = π_i Q_i(w)`, projection to the first coordinate.
Source: [[value-change-as-epistemic-update]] §6.4 ("sufficiency is the construction
`P'(A × {i}) := π_i Q_i(A)`")
Kind: D
Fidelity: exact -/
def superExtension (P₀ : Prob W) (ℓ : Law W I) (hM : LawMartingale P₀ ℓ) : Extension P₀ where
  Ω' := W × I
  fin := inferInstance
  dec := inferInstance
  P' := (superJoint ℓ).toProb
  proj := Prod.fst
  push := by
    intro w
    have hset : (univ : Finset (W × I)).filter (fun x => x.1 = w) = {w} ×ˢ univ := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, and_true]
    rw [hset, sum_product, sum_singleton, hM w]
    rfl

theorem superPartition_disjoint (i j : I) (hij : i ≠ j) :
    Disjoint (superPartition (W := W) i) (superPartition j) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [superPartition, mem_filter, mem_univ, true_and] at hx hx'
  exact hij (hx.symm.trans hx')

theorem superPartition_cover (x : W × I) : ∃ i, x ∈ superPartition i :=
  ⟨x.2, by simp [superPartition]⟩

theorem superExtension_mass (ℓ : Law W I) (i : I) :
    (superJoint ℓ).toProb.mass (superPartition i) = ℓ.π i := by
  have hset : superPartition (W := W) i = univ ×ˢ {i} := by
    ext ⟨a, b⟩
    simp only [superPartition, mem_filter, mem_univ, true_and, mem_product, mem_singleton]
  unfold Prob.mass
  rw [hset, sum_product]
  simp_rw [sum_singleton]
  show ∑ a, ℓ.π i * ℓ.Q.Q i a = ℓ.π i
  rw [← mul_sum, ℓ.Q.sum_one, mul_one]

theorem superExtension_conditioning (P₀ : Prob W) (ℓ : Law W I) (hM : LawMartingale P₀ ℓ) (i : I)
    (hpos : 0 < (superExtension P₀ ℓ hM).P'.mass (superPartition i)) :
    (superExtension P₀ ℓ hM).IsConditioning (ℓ.Q.state i) (superPartition i) := by
  refine ⟨hpos, fun w => ?_⟩
  have hset : (univ : Finset (W × I)).filter (fun x => x.1 = w ∧ x ∈ superPartition i) = {(w, i)} := by
    ext ⟨a, b⟩; simp [superPartition]
  show ℓ.Q.Q i w * (superJoint ℓ).toProb.mass (superPartition i) =
    ∑ x ∈ (univ : Finset (W × I)).filter (fun x => x.1 = w ∧ x ∈ superPartition i),
      (superJoint ℓ).toProb.p x
  rw [hset, sum_singleton, superExtension_mass]
  show ℓ.Q.Q i w * ℓ.π i = ℓ.π i * ℓ.Q.Q i w
  ring

/-- **T12(g) as an iff over finite extensions (random superconditioning)**: there is a finite
extension `(Ω', P')` of `P₀` with a partition `(E_i)_i` such that `P'(E_i) = π_i` and
`P'(· ∣ E_i)|_W = Q_i` on every non-null cell, iff (M) `P₀ = ∑_i π_i Q_i`. Necessity is
`lawMartingale_of_extension`; sufficiency is the superconditioned joint on `W × I` with the cells
`W × {i}` (`superExtension`, `superPartition`).
Source: [[value-change-as-epistemic-update]] §6.4 ("the update law is a simultaneous conditioning
in some extension iff (M)")
Kind: C
Fidelity: exact (finite extensions)
Hyps: (a) none -/
theorem superconditioning_random (P₀ : Prob W) (ℓ : Law W I) :
    (∃ (X : Extension P₀) (E : I → Finset X.Ω'),
        (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧ (∀ ω', ∃ i, ω' ∈ E i) ∧
        (∀ i, ℓ.π i = X.P'.mass (E i)) ∧
        (∀ i, 0 < X.P'.mass (E i) → X.IsConditioning (ℓ.Q.state i) (E i))) ↔
      LawMartingale P₀ ℓ := by
  constructor
  · rintro ⟨X, E, hdisj, hcover, hπ, hcond⟩
    exact lawMartingale_of_extension P₀ ℓ X E hdisj hcover hπ hcond
  · intro hM
    refine ⟨superExtension P₀ ℓ hM, superPartition, superPartition_disjoint, superPartition_cover,
      fun i => ?_, superExtension_conditioning P₀ ℓ hM⟩
    exact (superExtension_mass ℓ i).symm

/-- The note's extension for sufficiency: `Ω' = W × Bool`, `P'(w, true) = Q(w)/k`,
`P'(w, false) = P₀(w) − Q(w)/k`, `E = W × {true}`.
Source: [[value-change-as-epistemic-update]] §6.4 ("Sufficiency: on `Ω × {0, 1}` put …")
Kind: D
Fidelity: exact -/
def noteExtension (P₀ Q : Prob W) (k : ℝ) (hk1 : 1 ≤ k) (hk : ∀ w, Q.p w ≤ k * P₀.p w) :
    Extension P₀ where
  Ω' := W × Bool
  fin := inferInstance
  dec := inferInstance
  P' := {
    p := fun y => if y.2 then Q.p y.1 / k else P₀.p y.1 - Q.p y.1 / k
    nonneg := fun y => by
      have hk0 : 0 < k := by linarith
      split_ifs
      · exact div_nonneg (Q.nonneg _) hk0.le
      · rw [sub_nonneg, div_le_iff₀ hk0]; linarith [hk y.1]
    sum_one := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      rw [sum_add_distrib, sum_sub_distrib, P₀.sum_one]; ring }
  proj := Prod.fst
  push := fun w => by
    have hset : (univ : Finset (W × Bool)).filter (fun y => y.1 = w) = {(w, true), (w, false)} := by
      ext ⟨v, b⟩; simp; constructor
      · rintro rfl; cases b <;> simp
      · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> rfl
    rw [hset, sum_pair (by simp)]
    simp

/-- **T12(f) ⇐, sufficiency**: if `Q ≤ k P₀` then `Q` is a conditioning in the note's extension on
`E = W × {true}`, with `P'(E) = 1/k`.
Source: [[value-change-as-epistemic-update]] §6.4 (Sufficiency)
Kind: P
Fidelity: exact
Hyps: (a) `1 ≤ k`, `Q ≤ k P₀` -/
theorem conditioning_of_boundedDensity (P₀ Q : Prob W) (k : ℝ) (hk1 : 1 ≤ k)
    (hk : ∀ w, Q.p w ≤ k * P₀.p w) :
    (noteExtension P₀ Q k hk1 hk).IsConditioning Q ((univ : Finset W) ×ˢ {true}) := by
  have hk0 : 0 < k := by linarith
  have hmass : (noteExtension P₀ Q k hk1 hk).P'.mass ((univ : Finset W) ×ˢ {true}) = 1 / k := by
    unfold Prob.mass noteExtension
    simp only
    rw [sum_product]
    simp only [sum_singleton, if_true]
    rw [← sum_div, Q.sum_one]
  refine ⟨by rw [hmass]; positivity, fun w => ?_⟩
  rw [hmass]
  have hset : (univ : Finset (W × Bool)).filter
      (fun ω' => ω'.1 = w ∧ ω' ∈ (univ : Finset W) ×ˢ ({true} : Finset Bool)) = {(w, true)} := by
    ext ⟨v, b⟩; simp
  show Q.p w * (1 / k) = ∑ ω' ∈ (univ : Finset (W × Bool)).filter
      (fun ω' => ω'.1 = w ∧ ω' ∈ (univ : Finset W) ×ˢ ({true} : Finset Bool)),
      (noteExtension P₀ Q k hk1 hk).P'.p ω'
  rw [hset, sum_singleton]
  simp [noteExtension]; ring

/-- **T12(f), superconditioning for a single transition**: `Q` is a conditioning in some finite
extension of `P₀` iff `Q ≤ k P₀` for some `k`.
Source: [[value-change-as-epistemic-update]] §6.4 (Single transition)
Kind: C
Fidelity: exact (finite extensions)
Hyps: (a) none -/
theorem superconditioning_single (P₀ Q : Prob W) :
    (∃ (X : Extension P₀) (E : Finset X.Ω'), X.IsConditioning Q E) ↔ BoundedDensity P₀ Q := by
  constructor
  · rintro ⟨X, E, h⟩; exact boundedDensity_of_conditioning P₀ Q X E h
  · rintro ⟨k, hk1, hk⟩
    exact ⟨noteExtension P₀ Q k hk1 hk, _, conditioning_of_boundedDensity P₀ Q k hk1 hk⟩

/-! ## (e) The Dutch book of §6.3 -/

/-- The bookie's net on the four states `(θ, coin)` of §6.3's coin agent: at time 0 the bookie
buys, at the agent's price `1/2`, the bet on `θ = A` called off unless the coin shows `A`, and
likewise for `B`; at time 1, if the coin shows `A`, sells the agent the bet on `θ = A` at `9/10`,
and symmetrically. Net per state: the conditional bets pay `[θ = coin] − 1/2` on the active side;
the time-1 sale pays `9/10 − [θ = coin]`.
Source: [[value-change-as-epistemic-update]] §6.3 ("the bookie nets `0.4` in every state")
Kind: D
Fidelity: exact as a description; the two prices are literals here (the model-priced version is
`bookieNetModel` in `Variants.lean`) -/
def bookieNet (θ coin : Bool) : ℝ :=
  ((if θ = coin then 1 else 0) - 1 / 2) + (9 / 10 - (if θ = coin then 1 else 0))

/-- **T12(e), the Dutch book, arithmetic form**: the portfolio nets `2/5` for the bookie in every
one of the four states. What the kernel checks here is the arithmetic of the hand-written portfolio
(`(f − 1/2) + (9/10 − f) = 2/5` for any payoff `f`, the bet cancelling between the legs); the
version whose prices are derived from the model (`coinJoint`, `install9`) is `dutch_book_model`
(`Variants.lean`), and that is the headline. (Audit r1, B5.)
Source: [[value-change-as-epistemic-update]] §6.3
Kind: L
Fidelity: exact as arithmetic; the headline is `dutch_book_model` -/
theorem dutch_book : ∀ θ coin : Bool, bookieNet θ coin = 2 / 5 := by
  intro θ coin; cases θ <;> cases coin <;> simp [bookieNet] <;> norm_num

end

end Cleanroom.Corrigibility.CorrValueChange
