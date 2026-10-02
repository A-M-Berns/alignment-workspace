import Cleanroom.Lit.LitDdbAccuracyMm.Defs

/-!
# Infrastructure: sums, the reflected rule `X ↦ −X`, conditional distributions, Simple Trust

Supporting lemmas for `lit-ddb-accuracy-mm` (no ledger rows except the two Target 1 bridges
`totalTrust_iff_forall_totalTrustOn` and `simpleTrustOn_iff_totalTrustOn_ind`).
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Sums -/

/-- `E_π(I_X(P)) − E_π(I_X(x))` as one sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem expInaccP_sub_expInacc (π : W → ℝ) (F : Frame W) (X : W → ℝ) (I : Rule) (x : ℝ) :
    expInaccP π F X I - expInacc π X I x =
      ∑ w, π w * (I (E (F.P w) X) (X w) - I x (X w)) := by
  simp only [expInaccP, expInacc, mul_sub, sum_sub_distrib]

/-- Some world has `X w ≤ E_ρ(X)` (`ρ` a distribution).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_le_E {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (X : W → ℝ) : ∃ w, X w ≤ E ρ X := by
  by_contra h
  simp only [not_exists, not_le] at h
  obtain ⟨w₀, hw₀⟩ := supp_nonempty hρ
  have hw₀' : 0 < ρ w₀ := by simpa [supp] using hw₀
  have hlt : ∑ w, ρ w * E ρ X < ∑ w, ρ w * X w := by
    apply sum_lt_sum
    · intro w _; exact mul_le_mul_of_nonneg_left (h w).le (hρ.1 w)
    · exact ⟨w₀, mem_univ _, mul_lt_mul_of_pos_left (h w₀) hw₀'⟩
  rw [← sum_mul, hρ.2, one_mul] at hlt
  exact lt_irrefl _ hlt

/-- Some world has `E_ρ(X) ≤ X w` (`ρ` a distribution).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_E_le {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) (X : W → ℝ) : ∃ w, E ρ X ≤ X w := by
  obtain ⟨w, hw⟩ := exists_le_E hρ (-X)
  refine ⟨w, ?_⟩
  rw [E_neg_right] at hw
  simpa using hw

/-- `E_ρ(X) ≤ c` when `X ≤ c` everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_le_of_forall_le {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) {X : W → ℝ} {c : ℝ}
    (h : ∀ w, X w ≤ c) : E ρ X ≤ c := by
  have := E_le_E (X := X) (Y := fun _ => c) hρ.1 h
  rwa [E_const hρ] at this

/-- `c ≤ E_ρ(X)` when `c ≤ X` everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem le_E_of_forall_le {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) {X : W → ℝ} {c : ℝ}
    (h : ∀ w, c ≤ X w) : c ≤ E ρ X := by
  have := E_le_E (X := fun _ => c) (Y := X) hρ.1 h
  rwa [E_const hρ] at this

/-! ## The reflected rule -/

/-- The reflected rule `I.neg x k := I (−x) (−k)`: the rule for `−X` obtained from a rule for
`X`. Every class in Target 2 is transported along it.
Source: none: infrastructure (the dual trick `X ↦ −X`)
Kind: D
Fidelity: n/a -/
def Rule.neg (I : Rule) : Rule := fun x k => I (-x) (-k)

/-- `E_ρ(I^−_{−X}(x)) = E_ρ(I_X(−x))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem expInacc_neg (ρ X : W → ℝ) (I : Rule) (x : ℝ) :
    expInacc ρ (-X) I.neg x = expInacc ρ X I (-x) := by
  simp [expInacc, Rule.neg]

/-- `E_π(I^−_{−X}(P)) = E_π(I_X(P))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem expInaccP_neg (π : W → ℝ) (F : Frame W) (X : W → ℝ) (I : Rule) :
    expInaccP π F (-X) I.neg = expInaccP π F X I := by
  simp [expInaccP, Rule.neg, E_neg_right]

/-- Gsp on the range transports to the reflected rule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsGspOn.neg {X : W → ℝ} {I : Rule} (h : IsGspOn X I) : IsGspOn (-X) I.neg := by
  intro ρ hρ s ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ hs
  rw [expInacc_neg, expInacc_neg, E_neg_right, neg_neg]
  rw [E_neg_right] at hs
  apply h ρ hρ (-s)
  · exact ⟨w₂, by have := hw₂; simp only [Pi.neg_apply] at this; linarith⟩
  · exact ⟨w₁, by have := hw₁; simp only [Pi.neg_apply] at this; linarith⟩
  · intro h'; apply hs; rw [← h', neg_neg]

/-- Gsp transports to the reflected rule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsGsp.neg {X : W → ℝ} {I : Rule} (h : IsGsp X I) : IsGsp (-X) I.neg := by
  intro ρ hρ s hs
  rw [expInacc_neg, expInacc_neg, E_neg_right, neg_neg]
  rw [E_neg_right] at hs
  apply h ρ hρ (-s)
  intro h'; apply hs; rw [← h', neg_neg]

/-- Value-directedness transports to the reflected rule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ValueDirected.neg {X : W → ℝ} {I : Rule} (h : ValueDirected X I) :
    ValueDirected (-X) I.neg := by
  intro w e₁ e₂
  obtain ⟨h1, h2⟩ := h w (-e₁) (-e₂)
  simp only [Pi.neg_apply, Rule.neg, neg_neg]
  constructor
  · rintro ⟨hlt, hle⟩
    exact h2 ⟨by linarith, by linarith⟩
  · rintro ⟨hle, hlt⟩
    exact h1 ⟨by linarith, by linarith⟩

/-- Value-directedness everywhere gives value-directedness on the value range.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ValueDirected.valueDirectedOn {X : W → ℝ} {I : Rule} (h : ValueDirected X I) :
    ValueDirectedOn X I :=
  fun w e₁ e₂ =>
    ⟨fun _ h12 h2 => (h w e₁ e₂).1 ⟨h12, h2⟩, fun _ h2 h21 => (h w e₁ e₂).2 ⟨h2, h21⟩⟩

/-- Value-directedness on the range transports to the reflected rule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ValueDirectedOn.neg {X : W → ℝ} {I : Rule} (h : ValueDirectedOn X I) :
    ValueDirectedOn (-X) I.neg := by
  intro w e₁ e₂
  obtain ⟨h1, h2⟩ := h w (-e₁) (-e₂)
  simp only [Pi.neg_apply, Rule.neg, neg_neg]
  constructor
  · rintro ⟨w₀, hw₀⟩ hlt hle
    exact h2 ⟨w₀, by linarith⟩ (by linarith) (by linarith)
  · rintro ⟨w₀, hw₀⟩ hle hlt
    exact h1 ⟨w₀, by linarith⟩ (by linarith) (by linarith)

/-- Continuity in the estimate transports to the reflected rule.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Rule.neg_continuous {I : Rule} (h : ∀ k, Continuous (fun x => I x k)) (k : ℝ) :
    Continuous (fun x => I.neg x k) :=
  (h (-k)).comp continuous_neg

omit [DecidableEq W] in
/-- Gsp implies gsp on the range.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsGsp.isGspOn {X : W → ℝ} {I : Rule} (h : IsGsp X I) : IsGspOn X I :=
  fun ρ hρ s _ _ hs => h ρ hρ s hs

/-! ## Target 1 bridges -/

/-- **Target 1.** Total Trust is Total Trust with respect to every variable.
Source: [[Deference Done Better]] §3 l. 271; mandate Target 1
Kind: L
Fidelity: exact -/
theorem totalTrust_iff_forall_totalTrustOn {π : W → ℝ} {F : Frame W} :
    TotalTrust π F ↔ ∀ X, TotalTrustOn X π F := by
  constructor
  · intro h X
    exact ⟨fun s => h X s, fun s => totalTrust_iff_dual.1 h X s⟩
  · intro h X s
    exact (h X).1 s

/-- The two clauses of `TotalTrustOn` swap under `X ↦ −X`.
Source: none: infrastructure (the dual trick, per variable)
Kind: L
Fidelity: n/a -/
theorem TotalTrustOn.neg {X π : W → ℝ} {F : Frame W} (h : TotalTrustOn X π F) :
    TotalTrustOn (-X) π F := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro s
    have e : ∑ w, π w * ((-X) w - s) * (if s ≤ E (F.P w) (-X) then 1 else 0) =
        -∑ w, π w * (X w - -s) * (if E (F.P w) X ≤ -s then 1 else 0) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro w _
      simp only [E_neg_right, Pi.neg_apply]
      by_cases hc : E (F.P w) X ≤ -s
      · rw [if_pos (by linarith), if_pos hc]; ring
      · rw [if_neg (fun h => hc (by linarith)), if_neg hc]; ring
    rw [e]
    linarith [h2 (-s)]
  · intro s
    have e : ∑ w, π w * ((-X) w - s) * (if E (F.P w) (-X) ≤ s then 1 else 0) =
        -∑ w, π w * (X w - -s) * (if -s ≤ E (F.P w) X then 1 else 0) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro w _
      simp only [E_neg_right, Pi.neg_apply]
      by_cases hc : -s ≤ E (F.P w) X
      · rw [if_pos (by linarith), if_pos hc]; ring
      · rw [if_neg (fun h => hc (by linarith)), if_neg hc]; ring
    rw [e]
    linarith [h1 (-s)]

/-- Clause 1 of `TotalTrustOn` as a sum over `[E(X) ≥ s]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem TotalTrustOn.event_sum {X π : W → ℝ} {F : Frame W} (h : TotalTrustOn X π F) (s : ℝ) :
    0 ≤ ∑ w ∈ F.estEvent X s, π w * (X w - s) := by
  rw [← totalTrust_sum_eq]; exact h.1 s

/-- Clause 2 of `TotalTrustOn` as a sum over `[E(X) ≤ s]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem TotalTrustOn.dual_event_sum {X π : W → ℝ} {F : Frame W} (h : TotalTrustOn X π F)
    (s : ℝ) : ∑ w ∈ F.estEventLE X s, π w * (X w - s) ≤ 0 := by
  rw [← totalTrust_dual_sum_eq]; exact h.2 s

/-! ## Conditional distributions -/

/-- `π(· | A)` as a vector: `w ↦ 𝟙[w ∈ A] · π w / π(A)`. Meaningful only under `0 < π(A)`, which
every consumer carries; used only inside proofs (never in a definition of record).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def condDist (π : W → ℝ) (A : Finset W) : W → ℝ :=
  fun w => if w ∈ A then π w / mass π A else 0

/-- `π(· | A)` is a distribution when `0 < π(A)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condDist_mem_stdSimplex {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {A : Finset W}
    (h : 0 < mass π A) : condDist π A ∈ stdSimplex ℝ W := by
  refine ⟨fun w => ?_, ?_⟩
  · unfold condDist
    split_ifs
    · exact div_nonneg (hπ w) h.le
    · exact le_rfl
  · simp only [condDist]
    rw [sum_ite_mem, univ_inter]
    simp only [div_eq_mul_inv]
    rw [← sum_mul]
    exact mul_inv_cancel₀ h.ne'

/-- `E_{π(·|A)}(X) · π(A) = ∑_{w ∈ A} π w X w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_condDist (π : W → ℝ) (A : Finset W) (X : W → ℝ) :
    E (condDist π A) X = (∑ w ∈ A, π w * X w) / mass π A := by
  simp only [E, condDist, ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter, div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro w _
  ring

/-- `E_{π(·|A)}(I_X(x)) = (∑_{w ∈ A} π w I(x, X w)) / π(A)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem expInacc_condDist (π : W → ℝ) (A : Finset W) (X : W → ℝ) (I : Rule) (x : ℝ) :
    expInacc (condDist π A) X I x = (∑ w ∈ A, π w * I x (X w)) / mass π A := by
  simp only [expInacc, condDist, ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter, div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro w _
  ring

/-- On a `π`-null event every `π w` vanishes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_eq_zero_of_mass_eq_zero {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {A : Finset W}
    (h : mass π A = 0) (f : W → ℝ) : ∑ w ∈ A, π w * f w = 0 :=
  sum_eq_zero fun w hw => by rw [eq_zero_of_mass_eq_zero hπ h hw, zero_mul]

/-! ## Simple Trust with respect to `q` -/

omit [Fintype W] in
/-- `∑_{w ∈ A} π w (𝟙_q w − t) = π(q ∧ A) − t · π(A)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_ind_sub (π : W → ℝ) (q A : Finset W) (t : ℝ) :
    ∑ w ∈ A, π w * (ind q w - t) = mass π (q ∩ A) - t * mass π A := by
  simp only [mass]
  rw [mul_sum, inter_comm, ← sum_ite_mem, ← sum_sub_distrib]
  apply sum_congr rfl
  intro w _
  simp only [ind]
  split_ifs <;> ring

/-- `[P(q) ≤ t]` is `[E(𝟙_q) ≤ t]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem probEventLE_eq_estEventLE (F : Frame W) (q : Finset W) (t : ℝ) :
    probEventLE F q t = F.estEventLE (ind q) t := by
  ext w; simp [probEventLE, Frame.estEventLE, E_ind]

/-- **Target 7 (bridge).** Simple Trust with respect to `q` is Total Trust with respect to `𝟙_q`.
Source: [[Deference Done Better]] §3 l. 255, l. 271; mandate Target 7
Kind: L
Fidelity: exact -/
theorem simpleTrustOn_iff_totalTrustOn_ind {π : W → ℝ} {F : Frame W} (q : Finset W) :
    SimpleTrustOn q π F ↔ TotalTrustOn (ind q) π F := by
  unfold SimpleTrustOn TotalTrustOn
  have e1 : ∀ t : ℝ, ∑ w, π w * (ind q w - t) * (if t ≤ E (F.P w) (ind q) then 1 else 0) =
      mass π (q ∩ F.probEvent q t) - t * mass π (F.probEvent q t) := by
    intro t
    rw [totalTrust_sum_eq, ← Frame.probEvent_eq_estEvent, sum_ind_sub]
  have e2 : ∀ t : ℝ, ∑ w, π w * (ind q w - t) * (if E (F.P w) (ind q) ≤ t then 1 else 0) =
      mass π (q ∩ probEventLE F q t) - t * mass π (probEventLE F q t) := by
    intro t
    rw [totalTrust_dual_sum_eq, ← probEventLE_eq_estEventLE, sum_ind_sub]
  simp only [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun t => by linarith [h1 t], fun t => by linarith [h2 t]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun t => by linarith [h1 t], fun t => by linarith [h2 t]⟩

end

end Cleanroom.Lit.LitDdbAccuracyMm
