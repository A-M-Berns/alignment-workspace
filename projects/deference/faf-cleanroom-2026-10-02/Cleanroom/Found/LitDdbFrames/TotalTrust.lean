import Cleanroom.Found.LitDdbFrames.Basic

/-!
# Total Trust: the product form and its immediate consequences

Package `lit-ddb-frames`, Targets 2 and 11. The definition of record is `TotalTrust` in
`Defs.lean`; this file proves that it is DDB's Total Trust exactly (dual form, conditional form
off null events, triviality on null events), the strict-threshold form, that Simple Trust and
Trust are instances, and the three consequences the cycle needs (candidate reflexivity,
conditional Total Trust, New Reflection at candidates) — instances of item 053's ladder, which
`lit-ddb-facts` generalises.
-/

namespace Cleanroom.Found.LitDdbFrames

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## The events `[E(X) ≥ s]` and `[E(X) ≤ s]` -/

/-- The proposition `[E(X) ≥ s]`: worlds where the expert's estimate of `X` is at least `s`.
Source: [[Deference Done Better]] §2 l. 171
Kind: D
Fidelity: exact -/
def Frame.estEvent (F : Frame W) (X : W → ℝ) (s : ℝ) : Finset W :=
  univ.filter (fun w => s ≤ E (F.P w) X)

/-- The proposition `[E(X) ≤ s]`.
Source: [[Deference Done Better]] §2 l. 180
Kind: D
Fidelity: exact -/
def Frame.estEventLE (F : Frame W) (X : W → ℝ) (s : ℝ) : Finset W :=
  univ.filter (fun w => E (F.P w) X ≤ s)

/-- Membership in `[E(X) ≥ s]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem Frame.mem_estEvent {F : Frame W} {X : W → ℝ} {s : ℝ} {w : W} :
    w ∈ F.estEvent X s ↔ s ≤ E (F.P w) X := by simp [Frame.estEvent]

/-- Membership in `[E(X) ≤ s]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem Frame.mem_estEventLE {F : Frame W} {X : W → ℝ} {s : ℝ} {w : W} :
    w ∈ F.estEventLE X s ↔ E (F.P w) X ≤ s := by simp [Frame.estEventLE]

/-- The product-form sum of Total Trust as a sum over the event `[E(X) ≥ s]`.
Source: none: infrastructure (Target 2)
Kind: L
Fidelity: n/a -/
theorem totalTrust_sum_eq (F : Frame W) (π X : W → ℝ) (s : ℝ) :
    ∑ w, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) =
      ∑ w ∈ F.estEvent X s, π w * (X w - s) := by
  rw [Frame.estEvent, sum_filter]
  simp [mul_ite]

/-- The dual product-form sum as a sum over the event `[E(X) ≤ s]`.
Source: none: infrastructure (Target 2)
Kind: L
Fidelity: n/a -/
theorem totalTrust_dual_sum_eq (F : Frame W) (π X : W → ℝ) (s : ℝ) :
    ∑ w, π w * (X w - s) * (if E (F.P w) X ≤ s then 1 else 0) =
      ∑ w ∈ F.estEventLE X s, π w * (X w - s) := by
  rw [Frame.estEventLE, sum_filter]
  simp [mul_ite]

/-- Total Trust as an inequality over the event `[E(X) ≥ s]`.
Source: none: infrastructure (Target 2)
Kind: L
Fidelity: n/a -/
theorem TotalTrust.event_sum {π : W → ℝ} {F : Frame W} (h : TotalTrust π F) (X : W → ℝ)
    (s : ℝ) : 0 ≤ ∑ w ∈ F.estEvent X s, π w * (X w - s) := by
  rw [← totalTrust_sum_eq]; exact h X s

/-! ## Target 2(a): the dual form -/

/-- **Target 2(a).** Total Trust is equivalent to its dual `∀ X s, ∑ w, π w · (X w − s) ·
𝟙[E_{P_w}(X) ≤ s] ≤ 0` (substitute `−X, −s`).
Source: [[Deference Done Better]] §2 l. 180
Kind: L
Fidelity: exact -/
theorem totalTrust_iff_dual {π : W → ℝ} {F : Frame W} :
    TotalTrust π F ↔
      ∀ (X : W → ℝ) (s : ℝ), ∑ w, π w * (X w - s) * (if E (F.P w) X ≤ s then 1 else 0) ≤ 0 := by
  have key : ∀ (X : W → ℝ) (s : ℝ),
      ∑ w, π w * ((-X) w - -s) * (if -s ≤ E (F.P w) (-X) then 1 else 0) =
        -∑ w, π w * (X w - s) * (if E (F.P w) X ≤ s then 1 else 0) := by
    intro X s
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro w _
    simp only [E_neg_right, neg_le_neg_iff, Pi.neg_apply]
    ring
  constructor
  · intro h X s
    have := h (-X) (-s)
    rw [key] at this
    linarith
  · intro h X s
    have := h (-X) (-s)
    have e : ∑ w, π w * ((-X) w - -s) * (if E (F.P w) (-X) ≤ -s then 1 else 0) =
        -∑ w, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro w _
      simp only [E_neg_right, neg_le_neg_iff, Pi.neg_apply]
      ring
    rw [e] at this
    linarith

/-- Total Trust as an inequality over the event `[E(X) ≤ s]`.
Source: none: infrastructure (Target 2)
Kind: L
Fidelity: n/a -/
theorem TotalTrust.dual_event_sum {π : W → ℝ} {F : Frame W} (h : TotalTrust π F) (X : W → ℝ)
    (s : ℝ) : ∑ w ∈ F.estEventLE X s, π w * (X w - s) ≤ 0 := by
  rw [← totalTrust_dual_sum_eq]; exact totalTrust_iff_dual.1 h X s

/-! ## Target 2(b): the conditional form off null events -/

/-- On a positive-mass event `A`, the product inequality `0 ≤ ∑_{w ∈ A} π w (X w − s)` is the
ratio inequality `s ≤ E_π(X | A)`.
Source: none: infrastructure (Target 2)
Kind: L
Fidelity: n/a -/
theorem prod_ineq_iff_cond {π X : W → ℝ} {A : Finset W} {s : ℝ} (h : 0 < mass π A) :
    0 ≤ ∑ w ∈ A, π w * (X w - s) ↔ s ≤ (∑ w ∈ A, π w * X w) / mass π A := by
  rw [le_div_iff₀ h]
  have : ∑ w ∈ A, π w * (X w - s) = (∑ w ∈ A, π w * X w) - s * mass π A := by
    simp [mul_sub, sum_sub_distrib, mass, mul_sum, mul_comm]
  rw [this]
  constructor <;> intro h' <;> linarith

/-- On a `π`-null event the product sum vanishes, so the product inequality holds trivially.
Source: none: infrastructure (Target 2)
Kind: L
Fidelity: n/a -/
theorem prod_sum_eq_zero_of_mass_eq_zero {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {A : Finset W}
    (h : mass π A = 0) (X : W → ℝ) (s : ℝ) : ∑ w ∈ A, π w * (X w - s) = 0 :=
  sum_eq_zero fun w hw => by rw [eq_zero_of_mass_eq_zero hπ h hw, zero_mul]

/-- **Target 2(b).** The definition of record is *exactly* DDB's Total Trust under DDB's
convention that `E_π(X | E(X) ≥ s) ≥ s` is required only when `π(E(X) ≥ s) > 0`: Total Trust
holds iff for every `X, s` with `0 < π(E(X) ≥ s)`, `s ≤ E_π(X | E(X) ≥ s)` in ratio form. On a
`π`-null event the product inequality is `0 ≤ 0`.
Source: [[Deference Done Better]] §2 l. 175, App. B Lemma 7.1 l. 484 ("this implies
`π(E(X) ≥ t) > 0`"); item 034 (Weatherson) for the convention
Kind: L
Fidelity: exact -/
theorem totalTrust_iff_cond {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} :
    TotalTrust π F ↔
      ∀ (X : W → ℝ) (s : ℝ), 0 < mass π (F.estEvent X s) →
        s ≤ (∑ w ∈ F.estEvent X s, π w * X w) / mass π (F.estEvent X s) := by
  constructor
  · intro h X s hpos
    exact (prod_ineq_iff_cond hpos).1 (h.event_sum X s)
  · intro h X s
    rw [totalTrust_sum_eq]
    rcases (mass_nonneg hπ (F.estEvent X s)).lt_or_eq with hpos | hzero
    · exact (prod_ineq_iff_cond hpos).2 (h X s hpos)
    · rw [prod_sum_eq_zero_of_mass_eq_zero hπ hzero.symm]

/-! ## Target 2(c): the strict-threshold form -/

/-- **Target 2(c).** Total Trust yields the strict-threshold inequality
`0 ≤ ∑ w, π w · (X w − s) · 𝟙[s < E_{P_w}(X)]`: on a finite frame `[E(X) > s] = [E(X) ≥ s']`
for the next attained value `s'`, and `(X − s) = (X − s') + (s' − s)`.
Source: [[Deference Done Better]] §2 l. 175 (variant); mandate Target 2(c)
Kind: L
Fidelity: variant: strict threshold, derived from the record form -/
theorem TotalTrust.strict {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : TotalTrust π F)
    (X : W → ℝ) (s : ℝ) :
    0 ≤ ∑ w, π w * (X w - s) * (if s < E (F.P w) X then 1 else 0) := by
  set B := univ.filter (fun w => s < E (F.P w) X) with hB
  have hsum : ∑ w, π w * (X w - s) * (if s < E (F.P w) X then 1 else 0) =
      ∑ w ∈ B, π w * (X w - s) := by
    rw [hB, sum_filter]; simp [mul_ite]
  rw [hsum]
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · simp [hBe]
  obtain ⟨m, hmB, hmin⟩ := B.exists_min_image (fun w => E (F.P w) X) hBne
  set s' := E (F.P m) X with hs'
  have hss' : s < s' := (mem_filter.1 hmB).2
  have hBeq : F.estEvent X s' = B := by
    ext w
    simp only [Frame.mem_estEvent, hB, mem_filter, mem_univ, true_and]
    exact ⟨fun hw => lt_of_lt_of_le hss' hw, fun hw => hmin w (by simp [hB, hw])⟩
  have h1 := h.event_sum X s'
  rw [hBeq] at h1
  have h2 : ∑ w ∈ B, π w * (X w - s) =
      ∑ w ∈ B, π w * (X w - s') + (s' - s) * mass π B := by
    simp only [mass, mul_sum]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro w _
    ring
  rw [h2]
  have h3 : 0 ≤ (s' - s) * mass π B := mul_nonneg (by linarith) (mass_nonneg hπ B)
  linarith

/-! ## Target 2(d): Simple Trust is an instance -/

/-- `[P(q) ≥ t]` is `[E(𝟙_q) ≥ t]`.
Source: none: infrastructure (Target 2)
Kind: L
Fidelity: n/a -/
theorem Frame.probEvent_eq_estEvent (F : Frame W) (q : Finset W) (t : ℝ) :
    F.probEvent q t = F.estEvent (ind q) t := by
  ext w; simp [Frame.probEvent, E_ind]

/-- **Target 2(d), Simple Trust.** Total Trust implies Simple Trust (take `X := 𝟙_q`).
Source: [[Deference Done Better]] §2 l. 171 ("Simple Trust is simply the requirement that,
for every indicator variable…")
Kind: L
Fidelity: exact -/
theorem TotalTrust.simpleTrust {π : W → ℝ} {F : Frame W} (h : TotalTrust π F) :
    SimpleTrust π F := by
  intro q t _
  have h1 := h.event_sum (ind q) t
  rw [← Frame.probEvent_eq_estEvent] at h1
  have h2 : ∑ w ∈ F.probEvent q t, π w * (ind q w - t) =
      mass π (q ∩ F.probEvent q t) - t * mass π (F.probEvent q t) := by
    simp only [mass]
    rw [mul_sum, inter_comm, ← sum_ite_mem, ← sum_sub_distrib]
    apply sum_congr rfl
    intro w _
    simp only [ind]
    split_ifs <;> ring
  linarith

/-! ## Target 11(a): candidate reflexivity from Total Trust -/

/-- **Target 11(a).** Under Total Trust every candidate `ρ ∈ C_π` has `0 < ρ(P = ρ)`: apply the
dual at `s = 0` to `X := 𝟙[P = ρ]`; if `ρ(P = ρ) = 0` the whole cell lies inside `[E(X) ≤ 0]`,
forcing `π(P = ρ) ≤ 0`. (Instance of item 053(i); `lit-ddb-facts` generalises.)
Source: [[Deference Done Better]] fn 37 (presupposition), App. B Lemma 7.2.5 (conclusion under
the hull condition); mandate Target 11(a)
Kind: P
Fidelity: exact -/
theorem TotalTrust.selfMass_pos {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : TotalTrust π F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) : 0 < F.selfMass ρ := by
  have hρs := F.mem_stdSimplex_of_mem_cands hρ
  rcases (mass_nonneg hρs.1 (F.cell ρ)).lt_or_eq with hpos | hzero
  · exact hpos
  exfalso
  have hzero' : F.selfMass ρ = 0 := hzero.symm
  have h1 := h.dual_event_sum (ind (F.cell ρ)) 0
  have hsub : F.cell ρ ⊆ F.estEventLE (ind (F.cell ρ)) 0 := by
    intro w hw
    rw [Frame.mem_estEventLE, E_ind, (Frame.mem_cell.1 hw)]
    exact hzero'.le
  have h2 : ∑ w ∈ F.estEventLE (ind (F.cell ρ)) 0, π w * (ind (F.cell ρ) w - 0) =
      mass π (F.cell ρ) := by
    rw [mass, ← sum_subset hsub]
    · apply sum_congr rfl
      intro w hw
      simp [ind, hw]
    · intro w _ hw
      simp [ind, hw]
  rw [h2] at h1
  have h3 : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ).1 hρ
  linarith

/-! ## Target 11(b): conditional Total Trust -/

/-- The proposition `[E(X | q) ≥ t]`, product-guarded: worlds with `P_w(q) > 0` and
`t · P_w(q) ≤ ∑ v ∈ q, P_w v · X v`.
Source: [[Deference Done Better]] §2 l. 182, fn 36
Kind: D
Fidelity: exact -/
def Frame.condEstEvent (F : Frame W) (X : W → ℝ) (q : Finset W) (t : ℝ) : Finset W :=
  univ.filter (fun w => 0 < mass (F.P w) q ∧ t * mass (F.P w) q ≤ ∑ v ∈ q, F.P w v * X v)

/-- Membership in `[E(X | q) ≥ t]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem Frame.mem_condEstEvent {F : Frame W} {X : W → ℝ} {q : Finset W} {t : ℝ}
    {w : W} : w ∈ F.condEstEvent X q t ↔
      0 < mass (F.P w) q ∧ t * mass (F.P w) q ≤ ∑ v ∈ q, F.P w v * X v := by
  simp [Frame.condEstEvent]

/-- Under Total Trust, a world of `q` at which the expert gives `q` probability zero is
`π`-null (the dual at `(𝟙_q, 0)`).
Source: none: infrastructure (Target 11(b))
Kind: L
Fidelity: n/a -/
theorem TotalTrust.null_of_mass_eq_zero {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : TotalTrust π F) {q : Finset W} {w : W} (hw : w ∈ q) (hq : mass (F.P w) q = 0) :
    π w = 0 := by
  have h1 := h.dual_event_sum (ind q) 0
  have hmem : w ∈ F.estEventLE (ind q) 0 := by
    rw [Frame.mem_estEventLE, E_ind, hq]
  have hterm : ∀ v ∈ F.estEventLE (ind q) 0, 0 ≤ π v * (ind q v - 0) := by
    intro v _
    simp only [sub_zero, ind]
    split_ifs <;> simp [hπ v]
  have h2 : π w * (ind q w - 0) ≤ 0 :=
    le_trans (single_le_sum hterm hmem) h1
  simp only [sub_zero, ind, hw, if_true, mul_one] at h2
  exact le_antisymm h2 (hπ w)

/-- The expert's estimate of `(X − t) · 𝟙_q`.
Source: none: infrastructure (Target 11(b))
Kind: L
Fidelity: n/a -/
theorem E_cond_aux (ρ X : W → ℝ) (q : Finset W) (t : ℝ) :
    E ρ (fun v => if v ∈ q then X v - t else 0) = (∑ v ∈ q, ρ v * X v) - t * mass ρ q := by
  unfold E mass
  rw [mul_sum, ← sum_sub_distrib, ← sum_subset (subset_univ q)]
  · apply sum_congr rfl
    intro v hv
    simp only [hv, if_true]
    ring
  · intro v _ hv
    simp [hv]

/-- **Target 11(b).** Conditional Total Trust in product form: for every `X`, `q`, `t`,
`t · π(q ∧ [E(X | q) ≥ t]) ≤ ∑_{w ∈ q ∧ [E(X | q) ≥ t]} π w · X w`. Proved directly from the
record form at `(Y, 0)` with `Y := (X − t) · 𝟙_q`, using that worlds of `q` where the expert
gives `q` probability zero are `π`-null — bypassing fn 36's biconvexity. (Instance of item
053(ii); `lit-ddb-facts` generalises.)
Source: [[Deference Done Better]] §2 l. 182, fn 36; mandate Target 11(b)
Kind: P
Fidelity: exact -/
theorem TotalTrust.cond {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : TotalTrust π F)
    (X : W → ℝ) (q : Finset W) (t : ℝ) :
    t * mass π (q ∩ F.condEstEvent X q t) ≤ ∑ w ∈ q ∩ F.condEstEvent X q t, π w * X w := by
  set Y : W → ℝ := fun v => if v ∈ q then X v - t else 0 with hY
  have h1 := h Y 0
  have key : ∑ w, π w * (Y w - 0) * (if 0 ≤ E (F.P w) Y then 1 else 0) =
      ∑ w ∈ q ∩ F.condEstEvent X q t, π w * (X w - t) := by
    rw [← univ_inter (q ∩ F.condEstEvent X q t), ← sum_ite_mem]
    apply sum_congr rfl
    intro w _
    rw [hY, E_cond_aux]
    simp only [sub_zero]
    by_cases hwq : w ∈ q
    · rcases (mass_nonneg (F.P_nonneg w) q).lt_or_eq with hpos | hzero
      · have e : (0 ≤ (∑ v ∈ q, F.P w v * X v) - t * mass (F.P w) q) ↔
            w ∈ q ∩ F.condEstEvent X q t := by
          rw [mem_inter, Frame.mem_condEstEvent]
          constructor
          · intro h'; exact ⟨hwq, hpos, by linarith⟩
          · intro h'; linarith [h'.2.2]
        by_cases hc : w ∈ q ∩ F.condEstEvent X q t
        · rw [if_pos (e.2 hc), if_pos hc, if_pos hwq]; ring
        · rw [if_neg (fun h' => hc (e.1 h')), if_neg hc]; ring
      · have hnull : π w = 0 := h.null_of_mass_eq_zero hπ hwq hzero.symm
        simp [hnull]
    · have hout : w ∉ q ∩ F.condEstEvent X q t := fun h' => hwq (mem_inter.1 h').1
      rw [if_neg hwq, if_neg hout]; ring
  rw [key] at h1
  have h2 : ∑ w ∈ q ∩ F.condEstEvent X q t, π w * (X w - t) =
      (∑ w ∈ q ∩ F.condEstEvent X q t, π w * X w) - t * mass π (q ∩ F.condEstEvent X q t) := by
    simp [mul_sub, sum_sub_distrib, mass, mul_sum, mul_comm]
  linarith

/-- Conditional Total Trust in DDB's ratio form, off null events:
`0 < π(q ∧ [E(X | q) ≥ t]) → t ≤ E_π(X | q ∧ [E(X | q) ≥ t])`.
Source: [[Deference Done Better]] §2 l. 182, fn 36
Kind: L
Fidelity: exact -/
theorem TotalTrust.cond_ratio {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : TotalTrust π F) (X : W → ℝ) (q : Finset W) (t : ℝ)
    (hpos : 0 < mass π (q ∩ F.condEstEvent X q t)) :
    t ≤ (∑ w ∈ q ∩ F.condEstEvent X q t, π w * X w) / mass π (q ∩ F.condEstEvent X q t) := by
  rw [le_div_iff₀ hpos]
  exact h.cond hπ X q t

/-! ## Target 2(d): Trust is an instance -/

/-- `[P(q | p) ≥ t]` is `[E(𝟙_q | p) ≥ t]`.
Source: none: infrastructure (Target 2)
Kind: L
Fidelity: n/a -/
theorem Frame.condProbEvent_eq_condEstEvent (F : Frame W) (q p : Finset W) (t : ℝ) :
    F.condProbEvent q p t = F.condEstEvent (ind q) p t := by
  ext w
  simp only [Frame.condProbEvent, Frame.condEstEvent, mem_filter, mem_univ, true_and]
  have : ∑ v ∈ p, F.P w v * ind q v = mass (F.P w) (q ∩ p) := by
    rw [mass, inter_comm, ← sum_ite_mem]
    apply sum_congr rfl
    intro v _
    simp [ind, mul_ite]
  rw [this]

/-- **Target 2(d), Trust.** Total Trust implies Trust (conditional Total Trust at `X := 𝟙_q`).
Source: [[Deference Done Better]] §2 l. 182 ("Total Trust implies Trust (let `X` be an
indicator variable)")
Kind: C
Fidelity: exact -/
theorem TotalTrust.trust {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : TotalTrust π F) :
    Trust π F := by
  intro q p t _
  rw [Frame.condProbEvent_eq_condEstEvent]
  have h1 := h.cond hπ (ind q) p t
  have h2 : ∑ w ∈ p ∩ F.condEstEvent (ind q) p t, π w * ind q w =
      mass π (q ∩ (p ∩ F.condEstEvent (ind q) p t)) := by
    have : ∀ w ∈ p ∩ F.condEstEvent (ind q) p t, π w * ind q w = if w ∈ q then π w else 0 :=
      fun w _ => by simp [ind, mul_ite]
    rw [sum_congr rfl this, sum_ite_mem, mass, inter_comm]
  rw [h2] at h1
  exact h1

/-! ## Target 11(c): New Reflection at candidates -/

/-- The expert's estimate, on the cell of `ρ`, of the variable `𝟙[P = ρ] · (c · 𝟙_{w} − ρ w)`
vanishes when `c = ρ(P = ρ)` and `w` is in the cell.
Source: none: infrastructure (Target 11(c))
Kind: L
Fidelity: n/a -/
theorem E_cell_probe (F : Frame W) (ρ : W → ℝ) {w : W} (hw : F.P w = ρ) :
    E ρ (fun v => if F.P v = ρ then F.selfMass ρ * (if v = w then 1 else 0) - ρ w else 0) = 0 := by
  rw [E_eq_sum_of_support (q := F.cell ρ)]
  · have : ∀ v ∈ F.cell ρ, ρ v * (if F.P v = ρ then F.selfMass ρ * (if v = w then 1 else 0) - ρ w
        else 0) = F.selfMass ρ * (ρ v * (if v = w then 1 else 0)) - ρ w * ρ v := by
      intro v hv
      rw [Frame.mem_cell] at hv
      simp only [hv, if_true]
      ring
    rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum]
    have hw' : w ∈ F.cell ρ := Frame.mem_cell.2 hw
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', if_pos hw']
    have hc : ∑ i ∈ F.cell ρ, ρ i = F.selfMass ρ := rfl
    rw [hc]
    ring
  · intro v hv
    rw [Frame.mem_cell] at hv
    simp [hv]

/-- Under Total Trust, on the cell of a candidate `ρ`: `π w · ρ(P = ρ) = π(P = ρ) · ρ w` — the
product-form New Reflection identity at one world, from the record form at
`X := 𝟙[P = ρ] · (ρ(P = ρ) · 𝟙_{w} − ρ w)` and its negative, threshold `0`.
Source: none: infrastructure (Target 11(c))
Kind: L
Fidelity: n/a -/
theorem TotalTrust.cell_identity {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : TotalTrust π F) {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) {w : W} (hw : F.P w = ρ) :
    π w * F.selfMass ρ = mass π (F.cell ρ) * ρ w := by
  set c := F.selfMass ρ with hc
  set X : W → ℝ := fun v => if F.P v = ρ then c * (if v = w then 1 else 0) - ρ w else 0 with hX
  have hsum : ∀ (Z : W → ℝ), (∀ v, F.P v = ρ → E (F.P v) Z = 0) → (∀ v, F.P v ≠ ρ → Z v = 0) →
      ∑ v, π v * (Z v - 0) * (if 0 ≤ E (F.P v) Z then 1 else 0) = ∑ v ∈ F.cell ρ, π v * Z v := by
    intro Z hE hZ
    rw [← sum_subset (subset_univ (F.cell ρ))]
    · apply sum_congr rfl
      intro v hv
      rw [Frame.mem_cell] at hv
      simp [hE v hv]
    · intro v _ hv
      rw [Frame.mem_cell] at hv
      simp [hZ v hv]
  have hcell : ∀ v, F.P v = ρ → E (F.P v) X = 0 := fun v hv => by
    rw [hv]; exact E_cell_probe F ρ hw
  have hoff : ∀ v, F.P v ≠ ρ → X v = 0 := fun v hv => by simp [hX, hv]
  have hval : ∑ v ∈ F.cell ρ, π v * X v = c * π w - ρ w * mass π (F.cell ρ) := by
    have : ∀ v ∈ F.cell ρ, π v * X v = c * (π v * (if v = w then 1 else 0)) - ρ w * π v := by
      intro v hv
      rw [Frame.mem_cell] at hv
      simp only [hX, hv, if_true]
      ring
    rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, ← mul_sum, mass]
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', if_pos (Frame.mem_cell.2 hw)]
  have h1 := h X 0
  rw [hsum X hcell hoff, hval] at h1
  have hcellN : ∀ v, F.P v = ρ → E (F.P v) (-X) = 0 := fun v hv => by
    rw [E_neg_right, hcell v hv, neg_zero]
  have hoffN : ∀ v, F.P v ≠ ρ → (-X) v = 0 := fun v hv => by simp [hoff v hv]
  have h2 := h (-X) 0
  rw [hsum (-X) hcellN hoffN] at h2
  have hvalN : ∑ v ∈ F.cell ρ, π v * (-X) v = -(c * π w - ρ w * mass π (F.cell ρ)) := by
    rw [← hval, ← sum_neg_distrib]
    apply sum_congr rfl
    intro v _
    simp
  rw [hvalN] at h2
  linarith

/-- **Target 11(c).** Total Trust implies New Reflection in the strong reading: every candidate
has a positive self-cell (Target 11(a)) and `π(· | P = ρ) = ρ(· | P = ρ)` in product form.
(Instance of item 053; both directions of fn 37; `lit-ddb-facts` generalises.)
Source: [[Deference Done Better]] §2 l. 182, l. 227, fn 37
Kind: P
Fidelity: exact -/
theorem TotalTrust.newReflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : TotalTrust π F) : NewReflects π F := by
  intro ρ hρ
  refine ⟨h.selfMass_pos hπ hρ, fun w => ?_⟩
  by_cases hw : F.P w = ρ
  · have hind : ind (F.cell ρ) w = 1 := by simp [ind, hw]
    rw [hind, mul_one, mul_one]
    exact h.cell_identity hπ hρ hw
  · have hind : ind (F.cell ρ) w = 0 := by simp [ind, hw]
    rw [hind]; ring

/-- **Target 22 (part).** Under Total Trust the vacuous and strong readings of New Reflection
coincide.
Source: none: infrastructure (mandate Target 22)
Kind: L
Fidelity: n/a -/
theorem TotalTrust.newReflectsVac_iff {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : TotalTrust π F) : NewReflectsVac π F ↔ NewReflects π F :=
  ⟨fun hv ρ hρ => ⟨h.selfMass_pos hπ hρ, hv ρ hρ (h.selfMass_pos hπ hρ)⟩, NewReflects.vac⟩

end

end Cleanroom.Found.LitDdbFrames
