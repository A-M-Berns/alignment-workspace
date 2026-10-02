import Cleanroom.Trust.TtFiniteFrames.Corr
import Cleanroom.Found.LitDdbFrames.TotalTrust

/-!
# Partition experts: own-prior trust, the cross-prior characterization, the support-set reduction

Package `tt-finite-frames`, Targets T1, T3, T5.

* **T1** (instantiation, not discovery): a full-support prior totally trusts its own partition
  expert — the finite law of total expectation read as a Total Trust statement
  (trust-lab-063 `TT_condExpert`, [[route-transitivity]] §5.1 Link 1). Proved for every
  partitional correspondence; `ofPartition` is the map case.
* **T3** (load-bearing 2): for full-support `πH, πA` and any map `c`, `πH` totally trusts the
  `πA`-partition expert of `c` **iff** the two priors' conditionals agree on every cell, in product
  form `πA v · πH(cell v) = πH v · πA(cell v)` (trust-lab-064 `TT_condExpert_cross_iff`).
* **T5**: thresholds are redundant in Total Trust (rows sum to one), and Total Trust fails iff
  some nonempty support set `S` carries a homogeneous system with a negative `π`-weighted sum
  (trust-lab-065's reduction, the part that is a theorem).

All trust statements are the dependency's `TotalTrust`; nothing is redefined.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Plumbing -/

/-- Total Trust depends on a frame only through its rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem totalTrust_of_P_eq {π : W → ℝ} {F G : Frame W} (h : F.P = G.P) (hF : TotalTrust π F) :
    TotalTrust π G := by
  unfold TotalTrust at *
  rw [← h]
  exact hF

/-- On a cell of the conditioning frame, `∑_{w ∈ E v} π w (X w − s) = π(E v) · (E_{P_v}(X) − s)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.ofCorr_cell_sum (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (K : Corr W)
    (h : ∀ w, 0 < mass π (K w)) (v : W) (X : W → ℝ) (s : ℝ) :
    ∑ w ∈ K v, π w * (X w - s) = mass π (K v) * (E ((Frame.ofCorr π hπ K h).P v) X - s) := by
  rw [mul_sub, mul_comm, Frame.ofCorr_E]
  unfold mass
  rw [sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro w _
  ring

/-! ## T1: a prior totally trusts its own partition expert (classical instantiation) -/

/-- **T1 (partitional correspondences).** A full-support prior totally trusts the conditioning
frame of any partitional correspondence: the event `[E(X) ≥ s]` is a union of cells, and each
cell contributes `π(cell) · (E_π(X | cell) − s) ≥ 0`. The finite law of total expectation as a
Total Trust statement — a classical instantiation, not a discovery.
Source: trust-lab-063 `TT_condExpert`; [[route-transitivity]] §5.1 Link 1
Kind: P (instantiation)
Fidelity: exact
Hyps: (a) `hpos` full support (the lab's standing assumption), `hK` partitional -/
theorem totalTrust_ofCorr_of_partitional {π : W → ℝ} (hpos : ∀ w, 0 < π w) {K : Corr W}
    (hK : K.Partitional) (h : ∀ w, 0 < mass π (K w)) :
    TotalTrust π (Frame.ofCorr π (fun w => (hpos w).le) K h) := by
  intro X s
  set F := Frame.ofCorr π (fun w => (hpos w).le) K h with hF
  rw [hK.sum_cells]
  apply sum_nonneg
  intro C hC
  obtain ⟨v, _, rfl⟩ := mem_image.1 hC
  have hrow : ∀ w ∈ K v, F.P w = F.P v := fun w hw =>
    Frame.ofCorr_P_eq_of_eq π _ K h (hK.2 v w hw).symm
  have : ∑ w ∈ K v, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) =
      (if s ≤ E (F.P v) X then 1 else 0) * ∑ w ∈ K v, π w * (X w - s) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro w hw
    rw [hrow w hw]
    ring
  rw [this, Frame.ofCorr_cell_sum π (fun w => (hpos w).le) K h]
  split_ifs with hs
  · have := h v
    nlinarith
  · simp

/-- **T1 (maps).** A full-support prior totally trusts its own partition expert `ofPartition π f`.
Source: trust-lab-063 `TT_condExpert`; [[route-transitivity]] §5.1 Link 1
Kind: P (instantiation)
Fidelity: exact
Hyps: (a) `hpos` full support -/
theorem totalTrust_ofPartition {ι : Type} [DecidableEq ι] {π : W → ℝ} (hpos : ∀ w, 0 < π w)
    (f : W → ι) : TotalTrust π (Frame.ofPartition π hpos f) :=
  totalTrust_ofCorr_of_partitional hpos (Corr.ofMap_partitional f) _

/-! ## T3: the cross-prior characterization -/

/-- Fibres of `c` through worlds of one fibre coincide.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Corr.ofMap_eq_of_mem {ι : Type} [DecidableEq ι] {c : W → ι} {u v : W}
    (h : u ∈ Corr.ofMap c v) : Corr.ofMap c u = Corr.ofMap c v := by
  rw [Corr.mem_ofMap] at h
  ext x
  simp [Corr.mem_ofMap, h]

/-- The conditionals of a full-support prior sum to one over each fibre.
Source: trust-lab-064 `cond_sum_one`
Kind: L
Fidelity: n/a -/
theorem sum_div_mass_ofMap {ι : Type} [DecidableEq ι] {π : W → ℝ} (hpos : ∀ w, 0 < π w)
    (c : W → ι) (v : W) :
    ∑ u ∈ Corr.ofMap c v, π u / mass π (Corr.ofMap c v) = 1 := by
  rw [← Finset.sum_div]
  exact div_self (Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional c).1 v).ne'

/-- **Mismatch direction (trust-lab-064 `TT_fails_of_cond_mismatch`).** If at some world `u`
the `πA`-conditional probability within its cell exceeds the `πH`-conditional one — in product
form `πH u · πA(cell u) < πA u · πH(cell u)` — then `πH` does not totally trust the
`πA`-partition expert: the witness is `X = 𝟙_{u}`, `s = πA(u | cell u)`, at which the event
`[E(X) ≥ s]` is exactly the cell of `u` and the product-form mass is `πH u − s · πH(cell u) < 0`.
Source: trust-lab-064 `TT_fails_of_cond_mismatch`
Kind: P
Fidelity: exact (product form of the source's ratio hypothesis)
Hyps: (a) `hposH`, `hposA` full support -/
theorem not_totalTrust_ofPartition_of_mismatch {ι : Type} [DecidableEq ι] {πH πA : W → ℝ}
    (hposH : ∀ w, 0 < πH w) (hposA : ∀ w, 0 < πA w) (c : W → ι) (u : W)
    (hmis : πH u * mass πA (Corr.ofMap c u) < πA u * mass πH (Corr.ofMap c u)) :
    ¬ TotalTrust πH (Frame.ofPartition πA hposA c) := by
  intro h
  set FA := Frame.ofPartition πA hposA c with hFA
  have hmA : 0 < mass πA (Corr.ofMap c u) :=
    Corr.mass_pos_of_reflexive hposA (Corr.ofMap_partitional c).1 u
  have hmH : 0 < mass πH (Corr.ofMap c u) :=
    Corr.mass_pos_of_reflexive hposH (Corr.ofMap_partitional c).1 u
  set s : ℝ := πA u / mass πA (Corr.ofMap c u) with hs
  have hspos : 0 < s := div_pos (hposA u) hmA
  -- the expert's estimate of `𝟙_{u}` at `w`
  have hE : ∀ w, E (FA.P w) (ind {u}) =
      (if c u = c w then πA u else 0) / mass πA (Corr.ofMap c w) := by
    intro w
    rw [hFA, Frame.ofPartition_E_eq]
    congr 1
    by_cases hcw : c u = c w
    · rw [if_pos hcw]
      rw [sum_eq_single u]
      · simp [ind]
      · intro b _ hb; simp [ind, hb]
      · intro hu; exact absurd (by rw [Corr.mem_ofMap]; exact hcw) hu
    · rw [if_neg hcw]
      apply sum_eq_zero
      intro b hb
      rw [Corr.mem_ofMap] at hb
      have : b ≠ u := fun e => hcw (by rw [← e, hb])
      simp [ind, this]
  have h1 := h (ind {u}) s
  -- the event `[E(X) ≥ s]` is the fibre of `u`
  have hev : ∀ w, (s ≤ E (FA.P w) (ind {u})) ↔ w ∈ Corr.ofMap c u := by
    intro w
    rw [hE w, Corr.mem_ofMap]
    by_cases hcw : c u = c w
    · rw [if_pos hcw]
      have : Corr.ofMap c w = Corr.ofMap c u := by
        ext x; simp [Corr.mem_ofMap, hcw]
      rw [this]
      simp [hs, hcw.symm]
    · rw [if_neg hcw, zero_div]
      constructor
      · intro hle; linarith
      · intro hcw'; exact absurd hcw'.symm hcw
  have h2 : ∑ w, πH w * (ind {u} w - s) * (if s ≤ E (FA.P w) (ind {u}) then 1 else 0) =
      ∑ w ∈ Corr.ofMap c u, πH w * (ind {u} w - s) := by
    rw [totalTrust_sum_eq]
    apply sum_congr _ (fun _ _ => rfl)
    ext w
    rw [Frame.mem_estEvent]
    exact hev w
  have h3 : ∑ w ∈ Corr.ofMap c u, πH w * (ind {u} w - s) =
      πH u - s * mass πH (Corr.ofMap c u) := by
    have hu : u ∈ Corr.ofMap c u := (Corr.ofMap_partitional c).1 u
    simp only [mul_sub, sum_sub_distrib]
    rw [sum_eq_single u]
    · simp only [ind, mem_singleton, if_true, mul_one]
      rw [mass, mul_sum]
      congr 1
      apply sum_congr rfl
      intro w _; ring
    · intro b _ hb; simp [ind, hb]
    · intro hnot; exact absurd hu hnot
  rw [h2, h3, hs] at h1
  -- `0 ≤ πH u − (πA u / πA(cell)) · πH(cell)`, contradicting the mismatch
  have h4 : πA u / mass πA (Corr.ofMap c u) * mass πH (Corr.ofMap c u) ≤ πH u := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hmA] at h4
  linarith

/-- **Pivot step.** If the two priors' conditionals disagree somewhere in a cell, some world of
that cell has a strict mismatch in the direction the witness needs (both conditionals sum to one
over the cell).
Source: trust-lab-064 (pivot step inside `TT_condExpert_cross_iff`)
Kind: L
Fidelity: n/a -/
theorem exists_mismatch_of_ne {ι : Type} [DecidableEq ι] {πH πA : W → ℝ}
    (hposH : ∀ w, 0 < πH w) (hposA : ∀ w, 0 < πA w) (c : W → ι) (v : W)
    (hne : πA v * mass πH (Corr.ofMap c v) ≠ πH v * mass πA (Corr.ofMap c v)) :
    ∃ u, πH u * mass πA (Corr.ofMap c u) < πA u * mass πH (Corr.ofMap c u) := by
  by_contra hall
  push Not at hall
  have hmA : 0 < mass πA (Corr.ofMap c v) :=
    Corr.mass_pos_of_reflexive hposA (Corr.ofMap_partitional c).1 v
  have hmH : 0 < mass πH (Corr.ofMap c v) :=
    Corr.mass_pos_of_reflexive hposH (Corr.ofMap_partitional c).1 v
  -- ratio form on the cell of `v`
  have hle : ∀ u ∈ Corr.ofMap c v,
      πA u / mass πA (Corr.ofMap c v) ≤ πH u / mass πH (Corr.ofMap c v) := by
    intro u hu
    have hcell := Corr.ofMap_eq_of_mem hu
    have := hall u
    rw [hcell] at this
    rw [div_le_div_iff₀ hmA hmH]
    linarith
  have hsumA := sum_div_mass_ofMap hposA c v
  have hsumH := sum_div_mass_ofMap hposH c v
  have heq := (sum_eq_sum_iff_of_le hle).1 (hsumA.trans hsumH.symm)
  have hv := heq v ((Corr.ofMap_partitional c).1 v)
  rw [div_eq_div_iff hmA.ne' hmH.ne'] at hv
  exact hne hv

/-- **Cellwise agreement is frame identity.** If `πH` and `πA` agree conditionally on every
cell of `c` (product form), their partition experts on `c` have the same rows. This is T3's (⇐)
step as a statement of its own: cross-prior Total Trust in a partition expert is identity of
that expert with the deferrer's own partition expert (`totalTrust_ofPartition_cross_iff`), so
every "cross-prior" link in a partition-expert chain is a self-instance at the frame level
(`T4.FA_P_eq_own`, `T4.FB_P_eq_own`).
Source: trust-lab-064 (the (⇐) direction of `TT_condExpert_cross_iff`); audit r1 fidelity N3
Kind: L
Fidelity: n/a -/
theorem Frame.ofPartition_P_eq_of_agree {ι : Type} [DecidableEq ι] {πH πA : W → ℝ}
    (hposH : ∀ w, 0 < πH w) (hposA : ∀ w, 0 < πA w) (c : W → ι)
    (hagree : ∀ v, πA v * mass πH (Corr.ofMap c v) = πH v * mass πA (Corr.ofMap c v)) :
    (Frame.ofPartition πH hposH c).P = (Frame.ofPartition πA hposA c).P := by
  funext w v
  rw [Frame.ofPartition_P_apply, Frame.ofPartition_P_apply]
  by_cases hcv : c v = c w
  · rw [if_pos hcv, if_pos hcv]
    have hcell : Corr.ofMap c v = Corr.ofMap c w := by
      ext x; simp [Corr.mem_ofMap, hcv]
    have hmA : 0 < mass πA (Corr.ofMap c v) :=
      Corr.mass_pos_of_reflexive hposA (Corr.ofMap_partitional c).1 v
    have hmH : 0 < mass πH (Corr.ofMap c v) :=
      Corr.mass_pos_of_reflexive hposH (Corr.ofMap_partitional c).1 v
    rw [← hcell, div_eq_div_iff hmH.ne' hmA.ne']
    have := hagree v
    linarith
  · rw [if_neg hcv, if_neg hcv, zero_div, zero_div]

/-- **T3 (load-bearing 2).** For full-support priors `πH, πA` and any map `c`: `πH` totally
trusts the `πA`-partition expert of `c` **iff** the two priors' conditional probabilities agree
within every cell, in product form `πA v · πH(cell v) = πH v · πA(cell v)` for every `v`.
(⇐) the expert equals `πH`'s own partition expert, then T1; (⇒) the contrapositive through the
pivot step and the mismatch witness. So the first expert's partition is irrelevant to the long
edge, and prior identity is sufficient but not necessary (`Chains.lean`, `sharper_recovery`).
Source: trust-lab-064 `TT_condExpert_cross_iff`
Kind: P
Fidelity: exact (product form of the source's ratio statement; ratio and product forms agree
under `hpos`)
Hyps: (a) `hposH`, `hposA` full support (the source's standing assumption; without it the ratio
form is junk on null cells) -/
theorem totalTrust_ofPartition_cross_iff {ι : Type} [DecidableEq ι] {πH πA : W → ℝ}
    (hposH : ∀ w, 0 < πH w) (hposA : ∀ w, 0 < πA w) (c : W → ι) :
    TotalTrust πH (Frame.ofPartition πA hposA c) ↔
      ∀ v, πA v * mass πH (Corr.ofMap c v) = πH v * mass πA (Corr.ofMap c v) := by
  constructor
  · intro h v
    by_contra hne
    obtain ⟨u, hu⟩ := exists_mismatch_of_ne hposH hposA c v hne
    exact not_totalTrust_ofPartition_of_mismatch hposH hposA c u hu h
  · intro hagree
    exact totalTrust_of_P_eq (Frame.ofPartition_P_eq_of_agree hposH hposA c hagree)
      (totalTrust_ofPartition hposH c)

/-! ## T5: thresholds are redundant; the support-set reduction -/

/-- **T5(a).** Thresholds are redundant in Total Trust: since rows sum to one,
`E_{P_w}(X − s) = E_{P_w}(X) − s`, so the record form at `(X, s)` is the record form at
`(X − s, 0)`. Total Trust is `∀ X, 0 ≤ ∑ w, π w · X w · 𝟙[0 ≤ E_{P_w}(X)]`.
Source: trust-lab-065 (the reduction's first step); DDB §2 (rows sum to one)
Kind: P
Fidelity: exact
Hyps: (a) none beyond the frame's row-stochasticity -/
theorem totalTrust_iff_zero_threshold {π : W → ℝ} {F : Frame W} :
    TotalTrust π F ↔ ∀ X : W → ℝ, 0 ≤ ∑ w, π w * X w * (if 0 ≤ E (F.P w) X then 1 else 0) := by
  constructor
  · intro h X
    have := h X 0
    simpa using this
  · intro h X s
    have := h (fun w => X w - s)
    have hE : ∀ w, E (F.P w) (fun w => X w - s) = E (F.P w) X - s := by
      intro w
      have := E_sub_right (F.P w) X (fun _ => s)
      rw [E_const (F.P_mem w)] at this
      exact this
    simp only [hE, sub_nonneg] at this
    exact this

/-- Total Trust as: for every `X`, the `π`-weighted sum of `X` over the event `[E(X) ≥ 0]` is
nonnegative.
Source: none: infrastructure (T5)
Kind: L
Fidelity: n/a -/
theorem totalTrust_iff_estEvent_zero {π : W → ℝ} {F : Frame W} :
    TotalTrust π F ↔ ∀ X : W → ℝ, 0 ≤ ∑ w ∈ F.estEvent X 0, π w * X w := by
  rw [totalTrust_iff_zero_threshold]
  apply forall_congr'
  intro X
  rw [Frame.estEvent, sum_filter]
  simp [mul_ite]

/-- **T5(b), the support-set reduction.** Total Trust fails iff some nonempty support set `S`
carries the homogeneous system "`E_{P_w}(X) ≥ 0` on `S`, `E_{P_w}(X) < 0` off `S`, and
`∑_{w ∈ S} π w X w < 0`". `S.Nonempty` is forced: an empty event gives mass `0`. Every later
"Total Trust fails" witness in the package is an instance.
Source: trust-lab-065 (`tt_search.py` header, the reduction)
Kind: P
Fidelity: exact (the source states it with thresholds; T5(a) removes them)
Hyps: (a) none -/
theorem not_totalTrust_iff_exists_support {π : W → ℝ} {F : Frame W} :
    ¬ TotalTrust π F ↔ ∃ S : Finset W, S.Nonempty ∧ ∃ X : W → ℝ,
      (∀ w ∈ S, 0 ≤ E (F.P w) X) ∧ (∀ w ∉ S, E (F.P w) X < 0) ∧ ∑ w ∈ S, π w * X w < 0 := by
  rw [totalTrust_iff_estEvent_zero]
  constructor
  · intro h
    push Not at h
    obtain ⟨X, hX⟩ := h
    refine ⟨F.estEvent X 0, ?_, X, fun w hw => ?_, fun w hw => ?_, hX⟩
    · rw [nonempty_iff_ne_empty]
      intro he
      rw [he, sum_empty] at hX
      exact lt_irrefl _ hX
    · exact Frame.mem_estEvent.1 hw
    · have := Frame.mem_estEvent.not.1 hw
      exact not_le.1 this
  · rintro ⟨S, _, X, hin, hout, hneg⟩ h
    have hS : F.estEvent X 0 = S := by
      ext w
      rw [Frame.mem_estEvent]
      constructor
      · intro hw
        by_contra hnot
        exact absurd hw (not_le.2 (hout w hnot))
      · exact hin w
    have := h X
    rw [hS] at this
    linarith

end

end Cleanroom.Trust.TtFiniteFrames
