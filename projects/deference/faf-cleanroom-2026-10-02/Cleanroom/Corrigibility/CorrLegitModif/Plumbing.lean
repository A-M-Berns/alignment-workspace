import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Corrigibility.CorrReflectFrames.Selection
import Cleanroom.Trust.TtFiniteFrames.Partition

/-!
# corr-legit-modif — frame plumbing

General lemmas about frames whose rows are conditionals (`condRow`, `refineFrame`,
`Frame.ofPartition`), used by the Y1 legitimacy label (T1(b)), the reflection facts (T1(d)),
the confident-case construction (T7), the self-posterior frame (T8) and the reach lemma (T12).
Nothing here is a headline.
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Trust.TtFiniteFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-! ## Rows determine every predicate -/

/-- Reflection depends on a frame only through its rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem reflects_of_P_eq {π : W → ℝ} {F G : Frame W} (h : F.P = G.P) (hF : Reflects π F) :
    Reflects π G := by
  unfold Reflects Frame.cands Frame.cell at *
  rw [← h]; exact hF

/-- Reflection (candidate-wise, product form) implies Reflection with respect to every question:
sum the pointwise identity over a partial answer.
Source: none: infrastructure ([[Deference Done Better]] §5: the local principle is the global
one restricted to partial answers)
Kind: L
Fidelity: n/a -/
theorem reflectsWrt_of_reflects {π : W → ℝ} {F : Frame W} (h : Reflects π F) (Q : W → C) :
    ReflectsWrt Q π F := by
  intro ρ hρ T
  have key : ∀ w, π w * ind (F.cell ρ) w = mass π (F.cell ρ) * ρ w := h ρ hρ
  unfold mass
  rw [mul_sum]
  have e : ∑ w ∈ F.cell ρ ∩ answer Q T, π w = ∑ w ∈ answer Q T, π w * ind (F.cell ρ) w := by
    rw [inter_comm, ← filter_mem_eq_inter, sum_filter]
    apply sum_congr rfl; intro w _; unfold ind; split_ifs <;> simp
  rw [e]
  exact sum_congr rfl (fun w _ => key w)

/-! ## Conditional rows -/

/-- Two conditional rows coincide when one fibre sits inside the other and the deferrer vanishes
on the difference.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_eq_of_subset_null {S T : Type} [DecidableEq S] [DecidableEq T] {π : W → ℝ}
    {f : W → S} {g : W → T} {w u : W} (hsub : fibre g u ⊆ fibre f w)
    (hnull : ∀ v ∈ fibre f w, v ∉ fibre g u → π v = 0) (hpos : 0 < mass π (fibre g u)) :
    condRow π g u = condRow π f w := by
  have hm : mass π (fibre f w) = mass π (fibre g u) := by
    unfold mass; exact (sum_subset hsub (fun v hv hnv => hnull v hv hnv)).symm
  have hpos' : 0 < mass π (fibre f w) := hm ▸ hpos
  rw [condRow_of_pos hpos, condRow_of_pos hpos', hm]
  funext v
  by_cases hv : v ∈ fibre g u
  · have hv' : v ∈ fibre f w := hsub hv
    simp [ind, hv, hv']
  · by_cases hv' : v ∈ fibre f w
    · simp [ind, hv, hv', hnull v hv' hv]
    · simp [ind, hv, hv']

/-- Conditional rows along two maps with the same fibre through `w` coincide.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_eq_of_fibre_eq {S T : Type} [DecidableEq S] [DecidableEq T] {π : W → ℝ}
    {f : W → S} {g : W → T} {w : W} (h : fibre g w = fibre f w) : condRow π g w = condRow π f w := by
  unfold condRow; rw [h]

/-- The conditional row of the deferrer restricted to `L`, along `f`, is the conditional of `π`
on `fibre f w ∩ L` (product form), when that event has positive mass.
Source: none: infrastructure (the rows of an `L`-conditioned successor, T1(b))
Kind: L
Fidelity: n/a -/
theorem condRow_restrict_eq {S : Type} [DecidableEq S] (π : W → ℝ) (L : Finset W) (f : W → S)
    (w : W) (hpos : 0 < mass π (fibre f w ∩ L)) :
    condRow (restrict π L) f w =
      fun v => ind (fibre f w ∩ L) v * π v / mass π (fibre f w ∩ L) := by
  have hpos' : 0 < mass (restrict π L) (fibre f w) := by rw [mass_restrict]; exact hpos
  rw [condRow_of_pos hpos', mass_restrict]
  funext v
  congr 1
  simp only [ind, restrict_apply, mem_inter]
  split_ifs <;> simp_all

/-- A distribution supported inside `L` gives `L` mass one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_eq_one_of_supp_subset {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) {L : Finset W}
    (h : ∀ v, v ∉ L → ρ v = 0) : mass ρ L = 1 := by
  have h1 := (mem_stdSimplex_iff.1 hρ).2
  unfold mass
  rw [← h1]
  exact sum_subset (subset_univ L) (fun v _ hv => h v hv)

/-- **Rows of a restricted deferrer's refinement are certain of `L`**: on a fibre of positive
restricted mass, the conditional row of `restrict π L` gives `L` mass one.
Source: none: infrastructure (why an `L`-conditioned successor passes
`legitimizingTT_certain_of_legit`, T1(b))
Kind: L
Fidelity: n/a -/
theorem condRow_restrict_certain {S : Type} [DecidableEq S] {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    (L : Finset W) (f : W → S) (w : W) (hpos : 0 < mass (restrict π L) (fibre f w)) :
    mass (condRow (restrict π L) f w) L = 1 := by
  apply mass_eq_one_of_supp_subset (condRow_mem (restrict_nonneg hπ L) f w)
  intro v hv
  rw [condRow_of_pos hpos]
  simp [restrict_apply, hv]

/-- The Bayesian refinement of `π` reflects every restriction of `π` to a union of its fibres.
Source: none: infrastructure (the informed-deferrer half of T1(d))
Kind: L
Fidelity: n/a -/
theorem reflects_restrict_refineFrame {S : Type} [DecidableEq S] {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    (f : W → S) (A : Finset W) (hA : ∀ w ∈ A, ∀ v, f v = f w → v ∈ A) :
    Reflects (restrict π A) (refineFrame π hπ f) := by
  intro ρ hρ w
  obtain ⟨w₀, hw₀, rfl⟩ := Frame.mem_cands.1 hρ
  rw [restrict_apply] at hw₀
  split_ifs at hw₀ with hw₀A
  · have hfib : 0 < mass π (fibre f w₀) := mass_fibre_pos_of_pos hπ hw₀
    rw [refineFrame_P, cell_condRow hπ hfib, condRow_apply_of_pos hfib, mass_restrict]
    have hsub : fibre f w₀ ⊆ A := fun v hv => hA w₀ hw₀A v (mem_fibre.1 hv)
    rw [inter_eq_left.2 hsub, restrict_apply]
    by_cases hw : w ∈ fibre f w₀
    · have hwA : w ∈ A := hsub hw
      rw [if_pos hwA]
      simp only [ind, hw, if_true, mul_one, one_mul]
      field_simp
    · simp [ind, hw]
  · exact absurd hw₀ (lt_irrefl 0)

/-- The partition expert of a full-support prior is reflected by it: its rows are the
conditionals on its own cells.
Source: none: infrastructure (`tt-finite-frames` has the Total-Trust half,
`totalTrust_ofPartition`)
Kind: L
Fidelity: n/a -/
theorem reflects_ofPartition {ι : Type} [DecidableEq ι] {π : W → ℝ} (hpos : ∀ w, 0 < π w)
    (f : W → ι) : Reflects π (Frame.ofPartition π hpos f) := by
  intro ρ hρ w
  obtain ⟨w₀, -, rfl⟩ := Frame.mem_cands.1 hρ
  rw [Frame.ofPartition_cell, Frame.ofPartition_P_apply]
  have hm : 0 < mass π (Corr.ofMap f w₀) :=
    Corr.mass_pos_of_reflexive hpos (Corr.ofMap_partitional f).1 w₀
  rw [mul_div_cancel₀ _ hm.ne']
  simp only [ind, Corr.mem_ofMap]
  split_ifs <;> simp

/-! ## The one-candidate Reflection clause -/

/-- **The Reflection clause toward a row that contains the deferrer's support**: for an event
`A ⊆ [P = ρ]`, the candidate-`ρ` clause of Reflection from `restrict π A` says exactly that `ρ` is
the conditional of `π` on `A` (product form `π w · 𝟙_A w = π(A) · ρ w`). With `ρ = π(· | C)` for a
coarser `C ⊇ A`, the clause holds iff `π(· | A) = π(· | C)` — the general half of
corr-wf14b-2-002's conjecture: an installed state equal to the coarse conditional is reflected
from a refinement of the cell iff the refinement does not move the conditional.
Source: corr-wf14b-2-002 (the general half); [[hudson-respondent]] B2(b) l. 51
Kind: L
Fidelity: exact
Hyps: (a) `A ⊆ F.cell ρ` -/
theorem reflect_clause_iff_cond {π : W → ℝ} {F : Frame W} {ρ : W → ℝ} {A : Finset W}
    (hA : A ⊆ F.cell ρ) :
    (∀ w, restrict π A w * ind (F.cell ρ) w = mass (restrict π A) (F.cell ρ) * ρ w) ↔
      ∀ w, π w * ind A w = mass π A * ρ w := by
  rw [mass_restrict, inter_eq_right.2 hA]
  apply forall_congr'
  intro w
  rw [restrict_apply]
  by_cases hw : w ∈ A
  · simp [ind, hw, hA hw]
  · simp [ind, hw]

end

end Cleanroom.Corrigibility.CorrLegitModif
