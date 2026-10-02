import Cleanroom.Lit.LitDdbFacts.Reflection
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Extreme

/-!
# The geometry of deserved deference (§4): Facts 4.2, 4.3 and Corollaries 4.4, 4.5

Package `lit-ddb-facts`, Targets 10–12. Which principle a *frame* validates (every row defers to
it): Reflection iff every row is immodest or in the hull of its other candidates (Fact 4.2), New
Reflection iff every row is in the hull of its candidates' informed selves (Fact 4.3), Total
Trust iff every row is modestly informed in the *unguarded* sense (Corollary 4.5). DDB's
footnote proofs of the converses of 4.2 and 4.3 each rest on an unstated step: 4.2 (⇐) uses
"`P_j` is in the convex hull of the immodest extreme rows" without the Minkowski/Krein–Milman
theorem that gives it, and 4.3 (⇐) — complete in the PDF, across the p. 28/29 break —
presupposes a positive self-cell at every candidate (the reading NR-str). Both steps are supplied
here, the second through the disjoint supports of the informed vectors, which pin the weights. Corollary 4.5 is false under the *guarded*
`Frame.ModestlyInformed` frozen by `lit-ddb-frames` (the witness is `nullSelf` in
`Examples.lean`) and is stated here with `ModestlyInformedU`.
-/

namespace Cleanroom.Lit.LitDdbFacts

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Total probability under Reflection and New Reflection (fns 58, 59) -/

/-- **Fn 58.** Under Reflection, `ρ = ∑_{σ ∈ C_ρ} ρ(P = σ) σ` (total probability then
Reflection on each cell).
Source: [[Deference Done Better]] fn 58
Kind: P
Fidelity: exact
Hyps: (a) nonnegativity of `ρ` -/
theorem reflects_eq_sum_cands {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) {F : Frame W}
    (h : Reflects ρ F) : ∑ σ ∈ F.cands ρ, mass ρ (F.cell σ) • σ = ρ := by
  funext w
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have : ∀ σ ∈ F.cands ρ, mass ρ (F.cell σ) * σ w = ρ w * ind (F.cell σ) w :=
    fun σ hσ => (h σ hσ w).symm
  rw [sum_congr rfl this]
  simp only [ind, Frame.mem_cell, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with hc
  · rfl
  · have : ρ w = 0 := by
      by_contra hne
      exact hc (F.P_mem_cands (lt_of_le_of_ne (hρ w) (Ne.symm hne)))
    exact this.symm

/-- **Fn 59 (⇒).** Under New Reflection, `ρ = ∑_{σ ∈ C_ρ} ρ(P = σ) P̂_σ`.
Source: [[Deference Done Better]] fn 59
Kind: P
Fidelity: exact
Hyps: (a) nonnegativity of `ρ` -/
theorem newReflects_eq_sum_informed {ρ : W → ℝ} (hρ : ∀ w, 0 ≤ ρ w) {F : Frame W}
    (h : NewReflects ρ F) : ∑ σ ∈ F.cands ρ, mass ρ (F.cell σ) • F.informed σ = ρ := by
  funext w
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have : ∀ σ ∈ F.cands ρ, mass ρ (F.cell σ) * F.informed σ w = ρ w * ind (F.cell σ) w := by
    intro σ hσ
    obtain ⟨hpos, hid⟩ := h σ hσ
    have hw' := hid w
    by_cases hw : F.P w = σ
    · have hind : ind (F.cell σ) w = 1 := by simp [ind, hw]
      rw [hind, mul_one, mul_one] at hw'
      rw [hind, mul_one]
      apply mul_right_cancel₀ hpos.ne'
      rw [mul_assoc, F.informed_mul_selfMass hpos hw]
      exact hw'.symm
    · rw [F.informed_eq_zero_of_ne hw, show ind (F.cell σ) w = 0 by simp [ind, hw]]
      ring
  rw [sum_congr rfl this]
  simp only [ind, Frame.mem_cell, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  split_ifs with hc
  · rfl
  · have : ρ w = 0 := by
      by_contra hne
      exact hc (F.P_mem_cands (lt_of_le_of_ne (hρ w) (Ne.symm hne)))
    exact this.symm

/-- An immodest distribution reflects the frame (its only candidate is itself).
Source: [[Deference Done Better]] fn 57 ("Reflection holds throughout `B`")
Kind: L
Fidelity: n/a -/
theorem reflects_self_of_selfMass_eq_one (F : Frame W) {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W)
    (h : F.selfMass ρ = 1) : Reflects ρ F := by
  intro σ hσ w
  rw [cands_eq_singleton_of_selfMass_eq_one F hρ h, mem_singleton] at hσ
  rw [hσ]
  have h1 : mass ρ (F.cell ρ) = 1 := h
  rw [h1, one_mul]
  by_cases hw : F.P w = ρ
  · simp [ind, hw]
  · rw [eq_zero_of_selfMass_eq_one F hρ h hw]
    simp [ind, hw]

/-! ## Target 10: Fact 4.2 -/

/-- **The extreme-point step of fn 57 (⇐), made into a proof.** If every row is immodest or in
the hull of its other candidates, then every row is a convex combination of *immodest* rows:
an extreme point of the hull of all rows is a row outside the hull of the other rows, hence
immodest; by Krein–Milman the hull of the rows is the hull of its extreme points.
Source: [[Deference Done Better]] fn 57 (gap filled: "`P_j` is in the convex hull of the
immodest `B`" is asserted, not proved)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem rows_mem_convexHull_immodest (F : Frame W)
    (H : ∀ i, F.selfMass (F.P i) = 1 ∨
      F.P i ∈ convexHull ℝ (↑(F.candsMinus (F.P i)) : Set (W → ℝ))) (i : W) :
    F.P i ∈ convexHull ℝ
      (↑((univ.image F.P).filter (fun ρ => F.selfMass ρ = 1)) : Set (W → ℝ)) := by
  classical
  set A : Finset (W → ℝ) := univ.image F.P with hA
  have hKc : IsCompact (convexHull ℝ (↑A : Set (W → ℝ))) := A.finite_toSet.isCompact_convexHull ℝ
  have hKv : Convex ℝ (convexHull ℝ (↑A : Set (W → ℝ))) := convex_convexHull ℝ _
  have hext : (convexHull ℝ (↑A : Set (W → ℝ))).extremePoints ℝ ⊆
      ↑(A.filter (fun ρ => F.selfMass ρ = 1)) := by
    intro x hx
    have hxA : x ∈ A := extremePoints_convexHull_subset hx
    rw [mem_coe, mem_filter]
    refine ⟨hxA, ?_⟩
    obtain ⟨j, _, rfl⟩ := mem_image.1 hxA
    rcases H j with h | h
    · exact h
    · exfalso
      rw [hKv.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff] at hx
      apply hx.2
      refine convexHull_mono ?_ h
      intro y hy
      rw [mem_coe, Frame.mem_candsMinus] at hy
      obtain ⟨hne, hyc⟩ := hy
      obtain ⟨v, _, rfl⟩ := Frame.mem_cands.1 hyc
      refine ⟨subset_convexHull ℝ _ (mem_coe.2 (mem_image_of_mem F.P (mem_univ v))), ?_⟩
      exact fun e => hne (Set.mem_singleton_iff.1 e)
  have hfin : ((convexHull ℝ (↑A : Set (W → ℝ))).extremePoints ℝ).Finite :=
    (A.filter _).finite_toSet.subset hext
  have hKM := closure_convexHull_extremePoints hKc hKv
  rw [(hfin.isClosed_convexHull ℝ).closure_eq] at hKM
  have hi : F.P i ∈ convexHull ℝ (↑A : Set (W → ℝ)) :=
    subset_convexHull ℝ _ (mem_coe.2 (mem_image_of_mem F.P (mem_univ i)))
  rw [← hKM] at hi
  exact convexHull_mono hext hi

/-- **A convex combination of immodest rows reflects the frame.** With
`ρ = ∑_{σ ∈ B} λ_σ σ` and every `σ ∈ B` immodest (supported on its own cell), a candidate `τ` of
`ρ` must be in `B` (only `τ` itself puts mass on `[P = τ]`), `ρ(P = τ) = λ_τ`, and on the cell
`ρ w = λ_τ τ w`.
Source: [[Deference Done Better]] fn 57 (⇐), the computation `P_j(q | P = P_k) = P_k(q)`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem reflects_of_mem_convexHull_immodest (F : Frame W) {ρ : W → ℝ}
    (hρ : ρ ∈ stdSimplex ℝ W) {B : Finset (W → ℝ)}
    (hB : ∀ σ ∈ B, σ ∈ stdSimplex ℝ W ∧ F.selfMass σ = 1)
    (h : ρ ∈ convexHull ℝ (↑B : Set (W → ℝ))) : Reflects ρ F := by
  obtain ⟨lam, _, _, hρeq⟩ := Finset.mem_convexHull'.1 h
  intro τ hτ w
  have hm : 0 < mass ρ (F.cell τ) := (F.mem_cands_iff_mass_cell_pos hρ.1).1 hτ
  have hmass : mass ρ (F.cell τ) = ∑ σ ∈ B, lam σ * mass σ (F.cell τ) := by
    rw [← hρeq, mass_sum_left]
  have hkey : ∀ σ ∈ B, σ ≠ τ → mass σ (F.cell τ) = 0 := by
    intro σ hσ hne
    apply sum_eq_zero
    intro v hv
    rw [Frame.mem_cell] at hv
    exact eq_zero_of_selfMass_eq_one F (hB σ hσ).1 (hB σ hσ).2 (by rw [hv]; exact hne.symm)
  have hτB : τ ∈ B := by
    by_contra hnot
    have : ∑ σ ∈ B, lam σ * mass σ (F.cell τ) = 0 :=
      sum_eq_zero fun σ hσ => by rw [hkey σ hσ (fun e => hnot (e ▸ hσ)), mul_zero]
    rw [← hmass] at this
    linarith
  have hmτ : mass ρ (F.cell τ) = lam τ := by
    rw [hmass, sum_eq_single τ]
    · have : mass τ (F.cell τ) = 1 := (hB τ hτB).2
      rw [this, mul_one]
    · intro σ hσ hne
      rw [hkey σ hσ hne, mul_zero]
    · intro habs; exact absurd hτB habs
  have hρw : ∀ u, ρ u = ∑ σ ∈ B, lam σ * σ u := by
    intro u
    rw [← hρeq, Finset.sum_apply]
    simp [Pi.smul_apply]
  by_cases hw : F.P w = τ
  · rw [show ind (F.cell τ) w = 1 by simp [ind, hw], mul_one, hmτ, hρw w, sum_eq_single τ]
    · intro σ hσ hne
      rw [eq_zero_of_selfMass_eq_one F (hB σ hσ).1 (hB σ hσ).2 (by rw [hw]; exact hne.symm),
        mul_zero]
    · intro habs; exact absurd hτB habs
  · rw [show ind (F.cell τ) w = 0 by simp [ind, hw], mul_zero,
      eq_zero_of_selfMass_eq_one F (hB τ hτB).1 (hB τ hτB).2 hw, mul_zero]

/-- **Target 10 (Fact 4.2).** A frame validates Reflection iff every row `P_i` is immodest
(`P_i(P = P_i) = 1`, the row condition) or lies in the convex hull of `C_i⁻`. (⇒) fn 57/58: a
positive self-cell makes `P_i` its own candidate, hence immodest by Target 1; a null self-cell
makes `C_i = C_i⁻` and fn 58 gives the hull membership. (⇐) via `rows_mem_convexHull_immodest`
and `reflects_of_mem_convexHull_immodest` — fn 57's converse asserts the extreme-point step
without proof.
Source: [[Deference Done Better]] §4 l. 339 (Fact 4.2), fns 57–58; item 067
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem validates_reflects_iff (F : Frame W) :
    F.Validates Reflects ↔ ∀ i, F.selfMass (F.P i) = 1 ∨
      F.P i ∈ convexHull ℝ (↑(F.candsMinus (F.P i)) : Set (W → ℝ)) := by
  constructor
  · intro h i
    have hi := h i
    rcases (mass_nonneg (F.P_nonneg i) (F.cell (F.P i))).lt_or_eq with hpos | hzero
    · left
      exact selfMass_eq_one_of_reflects (F.P_nonneg i) hi
        ((mem_cands_self_iff F (F.P_nonneg i)).2 hpos)
    · right
      have hzero' : F.selfMass (F.P i) = 0 := hzero.symm
      have hnot : F.P i ∉ F.cands (F.P i) := by
        rw [mem_cands_self_iff F (F.P_nonneg i), hzero']
        exact lt_irrefl _
      have hcm : F.candsMinus (F.P i) = F.cands (F.P i) := erase_eq_of_notMem hnot
      have hsum := reflects_eq_sum_cands (F.P_nonneg i) hi
      have key : (∑ σ ∈ F.cands (F.P i), mass (F.P i) (F.cell σ) • σ) ∈
          convexHull ℝ (↑(F.cands (F.P i)) : Set (W → ℝ)) := by
        apply (convex_convexHull ℝ _).sum_mem
        · intro σ _; exact mass_nonneg (F.P_nonneg i) _
        · exact sum_cands_mass_cell F (F.P_mem i)
        · intro σ hσ; exact subset_convexHull ℝ _ (mem_coe.2 hσ)
      rw [hsum] at key
      rw [hcm]
      exact key
  · intro H i
    exact reflects_of_mem_convexHull_immodest F (F.P_mem i)
      (fun σ hσ => ⟨by
        obtain ⟨j, _, rfl⟩ := mem_image.1 (mem_filter.1 hσ).1
        exact F.P_mem j, (mem_filter.1 hσ).2⟩)
      (rows_mem_convexHull_immodest F H i)

/-- Under validated Reflection every row's self-cell mass is `0` or `1` (fn 61's silent
dichotomy, made explicit).
Source: [[Deference Done Better]] fns 57, 61
Kind: L
Fidelity: n/a -/
theorem selfMass_eq_zero_or_one_of_validates {F : Frame W} (h : F.Validates Reflects) (i : W) :
    F.selfMass (F.P i) = 0 ∨ F.selfMass (F.P i) = 1 := by
  rcases (mass_nonneg (F.P_nonneg i) (F.cell (F.P i))).lt_or_eq with hpos | hzero
  · right
    exact selfMass_eq_one_of_reflects (F.P_nonneg i) (h i)
      ((mem_cands_self_iff F (F.P_nonneg i)).2 hpos)
  · left
    exact hzero.symm

/-! ## Target 11: Fact 4.3 -/

/-- **Target 11 (Fact 4.3), reading NR-str.** A frame validates New Reflection iff every row
`P_i` lies in the convex hull of `{P̂_j : P_j ∈ C_i}` — with the junk `P̂ = 0` of a null self-cell
*included* in the image (the sum-to-one constraint forces zero weight on it). (⇒) fn 59.
(⇐), whose one-line computation in fn 59 (complete in the PDF, across the p. 28/29 break)
presupposes that `P_i(· | P̂ = P̂_k)` is defined and that every `P̂_j` is immodest, i.e. positive
self-cells at every candidate: the `P̂_j` have pairwise disjoint supports, so in any
convex representation the weight on `P̂_j` is `P_i(P = P_j)`; a candidate with a null self-cell
would receive mass `0` from every `P̂`, contradicting candidacy — so the strong reading, not the
vacuous one (`swap2` in `Examples.lean` refutes the NR-vac reading of this Fact).
Source: [[Deference Done Better]] §4 l. 347 (Fact 4.3), fn 59; item 068
Kind: P
Fidelity: exact (NR-str)
Hyps: (a) none -/
theorem validates_newReflects_iff (F : Frame W) :
    F.Validates NewReflects ↔
      ∀ i, F.P i ∈ convexHull ℝ (↑((F.cands (F.P i)).image F.informed) : Set (W → ℝ)) := by
  constructor
  · intro h i
    have key := newReflects_eq_sum_informed (F.P_nonneg i) (h i)
    have : (∑ σ ∈ F.cands (F.P i), mass (F.P i) (F.cell σ) • F.informed σ) ∈
        convexHull ℝ (↑((F.cands (F.P i)).image F.informed) : Set (W → ℝ)) := by
      apply (convex_convexHull ℝ _).sum_mem
      · intro σ _; exact mass_nonneg (F.P_nonneg i) _
      · exact sum_cands_mass_cell F (F.P_mem i)
      · intro σ hσ
        exact subset_convexHull ℝ _ (mem_coe.2 (mem_image_of_mem F.informed hσ))
    rw [key] at this
    exact this
  · intro H i σ hσ
    have hρ := F.P_mem i
    obtain ⟨lam, _, _, hρeq⟩ := Finset.mem_convexHull'.1 (H i)
    have hm : 0 < mass (F.P i) (F.cell σ) := (F.mem_cands_iff_mass_cell_pos hρ.1).1 hσ
    have hσs := F.mem_stdSimplex_of_mem_cands hσ
    have hmass : mass (F.P i) (F.cell σ) =
        ∑ τ ∈ (F.cands (F.P i)).image F.informed, lam τ * mass τ (F.cell σ) := by
      conv_lhs => rw [← hρeq]
      rw [mass_sum_left]
    have hoff : ∀ τ ∈ (F.cands (F.P i)).image F.informed, τ ≠ F.informed σ →
        mass τ (F.cell σ) = 0 := by
      intro τ hτ hne
      obtain ⟨σ', _, rfl⟩ := mem_image.1 hτ
      have hne' : σ' ≠ σ := fun e => hne (congrArg F.informed e)
      exact F.mass_informed_cell_of_ne hne'
    have hinf_mem : F.informed σ ∈ (F.cands (F.P i)).image F.informed := mem_image_of_mem _ hσ
    have hmass' : mass (F.P i) (F.cell σ) =
        lam (F.informed σ) * mass (F.informed σ) (F.cell σ) := by
      rw [hmass, sum_eq_single (F.informed σ)]
      · intro τ hτ hne
        rw [hoff τ hτ hne, mul_zero]
      · intro habs; exact absurd hinf_mem habs
    clear hmass
    have hmass := hmass'
    have hpos : 0 < F.selfMass σ := by
      by_contra hnot
      have h0 : F.selfMass σ = 0 := le_antisymm (not_lt.1 hnot) (mass_nonneg hσs.1 _)
      have hz := (informed_eq_zero_iff F hσs.1).2 h0
      rw [hz] at hmass
      have : mass (0 : W → ℝ) (F.cell σ) = 0 := by simp [mass]
      rw [this, mul_zero] at hmass
      linarith
    refine ⟨hpos, fun w => ?_⟩
    have hic : mass (F.informed σ) (F.cell σ) = 1 := by
      have := F.mass_informed_cell_mul hpos
      exact (mul_left_inj' hpos.ne').1 (by rw [this, one_mul])
    rw [hic, mul_one] at hmass
    have hρw : ∀ u, F.P i u = ∑ τ ∈ (F.cands (F.P i)).image F.informed, lam τ * τ u := by
      intro u
      conv_lhs => rw [← hρeq]
      rw [Finset.sum_apply]
      simp [Pi.smul_apply]
    by_cases hw : F.P w = σ
    · have hind : ind (F.cell σ) w = 1 := by simp [ind, hw]
      rw [hind, mul_one, mul_one, hmass, hρw w, sum_eq_single (F.informed σ)]
      · rw [mul_assoc, F.informed_mul_selfMass hpos hw]
      · intro τ hτ hne
        obtain ⟨σ', _, rfl⟩ := mem_image.1 hτ
        have hne' : F.P w ≠ σ' := fun e => hne (by rw [← e, hw])
        rw [F.informed_eq_zero_of_ne hne', mul_zero]
      · intro habs; exact absurd hinf_mem habs
    · have hind : ind (F.cell σ) w = 0 := by simp [ind, hw]
      rw [hind]
      ring

/-! ## Target 12: the unguarded modest-informedness and Corollaries 4.4, 4.5 -/

/-- **Modestly informed, unguarded**: `ρ ∈ convexHull ({P̂_ρ} ∪ C_ρ⁻)` with no positivity clause
on the self-cell — DDB's literal fn 54, read with the junk `P̂_ρ = 0` at a null self-cell (where
the sum-to-one constraint forces `λ_ρρ = 0`, fn 61's silent reading). `lit-ddb-frames`' guarded
`Frame.ModestlyInformed` adds `0 < ρ(P = ρ)`; the two agree exactly when the self-cell is
positive (`modestlyInformedU_iff_of_pos`).
Source: [[Deference Done Better]] fn 54, fn 61
Kind: D
Fidelity: exact (DDB's literal reading; the guarded one is `Frame.ModestlyInformed`) -/
def ModestlyInformedU (F : Frame W) (ρ : W → ℝ) : Prop :=
  ρ ∈ convexHull ℝ (insert (F.informed ρ) (↑(F.candsMinus ρ) : Set (W → ℝ)))

/-- The λ-form of unguarded modest informedness: nonnegative weights on `{P̂_ρ} ∪ C_ρ⁻` summing to
one with `∑ λ y • y = ρ`.
Source: [[Deference Done Better]] fn 54 (the weights `λ_ij`)
Kind: L
Fidelity: exact -/
theorem modestlyInformedU_iff_weights (F : Frame W) (ρ : W → ℝ) :
    ModestlyInformedU F ρ ↔ ∃ c : (W → ℝ) → ℝ,
      (∀ y ∈ insert (F.informed ρ) (F.candsMinus ρ), 0 ≤ c y) ∧
      ∑ y ∈ insert (F.informed ρ) (F.candsMinus ρ), c y = 1 ∧
      ∑ y ∈ insert (F.informed ρ) (F.candsMinus ρ), c y • y = ρ := by
  unfold ModestlyInformedU
  rw [← coe_insert, Finset.mem_convexHull']

/-- At a positive self-cell the unguarded and guarded predicates agree.
Source: none: infrastructure (Target 12)
Kind: L
Fidelity: n/a -/
theorem modestlyInformedU_iff_of_pos (F : Frame W) {ρ : W → ℝ} (hpos : 0 < F.selfMass ρ) :
    ModestlyInformedU F ρ ↔ F.ModestlyInformed ρ :=
  ⟨fun h => ⟨hpos, h⟩, fun h => h.2⟩

/-- At a null self-cell the unguarded predicate is hull membership over `C_ρ⁻` alone: the
weight on the junk `0` must vanish (coordinates sum to one).
Source: [[Deference Done Better]] fn 61 (the `λ_ii = 0` reading)
Kind: L
Fidelity: n/a -/
theorem modestlyInformedU_iff_of_zero (F : Frame W) {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W)
    (h0 : F.selfMass ρ = 0) :
    ModestlyInformedU F ρ ↔ ρ ∈ convexHull ℝ (↑(F.candsMinus ρ) : Set (W → ℝ)) := by
  have hz := (informed_eq_zero_iff F hρ.1).2 h0
  unfold ModestlyInformedU
  rw [hz]
  constructor
  · intro h
    rw [← coe_insert, Finset.mem_convexHull'] at h
    obtain ⟨c, hc₀, hc₁, hρeq⟩ := h
    have h0notin : (0 : W → ℝ) ∉ F.candsMinus ρ := by
      intro hmem
      have := (F.mem_stdSimplex_of_mem_cands (Frame.mem_candsMinus.1 hmem).2).2
      simp at this
    rw [sum_insert h0notin] at hc₁ hρeq
    rw [smul_zero, zero_add] at hρeq
    have hcoord : ∑ σ ∈ F.candsMinus ρ, c σ = 1 := by
      have := congrArg (fun v : W → ℝ => ∑ w, v w) hρeq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [sum_comm] at this
      have e : ∀ σ ∈ F.candsMinus ρ, ∑ w, c σ * σ w = c σ := by
        intro σ hσ
        rw [← mul_sum, (F.mem_stdSimplex_of_mem_cands (Frame.mem_candsMinus.1 hσ).2).2, mul_one]
      rw [sum_congr rfl e, hρ.2] at this
      exact this
    rw [Finset.mem_convexHull']
    exact ⟨c, fun y hy => hc₀ y (mem_insert_of_mem hy), hcoord, hρeq⟩
  · intro h
    exact convexHull_mono (Set.subset_insert _ _) h

/-- **Corollary 4.4.** A frame validates Reflection iff every row is modestly informed with
*extreme* weights: some λ-form representation has `λ_ii ∈ {0, 1}`. (Under validated Reflection
every self-cell mass is `0` or `1`, `selfMass_eq_zero_or_one_of_validates`, so per row `λ_ii = 1`
⟺ `P_i = P̂_i` ⟺ immodest row and `λ_ii = 0` ⟺ `P_i ∈ hull C_i⁻`. The weights are indexed by the
*set* `{P̂_i} ∪ C_i⁻`, which merges `λ_ii` with a `λ_ij` when `P̂_i` coincides with another
candidate; that cannot happen under validated Reflection, where `P̂_i` is `P_i` or the junk `0`,
so the iff is unaffected, but the per-row reading of `λ_ii` above needs that hypothesis.) A
rewriting of Fact 4.2.
Source: [[Deference Done Better]] §4 l. 359 (Corollary 4.4), fn 60; item 069
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem validates_reflects_iff_extremeWeights (F : Frame W) :
    F.Validates Reflects ↔ ∀ i, ∃ c : (W → ℝ) → ℝ,
      (∀ y ∈ insert (F.informed (F.P i)) (F.candsMinus (F.P i)), 0 ≤ c y) ∧
      ∑ y ∈ insert (F.informed (F.P i)) (F.candsMinus (F.P i)), c y = 1 ∧
      ∑ y ∈ insert (F.informed (F.P i)) (F.candsMinus (F.P i)), c y • y = F.P i ∧
      (c (F.informed (F.P i)) = 0 ∨ c (F.informed (F.P i)) = 1) := by
  constructor
  · intro h i
    rcases selfMass_eq_zero_or_one_of_validates h i with h0 | h1
    · rcases (validates_reflects_iff F).1 h i with h1 | h2
      · exfalso; rw [h0] at h1; exact zero_ne_one h1
      · have hz := (informed_eq_zero_iff F (F.P_nonneg i)).2 h0
        have h0notin : F.informed (F.P i) ∉ F.candsMinus (F.P i) := by
          rw [hz]
          intro hmem
          have := (F.mem_stdSimplex_of_mem_cands (Frame.mem_candsMinus.1 hmem).2).2
          simp at this
        obtain ⟨c', hc₀, hc₁, hceq⟩ := Finset.mem_convexHull'.1 h2
        refine ⟨Function.update c' (F.informed (F.P i)) 0, ?_, ?_, ?_,
          Or.inl (Function.update_self _ _ _)⟩
        · intro y hy
          rcases eq_or_ne y (F.informed (F.P i)) with rfl | hne
          · rw [Function.update_self]
          · rw [Function.update_of_ne hne]
            exact hc₀ y (mem_of_mem_insert_of_ne hy hne)
        · rw [sum_insert h0notin, Function.update_self, zero_add, ← hc₁]
          apply sum_congr rfl
          intro y hy
          rw [Function.update_of_ne (show y ≠ F.informed (F.P i) from fun e => h0notin (e ▸ hy))]
        · rw [sum_insert h0notin, Function.update_self, zero_smul, zero_add]
          conv_rhs => rw [← hceq]
          apply sum_congr rfl
          intro y hy
          rw [Function.update_of_ne (show y ≠ F.informed (F.P i) from fun e => h0notin (e ▸ hy))]
    · have hinf : F.informed (F.P i) = F.P i := (informed_eq_self_iff F (F.P_mem i)).2 h1
      have hnotin : F.informed (F.P i) ∉ F.candsMinus (F.P i) := by
        rw [hinf]
        exact notMem_erase _ _
      refine ⟨Function.update (fun _ => (0 : ℝ)) (F.informed (F.P i)) 1, ?_, ?_, ?_,
        Or.inr (Function.update_self _ _ _)⟩
      · intro y _
        rcases eq_or_ne y (F.informed (F.P i)) with rfl | hne
        · rw [Function.update_self]
          exact zero_le_one
        · simp [Function.update_of_ne hne]
      · rw [sum_insert hnotin, Function.update_self, sum_eq_zero, add_zero]
        intro y hy
        rw [Function.update_of_ne (show y ≠ F.informed (F.P i) from fun e => hnotin (e ▸ hy))]
      · rw [sum_insert hnotin, Function.update_self, one_smul, sum_eq_zero, add_zero, hinf]
        intro y hy
        simp [Function.update_of_ne (show y ≠ F.informed (F.P i) from fun e => hnotin (e ▸ hy))]
  · intro H
    rw [validates_reflects_iff]
    intro i
    obtain ⟨c, hc₀, hc₁, hceq, hc⟩ := H i
    rcases hc with h0 | h1
    · right
      apply mem_convexHull_of_weights_subset hc₀ hc₁ hceq
      intro y hy hpos
      rcases mem_insert.1 hy with rfl | hy'
      · rw [h0] at hpos; exact absurd hpos (lt_irrefl _)
      · exact mem_coe.2 hy'
    · left
      have hmem := mem_insert_self (F.informed (F.P i)) (F.candsMinus (F.P i))
      have hrest : ∑ y ∈ (insert (F.informed (F.P i)) (F.candsMinus (F.P i))).erase
          (F.informed (F.P i)), c y = 0 := by
        have := sum_erase_add _ c hmem
        rw [hc₁, h1] at this
        linarith
      have hzero : ∀ y ∈ insert (F.informed (F.P i)) (F.candsMinus (F.P i)),
          y ≠ F.informed (F.P i) → c y = 0 := by
        intro y hy hne
        exact (sum_eq_zero_iff_of_nonneg (fun z hz => hc₀ z (mem_of_mem_erase hz))).1 hrest y
          (mem_erase.2 ⟨hne, hy⟩)
      have hself : F.P i = F.informed (F.P i) := by
        conv_lhs => rw [← hceq]
        rw [sum_eq_single (F.informed (F.P i))]
        · rw [h1, one_smul]
        · intro y hy hne
          rw [hzero y hy hne, zero_smul]
        · intro habs; exact absurd hmem habs
      exact (informed_eq_self_iff F (F.P_mem i)).1 hself.symm

/-- **Target 12, headline (Corollary 4.5), with the correction.** A frame validates Total Trust
iff every row is modestly informed in the *unguarded* sense. (⇒) Theorem 4.1 at `π := P_i`, with
fn 61's case split on `P_i(P = P_i) > 0`. (⇐) every candidate's unguarded modest informedness
gives the abstract decomposition, so `Frame.selfMass_pos_of_hull` supplies the guard at every
candidate and Theorem 4.1's fourth condition holds. With the *guarded* `Frame.ModestlyInformed`
in place of `ModestlyInformedU` the (⇒) direction is **false** (`nullSelf` in `Examples.lean`).
Source: [[Deference Done Better]] §4 l. 363 (Corollary 4.5), fn 61; item 069
Kind: C
Fidelity: exact (unguarded reading; the guarded reading is refuted)
Hyps: (a) none -/
theorem validates_totalTrust_iff (F : Frame W) :
    F.Validates TotalTrust ↔ ∀ i, ModestlyInformedU F (F.P i) := by
  constructor
  · intro h i
    have hπ := F.P_mem i
    have hmi := (totalTrust_iff_hullAndModestlyInformed hπ F).1 (h i)
    rcases (mass_nonneg hπ.1 (F.cell (F.P i))).lt_or_eq with hpos | hzero
    · exact (hmi.2 _ ((mem_cands_self_iff F hπ.1).2 hpos)).2
    · have hzero' : F.selfMass (F.P i) = 0 := hzero.symm
      rw [modestlyInformedU_iff_of_zero F hπ hzero']
      have hnot : F.P i ∉ F.cands (F.P i) := by
        rw [mem_cands_self_iff F hπ.1, hzero']
        exact lt_irrefl _
      rw [Frame.candsMinus, erase_eq_of_notMem hnot]
      exact hmi.1
  · intro H i
    have hπ := F.P_mem i
    rw [totalTrust_iff_hullAndModestlyInformed hπ F]
    have hdec : F.DecompOver (F.P i) := fun ρ hρ =>
      ⟨F.candsMinus ρ, fun σ hσ => by
        obtain ⟨hne, hσc⟩ := Frame.mem_candsMinus.1 hσ
        obtain ⟨v, hv, rfl⟩ := Frame.mem_cands.1 hσc
        exact ⟨hne, v, rfl, Or.inr hv⟩, by
          obtain ⟨v, _, rfl⟩ := Frame.mem_cands.1 hρ
          exact H v⟩
    have hhull : F.P i ∈ convexHull ℝ (↑(F.cands (F.P i)) : Set (W → ℝ)) := by
      rcases (mass_nonneg hπ.1 (F.cell (F.P i))).lt_or_eq with hpos | hzero
      · exact subset_convexHull ℝ _ (mem_coe.2 ((mem_cands_self_iff F hπ.1).2 hpos))
      · have hzero' : F.selfMass (F.P i) = 0 := hzero.symm
        have hnot : F.P i ∉ F.cands (F.P i) := by
          rw [mem_cands_self_iff F hπ.1, hzero']
          exact lt_irrefl _
        have := (modestlyInformedU_iff_of_zero F hπ hzero').1 (H i)
        rwa [Frame.candsMinus, erase_eq_of_notMem hnot] at this
    refine ⟨hhull, fun ρ hρ => ⟨F.selfMass_pos_of_hull hπ hhull hdec hρ, ?_⟩⟩
    obtain ⟨v, _, rfl⟩ := Frame.mem_cands.1 hρ
    exact H v

end

end Cleanroom.Lit.LitDdbFacts
