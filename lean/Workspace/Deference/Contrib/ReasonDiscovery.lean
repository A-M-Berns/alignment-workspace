/-
# Reason discovery: the residual, the information-cell obstruction, and the composition

Round `projects/deference/rounds/2026-09-16-noncapture-compilation/`, third pass.

The second pass left one quantity outside the non-capture theorem: the adverse mass of
true declared reasons that no independent inquiry puts on the docket before commitment.
This module states that residual type-correctly, proves the two facts about it that
hold in every finite inquiry model, and composes it with the second-pass theorem.

**1. The residual** (`adverseAbove_union`): with a *conditional* adverse certificate
`A_{r|D}` (how much adding `r` can lower the verdict on contents that already contain
the docket `D`), the advisor's gain from the undiscovered reasons is at most their
conditional adverse mass: `F D − F (D ∪ S) ≤ Σ_{r ∈ S} A r`.

**2. The frontier theorem** (`residual_le_zero_of_frontier_empty`): if every undiscovered
reason has conditional adverse mass `0` above the docket, the discovery residual is `≤ 0`.
Contrapositively, a positive residual names an undiscovered reason of positive
conditional adverse mass: an explicit inquiry obligation.

**3. The information-cell obstruction** (`residual_ge_cellGap`,
`exhaustive_attains_cellGap`): in a finite inquiry model, any sound docket policy (docketed
reasons are true, and the docket is a function of what the repertoire reveals) has, on
some world of every repertoire cell, residual at least the cell's gap
`V(certain K) − min_{ω ∈ K} V(Truth ω)`; the exhaustive policy attains exactly the gap.
So the least worst-case residual with unbounded budget is the largest cell gap.

**4. Progress under a witness-completeness hypothesis** (`potential_decay`): if every
step exposes a fixed fraction `γ` of the remaining potential, the potential decays
geometrically; the countermodels show the hypothesis fails for direct-query repertoires.

**5. Composition** (`li_noncapture_chain`): the second-pass theorem applied to the pairs
(actual, discovered) and (discovered, full) adds, giving
`𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ L·(α + β)`.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.ReasonSupply

namespace Workspace.Deference.Contrib.ReasonDiscovery

open LogicalInduction
open Workspace.Deference.Contrib.LICorrigibility
open Workspace.Deference.Contrib.TraceSteering
open Workspace.Deference.Contrib.ReasonSupply
open scoped Classical
open Finset

/-! ## 1. The conditional adverse certificate and the residual -/

section Residual

variable {ι : Type*} [DecidableEq ι]

/-- Conditional adverse sensitivity above a docket `D`: on contents containing `D`, adding
`r` lowers the verdict by at most `A r`. -/
def AdverseAbove (F : Finset ι → ℝ) (D : Finset ι) (A : ι → ℝ) : Prop :=
  ∀ (c : Finset ι) (r : ι), D ⊆ c → r ∉ c → F c - F (insert r c) ≤ A r

/-- The unconditional certificate is a conditional one above any docket. -/
theorem AdverseAbove.of_adverse {F : Finset ι → ℝ} {A : ι → ℝ} (h : Adverse F A)
    (D : Finset ι) : AdverseAbove F D A :=
  fun c r _ hr => h c r hr

/-- **The residual bound.**  The gain from the undiscovered reasons `S` above the docket
`D` is at most their conditional adverse mass. -/
theorem adverseAbove_union {F : Finset ι → ℝ} {D : Finset ι} {A : ι → ℝ}
    (h : AdverseAbove F D A) (s : Finset ι) (hd : Disjoint s D) :
    F D - F (D ∪ s) ≤ ∑ r ∈ s, A r := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hd' : Disjoint s D := Finset.disjoint_of_subset_left (Finset.subset_insert a s) hd
    have haD : a ∉ D := Finset.disjoint_left.mp hd (Finset.mem_insert_self a s)
    have hnot : a ∉ D ∪ s := by simp [haD, ha]
    have h1 := h (D ∪ s) a Finset.subset_union_left hnot
    have h2 := ih hd'
    rw [Finset.sum_insert ha, Finset.union_insert]
    linarith

/-- **The frontier theorem.**  If every undiscovered true reason has conditional adverse
mass `0` above the docket, the discovery residual is nonpositive. -/
theorem residual_le_zero_of_frontier_empty {F : Finset ι → ℝ} {A : ι → ℝ}
    (D truth : Finset ι) (hsub : D ⊆ truth) (h : AdverseAbove F D A)
    (hfront : ∀ r ∈ truth \ D, A r = 0) : F D - F truth ≤ 0 := by
  have := adverseAbove_union h (truth \ D) Finset.sdiff_disjoint
  rw [Finset.union_sdiff_of_subset hsub] at this
  calc F D - F truth ≤ ∑ r ∈ truth \ D, A r := this
    _ = 0 := Finset.sum_eq_zero hfront

end Residual

/-! ## 2. The information-cell obstruction -/

section Cells

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- A finite inquiry model: the adverse reasons true in each world, and a repertoire of
outcome functions (what each available inquiry reveals, as a function of the world). -/
structure Model (Ω ι : Type*) where
  truth : Ω → Finset ι
  V : Finset ι → ℝ
  Indist : Ω → Ω → Prop
  indist_refl : ∀ ω, Indist ω ω
  indist_symm : ∀ ω ω', Indist ω ω' → Indist ω' ω
  indist_trans : ∀ ω ω' ω'', Indist ω ω' → Indist ω' ω'' → Indist ω ω''

/-- The repertoire cell of a world: the worlds it cannot be told from. -/
noncomputable def Model.cell (M : Model Ω ι) (ω : Ω) : Finset Ω := univ.filter (M.Indist ω)

/-- The certain docket of a world: the reasons true in every world of its cell. -/
noncomputable def Model.certain (M : Model Ω ι) (ω : Ω) : Finset ι := (M.cell ω).inf M.truth

omit [Fintype ι] [DecidableEq ι] in
theorem Model.mem_cell_self (M : Model Ω ι) (ω : Ω) : ω ∈ M.cell ω := by
  simp [Model.cell, M.indist_refl]

theorem Model.certain_subset (M : Model Ω ι) (ω ω' : Ω) (h : ω' ∈ M.cell ω) :
    M.certain ω ⊆ M.truth ω' := by
  unfold Model.certain
  exact Finset.le_iff_subset.mp (Finset.inf_le (f := M.truth) h)

/-- A sound docket policy: what it dockets is true, and it cannot tell apart what the
repertoire cannot. -/
structure SoundPolicy (M : Model Ω ι) where
  D : Ω → Finset ι
  sound : ∀ ω, D ω ⊆ M.truth ω
  blind : ∀ ω ω', M.Indist ω ω' → D ω = D ω'

omit [DecidableEq Ω] in
/-- A sound policy's docket lies inside the certain docket. -/
theorem SoundPolicy.subset_certain {M : Model Ω ι} (P : SoundPolicy M) (ω : Ω) :
    P.D ω ⊆ M.certain ω := by
  unfold Model.certain
  refine Finset.le_iff_subset.mp (Finset.le_inf (f := M.truth) ?_)
  intro ω' hω'
  have hI : M.Indist ω ω' := (Finset.mem_filter.mp hω').2
  rw [P.blind ω ω' hI]
  exact Finset.le_iff_subset.mpr (P.sound ω')

/-- The gap of a world's cell: the residual of the certain docket on the worst world of
the cell. -/
noncomputable def Model.cellGap (M : Model Ω ι) (ω : Ω) : ℝ :=
  (M.cell ω).sup' ⟨ω, M.mem_cell_self ω⟩ (fun ω' => M.V (M.certain ω) - M.V (M.truth ω'))

/-- **The obstruction.**  For an antitone verdict, every sound policy has, on some world
of every cell, residual at least the cell gap. -/
theorem residual_ge_cellGap {M : Model Ω ι} (hanti : ∀ s t, s ⊆ t → M.V t ≤ M.V s)
    (P : SoundPolicy M) (ω : Ω) :
    ∃ ω' ∈ M.cell ω, M.cellGap ω ≤ M.V (P.D ω') - M.V (M.truth ω') := by
  obtain ⟨ω', hω', hmax⟩ := Finset.exists_max_image (M.cell ω)
    (fun ω' => M.V (M.certain ω) - M.V (M.truth ω')) ⟨ω, M.mem_cell_self ω⟩
  refine ⟨ω', hω', ?_⟩
  have hgap : M.cellGap ω = M.V (M.certain ω) - M.V (M.truth ω') := by
    unfold Model.cellGap
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun x hx => hmax x hx)
    · exact Finset.le_sup' (fun ω' => M.V (M.certain ω) - M.V (M.truth ω')) hω'
  have hI : M.Indist ω ω' := (Finset.mem_filter.mp hω').2
  have hD : P.D ω' = P.D ω := (P.blind ω ω' hI).symm
  have hsub : P.D ω ⊆ M.certain ω := P.subset_certain ω
  have := hanti _ _ hsub
  rw [hgap, hD]
  linarith

/-- The exhaustive policy: docket the certain reasons. -/
noncomputable def Model.exhaustive (M : Model Ω ι) : SoundPolicy M where
  D := M.certain
  sound := fun ω => M.certain_subset ω ω (M.mem_cell_self ω)
  blind := by
    intro ω ω' h
    have hcell : M.cell ω = M.cell ω' := by
      ext x
      simp only [Model.cell, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact M.indist_trans ω' ω x (M.indist_symm _ _ h) hx
      · intro hx
        exact M.indist_trans ω ω' x h hx
    unfold Model.certain
    rw [hcell]

/-- **The exhaustive policy attains the gap.** -/
theorem exhaustive_attains_cellGap (M : Model Ω ι) (ω : Ω) :
    ∀ ω' ∈ M.cell ω, M.V ((M.exhaustive).D ω') - M.V (M.truth ω') ≤ M.cellGap ω := by
  intro ω' hω'
  have hI : M.Indist ω ω' := (Finset.mem_filter.mp hω').2
  have : (M.exhaustive).D ω' = M.certain ω := ((M.exhaustive).blind ω ω' hI).symm
  rw [this]
  unfold Model.cellGap
  exact Finset.le_sup' (fun ω' => M.V (M.certain ω) - M.V (M.truth ω')) hω'

end Cells

/-! ## 3. Progress under witness completeness -/

section Progress

/-- Geometric decay of a potential under a fractional-progress hypothesis. -/
theorem potential_decay (x : ℕ → ℝ) (γ : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1)
    (hstep : ∀ t, x (t + 1) ≤ (1 - γ) * x t) : ∀ k, x k ≤ (1 - γ) ^ k * x 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hnn : 0 ≤ 1 - γ := by linarith [hγ.2]
    calc x (k + 1) ≤ (1 - γ) * x k := hstep k
      _ ≤ (1 - γ) * ((1 - γ) ^ k * x 0) := mul_le_mul_of_nonneg_left ih hnn
      _ = (1 - γ) ^ (k + 1) * x 0 := by ring

end Progress

/-! ## 4. Composition: actual → discovered → full -/

section Composition

/-- **The chain.**  The second-pass theorem on the pairs (actual, discovered) and
(discovered, full) adds: with a service bound `α = a/b` on the first and a discovery
bound `β = a'/b'` on the second, `𝔼ₙ(U_T) − 𝔼ₙ(U_full) ≲ₙ L·(α + β)`.  The middle
family (the discovered comparator's audit sentence and verdict) is shared, so the two
inequalities telescope. -/
theorem li_noncapture_chain {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (φs φd φf : ℕ → Sentence) (Xs Xd Xf Xδ₁ Xκ₁ Xδ₂ Xκ₂ : ℕ → LUV) (L : ℚ) (hL : 0 ≤ L)
    (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (a' b' : ℕ) (hb' : 0 < b') (hab' : a' ≤ b')
    (hvalid₁ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ValidAt (MediatedPair.compile (φs n) (φd n) (Xs n) (Xd n) (Xδ₁ n) (Xκ₁ n) L) v)
    (hvalid₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ValidAt (MediatedPair.compile (φd n) (φf n) (Xd n) (Xf n) (Xδ₂ n) (Xκ₂ n) L) v)
    (hsupply : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ d : ℝ, v.ValuesAt (Xδ₁ n) d ∧ (v.Holds (φs n) → v.Holds (φd n) → d ≤ (a : ℚ) / (b : ℚ)))
    (hdiscover : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ d : ℝ, v.ValuesAt (Xδ₂ n) d ∧ (v.Holds (φd n) → v.Holds (φf n) → d ≤ (a' : ℚ) / (b' : ℚ)))
    (hext₁ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Xκ₁ n) 0)
    (hext₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (Xκ₂ n) 0)
    (hsealed₁ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.Holds (φs n) → v.Holds (φd n))
    (hsealed₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.Holds (φd n) → v.Holds (φf n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hφs : RpnSentenceCodes φs) (hφd : RpnSentenceCodes φd) (hφf : RpnSentenceCodes φf)
    (hXs : LUV.RpnThresholdCodeSeq Xs) (hXd : LUV.RpnThresholdCodeSeq Xd)
    (hXf : LUV.RpnThresholdCodeSeq Xf)
    (hXδ₁ : LUV.RpnThresholdCodeSeq Xδ₁) (hXκ₁ : LUV.RpnThresholdCodeSeq Xκ₁)
    (hXδ₂ : LUV.RpnThresholdCodeSeq Xδ₂) (hXκ₂ : LUV.RpnThresholdCodeSeq Xκ₂) :
    (fun n => (gate (φs n) (Xs n)).expect P n - (gate (φf n) (Xf n)).expect P n) ≲ₙ
      fun _ => (L : ℝ) * (((a : ℚ) / (b : ℚ) : ℝ) + ((a' : ℚ) / (b' : ℚ) : ℝ)) := by
  have h1 := li_noncapture (P := P) (DP := DP) φs φd Xs Xd Xδ₁ Xκ₁ L hL a b hb hab hvalid₁
    hsupply hext₁ hsealed₁ hworld hφs hφd hXs hXd hXδ₁ hXκ₁
  have h2 := li_noncapture (P := P) (DP := DP) φd φf Xd Xf Xδ₂ Xκ₂ L hL a' b' hb' hab' hvalid₂
    hdiscover hext₂ hsealed₂ hworld hφd hφf hXd hXf hXδ₂ hXκ₂
  have h := asympLE_add h1 h2
  intro ε hε
  filter_upwards [h ε hε] with n hn
  simp only [MediatedPair.compile] at hn
  linarith

end Composition

end Workspace.Deference.Contrib.ReasonDiscovery

#print axioms Workspace.Deference.Contrib.ReasonDiscovery.adverseAbove_union
#print axioms Workspace.Deference.Contrib.ReasonDiscovery.residual_le_zero_of_frontier_empty
#print axioms Workspace.Deference.Contrib.ReasonDiscovery.SoundPolicy.subset_certain
#print axioms Workspace.Deference.Contrib.ReasonDiscovery.residual_ge_cellGap
#print axioms Workspace.Deference.Contrib.ReasonDiscovery.exhaustive_attains_cellGap
#print axioms Workspace.Deference.Contrib.ReasonDiscovery.potential_decay
#print axioms Workspace.Deference.Contrib.ReasonDiscovery.li_noncapture_chain
