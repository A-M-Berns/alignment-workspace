import Cleanroom.Corrigibility.CorrGeneralObject.Endorse
import Cleanroom.Corrigibility.CorrReflectFrames.Good

/-!
# corr-general-object — T7: acting on `Q` versus adopting `Q` is Value versus Reflection

The frame of announced beliefs `frameOf QH` (rows `(QH ω).mass`); its cells are the announcement
events `E_Q` and `ind (cell ρ)` is that push's kernel. **Cellwise (C-act)** `CellwiseAct P F V`:
for every recommended strategy `S` on the menu `𝒪_V = {V a}` and every candidate cell, the
strategy's action on the cell is `P(· | cell)`-optimal among the `V a` (constant on cells by
`IsStrategy`, so S6(a)'s common-recommendation condition is built in).

* **(a) P.** `CellwiseAct → Value` on the menu `𝒪_V` (`value_on_menu_of_cellwiseAct`): sum
  over cells.
* **(b) P (converse, immodest).** `F.Immodest → Value P.mass F → CellwiseAct P F V`
  (`cellwiseAct_of_value`) by the deviation menu `{Ŝ, Ŝ'}`: under immodesty every expert is
  indifferent or prefers `Ŝ`, so the constant strategy is recommended, and Value on `{Ŝ, Ŝ'}`
  is the cell inequality. DDB Thm 2.2 is `lit-ddb-frames`' `value_iff_totalTrust`, grade (a).
* **(c)** Modest frames: `Witnesses.lean` has the three-world modest frame where Value holds
  and `CellwiseAct` fails (`modest_value_not_cellwiseAct`).
* **(d) L.** `Reflects P.mass F ↔ ∀ ρ ∈ cands, Endorsed P (ind (cell ρ)) ρ` — cellwise literal
  (C-adopt) *is* Reflection (`reflects_iff_endorsed_cells`).
* **(e) L.** The informed expert `F.informed ρ` is `ρ` pushed by its own cell
  (`informed_eq_postPush`), and under New Reflection it is `P`'s post-push credence for the
  cell's kernel (`informed_eq_postPush_of_newReflects`).

Sources: [[general-object-final]] S5, P5; DDB Thm 2.2 through `lit-ddb-frames`;
[[corr-wf14b-inventory]] 008.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames
  Cleanroom.Corrigibility.CorrReflectFrames
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A : Type} [Fintype A] [DecidableEq A]

/-! ## The announcement frame and cellwise (C-act) -/

/-- The **frame of announced beliefs**: the overseers hold `QH ω` at world `ω`; its cells are the
announcement events `E_Q = {ω | QH ω = Q}`.
Source: [[general-object-final]] D4 (coarse-expert model), S5
Kind: D
Fidelity: exact -/
def frameOf (QH : Ω → Distr Ω) : Frame Ω where
  P ω := (QH ω).mass
  P_mem ω := (QH ω).mass_mem_stdSimplex

/-- The menu `𝒪_V = {V a | a ∈ A}` as a decision problem.
Source: [[general-object-final]] S5(a) ("the menu `A`")
Kind: D
Fidelity: exact -/
def menuOf (V : A → Ω → ℝ) : DecisionProblem Ω := univ.image V

/-- **Cellwise (C-act)**: for every strategy recommended by the frame on `𝒪_V`, every candidate
cell and every alternative `a`, the strategy's option on the cell beats `V a` in `P`-expectation
on the cell (product form). The strategy is constant on cells (`IsStrategy`), so this is
"acting on each announced `Q` is `P(· | E_Q)`-optimal".
Source: [[general-object-final]] S5(a), D7 (C-act)
Kind: D
Fidelity: exact (product form, candidates only) -/
def CellwiseAct (P : Distr Ω) (F : Frame Ω) (V : A → Ω → ℝ) : Prop :=
  ∀ S, F.Recommended (menuOf V) S → ∀ ρ ∈ F.cands P.mass, ∀ a,
    ∑ ω ∈ F.cell ρ, P.mass ω * (V a ω - S ω ω) ≤ 0

/-- A `P`-weighted sum decomposes over the candidate cells (null cells contribute nothing).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sum_eq_sum_cands_cells (P : Distr Ω) (F : Frame Ω) (X : Ω → ℝ) :
    ∑ ω, P.mass ω * X ω = ∑ ρ ∈ F.cands P.mass, ∑ ω ∈ F.cell ρ, P.mass ω * X ω := by
  rw [sum_rowClosed F (A := univ) (fun _ v _ _ => mem_univ v) (fun ω => P.mass ω * X ω)]
  have hsub : F.cands P.mass ⊆ univ.image F.P := image_subset_image (subset_univ _)
  rw [← sum_sdiff hsub, sum_eq_zero, zero_add]
  intro ρ hρ
  rw [mem_sdiff] at hρ
  apply sum_eq_zero
  intro ω hω
  have h0 : mass P.mass (F.cell ρ) = 0 := mass_cell_eq_zero_of_not_mem_cands P.nonneg F hρ.2
  rw [eq_zero_of_mass_eq_zero P.nonneg h0 hω, zero_mul]

/-- **T7(a): cellwise (C-act) implies Value on the menu `𝒪_V`** — for every recommended `S` and
every option `V a`, `E_P[V a] ≤ E_P[S]`; summing the cell inequalities.
Source: [[general-object-final]] S5(a), P5(a)
Kind: P
Fidelity: exact (Value restricted to the menu `𝒪_V`; the source's "Value on `A`")
Hyps: (a) `CellwiseAct` -/
theorem value_on_menu_of_cellwiseAct (P : Distr Ω) (F : Frame Ω) (V : A → Ω → ℝ)
    (h : CellwiseAct P F V) :
    ∀ S, F.Recommended (menuOf V) S → ∀ o ∈ menuOf V, E P.mass o ≤ stratValue P.mass S := by
  intro S hS o ho
  obtain ⟨a, _, rfl⟩ := mem_image.1 ho
  rw [stratValue_eq_E]
  have : E P.mass (V a) - E P.mass (fun w => S w w) = ∑ ω, P.mass ω * (V a ω - S ω ω) := by
    unfold E; rw [← sum_sub_distrib]; apply sum_congr rfl; intro ω _; ring
  rw [← sub_nonpos, this, sum_eq_sum_cands_cells P F]
  exact sum_nonpos fun ρ hρ => h S hS ρ hρ a

/-- Under immodesty a row vanishes off its own cell.
Source: none: infrastructure (DDB §1 l. 82: `P_w(P = P_w) = 1`). Kind: L. Fidelity: n/a -/
theorem immodest_off_cell {F : Frame Ω} (hF : F.Immodest) (w v : Ω) (hv : F.P v ≠ F.P w) :
    F.P w v = 0 :=
  eq_zero_of_mass_eq_one (F.P_mem w) (hF w) (by simp [Frame.mem_cell, hv])

/-- **T7(b): for an immodest frame, Value implies cellwise (C-act)** — the deviation menu
`{Ŝ, Ŝ'}` with `Ŝ'` following `S` off `cell ρ` and playing `V a` on it: under immodesty every
expert is indifferent or prefers `Ŝ`, so the constant strategy on `Ŝ` is recommended
(`Frame.Recommended` admits ties), and Value gives `E_P[Ŝ'] ≤ E_P[Ŝ]`, which is the cell
inequality.
Source: [[general-object-final]] S5(a) (converse "for an immodest frame"), P5(a); DDB l. 128
Kind: P
Fidelity: exact
Hyps: (a) `F.Immodest`, `Value P.mass F` -/
theorem cellwiseAct_of_value (P : Distr Ω) (F : Frame Ω) (V : A → Ω → ℝ) (hF : F.Immodest)
    (hV : Value P.mass F) : CellwiseAct P F V := by
  intro S hS ρ hρ a
  set Sh : Ω → ℝ := fun ω => S ω ω with hSh
  set Sh' : Ω → ℝ := fun ω => if F.P ω = ρ then V a ω else S ω ω with hSh'
  -- the constant strategy on `Ŝ` is recommended on `{Ŝ, Ŝ'}`
  have hrec : F.Recommended {Sh, Sh'} (fun _ => Sh) := by
    refine ⟨⟨fun _ => mem_insert_self _ _, fun _ _ _ => rfl⟩, fun w o ho => ?_⟩
    rcases mem_insert.1 ho with rfl | ho
    · exact le_refl _
    rw [mem_singleton] at ho
    subst ho
    by_cases hw : F.P w = ρ
    · -- the expert at `ρ`: `E_ρ Ŝ' = E_ρ (V a) ≤ E_ρ (S w) = E_ρ Ŝ`
      have e1 : E (F.P w) Sh' = E (F.P w) (V a) := by
        unfold E; apply sum_congr rfl; intro v _
        by_cases hv : F.P w v = 0
        · rw [hv, zero_mul, zero_mul]
        · have hvρ : F.P v = ρ := by
            by_contra hne
            exact hv (immodest_off_cell hF w v (by rw [hw]; exact hne))
          simp only [hSh', hvρ, if_true]
      have e2 : E (F.P w) Sh = E (F.P w) (S w) := by
        unfold E; apply sum_congr rfl; intro v _
        by_cases hv : F.P w v = 0
        · rw [hv, zero_mul, zero_mul]
        · have hvw : F.P v = F.P w := by
            by_contra hne
            exact hv (immodest_off_cell hF w v hne)
          simp only [hSh, hS.1.2 w v hvw.symm]
      rw [e1, e2]
      exact hS.2 w (V a) (mem_image_of_mem V (mem_univ a))
    · -- the expert elsewhere: indifferent (`Ŝ' = Ŝ` on its support)
      have e : E (F.P w) Sh' = E (F.P w) Sh := by
        unfold E; apply sum_congr rfl; intro v _
        by_cases hv : F.P w v = 0
        · rw [hv, zero_mul, zero_mul]
        · have hvw : F.P v = F.P w := by
            by_contra hne
            exact hv (immodest_off_cell hF w v hne)
          have hvρ : F.P v ≠ ρ := by rw [hvw]; exact hw
          simp only [hSh', hSh, hvρ, if_false]
      rw [e]
  have hval := hV {Sh, Sh'} (insert_nonempty _ _) _ hrec Sh' (mem_insert_of_mem (mem_singleton_self _))
  rw [stratValue] at hval
  -- `E_P Ŝ − E_P Ŝ'` is the cell sum
  have key : ∑ ω ∈ F.cell ρ, P.mass ω * (V a ω - S ω ω) = E P.mass Sh' - ∑ w, P.mass w * Sh w := by
    unfold E
    rw [← sum_sub_distrib, Frame.cell, sum_filter]
    apply sum_congr rfl; intro ω _
    by_cases hω : F.P ω = ρ
    · simp only [hω, if_true, hSh', hSh]; ring
    · simp only [hω, if_false, hSh', hSh]; ring
  rw [key]
  linarith

/-! ## (d) cellwise literal adoption is Reflection -/

/-- **T7(d): Reflection is cellwise endorsement** — `Reflects P.mass F` iff for every candidate
`ρ` the hard push `ind (cell ρ)` is endorsed toward `ρ` (cellwise literal (C-adopt)).
Source: [[general-object-final]] S5(b) ("cellwise literal (C-adopt) for every announced `Q` is
Reflection toward the frame"); DDB Thm 2.2 via `lit-ddb-frames`
Kind: L
Fidelity: exact (the definitions coincide term for term)
Hyps: (a) none -/
theorem reflects_iff_endorsed_cells (P : Distr Ω) (F : Frame Ω) :
    Reflects P.mass F ↔ ∀ ρ (hρ : ρ ∈ F.cands P.mass),
      Endorsed P (ind (F.cell ρ)) (Distr.ofSimplex ρ (F.mem_stdSimplex_of_mem_cands hρ)) := by
  unfold Reflects Endorsed
  constructor
  · intro h ρ hρ ω
    rw [pushMass_ind, Distr.ofSimplex_mass]
    exact h ρ hρ ω
  · intro h ρ hρ ω
    have := h ρ hρ ω
    rw [pushMass_ind, Distr.ofSimplex_mass] at this
    exact this

/-! ## (e) the informed expert is the cell's post-push credence -/

/-- **The informed expert is `ρ` pushed by its own cell**: `F.informed ρ = postPush ρ (ind (cell ρ))`
under `0 < ρ(P = ρ)` (New Reflection's informed target as a `postPush`).
Source: [[general-object-final]] S5(c) (New Reflection's informed target `Q̂`); DDB l. 95
Kind: L
Fidelity: exact (under the positivity guard, as DDB)
Hyps: (a) `0 < selfMass ρ` -/
theorem informed_eq_postPush (F : Frame Ω) {ρ : Ω → ℝ} (hρ : ρ ∈ stdSimplex ℝ Ω)
    (hpos : 0 < F.selfMass ρ) :
    F.informed ρ = (postPush (Distr.ofSimplex ρ hρ) (ind (F.cell ρ)) (isKernel_ind _).nonneg
      (by rw [pushMass_ind]; exact hpos)).mass := by
  funext w
  rw [postPush_mass, pushMass_ind, Distr.ofSimplex_mass]
  unfold Frame.informed Frame.selfMass ind Cleanroom.Found.LitDdbFrames.ind
  by_cases hw : F.P w = ρ
  · simp [hw, mass]
  · simp [hw, mass]

/-- **Under New Reflection the informed expert is `P`'s post-push credence for the cell's
kernel**: `F.informed ρ = postPush P (ind (cell ρ))` for every candidate `ρ` (the belief component
of a coarsened push, S5(c)).
Source: [[general-object-final]] S5(c); DDB ll. 95–100 (`NewReflects`)
Kind: L
Fidelity: exact
Hyps: (a) `NewReflects P.mass F`, candidacy -/
theorem informed_eq_postPush_of_newReflects (P : Distr Ω) (F : Frame Ω)
    (hN : NewReflects P.mass F) {ρ : Ω → ℝ} (hρ : ρ ∈ F.cands P.mass) :
    F.informed ρ = (postPush P (ind (F.cell ρ)) (isKernel_ind _).nonneg
      (by rw [pushMass_ind]
          exact (F.mem_cands_iff_mass_cell_pos P.nonneg).1 hρ)).mass := by
  obtain ⟨hself, h⟩ := hN ρ hρ
  funext w
  rw [postPush_mass, pushMass_ind]
  show F.informed ρ w = P.mass w * Cleanroom.Found.LitDdbFrames.ind (F.cell ρ) w / mass P.mass (F.cell ρ)
  have hpos : 0 < mass P.mass (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos P.nonneg).1 hρ
  rw [eq_div_iff hpos.ne']
  have hw := h w
  unfold Frame.informed
  by_cases hcell : F.P w = ρ
  · have hind : Cleanroom.Found.LitDdbFrames.ind (F.cell ρ) w = 1 := by
      simp [Cleanroom.Found.LitDdbFrames.ind, Frame.mem_cell, hcell]
    rw [hind] at hw ⊢
    simp only [hcell, if_true]
    rw [mul_one] at hw ⊢
    rw [div_mul_eq_mul_div, div_eq_iff hself.ne']
    linarith [hw]
  · have hind : Cleanroom.Found.LitDdbFrames.ind (F.cell ρ) w = 0 := by
      simp [Cleanroom.Found.LitDdbFrames.ind, Frame.mem_cell, hcell]
    rw [hind]
    simp [hcell]

end

end Cleanroom.Corrigibility.CorrGeneralObject
