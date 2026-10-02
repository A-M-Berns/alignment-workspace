import Cleanroom.Corrigibility.CorrGeneralObject.ActAdopt
import Cleanroom.Corrigibility.CorrGeneralObject.ExampleA
import Cleanroom.Corrigibility.CorrGeneralObject.Conjunction
import Cleanroom.Corrigibility.CorrReflectFrames.Selection

/-!
# corr-general-object — witnesses for T7 and T8(b)

* **T7, immodest (N+).** Example A's coarse-expert frame: the overseers learn whether `θ = θ₂`,
  `F := refineFrame P f` with `f ω := (ω = 1)`. It is immodest and valued (`corr-reflect-frames`'
  `refineFrame_immodest`, `refineFrame_value`), so `CellwiseAct` holds by T7(b) and Value on the
  menu by T7(a); the two cells `{θ₁, θ₃}` and `{θ₂}` are distinct and both of positive mass
  (`exA_frame_*`).
* **T7(c), modest (N+ counterexample).** A three-world *modest* frame where Value holds and
  `CellwiseAct` fails: rows `ρ_A = (1/4, 1/4, 1/2)` at worlds `0, 1` and `ρ_B = δ₂` at world
  `2`, deferrer `π = ρ_A`. Value via DDB Theorem 4.1 (`totalTrust_iff_hullAndModestlyInformed`,
  `value_iff_totalTrust`): `π` is a candidate and both candidates are modestly informed. On the
  menu `{(0, 0, 1), (3/4, 3/4, 0)}` the recommended strategy plays the first option everywhere,
  but on the cell `{0, 1}` the deferrer prefers the second by `3/8`
  (`modest_value_not_cellwiseAct`). So S5(a)'s converse needs immodesty, as the source says.
* **T8(b), Example B (N+).** The meta-algebra `{α = 1/10, α = 1/50}` with prior `η`; the stakes
  `u = (1/20, −71/2500)` derived from `ε = 1/50`, `(c, h) = (1, 4)`, `β = 3/5`; the second-order
  sensor `(α₂, β₂)`: comply iff `α₂/β₂ ≤ (η/(1−η))·(71/125)` (T3(b) instantiated); at `η = 1/2`
  comply at `(1/2, 9/10)` (`−1/2500`), override at `(3/5, 9/10)` (`+37/12500`); the coherent
  `Q̂(α = 1/50) = 9/14 ≠ 1`, and `= 1` only for a kernel with `α₂ = 0` (T8(a)).

Sources: [[general-object-final]] S5, S11, P5, P9, R6; [[corr-wf14b-inventory]] 008, 011.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames
  Cleanroom.Corrigibility.CorrReflectFrames
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

/-! ## T7: the immodest witness (Example A's coarse-expert frame) -/

/-- The overseers' signal in Example A: whether `θ = θ₂`.
Source: [[general-object-final]] D4 (coarse-expert model), S5
Kind: D
Fidelity: exact -/
def exA_f : Fin 3 → Bool := fun ω => decide (ω = 1)

/-- Example A's announcement frame: the Bayesian refinement of `P` along `exA_f`.
Source: [[general-object-final]] S5; `corr-reflect-frames` `refineFrame`
Kind: D
Fidelity: exact -/
def exA_frame : Frame (Fin 3) := refineFrame exA_P.mass exA_P.nonneg exA_f

/-- **N+ for T7(a)(b)**: Example A's announcement frame is immodest and valued, hence cellwise
(C-act) holds for every menu and Value holds on `𝒪_V`; the frame has two distinct cells of
positive mass (`{θ₁, θ₃}` and `{θ₂}`), so (a) and (b) bite.
Source: [[general-object-final]] S5(a), P5(a); `corr-reflect-frames` `refineFrame_immodest`,
`refineFrame_value`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_frame_witness :
    exA_frame.Immodest ∧ Value exA_P.mass exA_frame ∧ CellwiseAct exA_P exA_frame exA_V ∧
      (∀ S, exA_frame.Recommended (menuOf exA_V) S →
        ∀ o ∈ menuOf exA_V, E exA_P.mass o ≤ stratValue exA_P.mass S) ∧
      exA_frame.P 0 1 = 0 ∧ exA_frame.P 1 1 = 1 ∧
      0 < mass exA_P.mass (exA_frame.cell (exA_frame.P 0)) ∧
      0 < mass exA_P.mass (exA_frame.cell (exA_frame.P 1)) := by
  have hI : exA_frame.Immodest := refineFrame_immodest exA_P.nonneg exA_f
  have hV : Value exA_P.mass exA_frame := refineFrame_value exA_P.mass_mem_stdSimplex exA_f
  have hC : CellwiseAct exA_P exA_frame exA_V := cellwiseAct_of_value exA_P exA_frame exA_V hI hV
  have hfib0 : 0 < mass exA_P.mass (fibre exA_f 0) :=
    mass_fibre_pos_of_pos exA_P.nonneg (by simp [exA_P])
  have hfib1 : 0 < mass exA_P.mass (fibre exA_f 1) :=
    mass_fibre_pos_of_pos exA_P.nonneg (by simp [exA_P])
  refine ⟨hI, hV, hC, value_on_menu_of_cellwiseAct exA_P exA_frame exA_V hC, ?_, ?_, ?_, ?_⟩
  · show condRow exA_P.mass exA_f 0 1 = 0
    rw [condRow_apply_of_pos hfib0]
    simp [fibre, exA_f, Cleanroom.Found.LitDdbFrames.ind]
  · show condRow exA_P.mass exA_f 1 1 = 1
    rw [condRow_apply_of_pos hfib1]
    have : mass exA_P.mass (fibre exA_f 1) = 1/4 := by
      have e : fibre exA_f 1 = {1} := by decide
      rw [e]; simp [mass, exA_P]
    rw [this]; simp [exA_P, fibre, exA_f, Cleanroom.Found.LitDdbFrames.ind] <;> norm_num
  · exact mass_cell_pos_of_pos exA_P.nonneg exA_frame (by simp [exA_P])
  · exact mass_cell_pos_of_pos exA_P.nonneg exA_frame (by simp [exA_P])

/-! ### The immodest witness is not vacuous (audit r1 adversarial 3.4)

`CellwiseAct` and "Value on the menu" both quantify over *recommended* strategies for
`menuOf exA_V` on `exA_frame`; `exA_frame_witness` derives them from immodesty + Value and
exhibits none. Below: the rows of `exA_frame` (`(2/3, 0, 1/3)` on the cell `{θ₁, θ₃}`, `δ₂` on
`{θ₂}`), the recommended strategy "`plan₁` off `θ₂`, `plan₂` on `θ₂`", and the cell inequality
of `CellwiseAct` at it as a genuine number (`∑_{cell θ₁} P (V plan₂ − S) = −6`). Instance
supplied by the round-1 adversarial audit (`audit-r1-probes/RecommendedOnExA.lean`). -/

/-- Row of `exA_frame` at `θ₁`: `P(· | θ ≠ θ₂) = (2/3, 0, 1/3)`.
Source: [[general-object-final]] S5 on Example A. Kind: L. Fidelity: exact -/
theorem exA_row0 : exA_frame.P 0 = ![2/3, 0, 1/3] := by
  have hf : fibre exA_f 0 = {0, 2} := by decide
  have hm : mass exA_P.mass (fibre exA_f 0) = 3/4 := by
    rw [hf]; simp [mass, exA_P, sum_pair]; norm_num
  show condRow exA_P.mass exA_f 0 = _
  funext v
  rw [condRow_apply_of_pos (by rw [hm]; norm_num), hm, hf]
  fin_cases v <;> simp [exA_P, Cleanroom.Found.LitDdbFrames.ind] <;> norm_num

/-- Row of `exA_frame` at `θ₂`: `δ₂`. Source: [[general-object-final]] S5 on Example A. Kind: L.
Fidelity: exact -/
theorem exA_row1 : exA_frame.P 1 = ![0, 1, 0] := by
  have hf : fibre exA_f 1 = {1} := by decide
  have hm : mass exA_P.mass (fibre exA_f 1) = 1/4 := by
    rw [hf]; simp [mass, exA_P] <;> norm_num
  show condRow exA_P.mass exA_f 1 = _
  funext v
  rw [condRow_apply_of_pos (by rw [hm]; norm_num), hm, hf]
  fin_cases v <;> simp [exA_P, Cleanroom.Found.LitDdbFrames.ind] <;> norm_num

/-- Row of `exA_frame` at `θ₃`: the same as at `θ₁`. Source: [[general-object-final]] S5 on
Example A. Kind: L. Fidelity: exact -/
theorem exA_row2 : exA_frame.P 2 = ![2/3, 0, 1/3] := by
  have hf : fibre exA_f 2 = {0, 2} := by decide
  have hm : mass exA_P.mass (fibre exA_f 2) = 3/4 := by
    rw [hf]; simp [mass, exA_P, sum_pair]; norm_num
  show condRow exA_P.mass exA_f 2 = _
  funext v
  rw [condRow_apply_of_pos (by rw [hm]; norm_num), hm, hf]
  fin_cases v <;> simp [exA_P, Cleanroom.Found.LitDdbFrames.ind] <;> norm_num

/-- The rows of `exA_frame` at coordinate `θ₂` separate the two cells.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem exA_row_at1 (w : Fin 3) : exA_frame.P w 1 = if w = 1 then 1 else 0 := by
  fin_cases w
  · show exA_frame.P 0 1 = _; rw [exA_row0]; simp
  · show exA_frame.P 1 1 = _; rw [exA_row1]; simp
  · show exA_frame.P 2 1 = _; rw [exA_row2]; simp

/-- The strategy "`plan₁` off `θ₂`, `plan₂` on `θ₂`" on `exA_frame`.
Source: audit r1 witness. Kind: D. Fidelity: exact -/
def exA_S : Fin 3 → (Fin 3 → ℝ) := fun w => if w = 1 then exA_V 1 else exA_V 0

/-- **N+ for T7's quantifiers**: `exA_S` is a recommended strategy for `menuOf exA_V` on
`exA_frame` (constant on cells; each row's best option), so `CellwiseAct` and Value-on-the-menu
quantify over a nonempty set there.
Source: [[general-object-final]] S5(a), P5 on Example A; audit r1 adversarial 3.4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_S_recommended : exA_frame.Recommended (menuOf exA_V) exA_S := by
  refine ⟨⟨fun w => ?_, fun w v hwv => ?_⟩, fun w o ho => ?_⟩
  · unfold exA_S; split_ifs <;> exact mem_image_of_mem exA_V (mem_univ _)
  · have h1 := congrFun hwv 1
    rw [exA_row_at1 w, exA_row_at1 v] at h1
    unfold exA_S
    by_cases hw : w = 1 <;> by_cases hv : v = 1 <;> simp [hw, hv] at h1 ⊢
  · obtain ⟨a, _, rfl⟩ := mem_image.1 ho
    fin_cases w
    · show E (exA_frame.P 0) (exA_V a) ≤ E (exA_frame.P 0) (exA_S 0)
      rw [exA_row0]
      fin_cases a <;> simp [E, exA_S, exA_V, Fin.sum_univ_three] <;> norm_num
    · show E (exA_frame.P 1) (exA_V a) ≤ E (exA_frame.P 1) (exA_S 1)
      rw [exA_row1]
      fin_cases a <;> simp [E, exA_S, exA_V, Fin.sum_univ_three] <;> norm_num
    · show E (exA_frame.P 2) (exA_V a) ≤ E (exA_frame.P 2) (exA_S 2)
      rw [exA_row2]
      fin_cases a <;> simp [E, exA_S, exA_V, Fin.sum_univ_three] <;> norm_num

/-- The cell inequality of `CellwiseAct` at the recommended strategy is a genuine number: on
the cell of `θ₁` (`{θ₁, θ₃}`) the alternative `plan₂` loses by `6` in `P`-mass-weighted terms.
Source: [[general-object-final]] S5(a) on Example A; audit r1 adversarial 3.4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_cell_ineq_bites :
    ∑ ω ∈ exA_frame.cell (exA_frame.P 0), exA_P.mass ω * (exA_V 1 ω - exA_S ω ω) = -6 := by
  have hcell : exA_frame.cell (exA_frame.P 0) = {0, 2} := by
    ext w
    simp only [Frame.mem_cell]
    fin_cases w
    · simp
    · show exA_frame.P 1 = exA_frame.P 0 ↔ _
      rw [exA_row0, exA_row1]
      constructor
      · intro h; have := congrFun h 1; simp at this
      · intro h; simp at h
    · show exA_frame.P 2 = exA_frame.P 0 ↔ _
      rw [exA_row0, exA_row2]; simp
  rw [hcell, sum_pair (by decide)]
  simp [exA_P, exA_V, exA_S]; norm_num

/-! ## T7(c): a modest frame where Value holds and cellwise (C-act) fails -/

/-- The modest row `ρ_A = (1/4, 1/4, 1/2)` (announced at worlds `0` and `1`).
Source: mandate T7(c) (the construction is this package's). Kind: D. Fidelity: exact -/
def modρA : Fin 3 → ℝ := ![1/4, 1/4, 1/2]

/-- The row `ρ_B = δ₂` (announced at world `2`). Source: mandate T7(c). Kind: D. Fidelity: exact -/
def modρB : Fin 3 → ℝ := ![0, 0, 1]

/-- `ρ_A ≠ ρ_B`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem modρA_ne_modρB : modρA ≠ modρB := by
  intro h; have := congrFun h 2; simp [modρA, modρB] at this <;> norm_num at this

/-- The same inequality with the literals unfolded (for `simp`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem modρ_ne_lit : (![0, 0, 1] : Fin 3 → ℝ) ≠ ![1/4, 1/4, 1/2] ∧
    (![1/4, 1/4, 1/2] : Fin 3 → ℝ) ≠ ![0, 0, 1] :=
  ⟨modρA_ne_modρB.symm, modρA_ne_modρB⟩

/-- The modest frame: rows `ρ_A, ρ_A, ρ_B`.
Source: mandate T7(c). Kind: D. Fidelity: exact -/
def modF : Frame (Fin 3) where
  P w := if w = 2 then modρB else modρA
  P_mem w := by
    split_ifs
    · refine ⟨fun v => ?_, ?_⟩
      · fin_cases v <;> simp [modρB]
      · simp [modρB, Fin.sum_univ_three]
    · refine ⟨fun v => ?_, ?_⟩
      · fin_cases v <;> simp [modρA] <;> norm_num
      · simp [modρA, Fin.sum_univ_three]; norm_num

/-- The deferrer `π = ρ_A` as a FAF distribution. Source: mandate T7(c). Kind: D. Fidelity: exact -/
def modP : Distr (Fin 3) where
  mass := modρA
  nonneg i := by fin_cases i <;> simp [modρA] <;> norm_num
  sum_eq_one := by simp [modρA, Fin.sum_univ_three]; norm_num

/-- The rows of the modest frame. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem modF_P : modF.P 0 = modρA ∧ modF.P 1 = modρA ∧ modF.P 2 = modρB := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [modF]

/-- The cells of the modest frame. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem modF_cells : modF.cell modρA = {0, 1} ∧ modF.cell modρB = {2} := by
  constructor
  · ext w; fin_cases w <;> simp [Frame.cell, modF, modρA_ne_modρB.symm]
  · ext w; fin_cases w <;> simp [Frame.cell, modF, modρA_ne_modρB]

/-- The candidates of `π = ρ_A` are `{ρ_A, ρ_B}` (all three worlds have positive mass).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem modF_cands : modF.cands modρA = {modρA, modρB} := by
  ext σ
  simp only [Frame.mem_cands, mem_insert, mem_singleton]
  constructor
  · rintro ⟨w, _, rfl⟩
    fin_cases w <;> simp [modF]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [modρA], by simp [modF]⟩
    · exact ⟨2, by simp [modρA], by simp [modF]⟩

/-- The informed experts of the modest frame: `ρ_A(· | cell ρ_A) = (1/2, 1/2, 0)` and
`ρ_B(· | cell ρ_B) = ρ_B`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem modF_informed : modF.informed modρA = ![1/2, 1/2, 0] ∧ modF.informed modρB = modρB := by
  have hsA : modF.selfMass modρA = 1/2 := by
    unfold Frame.selfMass; rw [modF_cells.1]; simp [mass, modρA]; norm_num
  have hsB : modF.selfMass modρB = 1 := by
    unfold Frame.selfMass; rw [modF_cells.2]; simp [mass, modρB]
  constructor
  · funext w; unfold Frame.informed; rw [hsA]
    fin_cases w <;> simp [modF, modρA, modρB, modρA_ne_modρB.symm, modρ_ne_lit.1] <;> norm_num
  · funext w; unfold Frame.informed; rw [hsB]
    fin_cases w <;> simp [modF, modρA, modρB, modρA_ne_modρB, modρ_ne_lit.2] <;> norm_num

/-- **The modest frame is valued by `π = ρ_A`** (DDB Theorem 4.1 through `lit-ddb-frames`): `π`
is one of its own candidates, and both candidates are modestly informed — `ρ_A` is the midpoint
of its informed self `(1/2, 1/2, 0)` and the other candidate `ρ_B`, and `ρ_B` is its own
informed self.
Source: mandate T7(c); DDB Thm 4.1 via `totalTrust_iff_hullAndModestlyInformed`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem modF_value : Value modρA modF := by
  have hπ : modρA ∈ stdSimplex ℝ (Fin 3) := modP.mass_mem_stdSimplex
  rw [value_iff_totalTrust hπ, totalTrust_iff_hullAndModestlyInformed hπ]
  refine ⟨?_, ?_⟩
  · apply subset_convexHull
    rw [modF_cands]; simp
  · intro ρ hρ
    rw [modF_cands] at hρ
    rcases mem_insert.1 hρ with rfl | hρ
    · -- `ρ_A`: self-mass `1/2`, and the midpoint representation
      refine ⟨?_, ?_⟩
      · unfold Frame.selfMass; rw [modF_cells.1]; simp [mass, modρA] <;> norm_num
      · have hcm : modF.candsMinus modρA = {modρB} := by
          unfold Frame.candsMinus; rw [modF_cands]
          exact erase_insert (by simp [modρA_ne_modρB])
        rw [hcm, modF_informed.1, coe_singleton, convexHull_pair]
        refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
        funext w; fin_cases w <;> simp [modρA, modρB] <;> norm_num
    · rw [mem_singleton] at hρ; subst hρ
      refine ⟨?_, ?_⟩
      · unfold Frame.selfMass; rw [modF_cells.2]; simp [mass, modρB]
      · apply subset_convexHull
        rw [modF_informed.2]; simp

/-- The menu for the modest counterexample: `a = (0, 0, 1)`, `b = (3/4, 3/4, 0)`.
Source: mandate T7(c). Kind: D. Fidelity: exact -/
def modV : Bool → Fin 3 → ℝ := fun a => if a then ![0, 0, 1] else ![3/4, 3/4, 0]

/-- **T7(c): a modest frame with Value but not cellwise (C-act)** — the converse of T7(a) needs
immodesty. The frame is modest (`selfMass ρ_A = 1/2`), `π = ρ_A` values it, the constant
strategy on `a` is recommended on `{a, b}` (`E_{ρ_A}: 1/2 vs 3/8`; `E_{ρ_B}: 1 vs 0`), yet on the
cell `{0, 1}` the deferrer prefers `b` by `3/8 > 0`.
Source: [[general-object-final]] S5(a), P5(a) ("for a modest expert … the argument stops
(adversary's mechanism; no numeric instance constructed)"); mandate T7(c)
Kind: N+
Fidelity: exact (the instance the source did not construct)
Hyps: (a) none -/
theorem modest_value_not_cellwiseAct :
    ¬ modF.Immodest ∧ Value modP.mass modF ∧
      modF.Recommended (menuOf modV) (fun _ => modV true) ∧
      ¬ CellwiseAct modP modF modV := by
  refine ⟨?_, modF_value, ?_, ?_⟩
  · intro h
    have := h 0
    rw [modF_P.1] at this
    unfold Frame.selfMass at this; rw [modF_cells.1] at this
    simp [mass, modρA] at this <;> norm_num at this
  · refine ⟨⟨fun _ => mem_image_of_mem modV (mem_univ true), fun _ _ _ => rfl⟩, fun w o ho => ?_⟩
    obtain ⟨a, _, rfl⟩ := mem_image.1 ho
    fin_cases w <;> cases a <;> simp [E, modF, modV, modρA, modρB, Fin.sum_univ_three] <;> norm_num
  · intro h
    have hρ : modρA ∈ modF.cands modP.mass := by
      show modρA ∈ modF.cands modρA
      rw [modF_cands]; simp
    have hrec : modF.Recommended (menuOf modV) (fun _ => modV true) := by
      refine ⟨⟨fun _ => mem_image_of_mem modV (mem_univ true), fun _ _ _ => rfl⟩, fun w o ho => ?_⟩
      obtain ⟨a, _, rfl⟩ := mem_image.1 ho
      fin_cases w <;> cases a <;> simp [E, modF, modV, modρA, modρB, Fin.sum_univ_three] <;> norm_num
    have := h _ hrec modρA hρ false
    rw [modF_cells.1, sum_pair (by decide)] at this
    simp [modP, modV, modρA] at this <;> norm_num at this

/-! ## T8(b): Example B -/

/-- Example B's meta-prior `(1 − η, η)` on `{α = 1/10, α = 1/50}`.
Source: [[general-object-final]] S11. Kind: D. Fidelity: exact -/
def exB_P (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : Distr (Fin 2) where
  mass := ![1 - η, η]
  nonneg i := by fin_cases i <;> simp <;> linarith
  sum_eq_one := by simp [Fin.sum_univ_two]

/-- Example B's press-cell stake `u(α) = (1−ε)αc − εβh`: override gains `c` on right-and-pressed
worlds, loses `h` on wrong-and-pressed worlds.
Source: [[general-object-final]] P9
Kind: D
Fidelity: exact -/
def exB_u (ε c h β α : ℝ) : ℝ := (1 - ε) * α * c - ε * β * h

/-- The stakes at `ε = 1/50`, `(c, h) = (1, 4)`, `β = 3/5`: `u(1/10) = 1/20`, `u(1/50) = −71/2500`.
Source: [[general-object-final]] P9, S11
Kind: N+
Fidelity: exact -/
theorem exB_u_values :
    exB_u (1/50) 1 4 (3/5) (1/10) = 1/20 ∧ exB_u (1/50) 1 4 (3/5) (1/50) = -71/2500 := by
  unfold exB_u; constructor <;> norm_num

/-- Example B's decision variable on the meta-algebra: `X = (u(1/10), u(1/50)) = (1/20, −71/2500)`.
Source: [[general-object-final]] P9. Kind: D. Fidelity: exact -/
def exB_X : Fin 2 → ℝ := ![1/20, -71/2500]

/-- **T8(b), the threshold** (T3(b) instantiated on the meta-algebra): for `η ∈ (0, 1)` and a
second-order sensor `(α₂, β₂)` with `β₂ > 0`, the (C-act) verdict is comply iff
`α₂/β₂ ≤ (η/(1−η))·(71/125)`.
Source: [[general-object-final]] S11, P9
Kind: L
Fidelity: exact
Hyps: (a) `0 < η < 1`, `0 < β₂` -/
theorem exB_comply_iff (η α₂ β₂ : ℝ) (h0 : 0 < η) (h1 : η < 1) (hβ : 0 < β₂) :
    pushExpect (exB_P η h0.le h1.le) ![α₂, β₂] exB_X ≤ 0 ↔
      α₂ / β₂ ≤ (η / (1 - η)) * (71/125) := by
  simp [pushExpect, exB_P, exB_X, Fin.sum_univ_two]
  rw [div_le_iff₀ hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  constructor <;> intro H <;> nlinarith

/-- The claim push `(1/2, 9/10)` has positive mass (`7/10`) at `η = 1/2`. Source: none:
infrastructure. Kind: L. Fidelity: n/a -/
theorem exB_pushMass_pos :
    0 < pushMass (exB_P (1/2) (by norm_num) (by norm_num)) ![1/2, 9/10] := by
  simp [pushMass, exB_P, Fin.sum_univ_two]; norm_num

/-- **N+ for T8(b)**: at `η = 1/2`, `(α₂, β₂) = (1/2, 9/10)` complies (`E[X | claim] = −1/2500`),
`(3/5, 9/10)` overrides (`+37/12500`); the coherent post-claim credence on `α = 1/50` is `9/14 ≠ 1`
— the dogmatic target `δ_{α = 1/50}` is not literally adopted — and a kernel that does adopt it
has `α₂ = 0` (T8(a)).
Source: [[general-object-final]] S11, P9, R6; [[corr-wf14b-inventory]] 011
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exB_witness :
    pushExpect (exB_P (1/2) (by norm_num) (by norm_num)) ![1/2, 9/10] exB_X /
        pushMass (exB_P (1/2) (by norm_num) (by norm_num)) ![1/2, 9/10] = -1/2500 ∧
      pushExpect (exB_P (1/2) (by norm_num) (by norm_num)) ![3/5, 9/10] exB_X /
        pushMass (exB_P (1/2) (by norm_num) (by norm_num)) ![3/5, 9/10] = 37/12500 ∧
      (postPush (exB_P (1/2) (by norm_num) (by norm_num)) ![1/2, 9/10]
        (fun i => by fin_cases i <;> norm_num) exB_pushMass_pos).mass 1 = 9/14 ∧
      (∀ k : Fin 2 → ℝ, Endorsed (exB_P (1/2) (by norm_num) (by norm_num)) k (Distr.delta 1) →
        k 0 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [pushExpect, pushMass, exB_P, exB_X, Fin.sum_univ_two]; norm_num
  · simp [pushExpect, pushMass, exB_P, exB_X, Fin.sum_univ_two]; norm_num
  · rw [postPush_mass]
    simp [pushMass, exB_P, Fin.sum_univ_two]; norm_num
  · intro k hE
    apply endorsed_kernel_vanishes_off (exB_P (1/2) (by norm_num) (by norm_num)) hE (S := {1})
      (by simp [Distr.delta_mass]) 0 (by decide)
    simp [exB_P] <;> norm_num

end

end Cleanroom.Corrigibility.CorrGeneralObject
