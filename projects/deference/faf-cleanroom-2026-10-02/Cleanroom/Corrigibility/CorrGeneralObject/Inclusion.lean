import Cleanroom.Corrigibility.CorrGeneralObject.Endorse

/-!
# corr-general-object — T10: common prior plus information inclusion makes every push endorsed

Finite tower property. The agent observes `y : Ω → Y`, the overseers observe `g : Ω → G` with
`g` refining `y` (`y = f ∘ g`), and announce `QH ω = P(· | g = g ω)`. Then:

* **(a)** for every announced cell `g₀` of positive mass, the hard push `𝟙_{g = g₀}` is endorsed,
  *from the agent's credence `P(· | y = y₀)`*, toward the announcement `P(· | g = g₀)`
  (`tower_endorsed`: `E[P(A | 𝒢) | G] = P(A | G)` for `G ∈ 𝒢`);
* **(b)** for the coarsened press `Pr = {ω | E_{QH ω}[X] < 0}`, `E[X 𝟙_Pr] < 0` under the agent's
  credence whenever the press has positive mass — for every alternative's `X` at once
  (`coarse_press_negative`).

**Scope.** The common prior is load-bearing (one `P` for both parties); inclusion is one
sufficient route to the barycentre condition (T2(ii)), not the only one (CE2 has no inclusion
structure).

**Witnesses.** The mandate's instance (`w10_*`: `Fin 4`, `y` a 2-cell, `g = id` the 4-cell
partition) is **N−**: with `g = id` every announcement is a Dirac, so `tower_endorsed`'s
conclusion holds for every credence giving the cell positive mass (the refinement hypothesis is
never exercised) and the coarsened press is the exact press `{X < 0}` (audit r2 adversarial B1).
The **N+** instance is `w10c_*` (`Fin 6`, `y = (ω ≥ 3)`, `g = (0,0,1,2,2,3)` strictly coarser
than the points): the announced cell `{3, 4}` has the non-Dirac target `(2/3, 1/3)`, endorsement
is obtained *through* `tower_endorsed` (`w10c_tower_witness`), and for `X = (1, −3, 1, 1, −5, 1)`
world `3` with `X 3 = 1 > 0` lies in the coarsened press because its cell's *average* is `−1`,
with `E[X 𝟙_Pr] = −1/2 < 0` through `coarse_press_negative` (`w10c_coarse_press_witness`).
Instance supplied by the round-2 adversarial audit (`audit-r2-probes/TowerCoarse.lean`).

Sources: [[general-object-final]] S15, P10, (G); run-1 miri Prop 4.3 (sibling
`corr-three-step-facts`); [[corr-wf14b-inventory]] 013.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The cell `{ω | g ω = g₀}` of a signal.
Source: [[general-object-final]] P10 (`{Q^H = Q} ∩ {y}`)
Kind: D
Fidelity: exact -/
def cellOf {G : Type} [DecidableEq G] (g : Ω → G) (g₀ : G) : Finset Ω := univ.filter (fun ω => g ω = g₀)

/-- Membership in a cell. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem mem_cellOf {G : Type} [DecidableEq G] (g : Ω → G) (g₀ : G) (ω : Ω) :
    ω ∈ cellOf g g₀ ↔ g ω = g₀ := by simp [cellOf]

/-- Under refinement (`y = f ∘ g`) a `g`-cell lies inside one `y`-cell: the indicator of the
`y`-cell through `ω₀` is `1` on the `g`-cell through `ω₀`.
Source: none: infrastructure (the tower's measurability step). Kind: L. Fidelity: n/a -/
theorem ind_yCell_mul_ind_gCell {Y G : Type} [DecidableEq Y] [DecidableEq G] (y : Ω → Y)
    (g : Ω → G) (href : ∃ f : G → Y, y = f ∘ g) (ω₀ ω : Ω) :
    ind (cellOf y (y ω₀)) ω * ind (cellOf g (g ω₀)) ω = ind (cellOf g (g ω₀)) ω := by
  obtain ⟨f, hf⟩ := href
  unfold ind Cleanroom.Found.LitDdbFrames.ind
  by_cases hg : g ω = g ω₀
  · have hy : y ω = y ω₀ := by rw [hf]; simp [Function.comp, hg]
    simp [hg, hy]
  · simp [hg]

/-- **T10(a): the tower property makes every announcement endorsed from the agent's credence.**
With `Pa := P(· | y = y ω₀)` the agent's credence and `g₀ := g ω₀` an announced cell of positive
mass, the hard push `𝟙_{g = g₀}` is endorsed from `Pa` toward the announcement `P(· | g = g₀)`.
Source: [[general-object-final]] S15, P10 (`P(A | G) = E[P(A | 𝒢) | G] = Q(A)`); miri Prop 4.3
Kind: P
Fidelity: exact (finite tower property; common prior `P`)
Hyps: (a) refinement `href`, the two positivity guards -/
theorem tower_endorsed {Y G : Type} [DecidableEq Y] [DecidableEq G] (P : Distr Ω) (y : Ω → Y)
    (g : Ω → G) (href : ∃ f : G → Y, y = f ∘ g) (ω₀ : Ω)
    (hy : 0 < pushMass P (ind (cellOf y (y ω₀)))) (hg : 0 < pushMass P (ind (cellOf g (g ω₀)))) :
    Endorsed (postPush P (ind (cellOf y (y ω₀))) (isKernel_ind _).nonneg hy)
      (ind (cellOf g (g ω₀))) (postPush P (ind (cellOf g (g ω₀))) (isKernel_ind _).nonneg hg) := by
  intro ω
  simp only [postPush_mass]
  -- the push mass of the `g`-cell under `Pa` is `P(g-cell) / P(y-cell)`
  have hpm : pushMass (postPush P (ind (cellOf y (y ω₀))) (isKernel_ind _).nonneg hy)
      (ind (cellOf g (g ω₀))) = pushMass P (ind (cellOf g (g ω₀))) / pushMass P (ind (cellOf y (y ω₀))) := by
    unfold pushMass
    simp only [postPush_mass, sum_div]
    apply sum_congr rfl; intro ω' _
    rw [div_mul_eq_mul_div, mul_assoc, ind_yCell_mul_ind_gCell y g href ω₀ ω']
    rfl
  rw [hpm, div_mul_eq_mul_div, mul_assoc, ind_yCell_mul_ind_gCell y g href ω₀ ω]
  field_simp

/-- The overseers' announced row `QH ω = P(· | g = g ω)` as a mass function (junk at a null
cell, where it is `0`; the theorems below only use it at positive-mass cells).
Source: [[general-object-final]] D4 (coarse-expert model), S15
Kind: D
Fidelity: exact at positive-mass cells -/
def announceRow {G : Type} [DecidableEq G] (P : Distr Ω) (g : Ω → G) (ω : Ω) : Ω → ℝ :=
  fun ω' => P.mass ω' * ind (cellOf g (g ω)) ω' / pushMass P (ind (cellOf g (g ω)))

/-- The coarsened press: the worlds whose announcement says `E[X] < 0`.
Source: [[general-object-final]] P10 (`Pr := {E[X | 𝒢] < 0}`)
Kind: D
Fidelity: exact -/
def coarsePress {G : Type} [DecidableEq G] (P : Distr Ω) (g : Ω → G) (X : Ω → ℝ) : Finset Ω :=
  univ.filter (fun ω => ∑ ω', announceRow P g ω ω' * X ω' < 0)

/-- Membership in the coarsened press depends only on the `g`-cell.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem coarsePress_congr {G : Type} [DecidableEq G] (P : Distr Ω) (g : Ω → G) (X : Ω → ℝ)
    {ω ω' : Ω} (h : g ω = g ω') : (ω ∈ coarsePress P g X ↔ ω' ∈ coarsePress P g X) := by
  simp only [coarsePress, mem_filter, mem_univ, true_and, announceRow, h]

/-- **T10(b): on the coarsened press the below-threshold inequality holds in every cell at once.**
Under the agent's credence `Pa = P(· | y = y ω₀)`, if the coarsened press `Pr` has positive
push mass then `E_{Pa}[X 𝟙_Pr] < 0` — for every `X` (so for every alternative's decision variable).
Proof: group the sum by `g`-cells; on each cell the `y`- and `Pr`-indicators are constant; a cell
inside `Pr` contributes `P(cell) · E_{QH}[X] < 0`, others contribute `0`.
Source: [[general-object-final]] S15, P10 (`E[X | y, Pr] = E[E[X | 𝒢] | y, Pr] < 0`); script (G)
Kind: P
Fidelity: exact (finite; common prior)
Hyps: (a) refinement, the two positivity guards -/
theorem coarse_press_negative {Y G : Type} [DecidableEq Y] [DecidableEq G] [Fintype G]
    (P : Distr Ω) (y : Ω → Y) (g : Ω → G) (href : ∃ f : G → Y, y = f ∘ g) (ω₀ : Ω)
    (hy : 0 < pushMass P (ind (cellOf y (y ω₀)))) (X : Ω → ℝ)
    (hPr : 0 < pushMass (postPush P (ind (cellOf y (y ω₀))) (isKernel_ind _).nonneg hy)
      (ind (coarsePress P g X))) :
    pushExpect (postPush P (ind (cellOf y (y ω₀))) (isKernel_ind _).nonneg hy)
      (ind (coarsePress P g X)) X < 0 := by
  obtain ⟨f, hf⟩ := href
  set Pr := coarsePress P g X with hPrdef
  set yC := cellOf y (y ω₀) with hyC
  -- reduce to the unnormalised sum under `P`
  have hpe : pushExpect (postPush P (ind yC) (isKernel_ind _).nonneg hy) (ind Pr) X =
      (∑ ω, P.mass ω * ind yC ω * ind Pr ω * X ω) / pushMass P (ind yC) := by
    unfold pushExpect; simp only [postPush_mass, sum_div]
    apply sum_congr rfl; intro ω _; unfold pushMass; ring
  have hpm : pushMass (postPush P (ind yC) (isKernel_ind _).nonneg hy) (ind Pr) =
      (∑ ω, P.mass ω * ind yC ω * ind Pr ω) / pushMass P (ind yC) := by
    unfold pushMass; simp only [postPush_mass, sum_div]
    apply sum_congr rfl; intro ω _; unfold pushMass; ring
  rw [hpm] at hPr
  rw [hpe, div_neg_iff]
  right
  refine ⟨?_, hy⟩
  have hmass : 0 < ∑ ω, P.mass ω * ind yC ω * ind Pr ω := (div_pos_iff_of_pos_right hy).1 hPr
  -- group by `g`-cells
  have hgroup : ∀ h : Ω → ℝ, ∑ ω, h ω = ∑ g₀ : G, ∑ ω ∈ cellOf g g₀, h ω := by
    intro h
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := g) (fun ω _ => mem_univ (g ω)) h]
    apply sum_congr rfl; intro g₀ _
    apply sum_congr _ (fun _ _ => rfl)
    ext ω; simp [cellOf]
  rw [hgroup] at hmass ⊢
  -- per-cell terms: the indicators are constant on the cell
  have hconst : ∀ g₀ : G, ∀ ω ∈ cellOf g g₀, ∀ ω' ∈ cellOf g g₀,
      ind yC ω * ind Pr ω = ind yC ω' * ind Pr ω' := by
    intro g₀ ω hω ω' hω'
    rw [mem_cellOf] at hω hω'
    have hgg : g ω = g ω' := by rw [hω, hω']
    have h1 : ind yC ω = ind yC ω' := by
      unfold ind Cleanroom.Found.LitDdbFrames.ind
      have : (ω ∈ yC ↔ ω' ∈ yC) := by
        rw [hyC, mem_cellOf, mem_cellOf, hf]; simp [Function.comp, hgg]
      simp only [this]
    have h2 : ind Pr ω = ind Pr ω' := by
      unfold ind Cleanroom.Found.LitDdbFrames.ind
      simp only [hPrdef, coarsePress_congr P g X hgg]
    rw [h1, h2]
  -- each cell's contribution is `c · ∑_cell P X` with `c ∈ {0, 1}` the common indicator value
  have hcell : ∀ g₀ : G, ∑ ω ∈ cellOf g g₀, P.mass ω * ind yC ω * ind Pr ω * X ω ≤ 0 ∧
      (0 < ∑ ω ∈ cellOf g g₀, P.mass ω * ind yC ω * ind Pr ω →
        ∑ ω ∈ cellOf g g₀, P.mass ω * ind yC ω * ind Pr ω * X ω < 0) := by
    intro g₀
    by_cases hne : (cellOf g g₀).Nonempty
    · obtain ⟨ω₁, hω₁⟩ := hne
      set c := ind yC ω₁ * ind Pr ω₁ with hc
      have hterm : ∀ ω ∈ cellOf g g₀, P.mass ω * ind yC ω * ind Pr ω * X ω = c * (P.mass ω * X ω) := by
        intro ω hω; rw [hc, ← hconst g₀ ω hω ω₁ hω₁]; ring
      have hterm' : ∀ ω ∈ cellOf g g₀, P.mass ω * ind yC ω * ind Pr ω = c * P.mass ω := by
        intro ω hω; rw [hc, ← hconst g₀ ω hω ω₁ hω₁]; ring
      rw [sum_congr rfl hterm, sum_congr rfl hterm', ← mul_sum, ← mul_sum]
      have hc01 : c = 0 ∨ c = 1 := by
        rw [hc]; unfold ind Cleanroom.Found.LitDdbFrames.ind; split_ifs <;> simp
      rcases hc01 with hc0 | hc1
      · rw [hc0]; simp
      · rw [hc1, one_mul, one_mul]
        -- `c = 1` means `ω₁ ∈ Pr`, i.e. the announcement at `ω₁` says `E[X] < 0`
        have hPr1 : ω₁ ∈ Pr := by
          by_contra hn
          have : ind Pr ω₁ = 0 := by simp [ind, Cleanroom.Found.LitDdbFrames.ind, hn]
          rw [hc, this, mul_zero] at hc1
          exact zero_ne_one hc1
        rw [hPrdef, coarsePress, mem_filter] at hPr1
        have hneg := hPr1.2
        rw [mem_cellOf] at hω₁
        -- `∑ announceRow X < 0` is `(∑_cell P X) / P(cell) < 0`
        have hrow : ∑ ω', announceRow P g ω₁ ω' * X ω' =
            (∑ ω ∈ cellOf g g₀, P.mass ω * X ω) / pushMass P (ind (cellOf g g₀)) := by
          unfold announceRow
          rw [hω₁, sum_div]
          rw [← sum_filter_add_sum_filter_not univ (fun ω => ω ∈ cellOf g g₀)]
          have e1 : univ.filter (fun ω => ω ∈ cellOf g g₀) = cellOf g g₀ := by ext; simp
          rw [e1]
          have e2 : ∑ ω ∈ univ.filter (fun ω => ¬ ω ∈ cellOf g g₀),
              P.mass ω * ind (cellOf g g₀) ω / pushMass P (ind (cellOf g g₀)) * X ω = 0 := by
            apply sum_eq_zero; intro ω hω
            rw [mem_filter] at hω
            rw [show ind (cellOf g g₀) ω = 0 from by
              simp [ind, Cleanroom.Found.LitDdbFrames.ind, hω.2]]
            ring
          rw [e2, add_zero]
          apply sum_congr rfl; intro ω hω
          rw [show ind (cellOf g g₀) ω = 1 from by simp [ind, Cleanroom.Found.LitDdbFrames.ind, hω]]
          ring
        rw [hrow] at hneg
        have hn : ∑ ω ∈ cellOf g g₀, P.mass ω * X ω < 0 := by
          rcases div_neg_iff.1 hneg with ⟨_, hd⟩ | ⟨hn, _⟩
          · exact absurd hd (not_lt.2 (pushMass_nonneg P (isKernel_ind _).nonneg))
          · exact hn
        exact ⟨hn.le, fun _ => hn⟩
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  -- sum of nonpositive terms, one of them negative
  have hex : ∃ g₀ ∈ (univ : Finset G), 0 < ∑ ω ∈ cellOf g g₀, P.mass ω * ind yC ω * ind Pr ω := by
    by_contra hall
    push Not at hall
    have : ∑ g₀ : G, ∑ ω ∈ cellOf g g₀, P.mass ω * ind yC ω * ind Pr ω ≤ 0 :=
      sum_nonpos fun g₀ hg₀ => hall g₀ hg₀
    linarith
  obtain ⟨g₀, _, hg₀⟩ := hex
  calc ∑ g₁ : G, ∑ ω ∈ cellOf g g₁, P.mass ω * ind yC ω * ind Pr ω * X ω
      < ∑ g₁ : G, (0 : ℝ) := sum_lt_sum (fun g₁ _ => (hcell g₁).1) ⟨g₀, mem_univ _, (hcell g₀).2 hg₀⟩
    _ = 0 := by simp

/-! ## Witness: `Fin 4`, `y` a 2-cell and `g` the 4-cell partition -/

/-- The witness prior `(1/10, 2/10, 3/10, 4/10)`. Source: mandate T10 witness. Kind: D. Fidelity: exact -/
def w10P : Distr (Fin 4) where
  mass := ![1/10, 2/10, 3/10, 4/10]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_four]; norm_num

/-- The agent's 2-cell signal `y ω = (ω ≥ 2)`. Source: mandate T10 witness. Kind: D. Fidelity: exact -/
def w10y : Fin 4 → Bool := fun ω => decide (2 ≤ ω.val)

/-- **The mandate's T10 instance (N−)**: `g = id` refines `y`; both the `y`-cell of world `3` and
the `g`-cell `{3}` have positive mass, so `tower_endorsed` applies — the push `𝟙_{g = 3}` is
endorsed from `P(· | y = true)` toward `P(· | g = 3) = δ₃`. **Degenerate** (audit r2 adversarial
B1): with `g = id` the announced target is a Dirac, and `Endorsed Pa 𝟙_{3} δ₃` holds for *every*
`Pa` with `Pa(3) > 0`, whatever the relation between `y` and `g` — the refinement hypothesis is
not exercised. Kept as the mandate's spec; the N+ instance is `w10c_tower_witness`.
Source: mandate T10 witness ("`g` a 4-cell partition" of a four-point carrier)
Kind: N−
Fidelity: exact (degenerate: `g = id`, every announcement a Dirac — findings F-23)
Hyps: (a) none -/
theorem w10_witness :
    (∃ f : Fin 4 → Bool, w10y = f ∘ id) ∧
      0 < pushMass w10P (ind (cellOf w10y (w10y 3))) ∧
      0 < pushMass w10P (ind (cellOf (id : Fin 4 → Fin 4) ((id : Fin 4 → Fin 4) 3))) ∧
      (∀ g₀ : Fin 4, 0 < pushMass w10P (ind (cellOf (id : Fin 4 → Fin 4) g₀))) ∧
      cellOf w10y true ≠ univ := by
  refine ⟨⟨w10y, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [pushMass_ind]
    have : cellOf w10y (w10y 3) = {2, 3} := by decide
    rw [this]; simp [w10P, sum_pair] <;> norm_num
  · rw [pushMass_ind]
    have : cellOf (id : Fin 4 → Fin 4) ((id : Fin 4 → Fin 4) 3) = {3} := by decide
    rw [this]; simp [w10P] <;> norm_num
  · intro g₀
    rw [pushMass_ind]
    have : cellOf (id : Fin 4 → Fin 4) g₀ = {g₀} := by ext; simp [cellOf]
    rw [this, sum_singleton]
    fin_cases g₀ <;> simp [w10P] <;> norm_num
  · decide

/-! ### T10(b)'s package on the witness (audit r1 adversarial 3.3)

`coarse_press_negative` needs a variable `X` whose coarsened press has positive push mass under
the agent's credence; `w10_witness` checks the signal masses only. With `g = id`,
`y = (ω ≥ 2)`, `X = (1, 1, −1, 1)`: the coarsened press is `{2}` (the one world whose
announcement `δ₂` has `E[X] < 0`), its push mass under `P(· | y = true)` is `3/7 > 0`, and the
theorem yields `E[X 𝟙_Pr] = −3/7 < 0`. Instance supplied by the round-1 adversarial audit
(`audit-r1-probes/CoarsePressInstance.lean`). -/

/-- The T10(b) variable `X = (1, 1, −1, 1)`. Source: audit r1 witness. Kind: D. Fidelity: exact -/
def w10X : Fin 4 → ℝ := ![1, 1, -1, 1]

/-- With `g = id` every `g`-cell is a singleton. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem w10_cellOf_id (ω : Fin 4) : cellOf (id : Fin 4 → Fin 4) (id ω) = {ω} := by
  ext; simp [cellOf]

/-- With `g = id` the announcement at `ω` is `δ_ω`. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem w10_announceRow (ω ω' : Fin 4) :
    announceRow w10P (id : Fin 4 → Fin 4) ω ω' = if ω' = ω then 1 else 0 := by
  unfold announceRow
  rw [w10_cellOf_id, pushMass_ind, sum_singleton]
  have hpos : 0 < w10P.mass ω := by fin_cases ω <;> simp [w10P] <;> norm_num
  by_cases h : ω' = ω
  · subst h; simp [ind, Cleanroom.Found.LitDdbFrames.ind, hpos.ne']
  · simp [ind, Cleanroom.Found.LitDdbFrames.ind, h]

/-- The coarsened press of `X = (1, 1, −1, 1)` under `g = id` is `{2}`.
Source: audit r1 witness. Kind: L. Fidelity: exact -/
theorem w10_coarsePress : coarsePress w10P (id : Fin 4 → Fin 4) w10X = {2} := by
  ext ω
  simp only [coarsePress, mem_filter, mem_univ, true_and, w10_announceRow, mem_singleton]
  fin_cases ω <;> simp [w10X, Fin.sum_univ_four]

/-- The `y`-cell of world `3` is `{2, 3}`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem w10_yCell : cellOf w10y (w10y 3) = {2, 3} := by decide

/-- **The mandate's T10(b) instance (N−)**: on the T10 witness with `X = (1, 1, −1, 1)` the
coarsened press `{2}` has push mass `3/7 > 0` under `P(· | y = true)`, and
`coarse_press_negative` gives `E[X 𝟙_Pr] < 0` (`= −3/7`). **Degenerate** (audit r2 adversarial
B1): with `g = id` the announcement at `ω` is `δ_ω`, so the coarsened press is the exact press
`{X < 0}` and the inequality is immediate from positive mass — the within-cell averaging the
theorem is about is not exercised. The N+ instance is `w10c_coarse_press_witness`.
Source: mandate T10 witness; audit r1 adversarial 3.3
Kind: N−
Fidelity: exact (degenerate: `g = id` — findings F-23)
Hyps: (a) none -/
theorem w10_coarse_press_package :
    0 < pushMass (postPush w10P (ind (cellOf w10y (w10y 3))) (isKernel_ind _).nonneg
        w10_witness.2.1) (ind (coarsePress w10P (id : Fin 4 → Fin 4) w10X)) ∧
      pushExpect (postPush w10P (ind (cellOf w10y (w10y 3))) (isKernel_ind _).nonneg
        w10_witness.2.1) (ind (coarsePress w10P (id : Fin 4 → Fin 4) w10X)) w10X < 0 := by
  have hPr : 0 < pushMass (postPush w10P (ind (cellOf w10y (w10y 3))) (isKernel_ind _).nonneg
      w10_witness.2.1) (ind (coarsePress w10P (id : Fin 4 → Fin 4) w10X)) := by
    rw [w10_coarsePress, pushMass_ind, sum_singleton, postPush_mass, pushMass_ind, w10_yCell,
      sum_pair (by decide)]
    simp [w10P, ind, Cleanroom.Found.LitDdbFrames.ind]; norm_num
  exact ⟨hPr, coarse_press_negative w10P w10y id ⟨w10y, rfl⟩ 3 w10_witness.2.1 w10X hPr⟩

/-! ## Witness (N+): `Fin 6`, `g` strictly coarser than the points (audit r2 adversarial B1)

`Ω = Fin 6`, `P = (1/12, 1/6, 1/4, 1/6, 1/12, 1/4)`, `y = (ω ≥ 3)` (two cells), `g = (0,0,1,2,2,3)`
(four cells, two of them two-world cells), `X = (1, −3, 1, 1, −5, 1)`. The announced cell of
world `3` is `{3, 4}` with the non-Dirac target `(2/3, 1/3)`; its announcement has
`E[X] = (2/3)(1) + (1/3)(−5) = −1 < 0`, so world `3` is in the coarsened press although
`X 3 = 1 > 0`. Under `P(· | y = true) = (1/3, 1/6, 1/2)` on `{3, 4, 5}` the press has mass `1/2`
and `E[X 𝟙_Pr] = (1/3)(1) + (1/6)(−5) = −1/2`. -/

/-- The N+ prior `(1/12, 1/6, 1/4, 1/6, 1/12, 1/4)`. Source: audit r2 adversarial probe
`TowerCoarse.lean`. Kind: D. Fidelity: exact -/
def w10cP : Distr (Fin 6) where
  mass := ![1/12, 1/6, 1/4, 1/6, 1/12, 1/4]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_six]; norm_num

/-- The agent's 2-cell signal `y ω = (ω ≥ 3)`. Source: audit r2 adversarial probe. Kind: D.
Fidelity: exact -/
def w10cy : Fin 6 → Bool := fun ω => decide (3 ≤ ω.val)

/-- The overseers' 4-cell signal `g = (0, 0, 1, 2, 2, 3)` — strictly coarser than the points.
Source: audit r2 adversarial probe. Kind: D. Fidelity: exact -/
def w10cg : Fin 6 → Fin 4 := ![0, 0, 1, 2, 2, 3]

/-- `y = f ∘ g` with `f = (false, false, true, true)`. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem w10c_refines : ∃ f : Fin 4 → Bool, w10cy = f ∘ w10cg :=
  ⟨![false, false, true, true], by funext ω; fin_cases ω <;> rfl⟩

/-- The `y`-cell of world `3` is `{3, 4, 5}`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem w10c_yCell : cellOf w10cy (w10cy 3) = {3, 4, 5} := by decide

/-- The `g`-cell of world `3` is `{3, 4}` — two worlds. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem w10c_gCell : cellOf w10cg (w10cg 3) = {3, 4} := by decide

/-- The `y`-cell has positive mass (`1/2`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem w10c_yMass : 0 < pushMass w10cP (ind (cellOf w10cy (w10cy 3))) := by
  rw [pushMass_ind, w10c_yCell]
  simp [w10cP, sum_insert]; norm_num

/-- The `g`-cell has positive mass (`1/4`). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem w10c_gMass : 0 < pushMass w10cP (ind (cellOf w10cg (w10cg 3))) := by
  rw [pushMass_ind, w10c_gCell, sum_pair (by decide)]
  simp [w10cP]; norm_num

/-- **N+ for T10(a)**: the announced cell `{3, 4}` has two worlds, the announced target is
`(2/3, 1/3)` on them (not a Dirac), and the endorsement from the agent's credence
`P(· | y = true)` is obtained *through* `tower_endorsed` — the refinement hypothesis is
exercised (with `y` and `g` unrelated the conclusion would fail).
Source: [[general-object-final]] S15 (overseers strictly finer than the agent, not the points);
audit r2 adversarial B1 (`audit-r2-probes/TowerCoarse.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem w10c_tower_witness :
    (postPush w10cP (ind (cellOf w10cg (w10cg 3))) (isKernel_ind _).nonneg w10c_gMass).mass 3 = 2/3 ∧
      (postPush w10cP (ind (cellOf w10cg (w10cg 3))) (isKernel_ind _).nonneg w10c_gMass).mass 4 = 1/3 ∧
      Endorsed (postPush w10cP (ind (cellOf w10cy (w10cy 3))) (isKernel_ind _).nonneg w10c_yMass)
        (ind (cellOf w10cg (w10cg 3)))
        (postPush w10cP (ind (cellOf w10cg (w10cg 3))) (isKernel_ind _).nonneg w10c_gMass) := by
  have hm : pushMass w10cP (ind (cellOf w10cg (w10cg 3))) = 1/4 := by
    rw [pushMass_ind, w10c_gCell, sum_pair (by decide)]; simp [w10cP]; norm_num
  refine ⟨?_, ?_, tower_endorsed w10cP w10cy w10cg w10c_refines 3 w10c_yMass w10c_gMass⟩
  · rw [postPush_mass, hm, w10c_gCell]; simp [w10cP, ind, Cleanroom.Found.LitDdbFrames.ind]; norm_num
  · rw [postPush_mass, hm, w10c_gCell]; simp [w10cP, ind, Cleanroom.Found.LitDdbFrames.ind]; norm_num

/-- The T10(b) variable `X = (1, −3, 1, 1, −5, 1)`. Source: audit r2 adversarial probe. Kind: D.
Fidelity: exact -/
def w10cX : Fin 6 → ℝ := ![1, -3, 1, 1, -5, 1]

/-- World `3` is in the coarsened press: its cell `{3, 4}` announces `E[X] = −1 < 0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem w10c_mem_press : (3 : Fin 6) ∈ coarsePress w10cP w10cg w10cX := by
  simp only [coarsePress, mem_filter, mem_univ, true_and, announceRow]
  rw [w10c_gCell]
  have hm : pushMass w10cP (ind ({3, 4} : Finset (Fin 6))) = 1/4 := by
    rw [pushMass_ind, sum_pair (by decide)]; simp [w10cP]; norm_num
  rw [hm]
  simp [w10cP, w10cX, ind, Cleanroom.Found.LitDdbFrames.ind, Fin.sum_univ_six]; norm_num

/-- The coarsened press has positive push mass under the agent's credence `P(· | y = true)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem w10c_press_mass_pos :
    0 < pushMass (postPush w10cP (ind (cellOf w10cy (w10cy 3))) (isKernel_ind _).nonneg w10c_yMass)
      (ind (coarsePress w10cP w10cg w10cX)) := by
  rw [pushMass_ind]
  apply lt_of_lt_of_le _ (single_le_sum (f := fun ω =>
    (postPush w10cP (ind (cellOf w10cy (w10cy 3))) (isKernel_ind _).nonneg w10c_yMass).mass ω)
    (fun ω _ => (postPush w10cP _ _ w10c_yMass).nonneg ω) w10c_mem_press)
  rw [postPush_mass, w10c_yCell]
  have hm : pushMass w10cP (ind ({3, 4, 5} : Finset (Fin 6))) = 1/2 := by
    rw [pushMass_ind]; simp [w10cP, sum_insert]; norm_num
  rw [hm]; simp [w10cP, ind, Cleanroom.Found.LitDdbFrames.ind]

/-- **N+ for T10(b)**: a world with `X > 0` lies in the coarsened press (its cell's average is
negative — the within-cell averaging is exercised), the press has positive push mass, and the
conclusion `E_{Pa}[X 𝟙_Pr] < 0` is obtained through `coarse_press_negative` (`= −1/2`).
Source: [[general-object-final]] S15, P10; audit r2 adversarial B1 (`audit-r2-probes/TowerCoarse.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem w10c_coarse_press_witness :
    (3 : Fin 6) ∈ coarsePress w10cP w10cg w10cX ∧ 0 < w10cX 3 ∧
      pushExpect (postPush w10cP (ind (cellOf w10cy (w10cy 3))) (isKernel_ind _).nonneg w10c_yMass)
        (ind (coarsePress w10cP w10cg w10cX)) w10cX < 0 :=
  ⟨w10c_mem_press, by simp [w10cX],
    coarse_press_negative w10cP w10cy w10cg w10c_refines 3 w10c_yMass w10cX w10c_press_mass_pos⟩

end

end Cleanroom.Corrigibility.CorrGeneralObject
