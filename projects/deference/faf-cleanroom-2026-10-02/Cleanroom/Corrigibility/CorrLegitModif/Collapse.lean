import Cleanroom.Corrigibility.CorrLegitModif.Plumbing
import Cleanroom.Corrigibility.CorrReflectFrames.Collapse
import Cleanroom.Lit.LitDdbFacts.Reflection
import Cleanroom.Found.LitDdbFrames.Strategies

/-!
# corr-legit-modif — T2(a), T2(c): collapse under Reflection; domination under Value

[[approval-final]] D4–D5, S1, P1: on the reflection domain the value learner
`δ^VL = argmax_a E_P[U(a)]` and the uninformed approval-directed agent
`δ^{AD-u} = argmax_a E_P[R(a)]`, `R(a) = E_H[U(a)]`, are one decision rule — the tower property
`E_P[U(a)] = E_P[R(a)]`. Here, over DDB frames: `rating F o w := E_{P_w}(o)`, `vlChoice` is
`maximizers 𝒪 π`, `adUninformed` the same filter with `E_π(rating F o)`, and the collapse is
*set equality of the two argmax `Finset`s* (ties handled by the set, never by picking an
element).

Three strengths of hypothesis, from the strongest: full Reflection (`collapse_of_reflects`, via
`corr-reflect-frames`' `VarReflects`/`EstimateMatching`), Reflection with respect to a question
coarse enough to determine the utilities (`reflectsOn_of_reflectsWrt`), and the source's own
hypothesis — D5's Reflection on the domain `{U(a)}` only, `ReflectsOn`
(`collapse_of_reflectsOn`, by summing the level-set identities over the attained values).

**Scope (A1.1–A1.3, Known issues 8)**: the hypothesis holds only toward an immodest overseer —
`not_reflects_of_modestAt` (`lit-ddb-facts`), `immodest_of_legitReflects`
(`corr-legit-general`) — and the identity `E_π(X) = ∑ π_w E_{P_w}(X)` is the naive tower that
`corr-legit-general`'s `inf3_tower_refuted` refutes under Total Trust alone (`−41/100 ≠ −1/5`):
a "collapse" on a modest frame is vacuous, and under mere Total Trust the two rules separate
(`Separation.lean`). The calibrated-refining case `R(a) = E_P[U(a) | 𝒥]`, `𝒥 ⊇ ℐ`, is the
Bayesian refinement `refineFrame`, which reflects (`refineFrame_reflects`, cited).

T2(c): `domination_of_valuesWrt` (corr-wf14-124, P12) is the Value inequality read on the
`π`-optimal option — an instance of `ValuesWrt`, kind L; `stratValue_eq_of_single_cand` is the
simulating agent (A15.1): when every support row is `π` itself the recommended strategy's value
equals the `π`-optimum. Nothing about the mistreatment cost (Known issues 9).
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrLegitGeneral

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-! ## Decision rules -/

/-- The overseer's **rating** of an option: `R(o)(w) := E_{P_w}(o)`, a random variable.
Source: [[approval-final]] D4 l. 25 (`R_t(a) := E_H[U(a)]`), D5 l. 27
Kind: D
Fidelity: exact -/
def rating (F : Frame W) (o : W → ℝ) : W → ℝ := fun w => E (F.P w) o

/-- The **value learner's** choice set `δ^VL := argmax_{o ∈ 𝒪} E_π(o)`, as a `Finset` (all ties).
Source: [[approval-final]] D4 l. 25
Kind: D
Fidelity: exact (`maximizers` of `lit-ddb-frames`) -/
abbrev vlChoice (𝒪 : DecisionProblem W) (π : W → ℝ) : Finset (W → ℝ) := maximizers 𝒪 π

/-- The **uninformed approval-directed** choice set `δ^{AD-u} := argmax_{o ∈ 𝒪} E_π(R(o))`: act
on your expectation of the overseer's rating.
Source: [[approval-final]] D4 l. 25
Kind: D
Fidelity: exact -/
def adUninformed (𝒪 : DecisionProblem W) (π : W → ℝ) (F : Frame W) : Finset (W → ℝ) :=
  𝒪.filter (fun o => ∀ o' ∈ 𝒪, E π (rating F o') ≤ E π (rating F o))

/-- **Reflection with respect to one variable** (D5's hypothesis on the domain `{U(a)}`):
`E_π[X | R(X) = c] = c` for every attained `c`, in product form
`∑ w, π w · (X w − c) · 𝟙[E_{P_w}(X) = c] = 0` for every `c` (vacuous at unattained or null
levels). This is `corr-reflect-frames`' `VarReflects` at a single `X` (`reflectsOn_iff_varReflects_clause`).
D5's "given `ℐ`" clause is dropped here (`rating` is `E_{P_w}(o)`, a function of `w`); the
`ℐ`-conditioned variant is `ReflectsWrt`, handled by `collapse_of_reflectsWrt`.
Source: [[approval-final]] D5 l. 27 ("`P` reflects toward the overseer on `𝒟` given `ℐ` iff
`E_P[X | R(X) = c, ℐ] = c` for all `X ∈ 𝒟` and attained `c`")
Kind: D
Fidelity: exact (product form) -/
def ReflectsOn (X : W → ℝ) (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ c : ℝ, ∑ w, π w * (X w - c) * (if E (F.P w) X = c then 1 else 0) = 0

/-- The product-form clause is `VarReflects`' clause at `X`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem reflectsOn_iff_varReflects_clause (X π : W → ℝ) (F : Frame W) :
    ReflectsOn X π F ↔ ∀ s : ℝ, ∑ w ∈ estCell F X s, π w * X w = s * mass π (estCell F X s) := by
  unfold ReflectsOn
  apply forall_congr'
  intro c
  have e : ∑ w, π w * (X w - c) * (if E (F.P w) X = c then 1 else 0) =
      ∑ w ∈ estCell F X c, π w * X w - c * mass π (estCell F X c) := by
    unfold mass estCell
    rw [mul_sum, ← sum_sub_distrib, sum_filter]
    apply sum_congr rfl; intro w _
    split_ifs <;> ring
  rw [e, sub_eq_zero]

/-- Reflection implies Reflection with respect to every variable.
Source: none: infrastructure (`corr-reflect-frames` `varReflects_of_reflects`)
Kind: L
Fidelity: n/a -/
theorem reflectsOn_of_reflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : Reflects π F)
    (X : W → ℝ) : ReflectsOn X π F :=
  (reflectsOn_iff_varReflects_clause X π F).2 (fun s => varReflects_of_reflects hπ h X s)

/-! ## Grouping a sum by candidate cells -/

/-- A `π`-weighted sum of a function of the row groups by the candidates' cells (null worlds
contribute nothing, and the cells of distinct candidates are disjoint).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_by_cells {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (F : Frame W) (g : (W → ℝ) → W → ℝ) :
    ∑ w, π w * g (F.P w) w = ∑ ρ ∈ F.cands π, ∑ w ∈ F.cell ρ, π w * g ρ w := by
  have h1 : ∑ w, π w * g (F.P w) w = ∑ w ∈ supp π, π w * g (F.P w) w := by
    symm
    apply sum_subset (subset_univ _)
    intro w _ hw
    rw [eq_zero_of_not_mem_supp hπ hw, zero_mul]
  have h2 : ∑ w ∈ supp π, π w * g (F.P w) w =
      ∑ ρ ∈ F.cands π, ∑ w ∈ (supp π).filter (fun w => F.P w = ρ), π w * g (F.P w) w := by
    symm
    apply sum_fiberwise_of_maps_to
    intro w hw
    exact mem_image_of_mem F.P hw
  rw [h1, h2]
  apply sum_congr rfl
  intro ρ _
  have h3 : ∑ w ∈ (supp π).filter (fun w => F.P w = ρ), π w * g (F.P w) w =
      ∑ w ∈ (supp π).filter (fun w => F.P w = ρ), π w * g ρ w := by
    apply sum_congr rfl; intro w hw
    rw [(mem_filter.1 hw).2]
  rw [h3]
  apply sum_subset
  · intro w hw
    rw [mem_filter] at hw
    exact Frame.mem_cell.2 hw.2
  · intro w hw hnw
    rw [Frame.mem_cell] at hw
    rw [mem_filter, not_and] at hnw
    have : w ∉ supp π := fun h => hnw h hw
    rw [eq_zero_of_not_mem_supp hπ this, zero_mul]

/-- On a candidate's cell, Reflection with respect to `Q` turns a `π`-weighted sum of a
`Q`-measurable variable into `π(P = ρ) · E_ρ(X)` (the local form of `reflects_cell_sum`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem reflectsWrt_cell_sum {Q : W → C} {π : W → ℝ} {F : Frame W} (h : ReflectsWrt Q π F)
    {ρ : W → ℝ} (hρ : ρ ∈ F.cands π) {X : W → ℝ} (hX : MeasurableWrt Q X) :
    ∑ w ∈ F.cell ρ, π w * X w = mass π (F.cell ρ) * E ρ X := by
  obtain ⟨x, rfl⟩ := (measurableWrt_iff_exists_comp Q X).1 hX
  have key : ∀ (σ : W → ℝ) (A : Finset W),
      ∑ w ∈ A, σ w * (x ∘ Q) w = ∑ c, x c * mass σ (A ∩ answer Q {c}) := by
    intro σ A
    have e : ∀ w, σ w * (x ∘ Q) w = ∑ c, if Q w = c then x c * σ w else 0 := by
      intro w; rw [sum_ite_eq]; simp [Function.comp, mul_comm]
    simp only [e]
    rw [sum_comm]
    apply sum_congr rfl; intro c _
    unfold mass
    rw [mul_sum, ← filter_mem_eq_inter, sum_filter]
    apply sum_congr rfl; intro w _
    simp only [answer, mem_filter, mem_univ, true_and, mem_singleton]
  rw [key, E, key, mul_sum]
  apply sum_congr rfl; intro c _
  rw [h ρ hρ {c}]
  have : mass ρ (univ ∩ answer Q {c}) = mass ρ (answer Q {c}) := by rw [univ_inter]
  rw [this]; ring

/-- Reflection with respect to a question implies Reflection with respect to every variable the
question determines.
Source: none: infrastructure (the second weakening of S1's hypothesis)
Kind: L
Fidelity: n/a -/
theorem reflectsOn_of_reflectsWrt {Q : W → C} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : ReflectsWrt Q π F) {X : W → ℝ} (hX : MeasurableWrt Q X) : ReflectsOn X π F := by
  intro c
  simp only [mul_assoc]
  rw [sum_by_cells hπ F (fun ρ w => (X w - c) * (if E ρ X = c then 1 else 0))]
  apply sum_eq_zero
  intro ρ hρ
  have e : ∑ w ∈ F.cell ρ, π w * ((X w - c) * (if E ρ X = c then 1 else 0)) =
      (if E ρ X = c then 1 else 0) * (∑ w ∈ F.cell ρ, π w * X w - c * mass π (F.cell ρ)) := by
    unfold mass
    rw [mul_sum, ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl; intro w _; ring
  rw [e, reflectsWrt_cell_sum h hρ hX]
  split_ifs with hc
  · rw [hc]; ring
  · ring

/-! ## The tower identity -/

/-- **The tower under one-variable Reflection**: `E_π(X) = E_π(R(X))` — sum the level-set
identities over the attained values of `R(X)`; each world is counted at exactly its own level.
This is the content of S1's proof ("Tower property … the objectives agree on every `a`").
Source: [[approval-final]] P1 l. 87; corr-wf14-114
Kind: L (one summation of the hypothesis's level-set clauses over the attained values; regraded at
audit round 1)
Fidelity: exact
Hyps: (a) none beyond `ReflectsOn` -/
theorem tower_of_reflectsOn {X π : W → ℝ} {F : Frame W} (h : ReflectsOn X π F) :
    E π X = E π (rating F X) := by
  have hsum : ∑ c ∈ univ.image (fun w => E (F.P w) X),
      ∑ w, π w * (X w - c) * (if E (F.P w) X = c then 1 else 0) = 0 :=
    sum_eq_zero (fun c _ => h c)
  rw [sum_comm] at hsum
  have e : ∀ w, ∑ c ∈ univ.image (fun w => E (F.P w) X),
      π w * (X w - c) * (if E (F.P w) X = c then 1 else 0) = π w * (X w - E (F.P w) X) := by
    intro w
    simp only [mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq, if_pos (mem_image_of_mem _ (mem_univ w))]
  simp only [e] at hsum
  have : E π X - E π (rating F X) = ∑ w, π w * (X w - E (F.P w) X) := by
    rw [← E_sub_right]; rfl
  linarith

/-- **The tower under Reflection** (`corr-reflect-frames`' `EstimateMatching`, through
`VarReflects`): `E_π(X) = E_π(R(X))` for every `X`.
Source: [[approval-final]] P1 l. 87 ("Tower property"); [[Deference Done Better]] fn 16;
corr-wf14-114
Kind: C (cited `varReflects_of_reflects`, `estimateMatching_of_varReflects`)
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` -/
theorem tower_of_reflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : Reflects π F)
    (X : W → ℝ) : E π X = E π (rating F X) :=
  tower_of_reflectsOn (reflectsOn_of_reflects hπ h X)

/-! ## The collapse -/

/-- **S1, collapse under Reflection on the domain** (the source's own hypothesis): if `π`
reflects toward the overseer with respect to every option of the menu, the value learner's and
the uninformed approval-directed agent's choice sets coincide as `Finset`s (ties by set
equality). Scope: the hypothesis holds only toward an immodest overseer (A1.1–A1.3:
`not_reflects_of_modestAt`, `immodest_of_legitReflects`); under Total Trust alone the identity
fails (`inf3_tower_refuted`) and the rules separate (`separation_p2`).
Source: [[approval-final]] S1 l. 51, P1 l. 87, D4–D5 ll. 25–27; corr-wf14-114
Kind: L (`filter_congr` plus the tower; regraded at audit round 1)
Fidelity: exact (set equality of the argmax sets, the source's "as sets")
Hyps: (a) `ReflectsOn o π F` for every `o ∈ 𝒪` (D5 on `𝒟_t = {U(a)}`) -/
theorem collapse_of_reflectsOn {𝒪 : DecisionProblem W} {π : W → ℝ} {F : Frame W}
    (h : ∀ o ∈ 𝒪, ReflectsOn o π F) : vlChoice 𝒪 π = adUninformed 𝒪 π F := by
  unfold vlChoice adUninformed maximizers
  apply filter_congr
  intro o ho
  apply forall_congr'; intro o'; apply imp_congr_right; intro ho'
  rw [← tower_of_reflectsOn (h o ho), ← tower_of_reflectsOn (h o' ho')]

/-- **S1 under full Reflection**: `δ^VL = δ^{AD-u}` for every menu. Same scope as
`collapse_of_reflectsOn`.
Source: [[approval-final]] S1 l. 51; corr-wf14-114
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `Reflects π F` -/
theorem collapse_of_reflects {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} (h : Reflects π F)
    (𝒪 : DecisionProblem W) : vlChoice 𝒪 π = adUninformed 𝒪 π F :=
  collapse_of_reflectsOn (fun o _ => reflectsOn_of_reflects hπ h o)

/-- **S1 under local Reflection**: Reflection with respect to a question that determines every
option collapses the two rules.
Source: [[approval-final]] S1 l. 51 (D5's "given `ℐ`" read as a question); corr-wf14-114
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `ReflectsWrt Q π F`, every option `Q`-measurable -/
theorem collapse_of_reflectsWrt {Q : W → C} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (h : ReflectsWrt Q π F) {𝒪 : DecisionProblem W} (h𝒪 : ∀ o ∈ 𝒪, MeasurableWrt Q o) :
    vlChoice 𝒪 π = adUninformed 𝒪 π F :=
  collapse_of_reflectsOn (fun o ho => reflectsOn_of_reflectsWrt hπ h (h𝒪 o ho))

/-- **The calibrated-refining case reflects**: `R(a) = E_P[U(a) | 𝒥]` with `𝒥 ⊇ ℐ` is the
Bayesian refinement along the partition `𝒥`, which `π` reflects — so S1's hypothesis holds there
(cited `refineFrame_reflects`).
Source: [[approval-final]] S1 l. 51 ("in particular the calibrated-refining case"), P1 l. 87
Kind: L (cited (a))
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w` -/
theorem collapse_refineFrame {S : Type} [DecidableEq S] {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    (f : W → S) (𝒪 : DecisionProblem W) :
    vlChoice 𝒪 π = adUninformed 𝒪 π (refineFrame π hπ f) :=
  collapse_of_reflects hπ (refineFrame_reflects hπ f) 𝒪

/-! ## T2(c): domination under Value; the simulating agent -/

/-- **P12 / corr-wf14-124**: under Value with respect to `Q`, acting on the realised report
(any recommended strategy) is worth at least the `π`-optimal option of a `Q`-measurable menu —
`ValuesWrt` read at the maximiser. Says nothing about the mistreatment cost of the read
(A15.2, Known issues 9); corr-wf14-2-056 is this row.
Source: [[approval-final]] S15 l. 79, P12 l. 151; corr-wf14-124, corr-wf14-2-056
Kind: L
Fidelity: exact
Hyps: (a) `ValuesWrt Q π F`, nonempty `Q`-measurable menu, `o ∈ vlChoice`, `S` recommended -/
theorem domination_of_valuesWrt {Q : W → C} {π : W → ℝ} {F : Frame W} (h : ValuesWrt Q π F)
    {𝒪 : DecisionProblem W} (hne : 𝒪.Nonempty) (hmeas : ∀ o ∈ 𝒪, MeasurableWrt Q o)
    {o : W → ℝ} (ho : o ∈ vlChoice 𝒪 π) {S : W → (W → ℝ)} (hS : F.Recommended 𝒪 S) :
    E π o ≤ stratValue π S :=
  h 𝒪 hne hmeas S hS o (mem_maximizers.1 ho).1

/-- **The simulating agent (A15.1)**: when every support row of the frame is `π` itself (the
agent "knows exactly what Hugh will say"), a recommended strategy is constant on the support and
is a `π`-maximiser, so its value *equals* the `π`-optimum — Value holds with equality and the
read buys nothing.
Source: [[approval-adversary]] A15.1 l. 179; [[approval-final]] S15 l. 79 ("equality when
`R^cons_t` is `ℐ'_t`-measurable")
Kind: L
Fidelity: exact
Hyps: (a) `∀ w, 0 < π w → F.P w = π`, `0 < mass π univ`, `o ∈ vlChoice`, `S` recommended -/
theorem stratValue_eq_of_single_cand {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    (hF : ∀ w, 0 < π w → F.P w = π) {𝒪 : DecisionProblem W} {o : W → ℝ} (ho : o ∈ vlChoice 𝒪 π)
    {S : W → (W → ℝ)} (hS : F.Recommended 𝒪 S) {w₀ : W} (hw₀ : 0 < π w₀) :
    stratValue π S = E π o := by
  have hconst : ∀ w, 0 < π w → S w = S w₀ :=
    fun w hw => hS.1.2 w w₀ ((hF w hw).trans (hF w₀ hw₀).symm)
  have h1 : stratValue π S = E π (S w₀) := by
    unfold stratValue E
    apply sum_congr rfl; intro w _
    rcases (hπ w).lt_or_eq with hw | hw
    · rw [hconst w hw]
    · rw [← hw]; ring
  have hmax := mem_maximizers.1 ho
  have hSw₀ : S w₀ ∈ 𝒪 := hS.1.1 w₀
  have hle : E π (S w₀) ≤ E π o := hmax.2 _ hSw₀
  have hge : E π o ≤ E π (S w₀) := by
    have := hS.2 w₀ o hmax.1
    rwa [hF w₀ hw₀] at this
  rw [h1]; exact le_antisymm hle hge

end

end Cleanroom.Corrigibility.CorrLegitModif
