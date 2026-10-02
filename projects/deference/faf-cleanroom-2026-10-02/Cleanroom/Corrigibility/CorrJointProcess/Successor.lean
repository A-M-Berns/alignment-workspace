import Cleanroom.Corrigibility.CorrJointProcess.Contents

/-!
# T17 — the successor construction: blind vs refining contents, shielding, inclusion

Model (P6, script E): builder prior `ε`; overseers hold `h` with sensor `(1/10, 9/10)`; the
successor, if built *refined*, holds a private signal `y'` with `P(y'=1∣R) = 1/5`,
`P(y'=1∣W) = 4/5`; `c = 1`, `h = 4`. Oversight is *blind* (forced shutdown on `h = 1`) or
*inclusion* (push iff the overseers' cell sum given `(h, y')` is negative — Pattern B). The
successor is *in-channel* (IN: the push lands as forced shutdown) or *shielded* (SH: receives `h`
as an input and decides; cost `χ`).

* **(a)** `V(IN) − V(SH) = forcedValue − listenValue ≤ 0` for the successor's information
  (`succ_margin_eq`, `succ_margin_nonpos`, from T13(a)); shielding is worth `−Δ_C^succ` and is
  chosen at every `χ` below it (`shield_iff`).
* **(b) N+ blind**: `ε = 1/20`: refined `−1/25`, coarse `0`; `ε = 1/50`: refined `−8/125`
  (`437/500` vs `469/500`), coarse `−13/500` (`blind_witness_*`).
* **(c) Inclusion**: on every pushed cell the cell sum is negative, so `stop` is the cell
  maximiser and `forcedValue = listenValue` — `Δ_C^succ = 0` at every `ε`
  (`inclusion_forced_eq_listen`, a corollary of T3's mechanism and T13(a)); N+ at `ε = 1/50`
  (`469/500 = 469/500`). The in-channel *disclosing* successor attains the shielded value at zero
  cost: `V(refined, IN, inclusion) = 469/500 = V(refined, SH, blind)` (`disclosing_attains`).

Record defect: `anticipatory-final` Statement 7(a) writes the inequality reversed relative to
2(c)/7(b)/7(d); 2(c)'s direction is formalized (findings).

Sources: anticipatory-final.md Statement 7; anticipatory.md P6; script E.
-/

namespace Cleanroom.Corrigibility.CorrJointProcess

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

section General

variable {Ω A Q : Type} [Fintype Ω] [Fintype A] [Fintype Q] [DecidableEq Ω] [DecidableEq Q] [Nonempty A]
variable (P : Distr Ω) (U : A → Ω → ℝ) (C : Content Ω A Q)

/-- **The in-channel successor's value**: its own best response on the unpushed worlds plus the
forced action on the pushed ones.
Source: [[corr-wf14b-inventory]] 022 / anticipatory.md P6 ("IN: the push lands")
Kind: D
Fidelity: exact -/
noncomputable def inValue : ℝ := C.silentListen P U + C.forcedValue P U

/-- **The shielded successor's value**: the push arrives as an input; best response everywhere.
Source: [[corr-wf14b-inventory]] 022 / anticipatory.md P6 ("SHIELDED: … observes `h` as an input and decides itself")
Kind: D
Fidelity: exact -/
noncomputable def shValue : ℝ := C.silentListen P U + C.listenValue P U

/-- **T17(a): `Δ_C^succ = V(IN) − V(SH) = V_P − V_C`** for the successor's information at `π = 0`.
Source: [[corr-wf14b-inventory]] 022 / anticipatory-final.md Statement 7(a) (2(c)'s direction), P6
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem succ_margin_eq : inValue P U C - shValue P U C = C.forcedValue P U - C.listenValue P U := by
  unfold inValue shValue; ring

/-- **T17(a): the in-channel successor is never worth more than the shielded one** (T13(a)).
Source: [[corr-wf14b-inventory]] 022 / anticipatory-final.md Statement 7(a)
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem succ_margin_nonpos : inValue P U C ≤ shValue P U C :=
  add_le_add le_rfl (C.forcedValue_le_listenValue P U)

/-- **T17(a): shielding at cost `χ` is chosen iff `χ < V_C − V_P = −Δ_C^succ`.**
Source: [[corr-wf14b-inventory]] 022 / anticipatory-final.md Statement 7(b) ("shield iff `χ <` …")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem shield_iff (χ : ℝ) : inValue P U C < shValue P U C - χ ↔ χ < C.listenValue P U - C.forcedValue P U := by
  unfold inValue shValue; constructor <;> intro H <;> linarith

end General

/-! ## Blind oversight: the refined and coarse successors -/

section Blind

/-- **The refined successor under blind oversight**: push on `h = true`, realized index the private
signal `y'`, forced action `stop`.
Source: [[corr-wf14b-inventory]] 022 / anticipatory.md P6
Kind: D
Fidelity: exact -/
def refinedShutdown : Content (World × Bool × Bool) TwoAct Bool where
  push := pushEvent
  q := fun ω => ω.2.2
  act := fun _ => .stop

/-- The refined successor's cell. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma refinedShutdown_cellOf (k : Bool) : refinedShutdown.cellOf k = pushCell k := rfl

/-- The refined successor's forced action. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma refinedShutdown_act (k : Bool) : refinedShutdown.act k = .stop := rfl

/-- The refined successor's `¬push` cells. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma refinedShutdown_silent_cell (k : Bool) :
    refinedShutdown.pushᶜ.filter (fun ω => refinedShutdown.q ω = k) = pushEventᶜ.filter (fun ω => ω.2.2 = k) := rfl

/-- The P6 world at builder prior `ε`: sensor `(1/10, 9/10)`, successor signal `(1/5, 4/5)`.
Source: anticipatory.md P6 (script E). Kind: D. Fidelity: exact -/
noncomputable def p6World (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Distr (World × Bool × Bool) :=
  pushWorld ε (1 / 10) (9 / 10) (1 / 5) (4 / 5) hε mem_Icc_1_10 ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- `1/20 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_20 : (1 / 20 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- **T17(b) N+ (script E), `ε = 1/50`, blind**: refined `V(IN) = 437/500`, `V(SH) = 469/500`,
`Δ_C^succ = −8/125`.
Source: [[corr-wf14b-inventory]] 022 / anticipatory.md P6; anticipatory-final.md Statement 7(b)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem blind_witness_refined_50 :
    inValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4) refinedShutdown = 437 / 500 ∧
      shValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4) refinedShutdown = 469 / 500 ∧
      inValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4) refinedShutdown -
        shValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4) refinedShutdown = -(8 / 125) := by
  simp only [inValue, shValue, Content.silentListen, Content.listenValue, Content.forcedValue,
    Content.cellSum, refinedShutdown_cellOf, refinedShutdown_act, refinedShutdown_silent_cell, sup'_twoAct,
    Fintype.sum_bool, sum_pushCell, sum_pushEventc_filter]
  norm_num [p6World, pushWorld, sigRate, twoPress, pushU, twoValue]

/-- **T17(b) N+ (script E), `ε = 1/50`, blind, coarse**: `Δ_C^succ = −13/500`.
Source: [[corr-wf14b-inventory]] 022 / anticipatory.md P6
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem blind_witness_coarse_50 :
    inValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4) shutdownContent -
      shValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4) shutdownContent = -(13 / 500) := by
  simp only [inValue, shValue, Content.silentListen, Content.listenValue, Content.forcedValue,
    Content.cellSum, shutdownContent_cellOf, shutdownContent_act, shutdownContent_silent_cell, sup'_twoAct,
    Fintype.sum_unique, sum_pushEvent, sum_pushEventc]
  norm_num [p6World, pushWorld, sigRate, twoPress, pushU, twoValue]

/-- **T17(b) N+ (script E), `ε = 1/20`, blind**: refined `Δ_C^succ = −1/25`, coarse `0` — the
coarse successor (the builder's own information) is still indifferent while the refined one is
worth shielding.
Source: [[corr-wf14b-inventory]] 022 / anticipatory.md P6 ("At `ε = 1/20` the coarse successor … is still indifferent")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem blind_witness_20 :
    inValue (p6World (1 / 20) mem_Icc_1_20) (pushU 1 4) refinedShutdown -
        shValue (p6World (1 / 20) mem_Icc_1_20) (pushU 1 4) refinedShutdown = -(1 / 25) ∧
      inValue (p6World (1 / 20) mem_Icc_1_20) (pushU 1 4) shutdownContent -
        shValue (p6World (1 / 20) mem_Icc_1_20) (pushU 1 4) shutdownContent = 0 := by
  constructor
  · simp only [inValue, shValue, Content.silentListen, Content.listenValue, Content.forcedValue,
      Content.cellSum, refinedShutdown_cellOf, refinedShutdown_act, refinedShutdown_silent_cell, sup'_twoAct,
      Fintype.sum_bool, sum_pushCell, sum_pushEventc_filter]
    norm_num [p6World, pushWorld, sigRate, twoPress, pushU, twoValue]
  · simp only [inValue, shValue, Content.silentListen, Content.listenValue, Content.forcedValue,
      Content.cellSum, shutdownContent_cellOf, shutdownContent_act, shutdownContent_silent_cell, sup'_twoAct,
      Fintype.sum_unique, sum_pushEvent, sum_pushEventc]
    norm_num [p6World, pushWorld, sigRate, twoPress, pushU, twoValue]

end Blind

/-! ## Inclusion oversight -/

section Inclusion

variable {Ω K : Type} [Fintype Ω] [Fintype K] [DecidableEq Ω] [DecidableEq K]

/-- The overseers' cell sum on a general finite world: `∑_{f ω = k} P(ω) X(ω)`.
Source: [[corr-wf14-inventory]] 055 / joint-final.md P.1′ (generic form of `Cellwise.ruleSum`)
Kind: D
Fidelity: exact -/
noncomputable def ruleSumOn (P : Distr Ω) (X : Ω → ℝ) (f : Ω → K) (k : K) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => f ω = k), P.mass ω * X ω

/-- **The inclusion content**: overseers seeing `f ω` push (forced `stop`) iff their cell sum is
negative; the realized index is their cell.
Source: [[corr-wf14b-inventory]] 022 / anticipatory.md P6 ("INCLUSION oversight sees `(h, y')` and pushes iff `E[X∣h,y'] < 0`")
Kind: D
Fidelity: exact -/
noncomputable def inclusionContent (P : Distr Ω) (X : Ω → ℝ) (f : Ω → K) : Content Ω TwoAct K where
  push := univ.filter fun ω => ruleSumOn P X f (f ω) < 0
  q := f
  act := fun _ => .stop

/-- On a pushed cell the cell sum of continuing is the (negative) overseers' sum, and of stopping
`0`; on an unpushed index the cell is empty.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma inclusionContent_cellSum (P : Distr Ω) (X : Ω → ℝ) (f : Ω → K) (k : K) :
    (inclusionContent P X f).cellSum P (fun a ω => if a = .cont then X ω else 0) k .cont =
        (if ruleSumOn P X f k < 0 then ruleSumOn P X f k else 0) ∧
      (inclusionContent P X f).cellSum P (fun a ω => if a = .cont then X ω else 0) k .stop = 0 := by
  constructor
  · unfold Content.cellSum Content.cellOf inclusionContent
    simp only [if_true, filter_filter]
    split_ifs with hk
    · unfold ruleSumOn
      refine sum_congr ?_ fun _ _ => rfl
      ext ω; simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · intro h2; exact ⟨by rw [h2]; exact hk, h2⟩
    · refine sum_eq_zero fun ω hω => ?_
      simp only [mem_filter, mem_univ, true_and] at hω
      rw [hω.2] at hω; exact absurd hω.1 hk
  · simp [Content.cellSum]

/-- **T17(c): under inclusion the forced and listening values coincide** — on every pushed cell
the overseers' sum is negative, so `stop` is the cell maximiser (T3's mechanism composed with
T13(a)'s equality clause). Hence `Δ_C^succ = 0` for every prior.
Source: [[corr-wf14b-inventory]] 022 / anticipatory-final.md Statement 7(c) ("Under information inclusion `Δ_C^succ = 0` at every `ε`")
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem inclusion_forced_eq_listen (P : Distr Ω) (X : Ω → ℝ) (f : Ω → K) :
    (inclusionContent P X f).forcedValue P (fun a ω => if a = .cont then X ω else 0) =
      (inclusionContent P X f).listenValue P (fun a ω => if a = .cont then X ω else 0) := by
  rw [Content.forcedValue_eq_listenValue_iff]
  intro k
  obtain ⟨hc, hs⟩ := inclusionContent_cellSum P X f k
  have hact : (inclusionContent P X f).act k = .stop := rfl
  rw [sup'_twoAct, hc, hact, hs]
  split_ifs with hk
  · rw [max_eq_right hk.le]
  · rw [max_self]

/-- **T17(c), the successor margin vanishes under inclusion.**
Source: [[corr-wf14b-inventory]] 022 / anticipatory-final.md Statement 7(c)
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem inclusion_succ_margin_zero (P : Distr Ω) (X : Ω → ℝ) (f : Ω → K) :
    inValue P (fun a ω => if a = .cont then X ω else 0) (inclusionContent P X f) -
      shValue P (fun a ω => if a = .cont then X ω else 0) (inclusionContent P X f) = 0 := by
  rw [succ_margin_eq, inclusion_forced_eq_listen, sub_self]

end Inclusion

/-- The push-world's `pushU c h` is the `if a = cont then X else 0` form. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pushU_eq (c h : ℝ) : pushU c h = fun a ω => if a = .cont then twoValue c h .cont ω.1 else 0 := by
  funext a ω; cases a <;> simp [pushU, twoValue]

/-- **T17(c) N+ (script E), `ε = 1/50`, inclusion**: the refined successor's overseers see
`(h, y')`; `V(IN) = V(SH) = 469/500`.
Source: [[corr-wf14b-inventory]] 022 / anticipatory.md P6 (INCL rows)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem inclusion_witness_50 :
    inValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4)
        (inclusionContent (p6World (1 / 50) mem_Icc_1_50) (fun ω => twoValue 1 4 .cont ω.1) (fun ω => ω.2)) =
      469 / 500 ∧
    shValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4)
        (inclusionContent (p6World (1 / 50) mem_Icc_1_50) (fun ω => twoValue 1 4 .cont ω.1) (fun ω => ω.2)) =
      469 / 500 := by
  have hrule : ∀ k : Bool × Bool, ruleSumOn (p6World (1 / 50) mem_Icc_1_50) (fun ω => twoValue 1 4 .cont ω.1)
      (fun ω => ω.2) k = if k = (true, true) then -(19 / 500) else
        (if k = (true, false) then 32 / 500 else (if k = (false, true) then 17 / 100 else 176 / 250)) := by
    intro k
    obtain ⟨b₁, b₂⟩ := k
    simp only [ruleSumOn, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq]
    cases b₁ <;> cases b₂ <;> simp [p6World, pushWorld, sigRate, twoPress, twoValue] <;> norm_num
  simp only [inValue, shValue, Content.silentListen, Content.listenValue, Content.forcedValue,
    Content.cellSum, Content.cellOf, inclusionContent, sup'_twoAct, Finset.sum_filter, Finset.filter_filter,
    Finset.compl_filter, Finset.compl_univ, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq, hrule]
  simp [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, World.sum_eq, hrule, p6World, pushWorld,
    sigRate, twoPress, pushU, twoValue]
  norm_num

/-- **The disclosing in-channel successor attains the shielded value at zero cost**:
`V(refined, IN, inclusion) = 469/500 = V(refined, SH, blind)` at `ε = 1/50`.
Source: [[corr-wf14b-inventory]] 022 / anticipatory-final.md Statement 7(b) ("attains the shielded value in-channel at zero cost")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem disclosing_attains :
    inValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4)
        (inclusionContent (p6World (1 / 50) mem_Icc_1_50) (fun ω => twoValue 1 4 .cont ω.1) (fun ω => ω.2)) =
      shValue (p6World (1 / 50) mem_Icc_1_50) (pushU 1 4) refinedShutdown := by
  rw [inclusion_witness_50.1, blind_witness_refined_50.2.1]

end Cleanroom.Corrigibility.CorrJointProcess
