import Cleanroom.Found.CorrThreeStep.Setting
import Cleanroom.Corrigibility.CorrThreeStepFacts.Partition
import Cleanroom.Corrigibility.CorrCautionPower.Setting

/-!
# `corr-caution-power` — T9: option value cuts the other way (Turner C4)

Over `corr-three-step`'s Setting S (`ThreeStep Ω A₁ A₂`, shutdown menu `Sh`, continue menu
`Shᶜ`), add a **second channel** `E` (`Channel Ω E`: likelihoods `chan ω e ∈ [0, 1]` summing to
`1`). Objects at a first action `a` and observation index `o₀` (immaterial under A1):

* `informedContinue` — `∑_e max_{b ∈ Shᶜ} ∑_ω μ(ω) chan(ω, e) V(b, ω)`, the value of
  continuing and deciding after `E`;
* `priorContinue` — `max_{b ∈ Shᶜ} E_μ[V(b)]`; `stopValue` — `max_{b ∈ Sh} E_μ[V(b)]`;
* `optionValue := informedContinue − priorContinue` — the value of information of `E` on the
  continue menu ("stay alive to keep learning `ω`").

* **(a) Decomposition** `informed_sub_stop_decomp`: `informed − stop = (act-value − stop) +
  option value` — C4's identity, by definition.
* **(b) Nonnegativity** `optionValue_nonneg`: Good's theorem, finite form
  (`∑_e p_e max_b x_{e,b} ≥ max_b ∑_e p_e x_{e,b}`). Proved directly (ten lines); the bridge
  to `corr-three-step-facts`'s `priorBest_le_partValue` on the joint `Ω × E` is
  `optionValue_eq_partValue_sub` (the sibling's object), so the duplication is disclosed and
  checked against the sibling.
* **(c1) Refinement-monotone** `optionValue_coarsen_le`: a deterministic coarsening `E → E'` of
  the channel has no larger option value — the reading under which C4's "grows with capability"
  is true. **(c2)** menu-monotonicity is false (the sibling `corr-power-channel`'s "EVPI not
  monotone in the option set", corr-wf14-104): recorded in the findings, not duplicated.

Sources: [[corr-wf13-2-inventory]] 2-080 → `critique/turner.md` C4 (l. 81), Objection 1 (l. 159);
Turner's Corollary 6.14 is an MDP statement with no counterpart here (not a target).
-/

namespace Cleanroom.Corrigibility.CorrCautionPower

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect expect_const

/-- **A second channel:** an observation type `E` with likelihoods `chan ω e ∈ [0, 1]` summing to
`1` in each world.
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81, "gather more evidence `E`")
Kind: D
Fidelity: exact -/
structure Channel (Ω E : Type*) [Fintype E] where
  /-- The likelihood `P(e | ω)`. -/
  chan : Ω → E → ℝ
  nonneg : ∀ ω e, 0 ≤ chan ω e
  sum_eq_one : ∀ ω, ∑ e, chan ω e = 1

section OptionValue

variable {Ω A₁ A₂ E : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] [Fintype E]
variable (S : ThreeStep Ω A₁ A₂) (C : Channel Ω E) (a : A₁) (o₀ : Obs)

/-- The `e`-weighted value of the continue action `b`: `∑_ω μ(ω) chan(ω, e) V(b, ω)` (product
form, event mass included).
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81)
Kind: D
Fidelity: exact -/
noncomputable def chanValue (e : E) (b : A₂) : ℝ :=
  ∑ ω, (S.μ a).mass ω * C.chan ω e * S.V a o₀ b ω

/-- **The informed continue-value** `∑_e max_{b ∈ Shᶜ} ∑_ω μ(ω) chan(ω, e) V(b, ω)`.
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81, "option value of future learning about `ω`")
Kind: D
Fidelity: exact -/
noncomputable def informedContinue : ℝ :=
  ∑ e, S.Shᶜ.sup' S.Sh_compl_nonempty (fun b => chanValue S C a o₀ e b)

/-- **The prior continue-value** `max_{b ∈ Shᶜ} E_μ[V(b)]` (the value of acting on current
`ω`-beliefs).
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81, "value of acting on current `ω`-beliefs")
Kind: D
Fidelity: exact -/
noncomputable def priorContinue : ℝ :=
  S.Shᶜ.sup' S.Sh_compl_nonempty (fun b => expect (S.μ a) (S.V a o₀ b))

/-- **The shutdown value** `max_{b ∈ Sh} E_μ[V(b)]`.
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81, "value of shutdown")
Kind: D
Fidelity: exact -/
noncomputable def stopValue : ℝ := S.Sh.sup' S.Sh_nonempty (fun b => expect (S.μ a) (S.V a o₀ b))

/-- **The option value** of the channel `E` on the continue menu: informed minus prior.
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81)
Kind: D
Fidelity: exact -/
noncomputable def optionValue : ℝ := informedContinue S C a o₀ - priorContinue S a o₀

/-- **T9(a), C4's decomposition:** `informed − stop = (act-value − stop) + option value`. Holds
by definition of `optionValue`; stated so the identity Turner writes is on record.
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81, "Decompose `X` as …")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem informed_sub_stop_decomp :
    informedContinue S C a o₀ - stopValue S a o₀
      = (priorContinue S a o₀ - stopValue S a o₀) + optionValue S C a o₀ := by
  unfold optionValue; ring

/-- The prior value of `b` is the sum over `e` of its `e`-weighted values (`∑_e chan = 1`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_eq_sum_chanValue (b : A₂) :
    expect (S.μ a) (S.V a o₀ b) = ∑ e, chanValue S C a o₀ e b := by
  unfold expect chanValue
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  rw [← sum_mul, ← mul_sum, C.sum_eq_one, mul_one]

/-- **T9(b), Good's theorem (finite form):** `0 ≤ optionValue` — the value of learning `ω` by any
channel before continuing is nonnegative; "stay alive to keep learning" is on the *other* side
of the below-threshold inequality from where the thesis puts it.
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81, "The middle term is nonnegative by the same theorem"); corr-core-007 (Good's theorem)
Kind: P
Fidelity: exact (finite; duplicates `corr-three-step-facts`' `priorBest_le_partValue` on a stochastic channel — see `optionValue_eq_partValue_sub`)
Hyps: (a) only -/
theorem optionValue_nonneg : 0 ≤ optionValue S C a o₀ := by
  unfold optionValue informedContinue priorContinue
  rw [sub_nonneg]
  refine sup'_le _ _ fun b hb => ?_
  rw [expect_eq_sum_chanValue S C a o₀ b]
  exact sum_le_sum fun e _ => le_sup' (fun b => chanValue S C a o₀ e b) hb

/-! ### The bridge to `corr-three-step-facts`' Good's theorem on a partition -/

/-- The joint distribution of `(ω, e)` under the prior and the channel.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def jointChannel : Distr (Ω × E) where
  mass p := (S.μ a).mass p.1 * C.chan p.1 p.2
  nonneg p := mul_nonneg ((S.μ a).nonneg _) (C.nonneg _ _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, C.sum_eq_one, mul_one, (S.μ a).sum_eq_one]

/-- The continue menu as a type. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
abbrev ContMenu : Type _ := ↥(S.Shᶜ)

instance : Nonempty (ContMenu S) := S.Sh_compl_nonempty.to_subtype

/-- The payoff on the joint, indexed by the continue menu.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def jointV : ContMenu S → Ω × E → ℝ := fun b p => S.V a o₀ b p.1

/-- The `sup'` over the coerced menu equals the `sup'` over the finset.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sup'_contMenu (f : A₂ → ℝ) :
    (univ : Finset (ContMenu S)).sup' univ_nonempty (fun b => f b) = S.Shᶜ.sup' S.Sh_compl_nonempty f := by
  apply le_antisymm
  · exact sup'_le _ _ fun b _ => le_sup' f b.2
  · exact sup'_le _ _ fun b hb => le_sup' (fun b : ContMenu S => f b) (mem_univ ⟨b, hb⟩)

/-- A cell sum of the sibling's partition by `snd` on the joint is the `e`-weighted value.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellSum_joint_snd [DecidableEq E] (e : E) (b : ContMenu S) :
    Cleanroom.Corrigibility.CorrThreeStepFacts.cellSum (jointChannel S C a) (jointV S a o₀) Prod.snd e b
      = chanValue S C a o₀ e b := by
  unfold Cleanroom.Corrigibility.CorrThreeStepFacts.cellSum Cleanroom.Corrigibility.CorrThreeStepFacts.cell
    chanValue
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  simp only [jointChannel, jointV, sum_ite_eq', mem_univ, if_true]

/-- **The bridge:** the option value is the sibling's `partValue − priorBest` on the joint
`Ω × E` partitioned by `e`, with the menu `Shᶜ`.
Source: [[corr-wf13-2-inventory]] 2-080; corr-core-007 (the sibling's Good's theorem)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem optionValue_eq_partValue_sub [DecidableEq E] :
    optionValue S C a o₀
      = Cleanroom.Corrigibility.CorrThreeStepFacts.partValue (jointChannel S C a) (jointV S a o₀) Prod.snd
        - Cleanroom.Corrigibility.CorrThreeStepFacts.priorBest (jointChannel S C a) (jointV S a o₀) := by
  unfold optionValue informedContinue priorContinue
    Cleanroom.Corrigibility.CorrThreeStepFacts.partValue Cleanroom.Corrigibility.CorrThreeStepFacts.priorBest
  congr 1
  · refine sum_congr rfl fun e _ => ?_
    rw [← sup'_contMenu S (fun b => chanValue S C a o₀ e b)]
    congr 1; funext b; exact (cellSum_joint_snd S C a o₀ e b).symm
  · rw [← sup'_contMenu S (fun b => expect (S.μ a) (S.V a o₀ b))]
    congr 1; funext b
    rw [Cleanroom.Corrigibility.CorrThreeStepFacts.expect_eq_sum_cellSum _ _ Prod.snd,
      expect_eq_sum_chanValue S C a o₀]
    exact sum_congr rfl fun e _ => (cellSum_joint_snd S C a o₀ e b).symm

/-- **T9(b) re-derived from the sibling:** nonnegativity via `priorBest_le_partValue`.
Source: corr-core-007 (Good's theorem) via `corr-three-step-facts`
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem optionValue_nonneg' [DecidableEq E] : 0 ≤ optionValue S C a o₀ := by
  rw [optionValue_eq_partValue_sub, sub_nonneg]
  exact Cleanroom.Corrigibility.CorrThreeStepFacts.priorBest_le_partValue _ _ _

/-! ### (c1) Refinement-monotone -/

/-- **A deterministic coarsening of a channel** along `f : E → E'`: `chan' ω e' = ∑_{f e = e'} chan ω e`.
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81, "grows with … capability")
Kind: D
Fidelity: exact -/
noncomputable def Channel.coarsen {E' : Type*} [Fintype E'] [DecidableEq E'] (f : E → E') :
    Channel Ω E' where
  chan ω e' := ∑ e ∈ univ.filter (f · = e'), C.chan ω e
  nonneg ω e' := sum_nonneg fun e _ => C.nonneg ω e
  sum_eq_one ω := by rw [sum_fiberwise univ f (C.chan ω)]; exact C.sum_eq_one ω

/-- The `sup'` of a sum is at most the sum of the `sup'`s (over the continue menu).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sup'_sum_le_cont {ι : Type*} (s : Finset ι) (g : ι → A₂ → ℝ) :
    S.Shᶜ.sup' S.Sh_compl_nonempty (fun b => ∑ i ∈ s, g i b)
      ≤ ∑ i ∈ s, S.Shᶜ.sup' S.Sh_compl_nonempty (fun b => g i b) :=
  sup'_le _ _ fun b hb => sum_le_sum fun i _ => le_sup' (fun b => g i b) hb

/-- **T9(c1), refinement-monotone:** a coarsened channel has no larger informed value, hence no
larger option value: `optionValue (coarsen f C) ≤ optionValue C`. This is the reading of
"option value grows with capability" under which C4's claim is true (finer channel, more
option value); the menu-monotone reading is false (findings, sibling `corr-power-channel`).
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81), Objection 1 (l. 159)
Kind: P
Fidelity: exact (reading (c1))
Hyps: (a) only -/
theorem optionValue_coarsen_le {E' : Type*} [Fintype E'] [DecidableEq E'] (f : E → E') :
    optionValue S (C.coarsen f) a o₀ ≤ optionValue S C a o₀ := by
  unfold optionValue
  refine sub_le_sub_right ?_ _
  unfold informedContinue
  have hcell : ∀ e' b, chanValue S (C.coarsen f) a o₀ e' b
      = ∑ e ∈ univ.filter (f · = e'), chanValue S C a o₀ e b := by
    intro e' b
    unfold chanValue Channel.coarsen
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
  calc ∑ e', S.Shᶜ.sup' S.Sh_compl_nonempty (fun b => chanValue S (C.coarsen f) a o₀ e' b)
      = ∑ e', S.Shᶜ.sup' S.Sh_compl_nonempty
          (fun b => ∑ e ∈ univ.filter (f · = e'), chanValue S C a o₀ e b) := by
        refine sum_congr rfl fun e' _ => ?_
        congr 1; funext b; exact hcell e' b
    _ ≤ ∑ e', ∑ e ∈ univ.filter (f · = e'),
          S.Shᶜ.sup' S.Sh_compl_nonempty (fun b => chanValue S C a o₀ e b) :=
        sum_le_sum fun e' _ => sup'_sum_le_cont S _ _
    _ = ∑ e, S.Shᶜ.sup' S.Sh_compl_nonempty (fun b => chanValue S C a o₀ e b) :=
        sum_fiberwise univ f _

end OptionValue

/-! ### A non-degenerate instance: `0 < optionValue`

The parent's `twoState` has `Shᶜ = {cont}`, a singleton, on which the option value of *every*
channel is `0` (audit r1, `OptionValueTwoState.lean`). The smallest instance with content: a
two-element continue menu whose two actions are optimal under different worlds, and a perfect
channel. -/

section ThreeAct

/-- The three-action value: `0` (stop) is worth `0`; `1` is worth `1` when right, `0` when
wrong; `2` the reverse.
Source: none: infrastructure (witness for T9(b))
Kind: D
Fidelity: n/a -/
def threeVal : Fin 3 → World → ℝ :=
  ![fun _ => 0, fun ω => match ω with | .right => 1 | .wrong => 0,
    fun ω => match ω with | .right => 0 | .wrong => 1]

/-- **A three-action instance of Setting S** with a two-element continue menu: `A₂ = Fin 3`,
`Sh = {0}`, `Shᶜ = {1, 2}`; `Ω = World` with `μ(wrong) = ε`; the parent's sensor `(α, β)`;
`V = threeVal` (A1 by construction).
Source: none: infrastructure (witness for T9(b))
Kind: D
Fidelity: n/a -/
noncomputable def threeAct (ε α β : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) : ThreeStep World Unit (Fin 3) where
  Sh := {0}
  Sh_nonempty := ⟨0, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨1, by simp⟩
  μ := fun _ => twoPoint ε hε
  press := fun _ => twoPress α β
  press_nonneg := fun _ ω => match ω with
    | .right => hα.1
    | .wrong => hβ.1
  press_le_one := fun _ ω => match ω with
    | .right => hα.2
    | .wrong => hβ.2
  V := fun _ _ b ω => threeVal b ω

/-- **The perfect channel** on `World`: `E = World`, `chan ω e = 1[ω = e]`.
Source: none: infrastructure (witness for T9(b))
Kind: D
Fidelity: n/a -/
noncomputable def perfectChannel : Channel World World where
  chan ω e := if ω = e then 1 else 0
  nonneg _ _ := by split_ifs <;> norm_num
  sum_eq_one ω := by rw [World.sum_eq]; cases ω <;> simp

/-- The four values of `threeVal` on the continue menu.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma threeVal_vals : threeVal 1 .right = 1 ∧ threeVal 2 .right = 0 ∧
    threeVal 1 .wrong = 0 ∧ threeVal 2 .wrong = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [threeVal]

variable (ε α β : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The `sup'` over the continue menu `{1, 2}` is the `max` of the two values.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma threeAct_sup' (f : Fin 3 → ℝ) :
    (threeAct ε α β hε hα hβ).Shᶜ.sup' (threeAct ε α β hε hα hβ).Sh_compl_nonempty f
      = max (f 1) (f 2) := by
  apply le_antisymm
  · refine sup'_le _ _ fun b hb => ?_
    simp only [threeAct, mem_compl, mem_singleton] at hb
    fin_cases b
    · exact absurd rfl hb
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_sup' f (by simp [threeAct])) (le_sup' f (by simp [threeAct]))

/-- The channel value under the perfect channel is `μ(e) · V(b, e)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma chanValue_threeAct (e : World) (b : Fin 3) :
    chanValue (threeAct ε α β hε hα hβ) perfectChannel () .silent e b
      = (twoPoint ε hε).mass e * threeVal b e := by
  unfold chanValue
  rw [World.sum_eq]
  cases e <;> simp [threeAct, perfectChannel]

/-- **T9(b), a non-degenerate instance:** on `threeAct` with the perfect channel the option value
is `1 − max{1 − ε, ε} = min{ε, 1 − ε}` — the informed agent picks the right action in every world
(value `1`), the uninformed one the more likely world's action.
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81); witness for `optionValue_nonneg`
Kind: N+
Fidelity: exact (an instance)
Hyps: none -/
theorem optionValue_threeAct :
    optionValue (threeAct ε α β hε hα hβ) perfectChannel () .silent = 1 - max (1 - ε) ε := by
  unfold optionValue informedContinue priorContinue
  rw [World.sum_eq]
  simp only [threeAct_sup', chanValue_threeAct]
  have h1 : expect ((threeAct ε α β hε hα hβ).μ ()) ((threeAct ε α β hε hα hβ).V () .silent 1)
      = 1 - ε := by
    unfold expect; rw [World.sum_eq]; simp [threeAct, threeVal]
  have h2 : expect ((threeAct ε α β hε hα hβ).μ ()) ((threeAct ε α β hε hα hβ).V () .silent 2)
      = ε := by
    unfold expect; rw [World.sum_eq]; simp [threeAct, threeVal]
  rw [h1, h2]
  obtain ⟨v1r, v2r, v1w, v2w⟩ := threeVal_vals
  rw [v1r, v2r, v1w, v2w]
  simp only [twoPoint_right, twoPoint_wrong, mul_one, mul_zero]
  rw [max_eq_left (by linarith [hε.2] : (0 : ℝ) ≤ 1 - ε), max_eq_right hε.1]
  ring

/-- **`0 < optionValue` on `threeAct`** for `0 < ε < 1`: the witness the ledger's T9 row lacked
(audit r1 §3.1).
Source: [[corr-wf13-2-inventory]] 2-080 / turner.md C4 (l. 81); witness for `optionValue_nonneg`
Kind: N+
Fidelity: exact (an instance)
Hyps: none -/
theorem optionValue_threeAct_pos (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < optionValue (threeAct ε α β hε hα hβ) perfectChannel () .silent := by
  rw [optionValue_threeAct]
  rcases le_total (1 - ε) ε with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

end ThreeAct

end Cleanroom.Corrigibility.CorrCautionPower
