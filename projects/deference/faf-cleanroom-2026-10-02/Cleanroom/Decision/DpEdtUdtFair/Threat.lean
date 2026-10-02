import Cleanroom.Decision.DpEdtUdtFair.FairWitnesses
import Cleanroom.Decision.DpCalibration.Examples

/-!
# The threat tree (T8) and the no-trembles row (T7(i)): every untrembled sense approves a
dominated off-path profile on `𝔉`

On `twoPoint r₀ r₁ r₂` with `(a, y)` (`outY`), `p2` is off-path (`ν(O_{p2}) = 0`), so:

* **strict-OC EDT** with a *stipulated* state at the null observation approves `(a, y)`
  (`outY_strictOC_tEdt`): the state at `p1` is the strictly calibrated one, the state at `p2` is the
  source's fantasy state (`P` half-half on `inX, inY`, `V(x) = 0 < 5 = V(y)`) — built here as the
  calibrated state of a different problem, so it is a genuine `State`;
* **masked EDT** (Definition 9, LF variant, vacuity reading) approves `(a, y)` when `r₂ ≤ r₀`
  (`outY_masked_tEdt`): at `p1` the self-model `(½, y)` realizes `⊤` and sees `V(in) = r₂ ≤ r₀ =
  V(out)`; at `p2` no local self-model realizes `O_{p2}`;
* **Definition 22 (pure and mixed), Theorem 1 and Theorem 2** approve `(a, y)` on the threat tree
  (`threat_outY_coherent_thm1_thm2`), Theorem 2 vacuously at `p2` (`μ(occ p2) = 0`);
* **D2 rejects it** and it is not optimal (`threat_outY_not_eventTremble`, `FairWitnesses.lean`).

`threat_outY_untrembled` is the refutation row for identity Dead 1 (the quoted sentence and
reading are in its docstring); `fantasy_outY_untrembled` and `twoPoint340_outY_untrembled` are
T7(i)'s two instances (the imperfect equilibrium, and D3's 5-node sanity instance).

Limit-state EDT (D1) at the pinned null-observation state is shipped in `LimitState.lean`
(`outY_limitStateEdt`, every payoff triple; the rows with all senses are
`threat_outY_untrembled_all` and `fantasy_outY_untrembled_all` there).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

/-! ### Statistics on `twoPoint` -/

section stats

variable (r₀ r₁ r₂ p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)

/-- `ν` on `twoPoint` under `proc2 p q`. Source: none: infrastructure. Kind: L -/
theorem twoPoint_nu (X : Finset TwoW) :
    nu (proc2 p q hp0 hp1 hq0 hq1) (twoPoint r₀ r₁ r₂) X =
      (if TwoW.out ∈ X then p else 0) + (if TwoW.inX ∈ X then (1 - p) * q else 0) +
        (if TwoW.inY ∈ X then (1 - p) * (1 - q) else 0) := by
  rw [nu_eq_sum, twoPoint_sum]
  simp [twoPoint, leafLaw_decision, world_decision, proc2, FinDistr.act2]

/-- `𝔼[r 1_X]` on `twoPoint` under `proc2 p q`. Source: none: infrastructure. Kind: L -/
theorem twoPoint_paySum (X : Finset TwoW) :
    paySum (proc2 p q hp0 hp1 hq0 hq1) (twoPoint r₀ r₁ r₂) X =
      (if TwoW.out ∈ X then p * r₀ else 0) + (if TwoW.inX ∈ X then (1 - p) * q * r₁ else 0) +
        (if TwoW.inY ∈ X then (1 - p) * (1 - q) * r₂ else 0) := by
  rw [paySum_eq_sum_ite, twoPoint_sum]
  simp [twoPoint, leafLaw_decision, world_decision, payoff_decision, proc2, FinDistr.act2]

/-- Under `(a, y)`: `ν(O_{p1}) = 1`, `ν(O_{p2}) = 0`. Source: `fair-repair.md` §3.2. Kind: L -/
theorem outY_nu_obs :
    nu outY (twoPoint r₀ r₁ r₂) (twoObs .p1) = 1 ∧ nu outY (twoPoint r₀ r₁ r₂) (twoObs .p2) = 0 := by
  constructor <;> (show nu (proc2 1 0 _ _ _ _) _ _ = _; rw [twoPoint_nu]; simp [twoObs])

/-- No point-deviation of `(a, y)` at `p2` realizes `O_{p2}` (decided upstream by `out`).
Source: `calibration.md` CA-1′(iii); `identity.md` Open 7 ("local masking")
Kind: L -/
theorem outY_deviate_p2_nu_zero (m : FinDistr ℚ Act2) :
    nu (outY.deviate .p2 m) (twoPoint r₀ r₁ r₂) (twoObs .p2) = 0 := by
  rw [FinDistr.eq_act2 m]
  show nu ((proc2 1 0 _ _ _ _).deviate .p2 _) _ _ = _
  rw [proc2_deviate_p2, twoPoint_nu]
  simp [twoObs]

end stats

/-! ### The states -/

section states

/-- `ν(O_{p2}) = 1 > 0` on the fantasy problem `(0; 0, 5)` under `(in, ½)`.
Source: none: infrastructure
Kind: L -/
theorem fantasyProblem_nu_pos :
    0 < nu (proc2 0 (1 / 2) le_rfl zero_le_one (by norm_num) (by norm_num)) (twoPoint 0 0 5)
      (twoObs .p2) := by
  rw [twoPoint_nu]; simp [twoObs]

/-- **The fantasy state** at the null observation `O_{p2}` (fair-repair §3.2's "stipulate
`P_{s₂}` half-half on fantasy worlds with `V_{s₂}(y) = 5 > 0 = V_{s₂}(x)`"): built as the strictly
calibrated state of the *different* problem `(0; 0, 5)` under `(in, ½)`, so that it is a genuine
`State` (averaging axiom) with exactly the source's numbers.
Source: `fair-repair.md` §3.2 ("Without trembles"); `adversary-repair.md` A.1 ("the beliefs need
not even be fantasy")
Kind: D -/
noncomputable def fantasyState : State TwoW ℚ :=
  calibratedState (proc2 0 (1 / 2) le_rfl zero_le_one (by norm_num) (by norm_num)) (twoPoint 0 0 5)
    (twoObs .p2) fantasyProblem_nu_pos

/-- The fantasy state's numbers: `P(x) = P(y) = ½`, `V(x) = 0`, `V(y) = 5`.
Source: `fair-repair.md` §3.2
Kind: L -/
theorem fantasyState_numbers :
    fantasyState.pr (twoActEv .p2 .a) = 1 / 2 ∧ fantasyState.pr (twoActEv .p2 .b) = 1 / 2 ∧
    fantasyState.V (twoActEv .p2 .a) = 0 ∧ fantasyState.V (twoActEv .p2 .b) = 5 := by
  unfold fantasyState
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · first
      | (rw [calibratedState_pr, twoPoint_nu, twoPoint_nu])
      | (rw [calibratedState_V, twoPoint_paySum, twoPoint_nu])
    simp [twoActEv, twoObs]
    all_goals first | ring | field_simp | norm_num

variable (r₀ r₁ r₂ : ℚ)

/-- The strictly calibrated state of `(a, y)` at `p1` (`O = ⊤`).
Source: [[decision-problems-v2]] Definition 8
Kind: D -/
noncomputable def outYState : State TwoW ℚ :=
  calibratedState outY (twoPoint r₀ r₁ r₂) (twoObs .p1) (by rw [(outY_nu_obs r₀ r₁ r₂).1]; exact one_pos)

/-- **The strict-sense state assignment**: calibrated at `p1`, the fantasy state at the null `p2`.
Source: `fair-repair.md` §3.2
Kind: D -/
noncomputable def sStrict : Pt2 → State TwoW ℚ
  | .p1 => outYState r₀ r₁ r₂
  | .p2 => fantasyState

/-- The uniform mixed action on `Act2` is `(½, ½)`. Source: none: infrastructure. Kind: L -/
theorem uniform_eq_act2_half :
    (FinDistr.uniform : FinDistr ℚ Act2) = FinDistr.act2 (1 / 2) (by norm_num) (by norm_num) := by
  apply FinDistr.ext'
  intro x
  cases x <;> simp [FinDistr.uniform_w, FinDistr.act2, Fintype.card, Act2.univ_eq] <;> norm_num

/-- `(a, y)[p1 ↦ uniform] = (½, y)`. Source: none: infrastructure. Kind: L -/
theorem outY_deviate_p1_uniform :
    outY.deviate .p1 FinDistr.uniform =
      proc2 (1 / 2) 0 (by norm_num) (by norm_num) le_rfl zero_le_one := by
  rw [uniform_eq_act2_half]
  show (proc2 1 0 _ _ _ _).deviate .p1 _ = _
  rw [proc2_deviate_p1]

/-- `ν(⊤) = 1` under the self-model `(½, y)`. Source: none: infrastructure. Kind: L -/
theorem half_y_nu_obs_pos :
    0 < nu (proc2 (1 / 2) 0 (by norm_num) (by norm_num) le_rfl zero_le_one) (twoPoint r₀ r₁ r₂)
      (twoObs .p1) := by
  rw [twoPoint_nu]; simp [twoObs]

/-- The masked state at `p1`: strictly calibrated under the local full-support self-model `(½, y)`.
Source: [[decision-problems-v2]] Definition 9 (LF)
Kind: D -/
noncomputable def maskedState : State TwoW ℚ :=
  calibratedState (proc2 (1 / 2) 0 (by norm_num) (by norm_num) le_rfl zero_le_one)
    (twoPoint r₀ r₁ r₂) (twoObs .p1) (half_y_nu_obs_pos r₀ r₁ r₂)

/-- **The masked-sense state assignment**: masked at `p1`, the fantasy state at the null `p2`.
Source: `identity.md` ID-22 (M0) ("masked EDT (Def-9 vacuity reading, local masking)")
Kind: D -/
noncomputable def sMasked : Pt2 → State TwoW ℚ
  | .p1 => maskedState r₀ r₁ r₂
  | .p2 => fantasyState

end states

/-! ### Strict-OC EDT approves `(a, y)` with the fantasy state -/

section strict

variable (r₀ r₁ r₂ : ℚ)

/-- `(a, y)` is strictly observation-calibrated with `sStrict`: at `p1` by construction, at `p2`
vacuously (`ν(O_{p2}) = 0`, Definition 8's parenthetical).
Source: `fair-repair.md` §3.2 ("`ν(O_2) = 0`, so `d_2`'s state is unconstrained (Definition 8's
parenthetical)")
Kind: P -/
theorem outY_strictOC : StrictOC (sStrict r₀ r₁ r₂) twoObs outY (twoPoint r₀ r₁ r₂) := by
  intro d _ hpos
  cases d
  · exact strictClausesAt_calibratedState twoObs outY (twoPoint r₀ r₁ r₂) (sStrict r₀ r₁ r₂) .p1
      hpos rfl
  · rw [(outY_nu_obs r₀ r₁ r₂).2] at hpos
    exact absurd hpos (lt_irrefl 0)

/-- `A_{p1}^+ = {out}` for the strict state of `(a, y)`.
Source: `fair-repair.md` §3.2 ("at `d₁` calibration gives `A^+_{d₁} = {out}`")
Kind: L -/
theorem outY_aPlus_p1 : APlus (sStrict r₀ r₁ r₂) twoActEv .p1 = {.a} := by
  have hpr : ∀ x, (sStrict r₀ r₁ r₂ .p1).pr (twoActEv .p1 x) = if x = .a then 1 else 0 := by
    intro x
    show (outYState r₀ r₁ r₂).pr _ = _
    unfold outYState
    rw [calibratedState_pr, (outY_nu_obs r₀ r₁ r₂).1]
    show nu (proc2 1 0 _ _ _ _) _ _ / 1 = _
    rw [twoPoint_nu]
    cases x <;> simp [twoActEv, twoObs]
  ext x
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hpr]
  cases x <;> simp

/-- `A_{p2}^+ = {x, y}` for the fantasy state.
Source: `fair-repair.md` §3.2
Kind: L -/
theorem fantasy_aPlus_p2 (s : Pt2 → State TwoW ℚ) (hs : s .p2 = fantasyState) :
    APlus s twoActEv .p2 = Finset.univ := by
  obtain ⟨h1, h2, -, -⟩ := fantasyState_numbers
  ext x
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, hs, iff_true]
  cases x
  · rw [h1]; norm_num
  · rw [h2]; norm_num

/-- **`T_EDT` holds for `(a, y)` with `sStrict`**: at `p1`, `A^+ = {out} ∋ out`; at `p2` the
fantasy state prefers `y` (`5 > 0`).
Source: `fair-repair.md` §3.2 ("EDT approves out … `(out, y)` is strictly-calibrated-EDT-consistent")
Kind: P -/
theorem outY_tEdt : TEdt (sStrict r₀ r₁ r₂) twoActEv outY (twoPoint r₀ r₁ r₂) := by
  intro d _ _ a ha
  cases d
  · cases a <;> simp [outY, proc2, FinDistr.act2] at ha
    rw [mem_argmaxPlus, outY_aPlus_p1]
    simp
  · cases a <;> simp [outY, proc2, FinDistr.act2] at ha
    obtain ⟨-, -, h3, h4⟩ := fantasyState_numbers
    rw [mem_argmaxPlus, fantasy_aPlus_p2 (sStrict r₀ r₁ r₂) rfl]
    refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
    show fantasyState.V _ ≤ fantasyState.V _
    cases b
    · rw [h3, h4]; norm_num
    · exact le_rfl

/-- **Strict-OC EDT approves `(a, y)` on every `twoPoint` tree** with a stipulated state at the
null observation (the imperfect equilibrium): for every payoff triple.
Source: `fair-repair.md` §3.2; `identity.md` ID-22 (M0) ("strict-OC EDT (Def 8's null-observation
parenthetical)")
Kind: P
Fidelity: exact (the source's numbers `P = ½/½`, `V(y) = 5 > 0 = V(x)` at `p2`)
Hyps: (a) all -/
theorem outY_strictOC_tEdt :
    ∃ s : Pt2 → State TwoW ℚ,
      StrictOC s twoObs outY (twoPoint r₀ r₁ r₂) ∧ TEdt s twoActEv outY (twoPoint r₀ r₁ r₂) :=
  ⟨sStrict r₀ r₁ r₂, outY_strictOC r₀ r₁ r₂, outY_tEdt r₀ r₁ r₂⟩

end strict

/-! ### Masked EDT (LF, vacuity) approves `(a, y)` when `r₂ ≤ r₀` -/

section masked

variable (r₀ r₁ r₂ : ℚ)

/-- `(a, y)` is masked-calibrated (LF, vacuity) with `sMasked`: at `p1` the self-model `(½, y)`
realizes `⊤`; at `p2` no local self-model realizes `O_{p2}`.
Source: [[decision-problems-v2]] Definition 9 with A5; `identity.md` Open 7 (local masking)
Kind: P -/
theorem outY_maskedOC : MaskedOC (sMasked r₀ r₁ r₂) twoObs outY (twoPoint r₀ r₁ r₂) := by
  intro d _
  cases d
  · refine Or.inl ⟨outY.deviate .p1 FinDistr.uniform,
      ⟨FinDistr.uniform, fun a => FinDistr.uniform_w_pos a, rfl⟩, ?_, ?_⟩
    · rw [outY_deviate_p1_uniform]; exact half_y_nu_obs_pos r₀ r₁ r₂
    · rw [outY_deviate_p1_uniform]
      exact strictClausesAt_calibratedState twoObs _ (twoPoint r₀ r₁ r₂) (sMasked r₀ r₁ r₂) .p1
        (half_y_nu_obs_pos r₀ r₁ r₂) rfl
  · refine Or.inr ⟨rfl, fun C' hC' => ?_⟩
    obtain ⟨m, -, rfl⟩ := hC'
    exact outY_deviate_p2_nu_zero r₀ r₁ r₂ m

/-- The masked state at `p1`: `P(out) = P(in) = ½`, `V(out) = r₀`, `V(in) = r₂`.
Source: `identity.md` ID-22 (M0)
Kind: L -/
theorem maskedState_numbers :
    (maskedState r₀ r₁ r₂).pr (twoActEv .p1 .a) = 1 / 2 ∧
    (maskedState r₀ r₁ r₂).pr (twoActEv .p1 .b) = 1 / 2 ∧
    (maskedState r₀ r₁ r₂).V (twoActEv .p1 .a) = r₀ ∧
    (maskedState r₀ r₁ r₂).V (twoActEv .p1 .b) = r₂ := by
  unfold maskedState
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · first
      | (rw [calibratedState_pr, twoPoint_nu, twoPoint_nu])
      | (rw [calibratedState_V, twoPoint_paySum, twoPoint_nu])
    simp [twoActEv, twoObs]
    all_goals first | ring | field_simp | norm_num

/-- **`T_EDT` holds for `(a, y)` with `sMasked` when `r₂ ≤ r₀`**: at `p1` both acts are possible and
`V(in) = r₂ ≤ r₀ = V(out)`; at `p2` the fantasy state prefers `y`.
Source: `identity.md` ID-22 (M0) ("masked EDT (Def-9 vacuity reading, local masking)")
Kind: P -/
theorem outY_masked_tEdt (h : r₂ ≤ r₀) :
    TEdt (sMasked r₀ r₁ r₂) twoActEv outY (twoPoint r₀ r₁ r₂) := by
  intro d _ _ a ha
  cases d
  · cases a <;> simp [outY, proc2, FinDistr.act2] at ha
    obtain ⟨h1, h2, h3, h4⟩ := maskedState_numbers r₀ r₁ r₂
    rw [mem_argmaxPlus]
    refine ⟨?_, fun b _ => ?_⟩
    · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]
      show 0 < (maskedState r₀ r₁ r₂).pr _
      rw [h1]; norm_num
    · show (maskedState r₀ r₁ r₂).V _ ≤ (maskedState r₀ r₁ r₂).V _
      cases b
      · exact le_rfl
      · rw [h3, h4]; exact h
  · cases a <;> simp [outY, proc2, FinDistr.act2] at ha
    obtain ⟨-, -, h3, h4⟩ := fantasyState_numbers
    rw [mem_argmaxPlus, fantasy_aPlus_p2 (sMasked r₀ r₁ r₂) rfl]
    refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
    show fantasyState.V _ ≤ fantasyState.V _
    cases b
    · rw [h3, h4]; norm_num
    · exact le_rfl

/-- **Masked EDT (LF, vacuity reading) approves `(a, y)` whenever `r₂ ≤ r₀`**.
Source: `identity.md` ID-22 (M0), Open 7; A36 (iii)
Kind: P
Fidelity: variant: Definition 9's null case read as vacuity (A5), local full-support self-models
Hyps: (a) all -/
theorem outY_maskedOC_tEdt (h : r₂ ≤ r₀) :
    ∃ s : Pt2 → State TwoW ℚ,
      MaskedOC s twoObs outY (twoPoint r₀ r₁ r₂) ∧ TEdt s twoActEv outY (twoPoint r₀ r₁ r₂) :=
  ⟨sMasked r₀ r₁ r₂, outY_maskedOC r₀ r₁ r₂, outY_masked_tEdt r₀ r₁ r₂ h⟩

end masked

/-! ### Definition 22, Theorem 1, Theorem 2 on the threat tree -/

section localConds

/-- `(a, y)` on the threat tree is Definition-22-coherent (mixed and pure), Theorem-1-ratified at
both points (vacuously at the unreached `p2`, `Φ_{p2} ≡ 0`), Theorem-2-ratified at both points
(`ssaValue_le_iff'`), and `μ(occ p2) = 0`.
Source: `identity.md` ID-23 rider (a′) ("Def-22 coherence (pure and mixed), Theorem 1, Theorem 2 …
admit the non-optimal off-path profile `(a, y)` of the threat tree"); `calibration.md` CA-19′
Kind: N+ -/
theorem threat_outY_coherent_thm1_thm2 :
    Coherent outY threat ∧ CoherentPure outY threat ∧ Thm1 outY threat ∧
    (∀ d ∈ queried threat, ∀ m, ssaValue outY threat d m ≤ ssaValue outY threat d (outY d)) ∧
    mass outY threat (occ .p2 threat) = 0 := by
  have hcoh : Coherent outY threat := by
    intro d _
    cases d
    · rw [coherentAt_proc2_p1_iff]
      intro r r0 r1
      unfold threat; rw [twoPoint_value, twoPoint_value]; nlinarith
    · rw [coherentAt_proc2_p2_iff]
      intro r r0 r1
      unfold threat; rw [twoPoint_value, twoPoint_value]; nlinarith
  refine ⟨hcoh, Coherent.pure _ _ hcoh, ?_, fun d hd => (coherentAt_iff_ssa' outY threat d).mp (hcoh d hd), ?_⟩
  · intro d _
    cases d
    · rw [thm1At_act2_iff _ _ _ 1 zero_le_one le_rfl rfl]
      unfold threat
      rw [twoPoint_siaSum_p1_a, twoPoint_siaSum_p1_b]
      norm_num
    · rw [thm1At_act2_iff _ _ _ 0 le_rfl zero_le_one rfl]
      unfold threat
      rw [twoPoint_siaSum_p2_a, twoPoint_siaSum_p2_b]
      norm_num
  · rw [mass_occ]
    unfold threat
    rw [twoPoint_sum]
    simp [twoPoint, count_decision, leafLaw_decision, outY, proc2, FinDistr.act2]

end localConds

/-! ### The rows -/

section rows

/-- **T8 — the threat tree (refutation row for identity Dead 1).** On `threat = (1; 2, 0) ∈ 𝔉`,
the off-path profile `(a, y)` is Definition-22-coherent (pure and mixed), Theorem-1- and
Theorem-2-ratified, strict-OC-EDT-approved (stipulated state at the null `p2`),
masked-EDT-approved (LF, vacuity), **D2-rejected**, and not optimal (`V = 1 < 2 = V(in, x)`).
Quoted (identity.md l. 124): "On the fair class, local ratifiability (Def 22 / Theorem 2 /
tremble-EDT) has the same maximizers as global optimality". Reading: for every `B ∈ 𝔉` the sets
of Definition-22-coherent (or Theorem-2-ratified, or tremble-EDT-consistent) procedures and of
optimal procedures coincide. Refuted for Definition 22 and Theorem 2 by this tree (`(a, y)` is in
the former sets and not optimal) and, for tremble-EDT, by FR-12 (`fr12_outY_isOptimal_not_eventTremble`:
the inclusion is strict). Surviving neighbour: `∅ ≠ {D2} ⊊ {optimal}` on `𝔉`
(`eventTrembleEdt_isOptimal_of_fairClass`, `fr12_eventTremble_iff`). The general "Definition 22 /
Theorem 1 / Theorem 2 are blind at `μ(occ d) = 0`" is `dp-local-opt`'s `coherentAt_of_mass_eq_zero`
(not re-proved). Limit-state EDT (D1) approves `(a, y)` too: `outY_limitStateEdt` (`LimitState.lean`),
assembled with this row in `threat_outY_untrembled_all`.
Source: `identity.md` Dead 1 (l. 124), ID-22 (M0), ID-23 rider (a′); A36 (iii); `calibration.md`
CA-19′; dp-cf-028; dp-cf-2-058
Kind: N+ (refutation instance)
Fidelity: exact
Hyps: (a) all -/
theorem threat_outY_untrembled :
    FairClass twoObs twoActEv threat ∧
    Coherent outY threat ∧ CoherentPure outY threat ∧ Thm1 outY threat ∧
    (∀ d ∈ queried threat, ∀ m, ssaValue outY threat d m ≤ ssaValue outY threat d (outY d)) ∧
    (∃ s, StrictOC s twoObs outY threat ∧ TEdt s twoActEv outY threat) ∧
    (∃ s, MaskedOC s twoObs outY threat ∧ TEdt s twoActEv outY threat) ∧
    ¬ EventTrembleEdtConsistent twoObs twoActEv outY threat ∧
    ¬ IsOptimal outY threat ∧ value outY threat = 1 ∧ value inX threat = 2 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := threat_outY_coherent_thm1_thm2
  obtain ⟨n1, n2, n3, n4⟩ := threat_outY_not_eventTremble
  exact ⟨twoPoint_fairClass 1 2 0, h1, h2, h3, h4, outY_strictOC_tEdt 1 2 0,
    outY_maskedOC_tEdt 1 2 0 (by norm_num), n1, n2, n3, n4⟩

/-- D2 rejects `(a, y)` on `twoPoint r₀ r₁ r₂` whenever `r₂ < r₁`, and `(a, y)` is not optimal
whenever `r₀ < r₁`.
Source: `fair-repair.md` §3.2 ("Under trembles, `ε`-calibration forces `s₂` to the true
continuation, EDT flips `d₂` to `x`, then `d₁` to in")
Kind: L -/
theorem outY_not_eventTremble_of_lt (r₀ r₁ r₂ : ℚ) (h21 : r₂ < r₁) (h01 : r₀ < r₁) :
    ¬ EventTrembleEdtConsistent twoObs twoActEv outY (twoPoint r₀ r₁ r₂) ∧
    ¬ IsOptimal outY (twoPoint r₀ r₁ r₂) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [(twoPoint_fairClass r₀ r₁ r₂).eventTremble_iff_Q] at h
    obtain ⟨ε₀, hε₀, hQ⟩ := h
    have := hQ (min (ε₀ / 2) 1) (lt_min (by linarith) one_pos) (min_le_right _ _)
      ((min_le_left _ _).trans_lt (by linarith)) .p2 (twoPoint_queried r₀ r₁ r₂).2 .b
      (by simp [outY, proc2, FinDistr.act2]) .a
    rw [twoPoint_Q_p2_a, twoPoint_Q_p2_b] at this
    linarith
  · have := h inX
    unfold inX outY at this
    rw [twoPoint_value, twoPoint_value] at this
    linarith

/-- **T7(i), no trembles — the imperfect equilibrium on `fantasy241`**: `(a, y)` is
strict-OC-EDT-consistent with a fantasy state at the null `p2`, masked-EDT-consistent (vacuity),
Definition-22-coherent and Theorem-1-ratified (`dp-local-opt`), D2-rejected, not optimal
(`V = 2 < 4`); `fantasy241 ∈ 𝔉`. The tremble is load-bearing.
Source: `fair-repair.md` §3.2 ("Without trembles"); A36 (iii); `calibration.md` CA-1′(iii),
CA-19′; dp-cf-024, dp-cf-034, dp-cf-132
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem fantasy_outY_untrembled :
    FairClass twoObs twoActEv fantasy241 ∧
    (∃ s, StrictOC s twoObs outY fantasy241 ∧ TEdt s twoActEv outY fantasy241) ∧
    (∃ s, MaskedOC s twoObs outY fantasy241 ∧ TEdt s twoActEv outY fantasy241) ∧
    Coherent outY fantasy241 ∧ Thm1 outY fantasy241 ∧
    ¬ EventTrembleEdtConsistent twoObs twoActEv outY fantasy241 ∧
    ¬ IsOptimal outY fantasy241 ∧ value outY fantasy241 = 2 := by
  obtain ⟨hcoh, -, hthm1, -, hval, -, -⟩ := outY_coherent_thm1_not_optimal
  obtain ⟨n1, n2⟩ := outY_not_eventTremble_of_lt 2 4 1 (by norm_num) (by norm_num)
  exact ⟨twoPoint_fairClass 2 4 1, outY_strictOC_tEdt 2 4 1, outY_maskedOC_tEdt 2 4 1 (by norm_num),
    hcoh, hthm1, n1, n2, hval⟩

/-- **T7(i), second instance — D3's 5-node sanity instance `(3; 4, 0)`**: the same verdicts.
Source: `phase1/verify-prior-notes.md` D3 (the sanity instance); mandate T7(i)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem twoPoint340_outY_untrembled :
    FairClass twoObs twoActEv (twoPoint 3 4 0) ∧
    (∃ s, StrictOC s twoObs outY (twoPoint 3 4 0) ∧ TEdt s twoActEv outY (twoPoint 3 4 0)) ∧
    (∃ s, MaskedOC s twoObs outY (twoPoint 3 4 0) ∧ TEdt s twoActEv outY (twoPoint 3 4 0)) ∧
    ¬ EventTrembleEdtConsistent twoObs twoActEv outY (twoPoint 3 4 0) ∧
    ¬ IsOptimal outY (twoPoint 3 4 0) ∧ value outY (twoPoint 3 4 0) = 3 := by
  obtain ⟨n1, n2⟩ := outY_not_eventTremble_of_lt 3 4 0 (by norm_num) (by norm_num)
  exact ⟨twoPoint_fairClass 3 4 0, outY_strictOC_tEdt 3 4 0, outY_maskedOC_tEdt 3 4 0 (by norm_num),
    n1, n2, by unfold outY; rw [twoPoint_value]; norm_num⟩

end rows

end Cleanroom.Decision.DpEdtUdtFair
