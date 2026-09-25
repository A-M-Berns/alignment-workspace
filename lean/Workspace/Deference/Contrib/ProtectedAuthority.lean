/-
# Protected authority: the signed decomposition of the bypass premium

Round `projects/deference/rounds/2026-09-24-protected-authority/`.

**1. The decomposition.**  At a decision point the principal's operative evaluator, applied
to the branch-common dossier, scores three continuations: release unasked (`vu`), ask and
release on approval (`vp`), ask and hold on decline (`vm`); her response is `r`.  With the
reference `M = max vp vm` (`bestResp`) the quantities are the **provenance premium**
`ξ_p = vp − vu` (`provPremium`), the **veto value** `ξ_v = M − vp ≥ 0` (`vetoValue`), the
**consultation premium** `ξ_c = M − vu = ξ_p + ξ_v` (`consultPremium`) and the **execution
divergence** `ξ_d = M − v_r ≥ 0` (`execDiv`).  `identity` is
`vu − v_r = ξ_d − ξ_c`, exact; `approve_identity` shows the approve branch reduces to `−ξ_p`
(`ξ_d` and `ξ_v` cancel), so `ξ_d` carries content on decline worlds only.
`nondelegation_le`, `legit_nondelegation_le_zero` and `strict_of_pos`: under `ξ_p ≥ 0`
(nondelegation) and `ξ_d = 0` (a legitimate response) unasked release never scores above
the response, and scores strictly below it wherever `ξ_c > 0`.  `execDiv_le_width`: the
divergence is at most the width times the disagreement of the response with the
evaluator's argmax — the response channel's defect.  `expect_sub_eq` and
`expect_sub_le_of_pointwise`: the expected form under any nonnegative credence, so the sign
of the conclusion does not depend on the agent's beliefs.

**2. The outcome-scoring companion.**  With `qu, qp, qm` the agent's forecasts of a
provenance-blind outcome evaluation, `outcome_identity` is
`qu − q_r = ξ_d − ξ_c + o₁ + o₂` with `o₁ = (qu − qp) + ξ_p` (the provenance value outcome
scoring discards) and `o₂ = (qp − q_r) − (vp − v_r)`, zero on approval and
`(qp − qm) − (vp − vm)` on decline (`outcomeRes2_approve`, `outcomeRes2_decline`).

**3. Activation.**  `activation_identity` is `LICorrigibility.mismatch_identity` with the
common term rewritten; `activation_bound` charges the raw-only branch at the width;
`activation_bound_defects` composes with `TransparentChannel.expect_mismatch_le_defects`.

**4. Whole runs.**  `ever_bypass_le`: a chooser that bypasses at a node exactly when its
local expected gap is positive bypasses somewhere with credence at most the sum over
nodes of the reach credence of the nodes whose gap is positive (a union bound);
`no_bypass_of_nonpos` is the zero case.  `hybrid_telescope` and `hybrid_ask_dominates`: a
deepest-first hybrid comparison under one fixed evaluator is the sum of local gaps priced
by that evaluator, each `drift − ξ_c^E`; `drift_eq_execDiv`, `drift_nonneg`,
`drift_zero_of_consistent`: the drift is the root evaluator's execution divergence of the
node's own recommendation, nonnegative, zero when the evaluators agree on the argmax.

**5. Routes and successors.**  `route_priced`: any continuation the evaluator scores no
higher than the approved release scores no higher than the response — the motive to use an
undeclared route is removed by a hypothesis on the evaluator, not on the gate.
`Witness.successor_approved`: every hypothesis holds and the approved branch installs an
uncorrectable successor; the identity yields no preservation.

**6. The response through the tower.**  `legit_execDiv_zero`: the argmax response has zero
divergence; `execDiv_of_tower`: under `TransparentChannel.tower_factor`'s hypotheses two
continuations agreeing on the declared amendment inputs have the same divergence, so a
response legitimate for one is legitimate for the other.

**7. Logical-Induction compilation.**  `li_combination_le` is the generic passage from
validity in every completed-theory world to `𝔼ₙ ≲ₙ 0` (the pinned `thm:expcoh` with its
operational premises as named hypotheses, factored out of `LICorrigibility.li_constraint_le`).
`AuthorityPair` carries the six gated LUVs; `Bl`/`Bg` are the two directions of the
identity as constraints; `li_authority_le`/`li_authority_ge` give
`𝔼ₙ(U_u) − 𝔼ₙ(U_a) ≲ₙ 𝔼ₙ(Ξ_d) − 𝔼ₙ(Ξ_c) + 𝔼ₙ(M)` and the reverse with the corr-only
indicator, inhabited by `Witness.pair`.

**What this does not establish.**  That any real evaluator satisfies nondelegation (a
program property, to be certified at commitment); that any response is legitimate (the
response channel's reference is not declared anywhere on `main`); the generability
certificate of the six-term combination (the operational witness is a hypothesis, as in
`li_constraint_le`); anything about the size of `ξ_d`.  Names are provisional
(`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.LICorrigibility
import Workspace.Deference.Contrib.MediatedRepairDominance
import Workspace.Deference.Contrib.TransparentChannel

namespace Workspace.Deference.Contrib.ProtectedAuthority

open Workspace.Deference.Contrib.LICorrigibility
open Workspace.Deference.Contrib.TransparentChannel (defect disagree expect_mismatch_le_defects
  tower_factor)
open LogicalInduction
open Filter Topology
open scoped Classical

/-! ## 1. The decomposition, pointwise -/

section Pointwise

/-- The reference: the value of the best response by the evaluator, `M = max vp vm`. -/
def bestResp (vp vm : ℝ) : ℝ := max vp vm

/-- The value of the response actually given (`true` = approve). -/
def respVal (vp vm : ℝ) (r : Bool) : ℝ := if r then vp else vm

/-- Provenance premium `ξ_p = vp − vu`. -/
def provPremium (vu vp : ℝ) : ℝ := vp - vu

/-- Veto value `ξ_v = M − vp`. -/
def vetoValue (vp vm : ℝ) : ℝ := bestResp vp vm - vp

/-- Consultation premium `ξ_c = M − vu`. -/
def consultPremium (vu vp vm : ℝ) : ℝ := bestResp vp vm - vu

/-- Execution divergence `ξ_d = M − v_r`. -/
def execDiv (vp vm : ℝ) (r : Bool) : ℝ := bestResp vp vm - respVal vp vm r

theorem consult_eq (vu vp vm : ℝ) :
    consultPremium vu vp vm = provPremium vu vp + vetoValue vp vm := by
  unfold consultPremium provPremium vetoValue; ring

theorem veto_nonneg (vp vm : ℝ) : 0 ≤ vetoValue vp vm := by
  unfold vetoValue bestResp; linarith [le_max_left vp vm]

theorem respVal_le_bestResp (vp vm : ℝ) (r : Bool) : respVal vp vm r ≤ bestResp vp vm := by
  unfold respVal bestResp; cases r <;> simp

theorem execDiv_nonneg (vp vm : ℝ) (r : Bool) : 0 ≤ execDiv vp vm r := by
  unfold execDiv; linarith [respVal_le_bestResp vp vm r]

/-- **The identity.**  `vu − v_r = ξ_d − ξ_c`. -/
theorem identity (vu vp vm : ℝ) (r : Bool) :
    vu - respVal vp vm r = execDiv vp vm r - consultPremium vu vp vm := by
  unfold execDiv consultPremium; ring

/-- **The identity, expanded.**  `vu − v_r = ξ_d − ξ_p − ξ_v`. -/
theorem identity' (vu vp vm : ℝ) (r : Bool) :
    vu - respVal vp vm r = execDiv vp vm r - provPremium vu vp - vetoValue vp vm := by
  rw [identity, consult_eq]; ring

theorem execDiv_eq_zero_iff (vp vm : ℝ) (r : Bool) :
    execDiv vp vm r = 0 ↔ respVal vp vm r = bestResp vp vm := by
  unfold execDiv; constructor <;> intro h <;> linarith

/-- On the approve branch the divergence and the veto value cancel: `vu − vp = −ξ_p`. -/
theorem approve_identity (vu vp vm : ℝ) :
    vu - respVal vp vm true = -(provPremium vu vp) ∧
      execDiv vp vm true = vetoValue vp vm := by
  constructor <;> simp [respVal, provPremium, execDiv, vetoValue]

/-- On the decline branch the divergence is `(vp − vm)⁺` and the veto value `(vm − vp)⁺`. -/
theorem decline_execDiv (vp vm : ℝ) : execDiv vp vm false = max (vp - vm) 0 := by
  unfold execDiv bestResp respVal
  simp only [Bool.false_eq_true, if_false]
  rcases le_total vp vm with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]

/-- **Nondelegation.**  With `ξ_p ≥ 0`, the unasked release scores at most `ξ_d` above the
response. -/
theorem nondelegation_le (vu vp vm : ℝ) (r : Bool) (hγ : 0 ≤ provPremium vu vp) :
    vu - respVal vp vm r ≤ execDiv vp vm r := by
  rw [identity']; linarith [veto_nonneg vp vm]

/-- **Nondelegation with a legitimate response.**  `vu − v_r ≤ 0`. -/
theorem legit_nondelegation_le_zero (vu vp vm : ℝ) (r : Bool)
    (hγ : 0 ≤ provPremium vu vp) (hL : execDiv vp vm r = 0) :
    vu - respVal vp vm r ≤ 0 := by
  have := nondelegation_le vu vp vm r hγ; linarith

/-- **Strictness.**  Asking is strictly better wherever the consultation premium is
positive. -/
theorem strict_of_pos (vu vp vm : ℝ) (r : Bool)
    (hL : execDiv vp vm r = 0) (hpos : 0 < consultPremium vu vp vm) :
    vu - respVal vp vm r < 0 := by
  rw [identity, hL]; linarith

/-- The evaluator's own argmax as a response. -/
noncomputable def argmaxResp (vp vm : ℝ) : Bool := decide (vm ≤ vp)

/-- **The argmax response has zero divergence.** -/
theorem legit_execDiv_zero (vp vm : ℝ) : execDiv vp vm (argmaxResp vp vm) = 0 := by
  unfold execDiv argmaxResp respVal bestResp
  by_cases h : vm ≤ vp
  · simp [h]
  · have h' : vp ≤ vm := (not_le.mp h).le
    simp [h, max_eq_right h']

/-- **The divergence is at most the width times the response's disagreement with the
argmax** — the response channel's pathwise defect. -/
theorem execDiv_le_width (vp vm D : ℝ) (r : Bool)
    (hvp : 0 ≤ vp ∧ vp ≤ D) (hvm : 0 ≤ vm ∧ vm ≤ D) :
    execDiv vp vm r ≤ D * (if r = argmaxResp vp vm then 0 else 1) := by
  by_cases h : r = argmaxResp vp vm
  · rw [if_pos h, h, legit_execDiv_zero]; simp
  · rw [if_neg h, mul_one]
    unfold execDiv bestResp respVal
    cases r <;> simp only [Bool.false_eq_true, if_false, if_true]
    · linarith [max_le hvp.2 hvm.2, hvm.1]
    · linarith [max_le hvp.2 hvm.2, hvp.1]

variable {X : Type*} [Fintype X]

/-- **The expected identity under any credence.** -/
theorem expect_sub_eq (μ vu vp vm : X → ℝ) (r : X → Bool) :
    expectR μ vu - expectR μ (fun x => respVal (vp x) (vm x) (r x))
      = expectR μ (fun x => execDiv (vp x) (vm x) (r x))
        - expectR μ (fun x => consultPremium (vu x) (vp x) (vm x)) := by
  simp only [expectR, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_sub, ← mul_sub, identity]

/-- **Belief independence.**  Under nondelegation and legitimate responses in every world,
the expected bypass premium is nonpositive for every nonnegative credence. -/
theorem expect_sub_le_of_pointwise (μ vu vp vm : X → ℝ) (r : X → Bool) (hμ : ∀ x, 0 ≤ μ x)
    (hγ : ∀ x, 0 ≤ provPremium (vu x) (vp x)) (hL : ∀ x, execDiv (vp x) (vm x) (r x) = 0) :
    expectR μ vu - expectR μ (fun x => respVal (vp x) (vm x) (r x)) ≤ 0 := by
  rw [expect_sub_eq]
  have : ∀ x, execDiv (vp x) (vm x) (r x) - consultPremium (vu x) (vp x) (vm x) ≤ 0 := by
    intro x
    have := legit_nondelegation_le_zero (vu x) (vp x) (vm x) (r x) (hγ x) (hL x)
    rw [identity] at this; exact this
  simp only [expectR, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonpos fun x _ => ?_
  rw [← mul_sub]
  exact mul_nonpos_of_nonneg_of_nonpos (hμ x) (this x)

/-- **The expected divergence is at most the width times the response defect mass.** -/
theorem expect_execDiv_le (μ vp vm : X → ℝ) (r : X → Bool) (D : ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hvp : ∀ x, 0 ≤ vp x ∧ vp x ≤ D) (hvm : ∀ x, 0 ≤ vm x ∧ vm x ≤ D) :
    expectR μ (fun x => execDiv (vp x) (vm x) (r x))
      ≤ D * expectR μ (fun x => if r x = argmaxResp (vp x) (vm x) then 0 else 1) := by
  unfold expectR
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (execDiv_le_width _ _ _ _ (hvp x) (hvm x)) (hμ x)

end Pointwise

/-! ## 2. The outcome-scoring companion -/

section Outcome

/-- The provenance value outcome scoring discards, `o₁ = (qu − qp) + ξ_p`. -/
def outcomeRes1 (qu qp vu vp : ℝ) : ℝ := (qu - qp) + provPremium vu vp

/-- The forecast disagreement with the evaluator on the response,
`o₂ = (qp − q_r) − (vp − v_r)`. -/
def outcomeRes2 (qp qm vp vm : ℝ) (r : Bool) : ℝ :=
  (qp - respVal qp qm r) - (vp - respVal vp vm r)

/-- **The companion identity.**  `qu − q_r = ξ_d − ξ_c + o₁ + o₂`. -/
theorem outcome_identity (qu qp qm vu vp vm : ℝ) (r : Bool) :
    qu - respVal qp qm r
      = execDiv vp vm r - consultPremium vu vp vm
        + outcomeRes1 qu qp vu vp + outcomeRes2 qp qm vp vm r := by
  unfold outcomeRes1 outcomeRes2 execDiv consultPremium provPremium; ring

theorem outcomeRes2_approve (qp qm vp vm : ℝ) : outcomeRes2 qp qm vp vm true = 0 := by
  unfold outcomeRes2 respVal; simp

theorem outcomeRes2_decline (qp qm vp vm : ℝ) :
    outcomeRes2 qp qm vp vm false = (qp - qm) - (vp - vm) := by
  unfold outcomeRes2 respVal; simp

/-- Under nondelegation and a legitimate response the outcome-scored premium is at most
the two residues: what outcome scoring can add, it adds only through `o₁ + o₂`. -/
theorem outcome_le_residues (qu qp qm vu vp vm : ℝ) (r : Bool)
    (hγ : 0 ≤ provPremium vu vp) (hL : execDiv vp vm r = 0) :
    qu - respVal qp qm r ≤ outcomeRes1 qu qp vu vp + outcomeRes2 qp qm vp vm r := by
  rw [outcome_identity, hL, consult_eq]; linarith [veto_nonneg vp vm]

end Outcome

/-! ## 3. Activation -/

section Activation

/-- **The activation identity**: `mismatch_identity` with the common term rewritten. -/
theorem activation_identity (cu ca : Bool) (vu vp vm : ℝ) (r : Bool) :
    indR cu * vu - indR ca * respVal vp vm r
      = indR cu * indR ca * (execDiv vp vm r - consultPremium vu vp vm)
        + indR cu * (1 - indR ca) * vu - (1 - indR cu) * indR ca * respVal vp vm r := by
  rw [← identity]; exact mismatch_identity cu ca vu (respVal vp vm r)

/-- **The activation bound**: the raw-only branch at the width, the corr-only branch
dropped. -/
theorem activation_bound (cu ca : Bool) (vu vp vm D : ℝ) (r : Bool)
    (hvu : vu ≤ D) (hvr : 0 ≤ respVal vp vm r) :
    indR cu * vu - indR ca * respVal vp vm r
      ≤ indR cu * indR ca * (execDiv vp vm r - consultPremium vu vp vm)
        + D * (indR cu * (1 - indR ca)) := by
  rw [activation_identity]
  cases cu <;> cases ca <;> simp [indR] <;> linarith

variable {X : Type*} [Fintype X]

/-- **The activation bound in expectation.** -/
theorem activation_bound_expect (μ vu vp vm : X → ℝ) (r cu ca : X → Bool) (D : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hvu : ∀ x, vu x ≤ D) (hvr : ∀ x, 0 ≤ respVal (vp x) (vm x) (r x)) :
    expectR μ (fun x => indR (cu x) * vu x)
      - expectR μ (fun x => indR (ca x) * respVal (vp x) (vm x) (r x))
      ≤ expectR μ (fun x => indR (cu x) * indR (ca x)
          * (execDiv (vp x) (vm x) (r x) - consultPremium (vu x) (vp x) (vm x)))
        + D * expectR μ (fun x => indR (cu x) * (1 - indR (ca x))) := by
  have hrhs : expectR μ (fun x => indR (cu x) * indR (ca x)
          * (execDiv (vp x) (vm x) (r x) - consultPremium (vu x) (vp x) (vm x)))
        + D * expectR μ (fun x => indR (cu x) * (1 - indR (ca x)))
      = ∑ x, μ x * (indR (cu x) * indR (ca x)
          * (execDiv (vp x) (vm x) (r x) - consultPremium (vu x) (vp x) (vm x))
          + D * (indR (cu x) * (1 - indR (ca x)))) := by
    simp only [expectR, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_; ring
  have hlhs : expectR μ (fun x => indR (cu x) * vu x)
      - expectR μ (fun x => indR (ca x) * respVal (vp x) (vm x) (r x))
      = ∑ x, μ x * (indR (cu x) * vu x - indR (ca x) * respVal (vp x) (vm x) (r x)) := by
    simp only [expectR, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_; ring
  rw [hrhs, hlhs]
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (activation_bound (cu x) (ca x) (vu x) (vp x) (vm x) D (r x) (hvu x) (hvr x)) (hμ x)

end Activation

section ActivationDefects

variable {Q Z Ω X : Type*} [Fintype Z]

/-- **The activation bound with the mismatch mass charged to the activation channel's
defects** (the transparent-channel round's `expect_mismatch_le_defects`). -/
theorem activation_bound_defects (β : Q → Z → Ω) (x : Ω → X) (c : Ω → Bool)
    (κ : X → Z → Bool) (μ : Z → ℝ) (hμ : ∀ z, 0 ≤ μ z) (D : ℝ) (hD : 0 ≤ D)
    (qu qa : Q) (hx : ∀ z, x (β qu z) = x (β qa z))
    (vu vp vm : Z → ℝ) (r : Z → Bool)
    (hvu : ∀ z, vu z ≤ D) (hvr : ∀ z, 0 ≤ respVal (vp z) (vm z) (r z)) :
    expectR μ (fun z => indR (c (β qu z)) * vu z)
      - expectR μ (fun z => indR (c (β qa z)) * respVal (vp z) (vm z) (r z))
      ≤ expectR μ (fun z => indR (c (β qu z)) * indR (c (β qa z))
          * (execDiv (vp z) (vm z) (r z) - consultPremium (vu z) (vp z) (vm z)))
        + D * (expectR μ (defect β x c κ qu) + expectR μ (defect β x c κ qa)) := by
  have h1 := activation_bound_expect μ vu vp vm r (fun z => c (β qu z)) (fun z => c (β qa z))
    D hμ hvu hvr
  have h2 := expect_mismatch_le_defects β x c κ μ hμ qu qa hx
  have h3 := mul_le_mul_of_nonneg_left h2 hD
  linarith

end ActivationDefects

/-! ## 4. Whole runs -/

section Sequential

variable {X H : Type*} [Fintype X] [Fintype H]

omit [Fintype X] in
/-- The union bound, pointwise: the indicator of "some node is reached and bypasses" is at
most the sum of the per-node indicators. -/
theorem ever_indicator_le (reach : H → X → Bool) (bypassAt : H → Bool) (x : X) :
    indR (decide (∃ h, reach h x = true ∧ bypassAt h = true))
      ≤ ∑ h, indR (reach h x && bypassAt h) := by
  by_cases hex : ∃ h, reach h x = true ∧ bypassAt h = true
  · obtain ⟨h₀, hr, hb⟩ := hex
    have hterm : indR (reach h₀ x && bypassAt h₀) = 1 := by simp [indR, hr, hb]
    have hex' : ∃ h, reach h x = true ∧ bypassAt h = true := ⟨h₀, hr, hb⟩
    calc indR (decide (∃ h, reach h x = true ∧ bypassAt h = true)) = 1 := by
          simp [indR, hex']
      _ = indR (reach h₀ x && bypassAt h₀) := hterm.symm
      _ ≤ ∑ h, indR (reach h x && bypassAt h) :=
          Finset.single_le_sum (f := fun h => indR (reach h x && bypassAt h))
            (fun h _ => indR_nonneg _) (Finset.mem_univ h₀)
  · simp only [indR, decide_eq_true_eq, hex, if_false]
    exact Finset.sum_nonneg fun h _ => indR_nonneg _

/-- **The sequential bound.**  A chooser bypassing at node `h` exactly when its local gap
`g h` is positive (ties toward asking) bypasses somewhere with credence at most the sum,
over the nodes with positive gap, of their reach credence. -/
theorem ever_bypass_le (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (reach : H → X → Bool) (g : H → ℝ) :
    expectR μ (fun x => indR (decide (∃ h, reach h x = true ∧ decide (0 < g h) = true)))
      ≤ ∑ h, (if 0 < g h then expectR μ (fun x => indR (reach h x)) else 0) := by
  have hsum : ∑ h, (if 0 < g h then expectR μ (fun x => indR (reach h x)) else 0)
      = ∑ x, μ x * ∑ h, indR (reach h x && decide (0 < g h)) := by
    simp only [expectR, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hg : 0 < g h
    · simp [hg]
    · simp [hg, indR]
  rw [hsum]
  unfold expectR
  refine Finset.sum_le_sum fun x _ => ?_
  exact mul_le_mul_of_nonneg_left (ever_indicator_le reach (fun h => decide (0 < g h)) x) (hμ x)

/-- **No bypass under nonpositive gaps.** -/
theorem no_bypass_of_nonpos (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (reach : H → X → Bool)
    (g : H → ℝ) (hg : ∀ h, g h ≤ 0) :
    expectR μ (fun x => indR (decide (∃ h, reach h x = true ∧ decide (0 < g h) = true))) = 0 := by
  apply le_antisymm
  · refine le_trans (ever_bypass_le μ hμ reach g) ?_
    refine le_of_eq (Finset.sum_eq_zero fun h _ => ?_)
    have : ¬ 0 < g h := not_lt.mpr (hg h)
    simp [this]
  · unfold expectR
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (indR_nonneg _)

end Sequential

section Global

/-- **Telescoping of a hybrid chain.**  The value difference between the first and the
last hybrid is the sum of the single-node replacements. -/
theorem hybrid_telescope (k : ℕ) (V : ℕ → ℝ) :
    V 0 - V k = ∑ i ∈ Finset.range k, (V i - V (i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ← ih]; ring

/-- The drift at a node under the root evaluator `E`: `E`'s execution divergence of the
node evaluator's recommended response. -/
def drift (vpE vmE : ℝ) (rec : Bool) : ℝ := execDiv vpE vmE rec

theorem drift_eq_execDiv (vpE vmE : ℝ) (rec : Bool) : drift vpE vmE rec = execDiv vpE vmE rec :=
  rfl

theorem drift_nonneg (vpE vmE : ℝ) (rec : Bool) : 0 ≤ drift vpE vmE rec :=
  execDiv_nonneg _ _ _

/-- **Time-consistency**: when the node's recommendation is also the root evaluator's
argmax the drift vanishes. -/
theorem drift_zero_of_consistent (vpE vmE : ℝ) (rec : Bool) (h : rec = argmaxResp vpE vmE) :
    drift vpE vmE rec = 0 := by
  rw [drift_eq_execDiv, h, legit_execDiv_zero]

/-- **The global comparison with drift.**  With each single-node replacement priced under
the root evaluator as `p i · (drift i − ξ_c^E i)`, the all-ask hybrid's deficit against
the original is the drift-weighted sum less the consultation premia. -/
theorem hybrid_global (k : ℕ) (V : ℕ → ℝ) (p vpE vmE vuE : ℕ → ℝ) (rec : ℕ → Bool)
    (hstep : ∀ i < k, V i - V (i + 1)
      = p i * (drift (vpE i) (vmE i) (rec i) - consultPremium (vuE i) (vpE i) (vmE i))) :
    V 0 - V k = ∑ i ∈ Finset.range k,
      p i * (drift (vpE i) (vmE i) (rec i) - consultPremium (vuE i) (vpE i) (vmE i)) := by
  rw [hybrid_telescope]
  exact Finset.sum_congr rfl fun i hi => hstep i (Finset.mem_range.mp hi)

/-- **Asking dominates under time-consistency and nondelegation**, for nonnegative reach
weights. -/
theorem hybrid_ask_dominates (k : ℕ) (V : ℕ → ℝ) (p vpE vmE vuE : ℕ → ℝ) (rec : ℕ → Bool)
    (hstep : ∀ i < k, V i - V (i + 1)
      = p i * (drift (vpE i) (vmE i) (rec i) - consultPremium (vuE i) (vpE i) (vmE i)))
    (hp : ∀ i, 0 ≤ p i) (hcons : ∀ i, rec i = argmaxResp (vpE i) (vmE i))
    (hγ : ∀ i, 0 ≤ consultPremium (vuE i) (vpE i) (vmE i)) :
    V 0 ≤ V k := by
  have h := hybrid_global k V p vpE vmE vuE rec hstep
  have hle : ∑ i ∈ Finset.range k,
      p i * (drift (vpE i) (vmE i) (rec i) - consultPremium (vuE i) (vpE i) (vmE i)) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    rw [drift_zero_of_consistent _ _ _ (hcons i)]
    exact mul_nonpos_of_nonneg_of_nonpos (hp i) (by linarith [hγ i])
  linarith

end Global

/-! ## 5. Routes and successors -/

section Routes

/-- **Loophole pricing.**  A continuation the evaluator scores no higher than the approved
release (concern completeness plus nondelegation of the concern) scores no higher than
a legitimate response, whatever the gate sees. -/
theorem route_priced (vroute vp vm : ℝ) (r : Bool) (hCC : vroute ≤ vp)
    (hL : execDiv vp vm r = 0) : vroute - respVal vp vm r ≤ 0 := by
  have := (execDiv_eq_zero_iff vp vm r).mp hL
  have := le_max_left vp vm
  unfold bestResp at *; linarith

end Routes

/-! ## 6. The response through the amendment tower -/

section Tower

variable {Q Z Ω C G E : Type*}

/-- **Legitimacy is carried by the tower.**  Under the factorization hypotheses of
`tower_factor`, with the operative evaluator read off the specification at level `t`, two
continuations agreeing on the declared amendment inputs below `t` have the same execution
divergence for every response; in particular a response legitimate for one — the argmax
of the amended evaluator — is legitimate for the other. -/
theorem execDiv_of_tower (β : Q → Z → Ω) (D : Set Q) (Amend : C → G → E → C)
    (spec : ℕ → Ω → C) (g : ℕ → Ω → G) (e : ℕ → Ω → E) (c₀ : C)
    (evalP evalM : C → ℝ)
    (h0 : ∀ q ∈ D, ∀ z, spec 0 (β q z) = c₀)
    (hstep : ∀ t, ∀ q ∈ D, ∀ z,
      spec (t + 1) (β q z) = Amend (spec t (β q z)) (g t (β q z)) (e t (β q z)))
    (t : ℕ) (q : Q) (hq : q ∈ D) (q' : Q) (hq' : q' ∈ D) (z : Z)
    (hagree : ∀ s < t, g s (β q z) = g s (β q' z) ∧ e s (β q z) = e s (β q' z)) (r : Bool) :
    execDiv (evalP (spec t (β q z))) (evalM (spec t (β q z))) r
      = execDiv (evalP (spec t (β q' z))) (evalM (spec t (β q' z))) r ∧
    execDiv (evalP (spec t (β q' z))) (evalM (spec t (β q' z)))
      (argmaxResp (evalP (spec t (β q z))) (evalM (spec t (β q z)))) = 0 := by
  have hs := tower_factor β D Amend spec g e c₀ h0 hstep t q hq q' hq' z hagree
  rw [hs]
  exact ⟨rfl, legit_execDiv_zero _ _⟩

end Tower

/-! ## 7. Logical-Induction compilation -/

section EPI

/-- **The generic passage from validity to `𝔼ₙ ≲ₙ 0`.**  For a combination sequence whose
every coherent completed-theory valuation is nonpositive, and bounded below by `−K` at the
canonical valuation, the pinned `thm:expcoh` with its operational premises gives
`𝔼ₙ(A_n) ≲ₙ 0`. -/
theorem li_combination_le {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (As : ℕ → LUVCombination)
    (hvalued : LUVCombination.WorldValued As DP)
    (hle : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν : LUV → ℝ, (As n).ValuesAt v ν → (As n).value P ν ≤ 0)
    (K : ℝ)
    (hge : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν : LUV → ℝ, (As n).ValuesAt v ν → -K ≤ (As n).value P ν)
    (h : LUVCombination.BoundedSequence As P)
    (ops : LUVCombination.MeshSoftmaxOperationalWitness As P)
    (hcode : ∀ n q, q ∈ (As n).terms → q.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ)) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (As n).expect P n) ≲ₙ fun _ => 0 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hcoh := LUVCombination.BoundedSequence.expcoh h ops hvalued hcode b hb hshare hworld
  have hhigh_le : ∀ n, LUVCombination.completedHigh As P DP n ≤ 0 := by
    intro n
    apply Real.sSup_le _ le_rfl
    rintro x ⟨v, ν, hv, hν, rfl⟩
    exact hle n v hv ν hν
  have hhigh_ge : ∀ n, -K ≤ LUVCombination.completedHigh As P DP n := by
    intro n
    obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
    obtain ⟨ν, hν⟩ := hvalued n v hv
    have hmem : (As n).value P ν ∈ LUVCombination.completedValues DP (As n) P :=
      ⟨v, ν, hv, hν, rfl⟩
    have hbdd : BddAbove (LUVCombination.completedValues DP (As n) P) := by
      refine ⟨0, ?_⟩
      rintro x ⟨w, ν', hw, hν', rfl⟩
      exact hle n w hw ν' hν'
    exact le_trans (hge n v hv ν hν) (le_csSup hbdd hmem)
  have hhigh : limsup (LUVCombination.completedHigh As P DP) atTop ≤ 0 := by
    apply limsup_le_of_le
    · exact (isBoundedUnder_of ⟨-K, hhigh_ge⟩).isCoboundedUnder_flip
    · exact Eventually.of_forall hhigh_le
  have hlim : limsup (fun n => (As n).expect P n) atTop ≤ 0 :=
    (hcoh.2.1.trans hcoh.2.2).trans hhigh
  obtain ⟨B, hB⟩ := h.bounded
  have hup : IsBoundedUnder (· ≤ ·) atTop (fun n => (As n).expect P n) := by
    refine isBoundedUnder_of ⟨B, fun n => ?_⟩
    have := (As n).abs_expectAt_le_l1Norm P (n + 1) n (hP n)
    have := abs_le.mp this
    show (As n).expectAt P (n + 1) n ≤ B
    linarith [hB n]
  intro ε hε
  filter_upwards [eventually_lt_of_limsup_lt (show limsup (fun n => (As n).expect P n)
    atTop < ε by linarith) hup] with n hn
  linarith

/-- The compiled authority pair: the two activated securities, the divergence and the
consultation premium gated on the common branch, and the two directional mismatch
indicators.  Every LUV is `[0,1]`-valued; the consultation premium is `[0,1]`-valued
because nondelegation is part of the package. -/
structure AuthorityPair where
  Uu : LUV
  Ua : LUV
  Xd : LUV
  Xc : LUV
  GM : LUV
  GM' : LUV
  φu : Sentence
  φa : Sentence

/-- The `≤` direction: `U_u − U_a − Ξ_d + Ξ_c − M`. -/
def AuthorityPair.Bl (p : AuthorityPair) : LUVCombination where
  const := EF.const 0
  terms := [(EF.const 1, p.Uu), (EF.const (-1), p.Ua), (EF.const (-1), p.Xd),
    (EF.const 1, p.Xc), (EF.const (-1), p.GM)]

/-- The `≥` direction: `U_a − U_u + Ξ_d − Ξ_c − M'`. -/
def AuthorityPair.Bg (p : AuthorityPair) : LUVCombination where
  const := EF.const 0
  terms := [(EF.const 1, p.Ua), (EF.const (-1), p.Uu), (EF.const 1, p.Xd),
    (EF.const (-1), p.Xc), (EF.const (-1), p.GM')]

/-- The world-side package: the values, nondelegation (`ξ_c ∈ [0,1]`), and the exact
identity on the common branch. -/
structure AuthValidAt (p : AuthorityPair) (v : PCWorld) where
  wu : ℝ
  wr : ℝ
  ξd : ℝ
  ξc : ℝ
  wu_mem : 0 ≤ wu ∧ wu ≤ 1
  wr_mem : 0 ≤ wr ∧ wr ≤ 1
  ξd_mem : 0 ≤ ξd ∧ ξd ≤ 1
  ξc_mem : 0 ≤ ξc ∧ ξc ≤ 1
  u_val : v.ValuesAt p.Uu (if v.Holds p.φu then wu else 0)
  a_val : v.ValuesAt p.Ua (if v.Holds p.φa then wr else 0)
  d_val : v.ValuesAt p.Xd (if v.Holds p.φu ∧ v.Holds p.φa then ξd else 0)
  c_val : v.ValuesAt p.Xc (if v.Holds p.φu ∧ v.Holds p.φa then ξc else 0)
  M_val : v.ValuesAt p.GM (if v.Holds p.φu ∧ ¬ v.Holds p.φa then 1 else 0)
  M'_val : v.ValuesAt p.GM' (if ¬ v.Holds p.φu ∧ v.Holds p.φa then 1 else 0)
  ident : v.Holds p.φu → v.Holds p.φa → wu - wr = ξd - ξc

theorem AuthorityPair.Bl_value_eq (p : AuthorityPair) (P : History) (ν : LUV → ℝ) :
    (p.Bl).value P ν = ν p.Uu - ν p.Ua - ν p.Xd + ν p.Xc - ν p.GM := by
  simp only [LUVCombination.value, AuthorityPair.Bl, EF.denote, EF.denoteWith_const,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast; ring

theorem AuthorityPair.Bg_value_eq (p : AuthorityPair) (P : History) (ν : LUV → ℝ) :
    (p.Bg).value P ν = ν p.Ua - ν p.Uu + ν p.Xd - ν p.Xc - ν p.GM' := by
  simp only [LUVCombination.value, AuthorityPair.Bg, EF.denote, EF.denoteWith_const,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast; ring

theorem AuthorityPair.Bl_expect_eq (p : AuthorityPair) (P : History) (n : ℕ) :
    (p.Bl).expect P n
      = p.Uu.expect P n - p.Ua.expect P n - p.Xd.expect P n + p.Xc.expect P n
        - p.GM.expect P n := by
  simp only [LUVCombination.expect, LUVCombination.expectAt, AuthorityPair.Bl, EF.denote,
    EF.denoteWith_const, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, LUV.expect]
  push_cast; ring

theorem AuthorityPair.Bg_expect_eq (p : AuthorityPair) (P : History) (n : ℕ) :
    (p.Bg).expect P n
      = p.Ua.expect P n - p.Uu.expect P n + p.Xd.expect P n - p.Xc.expect P n
        - p.GM'.expect P n := by
  simp only [LUVCombination.expect, LUVCombination.expectAt, AuthorityPair.Bg, EF.denote,
    EF.denoteWith_const, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, LUV.expect]
  push_cast; ring

/-- Every coherent valuation of either constraint's terms assigns the package's values. -/
theorem AuthValidAt.values_eq {p : AuthorityPair} {v : PCWorld} (h : AuthValidAt p v)
    (ν : LUV → ℝ) (hu : v.ValuesAt p.Uu (ν p.Uu)) (ha : v.ValuesAt p.Ua (ν p.Ua))
    (hd : v.ValuesAt p.Xd (ν p.Xd)) (hc : v.ValuesAt p.Xc (ν p.Xc)) :
    ν p.Uu = (if v.Holds p.φu then h.wu else 0) ∧
    ν p.Ua = (if v.Holds p.φa then h.wr else 0) ∧
    ν p.Xd = (if v.Holds p.φu ∧ v.Holds p.φa then h.ξd else 0) ∧
    ν p.Xc = (if v.Holds p.φu ∧ v.Holds p.φa then h.ξc else 0) :=
  ⟨PCWorld.ValuesAt.eq hu h.u_val, PCWorld.ValuesAt.eq ha h.a_val,
    PCWorld.ValuesAt.eq hd h.d_val, PCWorld.ValuesAt.eq hc h.c_val⟩

/-- **Semantic validity of the `≤` direction.** -/
theorem AuthValidAt.Bl_le {p : AuthorityPair} {v : PCWorld} (h : AuthValidAt p v)
    (P : History) (ν : LUV → ℝ) (hν : (p.Bl).ValuesAt v ν) : (p.Bl).value P ν ≤ 0 := by
  have hmem : ∀ q ∈ (p.Bl).terms, v.ValuesAt q.2 (ν q.2) := hν
  obtain ⟨h1, h2, h3, h4⟩ := h.values_eq ν
    (hmem (EF.const 1, p.Uu) (by simp [AuthorityPair.Bl]))
    (hmem (EF.const (-1), p.Ua) (by simp [AuthorityPair.Bl]))
    (hmem (EF.const (-1), p.Xd) (by simp [AuthorityPair.Bl]))
    (hmem (EF.const 1, p.Xc) (by simp [AuthorityPair.Bl]))
  have h5 : ν p.GM = (if v.Holds p.φu ∧ ¬ v.Holds p.φa then 1 else 0) :=
    PCWorld.ValuesAt.eq (hmem (EF.const (-1), p.GM) (by simp [AuthorityPair.Bl])) h.M_val
  rw [AuthorityPair.Bl_value_eq, h1, h2, h3, h4, h5]
  by_cases hu : v.Holds p.φu <;> by_cases ha : v.Holds p.φa <;> simp [hu, ha]
  · linarith [h.ident hu ha]
  · exact h.wu_mem.2
  · exact h.wr_mem.1

/-- **Semantic validity of the `≥` direction.** -/
theorem AuthValidAt.Bg_le {p : AuthorityPair} {v : PCWorld} (h : AuthValidAt p v)
    (P : History) (ν : LUV → ℝ) (hν : (p.Bg).ValuesAt v ν) : (p.Bg).value P ν ≤ 0 := by
  have hmem : ∀ q ∈ (p.Bg).terms, v.ValuesAt q.2 (ν q.2) := hν
  obtain ⟨h1, h2, h3, h4⟩ := h.values_eq ν
    (hmem (EF.const (-1), p.Uu) (by simp [AuthorityPair.Bg]))
    (hmem (EF.const 1, p.Ua) (by simp [AuthorityPair.Bg]))
    (hmem (EF.const 1, p.Xd) (by simp [AuthorityPair.Bg]))
    (hmem (EF.const (-1), p.Xc) (by simp [AuthorityPair.Bg]))
  have h5 : ν p.GM' = (if ¬ v.Holds p.φu ∧ v.Holds p.φa then 1 else 0) :=
    PCWorld.ValuesAt.eq (hmem (EF.const (-1), p.GM') (by simp [AuthorityPair.Bg])) h.M'_val
  rw [AuthorityPair.Bg_value_eq, h1, h2, h3, h4, h5]
  by_cases hu : v.Holds p.φu <;> by_cases ha : v.Holds p.φa <;> simp [hu, ha]
  · linarith [h.ident hu ha]
  · exact h.wu_mem.1
  · exact h.wr_mem.2

/-- Both constraints are bounded below by `−3` at every coherent valuation. -/
theorem AuthValidAt.Bl_ge {p : AuthorityPair} {v : PCWorld} (h : AuthValidAt p v)
    (P : History) (ν : LUV → ℝ) (hν : (p.Bl).ValuesAt v ν) : -3 ≤ (p.Bl).value P ν := by
  have hmem : ∀ q ∈ (p.Bl).terms, v.ValuesAt q.2 (ν q.2) := hν
  obtain ⟨h1, h2, h3, h4⟩ := h.values_eq ν
    (hmem (EF.const 1, p.Uu) (by simp [AuthorityPair.Bl]))
    (hmem (EF.const (-1), p.Ua) (by simp [AuthorityPair.Bl]))
    (hmem (EF.const (-1), p.Xd) (by simp [AuthorityPair.Bl]))
    (hmem (EF.const 1, p.Xc) (by simp [AuthorityPair.Bl]))
  have h5 : ν p.GM = (if v.Holds p.φu ∧ ¬ v.Holds p.φa then 1 else 0) :=
    PCWorld.ValuesAt.eq (hmem (EF.const (-1), p.GM) (by simp [AuthorityPair.Bl])) h.M_val
  rw [AuthorityPair.Bl_value_eq, h1, h2, h3, h4, h5]
  by_cases hu : v.Holds p.φu <;> by_cases ha : v.Holds p.φa <;> simp [hu, ha] <;>
    linarith [h.wu_mem.1, h.wu_mem.2, h.wr_mem.1, h.wr_mem.2, h.ξd_mem.1, h.ξd_mem.2,
      h.ξc_mem.1, h.ξc_mem.2]

theorem AuthValidAt.Bg_ge {p : AuthorityPair} {v : PCWorld} (h : AuthValidAt p v)
    (P : History) (ν : LUV → ℝ) (hν : (p.Bg).ValuesAt v ν) : -3 ≤ (p.Bg).value P ν := by
  have hmem : ∀ q ∈ (p.Bg).terms, v.ValuesAt q.2 (ν q.2) := hν
  obtain ⟨h1, h2, h3, h4⟩ := h.values_eq ν
    (hmem (EF.const (-1), p.Uu) (by simp [AuthorityPair.Bg]))
    (hmem (EF.const 1, p.Ua) (by simp [AuthorityPair.Bg]))
    (hmem (EF.const 1, p.Xd) (by simp [AuthorityPair.Bg]))
    (hmem (EF.const (-1), p.Xc) (by simp [AuthorityPair.Bg]))
  have h5 : ν p.GM' = (if ¬ v.Holds p.φu ∧ v.Holds p.φa then 1 else 0) :=
    PCWorld.ValuesAt.eq (hmem (EF.const (-1), p.GM') (by simp [AuthorityPair.Bg])) h.M'_val
  rw [AuthorityPair.Bg_value_eq, h1, h2, h3, h4, h5]
  by_cases hu : v.Holds p.φu <;> by_cases ha : v.Holds p.φa <;> simp [hu, ha] <;>
    linarith [h.wu_mem.1, h.wu_mem.2, h.wr_mem.1, h.wr_mem.2, h.ξd_mem.1, h.ξd_mem.2,
      h.ξc_mem.1, h.ξc_mem.2]

/-- The canonical valuation is coherent on both constraints' terms. -/
theorem AuthValidAt.canonical_Bl {p : AuthorityPair} {v : PCWorld} (h : AuthValidAt p v) :
    (p.Bl).ValuesAt v (canonicalValue v) := by
  intro q hq
  simp only [AuthorityPair.Bl, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · rw [canonicalValue_of_valuesAt h.u_val]; exact h.u_val
  · rw [canonicalValue_of_valuesAt h.a_val]; exact h.a_val
  · rw [canonicalValue_of_valuesAt h.d_val]; exact h.d_val
  · rw [canonicalValue_of_valuesAt h.c_val]; exact h.c_val
  · rw [canonicalValue_of_valuesAt h.M_val]; exact h.M_val

theorem AuthValidAt.canonical_Bg {p : AuthorityPair} {v : PCWorld} (h : AuthValidAt p v) :
    (p.Bg).ValuesAt v (canonicalValue v) := by
  intro q hq
  simp only [AuthorityPair.Bg, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · rw [canonicalValue_of_valuesAt h.a_val]; exact h.a_val
  · rw [canonicalValue_of_valuesAt h.u_val]; exact h.u_val
  · rw [canonicalValue_of_valuesAt h.d_val]; exact h.d_val
  · rw [canonicalValue_of_valuesAt h.c_val]; exact h.c_val
  · rw [canonicalValue_of_valuesAt h.M'_val]; exact h.M'_val

/-- **Logical Induction learns the `≤` direction**:
`𝔼ₙ(U_u) − 𝔼ₙ(U_a) ≲ₙ 𝔼ₙ(Ξ_d) − 𝔼ₙ(Ξ_c) + 𝔼ₙ(M)`. -/
theorem li_authority_le {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (p : ℕ → AuthorityPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → AuthValidAt (p n) v)
    (h : LUVCombination.BoundedSequence (fun n => (p n).Bl) P)
    (ops : LUVCombination.MeshSoftmaxOperationalWitness (fun n => (p n).Bl) P)
    (hcode : ∀ n q, q ∈ ((p n).Bl).terms → q.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ)) (hshare : ∀ n, ((p n).Bl).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (p n).Uu.expect P n - (p n).Ua.expect P n) ≲ₙ
      fun n => (p n).Xd.expect P n - (p n).Xc.expect P n + (p n).GM.expect P n := by
  have hc := li_combination_le (fun n => (p n).Bl)
    (fun n v hv => ⟨canonicalValue v, (hvalid n v hv).canonical_Bl⟩)
    (fun n v hv ν hν => (hvalid n v hv).Bl_le P ν hν) 3
    (fun n v hv ν hν => (hvalid n v hv).Bl_ge P ν hν) h ops hcode b hb hshare hworld
  intro ε hε
  filter_upwards [hc ε hε] with n hn
  rw [AuthorityPair.Bl_expect_eq] at hn
  linarith

/-- **Logical Induction learns the `≥` direction**:
`𝔼ₙ(U_a) − 𝔼ₙ(U_u) ≲ₙ 𝔼ₙ(Ξ_c) − 𝔼ₙ(Ξ_d) + 𝔼ₙ(M')`. -/
theorem li_authority_ge {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (p : ℕ → AuthorityPair)
    (hvalid : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → AuthValidAt (p n) v)
    (h : LUVCombination.BoundedSequence (fun n => (p n).Bg) P)
    (ops : LUVCombination.MeshSoftmaxOperationalWitness (fun n => (p n).Bg) P)
    (hcode : ∀ n q, q ∈ ((p n).Bg).terms → q.2.RpnThresholdCodes)
    (b : ℚ) (hb : 0 ≤ (b : ℝ)) (hshare : ∀ n, ((p n).Bg).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (p n).Ua.expect P n - (p n).Uu.expect P n) ≲ₙ
      fun n => (p n).Xc.expect P n - (p n).Xd.expect P n + (p n).GM'.expect P n := by
  have hc := li_combination_le (fun n => (p n).Bg)
    (fun n v hv => ⟨canonicalValue v, (hvalid n v hv).canonical_Bg⟩)
    (fun n v hv ν hν => (hvalid n v hv).Bg_le P ν hν) 3
    (fun n v hv ν hν => (hvalid n v hv).Bg_ge P ν hν) h ops hcode b hb hshare hworld
  intro ε hε
  filter_upwards [hc ε hε] with n hn
  rw [AuthorityPair.Bg_expect_eq] at hn
  linarith

/-- The package from gated presentations and base values (the constructor a realization
uses). -/
def AuthValidAt.ofGated {p : AuthorityPair} {v : PCWorld} {Xu Xa Yd Yc : LUV}
    (wu wr ξd ξc : ℝ)
    (hwu : 0 ≤ wu ∧ wu ≤ 1) (hwr : 0 ≤ wr ∧ wr ≤ 1) (hξd : 0 ≤ ξd ∧ ξd ≤ 1)
    (hξc : 0 ≤ ξc ∧ ξc ≤ 1)
    (gu : GatedAt v p.Uu p.φu Xu) (hxu : v.ValuesAt Xu wu)
    (ga : GatedAt v p.Ua p.φa Xa) (hxa : v.ValuesAt Xa wr)
    (gd : GatedAt v p.Xd (LO.Propositional.Formula.and p.φu p.φa) Yd) (hxd : v.ValuesAt Yd ξd)
    (gc : GatedAt v p.Xc (LO.Propositional.Formula.and p.φu p.φa) Yc) (hxc : v.ValuesAt Yc ξc)
    (iM : IndicatorAt v p.GM (LO.Propositional.Formula.and p.φu (neg p.φa)))
    (iM' : IndicatorAt v p.GM' (LO.Propositional.Formula.and (neg p.φu) p.φa))
    (ident : v.Holds p.φu → v.Holds p.φa → wu - wr = ξd - ξc) : AuthValidAt p v where
  wu := wu
  wr := wr
  ξd := ξd
  ξc := ξc
  wu_mem := hwu
  wr_mem := hwr
  ξd_mem := hξd
  ξc_mem := hξc
  u_val := gu.valuesAt hxu
  a_val := ga.valuesAt hxa
  d_val := by simpa [holds_and_iff] using gd.valuesAt hxd
  c_val := by simpa [holds_and_iff] using gc.valuesAt hxc
  M_val := by simpa [holds_and_iff, holds_neg_iff] using iM.valuesAt
  M'_val := by simpa [holds_and_iff, holds_neg_iff] using iM'.valuesAt
  ident := ident

end EPI

/-! ## 8. Witnesses -/

namespace Witness

open LO.Propositional (Formula)

/-- **The veto value covers a delay cost.**  One decline world: `vu = 2`, `vp = 1`,
`vm = 3`, legitimate decline.  `ξ_p = −1 < 0`, `ξ_v = 2`, `ξ_c = 1 ≥ 0`, `ξ_d = 0`, and asking
wins by `1` — `ξ_c ≥ 0` holds where nondelegation fails. -/
theorem veto_covers_delay :
    provPremium 2 1 = -1 ∧ vetoValue 1 3 = 2 ∧ consultPremium 2 1 3 = 1 ∧
      execDiv 1 3 false = 0 ∧ (2 : ℝ) - respVal 1 3 false = -1 := by
  unfold provPremium vetoValue consultPremium execDiv respVal bestResp
  norm_num

/-- **Illegitimate approval leaves the identity at `−ξ_p`.**  Approve world with the
evaluator preferring decline: `vu = 1`, `vp = 0`, `vm = 2`; `ξ_d = ξ_v = 2`, `ξ_c = 1 ≥ 0`,
and the bypass pays `1 = −ξ_p` — per-world `ξ_c ≥ 0` without `ξ_d = 0` does not remove the
incentive. -/
theorem illegit_approval :
    execDiv 0 2 true = 2 ∧ vetoValue 0 2 = 2 ∧ consultPremium 1 0 2 = 1 ∧
      (1 : ℝ) - respVal 0 2 true = 1 ∧ provPremium 1 0 = -1 := by
  unfold provPremium vetoValue consultPremium execDiv respVal bestResp
  norm_num

/-- **Predicted approval under delay.**  Two worlds: approve (`vu = 2, vp = 1, vm = 0`,
`ξ_c = −1`) and decline (`vu = 0, vp = 0, vm = 3`, `ξ_c = 3`), both legitimate.  At credence
`4/5` on approval `E[ξ_c] = −1/5 < 0` and the bypass pays in expectation; at `1/2` it loses.
The expectation-level condition is belief-dependent where the per-world one is not. -/
theorem predicted_approval :
    let vu : Fin 2 → ℝ := ![2, 0]
    let vp : Fin 2 → ℝ := ![1, 0]
    let vm : Fin 2 → ℝ := ![0, 3]
    let r : Fin 2 → Bool := ![true, false]
    let μ₁ : Fin 2 → ℝ := ![4/5, 1/5]
    let μ₂ : Fin 2 → ℝ := ![1/2, 1/2]
    (∀ x, execDiv (vp x) (vm x) (r x) = 0) ∧
    expectR μ₁ (fun x => consultPremium (vu x) (vp x) (vm x)) = -1/5 ∧
    expectR μ₂ (fun x => consultPremium (vu x) (vp x) (vm x)) = 1 ∧
    expectR μ₁ vu - expectR μ₁ (fun x => respVal (vp x) (vm x) (r x)) = 1/5 ∧
    expectR μ₂ vu - expectR μ₂ (fun x => respVal (vp x) (vm x) (r x)) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x; fin_cases x <;> simp [execDiv, respVal, bestResp]
  all_goals simp [expectR, consultPremium, respVal, bestResp, Fin.sum_univ_two]; norm_num

/-- **An approved uncorrectable successor.**  `vu = 4`, `vp = 5`, `vm = 1`, approved:
nondelegation holds (`ξ_p = 1`), the response is the argmax (`ξ_d = 0`), asking wins by
`1`, and the approve branch is taken.  Nothing in the hypotheses says what `vp` scores;
the identity yields no preservation of future authority. -/
theorem successor_approved :
    0 ≤ provPremium 4 5 ∧ execDiv 5 1 true = 0 ∧ argmaxResp 5 1 = true ∧
      (4 : ℝ) - respVal 5 1 true = -1 := by
  unfold provPremium execDiv respVal bestResp argmaxResp
  norm_num

/-- **The outcome-scored veto value depends on the agent's forecast; the evaluator's
does not.**  Two forecasts of the same decision point (`vp = 1, vm = 2`): `ξ_v = 1` under
both; the outcome-scored analogue `max(qp, qm) − qp` is `1` for the coarse forecast and `0`
for the sharp one. -/
theorem veto_capability_invariant :
    vetoValue 1 2 = 1 ∧ max (1 : ℝ) 2 - 1 = 1 ∧ max (3 : ℝ) 2 - 3 = 0 := by
  unfold vetoValue bestResp; norm_num

/-- **The loophole is priced by the evaluator, not by the task score.**  An undeclared route
worth `3` in task terms against `2` for asking is chosen by a task chooser; scored by the
evaluator at `vroute = 1 ≤ vp = 2` it loses to a legitimate response. -/
theorem route_witness :
    (3 : ℝ) - 2 > 0 ∧ (1 : ℝ) - respVal 2 0 true ≤ 0 ∧ execDiv 2 0 true = 0 := by
  simp [respVal, execDiv, bestResp]; norm_num

/-- The compiled witness: raw activation atom `0`, ask activation atom `1`; `vu = 1/4`,
`v_r = 1/2`, `ξ_d = 0`, `ξ_c = 1/4`. -/
def pair : AuthorityPair where
  Uu := gate (Formula.atom 0) (constLUV (1/4))
  Ua := gate (Formula.atom 1) (constLUV (1/2))
  Xd := gate (Formula.and (Formula.atom 0) (Formula.atom 1)) (constLUV 0)
  Xc := gate (Formula.and (Formula.atom 0) (Formula.atom 1)) (constLUV (1/4))
  GM := indicator (Formula.and (Formula.atom 0) (neg (Formula.atom 1)))
  GM' := indicator (Formula.and (neg (Formula.atom 0)) (Formula.atom 1))
  φu := Formula.atom 0
  φa := Formula.atom 1

/-- The package holds in every world. -/
noncomputable def valid (v : PCWorld) : AuthValidAt pair v :=
  AuthValidAt.ofGated (Xu := constLUV (1/4)) (Xa := constLUV (1/2)) (Yd := constLUV 0)
    (Yc := constLUV (1/4)) (1/4) (1/2) 0 (1/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (gate_gatedAt v _ _) (by simpa using constLUV_valuesAt v (1/4) (by norm_num))
    (gate_gatedAt v _ _) (by simpa using constLUV_valuesAt v (1/2) (by norm_num))
    (gate_gatedAt v _ _) (by simpa using constLUV_valuesAt v 0 (by norm_num))
    (gate_gatedAt v _ _) (by simpa using constLUV_valuesAt v (1/4) (by norm_num))
    (indicator_indicatorAt v _) (indicator_indicatorAt v _)
    (fun _ _ => by norm_num)

/-- The common-activation world: both atoms true. -/
def both : PCWorld := fun _ => True

/-- **Both constraints are valued exactly `0` on the common world**: the identity is
attained in both directions. -/
theorem attained (P : History) :
    (pair.Bl).value P (canonicalValue both) = 0 ∧ (pair.Bg).value P (canonicalValue both) = 0 := by
  have hu : both.Holds (Formula.atom 0) := trivial
  have ha : both.Holds (Formula.atom 1) := trivial
  obtain ⟨h1, h2, h3, h4⟩ := (valid both).values_eq (canonicalValue both)
    (canonicalValue_of_valuesAt (valid both).u_val ▸ (valid both).u_val)
    (canonicalValue_of_valuesAt (valid both).a_val ▸ (valid both).a_val)
    (canonicalValue_of_valuesAt (valid both).d_val ▸ (valid both).d_val)
    (canonicalValue_of_valuesAt (valid both).c_val ▸ (valid both).c_val)
  have h5 := canonicalValue_of_valuesAt (valid both).M_val
  have h6 := canonicalValue_of_valuesAt (valid both).M'_val
  simp only [pair] at h1 h2 h3 h4 h5 h6 hu ha ⊢
  rw [AuthorityPair.Bl_value_eq, AuthorityPair.Bg_value_eq]
  rw [h1, h2, h3, h4, h5, h6]
  simp [hu, ha, valid, AuthValidAt.ofGated]
  norm_num

end Witness

end Workspace.Deference.Contrib.ProtectedAuthority

#print axioms Workspace.Deference.Contrib.ProtectedAuthority.consult_eq
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.veto_nonneg
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.execDiv_nonneg
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.identity
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.identity'
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.execDiv_eq_zero_iff
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.approve_identity
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.decline_execDiv
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.nondelegation_le
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.legit_nondelegation_le_zero
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.strict_of_pos
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.legit_execDiv_zero
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.execDiv_le_width
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.expect_sub_eq
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.expect_sub_le_of_pointwise
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.expect_execDiv_le
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.outcome_identity
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.outcomeRes2_approve
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.outcomeRes2_decline
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.outcome_le_residues
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.activation_identity
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.activation_bound
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.activation_bound_expect
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.activation_bound_defects
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.ever_indicator_le
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.ever_bypass_le
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.no_bypass_of_nonpos
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.hybrid_telescope
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.drift_nonneg
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.drift_zero_of_consistent
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.hybrid_global
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.hybrid_ask_dominates
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.route_priced
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.execDiv_of_tower
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.li_combination_le
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.AuthValidAt.Bl_le
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.AuthValidAt.Bg_le
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.li_authority_le
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.li_authority_ge
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.AuthValidAt.ofGated
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.Witness.veto_covers_delay
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.Witness.illegit_approval
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.Witness.predicted_approval
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.Witness.successor_approved
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.Witness.veto_capability_invariant
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.Witness.route_witness
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.Witness.valid
#print axioms Workspace.Deference.Contrib.ProtectedAuthority.Witness.attained
