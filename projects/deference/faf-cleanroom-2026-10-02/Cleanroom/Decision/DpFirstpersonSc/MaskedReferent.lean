import Cleanroom.Decision.DpFaithfulUdt.PiB
import Cleanroom.Decision.DpFirstpersonSc.Audit
import Cleanroom.Decision.DpFirstpersonSc.WitnessesLicense

/-!
# T13(b): the masked referent on the sequential Stag Hunt (FP-21′(ii))

The masked grades of the audit are the choices `s₀ = priorState (C.deviate d m) (stamp U B)`
(masked-local, Definition 9's `.LF`) and `s₀ = priorState C' (stamp U B)` with `C'` of full
support (masked-global, `.GF`). FP-21′(ii) says the first is the admissible masked referent and
the second is not, generalizing from one example and marked UNREVIEWED in the source; the
mandate asks for the instance only. On `dp-faithful-udt`'s strongly fair sequential Stag Hunt
`seqStag` under `(H, H∣S, H∣H)` at the root `d₁` (`occ(d₁) = ⊤` — `seqStag_occ_d1` — so the
referent, which is the per-run state by T1(a) (`pushState_fst_auditRef_stamp_agree`), is the
masked prior state on every event, `occState_agree_priorState_of_occ_univ`; the per-run-state
form of the two cells is `seqStag_local_mask_occState_V`/`seqStag_global_mask_occState_V`):

* **the local mask reproduces Theorem 2's evaluator**: for every full-support `m`,
  `V_{s₀_L}(first = S) = 0` and `V_{s₀_L}(first = H) = 1` — the continuation values of the
  agent's own continuation `(H∣S, H∣H)` (`stagCont_value`, `seqStag_local_mask_V`);
* **the global full-support mask misstates the continuation**: under the uniform self-model
  `V_{s₀_G}(first = S) = 1` and `V_{s₀_G}(first = H) = ½` (`seqStag_global_mask_V`) — the
  continuation is played by the mask, not by the agent;
* **the local mask at `d_{2S}` is undefined**: `μ_{C[d_{2S} ↦ m]}(occ(d_{2S})) = 0` for every
  `m` (`seqStag_local_mask_d2S_undefined`; `dp-faithful-udt`'s `seqStag_pdc_undefined_d2S` is
  the pure case), so the masked-local audit's guard fails there, while the global mask gives
  `d_{2S}` positive mass (`seqStag_global_mask_d2S_pos`) and audits a point the agent never
  reaches.

The general claim "the global mask is never an admissible referent" is stated nowhere here
(finding F20: checked on one example, as the source's UNREVIEWED mark warrants).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-- The first-act event `{first = a}` on the Stag Hunt worlds. Source: `firstperson.md`
FP-21′(ii) ("the continuation at `d₁`"). Kind: D -/
def stagFirst (a : Act2) : Finset MiniW := Finset.univ.filter fun w => w.1 = a

/-- The uniform self-model on the three points (a global full-support mask, `.GF`).
Source: `firstperson.md` FP-21′(ii) ("Definition 11's global mask"). Kind: D -/
def stagUnif : Proc StagPt (fun _ => Act2) ℚ := fun _ => FinDistr.uniform

/-- The continuation subtree of `seqStag` below the first act `a`. Source: none: infrastructure.
Kind: D -/
def stagCont (a : Act2) : Tree MiniW StagPt (fun _ => Act2) ℚ :=
  .decision (stage2 a) fun b => .leaf (a, b) (stagPay a b)

/-- `seqStag` is the root decision over its continuations. Source: none: infrastructure.
Kind: L -/
theorem seqStag_eq : seqStag = .decision .d1 stagCont := rfl

/-- **Theorem 2's evaluator at `d₁`**: the continuation values of `(H∣S, H∣H)` are `0` after `S`
and `1` after `H`. Source: `firstperson.md` FP-21′(ii) ("Theorem 2's evaluator on-path").
Kind: L -/
theorem stagCont_value (a : Act2) : value profHHH (stagCont a) = stagPay a .b := by
  cases a <;> simp [stagCont, DpFairnessReloc.value_decision, Proc.ofFun, stage2, stagPay]

/-- `occ(d₁) = ⊤` on `seqStag`: the root carries `d₁`. Source: none: infrastructure. Kind: L -/
theorem seqStag_occ_d1 : occ .d1 seqStag = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro ℓ
  rw [mem_occ]
  obtain ⟨x, y, ⟨⟩⟩ := ℓ
  cases x <;> simp [seqStag, count_decision, stage2]

/-- `μ_C(occ(d₁)) = 1 > 0` on `seqStag` for every `C`. Source: none: infrastructure. Kind: L -/
theorem seqStag_occ_d1_pos (C : Proc StagPt (fun _ => Act2) ℚ) :
    0 < mass C seqStag (occ .d1 seqStag) := by
  rw [seqStag_occ_d1, mass_univ]; exact zero_lt_one

/-- **The local mask reproduces Theorem 2's evaluator**: under `(H, H∣S, H∣H)[d₁ ↦ m]` with `m`
of full support, the masked prior state's desirability of `{first = S}` is `0` and of
`{first = H}` is `1` — the agent's own continuation values (`stagCont_value`). The masked prior
state is the audit's referent at `d₁` because `occ(d₁) = ⊤` (`seqStag_local_mask_occState_V`).
Source: `firstperson.md` FP-21′(ii) ("Definition 9's local mask equals Theorem 2's evaluator
on-path")
Kind: N+
Fidelity: exact (one tree, every full-support `m`)
Hyps: (a) `m` full-support -/
theorem seqStag_local_mask_V (m : FinDistr ℚ Act2) (hm : ∀ a, 0 < m.w a) :
    (priorState (profHHH.deviate .d1 m) seqStag).V (stagFirst .a) = 0 ∧
    (priorState (profHHH.deviate .d1 m) seqStag).V (stagFirst .b) = 1 := by
  have hb := (hm .b).ne'
  constructor <;>
  · rw [priorState_V, paySum_eq_sum_ite, nu_eq_sum, seqStag_sum, seqStag_sum]
    simp [seqStag, leafLaw_decision, world_decision, payoff_decision, Act2.sum_univ, stage2,
      stagPay, stagFirst, Proc.ofFun, hb]

/-- **The local-mask referent itself**: the per-run state at `d₁` under `C[d₁ ↦ m]` — the
pushed-down audit referent by T1(a) — has the same two desirabilities (`occ(d₁) = ⊤`,
`occState_V_eq_priorState_V_of_occ_univ`).
Source: `firstperson.md` FP-21′(ii), D7′; audit r1 fidelity N1
Kind: N+
Fidelity: exact (one tree, every full-support `m`)
Hyps: (a) `m` full-support -/
theorem seqStag_local_mask_occState_V (m : FinDistr ℚ Act2) (hm : ∀ a, 0 < m.w a) :
    (occState (profHHH.deviate .d1 m) seqStag .d1 (seqStag_occ_d1_pos _)).V (stagFirst .a) = 0 ∧
    (occState (profHHH.deviate .d1 m) seqStag .d1 (seqStag_occ_d1_pos _)).V (stagFirst .b) = 1 := by
  rw [occState_V_eq_priorState_V_of_occ_univ _ _ _ seqStag_occ_d1,
    occState_V_eq_priorState_V_of_occ_univ _ _ _ seqStag_occ_d1]
  exact seqStag_local_mask_V m hm

/-- **The global full-support mask misstates the continuation**: under the uniform self-model
the masked prior state's desirability of `{first = S}` is `1` and of `{first = H}` is `½` — the
continuation is the mask's `(½, ½)`, not the agent's `(H∣S, H∣H)`. The masked prior state is the
audit's referent at `d₁` because `occ(d₁) = ⊤` (`seqStag_global_mask_occState_V`).
Source: `firstperson.md` FP-21′(ii) ("the global mask misstates the continuation at `d₁`:
`(1, ½)` vs `(0, 1)`")
Kind: N+
Fidelity: exact (one instance; the generalization is UNREVIEWED in the source — F20) -/
theorem seqStag_global_mask_V :
    (priorState stagUnif seqStag).V (stagFirst .a) = 1 ∧
    (priorState stagUnif seqStag).V (stagFirst .b) = 1 / 2 := by
  constructor <;>
  · rw [priorState_V, paySum_eq_sum_ite, nu_eq_sum, seqStag_sum, seqStag_sum]
    simp [seqStag, leafLaw_decision, world_decision, payoff_decision, Act2.sum_univ, stage2,
      stagPay, stagFirst, stagUnif, act2_card]

/-- **The global-mask referent itself**: the per-run state at `d₁` under the uniform self-model
has the same two desirabilities (`occ(d₁) = ⊤`).
Source: `firstperson.md` FP-21′(ii); audit r1 fidelity N1
Kind: N+
Fidelity: exact (one instance) -/
theorem seqStag_global_mask_occState_V :
    (occState stagUnif seqStag .d1 (seqStag_occ_d1_pos _)).V (stagFirst .a) = 1 ∧
    (occState stagUnif seqStag .d1 (seqStag_occ_d1_pos _)).V (stagFirst .b) = 1 / 2 := by
  rw [occState_V_eq_priorState_V_of_occ_univ _ _ _ seqStag_occ_d1,
    occState_V_eq_priorState_V_of_occ_univ _ _ _ seqStag_occ_d1]
  exact seqStag_global_mask_V

/-- **The local mask at `d_{2S}` is undefined for every `m`**: deviating at `d_{2S}` does not
change the root's `H`, so `μ(occ(d_{2S})) = 0` and the masked-local audit's guard fails
(occurrence constancy; the pure case is `dp-faithful-udt`'s `seqStag_pdc_undefined_d2S`).
Source: `firstperson.md` FP-21′(ii) ("undefined at `d_{2S}`"); dp-cf-113
Kind: N+
Fidelity: exact -/
theorem seqStag_local_mask_d2S_undefined (m : FinDistr ℚ Act2) :
    mass (profHHH.deviate .d2S m) seqStag (occ .d2S seqStag) = 0 := by
  rw [occurrence_constancy, seqStag_occ_d2S_null]

/-- **The global mask gives `d_{2S}` positive mass**: `μ_{unif}(occ(d_{2S})) = ½`, so the
masked-global audit is *defined* at a point the agent never reaches — its referent there is the
mask's own play. Source: `firstperson.md` FP-21′(ii). Kind: N+ -/
theorem seqStag_global_mask_d2S_pos : mass stagUnif seqStag (occ .d2S seqStag) = 1 / 2 := by
  rw [mass_eq_sum_ite', seqStag_sum]
  have c : ∀ a b : Act2, count .d2S seqStag ⟨a, b, ()⟩ = if a = .a then 1 else 0 := by
    intro a b; cases a <;> simp [seqStag, count_decision, stage2]
  simp only [mem_occ, c]
  simp [seqStag, leafLaw_decision, Act2.sum_univ, stagUnif, act2_card]

end Cleanroom.Decision.DpFirstpersonSc
