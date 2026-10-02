import Cleanroom.Decision.DpFirstpersonSc.Stages
import Cleanroom.Decision.DpFirstpersonSc.Audit

/-!
# AN-25 on a tree: the stage problem's audit instance (repair round 1)

`stageTree p` realizes the pre-computation stage of the counterlogical mugging as a tree: a
trivial root query `d` (acts `Unit` — the agent is consulted before the digit is computed), the
digit chance node `digitCoin p` (index `0` is "the digit is 3", `X₃`, probability `p`; index `1`
is "the digit is 7", `X₇`), the fair coin (`FinDistr.uniform` on `Fin 2`); leaf world
`(digit, coin) : StageW`, payoff `0`. Every run consults `d` (`stageTree_occ`), so the audit's
referent at `d` is the prior state, whose `P` is `stagePriorQ p` (`stageTree_priorState_P`,
`occState_agree_priorState_of_occ_univ`). The post-computation state pulled back along the
embedding — `stagePostState`, `P = (½, ½, 0, 0)` (`pushDistr FinDistr.uniform stageEmbed`,
`Stages.lean`) — fails per-run clause 1 at `X₇` for `p < 1`
(`stagePostState_not_perRunClause1`: `0 ≠ 1 − p`), hence fails the audit at `d`
(`stagePostState_fails_audit`, through T1(a)): AN-25's "Def 13× fails exactly as per-run SSC
fails for the tails-certain state", as an `AuditPassAt` instance. The pulled-back state carries
the constant desirability `0` (`State.ofConst`): AN-25 is about the `P`-clause, and the tree's
payoffs are `0`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-- The digit coin: index `0` ("the digit is 3") with probability `p`, index `1` ("the digit is
7") with `1 − p`. Source: `anticipation.md` AN-22′ (`P_{t₀}(X₃) = p`). Kind: D -/
def digitCoin (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinDistr ℚ (Fin 2) where
  w i := if i = 0 then p else 1 - p
  nonneg i := by split_ifs <;> linarith
  sum_one := by rw [Fin.sum_univ_two]; simp

/-- **The stage problem as a tree**: a trivial root query `d` (acts `Unit`), the digit coin, the
fair coin; leaf world `(digit, coin)`, payoff `0`.
Source: `anticipation.md` AN-25 (the counterlogical mugging at the pre-computation stage);
AN-22′ (`P_{t₀}`: digit 3 with probability `p`, fair coin, independent)
Kind: D
Fidelity: variant: the stage problem as a tree with a trivial root query (the audit needs a
queried point; the mugging's own decision is not modelled — AN-25 is about the pulled-back `P`) -/
def stageTree (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Tree StageW Unit (fun _ => Unit) ℚ :=
  .decision () fun _ => .chance 2 (digitCoin p h0 h1) fun i =>
    .chance 2 FinDistr.uniform fun j => .leaf (i, j) 0

section shape

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1)

/-- Leaf sums. Source: none: infrastructure. Kind: L -/
theorem stageTree_sum {M : Type} [AddCommMonoid M] (f : (stageTree p h0 h1).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ j : Fin 2, f ⟨(), i, j, ()⟩ := by
  unfold stageTree at f ⊢
  rw [sum_leaves_decision, Fintype.sum_unique, sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The one-act procedure puts weight `1` on its act. Source: none: infrastructure. Kind: L -/
theorem proc_unit_w (C : Proc Unit (fun _ => Unit) ℚ) : (C ()).w () = 1 := by
  have := (C ()).sum_one
  rwa [Fintype.sum_unique] at this

/-- The leaf law. Source: none: infrastructure. Kind: L -/
theorem stageTree_leafLaw (C : Proc Unit (fun _ => Unit) ℚ) (i j : Fin 2) :
    leafLaw C (stageTree p h0 h1) ⟨(), i, j, ()⟩ =
      (C ()).w () * ((digitCoin p h0 h1).w i * ((FinDistr.uniform : FinDistr ℚ (Fin 2)).w j * 1)) := by
  unfold stageTree
  simp only [leafLaw_decision, leafLaw_chance, leafLaw_leaf]

/-- The world. Source: none: infrastructure. Kind: L -/
theorem stageTree_world (i j : Fin 2) : world (stageTree p h0 h1) ⟨(), i, j, ()⟩ = (i, j) := by
  unfold stageTree; simp [world_decision, world_chance, world_leaf]

/-- `#_d = 1` on every leaf. Source: none: infrastructure. Kind: L -/
theorem stageTree_count (i j : Fin 2) : count () (stageTree p h0 h1) ⟨(), i, j, ()⟩ = 1 := by
  unfold stageTree; simp [count_decision, count_chance, count_leaf]

/-- `occ(d) = ⊤`: every run consults the root query. Source: none: infrastructure. Kind: L -/
theorem stageTree_occ : occ () (stageTree p h0 h1) = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro ℓ
  rw [mem_occ]
  obtain ⟨⟨⟩, i, j, ⟨⟩⟩ := ℓ
  rw [stageTree_count]; exact Nat.one_pos

/-- `ν_C = stagePriorQ p` on the stage tree, for every self-model `C` (the root query has one
act). Source: `anticipation.md` AN-22′ (`P_{t₀}`). Kind: L -/
theorem stageTree_nu (C : Proc Unit (fun _ => Unit) ℚ) (X : Finset StageW) :
    nu C (stageTree p h0 h1) X = probOf (stagePriorQ p h0 h1) X := by
  rw [nu_eq_sum, stageTree_sum]
  simp only [stageTree_world, stageTree_leafLaw, proc_unit_w, one_mul, mul_one]
  rw [probOf, ← Finset.univ_inter X, ← Finset.sum_ite_mem, Fintype.sum_prod_type]
  simp only [Finset.mem_inter, Finset.mem_univ, true_and]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [digitCoin, stagePriorQ, FinDistr.uniform_w, div_eq_mul_inv]

/-- **The prior state on the stage tree is `stagePriorQ p`** — the audit's referent at `d`
(`occ(d) = ⊤`, `occState_agree_priorState_of_occ_univ`).
Source: `anticipation.md` AN-22′, AN-25. Kind: L -/
theorem stageTree_priorState_P (C : Proc Unit (fun _ => Unit) ℚ) :
    (priorState C (stageTree p h0 h1)).P = stagePriorQ p h0 h1 := by
  apply FinDistr.ext'
  intro w
  have := priorState_pr C (stageTree p h0 h1) {w}
  simp only [State.pr, probOf_singleton] at this
  rw [this, stageTree_nu, probOf_singleton]

/-- `P_{t₀}(X₇) = 1 − p`. Source: `anticipation.md` AN-22′. Kind: L -/
theorem stagePriorQ_X7 : probOf (stagePriorQ p h0 h1) X7 = 1 - p := by
  show (∑ w ∈ X7, (if w.1 = 0 then p else 1 - p) / 2) = 1 - p
  rw [X7, Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

end shape

/-- The pulled-back post-computation state `(½, ½, 0, 0)` gives `X₇` probability `0`.
Source: `anticipation.md` AN-25. Kind: L -/
theorem stagePost_X7 :
    probOf (pushDistr (FinDistr.uniform : FinDistr ℚ (Fin 2)) stageEmbed) X7 = 0 := by
  rw [probOf, X7, Finset.sum_filter, Fintype.sum_prod_type]
  simp [pushDistr_uniform_stageEmbed]

/-- **The post-computation state pulled back along the embedding, as a state on the stage
carrier**: `P = (½, ½, 0, 0)`, desirability `0` (the tree's payoffs are `0`; AN-25 is about `P`).
Source: `anticipation.md` AN-25 ("the post-computation state pulled back to `𝓔_{t₀}` is
`(½, ½, 0, 0)`")
Kind: D
Fidelity: exact on `P`; `V ≡ 0` is the tree's payoff -/
noncomputable def stagePostState : State StageW ℚ :=
  State.ofConst (pushDistr (FinDistr.uniform : FinDistr ℚ (Fin 2)) stageEmbed) 0

section audit

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1)

/-- **AN-25 on the stage tree: the pulled-back post-computation state fails per-run clause 1 at
`d`** for `p < 1`: at `X₇`, `P(X₇) · μ(occ(d)) = 0` against `μ(λ⁻¹X₇ ∩ occ(d)) = ν(X₇) = 1 − p`.
Source: `anticipation.md` AN-25 ("Def 13× fails exactly as per-run SSC fails for the
tails-certain state"); audit r1 adversarial N5
Kind: N+
Fidelity: exact (the stage problem as `stageTree`; the self-model `C : Proc Unit (fun _ => Unit) ℚ`
is the unique one — one point, one act, `proc_unit_w`)
Hyps: (a) `p < 1` -/
theorem stagePostState_not_perRunClause1 (hp : p < 1) (C : Proc Unit (fun _ => Unit) ℚ) :
    ¬ PerRunClause1At (fun _ => stagePostState) C (stageTree p h0 h1) () := by
  intro hc
  have := hc X7
  rw [stageTree_occ, mass_univ, mul_one, Finset.inter_univ] at this
  change probOf (pushDistr (FinDistr.uniform : FinDistr ℚ (Fin 2)) stageEmbed) X7 =
    nu C (stageTree p h0 h1) X7 at this
  rw [stagePost_X7, stageTree_nu, stagePriorQ_X7] at this
  linarith

/-- The stage tree's occurrence guard on the stamped prior (`occ(d) = ⊤`).
Source: none: infrastructure. Kind: L -/
theorem stageTree_stamp_occ_pos (C : Proc Unit (fun _ => Unit) ℚ) :
    0 < (priorState C (stamp {()} (stageTree p h0 h1))).pr
      (occW {()} (Finset.mem_singleton_self ())) := by
  rw [priorState_stamp_pr_occW, stageTree_occ, mass_univ]; exact zero_lt_one

/-- **AN-25 as an audit verdict**: on the stage tree the pulled-back post-computation state
fails the audit at `d` for `p < 1` (T1(a) applied to `stagePostState_not_perRunClause1`) — the
counterlogical mugging is the no-doubt mugging under the quotient, and it fails the audit as the
tails-certain state does on `B₁` (`mug1_tailsCertain_fails_audit'`). What the audit adds here:
nothing beyond the prior-identity check — at `occ(d) = ⊤` the strict-grade audit against the
stamped prior is agreement with the base prior state (`audit_iff_agree_priorState_of_occ_univ`,
`Audit.lean`), so this is `stage_pullback_ne_prior` generalized in `p` and routed through T1(a).
As an audit instance it is degenerate (one act, payoffs `0`, `occ = ⊤`, the `V`-clause trivial on
both sides); as a witness of AN-25's sentence it is the whole content (audit r2 adversarial N1,
fidelity N2).
Source: `anticipation.md` AN-25; audit r1 adversarial N5
Kind: N+ for AN-25's `P`-clause; N− as an audit instance (one act, payoffs `0`, `occ = ⊤`)
Fidelity: exact (the stage problem as `stageTree`; the referent is the prior state with
`P = stagePriorQ p`, `stageTree_priorState_P`; the self-model is the unique one)
Hyps: (a) `p < 1` -/
theorem stagePostState_fails_audit (hp : p < 1) (C : Proc Unit (fun _ => Unit) ℚ) :
    ¬ AuditPassAt (priorState C (stamp {()} (stageTree p h0 h1)))
      (occW {()} (Finset.mem_singleton_self ())) (stageTree_stamp_occ_pos p h0 h1 C) Prod.fst
      stagePostState := by
  rw [audit_iff_perRunClausesAt C (stageTree p h0 h1) {()} (Finset.mem_singleton_self ())
    (fun _ => stagePostState) (stageTree_stamp_occ_pos p h0 h1 C)]
  rintro ⟨hc1, -⟩
  exact stagePostState_not_perRunClause1 p h0 h1 hp C hc1

end audit

end Cleanroom.Decision.DpFirstpersonSc
