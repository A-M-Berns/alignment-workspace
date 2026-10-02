import Cleanroom.Udt.UdtCommTrust.Advice
import Cleanroom.Udt.UdtCommTrust.Count
import Mathlib.Tactic.FinCases

/-!
# `Cleanroom.Udt.UdtCommTrust.Witness`: `W2`, the two-instance concrete decision structure

Work package `udt-comm-trust`, the package's N+ generator (mandate T3, T6, T13(d)). `W2` has two
instances, a per-instance message (independent in support, correlated in law: both messages agree
with weight `3 : 1`), four chosen policies in the prior (`follow` the message; `anti`, which follows
at instance `0` and flips at instance `1`; `anti'`, the mirror image; `flip` at both — the last with
weight `1 : 3` against the others, so that every combination of instance policies is in the support
while the law still makes following strictly best), and an environment holding the *other*
instance's action as a free coordinate `a` that copies the agent's own external policy at the other
observation with weight `3 : 1`. Utility `1` iff the focal action equals the other instance's action.

Design constraints, all forced by the abstract structure (findings, T8′):
* the other instance's action must be a *free* environment coordinate — if it were the function
  `Π̈(1 − ö)` of the agent's dynamics, `B` and `E` would share it and `B ∨ E = (Ö, Ä)` would fail;
* it must be correlated with the agent only through `Π̈` — a copy of the *recommendation* would
  correlate `E` with `D_I` and break decision-determination;
* the recommendation tuple must factor by instance (`FactorsAsFam R`) for Advice-Following, hence
  per-instance messages; the chosen-policy family must factor by instance (`InstanceFactored`),
  hence the fourth policy.

Worlds: `((m, k), (ö, a))` with `m : Fin 2 × Fin 2` the two messages, `k : Fin 4` the policy,
`ö : Fin 2` the focal instance, `a : Fin 2` the other instance's action; weight
`(3 if m₀ = m₁ else 1) · (1 if k = 3 else 3) · (3 if a = Π̈(ö+1) else 1)`, total `640`.

Every numeric check is a natural-number count identity or inequality proved by `decide +kernel`
(kernel evaluation; no `native_decide`) and lifted to `ℝ` through `Count.lean`.
-/

set_option maxHeartbeats 1000000

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc Finset

namespace W2

/-- The world type of `W2`.
Source: none: infrastructure (mandate T13(d))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := ((Fin 2 × Fin 2) × Fin 4) × (Fin 2 × Fin 2)

/-- The message at an instance.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pick (m : Fin 2 × Fin 2) (e : Fin 2) : Fin 2 := if e = 0 then m.1 else m.2

/-- The four chosen policies: `0` follows the message, `1` flips it at instance `1`, `2` flips it
at instance `0`, `3` flips it at both.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol (k : Fin 4) (x : Fin 2) (e : Fin 2) : Fin 2 :=
  if k = 0 then x else if k = 1 then (if e = 0 then x else x + 1)
    else if k = 2 then (if e = 0 then x + 1 else x) else x + 1

/-- The messages `m` of a world.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def msg (ω : Ω) : Fin 2 × Fin 2 := ω.1.1

/-- The policy index `k` of a world.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def kk (ω : Ω) : Fin 4 := ω.1.2

/-- The focal instance `ö` of a world.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def foc (ω : Ω) : Fin 2 := ω.2.1

/-- The other instance's action `a` in a world.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def oth (ω : Ω) : Fin 2 := ω.2.2

/-- The focal external action `Ä = pol k (m ö) ö`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def act (ω : Ω) : Fin 2 := pol (kk ω) (pick (msg ω) (foc ω)) (foc ω)

/-- The external policy `Π̈` computed: `ö ↦ pol k (m ö) ö`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polC (ω : Ω) : Fin 2 → Fin 2 := fun e => pol (kk ω) (pick (msg ω) e) e

/-- The chosen (= effective) policy computed: `(ȯ, ö) ↦ (0, pol k (ȯ ö) ö)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polSC (ω : Ω) : Policy ((Fin 2 × Fin 2) × Fin 2) (Fin 1 × Fin 2) :=
  fun oe => (0, pol (kk ω) (pick oe.1 oe.2) oe.2)

/-- "The other instance's action copies the agent's policy at the other observation."
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def good (ω : Ω) : Prop := oth ω = polC ω (foc ω + 1)

instance (ω : Ω) : Decidable (good ω) := by unfold good; infer_instance

/-- The integer weights of `W2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt ω := (if (msg ω).1 = (msg ω).2 then 3 else 1) * (if kk ω = 3 then 1 else 3) *
    (if good ω then 3 else 1)
  pos ω := by
    show 0 < (if (msg ω).1 = (msg ω).2 then 3 else 1) * (if kk ω = 3 then 1 else 3) *
      (if good ω then 3 else 1)
    split_ifs <;> norm_num
  N := 640
  sum_eq := by decide +kernel

/-- The utility as a `{0,1}` indicator: `1` iff the focal action equals the other instance's action.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Q (ω : Ω) : Prop := act ω = oth ω

instance (ω : Ω) : Decidable (Q ω) := by unfold Q; infer_instance

/-- **`W2` as an abstract decision structure.** Every factorization field is discharged by an
explicit mixing function and `decide +kernel`; `IB_common` by hand; `BE_common` by a two-step chain.
Source: mandate T3 (the package's N+ generator)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 2 × Fin 2) (Fin 2) (Fin 1) (Fin 2) (Fin 2 × Fin 2)
    (Fin 2 × Fin 2) (Fin 4) (Fin 2 × Fin 2) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI := msg
  oE := foc
  aI _ := 0
  aE := act
  dI := msg
  dE ω := (foc ω, oth ω)
  dB := kk
  oH := msg
  oC _ := 0
  polS := polSC
  U ω := if Q ω then 1 else 0
  U_mem ω := by
    split_ifs <;> simp
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step
    (fun _ _ h => by rw [(Prod.mk.inj h).2])
    (fun _ _ h => by rw [(Prod.mk.inj (Prod.mk.inj h).1).1])
    (fun _ _ h => Or.inl (by rw [(Prod.mk.inj h).1]))
  BE_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω ω' => ((msg ω, kk ω), (foc ω, oth ω'))) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun (fun ω₁ ω₂ => (((act ω₁, act ω₁), 0), (foc ω₂, oth ω₂)))
    (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((msg ω₁, kk ω₂), (foc ω₁, oth ω₁))) (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((msg ω₂, kk ω₂), (foc ω₁, 0))) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((msg ω₁, 0), (foc ω₂, 0))) (by decide +kernel)
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **`W2` as a concrete decision structure**: each instance's semantics recommend that instance's
message; the side channel never forces.
Source: mandate T8, T13(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : ConcreteDS Ω (Fin 2 × Fin 2) (Fin 2) (Fin 1) (Fin 2) (Fin 2 × Fin 2)
    (Fin 2 × Fin 2) (Fin 4) (Fin 2 × Fin 2) (Fin 1) where
  toAbstractDS := absDS
  s e h := some (pick h e)
  p _ _ := none

/-! ### Computable descriptions of the derived objects -/

/-- **`Π̈` on `W2` is `polC`** (through `polE_eq_of`, past the `Classical.choose` in `rho`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = polC ω :=
  S.polE_eq_of polC (by decide +kernel) (by decide +kernel) (by decide +kernel) ω

/-- Supporting lemma `polOf_eq`: `[[d]]_Π̈` computed.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : (Fin 2 × Fin 2) × Fin 4) :
    S.polOf d = fun e => pol d.2 (pick d.1 e) e :=
  polE_eq ((d, (0, 0)) : Ω)

/-- Supporting lemma `projOH_eq`: `[[·]]_Ô` is the identity on `W2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projOH_eq (o : Fin 2 × Fin 2) : S.projOH o = o := S.projOH_oI (((o, 0), (0, 0)) : Ω)

/-- **`Π†` on `W2` is the chosen policy** (no side channel ever forces).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq (ω : Ω) : S.polD ω = polSC ω := by
  funext oe
  have h1 := S.projAI_B (((oe.1, kk ω), (oe.2, 0)) : Ω)
  have h2 := S.projAE_B (((oe.1, kk ω), (oe.2, 0)) : Ω)
  show (S.projAI (oe, kk ω), S.projAE (oe, kk ω)) = _
  exact Prod.ext h1 h2

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 2 → Fin 2) : S.evPolE π = event fun ω => polC ω = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- Supporting lemma `ev_E_polE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ev_E_polE_eq (e : Fin 2 × (Fin 2 × Fin 2)) (d : (Fin 2 × Fin 2) × Fin 4) :
    (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) =
      event fun ω => S.E ω = e ∧ polC ω = fun e' => pol d.2 (pick d.1 e') e' :=
  event_congr fun ω => by rw [polE_eq, polOf_eq]

/-- Supporting lemma `forall_fun2`: a universal over `Fin 2 → α` is a universal over two values.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem forall_fun2 {α : Type} {P : (Fin 2 → α) → Prop}
    (h : ∀ x y : α, P fun e => if e = 0 then x else y) : ∀ r, P r := fun r => by
  have : r = fun e => if e = 0 then r 0 else r 1 := by
    funext e
    fin_cases e <;> rfl
  rw [this]
  exact h _ _

/-! ### The checks -/

/-- **`W2` is decision-determined**, non-trivially: `(m, k) ↦ Π̈` is 16-to-4.
Source: mandate T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined : S.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · have h1 : act ω = act ω' := (Prod.mk.inj h).1
    have h2 : oth ω = oth ω' := (Prod.mk.inj (Prod.mk.inj h).2).2
    show (if Q ω then (1 : ℝ) else 0) = if Q ω' then 1 else 0
    have hq : Q ω ↔ Q ω' := by unfold Q; rw [h1, h2]
    exact if_congr hq rfl rfl
  · rw [ev_E_polE_eq, evPolE_eq, polOf_eq]
    exact weights.mass_mul_eq_of_cnt (by revert e d; decide +kernel)

/-- **`Π* ⊑ D_{I,B}` on `W2`.**
Source: mandate T7, T10 (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem polS_sub : IsSubvariable S.DIB S.polS := by decide +kernel

/-- **`R ⊑ D_{I,B}` on `W2`.**
Source: mandate T10 (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem R_sub_DIB : IsSubvariable S.DIB S.R := by decide +kernel

/-- Supporting: every chosen-action event at every input is attained on `W2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_nonempty (o : Fin 2 × Fin 2) (e : Fin 2) (ai : Fin 1) (a : Fin 2) :
    (S.evS o e (ai, a)).Nonempty :=
  weights.nonempty_of_cnt_pos (by revert o e ai a; decide +kernel)

/-- **`W2` has internally-driven recommendations, in the unguarded junk-`0` form** (every action
is attained at every input, so the guard is void).
Source: mandate T13(d) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem internallyDrivenJunk : S.InternallyDrivenJunk := by
  intro o e ai a a'
  apply forall_fun2
  intro x y
  exact weights.condProbJunk_eq_of_cnt (evS_nonempty o e ai a) (evS_nonempty o e ai a')
    (by revert o e ai a a' x y; decide +kernel)

/-- **`W2` has internally-driven recommendations** (the guarded definition of record).
Source: mandate T13(d) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem internallyDriven : S.InternallyDriven := internallyDrivenJunk.toInternallyDriven

/-- **Every realized recommendation is stable in the told form on `W2`**, with a strict gap
`1/2 > 7/16` and both conditioning events non-empty.
Source: mandate T13(d) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem stableR : ∀ r ∈ Set.range S.R, S.StableR r := by
  rintro r ⟨ω₀, rfl⟩ e a₀ hra o ho ai a' ha'
  rw [projOH_eq] at ho
  have key : ∀ (m : Fin 2 × Fin 2) (e a₀ : Fin 2) (o : Fin 2 × Fin 2) (ai : Fin 1) (a' : Fin 2),
      some (pick m e) = some a₀ → some (pick o e) = some a₀ → a' ≠ a₀ →
      0 < weights.cnt (S.evS o e (ai, a₀) ∩ S.evToldMinus (fun e => some (pick m e)) e) ∧
      0 < weights.cnt (S.evS o e (ai, a') ∩ S.evToldMinus (fun e => some (pick m e)) e) ∧
      weights.cnt ((S.evS o e (ai, a') ∩ S.evToldMinus (fun e => some (pick m e)) e).filter Q) *
          weights.cnt (S.evS o e (ai, a₀) ∩ S.evToldMinus (fun e => some (pick m e)) e) <
        weights.cnt ((S.evS o e (ai, a₀) ∩ S.evToldMinus (fun e => some (pick m e)) e).filter Q) *
          weights.cnt (S.evS o e (ai, a') ∩ S.evToldMinus (fun e => some (pick m e)) e) := by
    decide +kernel
  obtain ⟨h1, h2, h3⟩ := key (msg ω₀) e a₀ o ai a' hra ho ha'
  exact weights.condExpJunk_indicator_lt Q (weights.nonempty_of_cnt_pos h2)
    (weights.nonempty_of_cnt_pos h1) h3 (-1)

/-- **The recommendation tuple factors by instance on `W2`.**
Source: mandate T13(d) (witness; the instance factorization of `Ȯ`)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem R_fam : FactorsAsFam S.R :=
  factorsAsFam_of_fun (fun c => (((pick (msg (c 0)) 0, pick (msg (c 1)) 1), 0), (0, 0)))
    fun c i => by fin_cases i <;> rfl

/-- The policy index whose instance-`0` component is `k₀`'s and instance-`1` component is `k₁`'s.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def combine (k₀ k₁ : Fin 4) : Fin 4 :=
  (if k₀ = 2 ∨ k₀ = 3 then 2 else 0) + (if k₁ = 1 ∨ k₁ = 3 then 1 else 0)

/-- **The chosen and effective policies factor by instance on `W2`** (`InstanceFactored`).
Source: mandate T8 (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem instanceFactored : S.InstanceFactored := by
  have hfam : FactorsAsFam fun (ω : Ω) e => fun o => polSC ω (o, e) := by
    refine factorsAsFam_of_fun (fun c => (((0, 0), combine (kk (c 0)) (kk (c 1))), (0, 0))) ?_
    apply forall_fun2
    decide +kernel
  refine ⟨hfam, ?_⟩
  have : (fun (ω : Ω) e => fun o => S.polD ω (o, e)) = fun ω e => fun o => polSC ω (o, e) := by
    funext ω e o
    rw [polD_eq]
  rw [this]
  exact hfam

/-- **The policy utility is not constant across external policies on `W2`**: following-type
policies score strictly more than the mixed ones, so T6 is not `c = c` here.
Source: mandate T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem policyUtility_lt : S.policyUtility (fun e => e) < S.policyUtility (fun _ => 0) := by
  unfold AbstractDS.policyUtility
  rw [evPolE_eq, evPolE_eq]
  exact weights.condExpJunk_indicator_lt Q (weights.nonempty_of_cnt_pos (by decide +kernel))
    (weights.nonempty_of_cnt_pos (by decide +kernel)) (by decide +kernel) (-1)

/-- **The Advice-Following gap on `W2`, computed**: at input `(ȯ, ö) = ((0,0), 1)`, following
(`ä = 0`) beats deviating (`ä = 1`), both events attained.
Source: mandate T13(d) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem score_lt : S.score (0, 0) 1 (0, 1) < S.score (0, 0) 1 (0, 0) := by
  unfold AbstractDS.score
  exact weights.condExpJunk_indicator_lt Q (evS_nonempty _ _ _ _) (evS_nonempty _ _ _ _)
    (by decide +kernel) (-1)

/-- **`W2` is not a UDT fixed point**: the world with policy `anti` at input `((0,0), 1)` chooses
`ä = 1`, which scores strictly less than `ä = 0`. A nondegenerate prior over chosen policies is not
a fixed point of the pointwise rule (T14(b), bli-paper-089's "its existence is the real question").
Source: mandate T13(d), T14(b)
Kind: N+
Fidelity: n/a (refutation of `UdtRule` on this witness)
Hyps: none -/
theorem not_udtRule : ¬ S.UdtRule := by
  intro h
  have := h ((((0, 0), 1), (0, 0)) : Ω) (0, 0) 1 (0, 0)
  exact absurd this (not_le.2 score_lt)

end W2

end Cleanroom.Udt.UdtCommTrust
