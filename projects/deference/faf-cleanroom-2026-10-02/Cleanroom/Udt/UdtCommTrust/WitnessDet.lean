import Cleanroom.Udt.UdtCommTrust.Construct
import Cleanroom.Udt.UdtCommTrust.Witness
import Cleanroom.Udt.UdtCommTrust.WitnessSmall
import Mathlib.Tactic.FinCases

/-!
# `Cleanroom.Udt.UdtCommTrust.WitnessDet`: witnesses added in repair round 1

* `Det` (eight worlds `((m₀, m₁), ö)`, a constant following `Π*`): inhabits the **full hypothesis
  package of `polE_follows_R`** — pointwise UDT rule (`udtRule_of_const`), guarded internal drive,
  told-form stability (strict through the junk `−1` on the empty deviating event), `FactorsAsFam R`,
  `R ⊑ D_{I,B}`, no forcing, `hlink` — so the corollary's package is satisfiable after the round-1
  repair. **N−**: the conclusion holds by construction (`follows_direct`), and the stability
  inequality is the junk one; that is the best available under the pointwise rule, because on a
  nondegenerate prior the rule fails wherever advice-following has bite (`W2.not_udtRule`).
* `W2.udtRuleAt_follow`, `W2.aE_follows_at_follow_world`: the **per-world** form
  `aE_follows_R_of_udtRuleAt` has an **N+** witness on `W2` — nondegenerate prior, both events
  attained, strict gap `1/2 > 7/16`, and a deviating world of positive mass at the same input
  (`W2.deviating_world`), so the conclusion is not forced.
* `W2.semChanSplit`, `W2.polSC_eq_polS`: on `W2` (side channel constant, hence neutral and inert)
  the constructed `Π*_c` **is** `W2`'s `Π*` — the mandate's "witness: `W2` with a neutral value".
* `W2m.semChanSplit`, `W2m.neutral`, `W2m.neutralCompatible`, `W2m.not_factorsAs_oH_oC`: on `W2m`
  the construction is available under the weakened precondition while the mandate's
  `FactorsAs Ô Ǒ` fails (the side channel is linked to the message and the policy). N− in the
  sense the mandate asked for ("an `Ȯ` whose semantic and side-channel coordinates are linked").
-/

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc Finset

/-! ### `Det`: the deterministic witness for the full package of "`Π̈ = R` in fact" -/

namespace Det

/-- Worlds `((m₀, m₁), ö)`: one message per instance and the realized instance.
Source: none: infrastructure (repair round 1, T13(c) witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := (Fin 2 × Fin 2) × Fin 2

/-- The messages of a world.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def msg (ω : Ω) : Fin 2 × Fin 2 := ω.1

/-- The realized instance of a world.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def foc (ω : Ω) : Fin 2 := ω.2

/-- The constant chosen policy: follow the message of the instance.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def follow : Policy ((Fin 2 × Fin 2) × Fin 2) (Fin 1 × Fin 2) := fun oe => (0, W2.pick oe.1 oe.2)

/-- Uniform weights on eight worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 8
  sum_eq := by decide +kernel

/-- The utility indicator: the realized action is `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Q (ω : Ω) : Prop := W2.pick (msg ω) (foc ω) = 1

instance (ω : Ω) : Decidable (Q ω) := by unfold Q; infer_instance

/-- **`Det` as an abstract decision structure**: the action follows the instance's message, the
boundary dynamic is trivial, `D_I` carries the messages, `D_E` the instance.
Source: repair round 1 (T13(c) witness)
Kind: N−
Fidelity: n/a
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 2 × Fin 2) (Fin 2) (Fin 1) (Fin 2) (Fin 2 × Fin 2)
    (Fin 2) (Fin 1) (Fin 2 × Fin 2) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI := msg
  oE := foc
  aI _ := 0
  aE ω := W2.pick (msg ω) (foc ω)
  dI := msg
  dE := foc
  dB _ := 0
  oH := msg
  oC _ := 0
  polS _ := follow
  U ω := if Q ω then 1 else 0
  U_mem ω := by split_ifs <;> simp
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => ((W2.pick (msg ω₁) (foc ω₁), W2.pick (msg ω₁) (foc ω₁)), foc ω₂))
    (by decide +kernel)
  B_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (msg ω₂, foc ω₁)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => (msg ω₁, foc ω₂)) (by decide +kernel)
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **`Det` as a concrete decision structure**: the semantics recommend the instance's message;
nothing is ever forced.
Source: repair round 1 (T13(c) witness)
Kind: N−
Fidelity: n/a
Hyps: none -/
noncomputable def S : ConcreteDS Ω (Fin 2 × Fin 2) (Fin 2) (Fin 1) (Fin 2) (Fin 2 × Fin 2)
    (Fin 2) (Fin 1) (Fin 2 × Fin 2) (Fin 1) where
  toAbstractDS := absDS
  s e h := some (W2.pick h e)
  p _ _ := none

/-- `Π̈` on `Det`: follow the messages.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = fun e => W2.pick (msg ω) e :=
  S.polE_eq_of (fun ω e => W2.pick (msg ω) e) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ω

/-- `[[·]]_Ô` is the identity on `Det`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projOH_eq (o : Fin 2 × Fin 2) : S.projOH o = o := S.projOH_oI ((o, 0) : Ω)

/-- `Π†` on `Det` is the constant following policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq (ω : Ω) : S.polD ω = follow := by
  funext oe
  have h1 := S.projAI_B ((oe.1, oe.2) : Ω)
  have h2 := S.projAE_B ((oe.1, oe.2) : Ω)
  show (S.projAI (oe, 0), S.projAE (oe, 0)) = _
  exact Prod.ext h1 h2

/-- **The pointwise UDT rule holds on `Det`** (a constant chosen policy).
Source: repair round 1; mandate T14(b)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem udtRule : S.UdtRule := S.udtRule_of_const follow fun _ => rfl

/-- **`hlink` on `Det`**: the effective policy is the chosen one.
Source: repair round 1 (T13(c) witness)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω) :=
  fun ω _ => by rw [polD_eq]; rfl

/-- **`R ⊑ D_{I,B}` on `Det`.**
Source: repair round 1 (T13(c) witness)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem R_sub_DIB : IsSubvariable S.DIB S.R := by decide +kernel

/-- **Guarded internal drive on `Det`**: one action is attained per input, so the guard makes the
identity trivial.
Source: repair round 1 (T13(c) witness)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem internallyDriven : S.InternallyDriven := by
  intro o e ai a a' r ha ha'
  obtain ⟨ω₁, h₁⟩ := ha
  obtain ⟨ω₂, h₂⟩ := ha'
  rw [AbstractDS.mem_evS] at h₁ h₂
  have e1 : (follow (o, e)).2 = a := congrArg Prod.snd h₁
  have e2 : (follow (o, e)).2 = a' := congrArg Prod.snd h₂
  rw [← e1, ← e2]

/-- **Told-form stability of every realized recommendation on `Det`**: the deviating event is
empty (junk `−1`) and the following event contains the told world. This is where the witness is
degenerate: strictness comes from the convention, not from a computed gap.
Source: repair round 1 (T13(c) witness)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem stableR : ∀ r ∈ Set.range S.R, S.StableR r := by
  rintro r ⟨ω₀, rfl⟩ e a₀ hra o ho ai a' ha'
  rw [projOH_eq] at ho
  have hoa : W2.pick o e = a₀ := Option.some.inj ho
  have hempty : S.evS o e (ai, a') ∩ S.evToldMinus (S.R ω₀) e = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ω hω
    have h := (Finset.mem_inter.1 hω).1
    rw [AbstractDS.mem_evS] at h
    exact ha' ((congrArg Prod.snd h).symm.trans hoa)
  have hne : (S.evS o e (ai, a₀) ∩ S.evToldMinus (S.R ω₀) e).Nonempty := by
    refine ⟨ω₀, Finset.mem_inter.2 ⟨?_, ?_⟩⟩
    · rw [AbstractDS.mem_evS]
      exact Prod.ext (Subsingleton.elim _ _) hoa
    · simp [ConcreteDS.evToldMinus]
  rw [hempty, condExpJunk_of_empty]
  exact junk_lt_of_nonempty S.pos S.U_nonneg hne

/-- **The recommendation tuple factors by instance on `Det`.**
Source: repair round 1 (T13(c) witness)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem R_fam : FactorsAsFam S.R :=
  factorsAsFam_of_fun (fun c => ((W2.pick (msg (c 0)) 0, W2.pick (msg (c 1)) 1), 0))
    fun c i => by fin_cases i <;> rfl

/-- **"`Π̈ = R` in fact" applied to `Det`**: the full hypothesis package of `polE_follows_R` is
inhabited.
Source: repair round 1 (T13(c) witness)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem polE_follows_R : ∀ ω, ∀ e ∈ Set.range S.oE, ∀ a, S.R ω e = some a → S.polE ω e = a :=
  S.polE_follows_R udtRule (fun _ _ _ => rfl) hlink R_sub_DIB internallyDriven stableR R_fam

/-- **The conclusion holds on `Det` by construction** — which is why the witness is graded N−.
Source: repair round 1
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem follows_direct : ∀ ω e a, S.R ω e = some a → S.polE ω e = a := by
  intro ω e a h
  rw [polE_eq]
  exact Option.some.inj h

end Det

/-! ### `W2`: the per-world form has a non-degenerate witness; the constructed `Π*` is `W2`'s -/

namespace W2

/-- A world of `W2` running the following policy (`k = 0`) at input `((0,0), 1)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def followWorld : Ω := (((0, 0), 0), (1, 0))

/-- **The following world is a UDT argmax at its own input**: the two actions score `1/2` and
`7/16` (`score_lt`), and the world chooses the better one.
Source: repair round 1 (T13(c) per-world witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem udtRuleAt_follow : S.UdtRuleAt followWorld (0, 0) 1 := by
  intro x
  have hp : polSC followWorld ((0, 0), 1) = (0, 0) := by decide +kernel
  show S.score (0, 0) 1 x ≤ S.score (0, 0) 1 (polSC followWorld ((0, 0), 1))
  rw [hp]
  have hall : ∀ a : Fin 1 × Fin 2, a = (0, 0) ∨ a = (0, 1) := by decide
  rcases hall x with rfl | rfl
  · exact le_rfl
  · exact score_lt.le

/-- **"`Π̈ = R` in fact", per world, on `W2`**: at the following world the external action is the
recommendation, by `aE_follows_R_of_udtRuleAt` with every hypothesis discharged on `W2`
(nondegenerate prior, both conditioning events attained, strict gap `1/2 > 7/16`).
Source: repair round 1 (T13(c) per-world witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem aE_follows_at_follow_world : S.aE followWorld = 0 :=
  S.aE_follows_R_of_udtRuleAt followWorld udtRuleAt_follow (fun _ _ _ => rfl)
    (fun ω _ => by rw [polD_eq]; rfl) internallyDriven stableR R_fam (by decide +kernel)

/-- **A deviating world of positive mass at the same input**: with policy `anti` (`k = 1`) the
external action at `((0,0), 1)` is `1 ≠ 0`, so the per-world conclusion is not forced by the
structure; it is the rule at the world that forces it.
Source: repair round 1 (T13(c) per-world witness, non-degeneracy)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem deviating_world : S.aE ((((0, 0), 1), (1, 0)) : Ω) = 1 ∧
    S.R ((((0, 0), 1), (1, 0)) : Ω) 1 = some 0 := by decide +kernel

/-- **`Ȯ` is determined by `(Ô, Ǒ)` on `W2`** (the side channel is constant).
Source: mandate T4(b) (witness)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem semChanSplit : S.SemChanSplit := by unfold ConcreteDS.SemChanSplit; decide +kernel

/-- **On `W2` the constructed `Π*_c` (neutral value `0`) is `W2`'s chosen policy.** The side
channel is constant, so neutralizing does nothing and `Π*_c = Π† = Π*`. N−: the side channel is
trivial.
Source: mandate T4(b) ("witness: `W2` with a neutral value")
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem polSC_eq_polS (ω : Ω) : S.polSC 0 ω = S.polS ω := by
  funext oe
  have h : S.neutralize 0 oe.1 = oe.1 :=
    S.neutralize_spec semChanSplit (((oe.1, 0), (0, 0)) : Ω) rfl
  show S.polD ω (S.neutralize 0 oe.1, oe.2) = S.polS ω oe
  rw [h, polD_eq]
  rfl

/-- **`W2`'s side channel is inert** (trivially: it is constant and never forces).
Source: mandate T4(b)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem sideChannelInert : S.SideChannelInert 0 := by
  intro ω _
  have h : S.neutralize 0 (S.oI ω) = S.oI ω := S.neutralize_spec semChanSplit ω rfl
  rw [h]
  rfl

end W2

/-! ### `W2m`: the construction is available under the weakened precondition, not the mandate's -/

namespace W2m

/-- **`Ȯ = (Ô, Ǒ)` on `W2m`** (literally a pair).
Source: mandate T4(b) (failure case)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem semChanSplit : S.SemChanSplit := by unfold ConcreteDS.SemChanSplit; decide +kernel

/-- **`0` is a neutral side-channel value on `W2m`.**
Source: mandate T4(b)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem neutral : S.Neutral 0 := fun _ => rfl

/-- **The neutral value is compatible with every semantic observation on `W2m`** (the `k = 0`
worlds carry both messages with side channel `0`).
Source: mandate T4(b)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem neutralCompatible : S.NeutralCompatible 0 := by
  unfold ConcreteDS.NeutralCompatible; decide +kernel

/-- **`FactorsAs Ô Ǒ` fails on `W2m`**: the side channel `2` (forcing `1`) occurs only with message
`1`. So the mandate's precondition is strictly stronger than what the construction needs — this is
the "linked coordinates" failure case the mandate asked for, and on it the construction is still
available (`neutralCompatible`).
Source: mandate T4(b) (failure case)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem not_factorsAs_oH_oC : ¬ FactorsAs S.oH S.oC := by
  rw [factorsAs_iff]
  decide +kernel

end W2m

end Cleanroom.Udt.UdtCommTrust
