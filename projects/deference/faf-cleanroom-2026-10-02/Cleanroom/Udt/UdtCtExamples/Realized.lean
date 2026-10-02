import Cleanroom.Udt.UdtCommTrust.Advice
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCtExamples.CountExt

/-!
# `Cleanroom.Udt.UdtCtExamples.Realized`: what `P(Π̈ = R) = 1` does to the deviation
conditionals (T7(d), load-bearing 5)

Work package `udt-ct-examples`, target T7(d) (bli-paper-2-020). Sources: the Claude write-up in
[[udt-tiling-working-notes-2025-06-30]] lines 384–390 (the deviation conditionals of Stability and
Advice-Following); `udt-comm-trust`'s `Stable`, `StableR`, `adviceFollowing_R`.

Under `P(Π̈ = R) = 1`, no simultaneous recommendation and modification (`hnosim`), and the
prose meaning of `Π*` (`hlink`: the effective action is the chosen one at every unforced realized
input), a chosen-policy deviation from the recommendation at a realized input has probability zero
*with that input realized*: `{Π*(ȯ, ö) = (ȧ, a)} ∩ {Ȯ = ȯ, Ö = ö} = ∅` for `a ≠ r(ö)`. So the
deviation conditionals `E[U ∣ Π*(ȯ, ö) = (ȧ, a), …]` of `Stable`, `StableR` and the conclusion of
`adviceFollowing_R` are supported on worlds that do not realize the input `(ȯ, ö)` — they are
statements about what the chosen policy would do *there* as evaluated on worlds *elsewhere*. The
four-world witness `J2` exhibits it (the deviating chosen policies are realized only at the other
internal observation) and doubles as the consistency witness of T5(b)(iii) (`Convention.lean`).
-/

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

section General

variable {Ω OI OE AI AE DI DE DB OH OC : Type} [Fintype Ω] [DecidableEq Ω]
  [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE] [DecidableEq AI] [DecidableEq OI]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-- The event `{Ȯ = ȯ ∧ Ö = ö}`: the worlds that realize the input `(ȯ, ö)`.
Source: none: infrastructure (mandate T7(d))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def evInput (o : OI) (e : OE) : Finset Ω := event fun ω => S.oI ω = o ∧ S.oE ω = e

/-- Supporting lemma `mem_evInput`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem mem_evInput {o : OI} {e : OE} {ω : Ω} :
    ω ∈ evInput S o e ↔ S.oI ω = o ∧ S.oE ω = e := by simp [evInput]

/-- **Under `P(Π̈ = R) = 1` the realized external action is the recommendation** wherever one is
made: `R(ω)(Ö(ω)) = some a₀ → Ä(ω) = a₀`.
Source: [[communication-trust-translated]] line 424 (`Π̈ = R`); mandate T7(d)
Kind: L
Fidelity: exact
Hyps: none -/
theorem aE_eq_of_follows (h1 : mass S.μ.w S.evFollowsR = 1) {ω : Ω} {a₀ : AE}
    (hR : S.R ω (S.oE ω) = some a₀) : S.aE ω = a₀ := by
  have hf : ConcreteDS.Follows (S.polE ω) (S.R ω) := by
    have hu := (S.evFollowsR_eq_univ_iff).1 h1
    have hmem : ω ∈ S.evFollowsR := by rw [hu]; exact Finset.mem_univ _
    exact S.mem_evFollowsR.1 hmem
  rw [← S.polE_apply_oE]
  exact hf _ _ hR

/-- **The realized input never sees a chosen-policy deviation** (T7(d)(i), 2-020): under
`P(Π̈ = R) = 1`, `hnosim` and `hlink`, if the semantics at `ö` recommend `a₀` at `ȯ`, then for
every `ȧ` and `a ≠ a₀` the event `{Π*(ȯ, ö) = (ȧ, a)}` is disjoint from `{Ȯ = ȯ ∧ Ö = ö}`. Proof:
a world in both is unforced at its realized instance (`hnosim`), so its effective action is its
chosen one (`hlink`), `Ä = a`; but it follows the recommendation, `Ä = a₀`.
Source: [[udt-tiling-working-notes-2025-06-30]] lines 384–390 (bli-paper-2-020); mandate T7(d)(i)
Kind: C
Fidelity: exact
Hyps: (a) `mass evFollowsR = 1`, `hnosim` (hypotheses of `aE_follows_R_of_udtRuleAt`); (c) `hlink`: the paper's prose meaning of `Π*`, which the structure does not encode (`Π*` is a field) — an identification taken as a hypothesis and discharged on every witness (`CB`, `CBm`, `Mem`, `MemH`, `TB`, `J2`); §3 (c) -/
theorem deviation_unrealized (h1 : mass S.μ.w S.evFollowsR = 1)
    (hnosim : ∀ e o, (S.s e (S.projOH o)).isSome → S.p e (S.projOC o) = none)
    (hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω))
    {o : OI} {e : OE} {a₀ : AE} (hs : S.s e (S.projOH o) = some a₀) (ai : AI) {a : AE}
    (ha : a ≠ a₀) : S.evS o e (ai, a) ∩ evInput S o e = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ω hω
  rw [Finset.mem_inter, AbstractDS.mem_evS, mem_evInput] at hω
  obtain ⟨hpol, ho, he⟩ := hω
  have hnoforce : S.P ω (S.oE ω) = none := by
    show S.p (S.oE ω) (S.oC ω) = none
    rw [← S.projOC_oI, he, ho]
    exact hnosim e o (by rw [hs]; rfl)
  have hact := S.polD_apply_O ω
  rw [hlink ω hnoforce] at hact
  have hO : S.O ω = (o, e) := by
    show (S.oI ω, S.oE ω) = (o, e)
    rw [ho, he]
  rw [hO, hpol] at hact
  have haE : S.aE ω = a := (congrArg Prod.snd hact).symm
  have hR : S.R ω (S.oE ω) = some a₀ := by
    show S.s (S.oE ω) (S.oH ω) = some a₀
    rw [← S.projOH_oI, he, ho]
    exact hs
  exact ha (haE ▸ aE_eq_of_follows S h1 hR)

/-- **The deviation conditionals live off the input** (T7(d)(ii)): every world in
`{Π*(ȯ, ö) = (ȧ, a)}` with `a ≠ r(ö)` has `(Ȯ, Ö) ≠ (ȯ, ö)`. So the conditioning events of
`Stable`, `StableR` and the conclusion of `adviceFollowing_R` at a deviation are supported on
worlds that do not realize the input.
Source: [[udt-tiling-working-notes-2025-06-30]] lines 384–390 (bli-paper-2-020); mandate T7(d)(ii)
Kind: C
Fidelity: exact
Hyps: as `deviation_unrealized`; §3 (c) -/
theorem deviation_off_input (h1 : mass S.μ.w S.evFollowsR = 1)
    (hnosim : ∀ e o, (S.s e (S.projOH o)).isSome → S.p e (S.projOC o) = none)
    (hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω))
    {o : OI} {e : OE} {a₀ : AE} (hs : S.s e (S.projOH o) = some a₀) (ai : AI) {a : AE}
    (ha : a ≠ a₀) : ∀ ω ∈ S.evS o e (ai, a), (S.oI ω, S.oE ω) ≠ (o, e) := by
  intro ω hω hne
  have hin : ω ∈ evInput S o e := by
    rw [mem_evInput]
    exact ⟨(Prod.mk.inj hne).1, (Prod.mk.inj hne).2⟩
  have := deviation_unrealized S h1 hnosim hlink hs ai ha
  rw [Finset.eq_empty_iff_forall_notMem] at this
  exact this ω (Finset.mem_inter.2 ⟨hω, hin⟩)

/-- **At a realized recommended input the recommended action has conditional probability `1`**
(T7(d)(iii), 2-020(c)): `P(Ä = a₀ ∣ Ȯ = ȯ, Ö = ö) = 1` on a non-empty input event, under
`P(Π̈ = R) = 1` alone.
Source: [[udt-tiling-working-notes-2025-06-30]] line 390 (bli-paper-2-020(c)); mandate T7(d)(iii)
Kind: L
Fidelity: exact
Hyps: (a); §3 (c) -/
theorem condProb_aE_eq_one (h1 : mass S.μ.w S.evFollowsR = 1) {o : OI} {e : OE} {a₀ : AE}
    (hs : S.s e (S.projOH o) = some a₀) (hne : (evInput S o e).Nonempty) :
    condProbJunk S.μ.w (event fun ω => S.aE ω = a₀) (evInput S o e) 0 = 1 := by
  refine condProbJunk_eq_one_of_subset S.pos hne ?_ 0
  intro ω hω
  rw [mem_evInput] at hω
  rw [mem_event]
  obtain ⟨ho, he⟩ := hω
  apply aE_eq_of_follows S h1
  show S.s (S.oE ω) (S.oH ω) = some a₀
  rw [← S.projOH_oI, he, ho]
  exact hs

end General

/-! ### `J2`: the deviating chosen policies are realized only at the other internal observation -/

namespace J2

/-- Worlds `(d, c)`: `d` the dynamics (`0` observes the message "press `0`" and follows it,
`1` observes silence and presses `1`), `c` a coin.
Source: none: infrastructure (mandate T7(d)(iv), T5(b)(iii))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- Uniform weights on four worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 4
  sum_eq := by decide +kernel

/-- The utility numerator: the action matches the coin.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.1 = ω.2 then 1 else 0

/-- **`J2` as an abstract decision structure**: one instance; `Ȯ = Ô = D_I = d`; `Ä = d`; the
chosen policy presses `d` whatever it observes; the coin is `D_E`; `U = 𝟙[Ä = coin]`.
Source: mandate T7(d)(iv), T5(b)(iii)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 2) (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 2) (Fin 1)
    (Fin 2) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI ω := ω.1
  oE _ := 0
  aI _ := 0
  aE ω := ω.1
  dI ω := ω.1
  dE ω := ω.2
  dB _ := 0
  oH ω := ω.1
  oC _ := 0
  polS ω := fun _ => (0, ω.1)
  U := natDiv u 1
  U_mem := natDiv_mem u (by norm_num) (fun ω => by unfold u; split_ifs <;> omega)
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  B_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **`J2` as a concrete decision structure**: the semantic observation `0` recommends action `0`,
`1` is silent; nothing is ever forced.
Source: mandate T7(d)(iv), T5(b)(iii)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : ConcreteDS Ω (Fin 2) (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 2) (Fin 1)
    (Fin 2) (Fin 1) where
  toAbstractDS := absDS
  s _ h := if h = 0 then some 0 else none
  p _ _ := none

/-- **`Π̈` on `J2`.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = fun _ => ω.1 :=
  S.polE_eq_of (fun ω _ => ω.1) (fun _ => rfl) (by decide +kernel) (by decide +kernel) ω

/-- **`P(Π̈ = R) = 1` on `J2`**: the message worlds follow, the silent worlds are unconstrained.
Source: mandate T7(d)(iv)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem followsR : mass S.μ.w S.evFollowsR = 1 := by
  have : S.evFollowsR = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro ω
    rw [ConcreteDS.mem_evFollowsR, polE_eq]
    show ConcreteDS.Follows (fun _ => ω.1) (fun _ => if ω.1 = 0 then some 0 else none)
    revert ω
    decide
  rw [this]
  exact mass_univ S.μ

/-- **`hnosim` on `J2`** (vacuously: nothing is forced).
Source: mandate T7(d)(iv)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem hnosim : ∀ e o, (S.s e (S.projOH o)).isSome → S.p e (S.projOC o) = none := fun _ _ _ => rfl

/-- **`hlink` on `J2`**: the effective action is the chosen one everywhere.
Source: mandate T7(d)(iv)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω) := by
  intro ω _
  rw [AbstractDS.polD_apply_O]
  rfl

/-- Supporting lemma: the projection of `Ȯ` onto `Ô` is the identity (every value realized).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projOH_eq (o : Fin 2) : S.projOH o = o := S.projOH_oI ((o, 0) : Ω)

/-- **The deviating chosen policies at the message input are realized only at the silent
observation** (T7(d)(iv), N+): the semantics recommend `0` at `ȯ = 0`; the event
`{Π*(0, ·) = (0, 1)}` is the non-empty set of `d = 1` worlds, and every one of them has `Ȯ = 1`.
So `Stable`'s and `adviceFollowing_R`'s deviation conditional at the message input is an average
over worlds that never see the message — as `deviation_off_input` says it must be.
Source: mandate T7(d)(iv) (2-020(b))
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem deviation_witness :
    S.s 0 (S.projOH 0) = some 0 ∧ (S.evS 0 0 (0, 1)).Nonempty ∧
      ∀ ω ∈ S.evS 0 0 (0, 1), S.oI ω ≠ 0 := by
  refine ⟨by rw [projOH_eq]; rfl, ⟨(1, 0), by simp [S, absDS]⟩, fun ω hω => ?_⟩
  rw [AbstractDS.mem_evS] at hω
  have : ω.1 = 1 := (Prod.mk.inj hω).2
  show ω.1 ≠ 0
  rw [this]
  decide

/-- **The general theorem, instantiated on `J2`**: the deviating event is disjoint from the input
event by `deviation_unrealized`, with all three hypotheses discharged on the witness.
Source: mandate T7(d)(iv)
Kind: C
Fidelity: n/a
Hyps: none -/
theorem deviation_unrealized_J2 : S.evS 0 0 (0, 1) ∩ evInput S 0 0 = ∅ :=
  deviation_unrealized S followsR hnosim hlink (by rw [projOH_eq]; rfl) 0 (by decide)

end J2

end Cleanroom.Udt.UdtCtExamples
