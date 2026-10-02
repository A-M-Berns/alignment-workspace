import Cleanroom.Decision.DpFaithfulUdt.Cluster
import Cleanroom.Decision.DpFaithfulUdt.Pdc
import Cleanroom.Decision.DpLocalOpt.StrongFair
import Cleanroom.Decision.DpLocalOpt.TwoPointWitness

/-!
# `Π_B`'s off-path vacuity on a strongly fair tree, and `Π_A ≠ Π_B` on the Stag Hunt
(T11(c), T11(e))

T11(c), (e) of [[dp-faithful-udt-mandate]] (`firstperson.md` FP-11′, FP-13′, §6).

* **The strongly fair sequential Stag Hunt** `seqStag` (`d₁` then the distinct second-stage
  points `d_{2S}`, `d_{2H}`; `(S,S) → 2`, `(H,H) → 1`, else `0`): one node per point, so strongly
  fair (`seqStag_stronglyFair`). The profile `(H, H∣S, H∣H)` is pure- and mixed-Definition-22
  coherent with value `1 < 2` (`seqStag_HHH_coherent_not_optimal`), and `μ(occ(d_{2S})) = 0`
  under it (`seqStag_occ_d2S_null`), so D4's guard fails for every action and the PDC state is
  undefined there (`seqStag_pdc_undefined_d2S`; what `Π_B` then outputs is the junk default's
  tie, `seqStag_piB_vacuous`) — **off-path vacuity**,
  on a strongly fair tree: Theorem 3's fairness hypotheses are not what separates `Π_B` from
  tremble-EDT. On-path (`d_{2H}`) `Π_B` does what Theorem 2 says (`seqStag_piB_d2H`).
* **`Π_A ≠ Π_B` on the two-point Stag Hunt** (`twoStag_piA_ne_piB`): under any masked prior the
  cluster branch is `{(S, S)}` (value `2`), while `Π_B` at `(H, H)` with PDC stays at `(H, H)`
  (value `1`): `Π_B` is UDT1.0, `Π_A`'s cluster branch is UDT1.1, separated by the Stag Hunt
  (FP-11′'s verdict).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

/-- `MiniW` is inhabited (for the junk branch of `Cf.ofEvents`). Source: none: infrastructure.
Kind: D -/
instance : Nonempty MiniW := ⟨(.a, .a)⟩

/-- `(ofFun π)[d ↦ a] = ofFun (π[d ↦ a])`. Source: none: infrastructure. Kind: L -/
theorem ofFun_deviatePure {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    [DecidableEq ι] (π : (d : ι) → acts d) (d : ι) (a : acts d) :
    (Proc.ofFun π : Proc ι acts K).deviatePure d a = Proc.ofFun (Function.update π d a) := by
  funext d'
  by_cases h : d' = d
  · subst h; simp [Proc.deviatePure, Proc.ofFun]
  · simp [Proc.deviatePure, Proc.deviate_ne _ _ h, Proc.ofFun, Function.update_of_ne h]

/-! ### The strongly fair sequential Stag Hunt -/

section seqStag

/-- The points of the strongly fair sequential Stag Hunt: the root and the two second-stage
points.
Source: `firstperson.md` FP-13′ ("the sequential Stag Hunt `(H, H∣S, H∣H)`")
Kind: D -/
inductive StagPt : Type
  | d1
  | d2S
  | d2H
  deriving DecidableEq, Fintype

/-- The second-stage point reached after the first-stage action.
Source: none: infrastructure
Kind: D -/
def stage2 : Act2 → StagPt
  | .a => .d2S
  | .b => .d2H

/-- The Stag Hunt payoffs: `(S,S) → 2`, `(H,H) → 1`, else `0` (`S = a`).
Source: `firstperson.md` FP-11′ ("payoffs `2` at `(S,S)`, `1` at `(H,H)`, `0` off-diagonal")
Kind: D -/
def stagPay : Act2 → Act2 → ℚ
  | .a, .a => 2
  | .b, .b => 1
  | _, _ => 0

/-- **The strongly fair sequential Stag Hunt**: `d₁` at the root; below `S` the point `d_{2S}`,
below `H` the point `d_{2H}`; the leaf-world records both acts.
Source: `firstperson.md` FP-13′ ("on the sequential Stag Hunt `(H, H∣S, H∣H)` … strongly fair");
FP-11′ ("the strongly fair sequential tree (value-2 policy `(S, S∣S, H∣H)`)")
Kind: D -/
def seqStag : Tree MiniW StagPt (fun _ => Act2) ℚ :=
  .decision .d1 fun a => .decision (stage2 a) fun b => .leaf (a, b) (stagPay a b)

/-- The profile `(H, H∣S, H∣H)`. Source: `firstperson.md` FP-13′. Kind: D -/
abbrev profHHH : Proc StagPt (fun _ => Act2) ℚ := Proc.ofFun fun _ => Act2.b

/-- **`seqStag` is strongly fair**: one node per point.
Source: `firstperson.md` FP-13′ ("vacuously off-path even on strongly fair trees")
Kind: N+ -/
theorem seqStag_stronglyFair : StronglyFair seqStag := by
  apply StronglyFair.of_injective_pt
  rintro (_ | ⟨a, (_ | ⟨b, q⟩)⟩) (_ | ⟨a', (_ | ⟨b', q'⟩)⟩) h
  · rfl
  · cases a' <;> exact absurd h (by decide)
  · exact q'.elim
  · cases a <;> exact absurd h (by decide)
  · cases a <;> cases a' <;> first | rfl | exact absurd h (by decide)
  · exact q'.elim
  · exact q.elim
  · exact q.elim
  · exact q.elim

/-- `seqStag` is almost fair. Source: none: infrastructure. Kind: L -/
theorem seqStag_almostFair : AlmostFair seqStag :=
  StronglyFair.almostFair seqStag seqStag_stronglyFair

/-- Summing over the four leaves of `seqStag`. Source: none: infrastructure. Kind: L -/
theorem seqStag_sum (f : seqStag.Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ a : Act2, ∑ b : Act2, f ⟨a, b, ()⟩ := by
  unfold seqStag at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The value of a deterministic procedure on `seqStag` is the Stag Hunt payoff of the acts it
plays along its own path.
Source: none: infrastructure
Kind: L -/
theorem seqStag_value_ofFun (π : StagPt → Act2) :
    value (Proc.ofFun π) seqStag = stagPay (π .d1) (π (stage2 (π .d1))) := by
  rcases h1 : π .d1 with _ | _ <;> rcases h2 : π .d2S with _ | _ <;>
    rcases h3 : π .d2H with _ | _ <;>
    simp [seqStag, DpFairnessReloc.value_decision, DpFairnessReloc.value_leaf, Act2.sum_univ, Proc.ofFun, stage2, stagPay, h1,
      h2, h3]

/-- **T11(c) — `(H, H∣S, H∣H)` is Definition-22 coherent (pure and mixed) and not optimal on the
strongly fair sequential Stag Hunt**: `V = 1 < 2 = V(S, S∣S, ·)`.
Source: `firstperson.md` FP-13′ ("on the sequential Stag Hunt `(H, H∣S, H∣H)` is Def-22-coherent
with `V = 1 < 2`"); dp-cf-113
Kind: N+
Fidelity: exact
Hyps: none -/
theorem seqStag_HHH_coherent_not_optimal :
    CoherentPure profHHH seqStag ∧ Coherent profHHH seqStag ∧ value profHHH seqStag = 1 ∧
    value (Proc.ofFun fun _ => Act2.a) seqStag = 2 ∧ ¬ IsOptimal profHHH seqStag := by
  have hv1 : value profHHH seqStag = 1 := by rw [seqStag_value_ofFun]; rfl
  have hv2 : value (Proc.ofFun fun _ => Act2.a) seqStag = 2 := by rw [seqStag_value_ofFun]; rfl
  have hpure : CoherentPure profHHH seqStag := by
    intro d _ a
    rw [ofFun_deviatePure, seqStag_value_ofFun, hv1]
    cases d <;> cases a <;> simp [Function.update, stage2, stagPay]
  refine ⟨hpure, fun d hd => ?_, hv1, hv2, fun h => ?_⟩
  · exact (coherentAt_iff_coherentPureAt_of_almostFair profHHH d seqStag_almostFair).mpr
      (hpure d hd)
  · have := h (Proc.ofFun fun _ => Act2.a)
    rw [hv1, hv2] at this
    norm_num at this

/-- **Under `(H, H∣S, H∣H)` the point `d_{2S}` is off-path**: `μ(occ(d_{2S})) = 0`.
Source: `firstperson.md` FP-13′ ("`μ(occ(d_{2S})) = 0`")
Kind: L -/
theorem seqStag_occ_d2S_null : mass profHHH seqStag (occ .d2S seqStag) = 0 := by
  unfold mass
  apply Finset.sum_eq_zero
  intro ℓ hℓ
  rw [mem_occ] at hℓ
  rcases ℓ with ⟨a, b, ⟨⟩⟩
  cases a
  · simp [seqStag, leafLaw_decision, Proc.ofFun]
  · simp [seqStag, stage2] at hℓ

/-- **T11(c) — FP-13′, off-path vacuity of `Π_B` on a strongly fair tree**: at the off-path point
`d_{2S}` of the sequential Stag Hunt under `(H, H∣S, H∣H)`, *every* deviation has
`μ(occ(d_{2S})) = 0` (occurrence constancy), so D4's guard fails for every action and the PDC
state is undefined — the per-run evaluator has nothing to evaluate. The tree is strongly fair,
so the separator between `Π_B` and tremble-EDT is off-path vacuity, not Theorem 3's hypotheses.
(What `Π_B` then *outputs* is a convention of the junk default: `seqStag_piB_vacuous`.)
Source: `firstperson.md` FP-13′ ("Theorem 2's evaluator at `d_{2S}` returns `(0,0)` (`μ(occ(d_{2S}))
= 0`; Def 17's Unif fallback) … the separator between `Π_B` and tremble-EDT on fair trees is
off-path vacuity"); dp-cf-113
Kind: N+
Fidelity: exact (FP-13′'s content is the vanishing occurrence; the source's "`(0,0)` … Unif
fallback" is its own `x/0 = 0` convention, matched here by `State.trivial`)
Hyps: none -/
theorem seqStag_pdc_undefined_d2S (a : Act2) :
    ¬ 0 < mass (profHHH.deviatePure .d2S a) seqStag (occ .d2S seqStag) ∧
    pdcState profHHH seqStag .d2S a = State.trivial := by
  have hz : ¬ 0 < mass (profHHH.deviatePure .d2S a) seqStag (occ .d2S seqStag) := by
    rw [Proc.deviatePure, occurrence_constancy, seqStag_occ_d2S_null]
    exact lt_irrefl 0
  exact ⟨hz, by unfold pdcState; rw [dif_neg hz]⟩

/-- **Corollary — `Π_B`'s output at the off-path point is the junk default's tie**: for every
injective disposition assignment `ρ`, `cUDT_{PDC}` at `d_{2S}` returns the uniform distribution.
This is a property of the package's junk default `State.trivial` (`V ≡ 0`, so every act ties),
not of the tree: cUDT's domain is total, so Definition 17's empty-domain fallback never fires, and
a different junk default would give a different output. The tree content is
`seqStag_pdc_undefined_d2S`.
Source: `firstperson.md` FP-13′ ("Def 17's Unif fallback"); audit r1 (adversarial) N1
Kind: L
Fidelity: variant: the output is the junk default's constant desirability, not a fallback of
Definition 17
Hyps: (a) `ρ_{d_{2S}}` injective -/
theorem seqStag_piB_vacuous (ρ : (d : StagPt) → Act2 → Finset MiniW)
    (hinj : Function.Injective (ρ .d2S)) :
    cudtProc (pdcCf profHHH seqStag .d2S ρ) ρ .d2S = FinDistr.uniform := by
  unfold cudtProc pdcCf
  apply uniformArgmax_eq_uniform
  intro a b
  rw [Cf.ofEvents_apply ρ _ _ hinj, Cf.ofEvents_apply ρ _ _ hinj,
    (seqStag_pdc_undefined_d2S a).2, (seqStag_pdc_undefined_d2S b).2]
  rfl

/-- The recorded-act dispositions on `seqStag`'s carrier: `pol_{d₁} = a` is `{act₁ = a}`,
`pol_{d_{2S}} = a` is `{act₁ = S ∧ act₂ = a}`, `pol_{d_{2H}} = a` is `{act₁ = H ∧ act₂ = a}`.
Source: `firstperson.md` D3 (the disposition events on a tree whose world records the acts)
Kind: D -/
def stagRho : (d : StagPt) → Act2 → Finset MiniW
  | .d1, a => Finset.univ.filter fun w => w.1 = a
  | .d2S, a => Finset.univ.filter fun w => w.1 = .a ∧ w.2 = a
  | .d2H, a => Finset.univ.filter fun w => w.1 = .b ∧ w.2 = a

/-- `stagRho` is injective at `d_{2H}`. Source: none: infrastructure. Kind: L -/
theorem stagRho_d2H_injective : Function.Injective (stagRho .d2H) := by
  intro a b h
  have := Finset.ext_iff.mp h (Act2.b, a)
  simpa [stagRho] using this

/-- `occ(d_{2H})` has mass `1` under `(H, H∣S, H∣H)`. Source: none: infrastructure. Kind: L -/
theorem seqStag_occ_d2H_mass : mass profHHH seqStag (occ .d2H seqStag) = 1 := by
  unfold mass occ
  rw [Finset.sum_filter, seqStag_sum]
  simp [seqStag, leafLaw_decision, Proc.ofFun, stage2, Act2.sum_univ]

/-- The dispositions at `d_{2H}` are successful under their deviations.
Source: `firstperson.md` FP-10 ("success puts `P^a(ρ_d(a)) = 1`")
Kind: L -/
theorem seqStag_d2H_successOn (a : Act2) : SuccessOn profHHH seqStag .d2H a (stagRho .d2H a) := by
  unfold SuccessOn
  rw [occEv_eq_filter]
  unfold mass occ
  rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_filter, seqStag_sum, seqStag_sum]
  rw [ofFun_deviatePure]
  cases a <;> simp [seqStag, leafLaw_decision, Proc.ofFun, stage2, stagRho, Act2.sum_univ,
    Function.update]

/-- **On-path, `Π_B` is Theorem 2's evaluator**: at `d_{2H}` under `(H, H∣S, H∣H)`, `Π_B` with PDC
returns `H` (`ssaValue(δ_S) = 0 < 1 = ssaValue(δ_H)`).
Source: `firstperson.md` FP-13′ ("`Π_B` attains the optimum where coherence implies optimality …
on-path")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem seqStag_piB_d2H :
    cudtProc (pdcCf profHHH seqStag .d2H stagRho) stagRho .d2H = FinDistr.pure Act2.b := by
  have hpos : 0 < mass profHHH seqStag (occ .d2H seqStag) := by
    rw [seqStag_occ_d2H_mass]; exact one_pos
  rw [piB_eq_ssa_argmax _ _ _ _ stagRho_d2H_injective seqStag_d2H_successOn hpos]
  have hssa : ∀ a, ssaValue profHHH seqStag .d2H (FinDistr.pure a) = stagPay .b a := by
    intro a
    rw [ssaValue_eq_div, seqStag_occ_d2H_mass, div_one]
    unfold ssaNum occ
    rw [Finset.sum_filter, seqStag_sum, ← Proc.deviatePure, ofFun_deviatePure]
    cases a <;> simp [seqStag, leafLaw_decision, Proc.ofFun, stage2, stagPay, Act2.sum_univ,
      Function.update]
  apply uniformArgmax_eq_pure
  apply argmaxFull_act2_eq_b
  rw [hssa, hssa]
  simp [stagPay]

end seqStag

/-! ### `Π_A ≠ Π_B` on the two-point Stag Hunt -/

section twoStag

/-- The recorded-act dispositions on the two-point Stag Hunt's carrier.
Source: `firstperson.md` D3
Kind: D -/
def stag2Rho : (d : Pt2) → Act2 → Finset MiniW
  | .p1, a => Finset.univ.filter fun w => w.1 = a
  | .p2, a => Finset.univ.filter fun w => w.2 = a

/-- `stag2Rho` is injective at each point. Source: none: infrastructure. Kind: L -/
theorem stag2Rho_injective (d : Pt2) : Function.Injective (stag2Rho d) := by
  intro a b h
  cases d
  · have := Finset.ext_iff.mp h (a, a); simpa [stag2Rho] using this
  · have := Finset.ext_iff.mp h (a, a); simpa [stag2Rho] using this

/-- Every run of the two-point Stag Hunt meets both points. Source: none: infrastructure.
Kind: L -/
theorem twoStag_occ (d : Pt2) : occ d twoStag = Finset.univ := by
  cases d <;> decide

/-- Summing over the four leaves of `twoStag`. Source: none: infrastructure. Kind: L -/
theorem twoStag_sum (f : twoStag.Leaves → ℚ) :
    ∑ ℓ, f ℓ = (f ⟨.a, .a, ()⟩ + f ⟨.a, .b, ()⟩) + (f ⟨.b, .a, ()⟩ + f ⟨.b, .b, ()⟩) := by
  refine (sum_leaves_decision f).trans ?_
  rw [Act2.sum_univ]
  refine congrArg₂ (· + ·) ?_ ?_ <;>
    refine (sum_leaves_decision _).trans ?_ <;> rw [Act2.sum_univ] <;>
    exact congrArg₂ (· + ·) (Tree.sum_leaves_leaf _ _ _) (Tree.sum_leaves_leaf _ _ _)

/-- `ν` on the two-point Stag Hunt. Source: none: infrastructure. Kind: L -/
theorem twoStag_nu (C : Proc Pt2 (fun _ => Act2) ℚ) (X : Finset MiniW) :
    nu C twoStag X =
      ((if (Act2.a, Act2.a) ∈ X then (C .p1).w .a * (C .p2).w .a else 0) +
        (if (Act2.a, Act2.b) ∈ X then (C .p1).w .a * (C .p2).w .b else 0)) +
      ((if (Act2.b, Act2.a) ∈ X then (C .p1).w .b * (C .p2).w .a else 0) +
        (if (Act2.b, Act2.b) ∈ X then (C .p1).w .b * (C .p2).w .b else 0)) := by
  rw [nu_eq_sum, twoStag_sum]
  simp [twoStag]

/-- Theorem 2's evaluator on the two-point Stag Hunt is the deviation's value (`occ = ⊤`).
Source: none: infrastructure
Kind: L -/
theorem twoStag_ssaValue (C : Proc Pt2 (fun _ => Act2) ℚ) (d : Pt2) (a : Act2) :
    ssaValue C twoStag d (FinDistr.pure a) = value (C.deviatePure d a) twoStag := by
  rw [ssaValue_eq_div, twoStag_occ, mass_univ, div_one]
  unfold ssaNum value
  rw [twoStag_occ]

/-- The dispositions are successful under their deviations from `(H, H)`.
Source: `firstperson.md` FP-10
Kind: L -/
theorem twoStag_successOn (d : Pt2) (a : Act2) : SuccessOn profHH twoStag d a (stag2Rho d a) := by
  unfold SuccessOn occEv
  rw [twoStag_occ, Finset.inter_univ, mass_univ]
  show nu _ _ _ = 1
  rw [twoStag_nu]
  cases d <;> cases a <;>
    simp [stag2Rho, proc2_deviatePure_p1_a, proc2_deviatePure_p1_b, proc2_deviatePure_p2_a,
      proc2_deviatePure_p2_b]

/-- **`Π_B` at `(H, H)` on the two-point Stag Hunt stays at `H`** at both points (`S ↦ 0`,
`H ↦ 1`).
Source: `firstperson.md` FP-11′ ("`Π_B` with PDC cf gives `S ↦ 0, H ↦ 1` at both points and
stays")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem twoStag_piB_HH (d : Pt2) :
    cudtProc (pdcCf profHH twoStag d stag2Rho) stag2Rho d = FinDistr.pure Act2.b := by
  rw [piB_eq_ssa_argmax _ _ _ _ (stag2Rho_injective d) (twoStag_successOn d)
    (by rw [twoStag_occ, mass_univ]; exact one_pos)]
  obtain ⟨h1, h2, h3, h4⟩ := twoStag_pointGame 0 0 le_rfl zero_le_one le_rfl zero_le_one
  apply uniformArgmax_eq_pure
  apply argmaxFull_act2_eq_b
  simp only [twoStag_ssaValue]
  cases d
  · rw [h1, h2]; norm_num
  · rw [h3, h4]; norm_num

/-- The Stag Hunt payoff table. Source: `firstperson.md` FP-11′. Kind: D -/
def twoStagPay : Act2 → Act2 → ℚ
  | .a, .a => 2
  | .b, .b => 1
  | _, _ => 0

/-- The value of a deterministic procedure on the two-point Stag Hunt. Source: none:
infrastructure. Kind: L -/
theorem twoStag_value_ofFun (π : Pt2 → Act2) :
    value (Proc.ofFun π) twoStag = twoStagPay (π .p1) (π .p2) := by
  rcases h1 : π .p1 with _ | _ <;> rcases h2 : π .p2 with _ | _ <;>
    simp [twoStag, DpFairnessReloc.value_decision, DpFairnessReloc.value_leaf, Act2.sum_univ, Proc.ofFun, twoStagPay, h1, h2]

/-- **The cluster branch on the two-point Stag Hunt is `{(S, S)}`** under any masked prior.
Source: `firstperson.md` FP-11′ ("`Π_A`'s relocated root table `(2,0,0,1)` picks `(S,S)`")
Kind: N+
Fidelity: exact
Hyps: (a) `MaskedPriorCalibrated (lift univ C') (Rel twoStag) s°` -/
theorem twoStag_clusterBranch (C' : Proc Pt2 (fun _ => Act2) ℚ)
    (s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ)
    (hcal : MaskedPriorCalibrated (lift Finset.univ C') (relocRoot Finset.univ twoStag) s₀)
    (σ : (d : ↥(Finset.univ : Finset Pt2)) → Act2) :
    σ ∈ clusterBranch (Finset.univ : Finset Pt2) s₀ ↔
      σ ⟨.p1, Finset.mem_univ _⟩ = Act2.a ∧ σ ⟨.p2, Finset.mem_univ _⟩ = Act2.a := by
  rw [mem_clusterBranch_iff (Finset.univ : Finset Pt2) twoStag C' s₀ (Finset.subset_univ _) hcal]
  have hv : ∀ τ : (d : ↥(Finset.univ : Finset Pt2)) → Act2,
      value (Proc.ofFun (extendTuple Finset.univ τ)) twoStag =
        twoStagPay (τ ⟨.p1, Finset.mem_univ _⟩) (τ ⟨.p2, Finset.mem_univ _⟩) := by
    intro τ
    rw [twoStag_value_ofFun]
    simp [extendTuple]
  simp only [hv]
  constructor
  · intro h
    have h2 := h fun _ => Act2.a
    rcases hσ1 : σ ⟨.p1, Finset.mem_univ _⟩ with _ | _ <;>
      rcases hσ2 : σ ⟨.p2, Finset.mem_univ _⟩ with _ | _ <;>
      simp [hσ1, hσ2, twoStagPay] at h2 ⊢ <;> norm_num at h2
  · rintro ⟨h1, h2⟩ τ
    rw [h1, h2]
    cases τ ⟨.p1, Finset.mem_univ _⟩ <;> cases τ ⟨.p2, Finset.mem_univ _⟩ <;>
      simp [twoStagPay]

/-- **T11(e) — `Π_A ≠ Π_B` on the two-point Stag Hunt**: under any masked prior the cluster branch
of `Π_A` is exactly `{(S, S)}` (value `2`, optimal), while `Π_B` with PDC at `(H, H)` returns `H`
at both points (value `1`, not optimal). `Π_B` is UDT1.0, the cluster branch is UDT1.1; the Stag
Hunt separates them.
Source: `firstperson.md` FP-11′ ("the *procedures* are not one procedure — `Π_B` is UDT1.0, `Π_A`
is UDT1.1, separated by the Stag Hunt"), FP-10; dp-cf-113
Kind: N+
Fidelity: exact
Hyps: (a) `MaskedPriorCalibrated (lift univ C') (Rel twoStag) s°` -/
theorem twoStag_piA_ne_piB (C' : Proc Pt2 (fun _ => Act2) ℚ)
    (s₀ : State (RW MiniW (fun _ => Act2) Finset.univ) ℚ)
    (hcal : MaskedPriorCalibrated (lift Finset.univ C') (relocRoot Finset.univ twoStag) s₀) :
    (∀ σ ∈ clusterBranch (Finset.univ : Finset Pt2) s₀,
      IsOptimal (Proc.ofFun (extendTuple Finset.univ σ)) twoStag ∧
        value (Proc.ofFun (extendTuple Finset.univ σ)) twoStag = 2) ∧
    (∀ d, cudtProc (pdcCf profHH twoStag d stag2Rho) stag2Rho d = FinDistr.pure Act2.b) ∧
    value profHH twoStag = 1 ∧ ¬ IsOptimal profHH twoStag := by
  obtain ⟨-, -, -, hnot, hval, -⟩ := twoStag_HH_coherent_thm1_not_optimal
  refine ⟨fun σ hσ => ⟨clusterBranch_isOptimal Finset.univ twoStag C' s₀ twoStag_almostFair
    (Finset.subset_univ _) hcal σ hσ, ?_⟩, twoStag_piB_HH, hval, hnot⟩
  obtain ⟨h1, h2⟩ := (twoStag_clusterBranch C' s₀ hcal σ).mp hσ
  rw [twoStag_value_ofFun]
  simp [extendTuple, h1, h2, twoStagPay]

end twoStag

end Cleanroom.Decision.DpFaithfulUdt
