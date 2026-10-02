import Cleanroom.Decision.DpFaithfulUdt.SelfConfirming

/-!
# L23 at one point (T5) and the R1-calibrated cUDT (T8, general part)

T5 of [[dp-faithful-udt-mandate]] (faithful.md FA-5, FA-6′; v2 Q10): on a one-point tree
(`ι = Unit`) with `s°` masked-prior-calibrated under `lift C'` and the `pol` coordinate,
`UDT_{s°,pol}(d) = Unif argmax_a V_B(δ_a)` — the best deterministic procedure — on **every**
one-point tree, nested or not (`udtProc_onePoint`; the deviation of a one-point self-model is
deterministic and relocation is exact at the pure grade, FR-7(a)); hence `T_opt` holds on
non-nested (almost-fair) fibers (`udtProc_onePoint_isOptimal_of_almostFair`), and fails on the
nested AMD (`amd_inclusion_not_optimal`, `BestReply.lean`): optimal exactly where determinism is.
FA-6′: strict prior calibration to a deterministic self-model collapses Definition 17's domain to
`{C(d)}` and `UDT_{s°,pol}` ratifies `C` (`udtDomain_strict_collapse`, `udtProc_strict_collapse`),
which is why the masked variant is mandatory.

T8, general part (faithful.md FA-7′ (iv), (v)): the **R1 state** at the disposition `pol_d = a`
is the prior-calibrated state of `lift (C'[d ↦ a])` on the relocated tree (`r1State`), packaged
as a counterfactual structure on the `pol` events (`r1Cf`); the R1-calibrated `cUDT` at `d` is
`Unif argmax_a V_{Rel}(lift (C'[d ↦ a]))` on every tree and `Unif BR_d(C')` on almost-fair trees,
so it coincides with `UDT_{s°,pol}` under *any* masked-calibrated `s°` — and needs no mask of its
own (`cudtProc_r1_eq_udtProc`). The evidential coincidence (v): if `cf` is the Jeffrey
conditioning of `s°` on every `ρ`-event of positive prior probability and the domain is all of
`A_d`, then `cUDT_{s°,ρ} = UDT_{s°,ρ}` (`cudtProc_eq_udtProc_of_evidential`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ### FA-6′: the strict collapse -/

section strict

variable (U : Finset ι) (B : Tree Ω ι acts K) (s₀ : State (RW Ω acts U) K)

/-- `Unif({a}) = δ_a`. Source: none: infrastructure. Kind: L -/
theorem uniformOn_singleton {α : Type} [Fintype α] [DecidableEq α] (a : α) :
    uniformOn (K := K) {a} (Finset.singleton_nonempty a) = FinDistr.pure a := by
  apply FinDistr.ext'
  intro b
  simp [uniformOn_w, FinDistr.pure_w]

/-- **FA-6′ — strict prior calibration collapses the domain**: under Definition 11 unmasked with a
deterministic self-model `ofFun σ`, `P_{s°}(pol_d = a) = 1[a = σ_d]`, so Definition 17's domain at
`d ∈ U` is `{σ_d}`.
Source: `faithful.md` FA-6′ ("the disposition coordinate has `P_{s°}(E_a) = 1[a = C(d)]`,
Definition 17's domain is `{C(d)}`"); v2 amendment 4
Kind: P
Fidelity: exact
Hyps: (a) `PriorCalibrated (lift U (ofFun σ)) (Rel_U B) s°` -/
theorem udtDomain_strict_collapse (σ : (d : ι) → acts d)
    (hcal : PriorCalibrated (lift U (Proc.ofFun σ)) (relocRoot U B) s₀) {d : ι} (h : d ∈ U) :
    udtDomain s₀ (polEv U) d = {σ d} := by
  ext a
  rw [mem_udtDomain, Finset.mem_singleton, polEv_pr U B (Proc.ofFun σ) s₀ hcal h, Proc.ofFun_w]
  split_ifs with ha <;> simp [ha]

/-- **FA-6′ — `UDT_{s°,pol}` ratifies the deterministic self-model under strict calibration**:
`UDT_{s°,pol}(d) = δ_{σ_d}` for every `d ∈ U` — Remark 3.9's collapse one level up; the masked
variant of Definition 11 (or R1-calibrated cUDT, `cudtProc_r1_eq_udtProc`) is what gives the
updateless pair content.
Source: `faithful.md` FA-6′ ("`UDT_{s°,ρ}(d) = C(d)` for every deterministic `C`"); v2
amendment 4; Remark 3.9
Kind: P
Fidelity: exact
Hyps: (a) `PriorCalibrated (lift U (ofFun σ)) (Rel_U B) s°` -/
theorem udtProc_strict_collapse (σ : (d : ι) → acts d)
    (hcal : PriorCalibrated (lift U (Proc.ofFun σ)) (relocRoot U B) s₀) {d : ι} (h : d ∈ U) :
    udtProc s₀ (polEv U) d = FinDistr.pure (σ d) := by
  have hdom := udtDomain_strict_collapse U B s₀ σ hcal h
  have hmem : σ d ∈ udtArgmax s₀ (polEv U) d := by
    rw [mem_udtArgmax]
    have hp : 0 < s₀.pr (polEv U d (σ d)) := by
      rw [polEv_pr U B (Proc.ofFun σ) s₀ hcal h, Proc.ofFun_w, if_pos rfl]; exact one_pos
    refine ⟨hp, fun b hb => ?_⟩
    have : b ∈ udtDomain s₀ (polEv U) d := (mem_udtDomain s₀ (polEv U) d b).mpr hb
    rw [hdom, Finset.mem_singleton] at this
    rw [this]
  have hsub : udtArgmax s₀ (polEv U) d ⊆ {σ d} := by
    rw [← hdom]; exact argmaxPlus_subset _ _ _
  have heq : udtArgmax s₀ (polEv U) d = {σ d} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hmem)
  rw [udtProc_apply, dif_pos ⟨σ d, hmem⟩]
  simp only [heq]
  exact uniformOn_singleton (σ d)

end strict

/-! ### T5: one point -/

section onePoint

variable {acts : Unit → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  [∀ d, Nonempty (acts d)] (B : Tree Ω Unit acts K) (C' : Proc Unit acts K)
  (s₀ : State (RW Ω acts {()}) K)

/-- A one-point tree queries at most its point. Source: none: infrastructure. Kind: L -/
theorem queried_unit_subset : queried B ⊆ {()} := fun p _ => by simp

/-- **T5(a′) — on every one-point tree, `V_{s°}(pol = a) = V_B(δ_a)`** under masked prior
calibration to `lift C'`: the deviation `C'[d ↦ a]` of a one-point self-model is `δ_a`, and
relocation is exact at the pure grade (FR-7(a)) — no almost-fairness needed; the domain is all of
`A_d`.
Source: `faithful.md` FA-5 ("the Definition 17 domain is all of `A_d` and `UDT_{s°,ρ}(d) = Unif
argmax_a V_{s°}(ρ_d(a)) = Unif argmax_a V_B(δ_a)`"), with the value identity now proved on every
one-point tree
Kind: C
Fidelity: stronger (nested one-point trees included)
Hyps: (a) `MaskedPriorCalibrated (lift C') (Rel B) s°` -/
theorem polEv_V_onePoint (hcal : MaskedPriorCalibrated (lift {()} C') (relocRoot {()} B) s₀)
    (a : acts ()) :
    0 < s₀.pr (polEv {()} () a) ∧
      s₀.V (polEv {()} () a) = value (Proc.ofFun fun _ => a) B := by
  have hmem : () ∈ ({()} : Finset Unit) := Finset.mem_singleton_self _
  refine ⟨by rw [polEv_pr _ B C' s₀ hcal.2 hmem]; exact hcal.1 (.inl ()) a, ?_⟩
  rw [polEv_V_eq_value_reloc _ B C' s₀ hcal.2 hmem a (hcal.1 (.inl ()) a),
    deviatePure_unit_eq_ofFun, value_lift_ofFun _ B (queried_unit_subset B)]

/-- **T5(a) — L23, one point: `UDT_{s°,pol}(d) = Unif argmax_a V_B(δ_a)`** on every one-point tree
with `s°` masked-prior-calibrated under `lift C'`: faithful updateless choice at one point is the
best deterministic procedure (uniform over the best pure acts), whatever the full-support
self-model and whether or not the fiber is nested. (The *optimality* of this output is what
depends on nesting: `udtProc_onePoint_isOptimal_of_almostFair`, `amd_inclusion_not_optimal`.)
Scope: one queried point (`ι = Unit`), Definition 6, Definition 11 masked, the `pol` coordinate.
Source: `faithful.md` FA-5 ("`UDT_{s°,ρ}(d) = Unif argmax_a V_B(δ_a)`"); v2 amendment 5 ("One
point: … `UDT_{s°,ρ}` is the best deterministic procedure"); dp-cf-107, dp-core-056
Kind: C
Fidelity: stronger (every one-point tree; FA-5 assumes a value-faithful `ρ` exists — here the
`pol` coordinate is shown to be one)
Hyps: (a) `MaskedPriorCalibrated (lift C') (Rel B) s°` -/
theorem udtProc_onePoint (hcal : MaskedPriorCalibrated (lift {()} C') (relocRoot {()} B) s₀) :
    udtProc s₀ (polEv {()}) () = uniformArgmax fun a => value (Proc.ofFun fun _ => a) B := by
  rw [udtProc_eq_uniformArgmax s₀ (polEv {()}) () fun a => (polEv_V_onePoint B C' s₀ hcal a).1]
  have hf : (fun a => s₀.V (polEv {()} () a)) = fun a => value (Proc.ofFun fun _ => a) B :=
    funext fun a => (polEv_V_onePoint B C' s₀ hcal a).2
  rw [hf]

/-- **T5(b) — one point, non-nested: `UDT_{s°,pol}` is optimal.** On an almost-fair one-point tree
the uniform mixture over the best pure acts is optimal (affinity of `V_B` in `C(d)`): "optimal
exactly where determinism is optimal", the positive direction.
Scope: almost-fair one-point trees, Definition 6, Definition 11 masked.
Source: `faithful.md` FA-5 ("Hence `T_opt` holds … always when `F_d` is non-nested (Definition
21's multiaffinity)"); v2 Q10; dp-cf-107
Kind: C
Fidelity: exact (the direction "non-nested ⟹ optimal"; the converse has the tie caveat of the
findings)
Hyps: (a) `AlmostFair B`; (a) `MaskedPriorCalibrated (lift C') (Rel B) s°` -/
theorem udtProc_onePoint_isOptimal_of_almostFair (hB : AlmostFair B)
    (hcal : MaskedPriorCalibrated (lift {()} C') (relocRoot {()} B) s₀) :
    IsOptimal (udtProc s₀ (polEv {()})) B := by
  rw [isOptimal_udtProc_iff_support_subset_optima _ B C' s₀ hB (queried_unit_subset B) hcal]
  intro π hπ π'
  have hmem := hπ ()
  rw [mem_BR] at hmem
  have h := hmem (π' ())
  rw [deviatePure_unit_eq_ofFun, deviatePure_unit_eq_ofFun] at h
  have e1 : (fun _ : Unit => π' ()) = π' := by funext u; cases u; rfl
  have e2 : (fun _ : Unit => π ()) = π := by funext u; cases u; rfl
  rw [e1, e2] at h
  exact h

end onePoint

/-! ### T8: the R1 state and the R1-calibrated cUDT -/

section r1

variable (U : Finset ι) (C' : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **The R1 state at the disposition `pol_d = a`**: the prior-calibrated state of the deviated
self-model `lift (C'[d ↦ a])` on the relocated tree — "the law of `μ_{C'[d↦a]}` on dispositions",
Definition F2's R1 at the prior weighting, as a state on the enriched carrier.
Source: `faithful.md` FA-7′ (iv) ("`cf_{s°}(E_a) :=` law of `μ_{δ_a}` (R1-calibrated on
dispositions)"), Definition F2 (R1, prior `⊤`)
Kind: D -/
noncomputable def r1State (d : ι) (a : acts d) : State (RW Ω acts U) K :=
  priorState (lift U (C'.deviatePure d a)) (relocRoot U B)

/-- The R1 state puts probability one on its own disposition (`Success` at `pol_d = a`).
Source: `faithful.md` FA-7′ (iv); v2 Definition 2 (success)
Kind: L -/
theorem r1State_pr_self {d : ι} (h : d ∈ U) (a : acts d) :
    (r1State U C' B d a).pr (polEv U d a) = 1 := by
  unfold r1State
  rw [priorState_pr, nu_polEv U h]
  simp [Proc.deviatePure]

/-- **The R1 state's value of its disposition is the relocated value of the deviation**:
`V^{pol_d = a}(pol_d = a) = V_{Rel}(lift (C'[d ↦ a]))`, on every tree.
Source: `faithful.md` FA-7′ (iv)
Kind: P -/
theorem r1State_V_self {d : ι} (h : d ∈ U) (a : acts d) :
    (r1State U C' B d a).V (polEv U d a) = value (lift U (C'.deviatePure d a)) (relocRoot U B) := by
  unfold r1State
  rw [priorState_V, nu_polEv U h, paySum_polEv U B h, expPayoffPol_eq]
  have h1 : (Proc.deviatePure C' d a d).w a = 1 := by simp [Proc.deviatePure]
  have h2 : (C'.deviatePure d a).deviatePure d a = C'.deviatePure d a :=
    Proc.deviate_deviate C' d _ _
  simp only [h1, h2, one_mul, div_one]

/-- The R1 counterfactual structure on the `pol` events of `d` (junk elsewhere).
Source: `faithful.md` FA-7′ (iv)
Kind: D -/
noncomputable def r1Cf [Nonempty Ω] (d : ι) : Cf (RW Ω acts U) K :=
  Cf.ofEvents (polEv U) d fun a => r1State U C' B d a

/-- **T8(iv), general: the R1-calibrated cUDT is `Unif argmax_a V_{Rel}(lift (C'[d ↦ a]))`** on
every tree, with no prior state and no mask: the closed-domain faithful updateless procedure.
Source: `faithful.md` FA-7′ (iv) ("R1-calibrated cUDT is the closed-domain faithful updateless
procedure, no self-model mask needed")
Kind: C
Fidelity: exact
Hyps: none -/
theorem cudtProc_r1 [Nonempty Ω] {d : ι} (h : d ∈ U) :
    cudtProc (r1Cf U C' B d) (polEv U) d =
      uniformArgmax fun a => value (lift U (C'.deviatePure d a)) (relocRoot U B) := by
  unfold cudtProc
  congr 1
  funext a
  unfold r1Cf
  rw [Cf.ofEvents_apply (polEv U) d _ (polEv_injective U h), r1State_V_self U C' B h a]

/-- **T8(iv) + T9(b) on the self-locating carrier: R1-calibrated cUDT = masked UDT.** On almost-fair
`B`, for every `s°` masked-prior-calibrated under `lift C'`, `cUDT_{r1Cf, pol}(d) = UDT_{s°,pol}(d)
= Unif BR_d(C')` at every `d ∈ U`: the per-disposition cf slot and the self-locating prior state
carry one datum (FP-8′), and the two procedures coincide on this carrier (FP-20′(d), the
disposition level). The OC-carrier failure is `Carrier.lean`'s `mug1_oc_carrier_diverge`.
Source: `faithful.md` FA-7′ (iv)–(v); `firstperson.md` FP-20′(d) ("under PDC and with the
per-run-SSC carrier … `cUDT_{s°:=s_d,ρ} = UDT_{s°:=s_d,ρ}` at the disposition level")
Kind: C
Fidelity: exact (the self-locating state at the relocated root is the prior state, since every
run passes the root)
Hyps: (a) `AlmostFair B`; (a) `MaskedPriorCalibrated (lift U C') (Rel_U B) s°` -/
theorem cudtProc_r1_eq_udtProc [Nonempty Ω] (hB : AlmostFair B) (s₀ : State (RW Ω acts U) K)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) {d : ι} (h : d ∈ U) :
    cudtProc (r1Cf U C' B d) (polEv U) d = udtProc s₀ (polEv U) d ∧
      udtProc s₀ (polEv U) d = uniformOn (BR C' B d) (BR_nonempty C' B d) := by
  refine ⟨?_, udtProc_polEv_eq_bestReply U B C' s₀ hB hcal h⟩
  rw [cudtProc_r1 U C' B h, udtProc_polEv_eq_bestReply U B C' s₀ hB hcal h]
  have hf : (fun a => value (lift U (C'.deviatePure d a)) (relocRoot U B)) =
      fun a => value (C'.deviatePure d a) B :=
    funext fun a => AlmostFair.value_reloc hB U _
  simp only [uniformArgmax, hf]
  rfl

end r1

/-! ### T8(v): the evidential coincidence -/

section evidential

variable {Ω' : Type} [Fintype Ω'] [DecidableEq Ω'] (s₀ : State Ω' K)
  (ρ : (d : ι) → acts d → Finset Ω') (cf : Cf Ω' K)

/-- **T8(v) — Definition 20's evidential criterion makes cUDT and UDT coincide**: if the prior is
masked (every `ρ_d(a)` has positive prior probability, so the domain is all of `A_d`) and `cf`
agrees with Jeffrey conditioning of `s°` on every `ρ`-event, then `cUDT_{s°,ρ} = UDT_{s°,ρ}` on
every tree — `V^{ρ_d(a)}(ρ_d(a)) = V_{s°}(ρ_d(a) ∧ ρ_d(a)) = V_{s°}(ρ_d(a))`.
Source: `faithful.md` FA-7′ (i), (v) ("Coincidence: sufficient = masked prior (domain `A_d`) +
evidential criterion on the `ρ`-events"); [[decision-problems-v2]] §4 Definition 20 (the
evidential criterion)
Kind: L (one unfolding: `jeffreyCond_V` and `X ∩ X = X`; FA-7′(i)/(v) is near-definitional)
Fidelity: exact (general carrier, any `ρ`)
Hyps: (a) `∀ d a, 0 < P_{s°}(ρ_d(a))`; (a) `cf (ρ_d(a)) = jeffreyCond s° (ρ_d(a))` -/
theorem cudtProc_eq_udtProc_of_evidential (hpos : ∀ d a, 0 < s₀.pr (ρ d a))
    (hcf : ∀ d a, cf (ρ d a) = jeffreyCond s₀ (ρ d a) (hpos d a)) :
    cudtProc cf ρ = udtProc s₀ ρ := by
  funext d
  rw [udtProc_eq_uniformArgmax s₀ ρ d (hpos d)]
  unfold cudtProc
  congr 1
  funext a
  rw [hcf d a, jeffreyCond_V, Finset.inter_self]

/-- **T8(v) under `State.Agree`**: the evidential coincidence needs only *agreement* of
`cf (ρ_d(a))` with the Jeffrey conditioning (probabilities equal, desirabilities equal on
`P`-positive events), since `cUDT` reads `V` only at `ρ_d(a)`, which has probability `1` under
the conditioned state. This is the form `mug1_pdc_evidential_agree` delivers, so the SSC-carrier
identity `cudtProc = udtProc` follows for every parameter (`mug1_ssc_carrier_identity`).
Source: `faithful.md` FA-7′ (i), (v); [[decision-problems-v2]] §4 Definition 20; audit r1
(fidelity) N6
Kind: L
Fidelity: exact (general carrier, any `ρ`; `Agree` in place of state equality)
Hyps: (a) `∀ d a, 0 < P_{s°}(ρ_d(a))`; (a) `State.Agree (cf (ρ_d(a))) (jeffreyCond s° (ρ_d(a)))` -/
theorem cudtProc_eq_udtProc_of_evidential_agree (hpos : ∀ d a, 0 < s₀.pr (ρ d a))
    (hcf : ∀ d a, State.Agree (cf (ρ d a)) (jeffreyCond s₀ (ρ d a) (hpos d a))) :
    cudtProc cf ρ = udtProc s₀ ρ := by
  funext d
  rw [udtProc_eq_uniformArgmax s₀ ρ d (hpos d)]
  unfold cudtProc
  congr 1
  funext a
  have hP : (cf (ρ d a)).pr (ρ d a) = (jeffreyCond s₀ (ρ d a) (hpos d a)).pr (ρ d a) := by
    unfold State.pr
    rw [(hcf d a).1]
  have hpos' : 0 < (cf (ρ d a)).pr (ρ d a) := by
    rw [hP, jeffreyCond_pr, Finset.inter_self, div_self (hpos d a).ne']
    exact one_pos
  rw [(hcf d a).2 _ hpos', jeffreyCond_V, Finset.inter_self]

end evidential

end Cleanroom.Decision.DpFaithfulUdt
