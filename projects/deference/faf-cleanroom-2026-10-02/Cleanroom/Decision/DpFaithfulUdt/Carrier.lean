import Cleanroom.Decision.DpFaithfulUdt.Mugging

/-!
# The act/disposition asymmetry and the carrier-relative cUDT/UDT collapse (T9)

T9 of [[dp-faithful-udt-mandate]] (`firstperson.md` FP-3, FP-20′(d)).

* **FP-3, the asymmetry in success-axiom form** (`mug1_act_disposition_asymmetry`): under the
  pure-pay procedure on `B₁`, `ν(choice = pay) = ½` (the heads leaf-world reads `⊥`), while on the
  relocated carrier `ν(pol_d = pay) = 1` and `ν(pol_d = pay ∧ H) = ½`. So the deviation
  statistics are a success-obeying supposition (`P^a(a) = 1`) of the *disposition* event and
  never of the *act* event. The general form (`nu_lt_one_of_leaf`): whenever a leaf of positive
  law has a world outside `X`, `ν(X) < 1` — in every problem with a simulation branch the act
  event of the deviation has probability `< 1` (`nu_deviatePure_actEv_lt_one`).
* **FP-20′(d), the collapse is carrier-relative.** On `B₁` with the would-pay dispositions
  (`mugWp`, the realized-atom disposition events, unique by FA-3):
  - on the **self-locating (per-run SSC) carrier** — `s_d` the per-run state of the self-model
    (`occState`, which on `B₁` is the prior-calibrated state since `occ(d) = ⊤`) — the PDC
    counterfactual structure on the dispositions meets Definition 20's evidential criterion
    (`mug1_pdc_evidential_agree`: `cf(ρ_d(a))` *agrees* with the Jeffrey conditioning of `s_d`
    on `ρ_d(a)`), and `cUDT_{s_d,PDC} = UDT_{s_d,ρ}` as procedures for every parameter
    (`mug1_ssc_carrier_identity`), both paying when `y > x` (`mug1_ssc_carrier_collapse`);
  - on the **OC carrier** — `s` the strict-OC state at `O_T` (`dp-calibration`'s `mugState1`)
    with the same PDC `cf` — `UDT_{s,ρ}` refuses (`−x` vs `0`: the `H`-atoms of the disposition
    events are null, so the disposition value is the act value) while `cUDT_{s,PDC}` pays
    (`(y−x)/2` vs `0`): the two procedures diverge (`mug1_oc_carrier_diverge`).

  The collapse is therefore stated for the carrier, never unhedged (`firstperson.md` Dead, "the
  unhedged collapse"). The enriched-carrier (relocated, `pol`) form of the SSC-carrier identity is
  `OnePoint.lean`'s `cudtProc_r1_eq_udtProc`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ### The general form of the asymmetry -/

section general

variable (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **A leaf of positive law outside `X` keeps `ν(X)` below `1`.**
Source: `firstperson.md` FP-3 (the general reason the act event is not success-obeying "in every
problem with a simulation branch")
Kind: L -/
theorem nu_lt_one_of_leaf (X : Finset Ω) (ℓ₀ : B.Leaves) (hpos : 0 < leafLaw C B ℓ₀)
    (hw : world B ℓ₀ ∉ X) : nu C B X < 1 := by
  have h1 : nu C B X ≤ mass C B (Finset.univ.erase ℓ₀) := by
    unfold nu mass
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ
      rw [Finset.mem_erase]
      refine ⟨fun h => hw ?_, Finset.mem_univ _⟩
      unfold worldEv at hℓ
      rw [Finset.mem_filter] at hℓ
      rw [← h]; exact hℓ.2
    · intro ℓ _ _; exact leafLaw_nonneg C B ℓ
  have h2 : mass C B (Finset.univ.erase ℓ₀) = 1 - leafLaw C B ℓ₀ := by
    unfold mass
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_leafLaw]
  linarith

/-- **FP-3, general form**: if some run of positive law under every deviation at `d` has a world
satisfying no act event of `d` (a simulation branch whose world reads `⊥`), then the deviation
statistics give the act event probability `< 1` — Definition 20's success axiom is ill-typed on
act events there.
Source: `firstperson.md` FP-3 ("Def 20's counterfactual calibration is well-typed on dispositions,
ill-typed on acts, in every problem with a simulation branch")
Kind: L -/
theorem nu_deviatePure_actEv_lt_one (d : ι) (actEv : (d : ι) → acts d → Finset Ω)
    (ℓ₀ : B.Leaves) (hpos : ∀ a, 0 < leafLaw (C.deviatePure d a) B ℓ₀)
    (hw : ∀ a, world B ℓ₀ ∉ actEv d a) (a : acts d) :
    nu (C.deviatePure d a) B (actEv d a) < 1 :=
  nu_lt_one_of_leaf _ B _ ℓ₀ (hpos a) (hw a)

/-- `P_s({ω}) = P_s.w ω`. Source: none: infrastructure. Kind: L -/
theorem State.pr_singleton (s : State Ω K) (ω : Ω) : s.pr {ω} = s.P.w ω :=
  Finset.sum_singleton _ _

/-- **The per-run state is prior-calibrated when every run meets `d`** (`occ(d) = ⊤`): then
`P^{sl}_{s_d} = ν_C` and `V^{sl}_{s_d}(X) = 𝔼_C[r ∣ X]`.
Source: `firstperson.md` D5; [[decision-problems-v2]] Definition 11 (the one-point mugging: "the
state is exactly `ν_{C[d↦m]}`")
Kind: L -/
theorem occState_priorCalibrated_of_occ_univ (d : ι) (h : occ d B = Finset.univ)
    (hpos : 0 < mass C B (occ d B)) :
    PriorCalibrated C B (occState C B d hpos) := by
  have hev : ∀ X, occEv B d X = worldEv B X := by
    intro X; unfold occEv; rw [h, Finset.inter_univ]
  refine ⟨fun X => ?_, fun X hX => ?_⟩
  · rw [occState_pr, hev, h, mass_univ, div_one]; rfl
  · rw [occState_V, hev]
    have hp : occPay C B d X = paySum C B X := by
      unfold occPay paySum; rw [hev]
    rw [hp]
    show paySum C B X / nu C B X * nu C B X = paySum C B X
    rw [div_mul_cancel₀ _ hX.ne']

end general

/-! ### FP-3 on `B₁` -/

section mug

variable (x y : ℚ)

/-- **T9(a) — FP-3, the act/disposition asymmetry on `B₁`**: under `C[d ↦ pay]`,
`ν_{B₁}(choice = pay) = ½` (false on the heads leaf, whose choice coordinate reads `⊥`), while on
`B₁^{pol}` (the relocated carrier) `ν(pol_d = pay) = 1` and `ν(pol_d = pay ∧ H) = ½`. So the
deviation statistics are a success-obeying supposition of the disposition event, never of the
act event.
Source: `firstperson.md` FP-3 ("Under `C[d ↦ pay]` (Def 6): `ν_{B₁}(choice=pay) = ½` … while on
`B₁^{pol}` `ν(pol_d=pay) = 1`, `ν(pol_d=pay ∧ H) = ½`"); dp-cf-2-012
Kind: N+
Fidelity: exact (the stamped tree `B₁^{pol}` is the relocation `Rel_{{d}} B₁`, FR-7(a))
Hyps: none -/
theorem mug1_act_disposition_asymmetry :
    nu (Proc.ofFun fun _ => Act2.a) (mug1 x y) (mugActEv () .a) = 1 / 2 ∧
    nu (lift {()} (Proc.ofFun fun _ => Act2.a)) (relocRoot {()} (mug1 x y)) (polEv {()} () .a) = 1 ∧
    nu (lift {()} (Proc.ofFun fun _ => Act2.a)) (relocRoot {()} (mug1 x y))
      (preEv Prod.fst {MugW.hOne, MugW.hZero} ∩ polEv {()} () .a) = 1 / 2 := by
  have hmem : () ∈ ({()} : Finset Unit) := Finset.mem_singleton_self ()
  have hdev : (Proc.ofFun fun _ => Act2.a : Proc Unit (fun _ => Act2) ℚ).deviatePure () .a =
      Proc.ofFun fun _ => Act2.a := deviatePure_unit_eq_ofFun _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [mug1_nu]; simp [mugActEv]
  · rw [nu_polEv {()} hmem]; simp
  · rw [nu_preEv_inter_polEv {()} (mug1 x y) _ (mug1_almostFair x y) hmem, hdev, mug1_nu]
    simp

/-- The act event of the deviation is not success-obeying on `B₁` (the instance of the general
form: the heads leaf has law `½` under `δ_pay` and its world is `(H, ⊥, 1) ∉ {choice = pay}`).
Source: `firstperson.md` FP-3
Kind: L -/
theorem mug1_actEv_not_success : nu (Proc.ofFun fun _ => Act2.a) (mug1 x y) (mugActEv () .a) < 1 := by
  rw [(mug1_act_disposition_asymmetry x y).1]; norm_num

end mug

/-! ### FP-20′(d): the collapse on the self-locating carrier, its failure on the OC carrier -/

section carrier

variable (x y : ℚ) (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1)

/-- `μ(occ(d)) > 0` on `B₁` (it is `1`). Source: none: infrastructure. Kind: L -/
theorem mug1_occ_pos : 0 < mass (procQ q₀ h0.le h1.le) (mug1 x y) (occ () (mug1 x y)) := by
  rw [mug1_occ, mass_univ]; exact one_pos

/-- **The self-locating state `s_d` of the self-model `procQ q₀` on `B₁`** (D5's per-run SSC
state, FP-8′'s `P^{sl}`): the per-run state of the self-model at `d`.
Source: `firstperson.md` D5, FP-8′ ("Mugging: `P^{sl} = (q₀/2, (1−q₀)/2, q₀/2, (1−q₀)/2)`")
Kind: D -/
noncomputable abbrev mug1SscState : State MugW ℚ :=
  occState (procQ q₀ h0.le h1.le) (mug1 x y) () (mug1_occ_pos x y q₀ h0 h1)

/-- On `B₁` the self-locating state is the prior-calibrated state of the self-model (`occ(d) = ⊤`).
Source: `firstperson.md` FP-8′
Kind: L -/
theorem mug1SscState_priorCalibrated :
    PriorCalibrated (procQ q₀ h0.le h1.le) (mug1 x y) (mug1SscState x y q₀ h0 h1) :=
  occState_priorCalibrated_of_occ_univ _ _ () (mug1_occ x y) _

/-- The would-pay dispositions hold a.s. under their own deviation on `B₁` (success).
Source: `firstperson.md` FP-10 ("success puts `P^a(ρ_d(a)) = 1`")
Kind: L -/
theorem mug1_mugWp_successOn (a : Act2) :
    SuccessOn (procQ q₀ h0.le h1.le) (mug1 x y) () a (mugWp () a) := by
  unfold SuccessOn occEv
  rw [mug1_occ, Finset.inter_univ, mass_univ]
  have hdev : (procQ q₀ h0.le h1.le).deviatePure () a = Proc.ofFun fun _ => a :=
    deviatePure_unit_eq_ofFun _ _
  rw [hdev]
  show nu (Proc.ofFun fun _ => a) (mug1 x y) (mugWp () a) = 1
  rw [mug1_nu]
  cases a <;> simp [mugWp] <;> norm_num

/-- **`Π_B` on `B₁` with the would-pay dispositions pays** (`y > x`): `cUDT_{PDC}` evaluates the
dispositions at `(y−x)/2` vs `0`.
Source: `firstperson.md` FP-3 ("PDC gives … `V^{wp}(ρ_d(pay)) = ½(y − x)`"), FP-20′(d)
Kind: C
Fidelity: exact
Hyps: (a) `x < y`; (a) `0 < q₀ < 1` -/
theorem mug1_piB_pays (hxy : x < y) :
    cudtProc (pdcCf (procQ q₀ h0.le h1.le) (mug1 x y) () mugWp) mugWp () = FinDistr.pure Act2.a := by
  rw [piB_eq_ssa_argmax _ _ _ _ mugWp_injective (mug1_mugWp_successOn x y q₀ h0 h1)
    (mug1_occ_pos x y q₀ h0 h1)]
  obtain ⟨-, hVa, hVb⟩ := mug1_thm1_thm2_agree x y (procQ q₀ h0.le h1.le)
  apply uniformArgmax_eq_pure
  apply argmaxFull_act2_eq_a
  rw [hVa, hVb]; linarith

/-- **T9(b), the self-locating carrier — the collapse holds**: with `s° := s_d` the per-run SSC
state of the self-model and `cf := PDC` on the would-pay dispositions, `UDT_{s_d,ρ}` and
`cUDT_{s_d,PDC}` coincide on `B₁` (both pay when `y > x`). This is the `x < y` instance with the
outputs named; the identity for every parameter is `mug1_ssc_carrier_identity` (its third
conjunct follows from the first two here, the general one from the evidential mechanism).
Scope: the SSC carrier of `B₁` (one point, `occ(d) = ⊤`), realized-atom dispositions; the
enriched-carrier form is `cudtProc_r1_eq_udtProc`.
Source: `firstperson.md` FP-20′(d) ("under PDC *and with the per-run-SSC carrier* …
`cUDT_{s°:=s_d,ρ} = UDT_{s°:=s_d,ρ}` at the disposition level"); dp-cf-2-015
Kind: C
Fidelity: exact (carrier named)
Hyps: (a) `x < y`; (a) `0 < q₀ < 1` -/
theorem mug1_ssc_carrier_collapse (hxy : x < y) :
    udtProc (mug1SscState x y q₀ h0 h1) mugWp () = FinDistr.pure Act2.a ∧
    cudtProc (pdcCf (procQ q₀ h0.le h1.le) (mug1 x y) () mugWp) mugWp () = FinDistr.pure Act2.a ∧
    udtProc (mug1SscState x y q₀ h0 h1) mugWp () =
      cudtProc (pdcCf (procQ q₀ h0.le h1.le) (mug1 x y) () mugWp) mugWp () := by
  have hu := (mug1_wouldPay x y q₀ h0 h1 _ (mug1SscState_priorCalibrated x y q₀ h0 h1)).2.2.1 hxy
  have hc := mug1_piB_pays x y q₀ h0 h1 hxy
  exact ⟨hu, hc, hu.trans hc.symm⟩

/-- **FP-20′(d), the evidential criterion on the self-locating carrier**: the PDC state at the
disposition `ρ_d(a)` *agrees* (probabilities equal, desirabilities equal on `P`-positive events)
with the Jeffrey conditioning of the self-locating state `s_d` on `ρ_d(a)` — Definition 20's
evidential criterion holds for `cf` on the disposition events, which is why the two procedures
collapse there (`cudtProc_eq_udtProc_of_evidential` is the general mechanism).
Source: `firstperson.md` FP-20′(d) ("under PDC and with the per-run-SSC carrier, cf on
disposition events meets Def 20's evidential criterion"); [[decision-problems-v2]] §4 Definition 20
Kind: C
Fidelity: exact (agreement modulo junk desirabilities on null events)
Hyps: (a) `0 < q₀ < 1` -/
theorem mug1_pdc_evidential_agree (a : Act2) :
    State.Agree (pdcState (procQ q₀ h0.le h1.le) (mug1 x y) () a)
      (jeffreyCond (mug1SscState x y q₀ h0 h1) (mugWp () a)
        ((mugWp_lawFaithful x y q₀ h0 h1 _ (mug1SscState_priorCalibrated x y q₀ h0 h1) a).1)) := by
  have hlf := mugWp_lawFaithful x y q₀ h0 h1 (mug1SscState x y q₀ h0 h1)
    (mug1SscState_priorCalibrated x y q₀ h0 h1) a
  obtain ⟨hE, hw, hV⟩ := hlf
  have hguard : 0 < mass ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y)
      (occ () (mug1 x y)) := by
    rw [mug1_occ, mass_univ]; exact one_pos
  have hev : ∀ X, occEv (mug1 x y) () X = worldEv (mug1 x y) X := by
    intro X; unfold occEv; rw [mug1_occ, Finset.inter_univ]
  -- the PDC state's probabilities and desirabilities
  have hpr : ∀ X, (pdcState (procQ q₀ h0.le h1.le) (mug1 x y) () a).pr X =
      nu ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y) X := by
    intro X
    unfold pdcState
    rw [dif_pos hguard, occState_pr, hev, mug1_occ, mass_univ, div_one]
    rfl
  have hVp : ∀ X, (pdcState (procQ q₀ h0.le h1.le) (mug1 x y) () a).V X =
      paySum ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y) X /
        nu ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y) X := by
    intro X
    unfold pdcState
    rw [dif_pos hguard, occState_V, hev]
    unfold occPay paySum
    rw [hev]
    rfl
  -- the law-faithfulness clauses in the self-model's `procQ` form
  have hw' : ∀ X, (mug1SscState x y q₀ h0 h1).pr (X ∩ mugWp () a) =
      (mug1SscState x y q₀ h0 h1).pr (mugWp () a) *
        nu ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y) X := by
    intro X; have := hw X; rw [preEv_id] at this; exact this
  have hV' : ∀ X, (mug1SscState x y q₀ h0 h1).V (X ∩ mugWp () a) *
      (mug1SscState x y q₀ h0 h1).pr (X ∩ mugWp () a) =
      (mug1SscState x y q₀ h0 h1).pr (mugWp () a) *
        paySum ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y) X := by
    intro X; have := hV X; rw [preEv_id] at this; exact this
  refine ⟨?_, fun X hX => ?_⟩
  · apply FinDistr.ext'
    intro ω
    rw [← State.pr_singleton, ← State.pr_singleton, hpr, jeffreyCond_pr, eq_div_iff hE.ne', hw' {ω}]
    exact mul_comm _ _
  · rw [hpr] at hX
    rw [hVp, jeffreyCond_V, div_eq_iff hX.ne']
    have h3 : (mug1SscState x y q₀ h0 h1).V (X ∩ mugWp () a) *
        ((mug1SscState x y q₀ h0 h1).pr (mugWp () a) *
          nu ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y) X) =
        (mug1SscState x y q₀ h0 h1).pr (mugWp () a) *
          paySum ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y) X := by
      rw [← hw' X]; exact hV' X
    have h4 : (mug1SscState x y q₀ h0 h1).pr (mugWp () a) *
        ((mug1SscState x y q₀ h0 h1).V (X ∩ mugWp () a) *
          nu ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y) X) =
        (mug1SscState x y q₀ h0 h1).pr (mugWp () a) *
          paySum ((procQ q₀ h0.le h1.le).deviatePure () a) (mug1 x y) X := by
      rw [← h3]; ring
    exact (mul_left_cancel₀ hE.ne' h4).symm

/-- **T9(b), the SSC carrier — the identity, for every parameter**: with `s° := s_d` and
`cf := PDC` on the would-pay dispositions, `cUDT_{s_d,PDC} = UDT_{s_d,ρ}` on `B₁` *as
procedures*, for every `x, y` and self-model `q₀ ∈ (0,1)` — by the evidential mechanism
(`mug1_pdc_evidential_agree` chained with `cudtProc_eq_udtProc_of_evidential_agree`), not by
comparing outputs. `mug1_ssc_carrier_collapse` is its `x < y` instance with the outputs named.
Scope: the SSC carrier of `B₁`, realized-atom dispositions.
Source: `firstperson.md` FP-20′(d) ("under PDC *and with the per-run-SSC carrier* …
`cUDT_{s°:=s_d,ρ} = UDT_{s°:=s_d,ρ}` at the disposition level"); dp-cf-2-015; audit r1
(fidelity) N6
Kind: C
Fidelity: exact (carrier named; all parameters)
Hyps: (a) `0 < q₀ < 1` -/
theorem mug1_ssc_carrier_identity :
    cudtProc (pdcCf (procQ q₀ h0.le h1.le) (mug1 x y) () mugWp) mugWp =
      udtProc (mug1SscState x y q₀ h0 h1) mugWp := by
  have hpos : ∀ (d : Unit) (a : Act2), 0 < (mug1SscState x y q₀ h0 h1).pr (mugWp d a) := by
    intro d a
    cases d
    exact (mugWp_lawFaithful x y q₀ h0 h1 _ (mug1SscState_priorCalibrated x y q₀ h0 h1) a).1
  refine cudtProc_eq_udtProc_of_evidential_agree _ _ _ hpos fun d a => ?_
  cases d
  rw [pdcCf, Cf.ofEvents_apply mugWp _ _ mugWp_injective]
  exact mug1_pdc_evidential_agree x y q₀ h0 h1 a

/-- **T5(b)'s witness on `B₁`, on the relocated carrier**: under any masked prior calibrated to a
full-support self-model on `Rel B₁`, `UDT_{s°,pol}` pays when `y > x`
(`V_B(δ_pay) = (y−x)/2 > 0 = V_B(δ_refuse)`), by `udtProc_onePoint`.
Source: `faithful.md` FA-5; mandate T5(b) ("`mug1 x y`, `0 < x < y`: `udtProc` pays, value
`(y−x)/2`"); audit r1 (fidelity) N1
Kind: N+
Fidelity: exact
Hyps: (a) `x < y`; (a) `MaskedPriorCalibrated (lift C') (Rel B₁) s°` -/
theorem mug1_udtProc_onePoint_pays (hxy : x < y) (C' : Proc Unit (fun _ => Act2) ℚ)
    (s₀ : State (RW MugW (fun _ => Act2) {()}) ℚ)
    (hcal : MaskedPriorCalibrated (lift {()} C') (relocRoot {()} (mug1 x y)) s₀) :
    udtProc s₀ (polEv {()}) () = FinDistr.pure Act2.a := by
  rw [udtProc_onePoint (mug1 x y) C' s₀ hcal]
  apply uniformArgmax_eq_pure
  apply argmaxFull_act2_eq_a
  rw [mug1_value_pay, mug1_value_refuse]
  linarith

/-- **T9(b), the OC carrier — the collapse fails**: with `s :=` the strict-OC state at `O_T`
(`dp-calibration`'s `mugState1`, Proposition 6's state) and the *same* PDC `cf` on the would-pay
dispositions, `UDT_{s,ρ}` refuses (the disposition values are `−x` vs `0`: the `H`-atoms of the
disposition events are null under the OC state, so the disposition values are the act values)
while `cUDT_{s,PDC}` pays (`(y−x)/2` vs `0`). The two procedures disagree on a four-world state.
Scope: the OC carrier of `B₁`; the identity of T9(b) holds on the SSC carrier only.
Source: `firstperson.md` FP-20′(d) ("with an OC-calibrated `(P_s, V_s)` the two diverge on the
no-doubt mugging (UDT refuses, `−x` vs `0`; cUDT pays, `(y−x)/2` vs `0`) and the criterion
fails"); Dead ("the unhedged collapse"); dp-cf-2-015
Kind: N+
Fidelity: exact
Hyps: (a) `0 < x < y`; (a) `0 < q₀ < 1` -/
theorem mug1_oc_carrier_diverge (hx : 0 < x) (hxy : x < y) :
    udtProc (mugState1 x y q₀ h0.le h1.le) mugWp () = FinDistr.pure Act2.b ∧
    cudtProc (pdcCf (procQ q₀ h0.le h1.le) (mug1 x y) () mugWp) mugWp () = FinDistr.pure Act2.a := by
  refine ⟨?_, mug1_piB_pays x y q₀ h0 h1 hxy⟩
  have hA : mugWp () .a ∩ mugObs () = {MugW.tPay} := by decide
  have hB : mugWp () .b ∩ mugObs () = {MugW.tRefuse} := by decide
  have hO : 0 < nu (procQ q₀ h0.le h1.le) (mug1 x y) (mugObs ()) := by
    rw [mug1_nu]; simp [mugObs, procQ]; linarith
  have hnA : nu (procQ q₀ h0.le h1.le) (mug1 x y) {MugW.tPay} = 1 / 2 * q₀ := by
    rw [mug1_nu]; simp [procQ]
  have hnB : nu (procQ q₀ h0.le h1.le) (mug1 x y) {MugW.tRefuse} = 1 / 2 * (1 - q₀) := by
    rw [mug1_nu]; simp [procQ]
  have hpA : paySum (procQ q₀ h0.le h1.le) (mug1 x y) {MugW.tPay} = 1 / 2 * q₀ * (-x) := by
    rw [mug1_paySum]; simp [procQ]
  have hpB : paySum (procQ q₀ h0.le h1.le) (mug1 x y) {MugW.tRefuse} = 0 := by
    rw [mug1_paySum]; simp
  have hpos : ∀ a, 0 < (mugState1 x y q₀ h0.le h1.le).pr (mugWp () a) := by
    intro a
    unfold mugState1
    rw [calibratedState_pr]
    cases a
    · rw [hA, hnA]; exact div_pos (by linarith) hO
    · rw [hB, hnB]; exact div_pos (by linarith) hO
  have hVa : (mugState1 x y q₀ h0.le h1.le).V (mugWp () .a) = -x := by
    unfold mugState1
    rw [calibratedState_V, hA, hnA, hpA]
    field_simp
  have hVb : (mugState1 x y q₀ h0.le h1.le).V (mugWp () .b) = 0 := by
    unfold mugState1
    rw [calibratedState_V, hB, hpB, zero_div]
  rw [udtProc_eq_uniformArgmax _ _ _ hpos]
  apply uniformArgmax_eq_pure
  apply argmaxFull_act2_eq_b
  rw [hVa, hVb]; linarith

end carrier

end Cleanroom.Decision.DpFaithfulUdt
