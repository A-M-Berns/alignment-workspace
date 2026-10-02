import Cleanroom.Decision.DpDevicesCatalog.Values
import Cleanroom.Decision.DpLocalOpt.Ssa
import Cleanroom.Decision.DpCalibration.ToldYouSo
import Cleanroom.Decision.DpCalibration.Theories

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T5(a)–(c): Told-You-So (v2 §7.1, Proposition 8's value clause)

* (a) Proposition 8's value clause: every zero-respecting procedure (for the stipulated
  states) has `V = 5`; every procedure taking `ten` at both points has `V = 10`; `C*` is
  `V`-optimal.
* (b) DY-5's static separations: `C₀` is not pure-Definition-22-coherent at `d₅` and `C*` is
  coherent; Theorem 1 at `d₅` under `C₀` is `5` vs `10` (and `5` vs `10 − 5ε/2` under the
  tremble); Theorem 2 at `d₅` is `5` vs `10`; the bridge `fiberForced = siaSum` identifies D3⁰
  (`OccEdtConsistent`) with Theorem 1's condition, and `C*` satisfies it, `C₀` does not.
* (c) Remark 3.12 read literally (the typed device D2, `D2At` / `EventTrembleEdtConsistent`
  with Definition 18's escape clause) **inverts**: it approves `C₀` and rejects `C*` at every
  `ε`, because `ν_{C*^ε}(· ∣ O₅) = δ_{(5,5)}` exactly, so `A⁺_{d₅}(ε) = {five} ⊉ supp C*(d₅)`.
  v2's §7.1 remarks (2)/(4) presuppose a draw-conditioned evaluator (findings F1).

Inherited, not re-proved: the calibration clauses (`tys_fiveTen_strictOC/maskedOC/limitOC`,
`tys_take10_strictOC/limitOC`) and the refuted masked clause for `C*`
(`tys_take10_not_maskedOCV`, dp-calibration findings F2).
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-! ## (a) Proposition 8's value clause -/

/-- `A⁺_{d₅} = {five}` for the stipulated states. Source: none: infrastructure. Kind: L -/
theorem tys_aPlus_five : APlus tysState tysActEv .five = {.five} := by
  ext a; cases a <;> simp [APlus, tysState, State.dirac_pr, tysActEv]

/-- `A⁺_{d₁₀} = {ten}` for the stipulated states. Source: none: infrastructure. Kind: L -/
theorem tys_aPlus_ten : APlus tysState tysActEv .ten = {.ten} := by
  ext a; cases a <;> simp [APlus, tysState, State.dirac_pr, tysActEv]

/-- **Proposition 8, the value clause for `C₀`, for every zero-respecting procedure**: with the
stipulated states, `P_{s₅}(m=10) = 0` forces `C(d₅) = δ_five`, hence `V_{B_P}(C) = 5` whatever
`C(d₁₀)` is.
Source: [[decision-problems-v2]] §7.1 Proposition 8 ("`V(C₀) = 5`", `C₀` any zero-respecting
procedure)
Kind: P
Fidelity: exact (every zero-respecting `C`, not one representative)
Hyps: (a) zero-respecting for `tysState` -/
theorem tys_value_of_zeroRespecting (C : Proc Five10 (fun _ => Five10) ℚ)
    (h : ZeroRespecting tysState tysActEv C) : value C toldYouSo = 5 := by
  have hten : (C .five).w .ten = 0 := by
    by_contra hne
    have hpos : 0 < (C .five).w .ten := lt_of_le_of_ne ((C .five).nonneg _) (Ne.symm hne)
    have := h .five (by rw [tys_aPlus_five]; exact ⟨.five, by simp⟩) .ten hpos
    rw [tys_aPlus_five] at this
    simp at this
  rw [toldYouSo_value_all, hten]; ring

/-- **Proposition 8, the value clause for `C*`**: a procedure taking `ten` at both points has
`V_{B_P} = 10`.
Source: [[decision-problems-v2]] §7.1 Proposition 8 ("`10 = V(C*)`")
Kind: P
Fidelity: exact -/
theorem tys_value_of_take10 (C : Proc Five10 (fun _ => Five10) ℚ)
    (h5 : (C .five).w .ten = 1) (h10 : (C .ten).w .ten = 1) : value C toldYouSo = 10 := by
  rw [toldYouSo_value_all, h5, h10]; ring

/-- `V(C₀) = 5`. Source: v2 Prop. 8. Kind: N+ -/
theorem procFiveTen_value : value procFiveTen toldYouSo = 5 :=
  tys_value_of_zeroRespecting _ tys_zeroRespecting.1

/-- `V(C*) = 10`. Source: v2 Prop. 8. Kind: N+ -/
theorem procTake10_value : value procTake10 toldYouSo = 10 :=
  tys_value_of_take10 _ (by simp [procTake10]) (by simp [procTake10])

/-- **`C*` is `V`-optimal on Told-You-So** (`5(1−u) + u(10v + 5(1−v)) ≤ 10` on `[0,1]²`).
Source: [[decision-problems-v2]] §7.1 Proposition 8 ("`UDT_{B_P}`"); `calibration.md` CA-20′
(the `V`-optimal row, Told-You-So column `C*`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem procTake10_isOptimal : IsOptimal procTake10 toldYouSo := by
  intro C'
  rw [procTake10_value, toldYouSo_value_all]
  have hu0 := (C' .five).nonneg .ten
  have hu1 := (C' .five).w_le_one .ten
  have hv0 := (C' .ten).nonneg .ten
  have hv1 := (C' .ten).w_le_one .ten
  nlinarith [mul_nonneg hu0 (sub_nonneg.2 hv1)]

/-! ## (b) DY-5's static separations -/

/-- `C₀[d₅ ↦ ten]` is `C*` (as procedures). Source: none: infrastructure. Kind: L -/
theorem procFiveTen_deviatePure_five_ten : procFiveTen.deviatePure .five .ten = procTake10 := by
  funext d; cases d
  · simp [Proc.deviatePure, Proc.deviate, procTake10, Proc.ofFun]
  · simp [Proc.deviatePure, Proc.deviate, procFiveTen, procTake10, Proc.ofFun]

/-- **DY-5: `C₀` is not (pure) Definition-22-coherent at `d₅`**: the deviation `d₅ ↦ ten` yields
`10 > 5`.
Source: `dynamic.md` DY-5 ("Def-22 coherence rejects `C₀` (deviation `d₅ ↦ 10` yields
`10 > 5`)"); dp-cf-121
Kind: P
Fidelity: exact -/
theorem procFiveTen_not_coherentPureAt_five : ¬ CoherentPureAt procFiveTen toldYouSo .five := by
  intro h
  have := h .ten
  rw [procFiveTen_deviatePure_five_ten, procTake10_value, procFiveTen_value] at this
  norm_num at this

/-- **DY-5: `C*` is (mixed) Definition-22-coherent** (it is optimal).
Source: `dynamic.md` DY-5 ("holds for `C*`")
Kind: C
Fidelity: exact (mixed, A30) -/
theorem procTake10_coherent : Coherent procTake10 toldYouSo :=
  IsOptimal.coherent _ _ procTake10_isOptimal

/-- **Theorem 1's functional at `d₅`** for every procedure: `Φ_{d₅}(C, five) = 5`,
`Φ_{d₅}(C, ten) = 10 C(d₁₀)(ten) + 5 C(d₁₀)(five)`.
Source: [[decision-problems-v2]] §8 Theorem 1 on `B_P`; `dynamic.md` DY-5
Kind: P
Fidelity: exact -/
theorem tys_siaSum_five (C : Proc Five10 (fun _ => Five10) ℚ) :
    siaSum C toldYouSo .five .five = 5 ∧
    siaSum C toldYouSo .five .ten = 10 * (C .ten).w .ten + 5 * (C .ten).w .five := by
  constructor <;>
  · simp [toldYouSo, siaSum_decision, Five10.sum_univ, value_decision, value_leaf]
    try ring

/-- **Theorem 1's functional at `d₁₀`** for every procedure: `Φ_{d₁₀}(C, a) = C(d₅)(ten) ·
val(a)` (`10` for `ten`, `5` for `five`).
Source: [[decision-problems-v2]] §8 Theorem 1 on `B_P`
Kind: P
Fidelity: exact -/
theorem tys_siaSum_ten (C : Proc Five10 (fun _ => Five10) ℚ) :
    siaSum C toldYouSo .ten .ten = (C .five).w .ten * 10 ∧
    siaSum C toldYouSo .ten .five = (C .five).w .ten * 5 := by
  constructor <;>
  · simp [toldYouSo, siaSum_decision, Five10.sum_univ, value_decision, value_leaf]

/-- **DY-5, Theorem 1 at `d₅` under `C₀`: `5` vs `10`**, argmax `{ten}`; so `C₀` is not
Theorem-1-ratifiable at `d₅`.
Source: `dynamic.md` DY-5 ("Theorem 1 at `d₅` … argmax `{10}`")
Kind: P
Fidelity: exact -/
theorem procFiveTen_sia_five :
    siaSum procFiveTen toldYouSo .five .five = 5 ∧ siaSum procFiveTen toldYouSo .five .ten = 10 ∧
    ¬ Thm1At procFiveTen toldYouSo .five := by
  obtain ⟨h5, h10⟩ := tys_siaSum_five procFiveTen
  have h10' : siaSum procFiveTen toldYouSo .five .ten = 10 := by
    rw [h10]; simp [procFiveTen]
  refine ⟨h5, h10', fun h => ?_⟩
  have := h .five (by simp [procFiveTen]) .ten
  rw [h5, h10'] at this
  norm_num at this

/-- **DY-5, Theorem 1 at `d₅` under the tremble `C₀^ε`: `5` vs `10 − 5ε/2`**.
Source: `dynamic.md` DY-5 ("Theorem 1 at `d₅` under `C₀^ε`: `5` vs `10 − 5ε/2`")
Kind: P
Fidelity: exact -/
theorem procFiveTen_tremble_sia_five (ε : ℚ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    siaSum (tremble procFiveTen ε h0 h1) toldYouSo .five .five = 5 ∧
    siaSum (tremble procFiveTen ε h0 h1) toldYouSo .five .ten = 10 - 5 * ε / 2 := by
  obtain ⟨h5, h10⟩ := tys_siaSum_five (tremble procFiveTen ε h0 h1)
  refine ⟨h5, ?_⟩
  rw [h10]
  simp [tremble_w, procFiveTen, Proc.ofFun_w, five10_card]
  ring

/-- `occ(d₅)` is every run of `B_P` (the root queries `d₅`).
Source: none: infrastructure
Kind: L -/
theorem tys_occ_five : occ .five toldYouSo = Finset.univ := by
  ext ℓ
  unfold toldYouSo at ℓ ⊢
  rcases ℓ with ⟨a, ℓ⟩
  cases a <;> simp [count_decision]

/-- Theorem 2's evaluator at `d₅` is `V(C[d₅ ↦ m])` (`occ(d₅) = Leaves`).
Source: none: infrastructure (Remark 7.1's mechanism on `B_P`)
Kind: L -/
theorem tys_ssaValue_five (C : Proc Five10 (fun _ => Five10) ℚ) (m : FinDistr ℚ Five10) :
    ssaValue C toldYouSo .five m = value (C.deviate .five m) toldYouSo := by
  rw [ssaValue_eq_div, tys_occ_five, mass_univ, div_one, value_deviate_eq_ssaNum_add_offOcc]
  have : offOcc C toldYouSo .five = 0 := by unfold offOcc; rw [tys_occ_five]; simp
  rw [this, add_zero]

/-- **DY-5, Theorem 2 at `d₅` under `C₀`: `5` vs `10`**.
Source: `dynamic.md` DY-5 ("Theorem 2 at `d₅`: `5` vs `10`, argmax `{10}`")
Kind: P
Fidelity: exact -/
theorem procFiveTen_ssa_five :
    ssaValue procFiveTen toldYouSo .five (FinDistr.pure .five) = 5 ∧
    ssaValue procFiveTen toldYouSo .five (FinDistr.pure .ten) = 10 := by
  rw [tys_ssaValue_five, tys_ssaValue_five]
  have h1 : procFiveTen.deviate .five (FinDistr.pure .five) = procFiveTen := by
    funext d; cases d <;> simp [Proc.deviate, procFiveTen, Proc.ofFun]
  rw [h1, procFiveTen_value]
  exact ⟨rfl, by rw [← procTake10_value]; congr 1; exact procFiveTen_deviatePure_five_ten⟩

/-! ### The bridge D3⁰ = Theorem 1 -/

/-- **`fiberForced` is `siaSum`**: dp-calibration's fiber-summed forced payoff mass (the body of
D3 / D3⁰) is dp-local-opt's Theorem-1 functional, by `siaSum_eq_sum_fiber_forcedBelow`.
Source: `calibration.md` Devices (D3⁰ "= Theorem 1's condition"); mandate T8
Kind: L -/
theorem fiberForced_eq_siaSum {Ω ι : Type} [DecidableEq ι] {acts : ι → Type}
    [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (C : Proc ι acts ℚ)
    (B : Tree Ω ι acts ℚ) (d : ι) (a : acts d) :
    fiberForced B (NodePolicy.ofProc C B) d a = siaSum C B d a := by
  rw [siaSum_eq_sum_fiber_forcedBelow]
  unfold fiberForced
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with h
  · subst h; rfl
  · rfl

/-- **D3⁰ is Theorem 1's condition** at every queried point.
Source: `calibration.md` Devices (D3⁰ "Theorem 1's local-optimality condition proper")
Kind: L -/
theorem occEdtConsistent_iff_thm1 {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    [∀ d, Nonempty (acts d)] (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) :
    OccEdtConsistent C B ↔ Thm1 C B := by
  simp only [OccEdtConsistent, Thm1, Thm1At, fiberForced_eq_siaSum]

/-- **D3 with `ε > 0` is Theorem 1's condition under the tremble `C^ε`** for all small `ε`.
Source: `calibration.md` Devices (D3)
Kind: L -/
theorem occTrembleEdtConsistent_iff {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    [∀ d, Nonempty (acts d)] (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) :
    OccTrembleEdtConsistent C B ↔
      ∃ ε₀ > (0 : ℚ), ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
        ∀ d ∈ queried B, ∀ a, 0 < (C d).w a → ∀ b,
          siaSum (tremble C ε h0.le h1) B d b ≤ siaSum (tremble C ε h0.le h1) B d a := by
  simp only [OccTrembleEdtConsistent, fiberForced_eq_siaSum]

/-- **`C*` satisfies D3⁰** (Theorem 1 at both points: `5 ≤ 10` at `d₅`, `5 ≤ 10` at `d₁₀`), and
`C₀` does not (at `d₅`).
Source: `calibration.md` CA-20′ (D3⁰ row, Told-You-So column `C*`); `dynamic.md` DY-5
Kind: P
Fidelity: exact -/
theorem procTake10_occEdtConsistent :
    OccEdtConsistent procTake10 toldYouSo ∧ ¬ OccEdtConsistent procFiveTen toldYouSo := by
  rw [occEdtConsistent_iff_thm1, occEdtConsistent_iff_thm1]
  constructor
  · intro d _ a ha b
    obtain ⟨h55, h5t⟩ := tys_siaSum_five procTake10
    obtain ⟨htt, ht5⟩ := tys_siaSum_ten procTake10
    have h5t' : siaSum procTake10 toldYouSo .five .ten = 10 := by rw [h5t]; simp [procTake10]
    have htt' : siaSum procTake10 toldYouSo .ten .ten = 10 := by rw [htt]; simp [procTake10]
    have ht5' : siaSum procTake10 toldYouSo .ten .five = 5 := by rw [ht5]; simp [procTake10]
    simp only [procTake10, Proc.ofFun_w] at ha
    have ha' : a = .ten := by by_contra h; simp [h] at ha
    subst ha'
    cases d <;> cases b <;> simp only [h55, h5t', htt', ht5'] <;> norm_num
  · intro h
    exact procFiveTen_sia_five.2.2 (h .five (tys_queried .five))

/-- **`C*` satisfies D3 at every tremble size** (`5 ≤ 10 − 5ε/2` at `d₅`; at `d₁₀` the forced
values are `C^ε(d₅)(ten) · {5, 10}`); at `ε = 1/100` the `d₅` comparison is `5` vs `399/40`.
Source: `calibration.md` CA-20′ (D3 row: "`C*` (`5 < 399/40`)")
Kind: P
Fidelity: exact (every `ε ∈ (0, 1]`, hence D3 with `ε₀ = 1`) -/
theorem procTake10_occTrembleEdtConsistent :
    OccTrembleEdtConsistent procTake10 toldYouSo ∧
    siaSum (tremble procTake10 (1/100) (by norm_num) (by norm_num)) toldYouSo .five .ten = 399/40 := by
  constructor
  · rw [occTrembleEdtConsistent_iff]
    refine ⟨1, one_pos, fun ε h0 h1 _ d _ a ha b => ?_⟩
    obtain ⟨h55, h5t⟩ := tys_siaSum_five (tremble procTake10 ε h0.le h1)
    obtain ⟨htt, ht5⟩ := tys_siaSum_ten (tremble procTake10 ε h0.le h1)
    have h5t' : siaSum (tremble procTake10 ε h0.le h1) toldYouSo .five .ten = 10 - 5 * ε / 2 := by
      rw [h5t]; simp [tremble_w, procTake10, Proc.ofFun_w, five10_card]; ring
    have htt' : siaSum (tremble procTake10 ε h0.le h1) toldYouSo .ten .ten = (1 - ε / 2) * 10 := by
      rw [htt]; simp [tremble_w, procTake10, Proc.ofFun_w, five10_card]; ring
    have ht5' : siaSum (tremble procTake10 ε h0.le h1) toldYouSo .ten .five = (1 - ε / 2) * 5 := by
      rw [ht5]; simp [tremble_w, procTake10, Proc.ofFun_w, five10_card]; ring
    simp only [procTake10, Proc.ofFun_w] at ha
    have ha' : a = .ten := by by_contra h; simp [h] at ha
    subst ha'
    cases d <;> cases b <;> simp only [h55, h5t', htt', ht5'] <;> nlinarith
  · rw [(tys_siaSum_five _).2]
    simp [tremble_w, procTake10, Proc.ofFun_w, five10_card]
    norm_num

/-! ## (c) The typed Remark-3.12 device inverts -/

/-- `nuPoly (O₅) ≠ 0` for every procedure (the leaf `(5,5)` is chance-positive).
Source: none: infrastructure. Kind: L -/
theorem tys_nuPoly_obs_five_ne_zero (C : Proc Five10 (fun _ => Five10) ℚ) :
    nuPoly C toldYouSo (tysObs .five) ≠ 0 := by
  rw [nuPoly_ne_zero_iff]
  refine ⟨⟨.five, ()⟩, by simp [tysObs, toldYouSo], ?_⟩
  unfold toldYouSo; simp [chanceWeight]

/-- `nuPoly (O₁₀) ≠ 0` for every procedure. Source: none: infrastructure. Kind: L -/
theorem tys_nuPoly_obs_ten_ne_zero (C : Proc Five10 (fun _ => Five10) ℚ) :
    nuPoly C toldYouSo (tysObs .ten) ≠ 0 := by
  rw [nuPoly_ne_zero_iff]
  refine ⟨⟨.ten, .ten, ()⟩, by simp [tysObs, toldYouSo], ?_⟩
  unfold toldYouSo; simp [chanceWeight]

/-- The four action-within-observation events of `B_P`, as subsets of the three leaf-worlds:
`{m=5} ∧ O₅ = {(5,5)}`, `{m=10} ∧ O₅ = ∅` (no leaf-world), `{m=10} ∧ O₁₀ = {(10,10)}`,
`{m=5} ∧ O₁₀ = {(10,5)}`. Source: none: infrastructure. Kind: L -/
theorem tys_actEv_obs_mem :
    ((Five10.five, Five10.five) ∈ tysActEv .five .five ∩ tysObs .five ∧
      (Five10.ten, Five10.ten) ∉ tysActEv .five .five ∩ tysObs .five ∧
      (Five10.ten, Five10.five) ∉ tysActEv .five .five ∩ tysObs .five) ∧
    ((Five10.five, Five10.five) ∉ tysActEv .five .ten ∩ tysObs .five ∧
      (Five10.ten, Five10.ten) ∉ tysActEv .five .ten ∩ tysObs .five ∧
      (Five10.ten, Five10.five) ∉ tysActEv .five .ten ∩ tysObs .five) ∧
    ((Five10.five, Five10.five) ∉ tysActEv .ten .ten ∩ tysObs .ten ∧
      (Five10.ten, Five10.ten) ∈ tysActEv .ten .ten ∩ tysObs .ten ∧
      (Five10.ten, Five10.five) ∉ tysActEv .ten .ten ∩ tysObs .ten) ∧
    ((Five10.five, Five10.five) ∉ tysActEv .ten .five ∩ tysObs .ten ∧
      (Five10.ten, Five10.ten) ∉ tysActEv .ten .five ∩ tysObs .ten ∧
      (Five10.ten, Five10.five) ∈ tysActEv .ten .five ∩ tysObs .ten) := by
  simp [tysActEv, tysObs]

/-- **`ν_{C^ε}(· ∧ O₅)` on `B_P` under the tremble of any procedure**: the `five` act event
within `O₅` has mass `C^ε(d₅)(five)`, the `ten` act event within `O₅` has mass `0` — no
leaf-world has `n = 5 ∧ m = 10`.
Source: `dynamic.md` DY-5 ("`ν_{C*^ε}(· ∣ O₅) = δ_{(5,5)}` exactly")
Kind: P
Fidelity: exact -/
theorem tys_tremble_nu_five (C : Proc Five10 (fun _ => Five10) ℚ) (ε : ℚ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) :
    nu (tremble C ε h0 h1) toldYouSo (tysActEv .five .five ∩ tysObs .five) =
      (tremble C ε h0 h1 .five).w .five ∧
    nu (tremble C ε h0 h1) toldYouSo (tysActEv .five .ten ∩ tysObs .five) = 0 := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, -, -⟩ := tys_actEv_obs_mem
  constructor
  · rw [tys_nu]; simp [a1, a2, a3]
  · rw [tys_nu]; simp [b1, b2, b3]

/-- The masses and payoff masses within `O₁₀` under any tremble. Source: none: infrastructure.
Kind: L -/
theorem tys_tremble_nu_ten (C : Proc Five10 (fun _ => Five10) ℚ) (ε : ℚ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) :
    nu (tremble C ε h0 h1) toldYouSo (tysActEv .ten .ten ∩ tysObs .ten) =
      (tremble C ε h0 h1 .five).w .ten * (tremble C ε h0 h1 .ten).w .ten ∧
    nu (tremble C ε h0 h1) toldYouSo (tysActEv .ten .five ∩ tysObs .ten) =
      (tremble C ε h0 h1 .five).w .ten * (tremble C ε h0 h1 .ten).w .five ∧
    paySum (tremble C ε h0 h1) toldYouSo (tysActEv .ten .ten ∩ tysObs .ten) =
      (tremble C ε h0 h1 .five).w .ten * (tremble C ε h0 h1 .ten).w .ten * 10 ∧
    paySum (tremble C ε h0 h1) toldYouSo (tysActEv .ten .five ∩ tysObs .ten) =
      (tremble C ε h0 h1 .five).w .ten * (tremble C ε h0 h1 .ten).w .five * 5 := by
  obtain ⟨-, -, ⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩⟩ := tys_actEv_obs_mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tys_nu]; simp [c1, c2, c3]
  · rw [tys_nu]; simp [d1, d2, d3]
  · rw [tys_paySum]; simp [c1, c2, c3]
  · rw [tys_paySum]; simp [d1, d2, d3]

/-- Every tremble weight of a procedure on `B_P` is positive for `ε > 0`.
Source: none: infrastructure. Kind: L -/
theorem tys_tremble_w_pos (C : Proc Five10 (fun _ => Five10) ℚ) (ε : ℚ) (h0 : 0 < ε)
    (h1 : ε ≤ 1) (d a : Five10) : 0 < (tremble C ε h0.le h1 d).w a :=
  tremble_fullSupport C ε h0 h1 d a

/-- **The `O₁₀`-conditional act values under any tremble are `10` (ten) and `5` (five)**.
Source: none: infrastructure (the fallback node pays its act)
Kind: L -/
theorem tys_tremble_condExp_ten (C : Proc Five10 (fun _ => Five10) ℚ) (ε : ℚ) (h0 : 0 < ε)
    (h1 : ε ≤ 1) :
    condExp (tremble C ε h0.le h1) toldYouSo (tysActEv .ten .ten ∩ tysObs .ten) = 10 ∧
    condExp (tremble C ε h0.le h1) toldYouSo (tysActEv .ten .five ∩ tysObs .ten) = 5 := by
  obtain ⟨n1, n2, p1, p2⟩ := tys_tremble_nu_ten C ε h0.le h1
  have w1 := tys_tremble_w_pos C ε h0 h1 .five .ten
  have w2 := tys_tremble_w_pos C ε h0 h1 .ten .ten
  have w3 := tys_tremble_w_pos C ε h0 h1 .ten .five
  unfold condExp
  rw [n1, n2, p1, p2]
  constructor <;> field_simp

/-- **D2At holds for `C₀` at every `ε ∈ (0, 1]`**: at `d₅`, the only realized act event within
`O₅` is `five`, which `C₀` plays; at `d₁₀`, `ten` (value `10`) beats `five` (value `5`).
Source: `dynamic.md` DY-5 ("Remark 3.12 read literally … approves `C₀`")
Kind: P
Fidelity: exact (Definition 18's escape clause included, as `D2At` carries it) -/
theorem procFiveTen_d2At (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    D2At tysObs tysActEv toldYouSo procFiveTen ε h0 h1 := by
  intro d _ _ _ a ha
  simp only [procFiveTen, Proc.ofFun_w] at ha
  have ha' : a = d := by by_contra h; simp [h] at ha
  subst ha'
  obtain ⟨n55, n5t⟩ := tys_tremble_nu_five procFiveTen ε h0.le h1
  obtain ⟨ntt, nt5, -, -⟩ := tys_tremble_nu_ten procFiveTen ε h0.le h1
  obtain ⟨ctt, ct5⟩ := tys_tremble_condExp_ten procFiveTen ε h0 h1
  cases a
  · refine ⟨by rw [n55]; exact tys_tremble_w_pos _ _ h0 h1 _ _, fun b hb => ?_⟩
    cases b
    · exact le_rfl
    · rw [n5t] at hb; exact absurd hb (lt_irrefl 0)
  · have hpos : 0 < nu (tremble procFiveTen ε h0.le h1) toldYouSo
        (tysActEv .ten .ten ∩ tysObs .ten) := by
      rw [ntt]; exact mul_pos (tys_tremble_w_pos _ _ h0 h1 _ _) (tys_tremble_w_pos _ _ h0 h1 _ _)
    refine ⟨hpos, fun b _ => ?_⟩
    cases b
    · rw [ct5, ctt]; norm_num
    · exact le_rfl

/-- **D2At fails for `C*` at every `ε ∈ (0, 1]`**: at `d₅` the escape clause does not fire
(`five ∧ O₅` is realized, mass `ε/2`), but `C*` plays `ten`, whose act event within `O₅` has
mass `0` — `A⁺_{d₅}(ε) = {five} ⊉ supp C*(d₅) = {ten}`.
Source: `dynamic.md` DY-5 ("rejects `C*` … at every `ε`")
Kind: P
Fidelity: exact -/
theorem procTake10_not_d2At (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ¬ D2At tysObs tysActEv toldYouSo procTake10 ε h0 h1 := by
  intro h
  obtain ⟨n55, n5t⟩ := tys_tremble_nu_five procTake10 ε h0.le h1
  have hex : ∃ b, 0 < nu (tremble procTake10 ε h0.le h1) toldYouSo
      (tysActEv .five b ∩ tysObs .five) :=
    ⟨.five, by rw [n55]; exact tys_tremble_w_pos _ _ h0 h1 _ _⟩
  have := (h .five (tys_queried .five) (tys_nuPoly_obs_five_ne_zero _) hex .ten
    (by simp [procTake10])).1
  rw [n5t] at this
  exact lt_irrefl 0 this

/-- D2 (`EventTrembleEdtConsistent`) is "`D2At` for all small `ε`", definitionally.
Source: `calibration.md` Devices (D2); `dynamic.md` DY-3
Kind: L -/
theorem eventTremble_iff_d2At {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    [∀ d, Nonempty (acts d)] (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) :
    EventTrembleEdtConsistent obs actEv C B ↔
      ∃ ε₀ > (0 : ℚ), ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ → D2At obs actEv B C ε h0 h1 :=
  Iff.rfl

/-- **T5(c), the inversion**: the typed Remark-3.12 device approves `C₀` and rejects `C*`.
v2 §7.1 remark (2) ("a procedure evaluating actions by tremble-limit conditional value takes
ten at both points") and remark (4) presuppose an evaluator conditioning on the *draw* (D3),
not on the world-event `a ∧ O_d` (D2), which cannot value `m=10` at `d₅` at any `ε`.
Source: [[decision-problems-v2]] §7.1 remarks (2), (4) (line 229) — contradicted for the typed
device; `dynamic.md` DY-5; dp-cf-121; findings F1
Kind: P
Fidelity: exact (D2 with Definition 18's escape clause) -/
theorem tys_d2_inverts :
    EventTrembleEdtConsistent tysObs tysActEv procFiveTen toldYouSo ∧
    ¬ EventTrembleEdtConsistent tysObs tysActEv procTake10 toldYouSo := by
  rw [eventTremble_iff_d2At, eventTremble_iff_d2At]
  constructor
  · exact ⟨1, one_pos, fun ε h0 h1 _ => procFiveTen_d2At ε h0 h1⟩
  · rintro ⟨ε₀, hε₀, h⟩
    have hlt : min ε₀ 1 / 2 < ε₀ := by
      have := min_le_left ε₀ 1; linarith [lt_min hε₀ one_pos]
    have hpos : 0 < min ε₀ 1 / 2 := by linarith [lt_min hε₀ one_pos]
    have hle : min ε₀ 1 / 2 ≤ 1 := by linarith [min_le_right ε₀ 1]
    exact procTake10_not_d2At _ hpos hle (h _ hpos hle hlt)

end Cleanroom.Decision.DpDevicesCatalog
