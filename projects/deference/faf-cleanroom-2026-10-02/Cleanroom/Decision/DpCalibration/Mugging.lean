import Cleanroom.Decision.DpCalibration.Witnesses

/-!
# Counterfactual Mugging: Proposition 6 and the mugging rows of the implication diagram

T12 and two rows of T10 of [[dp-calibration-mandate]].

* `mug1_value`, `mug2_value` — `V_{B₁}(C) = q(y−x)/2`, `V_{B₂}(C) = (y − q(x+y))/2` with
  `q := C(d)(pay)`, for every procedure (supporting lemmas `dp-devices-catalog` may import).
* `mug_maskedOC_all` — **Proposition 6's calibration clause**: for every procedure `C` and every
  interior `q₀`, both `B₁` and `B₂` are masked-calibrated for `C` with the Proposition-6 state
  (`P_s(T) = 1`, `P_s(transfer = 0) = 1`, `P_s(pay) = q₀`) via the self-model `m(pay) = q₀` — the
  state is exactly `ν_{C[d↦m]}(· | O_T)`, which does not depend on `C(d)` (one point).
* `no_uniform_optimum` — **Proposition 6's optimality clause**: for `0 < x < y` no procedure is
  `T_opt` on both trees.
* `mug1_perRun_not_strict` (per-run SSC ⇏ strict OC) and `mug1_masked_not_strict` (masked ⇏
  strict, Proposition 6's phenomenon) — T10's witness rows on `B₁`.
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-- On a `Unit`-point tree, a point-deviation replaces the whole procedure.
Source: none: infrastructure. Kind: L -/
theorem deviate_unit {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {acts : Unit → Type} [∀ d, Fintype (acts d)] (C : Proc Unit acts K)
    (m : FinDistr K (acts ())) : C.deviate () m = fun _ => m := by
  funext u; cases u; simp [Proc.deviate]

section mugging

variable (x y : ℚ)

/-- A sum over the leaves of `B₁` as a double sum. Source: none: infrastructure. Kind: L -/
theorem mug1_sum (f : (mug1 x y).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold mug1 at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- A sum over the leaves of `B₂` as a double sum. Source: none: infrastructure. Kind: L -/
theorem mug2_sum (f : (mug2 x y).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold mug2 at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- **`V_{B₁}(C) = q(y − x)/2`**, `q := C(d)(pay)`, for every procedure.
Source: [[decision-problems-v2]] §6 Proposition 6 (`V_{B₁}(C) = ½ q (y − x)`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem mug1_value (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (mug1 x y) = (C ()).w .a * (y - x) / 2 := by
  unfold value
  rw [mug1_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPay, FinDistr.fair, FinDistr.coin]
  ring

/-- **`V_{B₂}(C) = (y − q(x + y))/2`**, `q := C(d)(pay)`, for every procedure.
Source: [[decision-problems-v2]] §6 Proposition 6 (`V_{B₂}(C) = ½(y − q(x + y))`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem mug2_value (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (mug2 x y) = (y - (C ()).w .a * (x + y)) / 2 := by
  unfold value
  rw [mug2_sum]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  simp [Fin.sum_univ_two, Act2.sum_univ, mug2, mugWorld2, mugPay, FinDistr.fair, FinDistr.coin]
  linear_combination (y / 2) * this

/-- `ν` on `B₁` as an explicit expression. Source: none: infrastructure. Kind: L -/
theorem mug1_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    nu C (mug1 x y) X =
      (if MugW.tPay ∈ X then (1/2 : ℚ) * (C ()).w .a else 0) +
      (if MugW.tRefuse ∈ X then (1/2 : ℚ) * (C ()).w .b else 0) +
      (if MugW.hOne ∈ X then (1/2 : ℚ) * (C ()).w .a else 0) +
      (if MugW.hZero ∈ X then (1/2 : ℚ) * (C ()).w .b else 0) := by
  rw [nu_eq_sum, mug1_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, FinDistr.fair, FinDistr.coin]
  ring

/-- `ν` on `B₂` as an explicit expression. Source: none: infrastructure. Kind: L -/
theorem mug2_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    nu C (mug2 x y) X =
      (if MugW.tPay ∈ X then (1/2 : ℚ) * (C ()).w .a else 0) +
      (if MugW.tRefuse ∈ X then (1/2 : ℚ) * (C ()).w .b else 0) +
      (if MugW.hZero ∈ X then (1/2 : ℚ) * (C ()).w .a else 0) +
      (if MugW.hOne ∈ X then (1/2 : ℚ) * (C ()).w .b else 0) := by
  rw [nu_eq_sum, mug2_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mug2, mugWorld2, FinDistr.fair, FinDistr.coin]
  ring

/-- `ν(O_T) = ½` on `B₁` for every procedure. Source: none: infrastructure. Kind: L -/
theorem mug1_nu_obs (C : Proc Unit (fun _ => Act2) ℚ) : nu C (mug1 x y) (mugObs ()) = 1 / 2 := by
  rw [mug1_nu]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  simp [mugObs]; linarith

/-- `ν(O_T) = ½` on `B₂` for every procedure. Source: none: infrastructure. Kind: L -/
theorem mug2_nu_obs (C : Proc Unit (fun _ => Act2) ℚ) : nu C (mug2 x y) (mugObs ()) = 1 / 2 := by
  rw [mug2_nu]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  simp [mugObs]; linarith

/-- `occ(d)` on `B₁` is every run (the point is queried on both branches).
Source: [[decision-problems-v2]] Proposition 6 (the hypothetical `H`-branch query); mandate T10
Kind: L -/
theorem mug1_occ : occ () (mug1 x y) = Finset.univ := by
  ext ℓ
  unfold mug1 at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  simp

/-- The queried points of `B₁`. Source: none: infrastructure. Kind: L -/
theorem mug1_queried : queried (mug1 x y) = {()} := by
  unfold mug1
  ext u; cases u
  simp [queried_chance, queried_decision, queried_leaf]

/-- The queried points of `B₂`. Source: none: infrastructure. Kind: L -/
theorem mug2_queried : queried (mug2 x y) = {()} := by
  unfold mug2
  ext u; cases u
  simp [queried_chance, queried_decision, queried_leaf]

/-- **The Proposition-6 state on `B₁`** with self-model `m(pay) = q₀`: the calibrated state
`ν_{C[d↦m]}(· | O_T)` — which is `ν_{procQ q₀}(· | O_T)`, independent of `C` (one point).
Source: [[decision-problems-v2]] §6 Proposition 6 ("the state is exactly `ν_{B_i, C[d↦m]}(· ∣ O_T)`")
Kind: D -/
noncomputable def mugState1 (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) : State MugW ℚ :=
  calibratedState (procQ q₀ h0 h1) (mug1 x y) (mugObs ()) (by rw [mug1_nu_obs]; norm_num)

/-- The Proposition-6 state on `B₂`. Source: [[decision-problems-v2]] Proposition 6. Kind: D -/
noncomputable def mugState2 (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) : State MugW ℚ :=
  calibratedState (procQ q₀ h0 h1) (mug2 x y) (mugObs ()) (by rw [mug2_nu_obs]; norm_num)

/-- The Proposition-6 state's beliefs: `P_s(T) = 1`, `P_s(transfer = 0) = 1`, `P_s(pay) = q₀`
(on `B₁`; the same numbers on `B₂`).
Source: [[decision-problems-v2]] §6 Proposition 6 (`P_s(T) = 1`, `P_s(transfer = 0) = 1`,
`P_s(pay) = q₀`)
Kind: L -/
theorem mugState1_beliefs (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) :
    (mugState1 x y q₀ h0 h1).pr (mugObs ()) = 1 ∧
    (mugState1 x y q₀ h0 h1).pr {.tPay, .tRefuse, .hZero} = 1 ∧
    (mugState1 x y q₀ h0 h1).pr {.tPay} = q₀ := by
  simp only [mugState1, calibratedState_pr, mug1_nu, mugObs, procQ, FinDistr.act2_a,
    FinDistr.act2_b]
  simp
  refine ⟨?_, ?_⟩ <;> field_simp <;> norm_num

/-- The same beliefs on `B₂`. Source: [[decision-problems-v2]] Proposition 6. Kind: L -/
theorem mugState2_beliefs (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) :
    (mugState2 x y q₀ h0 h1).pr (mugObs ()) = 1 ∧
    (mugState2 x y q₀ h0 h1).pr {.tPay, .tRefuse, .hZero} = 1 ∧
    (mugState2 x y q₀ h0 h1).pr {.tPay} = q₀ := by
  simp only [mugState2, calibratedState_pr, mug2_nu, mugObs, procQ, FinDistr.act2_a,
    FinDistr.act2_b]
  simp
  refine ⟨?_, ?_⟩ <;> field_simp <;> norm_num

/-- **Proposition 6, the calibration clause**: for every procedure `C` and every interior `q₀`,
`B₁` and `B₂` are masked-calibrated for `C` with the Proposition-6 states, via the self-model
`m(pay) = q₀` — the state is `ν_{C[d↦m]}(· | O_T) = ν_{procQ q₀}(· | O_T)`, the same for every
`C`.
Source: [[decision-problems-v2]] §6 Proposition 6 ("Both are masked-calibrated for *every*
procedure")
Kind: P
Fidelity: exact (interior `q₀`; Appendix B's boundary case not covered)
Hyps: (a) `0 < q₀ < 1` -/
theorem mug_maskedOC_all (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) (C : Proc Unit (fun _ => Act2) ℚ) :
    MaskedOC (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs C (mug1 x y) ∧
    MaskedOC (fun _ => mugState2 x y q₀ h0.le h1.le) mugObs C (mug2 x y) := by
  have hm : ∀ a, 0 < (FinDistr.act2 q₀ h0.le h1.le).w a := by
    intro a; cases a <;> simp <;> linarith
  have hdev : C.deviate () (FinDistr.act2 q₀ h0.le h1.le) = procQ q₀ h0.le h1.le :=
    deviate_unit C _
  constructor
  · intro d _
    cases d
    exact Or.inl ⟨procQ q₀ h0.le h1.le, ⟨_, hm, hdev.symm⟩, by rw [mug1_nu_obs]; norm_num,
      strictClausesAt_calibratedState mugObs _ (mug1 x y) _ () _ rfl⟩
  · intro d _
    cases d
    exact Or.inl ⟨procQ q₀ h0.le h1.le, ⟨_, hm, hdev.symm⟩, by rw [mug2_nu_obs]; norm_num,
      strictClausesAt_calibratedState mugObs _ (mug2 x y) _ () _ rfl⟩

/-- **Proposition 6, the optimality clause (no uniform optimum)**: for `0 < x < y`, optimality on
`B₁` forces `q = 1` and on `B₂` forces `q = 0`; no procedure is `T_opt` on both.
Source: [[decision-problems-v2]] §6 Proposition 6 ("Optimality on `B₁` forces `q = 1`, on `B₂`
forces `q = 0`; no procedure is optimal on both")
Kind: C
Fidelity: exact
Hyps: (a) `0 < x < y` -/
theorem no_uniform_optimum (hx : 0 < x) (hxy : x < y) (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ (TOpt C (mug1 x y) ∧ TOpt C (mug2 x y)) := by
  rintro ⟨h1, h2⟩
  have e1 := h1 (procQ 1 (by norm_num) (by norm_num))
  have e2 := h2 (procQ 0 (by norm_num) (by norm_num))
  rw [mug1_value, mug1_value] at e1
  rw [mug2_value, mug2_value] at e2
  simp only [procQ, FinDistr.act2_a] at e1 e2
  have hq1 : (C ()).w .a ≤ 1 := (C ()).w_le_one .a
  have hq0 : 0 ≤ (C ()).w .a := (C ()).nonneg .a
  nlinarith

/-! ## T10's mugging rows -/

/-- **Per-run SSC ⇏ strict OC** (`B₁`): the prior-calibrated state `(ν, 𝔼[r | ·])` is per-run
SSC at `d` (`occ(d)` is every run) and not strictly calibrated at `d` (`P_s(O_T) = ½ ≠ 1`), for
every procedure.
Source: mandate T10 ("per-run SSC ⇏ strict OC (`mug1`: the state `μ` pushed down is per-run SSC at
`d`, not strict OC)")
Kind: N+
Fidelity: stronger (every procedure, not only interior `q`) -/
theorem mug1_perRun_not_strict (C : Proc Unit (fun _ => Act2) ℚ) :
    PerRunSSCAt (fun _ => calibratedState C (mug1 x y) Finset.univ (nu_univ_pos C _)) C
      (mug1 x y) () ∧
    ¬ StrictOCAt (fun _ => calibratedState C (mug1 x y) Finset.univ (nu_univ_pos C _)) mugObs C
      (mug1 x y) () := by
  constructor
  · intro _
    exact perRunClausesAt_of_priorCalibrated_of_occ_univ C (mug1 x y) _ (mug1_occ x y)
      (priorCalibrated_calibratedState_univ C (mug1 x y) _)
  · intro h
    have hpos : 0 < nu C (mug1 x y) (mugObs ()) := by rw [mug1_nu_obs]; norm_num
    have := (h hpos).1 (mugObs ())
    rw [Finset.inter_self, calibratedState_pr, Finset.inter_univ, nu_univ, div_one,
      mug1_nu_obs] at this
    norm_num at this

/-- **Masked ⇏ strict** (`B₁`, Proposition 6's phenomenon): with a self-model `q₀ ≠ q`, the
Proposition-6 state is masked-calibrated for `procQ q` and not strictly calibrated for it.
Source: mandate T10 ("masked ⇏ strict (`mug1` with self-model `q₀ ≠ q`, Proposition 6's
phenomenon)")
Kind: N+ -/
theorem mug1_masked_not_strict (q₀ q : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hne : q₀ ≠ q) :
    MaskedOCAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs (procQ q hq0 hq1) (mug1 x y) () ∧
    ¬ StrictOCAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs (procQ q hq0 hq1) (mug1 x y) () := by
  refine ⟨(mug_maskedOC_all x y q₀ h0 h1 (procQ q hq0 hq1)).1 () (by rw [mug1_queried]; simp), ?_⟩
  intro h
  have hpos : 0 < nu (procQ q hq0 hq1) (mug1 x y) (mugObs ()) := by rw [mug1_nu_obs]; norm_num
  have := (h hpos).1 {.tPay}
  rw [mug1_nu_obs, (mugState1_beliefs x y q₀ h0.le h1.le).2.2, mug1_nu] at this
  simp [mugObs, procQ] at this
  exact hne (by linarith)

end mugging

end Cleanroom.Decision.DpCalibration
