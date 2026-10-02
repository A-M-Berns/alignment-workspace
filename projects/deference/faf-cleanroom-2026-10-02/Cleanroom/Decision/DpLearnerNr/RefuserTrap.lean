import Cleanroom.Decision.DpCalibLimits.AppendixB
import Cleanroom.Decision.DpLearnerNr.Refuser

/-!
# `dp-learner-nr` target 11(e): DY-15, the refuser trap named statically

For `C := δ_refuse` on both muggings (`h₁ = mug1`, `h₀ = mugInert`), the refuser's state — the
Proposition-6 calibrated state at the tails observation under a full-support self-model
`m(pay) = q₀` — satisfies `dp-calibration`'s `MaskedOCAt` for every interior self-model
(`refuser_maskedOC`, DY-15's clause 1), is the `O_T`-conditional state of every two-point mixture
of `h₁` and `h₀` and the same state on both (`refuser_mixture_calibrated`, DY-15's clause 2,
Appendix B item 4), and is `dp-calib-limits`' `MaskedEdtConsistent` (`refuser_maskedEdt`, the
masked family's CA-1′ — the extra the mandate's 11(e) named, not clause 2); the state's values are
the *same* under both hypotheses (`V(pay) = −x`, `V(refuse) = 0`) and correct as
tails-conditionals under either (`refuser_pay_given_tails`); what differs across hypotheses is
the *unconditional* deviation statistic `value (C.deviatePure d pay)`, `(y − x)/2` under `h₁` and
`−x/2` under `h₀` — the statistic that would separate the hypotheses is the one Remark 3.11
declines to impose (`refuser_trap_static`). The masked-calibration clauses hold for every
procedure, not only the refuser (`refuser_maskedOC_any_proc`), as DY-15 says. Statics can name
the trap; only dynamics prices the escape (`RefuserChain.lean`).
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Cleanroom.Decision.DpCalibLimits Finset

variable (x y : ℚ)

/-- `ν(O_T) = ½` on the inert mugging for every procedure. Source: none: infrastructure. Kind: L -/
theorem mugInert_nu_obs (C : Proc Unit (fun _ => Act2) ℚ) : nu C (mugInert x y) (mugObs ()) = 1 / 2 := by
  rw [mugInert_nu]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  simp [mugObs]; linarith

/-- The queried points of the inert mugging. Source: none: infrastructure. Kind: L -/
theorem mugInert_queried : queried (mugInert x y) = {()} := by
  unfold mugInert
  ext u; cases u
  simp [queried_chance, queried_decision, queried_leaf]

/-- `paySum` of `{tPay}` on the two muggings: `½·C(d)(pay)·(−x)`. Source: none: infrastructure. Kind: L -/
theorem mug_paySum_tPay (C : Proc Unit (fun _ => Act2) ℚ) :
    paySum C (mug1 x y) {MugW.tPay} = 1 / 2 * (C ()).w .a * (-x) ∧
    paySum C (mugInert x y) {MugW.tPay} = 1 / 2 * (C ()).w .a * (-x) := by
  constructor
  · rw [paySum_eq_sum_ite, mug1_sum]
    simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPay, FinDistr.fair, FinDistr.coin]
    first | done | ring
  · rw [paySum_eq_sum_ite, mugInert_sum]
    simp [Fin.sum_univ_two, Act2.sum_univ, mugInert, mugWorldInert, mugPay, FinDistr.fair,
      FinDistr.coin]
    first | done | ring

/-- `paySum` of `{tRefuse}` on the two muggings: `0`. Source: none: infrastructure. Kind: L -/
theorem mug_paySum_tRefuse (C : Proc Unit (fun _ => Act2) ℚ) :
    paySum C (mug1 x y) {MugW.tRefuse} = 0 ∧ paySum C (mugInert x y) {MugW.tRefuse} = 0 := by
  constructor
  · rw [paySum_eq_sum_ite, mug1_sum]
    simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPay, FinDistr.fair, FinDistr.coin]
  · rw [paySum_eq_sum_ite, mugInert_sum]
    simp [Fin.sum_univ_two, Act2.sum_univ, mugInert, mugWorldInert, mugPay, FinDistr.fair,
      FinDistr.coin]

/-- **The Proposition-6 state on the inert mugging** with self-model `m(pay) = q₀`.
Source: [[decision-problems-v2]] §6 Proposition 6 (the state `ν_{C[d↦m]}(· | O_T)`), on `h₀`;
[[dp-learner-nr-mandate]] target 11(e)
Kind: D -/
noncomputable def mugInertState (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) : State MugW ℚ :=
  calibratedState (procQ q₀ h0 h1) (mugInert x y) (mugObs ())
    (by rw [mugInert_nu_obs]; norm_num)

/-- The inert mugging is masked-calibrated for every procedure with the Proposition-6 state
(the companion of `dp-calibration`'s `mug_maskedOC_all`).
Source: [[decision-problems-v2]] §6 Proposition 6; [[dp-learner-nr-mandate]] target 11(e)
Kind: P
Hyps: (a) `0 < q₀ < 1` -/
theorem mugInert_maskedOC_all (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    MaskedOC (fun _ => mugInertState x y q₀ h0.le h1.le) mugObs C (mugInert x y) := by
  have hm : ∀ a, 0 < (FinDistr.act2 q₀ h0.le h1.le).w a := by
    intro a; cases a <;> simp <;> linarith
  have hdev : C.deviate () (FinDistr.act2 q₀ h0.le h1.le) = procQ q₀ h0.le h1.le :=
    deviate_unit C _
  intro d _
  cases d
  exact Or.inl ⟨procQ q₀ h0.le h1.le, ⟨_, hm, hdev.symm⟩, by rw [mugInert_nu_obs]; norm_num,
    strictClausesAt_calibratedState mugObs _ (mugInert x y) _ () _ rfl⟩

/-- The refuser's state's values and beliefs, the same on both muggings: `V(pay) = −x`,
`V(refuse) = 0`, `P(refuse) = 1 − q₀`.
Source: DY-15 ("calibrated … on its own data"); [[dp-learner-nr-mandate]] target 11(e)
Kind: L
Hyps: (a) `0 < q₀ < 1` -/
theorem refuser_state_values (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) :
    (mugState1 x y q₀ h0.le h1.le).V {MugW.tPay} = -x ∧
    (mugState1 x y q₀ h0.le h1.le).V {MugW.tRefuse} = 0 ∧
    (mugState1 x y q₀ h0.le h1.le).pr {MugW.tRefuse} = 1 - q₀ ∧
    (mugInertState x y q₀ h0.le h1.le).V {MugW.tPay} = -x ∧
    (mugInertState x y q₀ h0.le h1.le).V {MugW.tRefuse} = 0 ∧
    (mugInertState x y q₀ h0.le h1.le).pr {MugW.tRefuse} = 1 - q₀ := by
  have hP : ({MugW.tPay} : Finset MugW) ∩ mugObs () = {MugW.tPay} := by decide
  have hR : ({MugW.tRefuse} : Finset MugW) ∩ mugObs () = {MugW.tRefuse} := by decide
  obtain ⟨hp1, hp0⟩ := mug_paySum_tPay x y (procQ q₀ h0.le h1.le)
  obtain ⟨hr1, hr0⟩ := mug_paySum_tRefuse x y (procQ q₀ h0.le h1.le)
  have hq' : q₀ ≠ 0 := h0.ne'
  have hq1' : 1 - q₀ ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mugState1, calibratedState_V, hP, hp1, mug1_nu]
    simp [procQ]; field_simp
  · simp only [mugState1, calibratedState_V, hR, hr1]; simp
  · unfold mugState1
    rw [calibratedState_pr, hR, mug1_nu_obs, mug1_nu]
    simp [procQ]
    first | done | (field_simp; ring) | field_simp | ring
  · simp only [mugInertState, calibratedState_V, hP, hp0, mugInert_nu]
    simp [procQ]; field_simp
  · simp only [mugInertState, calibratedState_V, hR, hr0]; simp
  · unfold mugInertState
    rw [calibratedState_pr, hR, mugInert_nu_obs, mugInert_nu]
    simp [procQ]
    first | done | (field_simp; ring) | field_simp | ring

/-! ## DY-15's second clause: mixture calibration on its own data (Appendix B item 4)

Appendix B item 4 of [[decision-problems-v2]] reads: "*Mixture calibration*: `P_{s_d} = ν̄(· | O_d)`
with `ν̄ = ∫ ν_{B,C} dπ(B)` for a measure `π` on an abstract problem's instantiations". No
mixture-calibration predicate exists in `dp-calibration` or `dp-calib-limits`, so the clause is
rendered here directly: the two-point mixture `π = (λ, 1−λ)` of the instantiations `h₁ = mug1`,
`h₀ = mugInert` is itself a tree (`mugMix`, a chance node drawing the hypothesis), its objective
statistics are the mixture `λ ν_{h₁,C} + (1−λ) ν_{h₀,C}` (`mugMix_nu`, `mugMix_paySum`), and the
refuser's state is the `O_T`-conditional of *every* such mixture (`refuser_mixture_calibrated`) —
because inside `O_T` the two instantiations have the same statistics (`mug_nu_obs_eq`,
`mug_paySum_obs_eq`), which is what "on its own data" means. The `MaskedEdtConsistent` rows below
are a *different* predicate (the Appendix-B masked family's CA-1′), the one the mandate's target
11(e) text named for this clause; they are kept as the extra fact they are, not as clause 2
(audit r2 fidelity B1; mandate/standards conflict recorded in the report).
-/

/-- The leaf-world of the two-point mixture of the muggings: hypothesis index `j` (`0` = `h₁`
coupled, `1` = `h₀` inert), then the mugging's own coin `i` and act.
Source: [[decision-problems-v2]] Appendix B item 4 (the instantiations `π` ranges over); DY-15
Kind: D -/
def mugMixWorld (j i : Fin 2) (act : Act2) : MugW :=
  if j = 0 then mugWorld1 i act else mugWorldInert i act

/-- **The two-point mixture `π = (λ, 1−λ)` of `h₁` and `h₀` as a tree**: a chance node drawing the
hypothesis with weight `λ` on `h₁ = mug1`, then the mugging's fair coin, the query and the leaf.
Its objective statistics are `λ ν_{h₁,C} + (1−λ) ν_{h₀,C}` on every event (`mugMix_nu`), i.e.
Appendix B item 4's `ν̄ = ∫ ν_{B,C} dπ(B)` for `π` supported on the two instantiations — the
mixtures the refuser's credence `π` over `{h₁, h₀}` (GR-15) ranges over.
Source: [[decision-problems-v2]] Appendix B item 4; DY-15 ("mixture-calibrated (Appendix B item 4)
on its own data"); [[dp-learner-nr-mandate]] target 11(e)
Kind: D
Fidelity: variant: `π` is a two-point measure on `{h₁, h₀}` (the abstract problem's two
instantiations in play), not a measure on all instantiations -/
def mugMix (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1) : Tree MugW Unit (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin lam l0 l1) fun j =>
    .chance 2 FinDistr.fair fun i =>
      .decision () fun act => .leaf (mugMixWorld j i act) (mugPay x y (mugMixWorld j i act))

/-- Sums over the leaves of `mugMix`. Source: none: infrastructure. Kind: L -/
theorem mugMix_sum (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1)
    (f : (mugMix x y lam l0 l1).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ j : Fin 2, ∑ i : Fin 2, ∑ act : Act2, f ⟨j, i, act, ()⟩ := by
  unfold mugMix at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- **`ν` on the mixture tree is the mixture of the `ν`'s**: `ν_{mugMix λ, C}(X) = λ ν_{h₁,C}(X) +
(1−λ) ν_{h₀,C}(X)` for every event and every procedure — `mugMix` is Appendix B item 4's `ν̄`.
Source: [[decision-problems-v2]] Appendix B item 4 (`ν̄ = ∫ ν_{B,C} dπ(B)`)
Kind: L -/
theorem mugMix_nu (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1) (C : Proc Unit (fun _ => Act2) ℚ)
    (X : Finset MugW) :
    nu C (mugMix x y lam l0 l1) X = lam * nu C (mug1 x y) X + (1 - lam) * nu C (mugInert x y) X := by
  rw [nu_eq_sum, mugMix_sum, mug1_nu, mugInert_nu]
  simp [Fin.sum_univ_two, Act2.sum_univ, mugMix, mugMixWorld, mugWorld1, mugWorldInert,
    FinDistr.fair, FinDistr.coin]
  split_ifs <;> ring

/-- `paySum` on the mixture tree is the mixture of the `paySum`s. Source: none: infrastructure. Kind: L -/
theorem mugMix_paySum (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1) (C : Proc Unit (fun _ => Act2) ℚ)
    (X : Finset MugW) :
    paySum C (mugMix x y lam l0 l1) X
      = lam * paySum C (mug1 x y) X + (1 - lam) * paySum C (mugInert x y) X := by
  simp only [paySum_eq_sum_ite]
  rw [mugMix_sum, mug1_sum, mugInert_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mugMix, mugMixWorld, mug1, mugWorld1, mugInert,
    mugWorldInert, mugPay, FinDistr.fair, FinDistr.coin]
  split_ifs <;> ring

/-- **Inside `O_T` the two instantiations have the same statistics**, for every procedure: the tails
branches of `mug1` and `mugInert` are identical, so `ν(X ∩ O_T)` agrees ("on its own data").
Source: DY-15 ("on its own data"); DY-13 (likelihood ratio 1)
Kind: L -/
theorem mug_nu_obs_eq (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    nu C (mug1 x y) (X ∩ mugObs ()) = nu C (mugInert x y) (X ∩ mugObs ()) := by
  rw [mug1_nu, mugInert_nu]
  simp [mugObs]

/-- Inside `O_T` the two instantiations have the same payoff sums, for every procedure.
Source: DY-15 ("on its own data")
Kind: L -/
theorem mug_paySum_obs_eq (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    paySum C (mug1 x y) (X ∩ mugObs ()) = paySum C (mugInert x y) (X ∩ mugObs ()) := by
  simp only [paySum_eq_sum_ite]
  rw [mug1_sum, mugInert_sum]
  simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugInert, mugWorldInert, mugPay,
    mugObs, FinDistr.fair, FinDistr.coin]

/-- Inside `O_T` every mixture has the statistics of `h₁`. Source: none: infrastructure. Kind: L -/
theorem mugMix_nu_obs_eq (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1)
    (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    nu C (mugMix x y lam l0 l1) (X ∩ mugObs ()) = nu C (mug1 x y) (X ∩ mugObs ()) := by
  rw [mugMix_nu, ← mug_nu_obs_eq]; ring

/-- Inside `O_T` every mixture has the payoff sums of `h₁`. Source: none: infrastructure. Kind: L -/
theorem mugMix_paySum_obs_eq (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1)
    (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset MugW) :
    paySum C (mugMix x y lam l0 l1) (X ∩ mugObs ()) = paySum C (mug1 x y) (X ∩ mugObs ()) := by
  rw [mugMix_paySum, ← mug_paySum_obs_eq]; ring

/-- `ν(O_T) = ½` on every mixture for every procedure. Source: none: infrastructure. Kind: L -/
theorem mugMix_nu_obs (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1) (C : Proc Unit (fun _ => Act2) ℚ) :
    nu C (mugMix x y lam l0 l1) (mugObs ()) = 1 / 2 := by
  rw [mugMix_nu, mug1_nu_obs, mugInert_nu_obs]; ring

/-- Two states with the same `P` and `V` are equal (the averaging axiom is a proposition).
Source: none: infrastructure
Kind: L -/
theorem state_ext {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s t : State Ω ℚ} (hP : s.P = t.P)
    (hV : s.V = t.V) : s = t := by
  cases s; cases t; cases hP; cases hV; rfl

/-- **The calibrated state at `O` depends only on the statistics inside `O`**: two trees with the
same `ν(· ∩ O)` and `paySum(· ∩ O)` under `C` have the same Definition-8 state at `O`.
Source: [[decision-problems-v2]] §3.1 Definition 8 (the state is `ν(· | O)` and the
`O`-conditional expectations); none: infrastructure
Kind: L -/
theorem calibratedState_congr (C : Proc Unit (fun _ => Act2) ℚ)
    (B B' : Tree MugW Unit (fun _ => Act2) ℚ) (O : Finset MugW)
    (hB : 0 < nu C B O) (hB' : 0 < nu C B' O)
    (hnu : ∀ X, nu C B (X ∩ O) = nu C B' (X ∩ O))
    (hpay : ∀ X, paySum C B (X ∩ O) = paySum C B' (X ∩ O)) :
    calibratedState C B O hB = calibratedState C B' O hB' := by
  have hO : nu C B O = nu C B' O := by simpa using hnu O
  apply state_ext
  · ext ω
    simp only [calibratedState, nuCondDistr]
    split_ifs with hω
    · have h1 : ({ω} : Finset MugW) = {ω} ∩ O :=
        (Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hω)).symm
      rw [h1, hnu, hO]
    · rfl
  · funext X
    simp only [calibratedState]
    rw [hnu, hpay]

/-- **The Proposition-6 state on the two-point mixture** `λ h₁ + (1−λ) h₀` with self-model
`m(pay) = q₀`: the calibrated state `ν̄_{C[d↦m]}(· | O_T)` of Appendix B item 4.
Source: [[decision-problems-v2]] Appendix B item 4 (`P_{s_d} = ν̄(· | O_d)`); §6 Proposition 6
Kind: D -/
noncomputable def mugMixState (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1) (q₀ : ℚ) (h0 : 0 ≤ q₀)
    (h1 : q₀ ≤ 1) : State MugW ℚ :=
  calibratedState (procQ q₀ h0 h1) (mugMix x y lam l0 l1) (mugObs ())
    (by rw [mugMix_nu_obs]; norm_num)

/-- **Mixture calibration on its own data** (DY-15's second clause, Appendix B item 4 for `π` on
the two instantiations): for every interior self-model `q₀` and every two-point mixture
`π = (λ, 1−λ)` of `h₁`, `h₀`, the refuser's Proposition-6 state on `h₁` *is* the `O_T`-conditional
state of the mixture — and it is the state on `h₀` as well. The reason is `mug_nu_obs_eq`: inside
`O_T` the two instantiations are the same tree, so the state is calibrated against every mixture
because it is calibrated against each component; it says nothing about the heads transfer, which is
exactly what the two hypotheses disagree on (`refuser_trap_static`).
Source: DY-15 ("mixture-calibrated (Appendix B item 4) on its own data"); [[decision-problems-v2]]
Appendix B item 4; [[dp-learner-nr-mandate]] target 11(e); [[dp-learner-nr-audit-r2-fidelity]] B1
Kind: P
Fidelity: exact for two-point `π` on `{h₁, h₀}` (Appendix B item 4 quantifies over a measure on
all instantiations of the abstract problem; here the problem has the two in play)
Hyps: (a) `0 ≤ q₀ ≤ 1`, `0 ≤ λ ≤ 1` -/
theorem refuser_mixture_calibrated (q₀ : ℚ) (h0 : 0 ≤ q₀) (h1 : q₀ ≤ 1) (lam : ℚ) (l0 : 0 ≤ lam)
    (l1 : lam ≤ 1) :
    mugMixState x y lam l0 l1 q₀ h0 h1 = mugState1 x y q₀ h0 h1 ∧
    mugState1 x y q₀ h0 h1 = mugInertState x y q₀ h0 h1 :=
  ⟨calibratedState_congr _ _ _ _ _ _ (mugMix_nu_obs_eq x y lam l0 l1 _)
      (mugMix_paySum_obs_eq x y lam l0 l1 _),
    calibratedState_congr _ _ _ _ _ _ (mug_nu_obs_eq x y _) (mug_paySum_obs_eq x y _)⟩

/-- **The refuser's state is masked-calibrated on both muggings**, for every interior self-model
`q₀`. By construction: the state is the calibrated state under the admissible self-model
`procQ q₀`, so this is `mug_maskedOC_all`/`mugInert_maskedOC_all` at `C := procQ 0` — it holds
for every procedure, not only the refuser (`refuser_maskedOC_any_proc`), which is DY-15's own
wording.
Source: DY-15 ("Under both instantiations a refuser's state is masked-OC-calibrated (Def 9) for
every procedure"); [[dp-cf-2-inventory]] 025; [[dp-learner-nr-mandate]] target 11(e)
Kind: L (an instance of `mug_maskedOC_all`/`mugInert_maskedOC_all`; relabelled from P at audit
r1 — the new content of the row is `mugInert_maskedOC_all`, `refuser_tEdt` and the values)
Fidelity: exact
Hyps: (a) `0 < q₀ < 1` -/
theorem refuser_maskedOC (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) :
    MaskedOCAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs (procQ 0 le_rfl zero_le_one) (mug1 x y) () ∧
    MaskedOCAt (fun _ => mugInertState x y q₀ h0.le h1.le) mugObs (procQ 0 le_rfl zero_le_one)
      (mugInert x y) () :=
  ⟨(mug_maskedOC_all x y q₀ h0 h1 _).1 () (by rw [mug1_queried]; simp),
    mugInert_maskedOC_all x y q₀ h0 h1 _ () (by rw [mugInert_queried]; simp)⟩

/-- **Masked calibration has no refuser-specific content**: the same Proposition-6 states are
`MaskedOCAt` for *every* procedure on both muggings (`MaskedOCAtV .LF .vacuity` asks for *some*
admissible full-support self-model with the strict clauses, and the state is built from that
self-model). Adopted from audit r1's `MaskedOCAnyProc` probe.
Source: DY-15 ("for every procedure"); [[dp-learner-nr-audit-r1-adversarial]] §3 item 5
Kind: L
Hyps: (a) `0 < q₀ < 1` -/
theorem refuser_maskedOC_any_proc (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    MaskedOCAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs C (mug1 x y) () ∧
    MaskedOCAt (fun _ => mugInertState x y q₀ h0.le h1.le) mugObs C (mugInert x y) () :=
  ⟨(mug_maskedOC_all x y q₀ h0 h1 C).1 () (by rw [mug1_queried]; simp),
    mugInert_maskedOC_all x y q₀ h0 h1 C () (by rw [mugInert_queried]; simp)⟩

/-- **`T_EDT` approves the refuser under the Proposition-6 state** on both muggings (`0 ≤ x`):
refusing (`V = 0`) weakly beats paying (`V = −x`) in `A_d^+`. This is the approval half of
`dp-calib-limits`' `MaskedEdtConsistent` (the Appendix-B masked family's CA-1′), the predicate the
mandate's target 11(e) named; it is *not* DY-15's "mixture-calibrated (Appendix B item 4)" clause,
which is `refuser_mixture_calibrated` (the citation moved at repair r2, audit r2 fidelity B1).
Source: [[dp-learner-nr-mandate]] target 11(e) (`MaskedEdtConsistent`); `calibration.md` CA-1′
Kind: L
Hyps: (a) `0 < q₀ < 1`, `0 ≤ x` -/
theorem refuser_tEdt (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) (hx : 0 ≤ x) :
    TEdt (fun _ => mugState1 x y q₀ h0.le h1.le) mugActEv (procQ 0 le_rfl zero_le_one) (mug1 x y) ∧
    TEdt (fun _ => mugInertState x y q₀ h0.le h1.le) mugActEv (procQ 0 le_rfl zero_le_one)
      (mugInert x y) := by
  obtain ⟨hVa, hVb, hpb, hVa', hVb', hpb'⟩ := refuser_state_values x y q₀ h0 h1
  constructor
  · intro d _ _ a ha
    cases d
    cases a
    · simp [procQ] at ha
    · rw [mem_argmaxPlus]
      refine ⟨?_, ?_⟩
      · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, mugActEv]
        rw [hpb]; linarith
      · intro b _
        cases b
        · simp only [mugActEv]; rw [hVa, hVb]; linarith
        · exact le_rfl
  · intro d _ _ a ha
    cases d
    cases a
    · simp [procQ] at ha
    · rw [mem_argmaxPlus]
      refine ⟨?_, ?_⟩
      · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, mugActEv]
        rw [hpb']; linarith
      · intro b _
        cases b
        · simp only [mugActEv]; rw [hVa', hVb']; linarith
        · exact le_rfl

/-- **The refuser is masked-EDT-consistent on both muggings** (`dp-calib-limits`'
`MaskedEdtConsistent`, variant `LF`, vacuity reading): some masked-calibrated state assignment
(the Proposition-6 state at `q₀ = ½`) under which `T_EDT` approves `δ_refuse`.
Source: [[dp-learner-nr-mandate]] target 11(e) (which names this predicate); [[dp-cf-2-inventory]]
025; `calibration.md` CA-1′ (the Appendix-B masked family)
Kind: C
Fidelity: variant: `MaskedEdtConsistent` is the Appendix-B masked *family*'s CA-1′, not DY-15's
"mixture-calibrated (Appendix B item 4)" — no mixture-calibration predicate exists in
`dp-calibration`/`dp-calib-limits`; that clause is rendered literally by
`refuser_mixture_calibrated`, and this row is the extra fact the mandate's 11(e) text asked for
(audit r2 fidelity B1; mandate/standards conflict recorded in the report)
Hyps: (a) `0 ≤ x` -/
theorem refuser_maskedEdt (hx : 0 ≤ x) :
    MaskedEdtConsistent .LF .vacuity mugObs mugActEv (procQ 0 le_rfl zero_le_one) (mug1 x y) ∧
    MaskedEdtConsistent .LF .vacuity mugObs mugActEv (procQ 0 le_rfl zero_le_one) (mugInert x y) :=
  ⟨⟨fun _ => mugState1 x y (1/2) (by norm_num) (by norm_num),
      (mug_maskedOC_all x y (1/2) (by norm_num) (by norm_num) _).1,
      (refuser_tEdt x y (1/2) (by norm_num) (by norm_num) hx).1⟩,
    ⟨fun _ => mugInertState x y (1/2) (by norm_num) (by norm_num),
      mugInert_maskedOC_all x y (1/2) (by norm_num) (by norm_num) _,
      (refuser_tEdt x y (1/2) (by norm_num) (by norm_num) hx).2⟩⟩

/-- **The refuser's `V(pay) = −x` is correct on what it predicts**: the tails-conditional value of
paying under `δ_pay` is `−x` on both muggings. So the state at `O_T` is not wrong about anything
it predicts — it has no prediction of the heads transfer at all (sealed by its observation),
and that is DY-15's point. Adopted from audit r1's `RefuserCond` probe.
Source: DY-15 ("calibrated on its own data"); [[dp-learner-nr-audit-r1-adversarial]] §3 item 6
Kind: L -/
theorem refuser_pay_given_tails :
    condExp (procQ 1 zero_le_one le_rfl) (mug1 x y) {MugW.tPay} = -x ∧
    condExp (procQ 1 zero_le_one le_rfl) (mugInert x y) {MugW.tPay} = -x := by
  obtain ⟨h1, h0⟩ := mug_paySum_tPay x y (procQ 1 zero_le_one le_rfl)
  constructor
  · unfold condExp
    rw [h1, mug1_nu]
    simp [procQ]
    ring
  · unfold condExp
    rw [h0, mugInert_nu]
    simp [procQ]
    ring

/-- **DY-15, the trap named statically** (load-bearing 5): on both muggings the refuser's state
is masked-calibrated (every interior self-model; Definition 9), mixture-calibrated on its own data
(it is the `O_T`-conditional state of every two-point mixture of `h₁`, `h₀`, and the same state on
both — `refuser_mixture_calibrated`, Appendix B item 4), and masked-EDT-consistent (the extra the
mandate's 11(e) named); its value of paying is the *same* `−x` under both hypotheses — and that
value is *correct* as the tails-conditional value of paying under either hypothesis
(`refuser_pay_given_tails`) — while the *unconditional* deviation statistic `value (δ_pay)` differs
across hypotheses: `(y − x)/2` on `h₁` versus `−x/2` on `h₀`. DY-15's "uncalibrated exactly in the
deviation statistic" is this cross-hypothesis comparison of Remark 3.11's object, the all-instance
deviation `ν_{B,C[d↦pay]}`: its `O_T`-conditional agrees with the state under both hypotheses, its
unconditional value separates them, and the state (which has no prediction of the heads transfer,
being sealed by its observation) cannot tell which it is in. A self-confirming equilibrium:
statics names it, dynamics prices the escape. The masked-OC conjuncts are instances
(`refuser_maskedOC`, L); the content is `refuser_mixture_calibrated`, the value computations and
`refuser_tEdt`.
Source: DY-15 ("a refuser's state is masked-OC-calibrated … and mixture-calibrated … on its own
data, and uncalibrated exactly in the deviation statistic Remark 3.11 declines to impose — a
self-confirming equilibrium"); [[dp-cf-2-inventory]] 025; [[dp-learner-nr-mandate]] target 11(e)
Kind: P (the mixture-calibration state equality, the value computations and the deviation
contrast; the masked-OC/EDT conjuncts are L)
Fidelity: exact (of the three clauses: masked-OC over Definition 9's `MaskedOCAt`;
mixture-calibrated on its own data as `refuser_mixture_calibrated`, for two-point `π` on the two
instantiations; "uncalibrated in the deviation statistic" read as the cross-hypothesis comparison
above). The `MaskedEdtConsistent` conjuncts are the Appendix-B masked family's CA-1′ — the
predicate the mandate's target 11(e) named for clause 2 — and are *not* that clause (relabelled at
repair r2, audit r2 fidelity B1)
Hyps: (a) `0 < q₀ < 1`, `0 ≤ x`, `0 < y` -/
theorem refuser_trap_static (q₀ : ℚ) (h0 : 0 < q₀) (h1 : q₀ < 1) (hx : 0 ≤ x) (hy : 0 < y) :
    MaskedOCAt (fun _ => mugState1 x y q₀ h0.le h1.le) mugObs (procQ 0 le_rfl zero_le_one) (mug1 x y) () ∧
    MaskedOCAt (fun _ => mugInertState x y q₀ h0.le h1.le) mugObs (procQ 0 le_rfl zero_le_one)
      (mugInert x y) () ∧
    (∀ (lam : ℚ) (l0 : 0 ≤ lam) (l1 : lam ≤ 1),
      mugMixState x y lam l0 l1 q₀ h0.le h1.le = mugState1 x y q₀ h0.le h1.le) ∧
    mugState1 x y q₀ h0.le h1.le = mugInertState x y q₀ h0.le h1.le ∧
    MaskedEdtConsistent .LF .vacuity mugObs mugActEv (procQ 0 le_rfl zero_le_one) (mug1 x y) ∧
    MaskedEdtConsistent .LF .vacuity mugObs mugActEv (procQ 0 le_rfl zero_le_one) (mugInert x y) ∧
    (mugState1 x y q₀ h0.le h1.le).V {MugW.tPay} = -x ∧
    (mugInertState x y q₀ h0.le h1.le).V {MugW.tPay} = -x ∧
    value (procQ 1 zero_le_one le_rfl) (mug1 x y) = (y - x) / 2 ∧
    value (procQ 1 zero_le_one le_rfl) (mugInert x y) = -x / 2 ∧
    value (procQ 1 zero_le_one le_rfl) (mug1 x y) ≠ value (procQ 1 zero_le_one le_rfl) (mugInert x y) := by
  obtain ⟨hm1, hm0⟩ := refuser_maskedOC x y q₀ h0 h1
  obtain ⟨he1, he0⟩ := refuser_maskedEdt x y hx
  obtain ⟨hVa, _, _, hVa', _, _⟩ := refuser_state_values x y q₀ h0 h1
  have hv1 : value (procQ 1 zero_le_one le_rfl) (mug1 x y) = (y - x) / 2 := by
    rw [mug1_value]; simp [procQ]
  have hv0 : value (procQ 1 zero_le_one le_rfl) (mugInert x y) = -x / 2 := by
    rw [mugInert_value]; simp [procQ]
  refine ⟨hm1, hm0, fun lam l0 l1 => (refuser_mixture_calibrated x y q₀ h0.le h1.le lam l0 l1).1,
    (refuser_mixture_calibrated x y q₀ h0.le h1.le 0 le_rfl zero_le_one).2, he1, he0, hVa, hVa',
    hv1, hv0, ?_⟩
  rw [hv1, hv0]; intro h; linarith

end Cleanroom.Decision.DpLearnerNr
