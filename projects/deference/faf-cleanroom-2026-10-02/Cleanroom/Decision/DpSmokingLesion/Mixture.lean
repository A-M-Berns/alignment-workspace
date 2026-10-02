import Cleanroom.Decision.DpSmokingLesion.Prop11

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# T7: Appendix B item 4 — mixture calibration

[[dp-smoking-lesion-mandate]] T7, source [[decision-problems-v2]] line 344: "Smoking Lesion's
inconsistency (Proposition 11) survives mixing, since `ν_B(m) = C(d)(m)` is constant across
instantiations and the screening-off argument passes through the integral."

* **(a) Survives mixing under (S4)** (`mixture_not_S2`): for a finite family `B_i` of one-point
  `O_d = ⊤` trees each recording for `C` with cancer post-query independent of the draw, and
  weights `π`, the mixture `ν̄ = ∑ π_i ν_{B_i,C}` has `ν̄(m) = C(d)(m)` (`mixture_nu_actEv`) and
  `ν̄(k ∧ m) = ν̄(k) · C(d)(m)` (`mixture_nu_inter_actEv`), so the mixture state `P = ν̄`
  violates (S2). The integral is a finite sum (`Fidelity: weaker: finite mixtures`).
* **(b) Fails with one non-recording component** (`mixture_S2_slOne_e2a`): the equal-weight
  mixture of `slOne` and `e2a` at `δ_refrain` has (S2) — Appendix B's sentence presupposes (S4)
  (S3's "presupposes (S4)").
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-! ## `ν(X ∧ m) = ν(m) · ν(X)` at a recorded `⊤` point -/

section factor

variable {ι : Type} [DecidableEq ι] (C : Proc ι (fun _ => Bool) ℚ) (B : Tree TickleW ι (fun _ => Bool) ℚ)
  (d : ι)

/-- At a recorded `O_d = ⊤` point with `X` post-query independent of the draw,
`ν(X ∧ m) = ν(m) · ν(X)` for both acts (post-query screening summed over the other act).
Source: [[decision-problems-v2]] §7.3 Lemma 3 (`k ⊥ m` under `ν`); mandate T7(a)
Kind: C
Fidelity: exact
Hyps: (a) recording for `C` at `⊤`; (a) `PostQueryIndep C B d X` -/
theorem nu_inter_actEv_eq_mul_of_recordsFor (hrec : RecordsFor slObs slActEv C B d) (X : Finset TickleW)
    (hX : PostQueryIndep C B d X) (m : Bool) :
    nu C B (X ∩ evM m) = nu C B (evM m) * nu C B X := by
  have h := postQuery_screening_recorded slActEv C B d slObs rfl hrec X hX m (!m)
  simp only [slActEv_apply] at h
  have hu' : evM m ∪ evM (!m) = Finset.univ := by
    ext w; simp only [Finset.mem_union, mem_evM, Finset.mem_univ, iff_true]
    cases m <;> cases w.2.1 <;> simp
  have hd' : Disjoint (evM m) (evM (!m)) := by
    rw [Finset.disjoint_left]; intro w h1 h2; simp at h1 h2; rw [h1] at h2; cases m <;> simp at h2
  have hsum : nu C B (evM m) + nu C B (evM (!m)) = 1 := by
    rw [← nu_union C B hd', hu', nu_univ]
  have hX' : nu C B (X ∩ evM m) + nu C B (X ∩ evM (!m)) = nu C B X := by
    have hu : X ∩ evM m ∪ X ∩ evM (!m) = X := by
      rw [← Finset.inter_union_distrib_left, hu', Finset.inter_univ]
    have hd : Disjoint (X ∩ evM m) (X ∩ evM (!m)) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hd')
    rw [← nu_union C B hd, hu]
  -- `ν(X ∧ m) · ν(¬m) = ν(X ∧ ¬m) · ν(m)`; add `ν(X ∧ m) · ν(m)` to both sides
  have := congrArg (fun z => z + nu C B (X ∩ evM m) * nu C B (evM m)) h
  simp only at this
  have e1 : nu C B (X ∩ evM m) * nu C B (evM (!m)) + nu C B (X ∩ evM m) * nu C B (evM m) =
      nu C B (X ∩ evM m) := by rw [← mul_add, add_comm, hsum, mul_one]
  have e2 : nu C B (X ∩ evM (!m)) * nu C B (evM m) + nu C B (X ∩ evM m) * nu C B (evM m) =
      nu C B (evM m) * nu C B X := by rw [← hX']; ring
  linarith

end factor

/-! ## (a) The finite mixture -/

section mixture

variable {n : ℕ} (π : FinDistr ℚ (Fin n)) (Bs : Fin n → Tree TickleW Unit (fun _ => Bool) ℚ)
  (C : Proc Unit (fun _ => Bool) ℚ)

/-- The mixture statistic `ν̄(X) := ∑_i π_i ν_{B_i,C}(X)`.
Source: [[decision-problems-v2]] Appendix B item 4 (`ν̄ = ∫ ν_{B,C} dπ(B)`), finite form
Kind: D
Fidelity: weaker: finite mixtures -/
def mixNu (X : Finset TickleW) : ℚ := ∑ i, π.w i * nu C (Bs i) X

/-- The mixture as a weight vector on worlds: a `FinDistr`.
Source: [[decision-problems-v2]] Appendix B item 4 ("`P_{s_d} = ν̄(· ∣ O_d)`", at `O_d = ⊤`)
Kind: D -/
def mixDistr : FinDistr ℚ TickleW where
  w ω := mixNu π Bs C {ω}
  nonneg ω := Finset.sum_nonneg fun i _ => mul_nonneg (π.nonneg i) (nu_nonneg C (Bs i) _)
  sum_one := by
    unfold mixNu
    rw [Finset.sum_comm]
    have : ∀ i, (∑ ω, π.w i * nu C (Bs i) {ω}) = π.w i := by
      intro i
      rw [← Finset.mul_sum, ← nu_eq_sum_singleton, nu_univ, mul_one]
    simp only [this]
    exact π.sum_one

/-- `probOf (mixDistr) X = ν̄(X)`. Source: none: infrastructure. Kind: L -/
theorem probOf_mixDistr (X : Finset TickleW) : probOf (mixDistr π Bs C) X = mixNu π Bs C X := by
  unfold probOf mixDistr mixNu
  simp only
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← nu_eq_sum_singleton]

/-- The mixture state at `⊤`: `P = ν̄`, desirability constant (not read by (S2)).
Source: [[decision-problems-v2]] Appendix B item 4
Kind: D -/
def mixState : State TickleW ℚ := State.ofConst (mixDistr π Bs C) 0

/-- **`ν̄(m) = C(d)(m)`**: the act statistic is constant across recording instantiations, so the
mixture inherits it.
Source: [[decision-problems-v2]] Appendix B item 4 ("`ν_B(m) = C(d)(m)` is constant across
instantiations")
Kind: C
Fidelity: exact
Hyps: (a) every component records for `C` at `⊤` -/
theorem mixture_nu_actEv (hrec : ∀ i, RecordsFor slObs slActEv C (Bs i) ()) (m : Bool) :
    mixNu π Bs C (evM m) = (C ()).w m := by
  unfold mixNu
  have : ∀ i, nu C (Bs i) (evM m) = (C ()).w m := by
    intro i
    have h := nu_actEv_inter_obs_of_recordsFor slObs slActEv C (Bs i) (hrec i) m
    simp only [slActEv_apply, slObs_apply, Finset.inter_univ, nu_univ, mul_one] at h
    exact h
  simp only [this, ← Finset.sum_mul, π.sum_one, one_mul]

/-- **`ν̄(k ∧ m) = ν̄(k) · C(d)(m)`**: the screening passes through the finite sum.
Source: [[decision-problems-v2]] Appendix B item 4 ("the screening-off argument passes through
the integral")
Kind: C
Fidelity: weaker: finite mixtures
Hyps: (a) every component records for `C` at `⊤` and has cancer post-query independent of the
draw -/
theorem mixture_nu_inter_actEv (hrec : ∀ i, RecordsFor slObs slActEv C (Bs i) ())
    (hK : ∀ i, PostQueryIndep C (Bs i) () evK) (m : Bool) :
    mixNu π Bs C (evK ∩ evM m) = mixNu π Bs C evK * (C ()).w m := by
  unfold mixNu
  have : ∀ i, nu C (Bs i) (evK ∩ evM m) = (C ()).w m * nu C (Bs i) evK := by
    intro i
    rw [nu_inter_actEv_eq_mul_of_recordsFor C (Bs i) () (hrec i) evK (hK i) m]
    congr 1
    have h := nu_actEv_inter_obs_of_recordsFor slObs slActEv C (Bs i) (hrec i) m
    simp only [slActEv_apply, slObs_apply, Finset.inter_univ, nu_univ, mul_one] at h
    exact h
  simp only [this]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Appendix B item 4 under (S4)**: the mixture state of a finite family of recording
instantiations violates (S2) — Smoking Lesion's inconsistency survives mixing.
Source: [[decision-problems-v2]] Appendix B item 4 line 344 ("Smoking Lesion's inconsistency
(Proposition 11) survives mixing"); dp-core-036; mandate T7(a)
Kind: P
Fidelity: weaker: finite mixtures; (S4) made explicit (every component records)
Hyps: (a) every component records for `C` at `⊤` with `PostQueryIndep evK` -/
theorem mixture_not_S2 (hrec : ∀ i, RecordsFor slObs slActEv C (Bs i) ())
    (hK : ∀ i, PostQueryIndep C (Bs i) () evK) : ¬ S2 (mixState π Bs C) := by
  rintro ⟨-, -, hlt⟩
  simp only [mixState, State.pr, State.ofConst_P, probOf_mixDistr] at hlt
  rw [mixture_nu_actEv π Bs C hrec, mixture_nu_actEv π Bs C hrec,
    mixture_nu_inter_actEv π Bs C hrec hK, mixture_nu_inter_actEv π Bs C hrec hK] at hlt
  have : mixNu π Bs C evK * (C ()).w false * (C ()).w true =
      mixNu π Bs C evK * (C ()).w true * (C ()).w false := by ring
  rw [this] at hlt
  exact lt_irrefl _ hlt

/-- **N+**: the family of `slOne` trees at any parameters (all recording, all lesion-only)
inhabits the hypothesis package; with two components at the FDT and quarter numbers and weights
`(½, ½)`, `C(d) = ½`, the mixture has `ν̄(m=1) = ½` and `ν̄(k ∧ m=1) = ¼`.
Source: mandate T7(a)
Kind: N+ -/
theorem mixture_instance :
    let Bs : Fin 2 → Tree TickleW Unit (fun _ => Bool) ℚ :=
      ![slOne Lesion.fdt 1000 1000000, slOne Lesion.quarters 1 3]
    let C₀ := procBool (1/2) (by norm_num) (by norm_num)
    (∀ i, RecordsFor slObs slActEv C₀ (Bs i) () ∧ PostQueryIndep C₀ (Bs i) () evK) ∧
    mixNu FinDistr.fair Bs C₀ (evM true) = 1/2 ∧ mixNu FinDistr.fair Bs C₀ (evK ∩ evM true) = 1/4 ∧
    ¬ S2 (mixState FinDistr.fair Bs C₀) := by
  intro Bs C₀
  have hrec : ∀ i, RecordsFor slObs slActEv C₀ (Bs i) () ∧ PostQueryIndep C₀ (Bs i) () evK := by
    intro i
    fin_cases i
    · exact ⟨slOne_recordsFor _ _ _ _, (slOne_lesionOnlyAt _ _ _ _).postQueryIndep⟩
    · exact ⟨slOne_recordsFor _ _ _ _, (slOne_lesionOnlyAt _ _ _ _).postQueryIndep⟩
  refine ⟨hrec, ?_, ?_, mixture_not_S2 _ _ _ (fun i => (hrec i).1) (fun i => (hrec i).2)⟩
  · unfold mixNu
    simp only [Fin.sum_univ_two, FinDistr.fair, FinDistr.coin]
    simp only [Bs, Matrix.cons_val_zero, Matrix.cons_val_one, slOne_nu_m]
    simp [C₀, procBool]; norm_num
  · unfold mixNu
    simp only [Fin.sum_univ_two, FinDistr.fair, FinDistr.coin]
    simp only [Bs, Matrix.cons_val_zero, Matrix.cons_val_one, slOne_nu_k_m]
    simp [C₀, procBool, Lesion.fdt, Lesion.quarters]; norm_num

end mixture

/-! ## (b) One non-recording component breaks it -/

/-- **Appendix B item 4 presupposes (S4)**: the equal-weight mixture of `slOne` (recording) and
`e2a` (coverage failure) at `δ_refrain` has (S2): `ν̄(m=1) = 9/40`, `ν̄(k ∧ m=1) = 2007/10000`,
`ν̄(m=0) = 31/40`, `ν̄(k ∧ m=0) = 2993/10000`, and `2007 · 31 > 2993 · 9`.
Source: `sl-defensible-claims.md` S3 ("Appendix B item 4's 'survives mixing' … presupposes
(S4)"); mandate T7(b)
Kind: N−
Fidelity: exact (the refuted sentence is "survives mixing" read over (S1)–(S3) instantiations) -/
theorem mixture_S2_slOne_e2a :
    let Bs : Fin 2 → Tree TickleW Unit (fun _ => Bool) ℚ := ![slOne Lesion.fdt 1000 1000000, e2a₀]
    S2 (mixState FinDistr.fair Bs procRefrain) := by
  intro Bs
  obtain ⟨h1, h2, h3, h4⟩ := e2a_nu_values procRefrain
  have hv : ∀ X, (mixState FinDistr.fair Bs procRefrain).pr X = mixNu FinDistr.fair Bs procRefrain X := by
    intro X; simp [mixState, State.pr, probOf_mixDistr]
  unfold S2
  simp only [hv]
  unfold mixNu
  simp only [Fin.sum_univ_two, FinDistr.fair, FinDistr.coin, Bs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, slOne_nu_m, slOne_nu_k_m, h1, h2, h3, h4]
  simp [procRefrain, Lesion.fdt]; norm_num

end Cleanroom.Decision.DpSmokingLesion
