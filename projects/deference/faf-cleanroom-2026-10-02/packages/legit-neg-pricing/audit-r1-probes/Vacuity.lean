import Cleanroom.Corrigibility.LegitNegPricing.Inertness
import Cleanroom.Corrigibility.LegitNegPricing.Ratifiability
import Cleanroom.Corrigibility.LegitNegPricing.Scoring
import Cleanroom.Corrigibility.LegitNegPricing.CrossBranch

/-!
# Audit round 1 (adversarial) — probes for `legit-neg-pricing`

Not imported by the library. Elaborated with `scripts/lean-check`. Each probe is evidence for a
line of `legit-neg-pricing-audit-r1-adversarial.md`; none is a counterexample to a proved
theorem (every headline is kernel-checked and, as far as this audit can see, true). They show
where a grade or a kind oversells, and where a hypothesis is weaker than shipped.

* **P1** — `S2cell_witness4`'s cells coincide with `L_{a₁}`'s own partition for `a₁` and `a₀` is
  fully legitimate, so the shipped witness exercises only the two named instances of
  `P1_S2cell_eq_P1_S1_of_pure`. A replacement witness whose cells are *strictly* between the
  singleton partition and `L_{a₁}`'s partition for a non-trivially-legitimate action.
* **P2** — `P1_S2cell_eq_P1_S1_of_pure` holds *without* the positive-cell-mass hypothesis.
* **P3** — `argmaxLex_R2scoresP4a_eq` is an instance of "lex with a menu-common first
  coordinate is the argmax of the second", a fact about `Prod.Lex` with no R2 content.
* **P4** — `selectDiag P V = argmax (P.P1 V)` whenever `ratifiable V = univ`; so the two V14
  selection instances (both on scenarios where `ratifiable = univ`) say nothing beyond
  `V14_scenario_N/_C`'s first conjunct. Also: on scenario N the credence `(1/2, 1/2)` is *not*
  mixed-ratifiable, so the shipped interior point `(2/5, 3/5)` is genuinely isolated (N+ upheld).
* **P5** — `P5_located_eq_forall_iff` admits `π(L) = 0`: there every `P5` is `none`, both sides
  of the iff are false, and the theorem is about the unpacked formula, not `P5`.
* **P6** — `P2_S3_eq_one_of_hindsight_best` at `D = 0` needs no hindsight-best hypothesis
  (`S3 0` is the constant vector `1`); the mandate's `0 < D` is not in the statement.
* **P7** — `B14_toy`'s "`a₁` ratifiable for every `w`" includes `π_b = 1`, where it holds for
  the V1 reason (`P(L | a₁) = 0`, every menu score `0`), not the docstring's reason.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

variable {S A : Type} [Fintype S] [Fintype A]

/-! ## P1: the shipped B11 (ii) witness only hits the two named instances; a strictly-between one -/

/-- In `S2cell_witness4`, the cells are exactly `L_{a₁}`'s own partition (so for `a₁` the witness
is the `P1_S2cell_legPartition_eq` instance), and `a₀` is legitimate everywhere (so for `a₀` the
collapse is the tower property over any partition, no purity content). -/
theorem P1_shipped_witness_is_the_instances :
    let P : Problem (Fin 4) (Fin 2) :=
      { prior := fun _ => 1/4
        prior_nonneg := fun _ => by norm_num
        prior_sum := by simp
        leg := fun s a => !(decide (2 ≤ s.val) && decide (a = 1))
        u := fun s a => ![![1/2, 1], ![1/4, 3/4], ![0, 1/3], ![1, 1/5]] s a }
    let cellOf : Fin 4 → Finset (Fin 4) := fun s => if s.val < 2 then {0, 1} else {2, 3}
    (∀ s, cellOf s = univ.filter fun t => P.leg t 1 = P.leg s 1)
    ∧ (∀ s, P.leg s 0 = true) := by
  intro P cellOf
  exact ⟨by decide, by decide⟩

/-- A replacement witness: `a₁` legitimate on `{0, 1, 2}` and void on `{3}`; cells `{0, 1}`, `{2}`,
`{3}` — `L_{a₁}`-pure, strictly coarser than the singletons at `0` and strictly finer than
`L_{a₁}`'s partition `{0, 1, 2}` at `0`; `u(·, a₁)` non-constant; and the collapse holds. -/
theorem P1_strictly_between_witness :
    let P : Problem (Fin 4) (Fin 2) :=
      { prior := fun _ => 1/4
        prior_nonneg := fun _ => by norm_num
        prior_sum := by simp
        leg := fun s a => !(decide (s = 3) && decide (a = 1))
        u := fun s a => ![![1/2, 1], ![1/4, 1/2], ![0, 1/4], ![1, 0]] s a }
    let cellOf : Fin 4 → Finset (Fin 4) :=
      fun s => if s.val < 2 then {0, 1} else if s = 2 then {2} else {3}
    (∀ s, s ∈ cellOf s) ∧ (∀ s t, t ∈ cellOf s → cellOf t = cellOf s)
    ∧ (∀ s, 0 < ∑ t ∈ cellOf s, P.prior t)
    ∧ (∀ s t, t ∈ cellOf s → P.leg t 1 = P.leg s 1)
    ∧ cellOf 0 ≠ {0}
    ∧ cellOf 0 ≠ univ.filter (fun t => P.leg t 1 = P.leg 0 1)
    ∧ P.PL 1 = 3/4
    ∧ P.P1 (P.S2cell cellOf) 1 = 7/16 ∧ P.P1 (S1 P.u) 1 = 7/16 := by
  intro P cellOf
  have hmem : ∀ s, s ∈ cellOf s := by decide
  have hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s := by decide
  have hpos : ∀ s, 0 < ∑ t ∈ cellOf s, P.prior t := by
    intro s; fin_cases s <;> simp [cellOf, P] <;> norm_num
  have hpure : ∀ s t, t ∈ cellOf s → P.leg t 1 = P.leg s 1 := by decide
  refine ⟨hmem, hcell, hpos, hpure, by decide, by decide, ?_, ?_, ?_⟩
  · simp [P, Problem.PL, Problem.mass, Fin.sum_univ_four]; norm_num
  · simp [P, cellOf, Problem.P1, Problem.S2cell, Problem.Hc, Problem.cellprior, Fin.sum_univ_four]
    norm_num
  · simp [P, Problem.P1, Fin.sum_univ_four]; norm_num

/-! ## P2: the pure collapse needs no positive cell mass -/

/-- `P1_S2cell_eq_P1_S1_of_pure` without `hpos`: a zero-mass cell contributes `0 · junk = 0` on
both sides. -/
theorem P2_pure_collapse_without_positivity [DecidableEq S] (P : Problem S A)
    (cellOf : S → Finset S) (a : A)
    (hmem : ∀ s, s ∈ cellOf s) (hcell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s)
    (hpure : ∀ s t, t ∈ cellOf s → P.leg t a = P.leg s a) :
    P.P1 (P.S2cell cellOf) a = P.P1 (S1 P.u) a := by
  rw [P1_S2cell_eq P cellOf a hmem hcell]
  unfold Problem.P1
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hp : P.prior t = 0
  · simp [hp]
  · have h1 : 0 < P.prior t := lt_of_le_of_ne (P.prior_nonneg t) (Ne.symm hp)
    have hposc : 0 < ∑ s ∈ cellOf t, P.prior s :=
      lt_of_lt_of_le h1 (Finset.single_le_sum (fun s _ => P.prior_nonneg s) (hmem t))
    have hc : condLeg P cellOf a t = ind (P.leg t a) := by
      unfold condLeg
      rw [div_eq_iff hposc.ne', Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hpure t s hs]; ring
    rw [hc]; simp only [S1_apply]; ring

/-! ## P3: the P4a R2 inertness is a fact about `Prod.Lex` -/

/-- Lex order with a menu-common first coordinate: the argmax is the second coordinate's. -/
theorem P3_lex_const_first (c : ℚ) (f : A → ℚ) :
    argmaxLex (fun a => toLex (c, f a)) = argmax f := by
  ext a
  simp only [mem_argmaxLex, mem_argmax, Prod.Lex.toLex_le_toLex, lt_self_iff_false, true_and,
    false_or]

/-- `argmaxLex_R2scoresP4a_eq` is that fact at `c = P(L | a*)`, `f = R2scoresP3 (λ = 1)`. -/
theorem P3_R2scoresP4a_is_lex_const (P : Problem S A) (Wg V : MenuVec S A) (astar : A) :
    argmaxLex (R2scoresP4a P Wg V astar) = argmax (P.R2scoresP3 Wg 1 V astar) :=
  P3_lex_const_first (P.PL astar) (P.R2scoresP3 Wg 1 V astar)

/-! ## P4: the V14 selection instances are the `ratifiable = univ` conjunct in disguise -/

/-- Whenever every action is ratifiable, own-diagonal selection is R1-P1's argmax by definition. -/
theorem P4_selectDiag_of_univ (P : Problem S A) (V : MenuVec S A) (h : P.ratifiable V = univ) :
    selectDiag P V = argmax (P.P1 V) := by
  unfold selectDiag; rw [h]; ext a; simp [mem_argmax]

/-- Both V14 selection instances follow from the scenarios' `ratifiable = univ` conjunct alone. -/
theorem P4_V14_selection_from_univ :
    selectDiag (toyB (1/4) 0 (9/10) 1 (1/2) (by norm_num) (by norm_num))
        (S1 (toyB (1/4) 0 (9/10) 1 (1/2) (by norm_num) (by norm_num)).u)
      = argmax ((toyB (1/4) 0 (9/10) 1 (1/2) (by norm_num) (by norm_num)).P1
          (S1 (toyB (1/4) 0 (9/10) 1 (1/2) (by norm_num) (by norm_num)).u))
    ∧ selectDiag (toyB (1/20) (-1) (9/10) 1 (1/2) (by norm_num) (by norm_num))
        (S1 (toyB (1/20) (-1) (9/10) 1 (1/2) (by norm_num) (by norm_num)).u)
      = argmax ((toyB (1/20) (-1) (9/10) 1 (1/2) (by norm_num) (by norm_num)).P1
          (S1 (toyB (1/20) (-1) (9/10) 1 (1/2) (by norm_num) (by norm_num)).u)) :=
  ⟨P4_selectDiag_of_univ _ _ V14_scenario_N.1, P4_selectDiag_of_univ _ _ V14_scenario_C.1⟩

/-- On scenario N the uniform credence is *not* mixed-ratifiable: the forecast menu gives
`a₀` `41/80 > 40/80`, so `a₁` is in the support but not a maximiser. The shipped `(2/5, 3/5)`
is the unique interior mixed fixed point (N+ upheld). -/
theorem P4_V14_N_uniform_not_mixed :
    let P := toyB (1/4) 0 (9/10) 1 (1/2) (by norm_num) (by norm_num)
    ¬ MixedRatifiable P (S1 P.u) ![1/2, 1/2] := by
  intro P h
  obtain ⟨-, -, h3⟩ := h
  have h1 := h3 1 (by norm_num)
  rw [mem_argmax] at h1
  have h0 := h1 0
  simp only [Fin.sum_univ_two, P, toyB_R2scores_S1_zero, toyB_R2scores_S1_one, toyB_H_zero,
    toyB_H_one, Matrix.cons_val_zero, Matrix.cons_val_one] at h0
  norm_num at h0

/-! ## P5: `P5_located_eq_forall_iff` at `π(L) = 0` -/

/-- A sealed problem with `ℓ ≡ false`: the theorem's hypotheses hold, every `P5` is `none`,
`condL` is the junk zero vector, and both sides of the iff are false. -/
theorem P5_C7_at_zero_L_mass :
    let P : Problem (Fin 2) (Fin 2) :=
      { prior := ![1/2, 1/2]
        prior_nonneg := by intro s; fin_cases s <;> simp
        prior_sum := by simp [Fin.sum_univ_two]; norm_num
        leg := fun _ _ => false
        u := fun _ _ => 0 }
    let ℓ : Fin 2 → Bool := fun _ => false
    let info : Fin 2 → Fin 2 := id
    P.SealedBy ℓ
    ∧ P.mass (fun s => !ℓ s) ≠ 0
    ∧ (∀ k a, P.P5 (locatedK info k) (S1 P.u) a = none)
    ∧ (∀ i, condL P ℓ info i = 0)
    ∧ condL P ℓ info ≠ condN P ℓ info
    ∧ ¬ (∀ k : Fin 2 → ℚ, P.P1 (S1 P.u) 0 + (1 - P.PL 0) * P.Kbar (locatedK info k) 0
        = P.P1 (S1 P.u) 0 + P.mass (fun s => !ℓ s) * ∑ i, condN P ℓ info i * k i) := by
  intro P ℓ info
  have hPL : ∀ a, P.PL a = 0 := by intro a; simp [P, Problem.PL, Problem.mass]
  have hN : P.mass (fun s => !ℓ s) = 1 := by
    simp [P, ℓ, Problem.mass, Fin.sum_univ_two]; norm_num
  have hL : ∀ i, condL P ℓ info i = 0 := by
    intro i; simp [condL, massLI, P, ℓ, Problem.mass]
  have hcN : ∀ i, condN P ℓ info i = 1/2 := by
    intro i
    simp only [condN, massNI, hN, div_one]
    fin_cases i <;> simp [P, ℓ, info, Problem.mass]
  refine ⟨fun s a => rfl, by rw [hN]; norm_num, fun k a => ?_, hL, ?_, ?_⟩
  · unfold Problem.P5; rw [if_pos (hPL a)]
  · intro h
    have := congrFun h 0
    rw [hL, hcN] at this; norm_num at this
  · intro h
    have := h (fun _ => 1)
    simp only [hPL, hN, hcN, Fin.sum_univ_two] at this
    have hP1 : P.P1 (S1 P.u) 0 = 0 := by simp [P, Problem.P1]
    have hK : P.Kbar (locatedK info fun _ => (1 : ℚ)) 0 = 0 := by
      simp [Problem.Kbar, P, Problem.PL, Problem.mass]
    rw [hP1, hK] at this; norm_num at this

/-! ## P6: `S3 0` is the constant vector `1`, so the B12 conditioning headline is trivial at `D = 0` -/

theorem P6_S3_zero_no_hypothesis [Nonempty A] (P : Problem S A) (a : A) (h : P.PL a ≠ 0) :
    P.P2 (P.S3 0) a = some 1 := by
  rw [P2_of_ne _ _ _ h]
  congr 1
  have : P.P1 (P.S3 0) a = P.PL a := by
    unfold Problem.P1 Problem.PL Problem.mass
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [Problem.S3]
  rw [this, div_self h]

/-! ## P7: `B14_toy`'s parametric range includes the V1 vacuous case -/

theorem P7_B14_toy_at_pib_one :
    1 ∈ (toyB 0 0 0 1 1 (by norm_num) le_rfl).ratifiable (S1 (toyB 0 0 0 1 1 (by norm_num) le_rfl).u)
    ∧ (toyB 0 0 0 1 1 (by norm_num) le_rfl).PL 1 = 0 :=
  ⟨(B14_toy 0 0 0 1 (by norm_num) le_rfl (by norm_num)).1, by rw [toyB_PL_one]; norm_num⟩

end Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial

/-! ## Axioms used by the probes -/

#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial.P1_strictly_between_witness
#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial.P2_pure_collapse_without_positivity
#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial.P3_R2scoresP4a_is_lex_const
#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial.P4_V14_N_uniform_not_mixed
#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial.P5_C7_at_zero_L_mass
#print axioms Cleanroom.Corrigibility.LegitNegPricing.AuditR1Adversarial.P6_S3_zero_no_hypothesis
