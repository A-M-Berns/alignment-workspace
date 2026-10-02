import Cleanroom.Lit.LitShutdownPrefs.PostAppendix
import Cleanroom.Lit.LitShutdownPrefs.TimestepDominance

/-!
# Consistency of POSL ∧ ILPACS (repair round 1; audit round 1, adversarial B1)

The chain `neutrality_of_posl_ilpacs` (POSL ∧ ILPACS ⇒ Neutrality) is a correct theorem; this
file records what its hypothesis package can and cannot be satisfied by.

* **Inconsistency with expected-sum-total single-length preferences**
  (`posl_ilpacs_two_cycle`, `posl_ilpacs_inconsistent`): if `lt` satisfies POSL and ILPACS and
  ranks single-length-`1` lotteries by expected sum-total (Thornley 2024 fn `t08gkcadpjj`: "the
  agent prefers same-length sublotteries in line with their expected sum-total utilities" — the
  money-making POST-agent of 2025 App. 1 at the trajectory level), then two concrete lotteries
  `X`, `Y` satisfy `X ≻ Y ∧ Y ≻ X`. Both ILPACS instances are the paper's own moves: the
  decomposition into `[10]` and a part-shared `D` (POSL makes them lack a preference) gives
  `X ≻ Y`; the *length* decompositions — exactly the one 2025 §7 uses to derive Neutrality —
  give `Y ≻ X`. The mechanism: POSL forces part-shared lotteries to lack a preference, ILPACS
  then licenses arbitrary reweighting between such components, and the reweighting moves mass at
  a shared length in opposite directions in `X` and `Y`. So for every agent with expected-sum-total
  (or comparably monotone) preferences over single-length lotteries the antecedent of
  `neutrality_of_posl_ilpacs` is empty, and the 2025 chain says nothing about it (findings F7).
* **The trivial model** (`posl_ilpacs_trivial_model`): `lt := False` satisfies POSL ∧ ILPACS.
* **A consequence of the display's formal shape** (`ilpacs_lt_mix_of_lt`): since every lottery
  lacks a preference with itself, ILPACS admits the repeated decomposition `A = ½A + ½A`, and
  yields `A ≻ qB + (1−q)A` for all `q ∈ (0,1)` whenever `A ≻ B` — a betweenness property the
  paper does not state and presumably did not intend to build in (findings F7).
* **OPEN** (`posl_ilpacs_nontrivial_model_open`): whether *any* asymmetric relation with a strict
  preference satisfies POSL ∧ ILPACS. Direction unknown; see the docstring for what is known.
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace PostConsistency

open Lottery Strict Finset

/-! ## POSL ∧ ILPACS forces a two-cycle under expected-sum-total single-length preferences -/

/-- The part-shared component `D = ½[0] + ½[1,1]` (lengths `{1, 2}`).
Source: audit round 1, adversarial B1 (probe 1)
Kind: N+ -/
noncomputable def D : Lottery Traj := mix (1/2) (by norm_num) (dirac [0]) (dirac [1, 1])

/-- `D` has lengths `{1, 2}`.
Source: none: infrastructure
Kind: L -/
theorem D_lengths : D.lengths = {1, 2} := by
  unfold D; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]

/-- `X = 0.1·[10] + 0.9·D = 0.1[10] + 0.45[0] + 0.45[1,1]`.
Source: audit round 1, adversarial B1 (probe 1)
Kind: N+ -/
noncomputable def X : Lottery Traj :=
  comb ![1/10, 9/10] (fun i => by fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])
    ![dirac [10], D]

/-- `Y = 0.9·[9] + 0.1·D = 0.9[9] + 0.05[0] + 0.05[1,1]`.
Source: audit round 1, adversarial B1 (probe 1)
Kind: N+ -/
noncomputable def Y : Lottery Traj :=
  comb ![9/10, 1/10] (fun i => by fin_cases i <;> norm_num) (by norm_num [Fin.sum_univ_two])
    ![dirac [9], D]

/-- The length-1 conditional of `X`: `(2/11)[10] + (9/11)[0]`, expected sum-total `20/11`.
Source: audit round 1, adversarial B1 (probe 1)
Kind: N+ -/
noncomputable def X₁ : Lottery Traj := mix (2/11) (by norm_num) (dirac [10]) (dirac [0])

/-- The length-1 conditional of `Y`: `(18/19)[9] + (1/19)[0]`, expected sum-total `162/19`.
Source: audit round 1, adversarial B1 (probe 1)
Kind: N+ -/
noncomputable def Y₁ : Lottery Traj := mix (18/19) (by norm_num) (dirac [9]) (dirac [0])

/-- `X₁` is a single-length lottery of length `1`.
Source: none: infrastructure
Kind: L -/
theorem X₁_lengths : X₁.lengths = {1} := by
  unfold X₁; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]

/-- `Y₁` is a single-length lottery of length `1`.
Source: none: infrastructure
Kind: L -/
theorem Y₁_lengths : Y₁.lengths = {1} := by
  unfold Y₁; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]

/-- `X`'s length decomposition: `X = (11/20) X₁ + (9/20) [1,1]`.
Source: none: infrastructure
Kind: L -/
theorem X_decomp :
    X.p = ∑ i, (![11/20, 9/20] : Fin 2 → ℝ) i • ((![X₁, dirac [1, 1]] : Fin 2 → Lottery Traj) i).p := by
  ext t
  simp only [X, X₁, D, comb_p, mix_p, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

/-- `Y`'s length decomposition: `Y = (19/20) Y₁ + (1/20) [1,1]`.
Source: none: infrastructure
Kind: L -/
theorem Y_decomp :
    Y.p = ∑ i, (![19/20, 1/20] : Fin 2 → ℝ) i • ((![Y₁, dirac [1, 1]] : Fin 2 → Lottery Traj) i).p := by
  ext t
  simp only [Y, Y₁, D, comb_p, mix_p, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

/-- **POSL ∧ ILPACS force a two-cycle.** If `lt` satisfies POSL and ILPACS, is irreflexive, and
ranks single-length-`1` lotteries by expected sum-total (`hEU`; Thornley 2024 fn `t08gkcadpjj`),
then `lt X Y ∧ lt Y X`. ILPACS on `X = 0.1[10] + 0.9 D`, `Y = 0.9[9] + 0.1 D` (components `[10]`
and `D` lack a preference by POSL, `[10] ≻ [9]`) gives `X ≻ Y`; ILPACS on the length
decompositions `Y = (19/20) Y₁ + (1/20)[1,1]`, `X = (11/20) X₁ + (9/20)[1,1]` (components lack a
preference by POSL, `Y₁ ≻ X₁` since `162/19 > 20/11`) gives `Y ≻ X`. The `hEU` used is only for
these four single-length lotteries.
Source: audit round 1, adversarial B1 (probe `posl_ilpacs_two_cycle`); Thornley 2025 §6 l. 175
(ILPACS), §7 (the length decomposition); 2024 fn `t08gkcadpjj` (`hEU`)
Kind: P
Fidelity: exact
Hyps: (a) POSL, ILPACS, irreflexivity; (c) `hEU`: the sources' expected-sum-total ranking of
single-length lotteries, taken as the agent's (the 2024 footnote and the 2025 example agent both
have it) -/
theorem posl_ilpacs_two_cycle (lt : Lottery Traj → Lottery Traj → Prop)
    (hP : POSL lt) (hI : ILPACS lt) (hirr : ∀ Z, ¬ lt Z Z)
    (hEU : ∀ A B : Lottery Traj, A.lengths = {1} → B.lengths = {1} →
      B.expect sumTotal < A.expect sumTotal → lt A B) :
    lt X Y ∧ lt Y X := by
  have hlack : ∀ A B : Lottery Traj, A.lengths ≠ B.lengths → lacks lt A B := fun A B hne =>
    ⟨fun h => hne (hP _ _ h), fun h => hne (hP _ _ h).symm⟩
  have h10 : (dirac ([10] : Traj)).lengths = {1} := by simp [lengths_dirac, len]
  have h9 : (dirac ([9] : Traj)).lengths = {1} := by simp [lengths_dirac, len]
  have h11 : (dirac ([1, 1] : Traj)).lengths = {2} := by simp [lengths_dirac, len]
  have hXY : lt X Y := by
    refine hI 2 ![1/10, 9/10] ![9/10, 1/10] ![dirac [10], D] ![dirac [9], D] X Y rfl rfl
      (fun i => by fin_cases i <;> norm_num) (fun i => by fin_cases i <;> norm_num)
      (fun i j hij => ?_) (fun i => ?_) ⟨0, ?_⟩
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hlack (dirac [10]) D (by rw [h10, D_lengths]; decide)
      · exact hlack D (dirac [10]) (by rw [h10, D_lengths]; decide)
      · exact absurd rfl hij
    · fin_cases i
      · exact Or.inl (hEU _ _ h10 h9 (by norm_num [sumTotal]))
      · exact Or.inr (Strict.indiff_self _ (hirr _))
    · exact hEU _ _ h10 h9 (by norm_num [sumTotal])
  have hYX : lt Y X := by
    refine hI 2 ![19/20, 1/20] ![11/20, 9/20] ![Y₁, dirac [1, 1]] ![X₁, dirac [1, 1]] Y X
      Y_decomp X_decomp
      (fun i => by fin_cases i <;> norm_num) (fun i => by fin_cases i <;> norm_num)
      (fun i j hij => ?_) (fun i => ?_) ⟨0, ?_⟩
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hlack Y₁ (dirac [1, 1]) (by rw [Y₁_lengths, h11]; decide)
      · exact hlack (dirac [1, 1]) Y₁ (by rw [Y₁_lengths, h11]; decide)
      · exact absurd rfl hij
    · fin_cases i
      · exact Or.inl (hEU _ _ Y₁_lengths X₁_lengths (by norm_num [Y₁, X₁, sumTotal]))
      · exact Or.inr (Strict.indiff_self _ (hirr _))
    · exact hEU _ _ Y₁_lengths X₁_lengths (by norm_num [Y₁, X₁, sumTotal])
  exact ⟨hXY, hYX⟩

/-- **POSL ∧ ILPACS ∧ asymmetry ∧ expected-sum-total single-length preferences is inconsistent.**
The antecedent of `neutrality_of_posl_ilpacs` is empty for every asymmetric agent that ranks
single-length-`1` lotteries by expected sum-total.
Source: audit round 1, adversarial B1 (probe `posl_ilpacs_inconsistent`); Thornley 2025 §6–§7
Kind: C
Fidelity: exact
Hyps: (a) POSL, ILPACS, asymmetry; (c) `hEU` as in `posl_ilpacs_two_cycle` -/
theorem posl_ilpacs_inconsistent (lt : Lottery Traj → Lottery Traj → Prop)
    (hP : POSL lt) (hI : ILPACS lt) (hasymm : ∀ A B, lt A B → ¬ lt B A)
    (hEU : ∀ A B : Lottery Traj, A.lengths = {1} → B.lengths = {1} →
      B.expect sumTotal < A.expect sumTotal → lt A B) : False :=
  have h := posl_ilpacs_two_cycle lt hP hI (fun Z h => hasymm Z Z h h) hEU
  hasymm _ _ h.1 h.2

/-! ## What is known on the positive side -/

/-- **The trivial model**: the empty relation satisfies POSL and ILPACS (and is asymmetric). It is
the only model of POSL ∧ ILPACS exhibited in this package.
Source: repair round 1 (the ledger's Witness cell for `neutrality_of_posl_ilpacs`)
Kind: N−
Fidelity: n/a -/
theorem posl_ilpacs_trivial_model :
    POSL (fun _ _ => False) ∧ ILPACS (fun _ _ => False) ∧
      (∀ A B : Lottery Traj, (fun _ _ => False) A B → ¬ (fun _ _ => False) B A) :=
  ⟨fun _ _ h => h.elim, fun _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, h⟩ => h, fun _ _ h => h.elim⟩

/-- **ILPACS with a repeated part.** Every lottery lacks a preference with itself (for an
irreflexive relation), so the ILPACS display admits `X₁ = X₂ = A` with `X = ½A + ½A = A`; taking
`Y₁ = B`, `Y₂ = A` gives `A ≻ qB + (1−q)A` for every `q ∈ (0,1)` whenever `A ≻ B`. A betweenness
property built into the formal statement by its quantifier over decompositions.
Source: Thornley 2025 §6 l. 175 (the display as formalized in `ILPACS`); repair round 1
Kind: P
Fidelity: exact (of the display)
Hyps: (a) all -/
theorem ilpacs_lt_mix_of_lt {lt : Lottery Traj → Lottery Traj → Prop} (hI : ILPACS lt)
    (hirr : ∀ Z, ¬ lt Z Z) {A B : Lottery Traj} (hAB : lt A B) (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    lt A (mix q ⟨hq.1.le, hq.2.le⟩ B A) := by
  refine hI 2 ![1/2, 1/2] ![q, 1 - q] ![A, A] ![B, A] A (mix q ⟨hq.1.le, hq.2.le⟩ B A) ?_ ?_
    (fun i => by fin_cases i <;> norm_num)
    (fun i => by
      fin_cases i
      · simpa using hq
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Set.mem_Ioo]
        constructor <;> linarith [hq.1, hq.2])
    (fun i j _ => by fin_cases i <;> fin_cases j <;> exact ⟨hirr _, hirr _⟩)
    (fun i => ?_) ⟨0, hAB⟩
  · ext t
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul]
    ring
  · ext t
    simp only [mix_p, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  · fin_cases i
    · exact Or.inl hAB
    · exact Or.inr (Strict.indiff_self _ (hirr _))

/-- **OPEN: does POSL ∧ ILPACS have a non-trivial asymmetric model?** Stated in the existence
direction; the direction is *unknown*. What is known: (i) `posl_ilpacs_inconsistent` — no model
ranks single-length lotteries by expected sum-total (so none of the sources' example agents is
one); (ii) the only exhibited model is the empty relation (`posl_ilpacs_trivial_model`); (iii)
any model must have preferences between multi-length lotteries, since `[10] ≻ [9]` and POSL
force `p[10] + (1−p)D ≻ q[9] + (1−q)D` for every `D` of a different length set and all
`p, q ∈ (0,1)`; (iv) hand analysis (report, Repair round 1) of the ILPACS-closure of the single
preference `[10] ≻ [9]` found only chains, no cycle — candidate models are *ordinal* (support- or
order-based) relations, since every cardinal potential tried (expected sum-total, mass on `[10]`
minus mass on `[9]`, the odds of `[10]` against `[9]`) is defeated by a three-part decomposition
with decoupled weights. A proof either way is a finding about Thornley 2025 §7: a model would show
ILPACS is consistent but only with non-EU within-length preferences; impossibility would show the
2025 chain is vacuous for every agent.
Source: audit round 1, adversarial B1 (fix (iv)); repair round 1
Kind: OPEN
Fidelity: exact (of the question)
Hyps: none -/
theorem posl_ilpacs_nontrivial_model_open :
    ∃ lt : Lottery Traj → Lottery Traj → Prop, POSL lt ∧ ILPACS lt ∧
      (∀ A B, lt A B → ¬ lt B A) ∧ ∃ A B, lt A B := by
  sorry

end PostConsistency

end Cleanroom.Lit.LitShutdownPrefs
