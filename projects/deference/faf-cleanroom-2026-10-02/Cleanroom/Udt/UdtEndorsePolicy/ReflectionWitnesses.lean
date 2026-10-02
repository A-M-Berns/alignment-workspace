import Cleanroom.Udt.UdtEndorsePolicy.Reflection
import Cleanroom.Udt.UdtSupercondition.Witnesses
import Mathlib.Tactic.FinCases

/-!
# T3(d): both steps of the ladder are strict

* `reflective_not_endorsed_witness`: SC's own `as38` (uniform `Fin 4`, atoms = parity, kernels
  `(1/2, 0, 1/4, 1/4)` / `(0, 1/2, 1/4, 1/4)`) is reflective but not belief-endorsed on
  `X = {0, 2}`: the future belief report is `3/4` on the even atom, where `P(X | atom) = 1`.
* `endorsed_not_calibrated_witness`: on the uniform `Fin 3` with `a = id` and kernels
  `κ₀ = (1/2, 0, 1/2)`, `κ₁ = (1/2, 1/2, 0)`, `κ₂ = (0, 1/2, 1/2)` the prior is belief-endorsed
  on all eight events (each value class is either an atom where `P(X | atom) ∈ {0, 1}` equals
  the kernel's value, or the pair of atoms whose kernels put `1/2` on `X`, where
  `P(X | pair) = 1/2`), but not calibrated (`κ₀ ≠ δ₀`).
* `beliefEndorsedAll_not_expectationEndorsedAll_witness` (T2(d)(ii)): the same `Fin 3`
  structure is not expectation-endorsed for `V = (1, 2, 0)` — the future expectation report takes
  three distinct values, so endorsement would force `E[V | {0}] = 1` to equal `1/2`.

The mandate writer's hand computations (mandate T3(d)) are confirmed by these proofs.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Finset
open Cleanroom.Udt.UdtSupercondition (AnticipationStructure pmfOfReal pmfOfReal_apply unif4 as38
  kappa38 parity4 reflective_not_calibrated_witness ofReal_ne_ofReal ofReal_mul_eq)
open scoped ENNReal

noncomputable section

/-! ### Toolkit for `pmfOfReal` structures -/

/-- Supporting lemma: the real weights of `pmfOfReal v` are `v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pw_pmfOfReal {n : ℕ} (v : Fin n → ℝ) (h0 : ∀ i, 0 ≤ v i) (h1 : ∑ i, v i = 1) :
    pw (pmfOfReal v h0 h1) = v := by
  funext i
  rw [pw, pmfOfReal_apply, ENNReal.toReal_ofReal (h0 i)]

/-- Supporting lemma: the real mass of a finite event under `pmfOfReal v` is `∑ i ∈ X, v i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toReal_mass_pmfOfReal {n : ℕ} (v : Fin n → ℝ) (h0 : ∀ i, 0 ≤ v i) (h1 : ∑ i, v i = 1)
    (X : Finset (Fin n)) :
    (UdtSupercondition.mass (pmfOfReal v h0 h1) (↑X : Set (Fin n))).toReal = ∑ i ∈ X, v i := by
  rw [toReal_mass_finset, mass, pw_pmfOfReal]

/-! ### Reflective, not endorsed: SC's `as38` -/

/-- The event `X = {0, 2}` on `Fin 4` (the even atom of `parity4`).
Source: mandate T3(d)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def X02f4 : Finset (Fin 4) := {0, 2}

/-- Supporting lemma: the real weights of `unif4` are `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pw_unif4 (ω : Fin 4) : pw unif4 ω = 1 / 4 := by
  rw [unif4, pw_pmfOfReal]
  fin_cases ω <;> simp

/-- Supporting lemma: on `as38`, the future belief about `{0, 2}` is `3/4` on the even atom and
`1/4` on the odd atom.
Source: mandate T3(d) (hand computation, confirmed)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem futureBelief_as38_X02 : futureBelief as38 X02f4 = ![3 / 4, 1 / 4, 3 / 4, 1 / 4] := by
  funext ω
  show (UdtSupercondition.mass (kappa38 (parity4 ω)) ↑X02f4).toReal = _
  fin_cases ω <;>
  · simp only [parity4, kappa38, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue]
    rw [toReal_mass_pmfOfReal, X02f4, Finset.sum_pair (by decide)]
    simp only [Matrix.cons_val, Fin.isValue]
    norm_num

/-- **T3(d), reflective ⇏ endorsed** (N+, `refuted` for the converse of T3(c)): SC's `as38` is
reflective (`reflective_not_calibrated_witness`) but not belief-endorsed on `{0, 2}`: on the
class `{Q_X = 3/4}`, which is the even atom `{0, 2}` itself, `P(X | class) = 1 ≠ 3/4`.
(i) The refuted sentence: the inventory's converse "endorsement ⟸ the future belief is a
conditional of the present one" read as "reflective ⟹ endorsed" (udt-rep-2-014); (ii) reading:
SC's Def 3.7 reflection versus `BeliefEndorsedAll`; (iii) survivor: `reflective_of_beliefEndorsedAll`
(the direction that holds) and `beliefEndorsedAll_condAnticipation` (reflection *of a
conditional* is endorsed).
Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle | udt-rep-2-014 | SC Prop 3.8
Kind: N+
Fidelity: n/a (SC's own example: two atoms, non-degenerate kernels, non-constant report)
Hyps: none -/
theorem reflective_not_endorsed_witness : as38.Reflective ∧ ¬ BeliefEndorsedAll unif4 as38 := by
  refine ⟨reflective_not_calibrated_witness.1, fun h => ?_⟩
  have h1 := (beliefEndorses_iff_forall_pt (pw_nonneg _) _ _).1 (h X02f4) 0
    (by rw [pw_unif4]; norm_num)
  rw [mass_inter_event_eq, mass_event_eq, Fin.sum_univ_four, Fin.sum_univ_four,
    futureBelief_as38_X02] at h1
  simp only [pw_unif4, X02f4, Matrix.cons_val, Fin.isValue, Finset.mem_insert,
    Finset.mem_singleton] at h1
  norm_num at h1

/-! ### Endorsed, not calibrated (and not expectation-endorsed): the `Fin 3` structure -/

/-- The uniform distribution on `Fin 3`.
Source: mandate T3(d)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def unif3 : PMF (Fin 3) :=
  pmfOfReal ![1 / 3, 1 / 3, 1 / 3] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)

/-- The kernel table `κ₀ = (1/2, 0, 1/2)`, `κ₁ = (1/2, 1/2, 0)`, `κ₂ = (0, 1/2, 1/2)`: each atom's
future belief is uniform on itself and its predecessor (mod 3).
Source: mandate T3(d)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def kv3 : Fin 3 → Fin 3 → ℝ := ![![1 / 2, 0, 1 / 2], ![1 / 2, 1 / 2, 0], ![0, 1 / 2, 1 / 2]]

/-- Supporting lemma `kv3_nonneg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem kv3_nonneg (i j : Fin 3) : 0 ≤ kv3 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [kv3]

/-- Supporting lemma `kv3_sum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem kv3_sum (i : Fin 3) : ∑ j, kv3 i j = 1 := by
  fin_cases i <;> simp [kv3, Fin.sum_univ_three] <;> norm_num

/-- The kernels of the `Fin 3` structure.
Source: mandate T3(d)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def kappa3 (i : Fin 3) : PMF (Fin 3) := pmfOfReal (kv3 i) (kv3_nonneg i) (kv3_sum i)

/-- The `Fin 3` anticipation structure: atoms are the points (`a = id`), kernels `kappa3`.
Source: mandate T3(d)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def as3 : AnticipationStructure unif3 (Fin 3) := { A := Fin 3, a := id, κ := kappa3 }

/-- Supporting lemma: the real weights of `unif3` are `1/3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pw_unif3 (ω : Fin 3) : pw unif3 ω = 1 / 3 := by
  rw [unif3, pw_pmfOfReal]
  fin_cases ω <;> simp

/-- Supporting lemma: the real kernel weights of `as3` are `kv3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem kappa3_toReal (i j : Fin 3) : (kappa3 i j).toReal = kv3 i j := by
  rw [← pw, kappa3, pw_pmfOfReal]

/-- Supporting lemma: on `as3` the future belief about `X` at `ω` is `∑_{i ∈ X} kv3 ω i`, as an
`if`-sum over the three points.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem futureBelief_as3 (X : Finset (Fin 3)) (ω : Fin 3) :
    futureBelief as3 X ω = ∑ i, if i ∈ X then kv3 ω i else 0 := by
  show (UdtSupercondition.mass (kappa3 ω) ↑X).toReal = _
  rw [kappa3, toReal_mass_pmfOfReal]
  exact ((Finset.sum_ite_mem univ X (kv3 ω)).trans (by rw [Finset.univ_inter])).symm

/-- **The `Fin 3` structure is belief-endorsed on every event** (all eight events, all three
points, checked cell by cell).
Source: mandate T3(d) (hand computation, confirmed)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem as3_beliefEndorsedAll : BeliefEndorsedAll unif3 as3 := by
  intro X
  rw [beliefEndorses_iff_forall_pt (pw_nonneg _)]
  intro ω _
  rw [mass_inter_event_eq, mass_event_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [futureBelief_as3, Fin.sum_univ_three, pw_unif3]
  fin_cases ω <;> by_cases h0 : (0 : Fin 3) ∈ X <;> by_cases h1 : (1 : Fin 3) ∈ X <;>
    by_cases h2 : (2 : Fin 3) ∈ X <;>
  · simp only [h0, h1, h2, kv3, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, if_true, if_false, and_true, and_false, and_self]
    norm_num

/-- **The `Fin 3` structure is not calibrated**: on the atom `{0}`, `P(0 | {0}) = 1 ≠ 1/2 = κ₀(0)`.
Source: mandate T3(d)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem as3_not_calibrated : ¬ as3.Calibrated := by
  intro h
  have := h (show as3.A from (0 : Fin 3)) 0
  change UdtSupercondition.mass unif3 (id ⁻¹' {0} ∩ {0}) = kappa3 0 0 * (unif3.map id) 0 at this
  rw [UdtSupercondition.mass_inter_singleton, Set.indicator_of_mem (by simp), PMF.map_id] at this
  simp only [unif3, kappa3, kv3, pmfOfReal_apply, Matrix.cons_val, Fin.isValue] at this
  rw [ofReal_mul_eq (by norm_num) rfl] at this
  exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) this

/-- **T3(d), endorsed ⇏ calibrated** (N+, `refuted` for the converse of T3(b)): the `Fin 3`
structure is belief-endorsed on every event but not calibrated. (i) The refuted sentence: the
converse of "calibration ⟹ endorsement" (mandate T3(d)); (ii) reading: SC-internal calibration
(Def 3.5) versus `BeliefEndorsedAll`; (iii) survivor: `beliefEndorsedAll_of_calibrated` and, for
expectation reports, `expectationEndorsedAll_of_calibrated` (the stretch question of whether
`ExpectationEndorsedAll` characterizes calibration up to kernel-coarsening is left open in the
report).
Source: [[meaning-and-agency-reference]] §The Van Fraassen Reflection Principle | udt-rep-2-014 | SC Def 3.5
Kind: N+
Fidelity: n/a (three atoms, non-degenerate kernels, every report non-constant on the non-trivial events)
Hyps: none -/
theorem endorsed_not_calibrated_witness : BeliefEndorsedAll unif3 as3 ∧ ¬ as3.Calibrated :=
  ⟨as3_beliefEndorsedAll, as3_not_calibrated⟩

/-- The variable `V = (1, 2, 0)`.
Source: mandate T3(d)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def V120 : Fin 3 → ℝ := ![1, 2, 0]

/-- Supporting lemma: on `as3`, the future expectation of `V120` is `(1/2, 3/2, 1)`.
Source: mandate T3(d) (hand computation, confirmed)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem futureExp_as3_V120 : futureExp as3 V120 = ![1 / 2, 3 / 2, 1] := by
  funext ω
  show ∑ x, (kappa3 ω x).toReal * V120 x = _
  simp only [kappa3_toReal, Fin.sum_univ_three]
  fin_cases ω <;>
  · simp only [kv3, V120, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
    norm_num

/-- **The `Fin 3` structure is not expectation-endorsed** for `V = (1, 2, 0)`: the future
expectation report `(1/2, 3/2, 1)` separates the points, so the class of `0` is `{0}`, where
`E[V | {0}] = 1 ≠ 1/2`.
Source: mandate T3(d)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem as3_not_expectationEndorsedAll : ¬ ExpectationEndorsedAll unif3 as3 := by
  intro h
  have h1 := (expectationEndorses_iff_forall_pt (pw_nonneg _) _ _).1 (h V120) 0
    (by rw [pw_unif3]; norm_num)
  rw [wsum_event_eq, mass_event_eq, Fin.sum_univ_three, Fin.sum_univ_three,
    futureExp_as3_V120] at h1
  simp only [pw_unif3, V120, Matrix.cons_val, Fin.isValue] at h1
  norm_num at h1

/-- **T2(d)(ii): belief endorsement on every event does not imply expectation endorsement on
every variable** (N+): the `Fin 3` structure is belief-endorsed on all eight events but not
expectation-endorsed for `V = (1, 2, 0)`. So "expectation endorsement generalizes belief
endorsement" is a proper generalization even when quantified over all events/variables.
Source: [[meaning-and-agency-reference]] §Expectation Endorsement (the "generalizes" line) | udt-rep-2-013 | mandate T2(d)(ii), T3(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem beliefEndorsedAll_not_expectationEndorsedAll_witness :
    BeliefEndorsedAll unif3 as3 ∧ ¬ ExpectationEndorsedAll unif3 as3 :=
  ⟨as3_beliefEndorsedAll, as3_not_expectationEndorsedAll⟩

end

end Cleanroom.Udt.UdtEndorsePolicy
