import Cleanroom.Udt.UdtSupercondition.Anticipation
import Cleanroom.Udt.UdtSupercondition.DZ
import Cleanroom.Udt.UdtSupercondition.Calibration
import Cleanroom.Udt.UdtSupercondition.Canonical
import Mathlib.Data.Fin.VecNotation

/-!
# Finite witnesses and refutations, I

Non-vacuity witnesses and refutation instances on `Fin n` carriers with rational weights
(`pmfOfReal`), proved by pushing the `ℝ≥0∞` arithmetic through `ENNReal.ofReal` and finishing
with `norm_num` (plan §0.4 rule 8: `n ≤ 8`, no `native_decide`).

* T3 `thm24_sufficiency_refuted`: the quotient obstruction on `Fin 2 → Fin 1` (refutes SC
  Thm 2.4 (⇐) as stated, N+).
* T4 `commonInfo_condModel_witness`: the repaired theorem inhabited with `B = 4/3` (N+).
* T7 `reflective_not_calibrated_witness` (SC Prop 3.8's own example, N+).
* T9 `calibrated_condModel_witness`: Thm 4.5 inhabited with `|A| = 2`, `Q = Fin 3 ≠ Ω`,
  `Q ≠ Q₀`, `B = 2`, non-degenerate kernels (N+).
* T14 `condOn_not_dz_witness`: a bounded-density posterior that is no event conditioning
  (refutes Prop 6.4 under the Diaconis–Zabell reading).

`WitnessesB.lean` has the T10 and T13 instances; `WitnessCountable.lean` the countable ones.

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

/-! ### The numeric toolkit -/

/-- A PMF on `Fin n` from nonnegative real weights summing to one.
Source: none: infrastructure (witness layer; plan §0.4 rule 8)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def pmfOfReal {n : ℕ} (v : Fin n → ℝ) (h0 : ∀ i, 0 ≤ v i) (h1 : ∑ i, v i = 1) :
    PMF (Fin n) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (v i))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 i), h1, ENNReal.ofReal_one])

/-- The mass function of `pmfOfReal`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pmfOfReal_apply {n : ℕ} (v : Fin n → ℝ) (h0 : ∀ i, 0 ≤ v i) (h1 : ∑ i, v i = 1)
    (i : Fin n) : pmfOfReal v h0 h1 i = ENNReal.ofReal (v i) := rfl

/-- Event mass on a finite carrier is a finite sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem mass_fintype {X : Type*} [Fintype X] (P : PMF X) (s : Set X) :
    mass P s = ∑ x, s.indicator P x :=
  PMF.toOuterMeasure_apply_fintype P s

/-- Membership in the preimage of a singleton is decidable when the target has decidable
equality (so `decide` evaluates atom membership on finite witnesses).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
instance decidableMemPreimageSingleton {X Y : Type} [DecidableEq Y] (f : X → Y) (y : Y) (x : X) :
    Decidable (x ∈ f ⁻¹' {y}) :=
  inferInstanceAs (Decidable (f x = y))

/-- `ofReal a + ofReal b = ofReal c` from real arithmetic.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ofReal_add_eq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = c) :
    ENNReal.ofReal a + ENNReal.ofReal b = ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_add ha hb, h]

/-- `ofReal a * ofReal b = ofReal c` from real arithmetic.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ofReal_mul_eq {a b c : ℝ} (ha : 0 ≤ a) (h : a * b = c) :
    ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_mul ha, h]

/-- `ofReal a * ofReal b + ofReal c * ofReal d = ofReal e` from real arithmetic.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ofReal_mul_add_eq {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a * b + c * d = e) :
    ENNReal.ofReal a * ENNReal.ofReal b + ENNReal.ofReal c * ENNReal.ofReal d =
      ENNReal.ofReal e := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_add (mul_nonneg ha hb) (mul_nonneg hc hd), h]

/-- `ofReal a ≠ ofReal b` from real arithmetic.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ofReal_ne_ofReal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≠ b) :
    ENNReal.ofReal a ≠ ENNReal.ofReal b :=
  fun e => h ((ENNReal.ofReal_eq_ofReal_iff ha hb).1 e)

/-- `ofReal a ≠ 0` for positive `a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ofReal_ne_zero' {a : ℝ} (h : 0 < a) : ENNReal.ofReal a ≠ 0 :=
  (ENNReal.ofReal_pos.2 h).ne'

/-- The uniform distribution on `Fin 2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def unif2 : PMF (Fin 2) :=
  pmfOfReal ![1/2, 1/2] (by intro i; fin_cases i <;> norm_num) (by simp [Fin.sum_univ_two]; norm_num)

/-- The uniform distribution on `Fin 4`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def unif4 : PMF (Fin 4) :=
  pmfOfReal ![1/4, 1/4, 1/4, 1/4] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)

/-! ### T14: a bounded-density posterior that is no event conditioning -/

/-- The posterior `(1/3, 2/3)` on `Fin 2`.
Source: none: infrastructure (mandate T14's finding)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def third23 : PMF (Fin 2) :=
  pmfOfReal ![1/3, 2/3] (by intro i; fin_cases i <;> norm_num) (by simp [Fin.sum_univ_two]; norm_num)

/-- `(1/3, 2/3)` has density `≤ 2` w.r.t. the uniform prior on `Fin 2`.
Source: none: infrastructure (mandate T14)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem third23_boundedDensity : BoundedDensity third23 unif2 2 := by
  intro x
  rw [← ENNReal.ofReal_ofNat 2]
  fin_cases x <;>
  · simp only [third23, unif2, pmfOfReal_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one]
    rw [ofReal_mul_eq (by norm_num) rfl]
    exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **Prop 6.4 under the Diaconis–Zabell reading is false:** `(1/3, 2/3)` is in the D–Z set of
the uniform prior on `Fin 2` but is not `P(· | S)` for any event `S` — the three candidates are
`(1, 0)`, `(0, 1)`, `(1/2, 1/2)`. Refinement inside `P̄` can never enrich.
Source: [[superconditioning-mismatched-ontologies]] §6.3 Prop 6.4, §8.4 ("recovers unconstrained
same-ontology superconditioning") | udt-rep-063 (mandate T14's finding)
Kind: N+
Fidelity: n/a (refutation instance)
Hyps: (a) -/
theorem condOn_not_dz_witness :
    third23 ∈ dzPosteriors unif2 ∧
      ¬ ∃ (S : Set (Fin 2)) (h : 0 < mass unif2 S), third23 = condOn unif2 S h := by
  refine ⟨⟨2, ENNReal.ofNat_ne_top, third23_boundedDensity⟩, ?_⟩
  rintro ⟨S, h, e⟩
  have e0 := congrFun (congrArg DFunLike.coe e) 0
  have e1 := congrFun (congrArg DFunLike.coe e) 1
  rw [condOn_apply] at e0 e1
  by_cases h0 : (0 : Fin 2) ∈ S
  · by_cases h1 : (1 : Fin 2) ∈ S
    · rw [indicator_of_mem h0] at e0
      rw [indicator_of_mem h1] at e1
      have : third23 0 = third23 1 := by
        rw [e0, e1]
        simp only [unif2, pmfOfReal_apply, Matrix.cons_val]
      simp only [third23, pmfOfReal_apply, Matrix.cons_val] at this
      exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) this
    · rw [indicator_of_notMem h1, zero_mul] at e1
      simp only [third23, pmfOfReal_apply, Matrix.cons_val] at e1
      exact ofReal_ne_zero' (by norm_num) e1
  · rw [indicator_of_notMem h0, zero_mul] at e0
    simp only [third23, pmfOfReal_apply, Matrix.cons_val] at e0
    exact ofReal_ne_zero' (by norm_num) e0

/-! ### T7: reflective but not calibrated (SC Prop 3.8) -/

/-- The two-atom anticipation map on `Fin 4`: atoms `{0, 2}` (`false`) and `{1, 3}` (`true`)
(SC's `ā₁ = p₁ ∪ p₃`, `ā₂ = p₂ ∪ p₄`).
Source: [[superconditioning-mismatched-ontologies]] §3.4 Prop 3.8
Kind: D
Fidelity: exact
Hyps: n/a -/
def parity4 : Fin 4 → Bool := ![false, true, false, true]

/-- SC's kernel `κ_{ā₁} = (1/2, 0, 1/4, 1/4)`, `κ_{ā₂} = (0, 1/2, 1/4, 1/4)`.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Prop 3.8
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def kappa38 : Bool → PMF (Fin 4)
  | false => pmfOfReal ![1/2, 0, 1/4, 1/4] (by intro i; fin_cases i <;> norm_num)
      (by simp [Fin.sum_univ_four]; norm_num)
  | true => pmfOfReal ![0, 1/2, 1/4, 1/4] (by intro i; fin_cases i <;> norm_num)
      (by simp [Fin.sum_univ_four]; norm_num)

/-- SC Prop 3.8's anticipation structure on the uniform `Fin 4`.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Prop 3.8
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def as38 : AnticipationStructure unif4 (Fin 4) :=
  { A := Bool, a := parity4, κ := kappa38 }

/-- The atom masses of `parity4` under `unif4` are `1/2` each.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem unif4_map_parity4 (b : Bool) : (unif4.map parity4) b = ENNReal.ofReal (1/2) := by
  rw [map_apply_eq_mass, mass_fintype, Fin.sum_univ_four]
  cases b <;>
  · simp only [indicator_apply, mem_preimage, mem_singleton_iff, parity4, Matrix.cons_val,
      Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, unif4,
      pmfOfReal_apply, add_zero, zero_add]
    exact ofReal_add_eq (by norm_num) (by norm_num) (by norm_num)

/-- **SC Prop 3.8, second half (N+):** SC's own structure is reflective but not calibrated —
`P(· | ā₁) = (1/2, 0, 1/2, 0) ≠ κ_{ā₁}`.
Source: [[superconditioning-mismatched-ontologies]] §3.4 Prop 3.8 | udt-rep-057
Kind: N+
Fidelity: exact (SC's own example; `|A| = 2`, non-degenerate kernels)
Hyps: (a) -/
theorem reflective_not_calibrated_witness : as38.Reflective ∧ ¬ as38.Calibrated := by
  constructor
  · refine PMF.ext fun x => ?_
    rw [AnticipationStructure.priorPredictive_apply]
    show ∑' b : Bool, (unif4.map parity4) b * kappa38 b x = unif4 x
    rw [tsum_fintype, Fintype.sum_bool, unif4_map_parity4, unif4_map_parity4]
    fin_cases x <;>
    · simp only [kappa38, unif4, pmfOfReal_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk]
      exact ofReal_mul_add_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
  · intro h
    have := h false 2
    change mass unif4 (parity4 ⁻¹' {false} ∩ {2}) = kappa38 false 2 * (unif4.map parity4) false
      at this
    rw [mass_inter_singleton, indicator_of_mem (by decide), unif4_map_parity4] at this
    simp only [unif4, kappa38, pmfOfReal_apply, Matrix.cons_val] at this
    rw [ofReal_mul_eq (by norm_num) rfl] at this
    exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) this

/-! ### T3: the quotient obstruction instance (refutation of Thm 2.4 (⇐) as stated) -/

/-- The obstruction's common information: `Ω = Fin 2`, `Ω′ = Fin 1`, `C = Fin 2`, `c = id`,
`c′ = const 0` — a homomorphism sending the nonempty event `{1}` to `⊥` (SC §0.2 allows it; the
decision-problems' deductive quotient AN-21 is such a `c′`).
Source: dp-cf-105 (AN-22′) | [[cleanup-audit-2026-08-05]] finding 7
Kind: D
Fidelity: exact
Hyps: n/a -/
def ci3 : CommonInfo (Fin 2) (Fin 1) := { C := Fin 2, c := id, c' := fun _ => 0 }

/-- The point mass on `Fin 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def unif1 : PMF (Fin 1) := PMF.pure 0

/-- **SC Thm 2.4 (⇐) is false as stated (N+ refutation instance):** with `P` uniform on `Fin 2`,
`P′ = δ` on `Fin 1`, `C = Fin 2`, `c = id`, `c′ ≡ 0`, SC's hypotheses hold (`C′ = δ₀ ≤ 2 · C`,
so `C′ ≪ C` with density `≤ 2`), yet no `Ĉ`-compatible conditioning model exists: `C(1) = 1/2 > 0`
but `1 ∉ range c′`.
Source: [[superconditioning-mismatched-ontologies]] §2.5 Thm 2.4 ("A `Ĉ`-compatible conditioning
model … exists if and only if `C′ ≪ C` and `‖dC′/dC‖_∞ < ∞`") | dp-cf-105 | udt-rep-055
Kind: N+
Fidelity: n/a (refutation of SC's sentence under the reading that homomorphisms may send events
to `⊥`, SC §0.2; ATTRIBUTION-UNVETTED whether a surjective `c′` was tacitly meant)
Hyps: (a) -/
theorem thm24_sufficiency_refuted :
    BoundedDensity (ci3.C₂ unif1) (ci3.C₁ unif2) 2 ∧
      ¬ ∃ m : CondModel unif2 unif1, Compatible m ci3 := by
  have hC₁ : ci3.C₁ unif2 = unif2 := PMF.map_id unif2
  have hC₂ : ci3.C₂ unif1 = PMF.pure (0 : Fin 2) := by
    show (PMF.pure (0 : Fin 1)).map (fun _ => (0 : Fin 2)) = PMF.pure 0
    rw [PMF.pure_map]
  constructor
  · rw [hC₁, hC₂]
    have key : @BoundedDensity (Fin 2) (PMF.pure 0) unif2 2 := by
      intro y
      rw [PMF.pure_apply, ← ENNReal.ofReal_ofNat 2]
      fin_cases y
      · simp only [unif2, pmfOfReal_apply, Matrix.cons_val, Fin.zero_eta, if_true]
        rw [ofReal_mul_eq (by norm_num) rfl, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      · simp only [Fin.mk_one, one_ne_zero, if_false]
        exact zero_le
    exact key
  · rintro ⟨m, hm⟩
    have h1 : 0 < ci3.C₁ unif2 (1 : Fin 2) := by
      rw [hC₁]
      simp only [unif2, pmfOfReal_apply, Matrix.cons_val]
      exact ENNReal.ofReal_pos.2 (by norm_num)
    obtain ⟨x', hx'⟩ := compatible_range_subset hm (1 : Fin 2) h1
    exact Fin.zero_ne_one (hx' : (0 : Fin 2) = 1)

/-! ### T4: the repaired theorem's N+ witness -/

/-- The witness common information: `Ω = Fin 4`, `Ω′ = Fin 3`, `C = Bool`, `c x = [x < 2]`,
`c′ = (true, false, false)` — both translations non-injective, ontologies of different size.
Source: mandate T4 (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ci4 : CommonInfo (Fin 4) (Fin 3) :=
  { C := Bool, c := ![true, true, false, false], c' := ![true, false, false] }

/-- The posterior `(2/3, 1/6, 1/6)` on `Fin 3`.
Source: mandate T4 (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def post3 : PMF (Fin 3) :=
  pmfOfReal ![2/3, 1/6, 1/6] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)

/-- `C₁ = (1/2, 1/2)` on `Bool`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ci4_C₁ (b : Bool) : ci4.C₁ unif4 b = ENNReal.ofReal (1/2) := by
  rw [ci4.C₁_apply]
  show mass unif4 ((![true, true, false, false] : Fin 4 → Bool) ⁻¹' {b}) = _
  rw [mass_fintype, Fin.sum_univ_four]
  cases b <;>
  · simp only [indicator_apply, mem_preimage, mem_singleton_iff, ci4, Matrix.cons_val,
      Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, unif4,
      pmfOfReal_apply, add_zero, zero_add]
    exact ofReal_add_eq (by norm_num) (by norm_num) (by norm_num)

/-- `C₂ = (2/3 at true, 1/3 at false)` on `Bool`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ci4_C₂ :
    ci4.C₂ post3 true = ENNReal.ofReal (2/3) ∧ ci4.C₂ post3 false = ENNReal.ofReal (1/3) := by
  constructor
  · rw [ci4.C₂_apply]
    show mass post3 ((![true, false, false] : Fin 3 → Bool) ⁻¹' {true}) = _
    rw [mass_fintype, Fin.sum_univ_three]
    simp only [indicator_apply, mem_preimage, mem_singleton_iff, Matrix.cons_val,
      Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, post3,
      pmfOfReal_apply, add_zero, zero_add]
  · rw [ci4.C₂_apply]
    show mass post3 ((![true, false, false] : Fin 3 → Bool) ⁻¹' {false}) = _
    rw [mass_fintype, Fin.sum_univ_three]
    simp only [indicator_apply, mem_preimage, mem_singleton_iff, Matrix.cons_val,
      Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, post3,
      pmfOfReal_apply, add_zero, zero_add]
    exact ofReal_add_eq (by norm_num) (by norm_num) (by norm_num)

/-- **The repaired Thm 2.4's N+ witness:** for the pair above a `Ĉ`-compatible model exists with
evidence mass `3/4` (`B = 4/3 > 1`); `C₂ ≠ C₁`, so a bound `B > 1` is genuinely needed (the
`B = 1` case of T4 is `C₂ = C₁`); both translations are non-injective and the ontologies have
different cardinalities.
Source: mandate T4 (witness) | [[superconditioning-mismatched-ontologies]] §2.5 | audit r1
(adversarial §3.4: the `C₂ ≠ C₁` conjunct)
Kind: N+
Fidelity: n/a
Hyps: (a): the hypotheses of `commonInfo_condModel_exists_with_mass` are discharged by
`ci4_C₁`, `ci4_C₂` -/
theorem commonInfo_condModel_witness :
    (∃ m : CondModel unif4 post3, Compatible m ci4 ∧ mass m.μ m.ev = (ENNReal.ofReal (4/3))⁻¹) ∧
      1 < ENNReal.ofReal (4/3) ∧ ci4.C₂ post3 ≠ ci4.C₁ unif4 ∧
        ci4.c 0 = ci4.c 1 ∧ ci4.c' 1 = ci4.c' 2 := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · refine commonInfo_condModel_exists_with_mass ci4 unif4 post3 ENNReal.ofReal_ne_top ?_ ?_
    · show ∀ y : Bool, ci4.C₂ post3 y ≤ ENNReal.ofReal (4/3) * ci4.C₁ unif4 y
      intro y
      rw [ci4_C₁]
      cases y
      · rw [ci4_C₂.2, ofReal_mul_eq (by norm_num) rfl]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      · rw [ci4_C₂.1, ofReal_mul_eq (by norm_num) rfl]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
    · show ∀ y : Bool, 0 < ci4.C₁ unif4 y → y ∈ Set.range ci4.c'
      intro y _
      cases y
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  · rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num
  · intro e
    have h1 := ci4_C₂.1
    rw [e, ci4_C₁] at h1
    exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h1

/-! ### T9: Thm 4.5's N+ witness -/

/-- The T9 kernel: `κ_{false} = (1/2, 1/4, 1/4)`, `κ_{true} = (0, 1/2, 1/2)` on `Fin 3`.
Source: mandate T9 (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def kappa9 : Bool → PMF (Fin 3)
  | false => pmfOfReal ![1/2, 1/4, 1/4] (by intro i; fin_cases i <;> norm_num)
      (by simp [Fin.sum_univ_three]; norm_num)
  | true => pmfOfReal ![0, 1/2, 1/2] (by intro i; fin_cases i <;> norm_num)
      (by simp [Fin.sum_univ_three]; norm_num)

/-- The T9 anticipation structure on the uniform `Fin 4`, targeting `Fin 3`.
Source: mandate T9 (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def as9 : AnticipationStructure unif4 (Fin 3) :=
  { A := Bool, a := parity4, κ := kappa9 }

/-- The prescribed posterior `(1/2, 1/4, 1/4)` on `Fin 3`.
Source: mandate T9 (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def post9 : PMF (Fin 3) :=
  pmfOfReal ![1/2, 1/4, 1/4] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num)

/-- The prior-predictive of `as9` is `(1/4, 3/8, 3/8)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem as9_priorPredictive (q : Fin 3) :
    as9.priorPredictive q = ENNReal.ofReal (![1/4, 3/8, 3/8] q) := by
  rw [AnticipationStructure.priorPredictive_apply]
  show ∑' b : Bool, (unif4.map parity4) b * kappa9 b q = _
  rw [tsum_fintype, Fintype.sum_bool, unif4_map_parity4, unif4_map_parity4]
  fin_cases q <;>
  · simp only [kappa9, pmfOfReal_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    exact ofReal_mul_add_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Thm 4.5's N+ witness:** with `|A| = 2`, `Q = Fin 3 ≠ Ω = Fin 4`, non-degenerate kernels,
`post9 ≠ Q₀` and `B = 2 > 1`, a calibrated model with posterior `post9` and evidence mass `1/2`
exists.
Source: mandate T9 (witness) | [[superconditioning-mismatched-ontologies]] §4.4 Thm 4.5
Kind: N+
Fidelity: n/a
Hyps: (a): the density bound is discharged by `as9_priorPredictive` -/
theorem calibrated_condModel_witness :
    (∃ m : CondModel unif4 post9, CMCalibrated m as9 ∧ mass m.μ m.ev = (2 : ℝ≥0∞)⁻¹) ∧
      post9 ≠ as9.priorPredictive := by
  constructor
  · refine calibrated_condModel_exists as9 post9 ENNReal.ofNat_ne_top fun q => ?_
    rw [as9_priorPredictive, ← ENNReal.ofReal_ofNat 2]
    fin_cases q <;>
    · simp only [post9, pmfOfReal_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      rw [ofReal_mul_eq (by norm_num) rfl]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
  · intro e
    have := congrFun (congrArg DFunLike.coe e) 0
    rw [as9_priorPredictive] at this
    simp only [post9, pmfOfReal_apply, Matrix.cons_val] at this
    exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) this

end Cleanroom.Udt.UdtSupercondition
