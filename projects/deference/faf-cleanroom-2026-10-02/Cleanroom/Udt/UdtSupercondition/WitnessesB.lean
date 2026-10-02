import Cleanroom.Udt.UdtSupercondition.Witnesses
import Cleanroom.Udt.UdtSupercondition.Landscape

/-!
# Finite witnesses and refutations, II

* T10 `prop47_refuted`: both of SC Prop 4.7's D–Z conditions hold (`B = 1`), the anticipation is
  not `Ĉ`-calibrated, and no compatible calibrated model exists (N+, cross-ontology
  `Fin 2 → Bool`).
* T10 `bridgeCalibrated_not_calibrated`: `Ĉ`-calibration does not imply calibration (N+: SC's
  `Fin 4` carrier, `C = Bool`, `c = c′ = parity4`, non-constant and non-injective, two atoms,
  point-mass kernels — repair round 1, replacing the trivial-`C` instance, kept as the N−
  `bridgeCalibrated_not_calibrated_trivialCI`).
* T13 `canonical_not_jeffreyMixture_witness`: a canonical posterior with an `x`-dependent
  selection that is no Jeffrey mixture (N+, on SC's Prop 3.8 structure);
  `post13_not_jeffreyOnA`: the same posterior is no Jeffrey update on the atoms of `parity4`
  in the general sense either (robustness of the strictness to the reading of "Jeffrey").
* T13 `dz_not_canonical_witness`: a bounded-density posterior that is not canonical (N+).

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

/-- `ofReal a * ofReal b * ofReal c = ofReal d` from real arithmetic.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ofReal_mul_mul_eq {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * b * c = d) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c = ENNReal.ofReal d := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb), h]

/-! ### T10: Prop 4.7 refuted -/

/-- A PMF on `Bool` with `true ↦ p`, `false ↦ 1 − p`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def pmfBool (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => match b with
    | true => ENNReal.ofReal p
    | false => ENNReal.ofReal (1 - p))
    (by
      rw [Fintype.sum_bool]
      show ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1
      rw [← ENNReal.ofReal_add h0 (by linarith), add_sub_cancel, ENNReal.ofReal_one])

/-- `pmfBool` at `true`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pmfBool_true (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : pmfBool p h0 h1 true = ENNReal.ofReal p :=
  rfl

/-- `pmfBool` at `false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pmfBool_false (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    pmfBool p h0 h1 false = ENNReal.ofReal (1 - p) :=
  rfl

/-- The uniform distribution on `Bool`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def unifB : PMF Bool := pmfBool (1/2) (by norm_num) (by norm_num)

/-- The identification `Bool → Fin 2`, `true ↦ 1`, `false ↦ 0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def boolToFin2 : Bool → Fin 2 := fun b => bif b then 1 else 0

/-- Prop 4.7's refutation common information: `Ω = Fin 2`, `Ω′ = Bool`, `C = Fin 2`, `c = id`,
`c′ = boolToFin2` (two ontologies, a bijective translation).
Source: mandate T10 (refutation)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ci10 : CommonInfo (Fin 2) Bool := { C := Fin 2, c := id, c' := boolToFin2 }

/-- Prop 4.7's refutation kernels: `κ₀ = (true ↦ 3/4, false ↦ 1/4)`, `κ₁ = (true ↦ 1/4, false ↦ 3/4)`.
Source: mandate T10 (refutation)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def kappa10 : Fin 2 → PMF Bool :=
  ![pmfBool (3/4) (by norm_num) (by norm_num), pmfBool (1/4) (by norm_num) (by norm_num)]

/-- Prop 4.7's refutation anticipation structure: `A = Fin 2`, `a = id`, kernels `kappa10`.
Source: mandate T10 (refutation)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def as10 : AnticipationStructure unif2 Bool := { A := Fin 2, a := id, κ := kappa10 }

/-- `C₂ = (1/2, 1/2)`: the shared-language image of the uniform `Bool` is uniform on `Fin 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem ci10_C₂ (y : Fin 2) : ci10.C₂ unifB y = ENNReal.ofReal (1/2) := by
  rw [ci10.C₂_apply]
  show mass unifB (boolToFin2 ⁻¹' {y}) = _
  rw [mass_fintype, Fintype.sum_bool]
  fin_cases y <;>
    simp only [indicator_apply, mem_preimage, mem_singleton_iff, boolToFin2, Fin.zero_eta,
      Fin.mk_one, Bool.cond_true, Bool.cond_false, Fin.isValue, one_ne_zero, zero_ne_one,
      ite_true, ite_false, unifB, pmfBool_true, pmfBool_false, add_zero, zero_add] <;>
    (congr 1; norm_num)

/-- `unif2` is `1/2` everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem unif2_apply (x : Fin 2) : unif2 x = ENNReal.ofReal (1/2) := by
  fin_cases x <;> rfl

/-- The prior-predictive of `as10` is uniform on `Bool`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem as10_priorPredictive : as10.priorPredictive = unifB := by
  refine PMF.ext fun b => ?_
  rw [AnticipationStructure.priorPredictive_apply]
  show ∑' ā : Fin 2, (unif2.map id) ā * kappa10 ā b = unifB b
  rw [PMF.map_id, tsum_fintype, Fin.sum_univ_two]
  cases b <;>
  · simp only [unif2, pmfOfReal_apply, Matrix.cons_val, kappa10, pmfBool_true, pmfBool_false,
      unifB]
    exact ofReal_mul_add_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `as10` is not `Ĉ`-calibrated: at atom `0` and shared proposition `0`,
`P(0) = 1/2 ≠ κ₀(false) · P(0) = 1/8`.
Source: mandate T10 (refutation)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem as10_not_bridgeCalibrated : ¬ BridgeCalibrated as10 ci10 := by
  intro h
  have := h (0 : Fin 2) (0 : Fin 2)
  change mass unif2 ((id : Fin 2 → Fin 2) ⁻¹' {0} ∩ (id : Fin 2 → Fin 2) ⁻¹' {0}) =
    mass (kappa10 0) (boolToFin2 ⁻¹' {0}) * (unif2.map id) 0 at this
  rw [preimage_id, inter_self, mass_singleton, PMF.map_id, mass_fintype, Fintype.sum_bool] at this
  simp only [indicator_apply, mem_preimage, mem_singleton_iff, boolToFin2, Bool.cond_true,
    Bool.cond_false, Fin.isValue, one_ne_zero, ite_true, ite_false, unif2, pmfOfReal_apply,
    Matrix.cons_val, kappa10, pmfBool_false, zero_add] at this
  rw [ofReal_mul_eq (by norm_num) rfl] at this
  exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) this

/-- **SC Prop 4.7 as stated is refuted (N+):** for `as10`/`ci10`/`unifB` both D–Z conditions hold
with `B = 1` (`C′ = C`, `P′ = Q₀`), the anticipation is not `Ĉ`-calibrated, and no `Ĉ`-compatible
calibrated conditioning model exists.
Source: [[superconditioning-mismatched-ontologies]] §4.5 Prop 4.7 ("The combined constraint still
does not restrict achievable posteriors beyond `C′ ≪ C` with bounded density … and `P′ ≪ Q₀` with
bounded density") | udt-rep-060
Kind: N+
Fidelity: n/a (refutation instance; `|A| = 2`, non-degenerate kernels, two ontologies; the
common information is *full* — `c = id`, `c′` bijective — so this instance shows the failure at
the full-information corner only; the general obstruction is
`not_compatible_calibrated_of_not_bridgeCalibrated`, which covers partial common information)
Hyps: (a) -/
theorem prop47_refuted :
    BoundedDensity (ci10.C₂ unifB) (ci10.C₁ unif2) 1 ∧
      BoundedDensity unifB as10.priorPredictive 1 ∧
      ¬ BridgeCalibrated as10 ci10 ∧
      ¬ ∃ m : CondModel unif2 unifB, Compatible m ci10 ∧ CMCalibrated m as10 := by
  refine ⟨?_, ?_, as10_not_bridgeCalibrated,
    not_compatible_calibrated_of_not_bridgeCalibrated as10 ci10 as10_not_bridgeCalibrated⟩
  · show ∀ y : Fin 2, ci10.C₂ unifB y ≤ 1 * ci10.C₁ unif2 y
    intro y
    have hC₁ : ci10.C₁ unif2 = unif2 := PMF.map_id unif2
    rw [ci10_C₂, hC₁, one_mul]
    exact le_of_eq (unif2_apply y).symm
  · rw [as10_priorPredictive]; exact boundedDensity_self unifB

/-! ### T10: `Ĉ`-calibration does not imply calibration -/

/-- The trivial common information on `Fin 2` with itself (`C = Unit`).
Source: mandate T10 (well-posedness note)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ciU : CommonInfo (Fin 2) (Fin 2) := { C := Unit, c := fun _ => (), c' := fun _ => () }

/-- The one-atom anticipation structure with kernel `δ₀` on the uniform `Fin 2`.
Source: mandate T10 (well-posedness note)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def asU : AnticipationStructure unif2 (Fin 2) :=
  { A := Unit, a := fun _ => (), κ := fun _ => PMF.pure 0 }

/-- **The trivial-`C` corner (N−):** `asU` is `Ĉ`-calibrated w.r.t. `ciU` and not calibrated —
but with `C = Unit` *every* anticipation structure is `Ĉ`-calibrated
(`bridgeCalibrated_trivialCI`), so the first conjunct is vacuous and this instance exercises
nothing of "`Ĉ`-calibration is weaker than calibration". Kept as the degenerate corner; the N+
witness is `bridgeCalibrated_not_calibrated` (`C = Bool`, `c = parity4`).
Source: [[superconditioning-mismatched-ontologies]] §5.2 ("weaker than full calibration") |
udt-rep-061 | audit r1 (adversarial B1)
Kind: N-
Fidelity: n/a (degenerate: trivial `C`, one atom)
Hyps: (a) -/
theorem bridgeCalibrated_not_calibrated_trivialCI :
    BridgeCalibrated asU ciU ∧ ¬ asU.Calibrated := by
  constructor
  · intro ā y
    cases ā
    cases y
    have h2 : (fun _ : Fin 2 => ()) ⁻¹' {()} = univ := eq_univ_of_forall fun _ => rfl
    change mass unif2 ((fun _ : Fin 2 => ()) ⁻¹' {()} ∩ (fun _ : Fin 2 => ()) ⁻¹' {()}) =
      mass (PMF.pure 0) ((fun _ : Fin 2 => ()) ⁻¹' {()}) * (unif2.map fun _ => ()) ()
    rw [h2, inter_self, mass_univ, mass_univ, map_apply_eq_mass, h2, mass_univ, one_mul]
  · intro h
    have := h () 1
    change mass unif2 ((fun _ : Fin 2 => ()) ⁻¹' {()} ∩ {1}) =
      (PMF.pure (0 : Fin 2)) 1 * (unif2.map fun _ => ()) () at this
    have h2 : (fun _ : Fin 2 => ()) ⁻¹' {()} = univ := eq_univ_of_forall fun _ => rfl
    rw [h2, univ_inter, mass_singleton, PMF.pure_apply, if_neg one_ne_zero, zero_mul] at this
    simp only [unif2, pmfOfReal_apply, Matrix.cons_val] at this
    exact ofReal_ne_zero' (by norm_num) this

/-- `C = Bool`, `c = c′ = parity4` on `Fin 4`: non-constant, non-injective common information on
SC's own carrier.
Source: mandate T10 (well-posedness note) | audit r1 (adversarial B1, probe B)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ciPar : CommonInfo (Fin 4) (Fin 4) := { C := Bool, c := parity4, c' := parity4 }

/-- Point-mass kernels `κ_false = δ₀`, `κ_true = δ₁`.
Source: mandate T10 (well-posedness note) | audit r1 (adversarial B1, probe B)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def kappaPar : Bool → PMF (Fin 4)
  | false => PMF.pure 0
  | true => PMF.pure 1

/-- The two-atom anticipation structure `a = parity4` with point-mass kernels on `unif4`.
Source: mandate T10 (well-posedness note) | audit r1 (adversarial B1, probe B)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def asPar : AnticipationStructure unif4 (Fin 4) :=
  { A := Bool, a := parity4, κ := kappaPar }

/-- The two parity classes are disjoint.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem parity4_preimage_inter_ne :
    parity4 ⁻¹' {false} ∩ parity4 ⁻¹' {true} = ∅ := by
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
    not_and]
  intro h1 h2
  exact Bool.false_ne_true (h1.symm.trans h2)

/-- The four `Ĉ`-calibration cases of `asPar`/`ciPar`, stated over `Bool` directly.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem asPar_bridge_cases (ā y : Bool) :
    mass unif4 (parity4 ⁻¹' {ā} ∩ parity4 ⁻¹' {y}) =
      mass (kappaPar ā) (parity4 ⁻¹' {y}) * (unif4.map parity4) ā := by
  rw [unif4_map_parity4]
  cases ā <;> cases y
  · rw [inter_self, ← map_apply_eq_mass, unif4_map_parity4]
    change _ = (PMF.pure (0 : Fin 4)).toOuterMeasure (parity4 ⁻¹' {false}) * _
    rw [PMF.toOuterMeasure_pure_apply, if_pos (show (0 : Fin 4) ∈ parity4 ⁻¹' {false} from rfl),
      one_mul]
  · rw [parity4_preimage_inter_ne, mass_empty]
    change 0 = (PMF.pure (0 : Fin 4)).toOuterMeasure (parity4 ⁻¹' {true}) * _
    rw [PMF.toOuterMeasure_pure_apply,
      if_neg (show (0 : Fin 4) ∉ parity4 ⁻¹' {true} from Bool.false_ne_true), zero_mul]
  · rw [inter_comm, parity4_preimage_inter_ne, mass_empty]
    change 0 = (PMF.pure (1 : Fin 4)).toOuterMeasure (parity4 ⁻¹' {false}) * _
    rw [PMF.toOuterMeasure_pure_apply,
      if_neg (show (1 : Fin 4) ∉ parity4 ⁻¹' {false} from fun h => Bool.false_ne_true h.symm),
      zero_mul]
  · rw [inter_self, ← map_apply_eq_mass, unif4_map_parity4]
    change _ = (PMF.pure (1 : Fin 4)).toOuterMeasure (parity4 ⁻¹' {true}) * _
    rw [PMF.toOuterMeasure_pure_apply, if_pos (show (1 : Fin 4) ∈ parity4 ⁻¹' {true} from rfl),
      one_mul]

/-- `asPar` is not calibrated: atom `false`, point `2`: `P({2}) = 1/4 ≠ δ₀(2) · P(false) = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem asPar_not_calibrated : ¬ asPar.Calibrated := by
  intro h
  have := h false 2
  change mass unif4 (parity4 ⁻¹' {false} ∩ {2}) =
    (PMF.pure (0 : Fin 4)) 2 * (unif4.map parity4) false at this
  rw [mass_inter_singleton, indicator_of_mem (show (2 : Fin 4) ∈ parity4 ⁻¹' {false} from rfl),
    PMF.pure_apply, if_neg (by decide), zero_mul] at this
  simp only [unif4, pmfOfReal_apply, Matrix.cons_val] at this
  exact ofReal_ne_zero' (by norm_num) this

/-- Under `ciPar`, SC's Prop 3.8 structure `as38` is *not* `Ĉ`-calibrated: at `(false, false)`,
`P(parity⁻¹ false) = 1/2` while `κ_false(parity⁻¹ false) · P(false) = (1/2 + 1/4) · 1/2 = 3/8`.
So `Ĉ`-calibration w.r.t. `ciPar` is a genuine constraint (unlike w.r.t. `ciU`).
Source: none: infrastructure (non-degeneracy check for `bridgeCalibrated_not_calibrated`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem as38_not_bridgeCalibrated : ¬ BridgeCalibrated as38 ciPar := by
  intro h
  have := h false false
  change mass unif4 (parity4 ⁻¹' {false} ∩ parity4 ⁻¹' {false}) =
    mass (kappa38 false) (parity4 ⁻¹' {false}) * (unif4.map parity4) false at this
  rw [inter_self, ← map_apply_eq_mass unif4 parity4 false, unif4_map_parity4, mass_fintype,
    Fin.sum_univ_four] at this
  simp only [indicator_apply, mem_preimage, mem_singleton_iff, parity4, Matrix.cons_val,
    Bool.true_eq_false, ite_true, ite_false, kappa38, pmfOfReal_apply, add_zero,
    Fin.isValue] at this
  rw [ofReal_add_eq (by norm_num) (by norm_num) rfl, ofReal_mul_eq (by norm_num) rfl] at this
  exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) this

/-- **`Ĉ`-calibration does not imply calibration (N+):** on SC's `Fin 4` carrier with `C = Bool`,
`c′ = c = parity4` (non-injective: `c 0 = c 2`; non-constant: `c 0 ≠ c 1`), the two-atom structure
with point-mass kernels is `Ĉ`-calibrated but not calibrated. Inhabits the full hypothesis package
of `Calibrated.bridgeCalibrated` (same ontology, `c′ = c`) and shows its converse fails; unlike
the trivial-`C` corner (`bridgeCalibrated_not_calibrated_trivialCI`, N−), the first conjunct is
not automatic here (`as38_not_bridgeCalibrated`: SC's Prop 3.8 structure fails it under `ciPar`
at `(false, false)`, `1/2 ≠ 3/8`).
Source: [[superconditioning-mismatched-ontologies]] §5.2 ("weaker than full calibration") |
udt-rep-061 | audit r1 (adversarial B1)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem bridgeCalibrated_not_calibrated :
    BridgeCalibrated asPar ciPar ∧ ¬ asPar.Calibrated ∧ ciPar.c' = ciPar.c ∧
      ciPar.c 0 = ciPar.c 2 ∧ ciPar.c 0 ≠ ciPar.c 1 :=
  ⟨fun ā y => asPar_bridge_cases ā y, asPar_not_calibrated, rfl, rfl,
    fun h => Bool.false_ne_true h⟩

/-! ### T13: the two strictness witnesses (on SC's Prop 3.8 structure) -/

/-- The `x`-dependent selection `S 0 = {false}`, `S 1 = {true}`, `S 2 = {false}`, `S 3 = ∅`.
Source: mandate T13 (witness: "an `S` varying with `x`")
Kind: D
Fidelity: n/a
Hyps: n/a -/
def sel13 : Fin 4 → Set Bool := ![{false}, {true}, {false}, ∅]

/-- The canonical posterior of `sel13`: `(2/5, 2/5, 1/5, 0)`.
Source: mandate T13 (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def post13 : PMF (Fin 4) :=
  pmfOfReal ![2/5, 2/5, 1/5, 0] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)

/-- The canonical weights of `sel13` are `(1/4, 1/4, 1/8, 0)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem canonicalWeight_sel13 (x : Fin 4) :
    canonicalWeight as38 sel13 x = ENNReal.ofReal (![1/4, 1/4, 1/8, 0] x) := by
  classical
  change ∑' ā : Bool, (sel13 x).indicator (fun ā => (unif4.map parity4) ā * kappa38 ā x) ā = _
  rw [tsum_fintype, Fintype.sum_bool]
  fin_cases x <;>
  · simp only [indicator_apply, sel13, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      mem_singleton_iff, mem_empty_iff_false, Bool.false_eq_true, Bool.true_eq_false, ite_true,
      ite_false, unif4_map_parity4, kappa38, pmfOfReal_apply, add_zero, zero_add]
    first
      | exact ofReal_mul_eq (by norm_num) (by norm_num)
      | exact ENNReal.ofReal_zero.symm

/-- The canonical total of `sel13` is `5/8`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem canonicalTotal_sel13 : canonicalTotal as38 sel13 = ENNReal.ofReal (5/8) := by
  rw [canonicalTotal, tsum_fintype, Fin.sum_univ_four]
  simp only [canonicalWeight_sel13, Matrix.cons_val, ENNReal.ofReal_zero, add_zero]
  rw [ofReal_add_eq (by norm_num) (by norm_num) rfl, ofReal_add_eq (by norm_num) (by norm_num) rfl]
  congr 1; norm_num

/-- **Jeffrey mixtures ⊊ canonical posteriors (N+):** `post13` is canonical (selection `sel13`) but
is no Jeffrey mixture, since every Jeffrey mixture puts positive mass on atom `3` while
`post13 3 = 0`.
Source: [[superconditioning-mismatched-ontologies]] §6.1 Prop 6.1 (first strictness) |
udt-rep-062
Kind: N+
Fidelity: n/a (`|A| = 2`, SC's own Prop 3.8 kernels)
Hyps: (a) -/
theorem canonical_not_jeffreyMixture_witness :
    post13 ∈ canonicalPosteriors as38 ∧ post13 ∉ JeffreyMixtures as38 := by
  constructor
  · refine ⟨sel13, by rw [canonicalTotal_sel13]; exact ENNReal.ofReal_pos.2 (by norm_num),
      fun x => ?_⟩
    rw [canonicalWeight_sel13, canonicalTotal_sel13, ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    fin_cases x <;>
    · simp only [post13, pmfOfReal_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      first
        | exact (ofReal_mul_eq (by norm_num) (by norm_num)).symm
        | (rw [ENNReal.ofReal_zero, zero_mul])
  · rintro ⟨T, ⟨ā₀, hā₀, hpos⟩, hP⟩
    have h3 := hP 3
    change post13 3 = (∑' ā : Bool, T.indicator (fun ā => (unif4.map parity4) ā * kappa38 ā 3) ā) *
      (mass (unif4.map parity4) T)⁻¹ at h3
    simp only [post13, pmfOfReal_apply, Matrix.cons_val, ENNReal.ofReal_zero] at h3
    rcases mul_eq_zero.1 h3.symm with h | h
    · rw [ENNReal.tsum_eq_zero] at h
      have := h ā₀
      rw [indicator_of_mem hā₀, unif4_map_parity4] at this
      rcases mul_eq_zero.1 this with h' | h'
      · exact ofReal_ne_zero' (by norm_num) h'
      · revert h'
        cases ā₀ <;>
        · simp only [kappa38, pmfOfReal_apply, Matrix.cons_val]
          exact ofReal_ne_zero' (by norm_num)
    · exact (ENNReal.inv_ne_zero.2 (mass_ne_top _ _)) h

/-- **The first strictness is robust to the reading of "Jeffrey":** `post13` is not a Jeffrey
update of `unif4` on the atoms of `parity4` in the general sense (`JeffreyOnA`) either, since a
Jeffrey update has a density constant on each atom while `post13 0 = 2/5 ≠ 1/5 = post13 2` with
`parity4 0 = parity4 2`. So SC Prop 6.1's first inclusion is strict whichever of `JeffreyMixtures`
(the mandate's reading) or `JeffreyOnA` "the Jeffrey posteriors" means — though the *inclusion*
itself holds only for `JeffreyMixtures` (see `JeffreyMixtures`'s docstring).
Source: [[superconditioning-mismatched-ontologies]] §6.1 Prop 6.1 (first strictness) | audit r1
(fidelity §3.7, probe 2)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem post13_not_jeffreyOnA : ¬ JeffreyOnA unif4 parity4 post13 := by
  intro h
  have hc := ((jeffreyOnA_iff_density_const unif4 post13 parity4).1 h).2 0 2 rfl
  simp only [post13, unif4, pmfOfReal_apply, Matrix.cons_val, Fin.isValue] at hc
  rw [ofReal_mul_eq (by norm_num) rfl, ofReal_mul_eq (by norm_num) rfl] at hc
  exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) hc

/-- The bounded-density posterior `(1/3, 2/3, 0, 0)` on `Fin 4`.
Source: mandate T13 (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def post13' : PMF (Fin 4) :=
  pmfOfReal ![1/3, 2/3, 0, 0] (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_four]; norm_num)

/-- **Canonical posteriors ⊊ Diaconis–Zabell (N+):** `post13′` has density `≤ 4` w.r.t. the uniform
prior but is not canonical: any canonical posterior positive at both `0` and `1` has
`P′ 0 = P′ 1` (their only available unnormalized weight is `P(false)·κ_{false}(0) =
P(true)·κ_{true}(1) = 1/4`), while `1/3 ≠ 2/3`.
Source: [[superconditioning-mismatched-ontologies]] §6.1 Prop 6.1 (second strictness) |
udt-rep-062
Kind: N+
Fidelity: n/a (`|A| = 2`, `|supp P| = 4 ≥ 2`, SC's own Prop 3.8 kernels)
Hyps: (a) -/
theorem dz_not_canonical_witness :
    post13' ∈ dzPosteriors unif4 ∧ post13' ∉ canonicalPosteriors as38 := by
  classical
  constructor
  · refine ⟨4, ENNReal.ofNat_ne_top, fun x => ?_⟩
    rw [← ENNReal.ofReal_ofNat 4]
    fin_cases x <;>
    · simp only [post13', unif4, pmfOfReal_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk]
      rw [ofReal_mul_eq (by norm_num) rfl]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
  · have key : ∀ S : Fin 4 → Set Bool, 0 < canonicalTotal as38 S →
        (∀ x, post13' x = canonicalWeight as38 S x * (canonicalTotal as38 S)⁻¹) → False := by
      intro S _ hP
      have h0 := hP 0
      have h1 := hP 1
      have e0 : canonicalWeight as38 S 0 = (S 0).indicator (fun _ => ENNReal.ofReal (1/4)) false := by
        change ∑' ā : Bool, (S 0).indicator (fun ā => (unif4.map parity4) ā * kappa38 ā 0) ā = _
        rw [tsum_fintype, Fintype.sum_bool]
        have ht : (S 0).indicator (fun ā => (unif4.map parity4) ā * kappa38 ā 0) true = 0 := by
          by_cases h : true ∈ S 0
          · rw [indicator_of_mem h]
            simp only [kappa38, pmfOfReal_apply, Matrix.cons_val, ENNReal.ofReal_zero, mul_zero]
          · rw [indicator_of_notMem h]
        rw [ht, zero_add]
        by_cases hf : false ∈ S 0
        · rw [indicator_of_mem hf, indicator_of_mem hf, unif4_map_parity4]
          simp only [kappa38, pmfOfReal_apply, Matrix.cons_val]
          exact ofReal_mul_eq (by norm_num) (by norm_num)
        · rw [indicator_of_notMem hf, indicator_of_notMem hf]
      have e1 : canonicalWeight as38 S 1 = (S 1).indicator (fun _ => ENNReal.ofReal (1/4)) true := by
        change ∑' ā : Bool, (S 1).indicator (fun ā => (unif4.map parity4) ā * kappa38 ā 1) ā = _
        rw [tsum_fintype, Fintype.sum_bool]
        have hf : (S 1).indicator (fun ā => (unif4.map parity4) ā * kappa38 ā 1) false = 0 := by
          by_cases h : false ∈ S 1
          · rw [indicator_of_mem h]
            simp only [kappa38, pmfOfReal_apply, Matrix.cons_val, ENNReal.ofReal_zero, mul_zero]
          · rw [indicator_of_notMem h]
        rw [hf, add_zero]
        by_cases ht : true ∈ S 1
        · rw [indicator_of_mem ht, indicator_of_mem ht, unif4_map_parity4]
          simp only [kappa38, pmfOfReal_apply, Matrix.cons_val]
          exact ofReal_mul_eq (by norm_num) (by norm_num)
        · rw [indicator_of_notMem ht, indicator_of_notMem ht]
      rw [e0] at h0
      rw [e1] at h1
      simp only [post13', pmfOfReal_apply, Matrix.cons_val] at h0 h1
      by_cases hf : false ∈ S 0
      · by_cases ht : true ∈ S 1
        · rw [indicator_of_mem hf] at h0
          rw [indicator_of_mem ht] at h1
          exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) (h0.trans h1.symm)
        · rw [indicator_of_notMem ht, zero_mul] at h1
          exact ofReal_ne_zero' (by norm_num) h1
      · rw [indicator_of_notMem hf, zero_mul] at h0
        exact ofReal_ne_zero' (by norm_num) h0
    rintro ⟨S, hS, hP⟩
    exact key S hS hP

end Cleanroom.Udt.UdtSupercondition
