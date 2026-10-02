import Cleanroom.Udt.UdtSupercondition.Witnesses
import Cleanroom.Udt.UdtSupercondition.Landscape
import Cleanroom.Udt.UdtSupercondition.WitnessesB
import Cleanroom.Udt.UdtSupercondition.WitnessCountable
import Cleanroom.Udt.UdtSupercondition.Coherence

/-!
# udt-supercondition — audit round 2, adversarial lens: probes

Evidence for [[udt-supercondition-audit-r2-adversarial]]. **Not imported by the library.**

* Probe A (`prop47_refuted_partialC`): SC Prop 4.7 refuted with *partial* common information
  (`C = Bool`, `c = c′ = parity4`, both non-injective) on SC's own Prop 3.8 structure `as38`:
  both D–Z conditions hold with `B = 1`, `as38` is not `Ĉ`-calibrated, no compatible calibrated
  model. Closes the package's "Not done" item (the library's `prop47_refuted` is at the
  full-common-information corner).
* Probe B (`compatible_calibrated_witness_partialC`): a non-degenerate inhabitant of the
  *positive* direction of T10 (`compatible_calibrated_iff_bridgeCalibrated`), which the ledger
  witnesses only by the construction `bridgeModel`: cross-ontology (`Fin 4 → Fin 3`), partial
  common information (`ci4`, both translations non-injective), `|A| = 2` with non-deterministic
  kernels, `B = 4/3 > 1`, `P′ ≠ Q₀`. Graded N+ by the auditor.
* Probe C (`crossCoherentVia_not_calibratedModel`, `crossCoherentVia_iff_of_bridgeCalibrated`,
  `coherentVia_eq_kappa`, `compatible_of_bridgeCalibrated_kappa`): SC Def 12.2's clause (2)
  never mentions the *measure* `Xⱼ` (only the space), so even the fixed-structure
  `CrossCoherentVia ci Xi Xj as` (i) is strictly weaker than "a compatible model calibrated
  w.r.t. `as` exists", (ii) once `as` is `Ĉ`-calibrated depends on `Xⱼ` only through Thm 2.4's
  condition — unlike `CoherentVia as Xj`, which forces `Xⱼ = κ_{ā₀}` — and (iii) the natural
  Def 12.1-style analogue "`as` is `Ĉ`-calibrated and `Xⱼ = κ_{ā₀}` at a positive atom" already
  implies clause (1), so the repaired definition needs no clause (1) at all.
* Probe D (`not_thinningClosed_eq`): the predicate `P′ = P` is not thinning-closed (the ledger
  cites "audit r1 checks" in prose for this; here it is Lean).
* Probe E (`canonicalWeight_condAnticipation`, `pure0_canonical_not_jeffreyMixture_cal`,
  `post13'_not_canonical_cal`): Prop 6.1's two strictness instances on the *calibrated*
  structure `condAnticipation unif4 parity4` (SC's literal "measure determined by calibration"
  reading), where the canonical weight at `x` is `P x · 𝟙[a x ∈ S x]`; the library's witnesses
  live on the reflective, non-calibrated `as38` and the round-1 audits checked this case by hand.
-/

namespace Cleanroom.Udt.UdtSupercondition.AuditR2

open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Set

/-! ### Probe A: Prop 4.7 refuted with partial common information -/

/-- SC Prop 4.7 fails on SC's own Prop 3.8 structure with the parity common information:
both D–Z conditions hold with `B = 1` (`C′ = C`, `P′ = Q₀ = P` by reflection), `as38` is not
`Ĉ`-calibrated (library `as38_not_bridgeCalibrated`, at `(false, false)`: `1/2 ≠ 3/8`), and no
`Ĉ`-compatible calibrated model exists. `c = c′ = parity4` is non-injective and non-constant. -/
theorem prop47_refuted_partialC :
    BoundedDensity (ciPar.C₂ unif4) (ciPar.C₁ unif4) 1 ∧
      BoundedDensity unif4 as38.priorPredictive 1 ∧
      ¬ BridgeCalibrated as38 ciPar ∧
      ¬ ∃ m : CondModel unif4 unif4, Compatible m ciPar ∧ CMCalibrated m as38 := by
  have hR : as38.priorPredictive = unif4 := reflective_not_calibrated_witness.1
  refine ⟨?_, ?_, as38_not_bridgeCalibrated,
    not_compatible_calibrated_of_not_bridgeCalibrated as38 ciPar as38_not_bridgeCalibrated⟩
  · show BoundedDensity (unif4.map parity4) (unif4.map parity4) 1
    exact boundedDensity_self _
  · rw [hR]; exact boundedDensity_self _

/-! ### Probe B: T10's positive direction, inhabited non-degenerately -/

/-- Kernels on `Fin 3`: `κ_false = (1/2, 1/2, 0)`, `κ_true = (1/2, 0, 1/2)`. -/
noncomputable def kappaB : Bool → PMF (Fin 3)
  | false => pmfOfReal ![1/2, 1/2, 0] (by intro i; fin_cases i <;> norm_num)
      (by simp [Fin.sum_univ_three]; norm_num)
  | true => pmfOfReal ![1/2, 0, 1/2] (by intro i; fin_cases i <;> norm_num)
      (by simp [Fin.sum_univ_three]; norm_num)

/-- Two atoms (`parity4`) on the uniform `Fin 4`, targeting `Fin 3`. -/
noncomputable def asB : AnticipationStructure unif4 (Fin 3) :=
  { A := Bool, a := parity4, κ := kappaB }

/-- The four `Ĉ`-calibration cases of `asB` under `ci4` (`c = [x < 2]`, `c′ = (T, F, F)`):
`P(ā ∩ c⁻¹y) = 1/4 = κ_ā(c′⁻¹y) · P(ā) = (1/2)(1/2)` in every case. -/
theorem asB_bridge (ā y : Bool) :
    mass unif4 (parity4 ⁻¹' {ā} ∩ ci4.c ⁻¹' {y}) =
      mass (kappaB ā) (ci4.c' ⁻¹' {y}) * (unif4.map parity4) ā := by
  show mass unif4 (parity4 ⁻¹' {ā} ∩ (![true, true, false, false] : Fin 4 → Bool) ⁻¹' {y}) =
    mass (kappaB ā) ((![true, false, false] : Fin 3 → Bool) ⁻¹' {y}) * (unif4.map parity4) ā
  rw [unif4_map_parity4, mass_fintype, mass_fintype, Fin.sum_univ_four, Fin.sum_univ_three]
  cases ā <;> cases y <;>
  · simp only [indicator_apply, mem_inter_iff, mem_preimage, mem_singleton_iff, parity4,
      Matrix.cons_val, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false, and_self,
      ite_true, ite_false, unif4, kappaB, pmfOfReal_apply, ENNReal.ofReal_zero, add_zero, zero_add]
    simp (disch := norm_num) only [← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
    first | done | (congr 1; norm_num)

/-- `asB` is `Ĉ`-calibrated w.r.t. `ci4`. -/
theorem asB_bridgeCalibrated : BridgeCalibrated asB ci4 := fun ā y => asB_bridge ā y

/-- The prior-predictive of `asB` is `(1/2, 1/4, 1/4)`. -/
theorem asB_priorPredictive (q : Fin 3) :
    asB.priorPredictive q = ENNReal.ofReal (![1/2, 1/4, 1/4] q) := by
  rw [AnticipationStructure.priorPredictive_apply]
  show ∑' b : Bool, (unif4.map parity4) b * kappaB b q = _
  rw [tsum_fintype, Fintype.sum_bool, unif4_map_parity4, unif4_map_parity4]
  fin_cases q <;>
  · simp only [kappaB, pmfOfReal_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    exact ofReal_mul_add_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **T10 (⇐) inhabited (N+):** for `(unif4, post3)` with `ci4` and `asB`, a `Ĉ`-compatible
calibrated conditioning model exists with evidence mass `3/4` (`B = 4/3 > 1`); `post3 ≠ Q₀`;
both translations non-injective; two atoms with non-deterministic kernels. -/
theorem compatible_calibrated_witness_partialC :
    (∃ m : CondModel unif4 post3, Compatible m ci4 ∧ CMCalibrated m asB ∧
        mass m.μ m.ev = (ENNReal.ofReal (4/3))⁻¹) ∧
      BridgeCalibrated asB ci4 ∧ post3 ≠ asB.priorPredictive ∧ 1 < ENNReal.ofReal (4/3) ∧
      ci4.c 0 = ci4.c 1 ∧ ci4.c' 1 = ci4.c' 2 ∧ asB.a 0 = asB.a 2 ∧ asB.a 0 ≠ asB.a 1 := by
  have hbr : BridgeCalibrated asB ci4 := asB_bridgeCalibrated
  have hBD : BoundedDensity post3 asB.priorPredictive (ENNReal.ofReal (4/3)) := by
    intro q
    rw [asB_priorPredictive]
    fin_cases q <;>
    · simp only [post3, pmfOfReal_apply, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
      rw [ofReal_mul_eq (by norm_num) rfl]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
  refine ⟨⟨bridgeModel asB ci4 hbr ENNReal.ofReal_ne_top hBD,
    bridgeModel_compatible asB ci4 hbr ENNReal.ofReal_ne_top hBD,
    bridgeModel_cmCalibrated asB ci4 hbr ENNReal.ofReal_ne_top hBD,
    bridgeModel_mass_ev asB ci4 hbr ENNReal.ofReal_ne_top hBD⟩, hbr, ?_, ?_, rfl, rfl, rfl,
    fun h => Bool.false_ne_true h⟩
  · intro e
    have := congrFun (congrArg DFunLike.coe e) 0
    rw [asB_priorPredictive] at this
    simp only [post3, pmfOfReal_apply, Matrix.cons_val] at this
    exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) this
  · rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num

/-! ### Probe C: Def 12.2's clause (2) does not mention `Xⱼ` -/

/-- `CrossCoherentVia` holds for `(ciU, unif2, δ₁, asU)` although no compatible model
calibrated w.r.t. `asU` exists (`Q₀ = δ₀`, and `δ₁ ≪ δ₀` fails): the fixed-structure Def 12.2
is strictly weaker than `∃ m, Compatible m ci ∧ CMCalibrated m as`. -/
theorem crossCoherentVia_not_calibratedModel :
    CrossCoherentVia ciU unif2 (PMF.pure 1) asU ∧
      ¬ ∃ m : CondModel unif2 (PMF.pure 1), Compatible m ciU ∧ CMCalibrated m asU := by
  refine ⟨⟨⟨productModel unif2 (PMF.pure 1), funext fun _ => rfl⟩,
    bridgeCalibrated_not_calibrated_trivialCI.1⟩, ?_⟩
  rintro ⟨m, -, hc⟩
  have hB := hc.boundedDensity
  have hQ : asU.priorPredictive = PMF.pure 0 := by
    show (unif2.map fun _ => ()).bind (fun _ => PMF.pure 0) = PMF.pure 0
    exact PMF.bind_const _ _
  rw [hQ] at hB
  have h1 := hB 1
  rw [PMF.pure_apply, PMF.pure_apply, if_pos rfl, if_neg (by decide), mul_zero] at h1
  exact absurd h1 (not_le.2 (zero_lt_one : (0 : ℝ≥0∞) < 1))

/-- Once `as` is `Ĉ`-calibrated, `CrossCoherentVia ci Xi Xj as` depends on `Xⱼ` only through
the existence of a compatible model (Thm 2.4): the anticipation clause says nothing about
`Xⱼ`. Immediate from the definition — recorded because the docstring calls it "the
cross-ontology counterpart of `CoherentVia`". -/
theorem crossCoherentVia_iff_of_bridgeCalibrated {Ωi Ωj : Type} (ci : CommonInfo Ωi Ωj)
    (Xi : PMF Ωi) (as : AnticipationStructure Xi Ωj) (h : BridgeCalibrated as ci) (Xj : PMF Ωj) :
    CrossCoherentVia ci Xi Xj as ↔ ∃ m : CondModel Xi Xj, Compatible m ci :=
  ⟨fun h => h.1, fun hm => ⟨hm, h⟩⟩

/-- By contrast, same-ontology `CoherentVia as Xj` pins `Xⱼ` to an anticipated kernel:
`Xⱼ = κ_{ā₀}` for the atom `ā₀` (calibration turns `Xᵢ(· | ā₀)` into `κ_{ā₀}`). -/
theorem coherentVia_eq_kappa {Ω : Type} {Xi Xj : PMF Ω} {as : AnticipationStructure Xi Ω}
    (h : CoherentVia as Xj) : ∃ ā₀, Xj = as.κ ā₀ := by
  obtain ⟨hc, ā₀, hā₀, hXj⟩ := h
  exact ⟨ā₀, hXj.trans (hc.condOn_eq ā₀ hā₀)⟩

/-- The Def 12.1-style cross-ontology analogue — `as` is `Ĉ`-calibrated and `Xⱼ = κ_{ā₀}` at a
positive atom — already implies Def 12.2's clause (1): a compatible model for
`(Xᵢ, κ_{ā₀})` exists, with bound `1/Xᵢ(ā₀)`. So a repaired Def 12.2 needs only clause (2)
strengthened to name `Xⱼ`. -/
theorem compatible_of_bridgeCalibrated_kappa {Ωi Ωj : Type} [Countable Ωi] [Countable Ωj]
    (ci : CommonInfo Ωi Ωj) (Xi : PMF Ωi) (as : AnticipationStructure Xi Ωj)
    (h : BridgeCalibrated as ci) (ā₀ : as.A) (hā₀ : 0 < (Xi.map as.a) ā₀) :
    ∃ m : CondModel Xi (as.κ ā₀), Compatible m ci := by
  refine (commonInfo_condModel_iff ci Xi (as.κ ā₀)).2
    ⟨⟨((Xi.map as.a) ā₀)⁻¹, ENNReal.inv_ne_top.2 hā₀.ne', fun y => ?_⟩,
      fun y hy => h.range as ci y hy⟩
  rw [ci.C₂_apply, ci.C₁_apply]
  have e := h ā₀ y
  calc mass (as.κ ā₀) (ci.c' ⁻¹' {y})
      = mass (as.κ ā₀) (ci.c' ⁻¹' {y}) * (Xi.map as.a) ā₀ * ((Xi.map as.a) ā₀)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hā₀.ne' (PMF.apply_ne_top _ _), mul_one]
    _ = mass Xi (as.a ⁻¹' {ā₀} ∩ ci.c ⁻¹' {y}) * ((Xi.map as.a) ā₀)⁻¹ := by rw [e]
    _ ≤ mass Xi (ci.c ⁻¹' {y}) * ((Xi.map as.a) ā₀)⁻¹ :=
        mul_le_mul' (mass_mono _ inter_subset_right) le_rfl
    _ = ((Xi.map as.a) ā₀)⁻¹ * mass Xi (ci.c ⁻¹' {y}) := mul_comm _ _

/-! ### Probe D: `P′ = P` is not thinning-closed -/

/-- The weight `(1, 0)` on the trivial model of `unif2`. -/
def wD : Fin 2 → ℝ≥0∞ := ![1, 0]

/-- The predicate "the posterior is the prior" fails thinning-closure: thinning the trivial model
of `unif2` by `(1, 0)` has posterior `δ₀ ≠ unif2`. So `ThinningClosed` is not trivially true. -/
theorem not_thinningClosed_eq : ¬ ThinningClosed unif2 (fun P' _ => P' = unif2) := by
  intro h
  have hw0 : wD 0 = 1 := rfl
  have hw1 : wD 1 = 0 := rfl
  have hu0 : unif2 0 = ENNReal.ofReal (1/2) := rfl
  have hu1 : unif2 1 = ENNReal.ofReal (1/2) := rfl
  have hw : ∀ l, wD l ≤ 1 := Fin.forall_fin_two.2 ⟨le_of_eq hw0, by rw [hw1]; exact zero_le⟩
  have hden : (∑' l, (univ : Set (Fin 2)).indicator (fun l => wD l * unif2 l) l) =
      ENNReal.ofReal (1/2) := by
    rw [indicator_univ, tsum_fintype, Fin.sum_univ_two, hw0, hw1, hu0, one_mul, zero_mul, add_zero]
  have hnum : ∀ x : Fin 2, (∑' l, (id ⁻¹' {x} ∩ (univ : Set (Fin 2))).indicator
      (fun l => wD l * unif2 l) l) = wD x * unif2 x := by
    intro x
    rw [inter_univ, preimage_id, tsum_eq_single x]
    · exact indicator_of_mem (mem_singleton x) _
    · intro y hy; exact indicator_of_notMem (s := {x}) (a := y) hy _
  have hpos : 0 < ∑' l, (SameOntologyModel.trivial unif2).ev.indicator
      (fun l => wD l * (SameOntologyModel.trivial unif2).μ l) l := by
    show 0 < ∑' l, (univ : Set (Fin 2)).indicator (fun l => wD l * unif2 l) l
    rw [hden]; exact ENNReal.ofReal_pos.2 (by norm_num)
  have hP'' : ∀ x, (PMF.pure (0 : Fin 2)) x = thinPostFun (SameOntologyModel.trivial unif2).μ wD
      (SameOntologyModel.trivial unif2).ev (SameOntologyModel.trivial unif2).p x := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show PMF.pure (0 : Fin 2) 0 = (∑' l, (id ⁻¹' {(0 : Fin 2)} ∩ (univ : Set (Fin 2))).indicator
        (fun l => wD l * unif2 l) l) * (∑' l, (univ : Set (Fin 2)).indicator (fun l => wD l * unif2 l) l)⁻¹
      rw [hnum, hden, PMF.pure_apply, if_pos rfl, hw0, hu0, one_mul,
        ENNReal.mul_inv_cancel (ofReal_ne_zero' (by norm_num)) ENNReal.ofReal_ne_top]
    · show PMF.pure (0 : Fin 2) 1 = (∑' l, (id ⁻¹' {(1 : Fin 2)} ∩ (univ : Set (Fin 2))).indicator
        (fun l => wD l * unif2 l) l) * (∑' l, (univ : Set (Fin 2)).indicator (fun l => wD l * unif2 l) l)⁻¹
      rw [hnum, hden, PMF.pure_apply, if_neg (by decide), hw1, zero_mul, zero_mul]
  have := h unif2 (SameOntologyModel.trivial unif2) rfl wD hw hpos (PMF.pure 0) hP''
  have e := congrFun (congrArg DFunLike.coe this) 1
  rw [PMF.pure_apply, if_neg (by decide), hu1] at e
  exact ofReal_ne_zero' (by norm_num) e.symm

/-! ### Probe E: Prop 6.1's strictness on the calibrated structure -/

/-- Under the calibrated structure `condAnticipation P a`, the canonical weight at `x` is `P x`
if `a x ∈ S x` and `0` otherwise — SC's "measure determined by calibration" makes canonical
posteriors exactly the event conditionings (F4's observation, in Lean). -/
theorem canonicalWeight_condAnticipation {Ω A : Type} [Countable A] (P : PMF Ω) (a : Ω → A)
    (S : Ω → Set A) (x : Ω) :
    canonicalWeight (condAnticipation P a) S x = (S x).indicator (fun _ => P x) (a x) := by
  have e : (fun ā => (P.map a) ā * condKernel P a ā x) = fun ā => (a ⁻¹' {ā}).indicator P x := by
    funext ā
    rw [map_apply_eq_mass, mul_comm, condKernel_apply_mul]
  show ∑' ā, (S x).indicator (fun ā => (P.map a) ā * condKernel P a ā x) ā = _
  rw [e, tsum_eq_single (a x)]
  · by_cases h : a x ∈ S x
    · rw [indicator_of_mem h, indicator_of_mem h,
        indicator_of_mem (show x ∈ a ⁻¹' {a x} from rfl)]
    · rw [indicator_of_notMem h, indicator_of_notMem h]
  · intro ā hā
    by_cases h : ā ∈ S x
    · rw [indicator_of_mem h]
      exact indicator_of_notMem (s := a ⁻¹' {ā}) (a := x)
        (fun hx => hā (mem_singleton_iff.1 hx).symm) P
    · rw [indicator_of_notMem h]

/-- Case split over `Fin 4` with numerals. -/
theorem forall_fin4 {p : Fin 4 → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) (h3 : p 3) : ∀ x, p x := by
  intro x
  fin_cases x
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- The selection picking atom `false` at `0` only. -/
def selE : Fin 4 → Set Bool := ![{false}, ∅, ∅, ∅]

theorem cwE0 : canonicalWeight (condAnticipation unif4 parity4) selE 0 = ENNReal.ofReal (1/4) := by
  rw [canonicalWeight_condAnticipation, indicator_of_mem (show parity4 0 ∈ selE 0 from rfl)]; rfl

theorem cwE1 : canonicalWeight (condAnticipation unif4 parity4) selE 1 = 0 := by
  rw [canonicalWeight_condAnticipation, indicator_of_notMem (show parity4 1 ∉ selE 1 from fun h => h)]

theorem cwE2 : canonicalWeight (condAnticipation unif4 parity4) selE 2 = 0 := by
  rw [canonicalWeight_condAnticipation, indicator_of_notMem (show parity4 2 ∉ selE 2 from fun h => h)]

theorem cwE3 : canonicalWeight (condAnticipation unif4 parity4) selE 3 = 0 := by
  rw [canonicalWeight_condAnticipation, indicator_of_notMem (show parity4 3 ∉ selE 3 from fun h => h)]

theorem ctE : canonicalTotal (condAnticipation unif4 parity4) selE = ENNReal.ofReal (1/4) := by
  rw [canonicalTotal, tsum_fintype, Fin.sum_univ_four, cwE0, cwE1, cwE2, cwE3, add_zero, add_zero,
    add_zero]

/-- **Prop 6.1, first strictness, calibrated structure:** `δ₀` is a canonical posterior of
`condAnticipation unif4 parity4` (select atom `false` at `0` only) but no `κ`-mixture: every
mixture containing atom `false` is positive at `2`, and one without it vanishes at `0`. -/
theorem pure0_canonical_not_jeffreyMixture_cal :
    PMF.pure (0 : Fin 4) ∈ canonicalPosteriors (condAnticipation unif4 parity4) ∧
      PMF.pure (0 : Fin 4) ∉ JeffreyMixtures (condAnticipation unif4 parity4) := by
  have hu0 : unif4 0 = ENNReal.ofReal (1/4) := rfl
  have hu2 : unif4 2 = ENNReal.ofReal (1/4) := rfl
  constructor
  · refine ⟨selE, by rw [ctE]; exact ENNReal.ofReal_pos.2 (by norm_num), forall_fin4 ?_ ?_ ?_ ?_⟩
    · rw [ctE, cwE0, PMF.pure_apply, if_pos rfl,
        ENNReal.mul_inv_cancel (ofReal_ne_zero' (by norm_num)) ENNReal.ofReal_ne_top]
    · rw [ctE, cwE1, PMF.pure_apply, if_neg (by decide), zero_mul]
    · rw [ctE, cwE2, PMF.pure_apply, if_neg (by decide), zero_mul]
    · rw [ctE, cwE3, PMF.pure_apply, if_neg (by decide), zero_mul]
  · rintro ⟨T, -, hP⟩
    by_cases hT : false ∈ T
    · have h2 := hP 2
      change (PMF.pure (0 : Fin 4)) 2 =
        canonicalWeight (condAnticipation unif4 parity4) (fun _ => T) 2 *
          (mass (unif4.map parity4) T)⁻¹ at h2
      rw [canonicalWeight_condAnticipation, PMF.pure_apply, if_neg (by decide),
        indicator_of_mem (show parity4 2 ∈ T from hT)] at h2
      rw [hu2] at h2
      exact mul_ne_zero (ofReal_ne_zero' (by norm_num))
        (ENNReal.inv_ne_zero.2 (mass_ne_top _ _)) h2.symm
    · have h0 := hP 0
      change (PMF.pure (0 : Fin 4)) 0 =
        canonicalWeight (condAnticipation unif4 parity4) (fun _ => T) 0 *
          (mass (unif4.map parity4) T)⁻¹ at h0
      rw [canonicalWeight_condAnticipation, PMF.pure_apply, if_pos rfl,
        indicator_of_notMem (show parity4 0 ∉ T from hT), zero_mul] at h0
      exact one_ne_zero h0

/-- **Prop 6.1, second strictness, calibrated structure:** `(1/3, 2/3, 0, 0)` has bounded
density w.r.t. `unif4` (library `dz_not_canonical_witness.1`) but is not canonical for
`condAnticipation unif4 parity4`: canonical weights at `0` and `1` are each `0` or `1/4`, so a
canonical posterior positive at both has `P′ 0 = P′ 1`. -/
theorem post13'_not_canonical_cal :
    post13' ∈ dzPosteriors unif4 ∧
      post13' ∉ canonicalPosteriors (condAnticipation unif4 parity4) := by
  refine ⟨dz_not_canonical_witness.1, ?_⟩
  rintro ⟨S, -, hP⟩
  have h0 := hP 0
  have h1 := hP 1
  rw [canonicalWeight_condAnticipation] at h0 h1
  have hu0 : unif4 0 = ENNReal.ofReal (1/4) := rfl
  have hu1 : unif4 1 = ENNReal.ofReal (1/4) := rfl
  have hp0 : post13' 0 = ENNReal.ofReal (1/3) := rfl
  have hp1 : post13' 1 = ENNReal.ofReal (2/3) := rfl
  by_cases hS0 : parity4 0 ∈ S 0
  · by_cases hS1 : parity4 1 ∈ S 1
    · rw [indicator_of_mem hS0] at h0
      rw [indicator_of_mem hS1] at h1
      rw [hu0, hp0] at h0
      rw [hu1, hp1] at h1
      exact ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) (h0.trans h1.symm)
    · rw [indicator_of_notMem hS1, zero_mul, hp1] at h1
      exact ofReal_ne_zero' (by norm_num) h1
  · rw [indicator_of_notMem hS0, zero_mul, hp0] at h0
    exact ofReal_ne_zero' (by norm_num) h0

#print axioms Cleanroom.Udt.UdtSupercondition.AuditR2.not_thinningClosed_eq
#print axioms Cleanroom.Udt.UdtSupercondition.AuditR2.pure0_canonical_not_jeffreyMixture_cal
#print axioms Cleanroom.Udt.UdtSupercondition.AuditR2.post13'_not_canonical_cal
#print axioms Cleanroom.Udt.UdtSupercondition.AuditR2.prop47_refuted_partialC
#print axioms Cleanroom.Udt.UdtSupercondition.AuditR2.compatible_calibrated_witness_partialC
#print axioms Cleanroom.Udt.UdtSupercondition.AuditR2.crossCoherentVia_not_calibratedModel
#print axioms Cleanroom.Udt.UdtSupercondition.AuditR2.compatible_of_bridgeCalibrated_kappa

end Cleanroom.Udt.UdtSupercondition.AuditR2
