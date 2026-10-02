import Cleanroom.Info.InfoVoiLatents.Hazard
import Cleanroom.Info.InfoVoiLatents.Eig
import Cleanroom.Info.InfoVoiLatents.MediationAssembly

/-!
# info-voi-latents — inert press: conditional laws and means in product form, and the Pinsker
clause in expectation (Target 9(e); repair round 2)

Audit r2 (fidelity item 5(a)) recorded that Target 9(e)'s conditional-means identity had a plan
but no attempt. This file proves it on the finite carrier, by the same route as Target 4(iv)'s
information form: `Eig.klFin_joint3_fact3_eq_condMutualInfo` renders `I[X : Pr | Z]` as the finite
KL of the joint cells `P(x, p, z)` against the factorised cells `P(x, z)·P(p, z)/P(z)`, and
`klFin_eq_zero_iff` turns `I = 0` into the cell-by-cell identity `P(x, p, z) = P(x, z)·P(p, z)/P(z)`
(`joint3_eq_fact3_of_condMutualInfo_eq_zero`).

* `condLaw μ X Z z := x ↦ P(x, z)/P(z)` and `condLaw2 μ X Pr Z z p := x ↦ P(x, p, z)/P(p, z)`: the
  conditional laws of the loss given `Z = z`, and given `Z = z, Pr = p` (junk `0` at null cells).
* **`condLaw2_eq_condLaw_of_inert`**: `I[X : Pr | Z] = 0` ⇒ at every positive-mass cell `(z, p)`,
  `condLaw2 z p = condLaw z` — the product form of conditional independence; hence
  **`condMean_eq_of_inert`**: `E[v ∘ X | Z = z, Pr = p] = E[v ∘ X | Z = z]` for every `v` (the
  conditional-means identity the mandate asks for).
* **`sum_klFin_condLaw_eq_condMutualInfo`**: the conditional KL decomposition
  `∑_{p,z} P(p, z)·klFin (condLaw2 z p) (condLaw z) = I[X : Pr | Z]` — `I` is the expected KL of the
  press-conditioned law of the loss against the press-free one.
* **`expected_mean_shift_le`**: the Pinsker clause in expectation,
  `∑_{p,z} P(p, z)·|E[v∘X | z, p] − E[v∘X | z]| ≤ 2B·√(I[X : Pr | Z]/2)` for `|v| ≤ B` — the
  mandate's `E_{z,p}[|…|] ≤ 2‖X‖_∞ √(I/2)`, from `Hazard.mean_shift_le_two_sup_mul_tv` on each cell
  and Pinsker + Jensen in expectation (`Mediation.sum_mul_tv_le_sqrt`).

Mandate: Target 9(e). What remains for Target 9: the Lévy limit (not stated; see `Hazard.lean`)
and the D6 witness (not attempted).
-/

namespace Cleanroom.Info.InfoVoiLatents.Hazard

open MeasureTheory ProbabilityTheory Finset
open Cleanroom.Info.InfoVoiLatents.Eig Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type*} {S T U : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype S] [Fintype T] [Fintype U] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  {X : Ω → S} {Pr : Ω → T} {Z : Ω → U}

/-! ### Conditional laws on the finite carrier -/

/-- **The conditional law of `X` given `Z = z`**, `x ↦ P(x, z) / P(z)` (junk `0` at a null `z`).
Source: [[d1-special-case-final]] S2(e) l. 48 (`E[X | Z = z]`); none: infrastructure
Kind: D
Fidelity: exact under `pm1 μ Z z ≠ 0` -/
def condLaw (μ : Measure Ω) (X : Ω → S) (Z : Ω → U) (z : U) : S → ℝ :=
  fun x => pm2 μ X Z x z / pm1 μ Z z

/-- **The conditional law of `X` given `Z = z` and `Pr = p`**, `x ↦ P(x, p, z) / P(p, z)` (junk `0`
at a null cell).
Source: [[d1-special-case-final]] S2(e) l. 48 (`E[X | Z = z, Pr = p]`); none: infrastructure
Kind: D
Fidelity: exact under `pm2 μ Pr Z p z ≠ 0` -/
def condLaw2 (μ : Measure Ω) (X : Ω → S) (Pr : Ω → T) (Z : Ω → U) (z : U) (p : T) : S → ℝ :=
  fun x => pm3 μ X Pr Z x p z / pm2 μ Pr Z p z

/-- `P(p, z) ≤ P(z)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm2_Pr_le_pm1 (p : T) (z : U) : pm2 μ Pr Z p z ≤ pm1 μ Z z :=
  measureReal_mono Set.inter_subset_right

/-- A positive-mass cell `(p, z)` sits over a positive-mass `z`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm1_ne_zero_of_pm2_ne_zero {p : T} {z : U} (hpz : pm2 μ Pr Z p z ≠ 0) :
    pm1 μ Z z ≠ 0 :=
  fun h0 => hpz (le_antisymm (h0 ▸ pm2_Pr_le_pm1 p z) (pm2_nonneg (μ := μ) Pr Z p z))

/-- The conditional law given `Z = z` is a distribution at a positive-mass `z`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condLaw_mem (hX : Measurable X) {z : U} (hz : pm1 μ Z z ≠ 0) :
    condLaw μ X Z z ∈ stdSimplex ℝ S := by
  refine ⟨fun x => div_nonneg (pm2_nonneg (μ := μ) X Z x z) (pm1_nonneg (μ := μ) Z z), ?_⟩
  unfold condLaw
  rw [← Finset.sum_div, sum_pm2_x hX z, div_self hz]

/-- The conditional law given `(Z, Pr) = (z, p)` is a distribution at a positive-mass cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condLaw2_mem (hX : Measurable X) {z : U} {p : T} (hpz : pm2 μ Pr Z p z ≠ 0) :
    condLaw2 μ X Pr Z z p ∈ stdSimplex ℝ S := by
  refine ⟨fun x => div_nonneg (pm3_nonneg (μ := μ) X Pr Z x p z) (pm2_nonneg (μ := μ) Pr Z p z),
    ?_⟩
  unfold condLaw2
  rw [← Finset.sum_div, sum_pm3_x hX p z, div_self hpz]

/-! ### Inert press in product form -/

/-- **`I[X : Pr | Z] = 0` ⇒ the joint law is the factorised law** cell by cell
(`klFin = 0 ↔ p = q` on the simplex under absolute continuity).
Source: [[d1-special-case-final]] S2(e) l. 48; none: infrastructure
Kind: P
Fidelity: exact -/
theorem joint3_eq_fact3_of_condMutualInfo_eq_zero (hX : Measurable X) (hPr : Measurable Pr)
    (hZ : Measurable Z) (h : I[X : Pr | Z ; μ] = 0) : joint3 μ X Pr Z = fact3 μ X Pr Z := by
  rw [← klFin_joint3_fact3_eq_condMutualInfo hX hPr hZ] at h
  exact (klFin_eq_zero_iff (joint3_mem hX hPr hZ) (fact3_mem hX hPr hZ)
    (absCont_joint3_fact3 X Pr Z)).1 h

/-- **(e) Inert press ⇒ the conditional law of the loss given the press equals the conditional
law given the agent's information alone** (product form): `I[X : Pr | Z] = 0` ⇒ at every
positive-mass cell `(z, p)`, `condLaw2 μ X Pr Z z p = condLaw μ X Z z`.
Source: [[d1-special-case-final]] S2(e) l. 48, P2(e) l. 80 ("conditional independence ⇒ conditional
means agree"); mandate Target 9(e)
Kind: P
Fidelity: exact (finite carrier, positive-mass cells)
Hyps: (a) all — `I[X : Pr | Z] = 0` is the claim's antecedent -/
theorem condLaw2_eq_condLaw_of_inert (hX : Measurable X) (hPr : Measurable Pr) (hZ : Measurable Z)
    (h : I[X : Pr | Z ; μ] = 0) {z : U} {p : T} (hpz : pm2 μ Pr Z p z ≠ 0) :
    condLaw2 μ X Pr Z z p = condLaw μ X Z z := by
  have hf := joint3_eq_fact3_of_condMutualInfo_eq_zero hX hPr hZ h
  funext x
  have hx := congrFun hf (x, p, z)
  simp only [joint3, fact3] at hx
  unfold condLaw2 condLaw
  rw [hx, div_div, mul_comm (pm1 μ Z z) (pm2 μ Pr Z p z), ← div_div,
    mul_div_cancel_right₀ _ hpz]

/-- **(e) Inert press ⇒ conditional means agree**: `I[X : Pr | Z] = 0` ⇒
`E[v ∘ X | Z = z, Pr = p] = E[v ∘ X | Z = z]` at every positive-mass cell, for every `v` (the
conditional-means identity in product form, the mandate's Target 9(e)).
Source: [[d1-special-case-final]] S2(e) l. 48, P2(e) l. 80; mandate Target 9(e)
Kind: C
Fidelity: exact (finite carrier, positive-mass cells)
Hyps: (a) all -/
theorem condMean_eq_of_inert (hX : Measurable X) (hPr : Measurable Pr) (hZ : Measurable Z)
    (h : I[X : Pr | Z ; μ] = 0) (v : S → ℝ) {z : U} {p : T} (hpz : pm2 μ Pr Z p z ≠ 0) :
    E (condLaw2 μ X Pr Z z p) v = E (condLaw μ X Z z) v := by
  rw [condLaw2_eq_condLaw_of_inert hX hPr hZ h hpz]

/-! ### The conditional KL decomposition and the Pinsker clause in expectation -/

/-- **The conditional KL decomposition**: `∑_{p,z} P(p, z)·klFin (condLaw2 z p) (condLaw z)
= I[X : Pr | Z ; μ]` — the conditional mutual information is the expected KL of the
press-conditioned law of the loss against the press-free one (null cells contribute `0`).
Source: [[d1-special-case-final]] P2(e) l. 80 ("via Target 2 on the fibres of `Z`"); none:
infrastructure
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem sum_klFin_condLaw_eq_condMutualInfo (hX : Measurable X) (hPr : Measurable Pr)
    (hZ : Measurable Z) :
    ∑ p, ∑ z, pm2 μ Pr Z p z * klFin (condLaw2 μ X Pr Z z p) (condLaw μ X Z z)
      = I[X : Pr | Z ; μ] := by
  rw [← klFin_joint3_fact3_eq_condMutualInfo hX hPr hZ]
  have hterm : ∀ x p z, pm2 μ Pr Z p z
      * (condLaw2 μ X Pr Z z p x * Real.log (condLaw2 μ X Pr Z z p x / condLaw μ X Z z x))
      = joint3 μ X Pr Z (x, p, z)
        * Real.log (joint3 μ X Pr Z (x, p, z) / fact3 μ X Pr Z (x, p, z)) := by
    intro x p z
    simp only [joint3, fact3, condLaw2, condLaw]
    by_cases hpz : pm2 μ Pr Z p z = 0
    · have h3 : pm3 μ X Pr Z x p z = 0 :=
        le_antisymm (hpz ▸ pm3_le_pm2_YZ X Pr Z x p z) (pm3_nonneg (μ := μ) X Pr Z x p z)
      rw [hpz, h3]
      simp
    · rw [← mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hpz]
      congr 2
      rw [div_div_div_comm, mul_div_assoc, div_div]
  unfold klFin
  rw [sum_prod3]
  calc ∑ p, ∑ z, pm2 μ Pr Z p z
        * ∑ x, condLaw2 μ X Pr Z z p x * Real.log (condLaw2 μ X Pr Z z p x / condLaw μ X Z z x)
      = ∑ p, ∑ z, ∑ x, joint3 μ X Pr Z (x, p, z)
          * Real.log (joint3 μ X Pr Z (x, p, z) / fact3 μ X Pr Z (x, p, z)) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => hterm x p z
    _ = ∑ p, ∑ x, ∑ z, joint3 μ X Pr Z (x, p, z)
          * Real.log (joint3 μ X Pr Z (x, p, z) / fact3 μ X Pr Z (x, p, z)) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ x, ∑ p, ∑ z, joint3 μ X Pr Z (x, p, z)
          * Real.log (joint3 μ X Pr Z (x, p, z) / fact3 μ X Pr Z (x, p, z)) := Finset.sum_comm

/-- The press-conditioned law is absolutely continuous with respect to the press-free one at a
positive-mass cell (a null `x` under `Z = z` is null under `(Z, Pr) = (z, p)`).
Source: none: infrastructure (findings F10: the `AbsCont` Pinsker needs)
Kind: L
Fidelity: n/a -/
theorem absCont_condLaw2_condLaw {z : U} {p : T} (hpz : pm2 μ Pr Z p z ≠ 0) :
    AbsCont (condLaw2 μ X Pr Z z p) (condLaw μ X Z z) := by
  intro x hx
  have hz : pm1 μ Z z ≠ 0 := pm1_ne_zero_of_pm2_ne_zero hpz
  unfold condLaw at hx
  rw [div_eq_zero_iff] at hx
  rcases hx with hx | hx
  · unfold condLaw2
    rw [le_antisymm (hx ▸ pm3_le_pm2_XZ X Pr Z x p z) (pm3_nonneg (μ := μ) X Pr Z x p z), zero_div]
  · exact absurd hx hz

/-- The joint weight `(p, z) ↦ P(p, z)` is in the simplex on `T × U`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm2_Pr_Z_mem (hPr : Measurable Pr) (hZ : Measurable Z) :
    (fun q : T × U => pm2 μ Pr Z q.1 q.2) ∈ stdSimplex ℝ (T × U) := by
  refine ⟨fun q => pm2_nonneg (μ := μ) Pr Z q.1 q.2, ?_⟩
  rw [Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_comm]
  calc ∑ z, ∑ p, pm2 μ Pr Z p z = ∑ z, pm1 μ Z z := Finset.sum_congr rfl fun z _ => sum_pm2_x hPr z
    _ = 1 := sum_pm1 hZ

/-- **(e), the Pinsker clause in expectation**: for a bounded `v` (`|v| ≤ B`, `0 ≤ B`),
`∑_{p,z} P(p, z)·|E[v∘X | Z = z, Pr = p] − E[v∘X | Z = z]| ≤ 2B·√(I[X : Pr | Z ; μ]/2)` — the
mandate's `E_{z,p}[|…|] ≤ 2‖X‖_∞ √(I/2)`: `mean_shift_le_two_sup_mul_tv` on each positive-mass
cell, then Pinsker + Jensen in expectation (`Mediation.sum_mul_tv_le_sqrt`) and the conditional KL
decomposition. (The `2B` is the note's crude constant; the range form `M·tv` of
`Voi.E_sub_E_le_mul_tv` is sharper.)
Source: [[d1-special-case-final]] S2(e) l. 48, P2(e) l. 80 ("`E_{z,p}[|…|] ≤ 2‖X‖_∞ √(I[X : Pr | Z]/2)`");
mandate Target 9(e)
Kind: C
Fidelity: exact (finite carrier; the expectation is over the joint law of `(Pr, Z)`)
Hyps: (a) all — `hB` the bound on `v`, `hB0 : 0 ≤ B` (implied by `hB` on a nonempty carrier, kept
explicit) -/
theorem expected_mean_shift_le (hX : Measurable X) (hPr : Measurable Pr) (hZ : Measurable Z)
    {v : S → ℝ} {B : ℝ} (hB : ∀ x, |v x| ≤ B) (hB0 : 0 ≤ B) :
    ∑ p, ∑ z, pm2 μ Pr Z p z * |E (condLaw2 μ X Pr Z z p) v - E (condLaw μ X Z z) v|
      ≤ 2 * B * Real.sqrt (I[X : Pr | Z ; μ] / 2) := by
  have hpt : ∀ p z, pm2 μ Pr Z p z * |E (condLaw2 μ X Pr Z z p) v - E (condLaw μ X Z z) v|
      ≤ pm2 μ Pr Z p z * (2 * B * tv (condLaw2 μ X Pr Z z p) (condLaw μ X Z z)) := by
    intro p z
    by_cases hpz : pm2 μ Pr Z p z = 0
    · rw [hpz, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left
        (mean_shift_le_two_sup_mul_tv (condLaw2_mem hX hpz)
          (condLaw_mem hX (pm1_ne_zero_of_pm2_ne_zero hpz)) hB)
        (pm2_nonneg (μ := μ) Pr Z p z)
  calc ∑ p, ∑ z, pm2 μ Pr Z p z * |E (condLaw2 μ X Pr Z z p) v - E (condLaw μ X Z z) v|
      ≤ ∑ p, ∑ z, pm2 μ Pr Z p z * (2 * B * tv (condLaw2 μ X Pr Z z p) (condLaw μ X Z z)) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun z _ => hpt p z
    _ = 2 * B * ∑ q : T × U, pm2 μ Pr Z q.1 q.2
          * tv (condLaw2 μ X Pr Z q.2 q.1) (condLaw μ X Z q.2) := by
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ 2 * B * Real.sqrt ((∑ q : T × U, pm2 μ Pr Z q.1 q.2
          * klFin (condLaw2 μ X Pr Z q.2 q.1) (condLaw μ X Z q.2)) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hB0)
        exact Mediation.sum_mul_tv_le_sqrt (pm2_Pr_Z_mem hPr hZ)
          (p := fun q : T × U => condLaw2 μ X Pr Z q.2 q.1) (q := fun q => condLaw μ X Z q.2)
          (fun q hq => condLaw2_mem hX hq)
          (fun q hq => condLaw_mem hX (pm1_ne_zero_of_pm2_ne_zero hq))
          (fun q hq => absCont_condLaw2_condLaw hq)
    _ = 2 * B * Real.sqrt (I[X : Pr | Z ; μ] / 2) := by
        rw [Fintype.sum_prod_type]
        simp only
        rw [sum_klFin_condLaw_eq_condMutualInfo hX hPr hZ]

end

end Cleanroom.Info.InfoVoiLatents.Hazard
