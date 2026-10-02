import ShannonInformation.API
import Cleanroom.Info.InfoVoiLatents.Finite

/-!
# info-voi-latents — the EIG identity and its mediation twin (Target 1)

Carrier (ii): a probability space `(Ω, μ)` and measurable variables `X Y Z` into finite types.
The **atom masses** `pm1`, `pm2`, `pm3` (`μ.real` of the preimage cells) express every entropy
as a finite sum (`entropy_eq_sum_pm1`, …) and marginalise by summing (`sum_pm3_z`, …).

* `klFin_joint3_fact3_eq_condMutualInfo`: **`KL(P[X,Y,Z] ‖ P[Z]·P[X|Z]·P[Y|Z]) = I[X : Y | Z ; μ]`**
  over PFR's `condMutualInfo`, with the factorised law `fact3` a genuine distribution
  (`fact3_mem`) and the joint absolutely continuous with respect to it (`absCont_joint3_fact3`),
  so `klFin` is not junk. One theorem, two instances:
  - `eig_eq_klFin` (S1's identity): `(X, Y, Z) = (Λ, X_k, X_{≤t})` —
    `KL(P[X_{≤t}, X_k, Λ] ‖ P[X_{≤t}] P[X_k | X_{≤t}] P[Λ | X_{≤t}]) = I[Λ : X_k | X_{≤t}] = EIG`;
  - `medErr_eq_klFin` (the mediation twin): `(X, Y, Z) = (X_{≤t}, X_k, Λ)`.
* `condEntropy_eq_eig_add`: the chain rule `H[X_k | X_{≤t}] = EIG + H[X_k | ⟨Λ, X_{≤t}⟩]` — S1's
  "estimable only given a noise model".
* Definitions of record `EIG`, `medErr`, `redErr'`, `NaturalOver` (D9, D10): the Lean shows
  `EIG` is one of Wentworth–Lorell's two redundancy errors and `NaturalOver` needs all three
  (findings F1).

Witnesses are in `EigWitness.lean`. Mandate: Target 1.
-/

namespace Cleanroom.Info.InfoVoiLatents.Eig

open MeasureTheory ProbabilityTheory Finset Real

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type*} {S T U : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype S] [Fintype T] [Fintype U] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]

/-! ### Atom masses -/

/-- The law of `X` at `x`, `μ(X = x)`, as a real.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def pm1 (μ : Measure Ω) (X : Ω → S) (x : S) : ℝ := μ.real (X ⁻¹' {x})

/-- The joint law of `(X, Y)` at `(x, y)`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def pm2 (μ : Measure Ω) (X : Ω → S) (Y : Ω → T) (x : S) (y : T) : ℝ :=
  μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y})

/-- The joint law of `(X, Y, Z)` at `(x, y, z)`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def pm3 (μ : Measure Ω) (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (x : S) (y : T) (z : U) : ℝ :=
  μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z})

/-- Summing a finite partition by the values of a measurable `Y` inside any set `A` recovers
`μ.real A`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_measureReal_inter_preimage {Y : Ω → T} (hY : Measurable Y) (A : Set Ω) :
    ∑ y, μ.real (A ∩ Y ⁻¹' {y}) = μ.real A := by
  have h := sum_measureReal_preimage_singleton (μ := μ.restrict A) (univ : Finset T) (f := Y)
    (fun y _ => hY (measurableSet_singleton y))
  simp only [coe_univ, Set.preimage_univ] at h
  rw [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  rw [← h]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [measureReal_restrict_apply (hY (measurableSet_singleton y)), Set.inter_comm]

/-- `∑ y, pm2 X Y x y = pm1 X x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_pm2_y {X : Ω → S} {Y : Ω → T} (hY : Measurable Y) (x : S) :
    ∑ y, pm2 μ X Y x y = pm1 μ X x :=
  sum_measureReal_inter_preimage hY _

/-- `∑ x, pm2 X Y x y = pm1 Y y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_pm2_x {X : Ω → S} {Y : Ω → T} (hX : Measurable X) (y : T) :
    ∑ x, pm2 μ X Y x y = pm1 μ Y y := by
  unfold pm2
  simp_rw [Set.inter_comm (X ⁻¹' _)]
  exact sum_measureReal_inter_preimage hX _

/-- `∑ z, pm3 X Y Z x y z = pm2 X Y x y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_pm3_z {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hZ : Measurable Z) (x : S) (y : T) :
    ∑ z, pm3 μ X Y Z x y z = pm2 μ X Y x y :=
  sum_measureReal_inter_preimage hZ _

/-- `∑ y, pm3 X Y Z x y z = pm2 X Z x z`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_pm3_y {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hY : Measurable Y) (x : S) (z : U) :
    ∑ y, pm3 μ X Y Z x y z = pm2 μ X Z x z := by
  unfold pm3 pm2
  have : ∀ y, X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z} = (X ⁻¹' {x} ∩ Z ⁻¹' {z}) ∩ Y ⁻¹' {y} := by
    intro y
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    tauto
  simp_rw [this]
  exact sum_measureReal_inter_preimage hY _

/-- `∑ x, pm3 X Y Z x y z = pm2 Y Z y z`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_pm3_x {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hX : Measurable X) (y : T) (z : U) :
    ∑ x, pm3 μ X Y Z x y z = pm2 μ Y Z y z := by
  unfold pm3 pm2
  have : ∀ x, X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z} = (Y ⁻¹' {y} ∩ Z ⁻¹' {z}) ∩ X ⁻¹' {x} := by
    intro x
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    tauto
  simp_rw [this]
  exact sum_measureReal_inter_preimage hX _

/-- `∑ x, pm1 X x = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_pm1 {X : Ω → S} (hX : Measurable X) : ∑ x, pm1 μ X x = 1 := by
  have := sum_measureReal_inter_preimage (μ := μ) hX Set.univ
  simp only [Set.univ_inter] at this
  unfold pm1
  rw [this, measureReal_def, measure_univ, ENNReal.toReal_one]

/-- `pm1_nonneg`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm1_nonneg (X : Ω → S) (x : S) : 0 ≤ pm1 μ X x := measureReal_nonneg
/-- `pm2_nonneg`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm2_nonneg (X : Ω → S) (Y : Ω → T) (x : S) (y : T) : 0 ≤ pm2 μ X Y x y := measureReal_nonneg
/-- `pm3_nonneg`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm3_nonneg (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (x : S) (y : T) (z : U) :
    0 ≤ pm3 μ X Y Z x y z := measureReal_nonneg

/-- `pm3 ≤ pm2 X Z`, `pm3 ≤ pm2 Y Z`, `pm3 ≤ pm1 Z`: cells shrink under intersection.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm3_le_pm2_XZ (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (x : S) (y : T) (z : U) :
    pm3 μ X Y Z x y z ≤ pm2 μ X Z x z :=
  measureReal_mono (fun ω hω => ⟨hω.1.1, hω.2⟩)

/-- `pm3_le_pm2_YZ`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm3_le_pm2_YZ (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (x : S) (y : T) (z : U) :
    pm3 μ X Y Z x y z ≤ pm2 μ Y Z y z :=
  measureReal_mono (fun ω hω => ⟨hω.1.2, hω.2⟩)

/-- `pm3_le_pm1_Z`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm3_le_pm1_Z (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (x : S) (y : T) (z : U) :
    pm3 μ X Y Z x y z ≤ pm1 μ Z z :=
  measureReal_mono (fun ω hω => hω.2)

/-! ### Entropies as finite sums -/

/-- `H[X ; μ] = ∑ x, negMulLog (pm1 X x)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_eq_sum_pm1 {X : Ω → S} (hX : Measurable X) :
    H[X ; μ] = ∑ x, negMulLog (pm1 μ X x) := by
  rw [ProbabilityTheory.entropy_eq_sum, tsum_fintype]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_measureReal_apply hX (measurableSet_singleton x)]
  rfl

/-- The preimage of a pair singleton is the intersection of the coordinate cells.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem preimage_pair_singleton (X : Ω → S) (Y : Ω → T) (x : S) (y : T) :
    (fun ω => (X ω, Y ω)) ⁻¹' {(x, y)} = X ⁻¹' {x} ∩ Y ⁻¹' {y} := by
  ext ω
  simp [Prod.ext_iff]

/-- `H[⟨X, Y⟩ ; μ] = ∑ x, ∑ y, negMulLog (pm2 X Y x y)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_pair_eq_sum_pm2 {X : Ω → S} {Y : Ω → T} (hX : Measurable X) (hY : Measurable Y) :
    H[(⟨X, Y⟩ : Ω → S × T) ; μ] = ∑ x, ∑ y, negMulLog (pm2 μ X Y x y) := by
  rw [ProbabilityTheory.entropy_eq_sum, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [map_measureReal_apply (hX.prodMk hY) (measurableSet_singleton (x, y)),
    preimage_pair_singleton]
  rfl

/-- `H[⟨X, ⟨Y, Z⟩⟩ ; μ] = ∑ x, ∑ y, ∑ z, negMulLog (pm3 X Y Z x y z)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem entropy_triple_eq_sum_pm3 {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) :
    H[(⟨X, ⟨Y, Z⟩⟩ : Ω → S × (T × U)) ; μ] = ∑ x, ∑ y, ∑ z, negMulLog (pm3 μ X Y Z x y z) := by
  rw [ProbabilityTheory.entropy_eq_sum, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  rw [map_measureReal_apply (hX.prodMk (hY.prodMk hZ)) (measurableSet_singleton (x, (y, z)))]
  unfold pm3
  congr 1
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff, Set.mem_inter_iff]
  tauto

/-! ### The joint and factorised laws on `S × T × U` -/

/-- The joint law of `(X, Y, Z)` as a vector on `S × T × U`.
Source: [[generalization-final]] S1 l. 59 (`P[X_{≤t}, X_k, Λ]`)
Kind: D
Fidelity: exact -/
def joint3 (μ : Measure Ω) (X : Ω → S) (Y : Ω → T) (Z : Ω → U) : S × T × U → ℝ :=
  fun p => pm3 μ X Y Z p.1 p.2.1 p.2.2

/-- The factorised law `P[Z] · P[X | Z] · P[Y | Z] = P[X, Z] · P[Y, Z] / P[Z]` on `S × T × U`
(junk `0` where `P[Z] = 0`, where the joint vanishes too).
Source: [[generalization-final]] S1 l. 59 (`P[X_{≤t}] P[X_k | X_{≤t}] P[Λ | X_{≤t}]` with
`Z = X_{≤t}`)
Kind: D
Fidelity: exact -/
def fact3 (μ : Measure Ω) (X : Ω → S) (Y : Ω → T) (Z : Ω → U) : S × T × U → ℝ :=
  fun p => pm2 μ X Z p.1 p.2.2 * pm2 μ Y Z p.2.1 p.2.2 / pm1 μ Z p.2.2

/-- A sum over `S × T × U` as a triple sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_prod3 (f : S × T × U → ℝ) : ∑ p, f p = ∑ x, ∑ y, ∑ z, f (x, y, z) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]

/-- The joint law is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem joint3_mem {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) : joint3 μ X Y Z ∈ stdSimplex ℝ (S × T × U) := by
  refine ⟨fun p => pm3_nonneg _ _ _ _ _ _, ?_⟩
  rw [sum_prod3]
  simp_rw [joint3, sum_pm3_z hZ, sum_pm2_y hY, sum_pm1 hX]

/-- **The factorised law is a genuine distribution**: nonnegative and summing to `1`.
Source: [[generalization-final]] S1 l. 59; Target 1 ("a genuine distribution: prove `∑ = 1` and
nonnegativity")
Kind: P
Fidelity: exact -/
theorem fact3_mem {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) : fact3 μ X Y Z ∈ stdSimplex ℝ (S × T × U) := by
  refine ⟨fun p => div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)
    measureReal_nonneg, ?_⟩
  rw [sum_prod3]
  simp only [fact3]
  have h1 : ∀ x z, ∑ y, pm2 μ X Z x z * pm2 μ Y Z y z / pm1 μ Z z
      = pm2 μ X Z x z * pm1 μ Z z / pm1 μ Z z := by
    intro x z
    rw [← sum_pm2_x hY z, Finset.mul_sum, Finset.sum_div]
  have h2 : ∀ z, ∑ x, pm2 μ X Z x z * pm1 μ Z z / pm1 μ Z z = pm1 μ Z z := by
    intro z
    rw [← Finset.sum_div, ← Finset.sum_mul, sum_pm2_x hX z]
    rcases (pm1_nonneg (μ := μ) Z z).lt_or_eq with h | h
    · exact mul_div_cancel_right₀ _ h.ne'
    · rw [← h]
      simp
  calc ∑ x, ∑ y, ∑ z, pm2 μ X Z x z * pm2 μ Y Z y z / pm1 μ Z z
      = ∑ x, ∑ z, ∑ y, pm2 μ X Z x z * pm2 μ Y Z y z / pm1 μ Z z := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_comm
    _ = ∑ z, ∑ x, pm2 μ X Z x z * pm1 μ Z z / pm1 μ Z z := by
        simp_rw [h1]
        exact Finset.sum_comm
    _ = ∑ z, pm1 μ Z z := Finset.sum_congr rfl fun z _ => h2 z
    _ = 1 := sum_pm1 hZ

/-- **The joint is absolutely continuous with respect to the factorised law**, so `klFin` is
not junk on any cell.
Source: none: infrastructure (Target 1, trap)
Kind: L
Fidelity: n/a -/
theorem absCont_joint3_fact3 (X : Ω → S) (Y : Ω → T) (Z : Ω → U) :
    AbsCont (joint3 μ X Y Z) (fact3 μ X Y Z) := by
  rintro ⟨x, y, z⟩ h
  simp only [fact3, joint3] at h ⊢
  rw [div_eq_zero_iff, mul_eq_zero] at h
  rcases h with (h | h) | h
  · exact le_antisymm (h ▸ pm3_le_pm2_XZ X Y Z x y z) (pm3_nonneg _ _ _ _ _ _)
  · exact le_antisymm (h ▸ pm3_le_pm2_YZ X Y Z x y z) (pm3_nonneg _ _ _ _ _ _)
  · exact le_antisymm (h ▸ pm3_le_pm1_Z X Y Z x y z) (pm3_nonneg _ _ _ _ _ _)

/-! ### The identity -/

/-- The per-cell log identity, junk-safe: with `J = pm3`, `a = pm2 X Z`, `b = pm2 Y Z`, `c = pm1 Z`,
`J · log (J / (a·b/c)) = −negMulLog J − J·log a − J·log b + J·log c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem eig_term (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (x : S) (y : T) (z : U) :
    pm3 μ X Y Z x y z * Real.log (pm3 μ X Y Z x y z / (pm2 μ X Z x z * pm2 μ Y Z y z / pm1 μ Z z))
      = -negMulLog (pm3 μ X Y Z x y z) - pm3 μ X Y Z x y z * Real.log (pm2 μ X Z x z)
        - pm3 μ X Y Z x y z * Real.log (pm2 μ Y Z y z)
        + pm3 μ X Y Z x y z * Real.log (pm1 μ Z z) := by
  rcases (pm3_nonneg (μ := μ) X Y Z x y z).lt_or_eq with hJ | hJ
  · have ha : 0 < pm2 μ X Z x z := lt_of_lt_of_le hJ (pm3_le_pm2_XZ X Y Z x y z)
    have hb : 0 < pm2 μ Y Z y z := lt_of_lt_of_le hJ (pm3_le_pm2_YZ X Y Z x y z)
    have hc : 0 < pm1 μ Z z := lt_of_lt_of_le hJ (pm3_le_pm1_Z X Y Z x y z)
    rw [Real.log_div hJ.ne' (by positivity), Real.log_div (by positivity) hc.ne',
      Real.log_mul ha.ne' hb.ne', negMulLog]
    ring
  · rw [← hJ]
    simp

/-- **`KL(P[X, Y, Z] ‖ P[Z]·P[X|Z]·P[Y|Z]) = I[X : Y | Z ; μ]`** over PFR's conditional mutual
information, for measurable variables into finite types on a probability space. The
factorised law is a genuine distribution (`fact3_mem`) and the joint is absolutely continuous
with respect to it (`absCont_joint3_fact3`), so `klFin` renders the divergence. Route:
`ShannonInformation.condMutualInfo_eq'` (`I[X : Y | Z] = H[X | Z] − H[X | ⟨Y, Z⟩]`), the chain rule
`chain_rule''`, the four entropies as sums of `negMulLog` over cells, marginalisation, and the
per-cell identity `eig_term`.
Source: [[generalization-final]] S1 l. 59, P1 l. 104 (the general form of both identities)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem klFin_joint3_fact3_eq_condMutualInfo {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    klFin (joint3 μ X Y Z) (fact3 μ X Y Z) = I[X : Y | Z ; μ] := by
  rw [ShannonInformation.condMutualInfo_eq' hX hY hZ μ, ShannonInformation.chain_rule'' μ hX hZ,
    ShannonInformation.chain_rule'' μ hX (hY.prodMk hZ), entropy_pair_eq_sum_pm2 hX hZ,
    entropy_eq_sum_pm1 hZ, entropy_triple_eq_sum_pm3 hX hY hZ, entropy_pair_eq_sum_pm2 hY hZ]
  unfold klFin
  rw [sum_prod3]
  simp only [joint3, fact3]
  simp_rw [eig_term (μ := μ) X Y Z]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  -- the three marginal-weighted sums
  have hA : ∑ x, ∑ y, ∑ z, pm3 μ X Y Z x y z * Real.log (pm2 μ X Z x z)
      = -∑ x, ∑ z, negMulLog (pm2 μ X Z x z) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_mul, sum_pm3_y hY]
    simp [negMulLog]
  have hB : ∑ x, ∑ y, ∑ z, pm3 μ X Y Z x y z * Real.log (pm2 μ Y Z y z)
      = -∑ y, ∑ z, negMulLog (pm2 μ Y Z y z) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_mul, sum_pm3_x hX]
    simp [negMulLog]
  have hC : ∑ x, ∑ y, ∑ z, pm3 μ X Y Z x y z * Real.log (pm1 μ Z z)
      = -∑ z, negMulLog (pm1 μ Z z) := by
    have : ∀ x, ∑ y, ∑ z, pm3 μ X Y Z x y z * Real.log (pm1 μ Z z)
        = ∑ z, (∑ y, pm3 μ X Y Z x y z) * Real.log (pm1 μ Z z) := by
      intro x
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => (Finset.sum_mul _ _ _).symm
    simp_rw [this, sum_pm3_y hY]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_mul, sum_pm2_x hX]
    simp [negMulLog]
  rw [hA, hB, hC]
  ring

/-! ### Definitions of record and the two instances -/

/-- **Expected information gain** of the unseen judgments `Xk` about the concept `Λ` given the
seen judgments `Xle`: `I[Λ : Xk | Xle ; μ]` (D10, renamed from "natural-latent coverage").
Source: [[generalization-final]] D10 l. 45
Kind: D
Fidelity: exact -/
def EIG (Λ : Ω → S) (Xk : Ω → T) (Xle : Ω → U) (μ : Measure Ω) : ℝ := I[Λ : Xk | Xle ; μ]

/-- **Mediation error** `I[Xle : Xk | Λ ; μ]` (D10's `ε_med`).
Source: [[generalization-final]] D10 l. 45
Kind: D
Fidelity: exact -/
def medErr (Xle : Ω → U) (Xk : Ω → T) (Λ : Ω → S) (μ : Measure Ω) : ℝ := I[Xle : Xk | Λ ; μ]

/-- **The other redundancy error** `I[Λ : Xle | Xk ; μ]` — the direction the develop file omitted
(the new chunk alone identifies the concept).
Source: [[generalization-final]] D10 l. 45; [[generalization-adversary]] A1.2 l. 28
Kind: D
Fidelity: exact -/
def redErr' (Λ : Ω → S) (Xle : Ω → U) (Xk : Ω → T) (μ : Measure Ω) : ℝ := I[Λ : Xle | Xk ; μ]

/-- **Wentworth–Lorell naturality over two chunks, exact form**: mediation and both redundancy
directions vanish. `EIG` alone is one redundancy error, not naturality (findings F1).
Source: [[generalization-final]] D9 l. 43, D10 l. 45
Kind: D
Fidelity: exact (the `ε = 0` form; the approximate conditions are Target 10(iii)) -/
def NaturalOver (Λ : Ω → S) (Xle : Ω → U) (Xk : Ω → T) (μ : Measure Ω) : Prop :=
  medErr Xle Xk Λ μ = 0 ∧ EIG Λ Xk Xle μ = 0 ∧ redErr' Λ Xle Xk μ = 0

/-- **S1, the EIG identity**: `KL(P[X_{≤t}, X_k, Λ] ‖ P[X_{≤t}] P[X_k | X_{≤t}] P[Λ | X_{≤t}])
= I[Λ : X_k | X_{≤t} ; μ] = EIG`. (`fact3 μ Λ Xk Xle = P[Λ, X_{≤t}] P[X_k, X_{≤t}] / P[X_{≤t}]`, the
note's factorisation with `X₁ = X_{≤t}`.)
Source: [[generalization-final]] S1 l. 59, P1 l. 104; [[generalization-adversary]] A1.1 l. 28;
items 125, 2-069(a)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem eig_eq_klFin {Λ : Ω → S} {Xk : Ω → T} {Xle : Ω → U} (hΛ : Measurable Λ)
    (hXk : Measurable Xk) (hXle : Measurable Xle) :
    klFin (joint3 μ Λ Xk Xle) (fact3 μ Λ Xk Xle) = EIG Λ Xk Xle μ :=
  klFin_joint3_fact3_eq_condMutualInfo hΛ hXk hXle

/-- **The mediation twin**: `KL(P[X_{≤t}, X_k, Λ] ‖ P[Λ] P[X_{≤t} | Λ] P[X_k | Λ]) = I[X_{≤t} : X_k | Λ ; μ]
= ε_med`.
Source: [[generalization-final]] S1 l. 59, P1 l. 104 ("likewise the mediation error is
`I(X₁; X₂ | Λ)`")
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem medErr_eq_klFin {Λ : Ω → S} {Xk : Ω → T} {Xle : Ω → U} (hΛ : Measurable Λ)
    (hXk : Measurable Xk) (hXle : Measurable Xle) :
    klFin (joint3 μ Xle Xk Λ) (fact3 μ Xle Xk Λ) = medErr Xle Xk Λ μ :=
  klFin_joint3_fact3_eq_condMutualInfo hXle hXk hΛ

/-- **The chain rule behind "estimable only given a noise model"**:
`H[X_k | X_{≤t}] = EIG + H[X_k | ⟨Λ, X_{≤t}⟩]` — the predictive surprise splits into the target and
the judgment noise given the concept.
Source: [[generalization-final]] S1 l. 59 (estimability), P1 l. 104; [[generalization-adversary]]
A1.3 l. 28
Kind: L
Fidelity: exact -/
theorem condEntropy_eq_eig_add {Λ : Ω → S} {Xk : Ω → T} {Xle : Ω → U} (hΛ : Measurable Λ)
    (hXk : Measurable Xk) (hXle : Measurable Xle) :
    H[Xk | Xle ; μ] = EIG Λ Xk Xle μ + H[Xk | (⟨Λ, Xle⟩ : Ω → S × U) ; μ] := by
  unfold EIG
  rw [condMutualInfo_comm hΛ hXk, ShannonInformation.condMutualInfo_eq' hXk hΛ hXle μ]
  ring

end

end Cleanroom.Info.InfoVoiLatents.Eig
