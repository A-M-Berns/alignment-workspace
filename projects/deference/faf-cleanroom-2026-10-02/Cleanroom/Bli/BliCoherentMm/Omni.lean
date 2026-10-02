import Cleanroom.Bli.BliCoherentMm.FixedPoint
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# `bli-coherent-mm` · Omni (reconciled; extension): T7, omni-traders — the infinite fixed point,
stated OPEN, with the finite-support reduction proved

Soto's PDF 05 "Omni-traders" asks whether the world-priced fixed point (T1) survives when the
trader may demand shares of **infinitely many** sentences at once, priced by a probability
measure on the **infinite** worlds. Neither attempt stated it in Lean (both for want of a test
of the `ProbabilityMeasure` import beside FAF's vendored PFR); the reconciler tested the import
(it elaborates; no clash) and states it here:

* `ConsistentWorlds D` — the `D`-consistent Boolean worlds `{v : ℕ → Bool | toPCWorld v ⊨ D}`,
  closed in the Cantor space (FAF's `isClosed_consistentWith` at a constant process), hence
  compact; `ProbabilityMeasure (ConsistentWorlds D)` carries Mathlib's topology of weak
  convergence (Borel σ-algebra, `MeasurableSingletonClass`).
* `omniPrice D μ φ` — the mass `μ` gives to `{w | w ⊨ φ}`; `omniBenefit D G μ v` — the ℓ¹
  benefit `∑' φ, G μ φ · (payout_v φ − omniPrice μ φ)` of the demand `G μ` in the world `v`.
* **`omni_fixed_point` (OPEN, `sorry`, listed in `bli-coherent-mm-open.txt`)**: for a weakly
  continuous demand with ℓ¹ norm uniformly bounded by `M`, is there `μ` with
  `omniBenefit D G μ v ≤ 0` for every `v ∈ ConsistentWorlds D`? Open question in Soto PDF 05.
* **`omni_fixed_point_of_finiteSupport` (proved, Kind P)** — the finite-support reduction
  the mandate asked for: if the demand vanishes off a fixed finite `S` and factors through
  the marginal of `μ` on the first `B` atoms (`omniMarginal`), the OPEN statement **holds**,
  by T1's abstract lemma on the finite simplex over `WD D B` and the Dirac mixture
  (`diracMixtureP`) realising the fixed point as a probability measure on the consistent
  worlds. So the open part of T7 is exactly the infinitely-supported case.

(ii)–(iv) of bli-soto-a-046 stay out ((iv) ill-posed per the plan).

Sources: [[bli-coherent-mm-mandate]] T7; Soto PDF 05 "Omni-traders" (bli-soto-a-046 (i)).
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay MeasureTheory

/-! ## The consistent Cantor worlds -/

/-- **The `D`-consistent Boolean worlds**: the Cantor-space presentation of `pcworlds(D)`.
Source: [[bli-coherent-mm-mandate]] T7 (`K`)
Kind: D
Fidelity: exact -/
def ConsistentWorlds (D : Finset Sentence) : Set BoolPCWorld :=
  {v | (toPCWorld v).ConsistentWith D}

/-- The constant deductive process at a finite stage (to apply FAF's closedness lemma, which is
stated for a process and a day).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def constProcess (D : Finset Sentence) : DeductiveProcess :=
  ⟨fun _ => D, fun _ => Finset.Subset.refl D⟩

/-- The consistent worlds form a closed set (FAF's `isClosed_consistentWith`).
Source: [[bli-coherent-mm-mandate]] T7; FAF `isClosed_consistentWith`
Kind: L
Fidelity: exact -/
theorem isClosed_consistentWorlds (D : Finset Sentence) : IsClosed (ConsistentWorlds D) :=
  BoolPCWorld.isClosed_consistentWith (constProcess D) 0

/-- The consistent worlds form a compact set (closed in the Cantor space).
Source: [[bli-coherent-mm-mandate]] T7
Kind: L
Fidelity: exact -/
theorem isCompact_consistentWorlds (D : Finset Sentence) : IsCompact (ConsistentWorlds D) :=
  (isClosed_consistentWorlds D).isCompact

/-- **The price of a sentence under a probability measure on the consistent worlds**: the mass
of `{w | w ⊨ φ}`.
Source: [[bli-coherent-mm-mandate]] T7 (`μ {v | Holds φ}`)
Kind: D
Fidelity: exact -/
noncomputable def omniPrice (D : Finset Sentence) (μ : ProbabilityMeasure (ConsistentWorlds D))
    (φ : Sentence) : ℝ :=
  ((μ : Measure (ConsistentWorlds D)) {w | (toPCWorld w.1).Holds φ}).toReal

/-- **The benefit of an infinite demand** `G μ` (shares of every sentence, priced by `μ`) in the
world `v`: `∑' φ, G μ φ · (payout_v φ − omniPrice μ φ)`.
Source: [[bli-coherent-mm-mandate]] T7 (`B μ v`)
Kind: D
Fidelity: exact -/
noncomputable def omniBenefit (D : Finset Sentence)
    (G : ProbabilityMeasure (ConsistentWorlds D) → Sentence → ℝ)
    (μ : ProbabilityMeasure (ConsistentWorlds D)) (v : ConsistentWorlds D) : ℝ :=
  ∑' φ, G μ φ * ((toPCWorld v.1).payout φ - omniPrice D μ φ)

/-! ## T7: the OPEN statement -/

/-- **T7 (OPEN). Omni-traders: the infinite fixed point.** For a nonempty stage, a demand
`G : ProbabilityMeasure (ConsistentWorlds D) → (Sentence → ℝ)` continuous for the topology of
weak convergence, with ℓ¹ norm uniformly bounded (`∑' φ, |G μ φ| ≤ M`), is there a probability
measure `μ` on the `D`-consistent worlds such that the benefit of `G μ` is `≤ 0` in every
`D`-consistent world? Open question in Soto PDF 05 "Omni-traders"; T1 is the finitely-supported
case (`omni_fixed_point_of_finiteSupport`), so the open part is exactly the
infinitely-supported one.
Source: [[bli-coherent-mm-mandate]] T7; Soto PDF 05 "Omni-traders" (bli-soto-a-046 (i))
Kind: OPEN
Fidelity: exact (this run's precise form of Soto's question)
Hyps: (a) `hD`, `hG`, `hsum`, `hM` — the question's own hypotheses -/
theorem omni_fixed_point (D : Finset Sentence) (hD : (ConsistentWorlds D).Nonempty)
    (G : ProbabilityMeasure (ConsistentWorlds D) → Sentence → ℝ) (hG : Continuous G) (M : ℝ)
    (hsum : ∀ μ, Summable fun φ => |G μ φ|) (hM : ∀ μ, ∑' φ, |G μ φ| ≤ M) :
    ∃ μ : ProbabilityMeasure (ConsistentWorlds D), ∀ v, omniBenefit D G μ v ≤ 0 := by
  sorry

/-! ## The finite-support reduction: Dirac mixtures realise every finite simplex point -/

/-- The marginal of `μ` on the first `B` atoms: the mass of the worlds restricting to `u`.
Source: [[bli-coherent-mm-mandate]] T7 (the finite-support reduction)
Kind: D
Fidelity: exact -/
noncomputable def omniMarginal (D : Finset Sentence) (B : ℕ)
    (μ : ProbabilityMeasure (ConsistentWorlds D)) (u : FiniteWorld B) : ℝ :=
  ((μ : Measure (ConsistentWorlds D)) {w | FiniteWorld.restrict w.1 B = u}).toReal

/-- A `D`-consistent finite world, extended by `false`, is a `D`-consistent Boolean world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def embedWorld (D : Finset Sentence) (B : ℕ) (x : ↥(WD D B)) : ConsistentWorlds D :=
  ⟨x.1.toBoolPCWorld, mem_WD.mp x.2⟩

/-- Restricting the `false`-extension of a finite world gives it back.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_toBoolPCWorld {B : ℕ} (u : FiniteWorld B) :
    FiniteWorld.restrict u.toBoolPCWorld B = u := by
  funext a
  simp [FiniteWorld.restrict, FiniteWorld.toBoolPCWorld, a.isLt]

/-- Truth of a sentence within the atom bound is unchanged by restricting a Boolean world.
Source: FAF `eval_toBoolPCWorld_restrict`
Kind: L
Fidelity: n/a -/
theorem holds_worldOf_restrict_bool (w : BoolPCWorld) {B : ℕ} {φ : Sentence}
    (hφ : atomBound φ ≤ B) :
    (FiniteWorld.restrict w B).toBoolPCWorld.toPCWorld.Holds φ ↔ (toPCWorld w).Holds φ := by
  rw [← eval_eq_true_iff_holds, ← eval_eq_true_iff_holds, eval_toBoolPCWorld_restrict w B φ hφ]

/-- The restriction of a consistent Boolean world is a consistent finite world (atom bound on
`D`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_mem_WD_of_consistentWorlds {D : Finset Sentence} {B : ℕ}
    (hD : ∀ φ ∈ D, atomBound φ ≤ B) (v : ConsistentWorlds D) :
    FiniteWorld.restrict v.1 B ∈ WD D B := by
  rw [mem_WD]
  intro φ hφ
  exact (holds_worldOf_restrict_bool v.1 (hD φ hφ)).mpr (v.2 φ hφ)

/-- **The Dirac mixture** of a weight vector on the consistent finite worlds, as a measure on the
consistent Boolean worlds.
Source: [[bli-coherent-mm-mandate]] T7 (the finite-support reduction)
Kind: D
Fidelity: exact -/
noncomputable def diracMixture (D : Finset Sentence) (B : ℕ) (q : ↥(WD D B) → ℝ) :
    Measure (ConsistentWorlds D) :=
  ∑ x, ENNReal.ofReal (q x) • Measure.dirac (embedWorld D B x)

/-- The Dirac mixture of a set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem diracMixture_apply (D : Finset Sentence) (B : ℕ) (q : ↥(WD D B) → ℝ)
    (s : Set (ConsistentWorlds D)) :
    diracMixture D B q s = ∑ x, ENNReal.ofReal (q x) * s.indicator 1 (embedWorld D B x) := by
  unfold diracMixture
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

/-- The real mass of a set under the Dirac mixture of a nonnegative vector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem diracMixture_apply_toReal (D : Finset Sentence) (B : ℕ) (q : ↥(WD D B) → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (s : Set (ConsistentWorlds D)) :
    (diracMixture D B q s).toReal =
      ∑ x, q x * s.indicator (1 : ConsistentWorlds D → ℝ) (embedWorld D B x) := by
  rw [diracMixture_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hq0 x)]
    congr 1
    by_cases h : embedWorld D B x ∈ s
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp
  · intro x _
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    by_cases h : embedWorld D B x ∈ s
    · rw [Set.indicator_of_mem h]
      exact ENNReal.one_ne_top
    · rw [Set.indicator_of_notMem h]
      exact ENNReal.zero_ne_top

/-- The Dirac mixture of a simplex point is a probability measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem isProbabilityMeasure_diracMixture (D : Finset Sentence) (B : ℕ) {q : ↥(WD D B) → ℝ}
    (hq : q ∈ stdSimplex ℝ ↥(WD D B)) : IsProbabilityMeasure (diracMixture D B q) := by
  rw [isProbabilityMeasure_iff, diracMixture_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hq.1 x), hq.2, ENNReal.ofReal_one]

/-- **The Dirac mixture of a simplex point, as a probability measure** on the consistent worlds.
Source: [[bli-coherent-mm-mandate]] T7 (the finite-support reduction)
Kind: D
Fidelity: exact -/
noncomputable def diracMixtureP (D : Finset Sentence) (B : ℕ) (q : ↥(WD D B) → ℝ)
    (hq : q ∈ stdSimplex ℝ ↥(WD D B)) : ProbabilityMeasure (ConsistentWorlds D) :=
  ⟨diracMixture D B q, isProbabilityMeasure_diracMixture D B hq⟩

/-- **The marginal of the Dirac mixture is the simplex point** (extended by zero off the
consistent worlds).
Source: [[bli-coherent-mm-mandate]] T7 (the finite-support reduction)
Kind: L
Fidelity: exact -/
theorem omniMarginal_diracMixtureP (D : Finset Sentence) (B : ℕ) {q : ↥(WD D B) → ℝ}
    (hq : q ∈ stdSimplex ℝ ↥(WD D B)) (u : FiniteWorld B) :
    omniMarginal D B (diracMixtureP D B q hq) u = AttemptA.extR D B q u := by
  unfold omniMarginal diracMixtureP
  show (diracMixture D B q _).toReal = _
  rw [diracMixture_apply_toReal D B q hq.1]
  have key : ∀ x : ↥(WD D B),
      ({w : ConsistentWorlds D | FiniteWorld.restrict w.1 B = u}.indicator
        (1 : ConsistentWorlds D → ℝ) (embedWorld D B x)) = if x.1 = u then 1 else 0 := by
    intro x
    by_cases hx : x.1 = u
    · have hm : embedWorld D B x ∈ {w : ConsistentWorlds D | FiniteWorld.restrict w.1 B = u} := by
        show FiniteWorld.restrict x.1.toBoolPCWorld B = u
        rw [restrict_toBoolPCWorld]
        exact hx
      rw [Set.indicator_of_mem hm, if_pos hx]
      rfl
    · have hm : embedWorld D B x ∉ {w : ConsistentWorlds D | FiniteWorld.restrict w.1 B = u} := by
        show ¬ FiniteWorld.restrict x.1.toBoolPCWorld B = u
        rw [restrict_toBoolPCWorld]
        exact hx
      rw [Set.indicator_of_notMem hm, if_neg hx]
  simp_rw [key]
  unfold AttemptA.extR
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨u, h⟩ : ↥(WD D B))]
    · simp
    · intro x _ hx
      have hne : x.1 ≠ u := fun e => hx (Subtype.ext e)
      simp [hne]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero
    intro x _
    have hne : x.1 ≠ u := fun e => h (e ▸ x.2)
    simp [hne]

/-- **The prices of the Dirac mixture are the marginal's prices**: `omniPrice (mixture q) φ =
∑ u, extR q u · payout_u φ`, for every sentence (no atom bound needed).
Source: [[bli-coherent-mm-mandate]] T7 (the finite-support reduction)
Kind: L
Fidelity: exact -/
theorem omniPrice_diracMixtureP (D : Finset Sentence) (B : ℕ) {q : ↥(WD D B) → ℝ}
    (hq : q ∈ stdSimplex ℝ ↥(WD D B)) (φ : Sentence) :
    omniPrice D (diracMixtureP D B q hq) φ =
      ∑ u, AttemptA.extR D B q u * (worldOf u).payout φ := by
  unfold omniPrice diracMixtureP
  show (diracMixture D B q _).toReal = _
  rw [diracMixture_apply_toReal D B q hq.1, AttemptA.sum_extR_mul]
  apply Finset.sum_congr rfl
  intro x _
  congr 1

/-! ## The finite benefit and the reduction -/

/-- Zero-extension is continuous.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem continuous_extR (D : Finset Sentence) (B : ℕ) : Continuous (AttemptA.extR D B) := by
  apply continuous_pi
  intro u
  unfold AttemptA.extR
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

/-- **The finite benefit** of a demand `G'` read through the marginal, supported on `S`, in the
consistent finite world `x`, priced at the simplex point `q`.
Source: [[bli-coherent-mm-mandate]] T7 (the finite-support reduction)
Kind: D
Fidelity: exact -/
noncomputable def finBenefit (D : Finset Sentence) (B : ℕ) (S : Finset Sentence)
    (G' : (FiniteWorld B → ℝ) → Sentence → ℝ) (q : ↥(WD D B) → ℝ) (x : ↥(WD D B)) : ℝ :=
  ∑ φ ∈ S, G' (AttemptA.extR D B q) φ *
    ((worldOf x.1).payout φ - ∑ u, AttemptA.extR D B q u * (worldOf u).payout φ)

/-- The zero-expected-value identity for the finite benefit (from `∑ q = 1` alone).
Source: [[bli-coherent-mm-mandate]] T7, T1 (the identity)
Kind: P
Fidelity: exact -/
theorem sum_mul_finBenefit (D : Finset Sentence) (B : ℕ) (S : Finset Sentence)
    (G' : (FiniteWorld B → ℝ) → Sentence → ℝ) {q : ↥(WD D B) → ℝ} (hq1 : ∑ x, q x = 1) :
    ∑ x, q x * finBenefit D B S G' q x = 0 := by
  unfold finBenefit
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro φ _
  have hπ : ∑ u, AttemptA.extR D B q u * (worldOf u).payout φ =
      ∑ x, q x * (worldOf x.1).payout φ :=
    AttemptA.sum_extR_mul q (fun u => (worldOf u).payout φ)
  have hsplit : ∀ x : ↥(WD D B), q x * (G' (AttemptA.extR D B q) φ *
      ((worldOf x.1).payout φ - ∑ u, AttemptA.extR D B q u * (worldOf u).payout φ)) =
      G' (AttemptA.extR D B q) φ * (q x * (worldOf x.1).payout φ) -
        G' (AttemptA.extR D B q) φ * (∑ u, AttemptA.extR D B q u * (worldOf u).payout φ) * q x := by
    intro x
    ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq1, mul_one, ← hπ]
  ring

/-- Continuity of the finite benefit in the simplex coordinates, given continuity of the demand
in the marginal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem continuous_finBenefit (D : Finset Sentence) (B : ℕ) (S : Finset Sentence)
    (G' : (FiniteWorld B → ℝ) → Sentence → ℝ)
    (hG' : ∀ φ, Continuous fun p : FiniteWorld B → ℝ => G' p φ) (x : ↥(WD D B)) :
    Continuous fun q => finBenefit D B S G' q x := by
  unfold finBenefit
  apply continuous_finsetSum
  intro φ _
  apply Continuous.mul
  · exact (hG' φ).comp (continuous_extR D B)
  · apply Continuous.sub continuous_const
    apply continuous_finsetSum
    intro u _
    exact ((continuous_apply u).comp (continuous_extR D B)).mul continuous_const

/-- **T7, the finite-support reduction (proved).** If the demand vanishes off a finite `S`
(within the atom bound `B`) and factors through the marginal of `μ` on the first `B` atoms —
`G μ φ = if φ ∈ S then G' (omniMarginal D B μ) φ else 0` with `G'` continuous in the marginal —
then the omni-trader fixed point **exists**: by T1's abstract lemma on the simplex over the
`D`-consistent finite worlds, and the Dirac mixture of the fixed point as the measure. So the
open part of `omni_fixed_point` is exactly the infinitely-supported case.
Source: [[bli-coherent-mm-mandate]] T7 ("proved companion"); Soto PDF 05 "Omni-traders"
Kind: P
Fidelity: exact
Hyps: (a) `hD`, `hS` (atom bounds), `hW` (a consistent finite world), `hG'` (continuity in the
marginal), `hG` (the finite-support factorisation — the reduction's defining hypothesis) -/
theorem omni_fixed_point_of_finiteSupport (D : Finset Sentence) (B : ℕ)
    (hD : ∀ φ ∈ D, atomBound φ ≤ B) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)
    (S : Finset Sentence) (hS : ∀ φ ∈ S, atomBound φ ≤ B)
    (G' : (FiniteWorld B → ℝ) → Sentence → ℝ)
    (hG' : ∀ φ, Continuous fun p : FiniteWorld B → ℝ => G' p φ)
    (G : ProbabilityMeasure (ConsistentWorlds D) → Sentence → ℝ)
    (hG : ∀ μ φ, G μ φ = if φ ∈ S then G' (omniMarginal D B μ) φ else 0) :
    ∃ μ : ProbabilityMeasure (ConsistentWorlds D), ∀ v, omniBenefit D G μ v ≤ 0 := by
  haveI : Nonempty ↥(WD D B) := by
    obtain ⟨u, hu⟩ := hW
    exact ⟨⟨u, mem_WD.mpr hu⟩⟩
  obtain ⟨q, hq, hle⟩ := coherent_fixed_point_abstract (fun q x => finBenefit D B S G' q x)
    (continuous_pi fun x => continuous_finBenefit D B S G' hG' x).continuousOn
    (fun q hq => sum_mul_finBenefit D B S G' hq.2)
  refine ⟨diracMixtureP D B q hq, fun v => ?_⟩
  have hx : FiniteWorld.restrict v.1 B ∈ WD D B := restrict_mem_WD_of_consistentWorlds hD v
  have hmarg : omniMarginal D B (diracMixtureP D B q hq) = AttemptA.extR D B q :=
    funext fun u => omniMarginal_diracMixtureP D B hq u
  calc omniBenefit D G (diracMixtureP D B q hq) v = finBenefit D B S G' q ⟨_, hx⟩ := ?_
    _ ≤ 0 := hle ⟨_, hx⟩
  unfold omniBenefit finBenefit
  rw [tsum_eq_sum (s := S)]
  · apply Finset.sum_congr rfl
    intro φ hφ
    rw [hG, if_pos hφ, omniPrice_diracMixtureP, hmarg]
    have hpay : (toPCWorld v.1).payout φ = (worldOf (FiniteWorld.restrict v.1 B)).payout φ := by
      have hiff := holds_worldOf_restrict_bool v.1 (hS φ hφ)
      unfold PCWorld.payout
      by_cases h : (toPCWorld v.1).Holds φ
      · rw [if_pos h, if_pos (hiff.mpr h)]
      · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
    rw [hpay]
  · intro φ hφ
    rw [hG, if_neg hφ, zero_mul]

end Cleanroom.Bli.BliCoherentMm
