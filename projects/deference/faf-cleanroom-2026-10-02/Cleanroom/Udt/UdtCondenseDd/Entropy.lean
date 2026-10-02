import Cleanroom.Udt.UdtCondenseDd.Bridge
import Cleanroom.Udt.UdtCondenseDd.Approx
import Cleanroom.Info.InfoVoiLatents.Finite

/-!
# `Cleanroom.Udt.UdtCondenseDd.Entropy`: the entropy-level approximate DD (T11(c))

Work package `udt-condense-dd`, target T11(c) (mandate T7(c): "the form in which T3/T4's approximate
DD should be *read*"). Listed OPEN in the first version; proved in repair round 1.

**Statement** (`approxDD_entropy`). If `U` is a function of `E` (DD's clause (1)), then

`∑ d, P(D_{I,B} = d) · |E[U | D_{I,B} = d] − E[U | Π̈ = [[d]]]| ≤ √(I[E : D_{I,B} | Π̈] / 2)`,

where `I[· : · | ·]` is PFR's conditional mutual information (nats) under the structure's prior
`dsMeasure S`. At `I = 0` (i.e. DD) this is `udt-comm-trust`'s `condExp_DIB_eq_policyUtility`
averaged over the atoms; in general it is the quantitative form of "DD up to `δ`".

**Proof.** Three layers.

1. *Finite masses.* `jointDE d e = P(D_{I,B} = d, E = e)`, `jointZE z e = P(Π̈ = z, E = e)`, the
   conditionals `condE d = P(E | D_{I,B} = d)`, `condEz z = P(E | Π̈ = z)` (Lean's `x / 0 = 0` on
   unrealized atoms). Since `Π̈ = polOf ∘ D_{I,B}`, the `z`-masses are fibre sums of the
   `d`-masses (`jointZE_eq_sum`), and `d`-masses are dominated by their `z`-masses.
2. *The finite inequality* (`approxDD_entropy_fin`): on a realized atom `E[U | d] = ∑_e P(e | d) u(e)`
   and `E[U | [[d]]] = ∑_e P(e | [[d]]) u(e)` with `u ∈ [0, 1]`, so the gap is at most
   `tv(P(E | d), P(E | [[d]]))` (`abs_sum_sub_le_tv`), at most `√(KL / 2)` by Pinsker on the finite
   simplex (`Cleanroom.Info.InfoVoiLatents.pinsker`; absolute continuity holds because the
   `d`-atom lies inside the `[[d]]`-atom), and Jensen for `√` (`sum_mul_sqrt_le`) moves the
   `d`-average inside.
3. *The bridge* (`condMutualInfo_eq_sum_mul_klFin`): PFR's `I[E : D_{I,B} | Π̈] = H[E | Π̈] −
   H[E | ⟨D_{I,B}, Π̈⟩]` (`condMutualInfo_eq'`); the pair collapses to `H[E | D_{I,B}]` because
   `d ↦ (d, polOf d)` is injective (`condEntropy_of_injective'`); both conditional entropies are
   double sums of `negMulLog` of conditional masses (`condEntropy_eq_sum_sum_fintype`, with the
   conditional measures computed as mass ratios, `cond_map_real_singleton`); and the real identity
   `H[E | Π̈] − H[E | D_{I,B}] = ∑_d P(d) · KL(P(E | d) ‖ P(E | [[d]]))` (`sum_mul_klFin_eq`) is the
   fibre-sum regrouping of layer 1.

The Info package's `tv`/`klFin` (on `W → ℝ`) are referred to qualified, since this package has its
own `tv` on `FinDist`.
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust MeasureTheory ProbabilityTheory Finset
open Cleanroom.Info

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Layer 1: finite masses -/

section Finite

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]
  [Fintype DE] [DecidableEq DE] [Fintype DI] [DecidableEq DI] [Fintype DB] [DecidableEq DB]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- The joint mass `P(D_{I,B} = d, E = e)`.
Source: none: infrastructure (T11(c))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def jointDE (d : DI × DB) (e : AE × DE) : ℝ :=
  mass S.μ.w (event fun ω => S.DIB ω = d ∧ S.E ω = e)

/-- The joint mass `P(Π̈ = z, E = e)`.
Source: none: infrastructure (T11(c))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def jointZE (z : OE → AE) (e : AE × DE) : ℝ :=
  mass S.μ.w (event fun ω => S.polE ω = z ∧ S.E ω = e)

/-- The conditional `P(E = e | D_{I,B} = d)`; `0` on an unrealized atom (Lean's `x / 0 = 0`), where
it carries no weight in any statement below.
Source: none: infrastructure (T11(c))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def condE (d : DI × DB) (e : AE × DE) : ℝ := jointDE S d e / mass S.μ.w (S.evDIB d)

/-- The conditional `P(E = e | Π̈ = z)`; `0` on an unrealized atom.
Source: none: infrastructure (T11(c))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def condEz (z : OE → AE) (e : AE × DE) : ℝ := jointZE S z e / mass S.μ.w (S.evPolE z)

/-- Supporting lemma: joint masses are non-negative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem jointDE_nonneg (d : DI × DB) (e : AE × DE) : 0 ≤ jointDE S d e :=
  mass_nonneg (fun ω => S.μ.nonneg ω) _

/-- Supporting lemma: the `e`-sum of the joint masses is the atom mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_jointDE (d : DI × DB) : ∑ e, jointDE S d e = mass S.μ.w (S.evDIB d) := by
  unfold jointDE
  have h : ∀ e, (event fun ω => S.DIB ω = d ∧ S.E ω = e) =
      (S.evDIB d).filter fun ω => S.E ω = e := by
    intro e; ext ω; simp [AbstractDS.evDIB]
  simp_rw [h]
  unfold mass
  exact Finset.sum_fiberwise (S.evDIB d) S.E S.μ.w

/-- Supporting lemma: the `e`-sum of the policy-atom joint masses is the policy-atom mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_jointZE (z : OE → AE) : ∑ e, jointZE S z e = mass S.μ.w (S.evPolE z) := by
  unfold jointZE
  have h : ∀ e, (event fun ω => S.polE ω = z ∧ S.E ω = e) =
      (S.evPolE z).filter fun ω => S.E ω = e := by
    intro e; ext ω; simp [AbstractDS.evPolE]
  simp_rw [h]
  unfold mass
  exact Finset.sum_fiberwise (S.evPolE z) S.E S.μ.w

/-- Supporting lemma: a `d`-atom's joint mass is at most that of its policy atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem jointDE_le_jointZE (d : DI × DB) (e : AE × DE) :
    jointDE S d e ≤ jointZE S (S.polOf d) e := by
  unfold jointDE jointZE
  refine mass_mono (fun ω => S.μ.nonneg ω) fun ω hω => ?_
  rw [mem_event] at hω ⊢
  exact ⟨by rw [S.polE_eq, hω.1], hω.2⟩

/-- Supporting lemma: a joint mass is at most its atom mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem jointDE_le_mass (d : DI × DB) (e : AE × DE) : jointDE S d e ≤ mass S.μ.w (S.evDIB d) := by
  unfold jointDE
  refine mass_mono (fun ω => S.μ.nonneg ω) fun ω hω => ?_
  rw [mem_event] at hω
  exact (S.mem_evDIB).2 hω.1

/-- Supporting lemma: a `d`-atom's mass is at most its policy atom's.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_evDIB_le (d : DI × DB) :
    mass S.μ.w (S.evDIB d) ≤ mass S.μ.w (S.evPolE (S.polOf d)) :=
  mass_mono (fun ω => S.μ.nonneg ω) (S.evDIB_subset_evPolE d)

/-- **The policy-atom joint masses are fibre sums of the `d`-atom joint masses** (because
`Π̈ = polOf ∘ D_{I,B}`).
Source: none: infrastructure (T11(c), the chain-rule step)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem jointZE_eq_sum (z : OE → AE) (e : AE × DE) :
    jointZE S z e = ∑ d ∈ univ.filter (fun d => S.polOf d = z), jointDE S d e := by
  unfold jointZE jointDE
  rw [mass, ← Finset.sum_fiberwise (event fun ω => S.polE ω = z ∧ S.E ω = e) S.DIB S.μ.w,
    ← Finset.sum_filter_add_sum_filter_not univ (fun d => S.polOf d = z)]
  have h0 : ∑ d ∈ univ.filter (fun d => ¬ S.polOf d = z),
      ∑ ω ∈ (event fun ω => S.polE ω = z ∧ S.E ω = e).filter (fun ω => S.DIB ω = d), S.μ.w ω = 0 := by
    refine Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun ω hω => ?_
    rw [Finset.mem_filter] at hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    have h1 : S.polOf (S.DIB ω) = z := hω.1.1
    rw [hω.2] at h1
    exact absurd h1 hd.2
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_filter] at hd
  unfold mass
  congr 1
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h3, h2⟩
    refine ⟨⟨?_, h2⟩, h3⟩
    show S.polOf (S.DIB ω) = z
    rw [h3, hd.2]

/-- Supporting lemma: `P(E | d)` is a distribution on a realized atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condE_mem (d : DI × DB) (hd : 0 < mass S.μ.w (S.evDIB d)) :
    condE S d ∈ stdSimplex ℝ (AE × DE) := by
  simp only [stdSimplex, Set.mem_setOf_eq]
  refine ⟨fun e => div_nonneg (jointDE_nonneg S d e) hd.le, ?_⟩
  unfold condE
  rw [← Finset.sum_div, sum_jointDE S, div_self hd.ne']

/-- Supporting lemma: `P(E | z)` is a distribution on a realized policy atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condEz_mem (z : OE → AE) (hz : 0 < mass S.μ.w (S.evPolE z)) :
    condEz S z ∈ stdSimplex ℝ (AE × DE) := by
  simp only [stdSimplex, Set.mem_setOf_eq]
  refine ⟨fun e => div_nonneg (mass_nonneg (fun ω => S.μ.nonneg ω) _) hz.le, ?_⟩
  unfold condEz
  rw [← Finset.sum_div, sum_jointZE S, div_self hz.ne']

/-- Supporting lemma: `P(E | d) ≪ P(E | [[d]])` on a realized atom (the `d`-atom lies inside its
policy atom).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condE_absCont (d : DI × DB) (hd : 0 < mass S.μ.w (S.evDIB d)) :
    InfoVoiLatents.AbsCont (condE S d) (condEz S (S.polOf d)) := by
  unfold InfoVoiLatents.AbsCont
  intro e he
  have hB : 0 < mass S.μ.w (S.evPolE (S.polOf d)) := lt_of_lt_of_le hd (mass_evDIB_le S d)
  unfold condEz at he
  rw [div_eq_zero_iff] at he
  rcases he with he | he
  · have h0 : jointDE S d e = 0 :=
      le_antisymm (he ▸ jointDE_le_jointZE S d e) (jointDE_nonneg S d e)
    unfold condE
    rw [h0, zero_div]
  · exact absurd he hB.ne'

/-! ### Layer 1, continued: the entropy identity in finite form -/

/-- Supporting lemma: `P(d) · negMulLog P(e | d) = −P(d, e) · log P(e | d)` (both sides `0` on an
unrealized atom).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mul_negMulLog_condE (d : DI × DB) (e : AE × DE) :
    mass S.μ.w (S.evDIB d) * Real.negMulLog (condE S d e) =
      -(jointDE S d e * Real.log (condE S d e)) := by
  rcases eq_or_lt_of_le (mass_nonneg (fun ω => S.μ.nonneg ω) (S.evDIB d)) with h | h
  · have ha : jointDE S d e = 0 :=
      le_antisymm (h ▸ jointDE_le_mass S d e) (jointDE_nonneg S d e)
    rw [← h, ha]
    simp
  · have hab : mass S.μ.w (S.evDIB d) * condE S d e = jointDE S d e := by
      unfold condE
      field_simp
    unfold Real.negMulLog
    calc mass S.μ.w (S.evDIB d) * (-condE S d e * Real.log (condE S d e))
        = -(mass S.μ.w (S.evDIB d) * condE S d e) * Real.log (condE S d e) := by ring
      _ = -(jointDE S d e * Real.log (condE S d e)) := by rw [hab]; ring

/-- Supporting lemma: the same on a policy atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mul_negMulLog_condEz (z : OE → AE) (e : AE × DE) :
    mass S.μ.w (S.evPolE z) * Real.negMulLog (condEz S z e) =
      -(jointZE S z e * Real.log (condEz S z e)) := by
  rcases eq_or_lt_of_le (mass_nonneg (fun ω => S.μ.nonneg ω) (S.evPolE z)) with h | h
  · have hA : jointZE S z e = 0 := by
      have hle : jointZE S z e ≤ mass S.μ.w (S.evPolE z) := by
        unfold jointZE
        refine mass_mono (fun ω => S.μ.nonneg ω) fun ω hω => ?_
        rw [mem_event] at hω
        exact (S.mem_evPolE).2 hω.1
      exact le_antisymm (h ▸ hle) (mass_nonneg (fun ω => S.μ.nonneg ω) _)
    rw [← h, hA]
    simp
  · have hab : mass S.μ.w (S.evPolE z) * condEz S z e = jointZE S z e := by
      unfold condEz
      field_simp
    unfold Real.negMulLog
    calc mass S.μ.w (S.evPolE z) * (-condEz S z e * Real.log (condEz S z e))
        = -(mass S.μ.w (S.evPolE z) * condEz S z e) * Real.log (condEz S z e) := by ring
      _ = -(jointZE S z e * Real.log (condEz S z e)) := by rw [hab]; ring

/-- Supporting lemma: `P(d) · KL(P(E | d) ‖ P(E | [[d]])) = ∑_e P(d, e) (log P(e | d) − log P(e | [[d]]))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mul_klFin_condE (d : DI × DB) :
    mass S.μ.w (S.evDIB d) * InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) =
      ∑ e, jointDE S d e * (Real.log (condE S d e) - Real.log (condEz S (S.polOf d) e)) := by
  unfold InfoVoiLatents.klFin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases eq_or_lt_of_le (jointDE_nonneg S d e) with ha | ha
  · have hp : condE S d e = 0 := by
      unfold condE
      rw [← ha, zero_div]
    rw [hp, ← ha]
    simp
  · have hb : 0 < mass S.μ.w (S.evDIB d) := lt_of_lt_of_le ha (jointDE_le_mass S d e)
    have hA : 0 < jointZE S (S.polOf d) e := lt_of_lt_of_le ha (jointDE_le_jointZE S d e)
    have hB : 0 < mass S.μ.w (S.evPolE (S.polOf d)) := lt_of_lt_of_le hb (mass_evDIB_le S d)
    have hp : 0 < condE S d e := div_pos ha hb
    have hq : 0 < condEz S (S.polOf d) e := div_pos hA hB
    have hbp : mass S.μ.w (S.evDIB d) * condE S d e = jointDE S d e := by
      unfold condE
      field_simp
    rw [Real.log_div hp.ne' hq.ne', ← mul_assoc, hbp]

/-- Supporting lemma: regrouping the `d`-sum by policy atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_jointDE_log_condEz (e : AE × DE) :
    ∑ d, jointDE S d e * Real.log (condEz S (S.polOf d) e) =
      ∑ z, jointZE S z e * Real.log (condEz S z e) := by
  rw [← Finset.sum_fiberwise univ S.polOf
    (fun d => jointDE S d e * Real.log (condEz S (S.polOf d) e))]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [jointZE_eq_sum S, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_filter] at hd
  rw [hd.2]

/-- **The entropy identity in finite form**: `∑_d P(d) KL(P(E | d) ‖ P(E | [[d]])) =
∑_z ∑_e P(z) negMulLog P(e | z) − ∑_d ∑_e P(d) negMulLog P(e | d)`, i.e.
`H[E | Π̈] − H[E | D_{I,B}]` once the sums are read as entropies (`condMutualInfo_eq_sum_mul_klFin`).
Source: none: infrastructure (T11(c), the chain rule `I[E : D_{I,B} | Π̈] = E_d KL` for `Π̈ ⊑ D_{I,B}`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem sum_mul_klFin_eq :
    ∑ d, mass S.μ.w (S.evDIB d) * InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) =
      (∑ z, ∑ e, mass S.μ.w (S.evPolE z) * Real.negMulLog (condEz S z e)) -
        ∑ d, ∑ e, mass S.μ.w (S.evDIB d) * Real.negMulLog (condE S d e) := by
  have hswap : ∑ d, ∑ e, jointDE S d e * Real.log (condEz S (S.polOf d) e) =
      ∑ z, ∑ e, jointZE S z e * Real.log (condEz S z e) := by
    rw [Finset.sum_comm]
    simp_rw [sum_jointDE_log_condEz S]
    rw [Finset.sum_comm]
  simp_rw [mul_klFin_condE S, mul_negMulLog_condE S, mul_negMulLog_condEz S, mul_sub,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hswap]
  ring

/-! ### Layer 2: the finite inequality -/

/-- **Mean shift under a change of distribution is at most the total variation** for a `[0, 1]`-valued
integrand: `|∑ p u − ∑ q u| ≤ tv p q` (centring at `1/2`).
Source: none: infrastructure (T11(c), the per-atom step)
Kind: P
Fidelity: exact
Hyps: none -/
theorem abs_sum_sub_le_tv {W : Type} [Fintype W] {p q : W → ℝ} (hp : p ∈ stdSimplex ℝ W)
    (hq : q ∈ stdSimplex ℝ W) {u : W → ℝ} (hu : ∀ w, u w ∈ Set.Icc (0 : ℝ) 1) :
    |∑ w, p w * u w - ∑ w, q w * u w| ≤ InfoVoiLatents.tv p q := by
  have hz : ∑ w, (p w - q w) = 0 := by
    rw [Finset.sum_sub_distrib, hp.2, hq.2, sub_self]
  have hc : ∑ w, p w * u w - ∑ w, q w * u w = ∑ w, (p w - q w) * (u w - 1 / 2) := by
    have h : ∀ w, (p w - q w) * (u w - 1 / 2) =
        p w * u w - q w * u w - (1 / 2) * (p w - q w) := fun w => by ring
    simp_rw [h]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hz, mul_zero, sub_zero]
  rw [hc, InfoVoiLatents.tv, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [abs_mul]
  have h1 : |u w - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [(hu w).1, (hu w).2]
  calc |p w - q w| * |u w - 1 / 2| ≤ |p w - q w| * (1 / 2) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = 1 / 2 * |p w - q w| := by ring

/-- Supporting lemma: on a realized atom, `E[U | d] = ∑_e P(e | d) u(e)` when `U = u ∘ E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExp_evDIB_eq {u : AE × DE → ℝ} (hu : ∀ ω, S.U ω = u (S.E ω)) (d : DI × DB)
    (hd : 0 < mass S.μ.w (S.evDIB d)) :
    condExpJunk S.μ.w S.U (S.evDIB d) (-1) = ∑ e, condE S d e * u e := by
  rw [condExpJunk_of_pos hd]
  have h : ∑ ω ∈ S.evDIB d, S.μ.w ω * S.U ω = ∑ e, u e * jointDE S d e := by
    rw [show (∑ ω ∈ S.evDIB d, S.μ.w ω * S.U ω) = ∑ ω ∈ S.evDIB d, S.μ.w ω * u (S.E ω) from
      Finset.sum_congr rfl fun ω _ => by rw [hu ω], sum_mul_comp_eq]
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    unfold jointDE
    congr 1
    ext ω
    simp [AbstractDS.evDIB]
  rw [h, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold condE
  ring

/-- Supporting lemma: on a realized policy atom, `E[U | Π̈ = z] = ∑_e P(e | z) u(e)` when `U = u ∘ E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condExp_evPolE_eq {u : AE × DE → ℝ} (hu : ∀ ω, S.U ω = u (S.E ω)) (z : OE → AE)
    (hz : 0 < mass S.μ.w (S.evPolE z)) :
    condExpJunk S.μ.w S.U (S.evPolE z) (-1) = ∑ e, condEz S z e * u e := by
  rw [condExpJunk_of_pos hz]
  have h : ∑ ω ∈ S.evPolE z, S.μ.w ω * S.U ω = ∑ e, u e * jointZE S z e := by
    rw [show (∑ ω ∈ S.evPolE z, S.μ.w ω * S.U ω) = ∑ ω ∈ S.evPolE z, S.μ.w ω * u (S.E ω) from
      Finset.sum_congr rfl fun ω _ => by rw [hu ω], sum_mul_comp_eq]
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    unfold jointZE
    congr 1
    ext ω
    simp [AbstractDS.evPolE]
  rw [h, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold condEz
  ring

/-- **The per-atom bound**: `P(d) · |E[U | d] − E[U | [[d]]]| ≤ P(d) · √(KL(P(E | d) ‖ P(E | [[d]])) / 2)`,
by the mean-shift bound and Pinsker (trivially on an unrealized atom).
Source: none: infrastructure (T11(c))
Kind: C
Fidelity: exact
Hyps: none -/
theorem atom_bound {u : AE × DE → ℝ} (hu : ∀ ω, S.U ω = u (S.E ω))
    (hu01 : ∀ e, u e ∈ Set.Icc (0 : ℝ) 1) (d : DI × DB) :
    mass S.μ.w (S.evDIB d) *
        |condExpJunk S.μ.w S.U (S.evDIB d) (-1) - S.policyUtility (S.polOf d)| ≤
      mass S.μ.w (S.evDIB d) *
        Real.sqrt (InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) / 2) := by
  rcases eq_or_lt_of_le (mass_nonneg (fun ω => S.μ.nonneg ω) (S.evDIB d)) with h | h
  · rw [← h]
    simp
  · refine mul_le_mul_of_nonneg_left ?_ h.le
    have hB : 0 < mass S.μ.w (S.evPolE (S.polOf d)) := lt_of_lt_of_le h (mass_evDIB_le S d)
    rw [condExp_evDIB_eq S hu d h, AbstractDS.policyUtility, condExp_evPolE_eq S hu _ hB]
    exact (abs_sum_sub_le_tv (condE_mem S d h) (condEz_mem S _ hB) hu01).trans
      (InfoVoiLatents.pinsker (condE_mem S d h) (condEz_mem S _ hB) (condE_absCont S d h))

/-- Supporting lemma: the atom masses form a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_evDIB_mem : (fun d => mass S.μ.w (S.evDIB d)) ∈ stdSimplex ℝ (DI × DB) := by
  simp only [stdSimplex, Set.mem_setOf_eq]
  refine ⟨fun d => mass_nonneg (fun ω => S.μ.nonneg ω) _, ?_⟩
  have h := Finset.sum_fiberwise (univ : Finset Ω) S.DIB S.μ.w
  rw [S.μ.sum_one] at h
  exact h

/-- **Entropy-level approximate DD, finite form (T11(c))**: if `U` is a function of `E`, the
`D_{I,B}`-averaged gap between `E[U | D_{I,B} = d]` and the policy utility `E[U | Π̈ = [[d]]]` is at
most `√(E_d KL(P(E | d) ‖ P(E | [[d]])) / 2)`, with the KL as a finite sum.
Source: mandate T7(c), T11(c)
Kind: P
Fidelity: exact (the finite-sum form; the PFR form is `approxDD_entropy`)
Hyps: (a) `hU` -/
theorem approxDD_entropy_fin (hU : IsSubvariable S.E S.U) :
    ∑ d, mass S.μ.w (S.evDIB d) *
        |condExpJunk S.μ.w S.U (S.evDIB d) (-1) - S.policyUtility (S.polOf d)| ≤
      Real.sqrt ((∑ d, mass S.μ.w (S.evDIB d) *
        InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d))) / 2) := by
  obtain ⟨u, hu⟩ := (isSubvariable_iff_exists S.E S.U).1 hU
  set u' : AE × DE → ℝ := fun e => max 0 (min 1 (u e)) with hu'def
  have hu' : ∀ ω, S.U ω = u' (S.E ω) := fun ω => by
    simp only [hu'def, ← hu ω]
    rw [min_eq_right (S.U_mem ω).2, max_eq_right (S.U_mem ω).1]
  have hu'01 : ∀ e, u' e ∈ Set.Icc (0 : ℝ) 1 := fun e =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hx : ∀ d, 0 ≤ InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) / 2 := fun d => by
    rcases eq_or_lt_of_le (mass_nonneg (fun ω => S.μ.nonneg ω) (S.evDIB d)) with h | h
    · have h0 : InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) = 0 := by
        unfold InfoVoiLatents.klFin
        refine Finset.sum_eq_zero fun e _ => ?_
        unfold condE
        rw [← h, div_zero, zero_mul]
      rw [h0]
      norm_num
    · have hB := lt_of_lt_of_le h (mass_evDIB_le S d)
      have := InfoVoiLatents.klFin_nonneg (condE_mem S d h) (condEz_mem S _ hB)
        (condE_absCont S d h)
      linarith
  calc ∑ d, mass S.μ.w (S.evDIB d) *
          |condExpJunk S.μ.w S.U (S.evDIB d) (-1) - S.policyUtility (S.polOf d)|
      ≤ ∑ d, mass S.μ.w (S.evDIB d) *
          Real.sqrt (InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) / 2) :=
        Finset.sum_le_sum fun d _ => atom_bound S hu' hu'01 d
    _ ≤ Real.sqrt (∑ d, mass S.μ.w (S.evDIB d) *
          (InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) / 2)) :=
        InfoVoiLatents.sum_mul_sqrt_le (mass_evDIB_mem S) hx
    _ = Real.sqrt ((∑ d, mass S.μ.w (S.evDIB d) *
          InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d))) / 2) := by
        congr 1
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun d _ => by ring

end Finite

/-! ### Layer 3: the bridge to PFR's conditional mutual information -/

section Measure

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE] [Fintype DE] [DecidableEq DE]
  [Fintype DI] [DecidableEq DI] [Fintype DB] [DecidableEq DB]
variable [MeasurableSpace OE] [MeasurableSingletonClass OE] [MeasurableSpace AE]
  [MeasurableSingletonClass AE] [MeasurableSpace DE] [MeasurableSingletonClass DE]
  [MeasurableSpace DI] [MeasurableSingletonClass DI] [MeasurableSpace DB]
  [MeasurableSingletonClass DB]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- Supporting lemma: the real measure of a fibre is its mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dsMeasure_real_preimage {V : Type} [DecidableEq V] (Y : Ω → V) (y : V) :
    (dsMeasure S).real (Y ⁻¹' {y}) = mass S.μ.w (event fun ω => Y ω = y) := by
  rw [measureReal_def, show Y ⁻¹' {y} = {ω | Y ω = y} from rfl, dsMeasure_setOf,
    ENNReal.toReal_ofReal (mass_nonneg (fun ω => S.μ.nonneg ω) _)]

/-- Supporting lemma: the pushforward's real mass of a singleton is the fibre's mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem map_real_singleton {V : Type} [MeasurableSpace V] [MeasurableSingletonClass V]
    [DecidableEq V] (Y : Ω → V) (y : V) :
    ((dsMeasure S).map Y).real {y} = mass S.μ.w (event fun ω => Y ω = y) := by
  rw [map_measureReal_apply (measurable_of_countable Y) (measurableSet_singleton y),
    dsMeasure_real_preimage S Y y]

/-- Supporting lemma: the conditional measure's pushforward on a singleton is the mass ratio
(`0` on a null fibre, matching Lean's `x / 0 = 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cond_map_real_singleton {V W : Type} [MeasurableSpace V] [MeasurableSingletonClass V]
    [DecidableEq V] [MeasurableSpace W] [MeasurableSingletonClass W] [DecidableEq W]
    (Y : Ω → V) (y : V) (X : Ω → W) (x : W) :
    (((dsMeasure S)[|Y ⁻¹' {y}]).map X).real {x} =
      mass S.μ.w (event fun ω => Y ω = y ∧ X ω = x) / mass S.μ.w (event fun ω => Y ω = y) := by
  rw [map_measureReal_apply (measurable_of_countable X) (measurableSet_singleton x),
    measureReal_def, cond_apply ((measurable_of_countable Y) (measurableSet_singleton y)),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  have h1 : Y ⁻¹' {y} ∩ X ⁻¹' {x} = {ω | Y ω = y ∧ X ω = x} := by
    ext ω
    simp [Set.mem_inter_iff]
  rw [h1, dsMeasure_setOf, show Y ⁻¹' {y} = {ω | Y ω = y} from rfl, dsMeasure_setOf,
    ENNReal.toReal_ofReal (mass_nonneg (fun ω => S.μ.nonneg ω) _),
    ENNReal.toReal_ofReal (mass_nonneg (fun ω => S.μ.nonneg ω) _), div_eq_inv_mul]

/-- Supporting lemma: `H[E | D_{I,B}]` as a double sum of `negMulLog` of conditional masses.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condEntropy_E_DIB :
    H[S.E | S.DIB ; dsMeasure S] =
      ∑ d, ∑ e, mass S.μ.w (S.evDIB d) * Real.negMulLog (condE S d e) := by
  rw [condEntropy_eq_sum_sum_fintype (measurable_of_countable S.DIB) (dsMeasure S)]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  rw [map_real_singleton S, cond_map_real_singleton S]
  rfl

/-- Supporting lemma: `H[E | Π̈]` as a double sum of `negMulLog` of conditional masses.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condEntropy_E_polE :
    H[S.E | S.polE ; dsMeasure S] =
      ∑ z, ∑ e, mass S.μ.w (S.evPolE z) * Real.negMulLog (condEz S z e) := by
  rw [condEntropy_eq_sum_sum_fintype (measurable_of_countable S.polE) (dsMeasure S)]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun e _ => ?_
  rw [map_real_singleton S, cond_map_real_singleton S]
  rfl

/-- Supporting lemma: conditioning on `(D_{I,B}, Π̈)` is conditioning on `D_{I,B}` (`Π̈` is a
function of `D_{I,B}`; `d ↦ (d, polOf d)` is injective).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem condEntropy_E_pair :
    H[S.E | ⟨S.DIB, S.polE⟩ ; dsMeasure S] = H[S.E | S.DIB ; dsMeasure S] := by
  have h : (⟨S.DIB, S.polE⟩ : Ω → (DI × DB) × (OE → AE)) = (fun d => (d, S.polOf d)) ∘ S.DIB :=
    rfl
  rw [h]
  exact condEntropy_of_injective' (dsMeasure S) (measurable_of_countable _)
    (measurable_of_countable _) (fun d => (d, S.polOf d)) (fun a b hab => (Prod.mk.inj hab).1)
    (measurable_of_countable _)

/-- **The bridge**: PFR's `I[E : D_{I,B} | Π̈]` under the structure's prior is the
`D_{I,B}`-average of the finite KL divergences `KL(P(E | d) ‖ P(E | [[d]]))`.
Source: none: infrastructure (T11(c); FAF API request: the chain rule `I[X : Y | g ∘ Y] = E_y KL` in sum form)
Kind: P
Fidelity: exact
Hyps: none -/
theorem condMutualInfo_eq_sum_mul_klFin :
    I[S.E : S.DIB | S.polE ; dsMeasure S] =
      ∑ d, mass S.μ.w (S.evDIB d) * InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) := by
  rw [condMutualInfo_eq' (measurable_of_countable _) (measurable_of_countable _)
    (measurable_of_countable _), condEntropy_E_pair S, condEntropy_E_polE S, condEntropy_E_DIB S,
    sum_mul_klFin_eq S]

/-- **Entropy-level approximate DD (T11(c); OPEN in the first version, proved in repair round 1).**
If `U` is a function of `E` (DD's clause (1)), the `D_{I,B}`-averaged absolute gap between the
conditional expected utility given the dynamics and the policy utility of the encoded policy is at
most `√(I[E : D_{I,B} | Π̈] / 2)`. At `I = 0` this is `condExp_DIB_eq_policyUtility`
(udt-comm-trust) averaged; in general it is per-atom Pinsker + the chain rule for `Π̈ ⊑ D_{I,B}`
+ Jensen. Unrealized `d` contribute `0` (their mass is `0`). The conditional mutual information is
PFR's, in nats, under `dsMeasure S`. The bound is the `D_{I,B}`-averaged one: the mandate phrases
T11(c) per atom ("`I[…] ≤ δ` as a hypothesis and a bound on `|E[U | d] − E[U | [[d]]]|`"); the
per-atom form in terms of the atom's own `KL_d` is `atom_bound`, and one atom's `KL_d` can exceed
the average `I`, so the averaged form is what `I` alone bounds. Witness: `WitnessEntropy.XorSkew`
(repair round 2), a non-DD structure with `U ⊑ E`, `I > 0` and a positive left-hand side.
Source: mandate T7(c), T11(c) (the form in which T3/T4's approximate DD is to be read)
Kind: P
Fidelity: exact (averaged over `d`: `∑_d P(d) · |gap_d| ≤ √(I/2)`; the mandate's per-atom phrasing is `atom_bound` with `KL_d` in place of `I`)
Hyps: (a) `hU`; `udt-comm-trust` §3 (c) by reference (the carrier is the support) -/
theorem approxDD_entropy (hU : IsSubvariable S.E S.U) :
    ∑ d, mass S.μ.w (S.evDIB d) *
        |condExpJunk S.μ.w S.U (S.evDIB d) (-1) - S.policyUtility (S.polOf d)| ≤
      Real.sqrt (I[S.E : S.DIB | S.polE ; dsMeasure S] / 2) := by
  rw [condMutualInfo_eq_sum_mul_klFin S]
  exact approxDD_entropy_fin S hU

end Measure

end

end Cleanroom.Udt.UdtCondenseDd
