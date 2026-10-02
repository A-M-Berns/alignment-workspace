import Cleanroom.Bli.UdtBliSist.Crux
import Cleanroom.Bli.UdtBliSist.Skeleton

/-!
# `udt-bli-sist` · CruxWitness: the N+ of the crux (T5 a)

`udt-bli-core`'s tent prior (`Tent.tentPrior`: nine grid tables of mass `1/9`, independent uniform
points, the bet-on-`p` utility, `Reflective ∧ NoCrossBranch`) with `Σ = {coin}` at the observed
table `Tone = (1, 1/2)`:

* the hypotheses of `oneStep_iff_twoStep` hold and are **derived** (`ReflectiveAt` from
  `Reflective`, `ClassInert` from `NoCrossBranch` for any class containing the observed table,
  `SigmaClassPos` from `NDHOME`);
* the `Σ`-class is the three tables pricing the coin at `1` (`card_cls`), so it has `≥ 2` tables;
* the two-step conditional **genuinely changes the value**: `EU Tone give = 5/9` while
  `twoStepEU {coin} Tone give = 2/3` (`EU_tent`, `twoStepEU_tent`);
* and the maximizer sets coincide (`crux_nonvacuous`), as the crux says.

Source: mandate T5 (the trap: "check (a) is non-vacuous on a prior where the `Σ`-class has `≥ 2`
tables and the two-step conditional genuinely changes a value").
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Tent Finset

/-- `NoCrossBranch` gives `ClassInert 𝒞 Q` for every class containing `Q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma classInert_of_noCrossBranch {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type}
    [DecidableEq A] (P : FiniteBLIPrior 𝒮 m 𝒟 A) (hN : P.NoCrossBranch) (𝒞 : Finset ↥𝒟) (Q : ↥𝒟)
    (hQ : Q ∈ 𝒞) : ClassInert P 𝒞 Q := by
  intro T hT a b ha hb
  exact hN Q T a b (fun h => hT (h ▸ hQ)) ha hb

namespace CruxTent

/-- The `{coin}`-class of `Tone` is the set of grid tables pricing the coin at `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_cls_iff (T : ↥(grid witIndex witMesh.d 1)) :
    T ∈ sigmaClass ({pW1} : Finset ↥(witIndex.S 1)) Tone ↔ T.1 pW1 = 1 := by
  rw [mem_sigmaClass_iff]
  unfold agreesOn
  simp only [Finset.mem_singleton, forall_eq]
  have : Qone pW1 = 1 := by simp [Qone]
  rw [this]

/-- **The class has three tables.**
Source: mandate T5 (the trap: a class of `≥ 2` tables)
Kind: N+
Fidelity: exact -/
lemma card_cls : ((sigmaClass ({pW1} : Finset ↥(witIndex.S 1)) Tone).card : ℚ) = 3 := by
  have h := TentSist.sum_grid_coin_tentLaw 1 (one_mem_gridVals (by norm_num))
  have e : ∀ Q ∈ grid witIndex witMesh.d 1,
      (if Q pW1 = 1 then tentLaw witMesh 0 t₀ Q else 0) =
        1 / 9 * (if Q pW1 = 1 then (1 : ℚ) else 0) := by
    intro Q hQ
    rw [tentLaw_t₀ hQ]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum] at h
  have h2 : (∑ Q ∈ grid witIndex witMesh.d 1, if Q pW1 = 1 then (1 : ℚ) else 0) = 3 := by
    linarith
  have h3 : (∑ T ∈ sigmaClass ({pW1} : Finset ↥(witIndex.S 1)) Tone, (1 : ℚ)) =
      ∑ Q ∈ grid witIndex witMesh.d 1, if Q pW1 = 1 then (1 : ℚ) else 0 := by
    rw [← Finset.sum_coe_sort (grid witIndex witMesh.d 1)
      (fun Q => if Q pW1 = 1 then (1 : ℚ) else 0)]
    unfold sigmaClass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T _
    have hiff := mem_cls_iff T
    rw [mem_sigmaClass_iff] at hiff
    by_cases h : T.1 pW1 = 1
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h3
  rw [h3, h2]

/-- The branch weight of every table under the `Tone` point is `1/9`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma bp_tent (T : ↥(grid witIndex witMesh.d 1)) : tentPrior.branchProb T Tone true = 1 / 9 := by
  rw [tentPrior_structure.1 T Tone true (tentPrior_structure.2.2.2.2.2.2.2.1 Tone true),
    stateMass_tentPrior]

/-- The value a table `T ≠ Tone` assigns to the `Tone` point is `1/2` (its own bet is independent
of the point and right half the time).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condEU_tent (T : ↥(grid witIndex witMesh.d 1)) (hT : T ≠ Tone) :
    tentPrior.condEU T Tone true = 1 / 2 := by
  unfold tentPrior
  rw [condEU_ref tentData tentData.state₀ (fun ω a => betOnP ω.2 a) tentU_home T Tone true]
  unfold condExp
  rw [integralOf_congr_fun _ _ (fun _ => (1 / 2 : ℚ)) _ (by
    intro ω hω
    have hcp : ∀ b, condPoint tentData.toPrior (tentData.state₀ ω) Tone b true = 1 / 2 := by
      intro b
      rw [hω]
      unfold condPoint
      rw [tentData.independentPoints_toPrior_of_prodLaw tentHalf tentHalf_sum rfl T Tone b true hT,
        IndepData.ppMass_toPrior, IndepData.ppMass_toPrior]
      change massOf (prodLaw tentHalf) (fun π => π T = b) *
        massOf (prodLaw tentHalf) (fun π => π Tone = true) /
        massOf (prodLaw tentHalf) (fun π => π Tone = true) = 1 / 2
      rw [IndepData.massOf_prodLaw_point tentHalf tentHalf_sum,
        IndepData.massOf_prodLaw_point tentHalf tentHalf_sum]
      simp [tentHalf]
    simp only [hcp, Fintype.sum_bool, betOnP, if_true, Bool.false_eq_true, if_false]
    ring)]
  rw [integralOf_const, mul_div_assoc, div_self (ne_of_gt (baseMass_pos T)), mul_one]

/-- **The one-step value of betting `true` at `Tone` is `5/9`**: `1/9 · 1` from the home branch and
`8/9 · 1/2` from the others.
Source: mandate T5 (the trap)
Kind: N+
Fidelity: exact
Hyps: (a) none; uses faith (through `homeEU_true`) -/
theorem EU_tent : tentPrior.EU Tone true = 5 / 9 := by
  rw [tentPrior.EU_eq_sum_branch Tone true]
  have e : ∀ T, tentPrior.branchProb T Tone true * tentPrior.condEU T Tone true =
      1 / 18 + (if T = Tone then 1 / 18 else 0) := by
    intro T
    rw [bp_tent]
    by_cases h : T = Tone
    · subst h
      rw [if_pos rfl]
      change 1 / 9 * tentPrior.homeEU Tone true = _
      rw [homeEU_true]
      simp [Qone]
      norm_num
    · rw [if_neg h, condEU_tent T h]
      norm_num
  simp only [e]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    card_grid_witness, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  norm_num

/-- **The two-step value with `Σ = {coin}` at `Tone` is `2/3`**: `1/3 · 1` from the home branch and
`2/3 · 1/2` from the two other coin-`1` tables — the conditional genuinely changes the value.
Source: mandate T5 (the trap: "the two-step conditional genuinely changes a value")
Kind: N+
Fidelity: exact
Hyps: (a) none; uses faith (through `homeEU_true`) -/
theorem twoStepEU_tent : twoStepEU tentPrior ({pW1} : Finset ↥(witIndex.S 1)) Tone true = 2 / 3 := by
  rw [twoStepEU_eq_classEU]
  have hprod := classProb_mul_classEU tentPrior (sigmaClass ({pW1} : Finset ↥(witIndex.S 1)) Tone)
    Tone true
  have hcard := card_cls
  have hcp : classProb tentPrior (sigmaClass ({pW1} : Finset ↥(witIndex.S 1)) Tone) Tone true =
      1 / 3 := by
    unfold classProb
    simp only [bp_tent]
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    norm_num
  have hsum : ∑ T ∈ sigmaClass ({pW1} : Finset ↥(witIndex.S 1)) Tone,
      tentPrior.branchProb T Tone true * tentPrior.condEU T Tone true = 2 / 9 := by
    have e : ∀ T, tentPrior.branchProb T Tone true * tentPrior.condEU T Tone true =
        1 / 18 + (if T = Tone then 1 / 18 else 0) := by
      intro T
      rw [bp_tent]
      by_cases h : T = Tone
      · subst h
        rw [if_pos rfl]
        change 1 / 9 * tentPrior.homeEU Tone true = _
        rw [homeEU_true]
        simp [Qone]
        norm_num
      · rw [if_neg h, condEU_tent T h]
        norm_num
    simp only [e]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard, Finset.sum_ite_eq',
      if_pos (mem_sigmaClass_self _ _)]
    norm_num
  rw [hcp, hsum] at hprod
  linarith

/-- **The crux is non-vacuous**: on the tent prior with `Σ = {coin}` at `Tone`, the hypotheses
of `oneStep_iff_twoStep` hold (derived from `Reflective`, `NoCrossBranch`, `NDHOME`), the `Σ`-class
has three tables, the one-step and two-step values differ (`5/9` versus `2/3`), and the maximizer
sets coincide. **Where the inertness comes from**: `ClassInert` is met through `NoCrossBranch`
(the tent's utility is home-only), which makes *every* class containing `Tone` inert, so on this
prior one-step = updateful = two-step for every `Σ` (audit round 1, adversarial item 1). The
witness where the crux bites and `branchCut` does not — `ClassInert` for the `Σ`-class but not
for `{Q}` — is the CM/PH prior of `PhCm.lean` (`PhCm.crux`: the CM class is `sigmaClass {p} CM_A`,
inert; the singleton is not; the updateful rule refuses, the one-step rule pays).
Source: mandate T5 (the trap)
Kind: N+
Fidelity: exact
Hyps: (a) none; uses faith (the values) -/
theorem crux_nonvacuous :
    ReflectiveAt tentPrior Tone ∧
      ClassInert tentPrior (sigmaClass ({pW1} : Finset ↥(witIndex.S 1)) Tone) Tone ∧
      (∀ a, SigmaClassPos tentPrior ({pW1} : Finset ↥(witIndex.S 1)) Tone a) ∧
      ((sigmaClass ({pW1} : Finset ↥(witIndex.S 1)) Tone).card : ℚ) = 3 ∧
      tentPrior.EU Tone true ≠ twoStepEU tentPrior ({pW1} : Finset ↥(witIndex.S 1)) Tone true ∧
      (∀ a, tentPrior.IsOneStepChoice Tone a ↔
        IsTwoStepChoice tentPrior ({pW1} : Finset ↥(witIndex.S 1)) Tone a) := by
  have hR : ReflectiveAt tentPrior Tone :=
    reflectiveAt_of_reflective _ tentPrior_structure.1 Tone
      (fun a => tentPrior_structure.2.2.2.2.2.2.2.1 Tone a)
  have hI : ClassInert tentPrior (sigmaClass ({pW1} : Finset ↥(witIndex.S 1)) Tone) Tone :=
    classInert_of_noCrossBranch _ tentPrior_structure.2.1 _ _ (mem_sigmaClass_self _ _)
  have hpos : ∀ a, SigmaClassPos tentPrior ({pW1} : Finset ↥(witIndex.S 1)) Tone a := by
    intro a
    unfold SigmaClassPos
    rw [massOf_congr tentPrior.μ (fun ω => by rw [← mem_sigmaClass_iff]), massOf_class]
    exact lt_of_lt_of_le (tentPrior_structure.2.2.2.2.2.2.2.2.1 Tone a)
      (Finset.single_le_sum (fun T _ => tentPrior.jointMass_nonneg T Tone a)
        (mem_sigmaClass_self _ _))
  refine ⟨hR, hI, hpos, card_cls, ?_, fun a => oneStep_iff_twoStep _ _ _ hR hI hpos a⟩
  rw [EU_tent, twoStepEU_tent]
  norm_num

end CruxTent

end Cleanroom.Bli.UdtBliSist
