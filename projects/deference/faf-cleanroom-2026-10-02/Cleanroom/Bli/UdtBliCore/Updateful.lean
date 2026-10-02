import Cleanroom.Bli.UdtBliCore.Decomposition

/-!
# `udt-bli-core` · Updateful: the updateful-behaviour lemma, exact and ε (T5, load-bearing 1)

"UDT behaves updatefully unless it has reason not to" (bli-slides-037): if a policy-point choice
at `T` neither moves the branch probabilities nor what the other branches expect, the one-step
value differs across actions exactly by the home term, so the one-step and updateful maximizer
**sets** coincide.

* `branchCut` — the source's exact per-`T` statement (bli-soto-a-019): with the two invariances
  assumed for the home `T` only, `EU T a − EU T b = μ(state = T | pp · T = a) · (homeEU T a −
  homeEU T b)`. From the three-influence split: the first two influences vanish.
* `EU_sub_EU_of_reflective_noCrossBranch` — the global form under the point-level predicates
  `Reflective ∧ NoCrossBranch`, with the constant `stateMass T`.
* `oneStep_iff_updateful` — the maximizer sets coincide at every positive-mass table.
* `eps_updateful` — the ε-form: if the invariances hold up to `ε`, every one-step choice is
  `δ`-updateful-optimal with the explicit `δ = ε · (1 + (2|𝒟| + 1) M) / ρ`, vanishing with `ε`.

Guards: `Reflective` and `NoCrossBranch` are checked **false** on the mugging prior, where the
two rules separate (`Mugging.lean`), and `Reflective` alone is checked false on the
Transparent-Newcomb-shaped prior where branch re-weighting separates them (`WitnessCorr.lean`);
the N+ inhabitant with a varying updateful argmax is the tent prior (`OfSkeleton.lean`); the
ε-form is exercised at `ε = 1/25` on `WitnessEps.lean`'s two-table prior.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

namespace FiniteBLIPrior

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-- A null cell has branch probability `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma branchProb_eq_zero_of_jointMass_eq_zero {T' T : ↥𝒟} {a : A} (h : P.jointMass T' T a = 0) :
    P.branchProb T' T a = 0 := by
  unfold branchProb; rw [h, zero_div]

/-- **The branch-cutting identity** (the source's exact statement, hypotheses for the home `T`
only): if the choice at `T` leaves every branch probability unchanged and every *other* branch's
expectation unchanged (on positive cells), then
`EU T a − EU T b = μ(state = T | pp · T = a) · (homeEU T a − homeEU T b)`.
Holds with the junk conventions (a null cell contributes nothing to either side).
Source: bli-soto-a-019 (Notion 508–511: "we can ignore any branch whose conditional expectation,
and relative branch weight, is the same given each alternative action"); bli-slides-037
Kind: C (the three-influence split `EU_sub_EU_eq_three_influences` with two terms killed by the
hypotheses; the null-cell cases are the only work)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem branchCut (T : ↥𝒟) (a b : A)
    (hbp : ∀ T', P.branchProb T' T a = P.branchProb T' T b)
    (hcross : ∀ T', T' ≠ T → 0 < P.jointMass T' T a → 0 < P.jointMass T' T b →
      P.condEU T' T a = P.condEU T' T b) :
    P.EU T a - P.EU T b = P.branchProb T T a * (P.homeEU T a - P.homeEU T b) := by
  rw [P.EU_sub_EU_eq_three_influences T a b]
  have h1 : P.reweightInfluence T a b = 0 := by
    unfold reweightInfluence
    apply Finset.sum_eq_zero
    intro T' _
    rw [hbp T', sub_self, zero_mul]
  have h2 : P.crossUtilInfluence T a b = 0 := by
    unfold crossUtilInfluence
    apply Finset.sum_eq_zero
    intro T' hT'
    have hne : T' ≠ T := Finset.ne_of_mem_erase hT'
    by_cases hb : 0 < P.jointMass T' T b
    · by_cases ha : 0 < P.jointMass T' T a
      · rw [hcross T' hne ha hb, sub_self, mul_zero]
      · have hza : P.jointMass T' T a = 0 :=
          le_antisymm (not_lt.mp ha) (P.jointMass_nonneg T' T a)
        rw [← hbp T', P.branchProb_eq_zero_of_jointMass_eq_zero hza, zero_mul]
    · have hzb : P.jointMass T' T b = 0 :=
        le_antisymm (not_lt.mp hb) (P.jointMass_nonneg T' T b)
      rw [P.branchProb_eq_zero_of_jointMass_eq_zero hzb, zero_mul]
  rw [h1, h2, zero_add, zero_add]
  unfold homeInfluence
  rw [← hbp T]
  ring

/-- **The updateful-behaviour identity under `Reflective ∧ NoCrossBranch`**:
`EU T a − EU T b = μ(state = T) · (homeEU T a − homeEU T b)` at positive policy points.
Source: bli-slides-037; bli-soto-a-019; [[bli-program]] §3.9 U3
Kind: C
Fidelity: exact
Hyps: (a) `Reflective`, `NoCrossBranch` (point level), positivity of the two points; does not
use faith -/
theorem EU_sub_EU_of_reflective_noCrossBranch (hR : P.Reflective) (hN : P.NoCrossBranch)
    (T : ↥𝒟) (a b : A) (ha : 0 < P.ppMass T a) (hb : 0 < P.ppMass T b) :
    P.EU T a - P.EU T b = P.stateMass T * (P.homeEU T a - P.homeEU T b) := by
  have hbp : ∀ T', P.branchProb T' T a = P.branchProb T' T b := fun T' => by
    rw [hR T' T a ha, hR T' T b hb]
  rw [P.branchCut T a b hbp (fun T' hne hpa hpb => hN T T' a b hne hpa hpb), hR T T a ha]

/-- **One-step = updateful, as maximizer sets** (load-bearing 1): under `NDPOL`, `Reflective` and
`NoCrossBranch`, at every table of positive mass an action is a one-step choice iff it is an
updateful choice.
Source: bli-slides-037 ("then UDT will behave in an updateful manner"); bli-soto-a-019;
[[bli-program]] §3.9 U3
Kind: P
Fidelity: exact (sets of maximizers, ties allowed)
Hyps: (a) `NDPOL`, `Reflective`, `NoCrossBranch`, `0 < stateMass T`; does not use faith -/
theorem oneStep_iff_updateful (hpol : P.NDPOL) (hR : P.Reflective) (hN : P.NoCrossBranch)
    (T : ↥𝒟) (hT : 0 < P.stateMass T) (a : A) :
    P.IsOneStepChoice T a ↔ P.IsUpdatefulChoice T a := by
  unfold IsOneStepChoice IsUpdatefulChoice
  apply forall_congr'
  intro b
  rw [← sub_nonneg, P.EU_sub_EU_of_reflective_noCrossBranch hR hN T a b (hpol T a) (hpol T b),
    mul_nonneg_iff_of_pos_left hT, sub_nonneg]

/-- **One-step policies are the updateful policies** under `NDHOME`, `Reflective`,
`NoCrossBranch` (every table then has positive mass).
Source: [[bli-program]] §3.9 U3; mandate T6 corollary
Kind: C
Fidelity: exact
Hyps: (a) `NDHOME`, `Reflective`, `NoCrossBranch`; does not use faith -/
theorem oneStepPolicy_iff_updatefulPolicy [Fintype A] [Nonempty A] (hhome : P.NDHOME)
    (hR : P.Reflective) (hN : P.NoCrossBranch) (π : Policy 𝒟 A) :
    P.IsOneStepPolicy π ↔ P.IsUpdatefulPolicy π := by
  unfold IsOneStepPolicy IsUpdatefulPolicy
  apply forall_congr'
  intro T
  exact P.oneStep_iff_updateful (NDHOME.ndpol P hhome) hR hN T (NDHOME.stateMass_pos P hhome T) (π T)

/-! ## The ε-form -/

/-- The re-weighting influence is at most `|𝒟| · ε · M` under the `ε`-invariance of the branch
probabilities and `|U| ≤ M`.
Source: none: infrastructure (mandate T5, ε-form)
Kind: L
Fidelity: n/a -/
lemma abs_reweightInfluence_le (T : ↥𝒟) (a b : A) (ε M : ℚ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hbp : ∀ T', |P.branchProb T' T a - P.branchProb T' T b| ≤ ε)
    (hU : ∀ ω, |P.U ω| ≤ M) :
    |P.reweightInfluence T a b| ≤ (Fintype.card ↥𝒟 : ℚ) * (ε * M) := by
  have hcond : ∀ T', |P.condEU T' T a| ≤ M := fun T' =>
    abs_condExp_le P.μ P.U P.μ_nonneg _ M hM (fun ω _ => hU ω)
  have hcard : ((univ.erase T).card : ℚ) ≤ (Fintype.card ↥𝒟 : ℚ) := by
    exact_mod_cast Finset.card_le_univ _
  unfold reweightInfluence
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ T' ∈ univ.erase T,
      |(P.branchProb T' T a - P.branchProb T' T b) * P.condEU T' T a| ≤ ε * M := by
    intro T' _
    rw [abs_mul]
    exact mul_le_mul (hbp T') (hcond T') (abs_nonneg _) hε
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard (mul_nonneg hε hM)

/-- The cross-branch utility influence is at most `ε + |𝒟| · ε · M` under the `ε`-invariances
(the extra `ε` is the total branch weight; a cell that is null under `a` but not under `b` is
handled by the branch-probability closeness).
Source: none: infrastructure (mandate T5, ε-form)
Kind: L
Fidelity: n/a -/
lemma abs_crossUtilInfluence_le (T : ↥𝒟) (a b : A) (ε M : ℚ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hb : 0 < P.ppMass T b)
    (hbp : ∀ T', |P.branchProb T' T a - P.branchProb T' T b| ≤ ε)
    (hcross : ∀ T', T' ≠ T → 0 < P.jointMass T' T a → 0 < P.jointMass T' T b →
      |P.condEU T' T a - P.condEU T' T b| ≤ ε)
    (hU : ∀ ω, |P.U ω| ≤ M) :
    |P.crossUtilInfluence T a b| ≤ ε + (Fintype.card ↥𝒟 : ℚ) * (ε * M) := by
  have hcond : ∀ T' c, |P.condEU T' T c| ≤ M := fun T' c =>
    abs_condExp_le P.μ P.U P.μ_nonneg _ M hM (fun ω _ => hU ω)
  have hbpnn : ∀ T' c, 0 ≤ P.branchProb T' T c := fun T' c => P.branchProb_nonneg T' T c
  have hcard : ((univ.erase T).card : ℚ) ≤ (Fintype.card ↥𝒟 : ℚ) := by
    exact_mod_cast Finset.card_le_univ _
  unfold crossUtilInfluence
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ T' ∈ univ.erase T,
      |P.branchProb T' T b * (P.condEU T' T a - P.condEU T' T b)| ≤
        ε * P.branchProb T' T b + ε * M := by
    intro T' hT'
    have hne : T' ≠ T := Finset.ne_of_mem_erase hT'
    rw [abs_mul, abs_of_nonneg (hbpnn T' b)]
    by_cases hpb : 0 < P.jointMass T' T b
    · by_cases hpa : 0 < P.jointMass T' T a
      · have h1 : P.branchProb T' T b * |P.condEU T' T a - P.condEU T' T b| ≤
            P.branchProb T' T b * ε :=
          mul_le_mul_of_nonneg_left (hcross T' hne hpa hpb) (hbpnn T' b)
        have h2 : 0 ≤ ε * M := mul_nonneg hε hM
        linarith [h1, h2]
      · have hza : P.jointMass T' T a = 0 :=
          le_antisymm (not_lt.mp hpa) (P.jointMass_nonneg T' T a)
        have hbpa : P.branchProb T' T a = 0 := P.branchProb_eq_zero_of_jointMass_eq_zero hza
        have hcEU : P.condEU T' T a = 0 := by
          unfold condEU condExp
          rw [integralOf_eq_zero_of_massOf_eq_zero P.μ P.U P.μ_nonneg _ hza, zero_div]
        have hbple : P.branchProb T' T b ≤ ε := by
          have := hbp T'
          rw [hbpa, zero_sub, abs_neg, abs_of_nonneg (hbpnn T' b)] at this
          exact this
        have h1 : P.branchProb T' T b * |P.condEU T' T a - P.condEU T' T b| ≤ ε * M := by
          rw [hcEU, zero_sub, abs_neg]
          exact mul_le_mul hbple (hcond T' b) (abs_nonneg _) hε
        have h2 : 0 ≤ ε * P.branchProb T' T b := mul_nonneg hε (hbpnn T' b)
        linarith [h1, h2]
    · have hzb : P.jointMass T' T b = 0 :=
        le_antisymm (not_lt.mp hpb) (P.jointMass_nonneg T' T b)
      have hbpb : P.branchProb T' T b = 0 := P.branchProb_eq_zero_of_jointMass_eq_zero hzb
      rw [hbpb, zero_mul, mul_zero, zero_add]
      exact mul_nonneg hε hM
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hsum : ∑ T' ∈ univ.erase T, P.branchProb T' T b ≤ 1 := by
    rw [← P.sum_branchProb T b hb]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun T' _ _ => hbpnn T' b)
  have h1 : ε * ∑ T' ∈ univ.erase T, P.branchProb T' T b ≤ ε * 1 :=
    mul_le_mul_of_nonneg_left hsum hε
  have h2 : ((univ.erase T).card : ℚ) * (ε * M) ≤ (Fintype.card ↥𝒟 : ℚ) * (ε * M) :=
    mul_le_mul_of_nonneg_right hcard (mul_nonneg hε hM)
  linarith [h1, h2]

/-- The home influence is within `ε · M` of the home term `branchProb T T a · (homeEU T a −
homeEU T b)`.
Source: none: infrastructure (mandate T5, ε-form)
Kind: L
Fidelity: n/a -/
lemma abs_homeInfluence_sub_le (T : ↥𝒟) (a b : A) (ε M : ℚ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hbp : ∀ T', |P.branchProb T' T a - P.branchProb T' T b| ≤ ε)
    (hU : ∀ ω, |P.U ω| ≤ M) :
    |P.homeInfluence T a b - P.branchProb T T a * (P.homeEU T a - P.homeEU T b)| ≤ ε * M := by
  have hcond : |P.homeEU T b| ≤ M :=
    abs_condExp_le P.μ P.U P.μ_nonneg _ M hM (fun ω _ => hU ω)
  unfold homeInfluence
  have e : P.branchProb T T a * P.homeEU T a - P.branchProb T T b * P.homeEU T b -
      P.branchProb T T a * (P.homeEU T a - P.homeEU T b) =
      (P.branchProb T T a - P.branchProb T T b) * P.homeEU T b := by ring
  rw [e, abs_mul]
  exact mul_le_mul (hbp T) hcond (abs_nonneg _) hε

/-- **The ε-form of the branch-cutting identity**: if at `T` the branch probabilities move by at
most `ε` and the other branches' expectations (on positive cells) by at most `ε`, and `|U| ≤ M`,
then the one-step difference is within `ε · (1 + (2|𝒟| + 1) M)` of the home term.
Source: bli-slides-037 ("(significantly)"); mandate T5 (the constant is this run's)
Kind: P
Fidelity: exact (finite, explicit constant)
Hyps: (a) the `ε`-invariances, `0 < ppMass T b`, `|U| ≤ M`; does not use faith -/
theorem abs_EU_sub_sub_home_le (T : ↥𝒟) (a b : A) (ε M : ℚ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hb : 0 < P.ppMass T b)
    (hbp : ∀ T', |P.branchProb T' T a - P.branchProb T' T b| ≤ ε)
    (hcross : ∀ T', T' ≠ T → 0 < P.jointMass T' T a → 0 < P.jointMass T' T b →
      |P.condEU T' T a - P.condEU T' T b| ≤ ε)
    (hU : ∀ ω, |P.U ω| ≤ M) :
    |P.EU T a - P.EU T b - P.branchProb T T a * (P.homeEU T a - P.homeEU T b)| ≤
      ε * (1 + (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M) := by
  have h1 := P.abs_reweightInfluence_le T a b ε M hε hM hbp hU
  have h2 := P.abs_crossUtilInfluence_le T a b ε M hε hM hb hbp hcross hU
  have h3 := P.abs_homeInfluence_sub_le T a b ε M hε hM hbp hU
  rw [P.EU_sub_EU_eq_three_influences T a b]
  have e : P.reweightInfluence T a b + P.crossUtilInfluence T a b + P.homeInfluence T a b -
      P.branchProb T T a * (P.homeEU T a - P.homeEU T b) =
      P.reweightInfluence T a b + P.crossUtilInfluence T a b +
        (P.homeInfluence T a b - P.branchProb T T a * (P.homeEU T a - P.homeEU T b)) := by ring
  rw [e]
  have htri := abs_add_le (P.reweightInfluence T a b + P.crossUtilInfluence T a b)
    (P.homeInfluence T a b - P.branchProb T T a * (P.homeEU T a - P.homeEU T b))
  have htri' := abs_add_le (P.reweightInfluence T a b) (P.crossUtilInfluence T a b)
  have hfinal : (Fintype.card ↥𝒟 : ℚ) * (ε * M) + (ε + (Fintype.card ↥𝒟 : ℚ) * (ε * M)) + ε * M =
      ε * (1 + (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M) := by ring
  linarith [htri, htri', h1, h2, h3, hfinal]

/-- **ε-updateful behaviour** (the ε-form of load-bearing 1): under the `ε`-invariances at `T`,
`|U| ≤ M`, positive points, and a home branch probability `≥ ρ > 0` under the chosen action, every
one-step choice `a*` is `δ`-updateful-optimal:
`homeEU T b − homeEU T a* ≤ δ` for every `b`, with the **explicit**
`δ = ε · (1 + (2|𝒟| + 1) M) / ρ`, which tends to `0` with `ε`.
Source: bli-slides-037 ("(significantly)"); [[bli-program]] §3.9 U3 ("ε-version"); the
constant is this run's (mandate T5)
Kind: P
Fidelity: exact (finite, explicit constant)
Hyps: (a) the `ε`-invariances at `T`, `NDPOL` at `T`, `|U| ≤ M`, `ρ ≤ branchProb T T a*`; does
not use faith -/
theorem eps_updateful (T : ↥𝒟) (ε M ρ : ℚ) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hpol : ∀ c, 0 < P.ppMass T c)
    (hbp : ∀ T' c d, |P.branchProb T' T c - P.branchProb T' T d| ≤ ε)
    (hcross : ∀ T' c d, T' ≠ T → 0 < P.jointMass T' T c → 0 < P.jointMass T' T d →
      |P.condEU T' T c - P.condEU T' T d| ≤ ε)
    (hU : ∀ ω, |P.U ω| ≤ M)
    (astar : A) (hstar : P.IsOneStepChoice T astar) (hρa : ρ ≤ P.branchProb T T astar) (b : A) :
    P.homeEU T b - P.homeEU T astar ≤ ε * (1 + (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M) / ρ := by
  have hD := P.abs_EU_sub_sub_home_le T astar b ε M hε hM (hpol b) (fun T' => hbp T' astar b)
    (fun T' hne hc hd => hcross T' astar b hne hc hd) hU
  have hge : 0 ≤ P.EU T astar - P.EU T b := sub_nonneg.mpr (hstar b)
  have hupp := (abs_le.mp hD).2
  have hmain : P.branchProb T T astar * (P.homeEU T b - P.homeEU T astar) ≤
      ε * (1 + (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M) := by
    linarith [hupp, hge]
  have hKnn : 0 ≤ ε * (1 + (2 * (Fintype.card ↥𝒟 : ℚ) + 1) * M) :=
    mul_nonneg hε (add_nonneg zero_le_one (mul_nonneg (by positivity) hM))
  rw [le_div_iff₀ hρ]
  by_cases hsign : P.homeEU T b - P.homeEU T astar ≤ 0
  · nlinarith [hsign, hρ.le, hKnn]
  · have hpos : 0 < P.homeEU T b - P.homeEU T astar := lt_of_not_ge hsign
    have hmul : ρ * (P.homeEU T b - P.homeEU T astar) ≤
        P.branchProb T T astar * (P.homeEU T b - P.homeEU T astar) :=
      mul_le_mul_of_nonneg_right hρa hpos.le
    linarith [hmul, hmain]

end FiniteBLIPrior

end Cleanroom.Bli.UdtBliCore
