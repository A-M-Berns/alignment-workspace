import Cleanroom.Bli.BliLinkage.InstanceB2Point
import Cleanroom.Bli.BliLinkage.LiaSupport
import Cleanroom.Bli.BliTrajectory.Partition

/-!
# `bli-linkage` — what the K3 package demands of FAF's LIA: exact finite-day coherence on
the small sentences — and why no LIA can meet it (repair round 2, audit r2 B1 of both lenses;
repair round 3, audit r3 adversarial B1 / fidelity N1: the demand counted and **refuted**)

The K3 instances at FAF's LIA (`InstanceB2.no_degenerate_linked_bli_LIA`,
`InstanceK3.no_degenerate_linked_bli_LIA_family`, and `InstanceK3Grid.no_degenerate_linked_bli_LIA_oneCoord`)
conclude `¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E5σ … ∧ E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ Degenerate …)`:
the base under `E1x` is FAF's LIA. Repair round 1 shipped `InstanceB2Point.pointMass_degenerate_of_still`
as "K3's artifact check" and wrote that the package *of those instances* is inhabited in the
no-move regime. Both round-2 auditors found that false as written: that check inhabits
`E1x (pointMass v) (pointMass v)` — base = the superbelief itself — and says nothing about
the conjunct `E1x (liaHistory (paperDP 𝗜𝚺₁)) P`. This module makes exact what that conjunct
demands (the two auditors' probes `audit-r2-probes/ExactCoherence.lean` and
`LiaPackageCoherence.lean`, adopted, plus one sharper form), and states the demand's
satisfiability as the package's second OPEN.

1. **`package_forces_falsum_zero` / `package_forces_top_one` / `package_forces_stage_theorem_one`**:
   `PCPσ atoms DP P ∧ E1x Q P` make the base `Q` agree, on every day-`n` small sentence, with a
   convex combination of stage-consistent worlds — so `Q n ⊥ = 0` on every day, `Q n ⊤ = 1`
   on every day `n ≥ 1` (`⊤` is small from day 1), and `Q n φ = 1` for every small member
   `φ` of the stage `DP.D n`: **exact, finite-day** coherence of the base on the small algebra.
2. **`lia_package_forces_top_one`** (the `marketValue` form the instances' `hmove` is written
   in) and **`lia_package_forces_top_mem_support`** (sharper): FAF's `RationalBeliefState`
   prices every sentence *outside its finite entry list* at exactly `0`
   (`RationalBeliefState.quote_eq_zero_of_not_mem`), so the package forces `⊤` to be a
   *listed key* of the LIA's day-`n` belief state `liaStates (paperDP 𝗜𝚺₁) n` on every day
   `n ≥ 1` — a structural condition on the day-`n` trading firm's strategy support — and
   likewise every small stage theorem (`lia_package_forces_stage_theorem_mem_support`).
3. **`e1x_lia_pointMass_forces_01`**: the point mass of `InstanceB2Point` cannot inhabit the
   LIA package unless the LIA is a `0/1` market on every small sentence — so the repair-r1
   artifact check could not have been about the LIA package.
4. **The demand counted** (audit r3, both probes adopted and generalized to every deductive
   process `DP`): a stage mixture prices every sentence held in *every* world — every
   propositional tautology — at exactly `1` (`coherentOn_valid_one`), and prices `φ` and `∼φ`
   to `1` (`coherentOn_add_neg`); `E1x` carries both to the base on the small sentences
   (`package_forces_valid_one`, `package_forces_pair_sum_one`); at the LIA every small
   tautology must then be a *listed key* with exact quote `1`
   (`lia_package_forces_valid_mem_support`) and every small complementary pair must have a
   listed key (`lia_package_forces_pair_listed`, `lia_package_forces_atom_or_neg_listed`). The
   chain `tautChain k := ⊤ ⋎ ⊥ ⋎ … ⋎ ⊥` (`tokenSize = 4 + 4k`, injective) puts `2^(2^n − 2)`
   small tautologies on day `n ≥ 1`, so the package forces
   `2^(2^n − 2) ≤ (liaStates DP n).support.card` (`lia_package_forces_support_card`) —
   `16384` on day `4`, `2^30` on day `5`.
5. **The refutation** (`not_lia_small_coherent_mixture_exists`, for every `DP`; at
   `paperDP 𝗜𝚺₁` the exact negation of the round-2 OPEN): `LiaSupport.liaStates_support_card_le_day4`
   bounds the LIA's day-`4` support by `2945` for every deductive process — FAF's day-`n` firm is
   the join of the `n + 1` clocked enumerated traders, each placing at most `progClock j n + 1`
   trades — so the two conjuncts `PCPσ atoms DP P ∧ E1x (liaHistory DP) P` are contradictory
   on day `4` (`lia_package_unsat`). Hence **the three K3 instances at FAF's LIA are vacuous**
   (`k3_package_at_lia_empty`; `InstanceK3Local` states each instance's conclusion with `hχ`
   and `hmove` dropped): their conclusions hold because their hypothesis package is empty, for
   a reason unrelated to `hmove`. The mandate's K3 shape — the inductor under `E1x` on all
   of `smallSet n` with a stage-coherent superbelief — is incompatible with any market whose
   day-`n` support is subexponential in `sizeBound n` (findings FR-11). What survives is the
   *local* shape `Degenerate.no_degenerate_linked_bli_lit` (`E1x` only at the pinned cell
   literals, which is all K3 ever used) and its LIA instances in `InstanceK3Local`, whose
   precondition — the LIA lists tomorrow's literal of today's cell with exact quote `1` on
   every day from some day on — is one sentence per day and is not counted out.

Items 1–3 say which package the artifact check inhabited and what the instances' package
requires (findings FR-9); items 4–5 settle that the requirement cannot be met (findings FR-11).
The mandate's K3 shape (the inductor under `E1x` with a stage-coherent `P`) is what runs into
[[STANDARDS]] §3's artifact check.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB (payout_of_holds payout_of_not_holds)

/-! ## A stage mixture prices `⊥` at `0`, `⊤` at `1`, and every stage theorem at `1` -/

/-- A stage mixture prices `⊥` at `0`.
Source: none: infrastructure (audit r2 fidelity probe `ExactCoherence.coherentOn_falsum`)
Kind: L
Fidelity: n/a -/
theorem coherentOn_falsum {D : Finset Sentence} {A : Finset ℕ} {p : Sentence → ℝ}
    (h : CoherentOn D A p) : p ⊥ = 0 := by
  obtain ⟨k, W, w, -, -, -, hrep⟩ := h
  rw [hrep ⊥ (by simp)]
  exact Finset.sum_eq_zero fun i _ => by
    rw [payout_of_not_holds (v := W i) (φ := (⊥ : Sentence)) (fun h => h), mul_zero]

/-- A stage mixture prices `⊤` at `1`.
Source: none: infrastructure (audit r2 fidelity probe `ExactCoherence.coherentOn_verum`)
Kind: L
Fidelity: n/a -/
theorem coherentOn_verum {D : Finset Sentence} {A : Finset ℕ} {p : Sentence → ℝ}
    (h : CoherentOn D A p) : p ⊤ = 1 := by
  obtain ⟨k, W, w, -, -, hsum, hrep⟩ := h
  rw [hrep ⊤ (by simp), ← hsum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [payout_of_holds (v := W i) (φ := (⊤ : Sentence)) (PCWorld.holds_top _), mul_one]

/-- **Any base carrying the K3 package prices `⊥` at exactly `0` on every day.**
Source: this run (audit r2 fidelity B1, probe `ExactCoherence.e1x_pcpσ_falsum`)
Kind: L
Fidelity: n/a -/
theorem package_forces_falsum_zero {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
    {P Q : History} (hcoh : PCPσ atoms DP P) (hE1 : E1x Q P) (n : ℕ) : Q n ⊥ = 0 := by
  rw [← hE1 n ⊥ (falsum_mem_smallSet n)]
  exact coherentOn_falsum (hcoh n)

/-- **Any base carrying the K3 package prices `⊤` at exactly `1` on every day `n ≥ 1`**
(`⊤` is small from day 1, `top_mem_smallSet`).
Source: this run (audit r2 adversarial B1, probe `LiaPackageCoherence.package_forces_top_one`)
Kind: L
Fidelity: n/a -/
theorem package_forces_top_one {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess} {P Q : History}
    (hcoh : PCPσ atoms DP P) (hE1 : E1x Q P) {n : ℕ} (hn : 1 ≤ n) : Q n ⊤ = 1 := by
  rw [← hE1 n _ (Cleanroom.Bli.BliTrajectory.top_mem_smallSet hn)]
  exact coherentOn_verum (hcoh n)

/-- **Any base carrying the K3 package prices every small member of the stage `DP.D n` at
exactly `1` on day `n`.**
Source: this run (audit r2 adversarial B1, probe `LiaPackageCoherence.package_forces_stage_theorem_one`)
Kind: L
Fidelity: n/a -/
theorem package_forces_stage_theorem_one {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
    {P Q : History} (hcoh : PCPσ atoms DP P) (hE1 : E1x Q P) (n : ℕ) {φ : Sentence}
    (hφD : φ ∈ DP.D n) (hφs : φ ∈ smallSet n) : Q n φ = 1 := by
  obtain ⟨k, W, w, hcons, -, hw1, hrep⟩ := hcoh n
  have hA : sentenceAtomCodes φ ⊆ Cleanroom.Bli.BliLinkageB.smallAtoms n ∪ atoms n :=
    (Cleanroom.Bli.BliLinkageB.atoms_subset_smallAtoms hφs).trans Finset.subset_union_left
  rw [← hE1 n _ hφs, hrep φ hA]
  have h1 : ∀ i, (W i).payout φ = 1 := fun i => payout_of_holds (hcons i φ hφD)
  simp [h1, hw1]

/-! ## At FAF's LIA -/

/-- **The K3 instances' package forces the LIA's exact rational quote of `⊥` to be `0` on
every day** — a finite-day exact price FAF does not supply.
Source: this run (audit r2 fidelity B1, probe `ExactCoherence.lia_package_forces_falsum_zero`)
Kind: L
Fidelity: n/a -/
theorem lia_package_forces_falsum_zero {atoms : ℕ → Finset ℕ} {P : History}
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE1 : E1x (liaHistory (paperDP 𝗜𝚺₁)) P) (n : ℕ) :
    liaHistory (paperDP 𝗜𝚺₁) n ⊥ = 0 :=
  package_forces_falsum_zero hcoh hE1 n

/-- **The K3 instances' package forces the LIA's exact rational quote of `⊤` to be `1` on
every day `n ≥ 1`**, in the `marketValue` form the instances' `hmove` is written in.
Source: this run (audit r2 adversarial B1, probe `LiaPackageCoherence.lia_package_forces_top_one`)
Kind: L
Fidelity: n/a -/
theorem lia_package_forces_top_one {atoms : ℕ → Finset ℕ} {P : History}
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE1 : E1x (liaHistory (paperDP 𝗜𝚺₁)) P) {n : ℕ}
    (hn : 1 ≤ n) : marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (⊤ : Sentence))) = 1 := by
  have h := package_forces_top_one hcoh hE1 hn
  rw [← marketValue_pair_cast] at h
  exact_mod_cast h

/-- **The sharper form: the package forces `⊤` to be a listed key of the LIA's day-`n` belief
state on every day `n ≥ 1`.** FAF's `RationalBeliefState` prices every sentence outside its
finite entry list at exactly `0` (`quote_eq_zero_of_not_mem`), so a sentence the day-`n`
trading firm does not list cannot be priced `1`. This turns the demand into a structural
condition on the LIA's day-`n` support.
Source: this run (repair r2); FAF `RationalBeliefState.quote_eq_zero_of_not_mem`, `liaHistory_eq_quote_cast`
Kind: L
Fidelity: n/a -/
theorem lia_package_forces_top_mem_support {atoms : ℕ → Finset ℕ} {P : History}
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE1 : E1x (liaHistory (paperDP 𝗜𝚺₁)) P) {n : ℕ}
    (hn : 1 ≤ n) : (⊤ : Sentence) ∈ (liaStates (paperDP 𝗜𝚺₁) n).support := by
  by_contra h
  have h1 := package_forces_top_one hcoh hE1 hn
  rw [liaHistory_eq_quote_cast] at h1
  change (((liaStates (paperDP 𝗜𝚺₁) n).quote ⊤ : ℚ) : ℝ) = 1 at h1
  rw [RationalBeliefState.quote_eq_zero_of_not_mem _ h] at h1
  norm_num at h1

/-- **Every small stage theorem must be a listed key of the LIA's day-`n` belief state** under
the package.
Source: this run (repair r2); FAF `RationalBeliefState.quote_eq_zero_of_not_mem`
Kind: L
Fidelity: n/a -/
theorem lia_package_forces_stage_theorem_mem_support {atoms : ℕ → Finset ℕ} {P : History}
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE1 : E1x (liaHistory (paperDP 𝗜𝚺₁)) P) (n : ℕ)
    {φ : Sentence} (hφD : φ ∈ (paperDP 𝗜𝚺₁).D n) (hφs : φ ∈ smallSet n) :
    φ ∈ (liaStates (paperDP 𝗜𝚺₁) n).support := by
  by_contra h
  have h1 := package_forces_stage_theorem_one hcoh hE1 n hφD hφs
  rw [liaHistory_eq_quote_cast] at h1
  change (((liaStates (paperDP 𝗜𝚺₁) n).quote φ : ℚ) : ℝ) = 1 at h1
  rw [RationalBeliefState.quote_eq_zero_of_not_mem _ h] at h1
  norm_num at h1

/-- **The repair-r1 artifact check's base is the point mass itself.** Had its `E1x` been the
LIA's (the K3 instances' package), every small sentence's LIA price would be `0` or `1` on
every day — far more than "the rounded table is still".
Source: this run (audit r2 adversarial B1, probe `LiaPackageCoherence.e1x_lia_pointMass_forces_01`)
Kind: L
Fidelity: n/a -/
theorem e1x_lia_pointMass_forces_01 (v : PCWorld)
    (hE1 : E1x (liaHistory (paperDP 𝗜𝚺₁)) (pointMass v)) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) :
    liaHistory (paperDP 𝗜𝚺₁) n φ = 0 ∨ liaHistory (paperDP 𝗜𝚺₁) n φ = 1 := by
  rw [← hE1 n φ hφ]
  show v.payout φ = 0 ∨ v.payout φ = 1
  by_cases h : v.Holds φ
  · exact Or.inr (payout_of_holds h)
  · exact Or.inl (payout_of_not_holds h)

/-! ## Every small tautology, and every small complementary pair (audit r3, both probes adopted) -/

/-- A mixture of worlds prices a sentence held in every world at exactly `1`.
Source: none: infrastructure (audit r3 adversarial probe `SmallTautologiesListed.coherentOn_valid_one`, adopted)
Kind: L
Fidelity: n/a -/
theorem coherentOn_valid_one {D : Finset Sentence} {A : Finset ℕ} {p : Sentence → ℝ}
    (h : CoherentOn D A p) {φ : Sentence} (hA : sentenceAtomCodes φ ⊆ A)
    (hφ : ∀ v : PCWorld, v.Holds φ) : p φ = 1 := by
  obtain ⟨k, W, w, -, -, hsum, hrep⟩ := h
  rw [hrep φ hA, ← hsum]
  exact Finset.sum_congr rfl fun i _ => by rw [payout_of_holds (hφ (W i)), mul_one]

/-- A mixture of worlds prices `φ` and `∼φ` to `1`.
Source: none: infrastructure (audit r3 fidelity probe `PairListed.coherentOn_add_neg`, adopted)
Kind: L
Fidelity: n/a -/
theorem coherentOn_add_neg {D : Finset Sentence} {A : Finset ℕ} {p : Sentence → ℝ}
    (h : CoherentOn D A p) {φ : Sentence} (hφ : sentenceAtomCodes φ ⊆ A)
    (hnφ : sentenceAtomCodes (∼φ) ⊆ A) : p φ + p (∼φ) = 1 := by
  obtain ⟨k, W, w, -, -, hsum, hrep⟩ := h
  rw [hrep φ hφ, hrep (∼φ) hnφ, ← Finset.sum_add_distrib, ← hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Cleanroom.Bli.BliLinkageB.payout_neg]; ring

/-- **Any base carrying the K3 package prices every small sentence held in every world — every
small propositional tautology — at exactly `1`.**
Source: this run (audit r3 adversarial B1, probe `SmallTautologiesListed.package_forces_valid_one`, adopted)
Kind: L
Fidelity: n/a -/
theorem package_forces_valid_one {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess} {P Q : History}
    (hcoh : PCPσ atoms DP P) (hE1 : E1x Q P) (n : ℕ) {φ : Sentence} (hφs : φ ∈ smallSet n)
    (hφ : ∀ v : PCWorld, v.Holds φ) : Q n φ = 1 := by
  rw [← hE1 n φ hφs]
  exact coherentOn_valid_one (hcoh n)
    ((Cleanroom.Bli.BliLinkageB.atoms_subset_smallAtoms hφs).trans Finset.subset_union_left) hφ

/-- **Any base carrying the K3 package prices every small complementary pair to `1`.**
Source: this run (audit r3 fidelity N1, probe `PairListed.package_forces_pair_sum_one`, adopted)
Kind: L
Fidelity: n/a -/
theorem package_forces_pair_sum_one {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
    {P Q : History} (hcoh : PCPσ atoms DP P) (hE1 : E1x Q P) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet n) (hnφ : (∼φ) ∈ smallSet n) : Q n φ + Q n (∼φ) = 1 := by
  rw [← hE1 n φ hφ, ← hE1 n _ hnφ]
  exact coherentOn_add_neg (hcoh n)
    ((Cleanroom.Bli.BliLinkageB.atoms_subset_smallAtoms hφ).trans Finset.subset_union_left)
    ((Cleanroom.Bli.BliLinkageB.atoms_subset_smallAtoms hnφ).trans Finset.subset_union_left)

/-- At FAF's LIA (over any deductive process) the exact rational quote of a small tautology is
`1` under the package.
Source: this run (audit r3 adversarial probe, adopted and generalized to every `DP`)
Kind: L
Fidelity: n/a -/
theorem lia_package_forces_valid_quote_one {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
    {P : History} (hcoh : PCPσ atoms DP P) (hE1 : E1x (liaHistory DP) P) (n : ℕ)
    {φ : Sentence} (hφs : φ ∈ smallSet n) (hφ : ∀ v : PCWorld, v.Holds φ) :
    (liaStates DP n).quote φ = 1 := by
  have h1 := package_forces_valid_one hcoh hE1 n hφs hφ
  rw [liaHistory_eq_quote_cast] at h1
  change (((liaStates DP n).quote φ : ℚ) : ℝ) = 1 at h1
  exact_mod_cast h1

/-- **Every small tautology must be a listed key of the LIA's day-`n` belief state** under the
package (FAF prices unlisted sentences at exactly `0`).
Source: this run (audit r3 adversarial B1, probe `SmallTautologiesListed.lia_package_forces_valid_mem_support`, adopted, any `DP`)
Kind: L
Fidelity: n/a -/
theorem lia_package_forces_valid_mem_support {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
    {P : History} (hcoh : PCPσ atoms DP P) (hE1 : E1x (liaHistory DP) P) (n : ℕ)
    {φ : Sentence} (hφs : φ ∈ smallSet n) (hφ : ∀ v : PCWorld, v.Holds φ) :
    φ ∈ (liaStates DP n).support := by
  by_contra h
  have h1 := lia_package_forces_valid_quote_one hcoh hE1 n hφs hφ
  rw [RationalBeliefState.quote_eq_zero_of_not_mem _ h] at h1
  norm_num at h1

/-- **Every small complementary pair `(φ, ∼φ)` must have a listed key** in the LIA's day-`n`
belief state under the package.
Source: this run (audit r3 fidelity N1, probe `PairListed.lia_package_forces_pair_listed`, adopted, any `DP`)
Kind: L
Fidelity: n/a -/
theorem lia_package_forces_pair_listed {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
    {P : History} (hcoh : PCPσ atoms DP P) (hE1 : E1x (liaHistory DP) P) (n : ℕ)
    {φ : Sentence} (hφ : φ ∈ smallSet n) (hnφ : (∼φ) ∈ smallSet n) :
    φ ∈ (liaStates DP n).support ∨ (∼φ) ∈ (liaStates DP n).support := by
  by_contra h
  push Not at h
  have h1 := package_forces_pair_sum_one hcoh hE1 n hφ hnφ
  rw [liaHistory_eq_quote_cast, liaHistory_eq_quote_cast] at h1
  change (((liaStates DP n).quote φ : ℚ) : ℝ) + (((liaStates DP n).quote (∼φ) : ℚ) : ℝ) = 1 at h1
  rw [RationalBeliefState.quote_eq_zero_of_not_mem _ h.1,
    RationalBeliefState.quote_eq_zero_of_not_mem _ h.2] at h1
  norm_num at h1

/-- An atom and its negation are both small on day `n` once the atom's base-4 digit length
leaves room for the negation's three tokens.
Source: none: infrastructure (audit r3 fidelity probe `PairListed.atom_pair_small`, adopted)
Kind: L
Fidelity: n/a -/
theorem atom_pair_small (n a : ℕ) (h : (natDigits4 (a + 5)).length + 4 ≤ sizeBound n) :
    Formula.atom a ∈ smallSet n ∧ (∼ Formula.atom a) ∈ smallSet n := by
  constructor
  · rw [mem_smallSet]; unfold SmallOn; rw [tokenSize_atom]; omega
  · rw [mem_smallSet]; unfold SmallOn; rw [tokenSize_neg, tokenSize_atom]; omega

/-- On every day `n`, every atom `a` with digit length `≤ sizeBound n − 4` must be listed by
the LIA's day-`n` belief state, or its negation must (more than sixteen million atoms on
day `2`).
Source: this run (audit r3 fidelity N1, probe `PairListed.lia_package_forces_atom_or_neg_listed`, adopted, any `DP`)
Kind: L
Fidelity: n/a -/
theorem lia_package_forces_atom_or_neg_listed {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
    {P : History} (hcoh : PCPσ atoms DP P) (hE1 : E1x (liaHistory DP) P) (n a : ℕ)
    (h : (natDigits4 (a + 5)).length + 4 ≤ sizeBound n) :
    Formula.atom a ∈ (liaStates DP n).support ∨ (∼ Formula.atom a) ∈ (liaStates DP n).support :=
  lia_package_forces_pair_listed hcoh hE1 n (atom_pair_small n a h).1 (atom_pair_small n a h).2

/-! ## The size of the demand: a chain of small tautologies -/

/-- `tautChain k` is `⊤` with `k` disjuncts `⊥` appended.
Source: none: infrastructure (audit r3 adversarial probe, adopted)
Kind: D
Fidelity: n/a -/
def tautChain : ℕ → Sentence
  | 0 => (⊤ : Sentence)
  | k + 1 => tautChain k ⋎ ⊥

/-- Every world holds every member of the chain.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_tautChain (v : PCWorld) : ∀ k, v.Holds (tautChain k)
  | 0 => PCWorld.holds_top v
  | k + 1 => (PCWorld.holds_or v _ _).2 (Or.inl (holds_tautChain v k))

/-- `tokenSize (tautChain k) = 4 + 4k` (bli-found's `tokenSize_verum`/`_or`/`_falsum`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tokenSize_tautChain : ∀ k, tokenSize (tautChain k) = 4 + 4 * k
  | 0 => tokenSize_verum
  | k + 1 => by
    show tokenSize (tautChain k ⋎ ⊥) = 4 + 4 * (k + 1)
    rw [tokenSize_or, tokenSize_tautChain k, tokenSize_falsum]
    ring

/-- The chain's members are pairwise distinct (their sizes differ).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tautChain_injective : Function.Injective tautChain := by
  intro k k' h
  have := congrArg tokenSize h
  rw [tokenSize_tautChain, tokenSize_tautChain] at this
  omega

/-- `tautChain k` is small on day `n` once `4 + 4k ≤ sizeBound n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tautChain_mem_smallSet {n k : ℕ} (h : 4 + 4 * k ≤ sizeBound n) :
    tautChain k ∈ smallSet n := by
  rw [mem_smallSet]
  unfold SmallOn
  rw [tokenSize_tautChain]
  exact h

/-- `sizeBound n = 2^(2^n) = 4 · 2^(2^n − 2)` for `n ≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sizeBound_eq_four_mul (n : ℕ) (hn : 1 ≤ n) : sizeBound n = 4 * 2 ^ (2 ^ n - 2) := by
  unfold sizeBound
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 2 := ⟨2 ^ n - 2, (Nat.sub_add_cancel h2).symm⟩
  rw [hm, Nat.add_sub_cancel, pow_add]
  ring

/-- **Under the K3 package the LIA's day-`n` belief state lists at least `2^(2^n − 2)`
sentences, for every `n ≥ 1`** — all tautologies, all quoted exactly `1` (`16384` on day `4`,
`2^30` on day `5`, `2^62` on day `6`).
Source: this run (audit r3 adversarial B1, probe `SmallTautologiesListed.lia_package_forces_support_card`, adopted, any `DP`)
Kind: P
Fidelity: n/a -/
theorem lia_package_forces_support_card {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
    {P : History} (hcoh : PCPσ atoms DP P) (hE1 : E1x (liaHistory DP) P) {n : ℕ}
    (hn : 1 ≤ n) : 2 ^ (2 ^ n - 2) ≤ (liaStates DP n).support.card := by
  have hsub : (Finset.range (2 ^ (2 ^ n - 2))).image tautChain ⊆ (liaStates DP n).support := by
    intro φ hφ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hφ
    rw [Finset.mem_range] at hk
    refine lia_package_forces_valid_mem_support hcoh hE1 n (tautChain_mem_smallSet ?_)
      (fun v => holds_tautChain v k)
    rw [sizeBound_eq_four_mul n hn]
    generalize 2 ^ (2 ^ n - 2) = K at hk ⊢
    omega
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ tautChain_injective, Finset.card_range] at this

/-! ## The refutation: no deductive process makes FAF's LIA exactly small-coherent -/

/-- **The K3 package at FAF's LIA is unsatisfiable, for every deductive process**: on day `4`
the package demands `2^14 = 16384` listed tautologies (`lia_package_forces_support_card`)
while the LIA lists at most `2945` sentences (`LiaSupport.liaStates_support_card_le_day4`, the
day-`4` value of the firm's clock bound). The contradiction is on day `4` already; the gap
is doubly exponential against polynomial on every later day.
Source: this run (repair r3; audit r3 adversarial B1 "fix (iv)", the plumbing step closed in `LiaSupport`)
Kind: P
Fidelity: n/a
Hyps: (a) -/
theorem lia_package_unsat (DP : DeductiveProcess) {atoms : ℕ → Finset ℕ} {P : History}
    (hcoh : PCPσ atoms DP P) (hE1 : E1x (liaHistory DP) P) : False := by
  have h1 := lia_package_forces_support_card hcoh hE1 (n := 4) (by norm_num)
  have h2 := liaStates_support_card_le_day4 DP
  norm_num at h1
  omega

/-- **REFUTED (the round-2 OPEN, for every deductive process): no `P` is a stage-world
mixture on the small sentences that agrees with FAF's LIA there.** At `paperDP 𝗜𝚺₁` this is
the exact negation of the statement listed OPEN in repair round 2 as
`lia_small_coherent_mixture_exists` ("unknown in both directions"); it is false, by counting
listed keys. Consequently the three K3 instances at FAF's LIA
(`InstanceB2.no_degenerate_linked_bli_LIA`, `InstanceK3.no_degenerate_linked_bli_LIA_family`,
`InstanceK3Grid.no_degenerate_linked_bli_LIA_oneCoord`) are **vacuous**: their conclusions
hold with `hχ` and `hmove` dropped (`InstanceK3Local`), for a reason unrelated to the moves.
Source: this run (repair r3); [[STANDARDS]] §3 (artifact check for impossibility results); audit r2 B1 (both lenses), audit r3 adversarial B1 / fidelity N1; mandate Known issue 7
Kind: P
Fidelity: exact (the negation of the OPEN's statement, generalized from `paperDP 𝗜𝚺₁` to every `DP`)
Hyps: (a) -/
theorem not_lia_small_coherent_mixture_exists (DP : DeductiveProcess) :
    ¬ ∃ (atoms : ℕ → Finset ℕ) (P : History), PCPσ atoms DP P ∧ E1x (liaHistory DP) P :=
  fun ⟨_, _, hcoh, hE1⟩ => lia_package_unsat DP hcoh hE1

/-- **Any package containing `PCPσ atoms DP P` and `E1x (liaHistory DP) P` is empty**, whatever
the other conjuncts — the shape of every K3 instance at FAF's LIA.
Source: this run (repair r3)
Kind: L
Fidelity: n/a -/
theorem k3_package_at_lia_empty (DP : DeductiveProcess) {atoms : ℕ → Finset ℕ} {P : History}
    (A B : Prop) : ¬ (PCPσ atoms DP P ∧ A ∧ E1x (liaHistory DP) P ∧ B) :=
  fun ⟨hcoh, _, hE1, _⟩ => lia_package_unsat DP hcoh hE1

end Cleanroom.Bli.BliLinkage
