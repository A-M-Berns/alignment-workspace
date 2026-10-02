import Cleanroom.Bli.BliLinkage.InstanceB2
import LogicalInduction.Properties.AffineCoherence

/-!
# `bli-linkage` — the B2 package on the fixed grid, inhabited: the point mass on a
completed-theory world (repair round 1, adversarial B2)

Round 0 graded the B2 instance of record (`InstanceB2.determination_B2`) "N− by necessity" on
the strength of `charged_eq_tbl01` (any inhabitant is a point mass on `tbl 0 1`) — an upper
bound on the support, not a witness. The adversarial audit (B2) was right that no declaration
exhibited an inhabitant. This module builds the one `charged_eq_tbl01` allows.

**What is proved.** For any completed-theory world `v` of `paperDP 𝗜𝚺₁`
(`paperDP_nonvacuous`), the point mass `pointMass v` satisfies, unconditionally,
`PCPσTheory` (hence `PCPσ`) on every atom set, `E5σ` at the B2 state sentence over the fixed
grid with any representatives (exactly the actual rounded table holds in `v`,
`fixedStates_decided`), and `E1x` with itself. It satisfies `E2xσIdx` over `fixedSystemR rep01`
on the index `[⌜⊥⌝, ⌜⊤⌝]` **exactly when the LIA's rounded prices of `⊥` and `⊤` are `0` and `1`
on every day `m ≥ 1`** (`Tbl01At m`): faith at the listed `⊥` reads
`v.payout (⊥ ⋏ σ_actual) = rep01 (roundedBot m) · 1`, i.e. `0 = rep01 (roundedBot m)`, and at
`⊤` reads `1 = rep01 (roundedTop m)`. So the full package of `determination_B2` at `rep01` is
inhabited under `∀ m ≥ 1, Tbl01At m` (`determination_B2_pointMass`), and — by FAF's
provability induction on the constant families `⊤`/`⊥` (`lic_provind_true`/`_false`) — `Tbl01At m`
holds for every `m` from some day `N` on (`tbl01_eventually`). **What is not proved**: that
`Tbl01At` holds on the finite initial segment `1 ≤ m < N` (the LIA's day-`m` prices of `⊥`/`⊤`
at small `m` are opaque), hence the package is not shown inhabited *unconditionally*; nor is a
stage-level two-state inhabitant built (that would need the day-`(n+1)` literals shown absent
from `D n`, the check the mandate flagged). The ledger row says exactly this.

**N− by construction, and why.** The point mass charges one state; `charged_eq_tbl01` shows no
inhabitant of this package on this index charges more. The non-degenerate N+ of the
determination theorem lives in the abstract witness `Trilemma.determination_package_inhabited`
(an uncertain coordinate), as before.

Also here (repair r1, fidelity N7 / adversarial N1; **corrected in repair r2**, audit r2 B1
of both lenses): `pointMass_degenerate_of_still` / `pointMass_degenerate_eventually` show that
the four predicates `PCPσ ∧ E5σ ∧ E1x ∧ Degenerate` with `deg n := actualCode n` are jointly
satisfiable **with the base equal to the superbelief** (`E1x (pointMass v) (pointMass v)`) in
the no-move regime — a check that the superbelief-side predicates are not contradictory on
their own. It is **not** an inhabitant of the package of `InstanceB2.no_degenerate_linked_bli_LIA`
or `InstanceK3.no_degenerate_linked_bli_LIA_family` (base `liaHistory (paperDP 𝗜𝚺₁)`), nor of
the abstract `Degenerate.no_degenerate_linked_bli` (`[IsLogicalInductor Q DP]`): those packages
force exact finite-day coherence of the base on the small sentences (`LiaPackage`), which
FAF's LIA cannot meet on day `4` or later (`LiaPackage.not_lia_small_coherent_mixture_exists`,
repair r3): the LIA instances' packages are empty.
Repair round 1's sentence "the package is empty exactly because of the moves" was
unestablished for every theorem it was attached to and is withdrawn. The sharp form of the
conditional witness's gap (audit r2 adversarial N1) is `pointMass_faith_forces_rep`: no
day-dependent `rep` buys the initial-segment condition back.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset Filter
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB (fixedCF fixedSystemR σB2 mem_fixedStates_iff entryOf_tbl_bot
  entryOf_tbl_top mem_witnessIndex_iff payout_and payout_of_holds payout_of_not_holds)

/-! ## The point mass -/

/-- The point-mass market on a world: `P n φ := v.payout φ` on every day.
Source: none: infrastructure (attempt A's `Liar.pointP`, restated)
Kind: D
Fidelity: n/a -/
noncomputable def pointMass (v : PCWorld) : History := fun _ φ => v.payout φ

/-- `pointMass` unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma pointMass_apply (v : PCWorld) (n : ℕ) (φ : Sentence) :
    pointMass v n φ = v.payout φ := rfl

/-- No world holds `⊥`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_holds_falsum (v : PCWorld) : ¬ v.Holds (⊥ : Sentence) := fun h => h

/-- The point mass on a completed-theory world is coherent relative to the completed theory
on every atom set (one world, weight one).
Source: mandate § Definitions (`PCPσTheory`); attempt A `Liar.scoped_faith_consistent` (the same step)
Kind: L
Fidelity: n/a -/
theorem pointMass_pcpσTheory (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁))
    (atoms : ℕ → Finset ℕ) : PCPσTheory atoms (paperDP 𝗜𝚺₁) (pointMass v) :=
  fun _ => ⟨1, fun _ => v, fun _ => 1, fun _ => hv, fun _ => zero_le_one, by simp,
    fun φ _ => by simp [pointMass]⟩

/-- Hence stage-coherent on every day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pointMass_pcpσ (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁))
    (atoms : ℕ → Finset ℕ) : PCPσ atoms (paperDP 𝗜𝚺₁) (pointMass v) :=
  Cleanroom.Bli.BliLinkageB.PCPσTheory.toPCPσ (pointMass_pcpσTheory v hv atoms)

/-- In a completed-theory world the payout of a fixed table's state sentence is the indicator
of "this is the actual rounded table" (`fixedStates_decided`).
Source: bli-found `Grid.fixedStates_decided`
Kind: L
Fidelity: n/a -/
lemma payout_σB2_fixed (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) (m : ℕ)
    {q : ℕ} (hq : q ∈ fixedStates m) :
    v.payout (σB2 m q) = if q = actualCode 𝗜𝚺₁ halfRound witnessIndex m then 1 else 0 := by
  by_cases h : q = actualCode 𝗜𝚺₁ halfRound witnessIndex m
  · rw [if_pos h]; exact payout_of_holds ((fixedStates_decided m v hv q hq).2 h)
  · rw [if_neg h]
    exact payout_of_not_holds fun hh => h ((fixedStates_decided m v hv q hq).1 hh)

/-- **The point mass partitions at the B2 state sentence over the fixed grid**, for any
representatives: exactly the actual rounded table holds in `v`.
Source: mandate K1/K2 (`E5σ`); bli-found `Grid.fixedStates_decided`
Kind: L
Fidelity: n/a -/
theorem pointMass_e5σ (rep : ℕ → ℕ → ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) : E5σ σB2 (fixedSystemR rep) (pointMass v) := by
  intro n
  constructor
  · show ∑ q ∈ fixedStates (n + 1), v.payout (σB2 (n + 1) q) = 1
    rw [Finset.sum_eq_single_of_mem (actualCode 𝗜𝚺₁ halfRound witnessIndex (n + 1))
      (actualCode_mem_fixedStates (n + 1))]
    · rw [payout_σB2_fixed v hv (n + 1) (actualCode_mem_fixedStates (n + 1)), if_pos rfl]
    · intro q hq hne
      rw [payout_σB2_fixed v hv (n + 1) hq, if_neg hne]
  · intro q₁ hq₁ q₂ hq₂ hne
    show v.payout (σB2 (n + 1) q₁ ⋏ σB2 (n + 1) q₂) = 0
    rw [payout_and, payout_σB2_fixed v hv (n + 1) hq₁, payout_σB2_fixed v hv (n + 1) hq₂]
    by_cases h1 : q₁ = actualCode 𝗜𝚺₁ halfRound witnessIndex (n + 1)
    · rw [if_pos h1, if_neg fun h2 => hne (h1.trans h2.symm), mul_zero]
    · rw [if_neg h1, zero_mul]

/-- The point mass agrees with itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pointMass_e1x (v : PCWorld) : E1x (pointMass v) (pointMass v) := fun _ _ _ => rfl

/-! ## Faith on `[⌜⊥⌝, ⌜⊤⌝]` at `rep01`: the rounded-price condition -/

/-- **The rounded-price condition of day `m`**: the LIA's `halfRound` cell of `⊥` is `0` and of
`⊤` is `1` — i.e. the actual rounded table of day `m` is `tbl 0 1`.
Source: this run (audit r1 adversarial B2); `InstanceB2.charged_eq_tbl01`
Kind: D
Fidelity: n/a -/
def Tbl01At (m : ℕ) : Prop := roundedBot m = 0 ∧ roundedTop m = 1

/-- Under the condition the actual rounded table is `tbl 0 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actualCode_eq_tbl01 {m : ℕ} (h : Tbl01At m) :
    actualCode 𝗜𝚺₁ halfRound witnessIndex m = Encodable.encode (tbl 0 1) := by
  unfold actualCode
  rw [actualTable_eq_tbl, h.1, h.2]

/-- A fixed table's value at `⊥` is the representative of its first entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fixedSystemR_val_bot (rep : ℕ → ℕ → ℚ) (m a b : ℕ) :
    (fixedSystemR rep).val m (Encodable.encode (tbl a b)) ⊥ = ((rep m a : ℚ) : ℝ) := by
  show ((((entryOf (Encodable.encode (⊥ : Sentence)) (tableOfCode _)).map (rep m)).getD 0 :
    ℚ) : ℝ) = _
  rw [tableOfCode_encode, entryOf_tbl_bot]
  rfl

/-- A fixed table's value at `⊤` is the representative of its second entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fixedSystemR_val_top (rep : ℕ → ℕ → ℚ) (m a b : ℕ) :
    (fixedSystemR rep).val m (Encodable.encode (tbl a b)) ⊤ = ((rep m b : ℚ) : ℝ) := by
  show ((((entryOf (Encodable.encode (⊤ : Sentence)) (tableOfCode _)).map (rep m)).getD 0 :
    ℚ) : ℝ) = _
  rw [tableOfCode_encode, entryOf_tbl_top]
  rfl

/-- **The point mass has exact faith on the index at `rep01` under the rounded-price
condition on every day `m ≥ 1`**: faith at `⊥` on the actual candidate reads
`0 = rep01 (roundedBot m)` and at `⊤` reads `1 = rep01 (roundedTop m)`; on non-actual
candidates both sides vanish.
Source: mandate K2 (`E2xσ` at `(n, m, q, c)`); this run (audit r1 adversarial B2)
Kind: L
Fidelity: n/a -/
theorem pointMass_e2xσIdx (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁))
    (hact : ∀ m, 1 ≤ m → Tbl01At m) :
    E2xσIdx σB2 witnessIndex (fixedSystemR AttemptA.B2.rep01) (pointMass v) := by
  intro n m hnm q hq c hc _
  show v.payout (sentenceOfCode c ⋏ σB2 m q) =
    (fixedSystemR AttemptA.B2.rep01).val m q (sentenceOfCode c) * v.payout (σB2 m q)
  rw [payout_and, payout_σB2_fixed v hv m hq]
  by_cases hqa : q = actualCode 𝗜𝚺₁ halfRound witnessIndex m
  · rw [if_pos hqa, mul_one, mul_one, hqa, actualCode_eq_tbl01 (hact m (by omega))]
    rcases mem_witnessIndex_iff.1 hc with rfl | rfl
    · rw [sentenceOfCode_encode, fixedSystemR_val_bot, payout_of_not_holds (not_holds_falsum v)]
      simp [AttemptA.B2.rep01]
    · rw [sentenceOfCode_encode, fixedSystemR_val_top, payout_of_holds (PCWorld.holds_top v)]
      simp [AttemptA.B2.rep01]
  · rw [if_neg hqa, mul_zero, mul_zero]

/-- **The B2 package of record at `rep01` is inhabited by the point mass on any
completed-theory world, under the rounded-price condition on every day `m ≥ 1`** — and the
determination theorem's conclusion `D_NNUcell` then holds for it. **N−** (one state charged),
which `charged_eq_tbl01` shows is the only shape an inhabitant of this package on this index
can have. The condition holds from some day on (`tbl01_eventually`); on the finite initial
segment it is not established, so the package is not shown inhabited unconditionally (the
module docstring says what that would need).
Source: mandate K2 (judged item 1, "N+"); [[STANDARDS]] §3; this run (audit r1 adversarial B2)
Kind: N-
Fidelity: n/a (point mass; conditional on `Tbl01At` on every day `m ≥ 1`)
Hyps: (a); `hact` is the condition (true from some day on, `tbl01_eventually`; open on the initial segment) -/
theorem determination_B2_pointMass (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁))
    (hact : ∀ m, 1 ≤ m → Tbl01At m) :
    PCPσ (stateAtoms σB2 (fixedSystemR AttemptA.B2.rep01)) (paperDP 𝗜𝚺₁) (pointMass v) ∧
      E5σ σB2 (fixedSystemR AttemptA.B2.rep01) (pointMass v) ∧
      E1x (pointMass v) (pointMass v) ∧
      E2xσIdx σB2 witnessIndex (fixedSystemR AttemptA.B2.rep01) (pointMass v) ∧
      D_NNUcell (fixedCF AttemptA.B2.rep01) witnessIndex (pointMass v) := by
  have hcoh := pointMass_pcpσ v hv (stateAtoms σB2 (fixedSystemR AttemptA.B2.rep01))
  have hE5 := pointMass_e5σ AttemptA.B2.rep01 v hv
  have hE2 := pointMass_e2xσIdx v hv hact
  exact ⟨hcoh, hE5, pointMass_e1x v, hE2,
    determination_B2 AttemptA.B2.rep01 (fun _ => Finset.Subset.refl _) hcoh hE5 (pointMass_e1x v)
      hE2⟩

/-! ## The rounded-price condition holds from some day on (provability induction) -/

/-- The LIA's exact quote of a sentence, as a real, is its `liaHistory` price.
Source: bli-found `paperQuote_eq_liaHistory`
Kind: L
Fidelity: n/a -/
lemma marketValue_pair_cast (m : ℕ) (φ : Sentence) :
    ((marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode φ)) : ℚ) : ℝ) =
      liaHistory (paperDP 𝗜𝚺₁) m φ := by
  rw [paperQuote_eq_liaHistory]
  simp [marketValue]

/-- **From some day on the LIA's rounded prices of `⊥` and `⊤` are `0` and `1`**: provability
induction on the constant families (`lic_provind_false` at `⊥`, `lic_provind_true` at `⊤`)
puts the prices within `1/4` of `0` and `1` eventually, which `halfRound` reads as cells `0`
and `1`. `∃ N` only.
Source: FAF `thm:provind` (`lic_provind_true`/`_false`); this run (audit r1 adversarial B2, "discharge `hact` for large days")
Kind: C
Fidelity: exact (`∃ N`, no numeral)
Hyps: (a) -/
theorem tbl01_eventually : ∃ N, ∀ m ≥ N, Tbl01At m := by
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) := paperLIA 𝗜𝚺₁
  have hT := lic_provind_true (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) (fun _ => (⊤ : Sentence))
    (MachineSentenceCodes.const _) (fun _ v _ => PCWorld.holds_top v) (paperDP_hworld 𝗜𝚺₁)
  have hB := lic_provind_false (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) (fun _ => (⊥ : Sentence))
    (MachineSentenceCodes.const _) (fun _ v _ => (PCWorld.holds_neg v _).2 (not_holds_falsum v))
    (paperDP_hworld 𝗜𝚺₁)
  rw [asympEq_iff_eventuallyWithin] at hT hB
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hT (1 / 4) (by norm_num))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (hB (1 / 4) (by norm_num))
  refine ⟨max N₁ N₂, fun m hm => ⟨?_, ?_⟩⟩
  · have h := hN₂ m (le_of_max_le_right hm)
    have hx : ((marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode (⊥ : Sentence))) : ℚ) : ℝ) < 1 / 2 := by
      rw [marketValue_pair_cast]
      have := (abs_le.1 h).2
      linarith
    have hx' : marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode (⊥ : Sentence))) < 1 / 2 := by
      have h2 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
      rw [← Rat.cast_lt (K := ℝ), h2]
      exact hx
    unfold roundedBot halfRound
    rw [if_pos hx']
  · have h := hN₁ m (le_of_max_le_left hm)
    have hx : ¬ ((marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode (⊤ : Sentence))) : ℚ) : ℝ) < 1 / 2 := by
      rw [marketValue_pair_cast]
      have := (abs_le.1 h).1
      intro hlt
      linarith
    have hx' : ¬ marketValue 𝗜𝚺₁ (Nat.pair m (Encodable.encode (⊤ : Sentence))) < 1 / 2 := by
      have h2 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
      rw [← Rat.cast_lt (K := ℝ), h2]
      exact hx
    unfold roundedTop halfRound
    rw [if_neg hx']

/-! ## The superbelief-side predicates in the no-move regime (base = the point mass itself) -/

/-- **With the base equal to the superbelief, the four predicates are jointly satisfiable
whenever the actual rounded table is still** (`deg n := actualCode n`, today's rounded table
re-listed, the K3 shape): `PCPσ`, `E5σ`, `E1x (pointMass v) (pointMass v)` unconditionally,
and `Degenerate` because `v` holds tomorrow's actual state, which is today's when the table
does not move. **This is not an inhabitant of any K3 instance's package**: those have the
LIA (or an `IsLogicalInductor`) under `E1x`, and the point mass cannot carry that conjunct
unless the LIA is a `0/1` market on the small sentences (`LiaPackage.e1x_lia_pointMass_forces_01`);
the K3 packages at the LIA are in fact empty (`LiaPackage.not_lia_small_coherent_mixture_exists`,
repair r3).
Source: [[STANDARDS]] §3 (artifact check, at the superbelief side only); this run (audit r1 fidelity N7, adversarial N1; corrected audit r2 B1)
Kind: N-
Fidelity: n/a (point mass; `P = Q`; conditional on the table being still on every day; base not an inductor)
Hyps: (a); `hstill` is the no-move condition -/
theorem pointMass_degenerate_of_still (rep : ℕ → ℕ → ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁))
    (hstill : ∀ n, actualCode 𝗜𝚺₁ halfRound witnessIndex (n + 1) =
      actualCode 𝗜𝚺₁ halfRound witnessIndex n) :
    PCPσ (stateAtoms σB2 (fixedSystemR rep)) (paperDP 𝗜𝚺₁) (pointMass v) ∧
      E5σ σB2 (fixedSystemR rep) (pointMass v) ∧ E1x (pointMass v) (pointMass v) ∧
      Degenerate σB2 (pointMass v) (actualCode 𝗜𝚺₁ halfRound witnessIndex) := by
  refine ⟨pointMass_pcpσ v hv _, pointMass_e5σ rep v hv, pointMass_e1x v, fun n => ?_⟩
  show v.payout (σB2 (n + 1) (actualCode 𝗜𝚺₁ halfRound witnessIndex n)) = 1
  rw [← hstill n]
  exact payout_of_holds
    (stateSentence_actual_holds 𝗜𝚺₁ halfRound halfRound_computable witnessIndex (n + 1) v hv)

/-- The no-move condition holds from some day on (both rounded prices settle,
`tbl01_eventually`), so the point mass satisfies the `Degenerate` clause on every late day.
Source: this run (audit r1 fidelity N7, adversarial N1)
Kind: L
Fidelity: n/a -/
theorem pointMass_degenerate_eventually (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    ∃ N, ∀ n ≥ N, pointMass v n (σB2 (n + 1) (actualCode 𝗜𝚺₁ halfRound witnessIndex n)) = 1 := by
  obtain ⟨N, hN⟩ := tbl01_eventually
  refine ⟨N, fun n hn => ?_⟩
  show v.payout (σB2 (n + 1) (actualCode 𝗜𝚺₁ halfRound witnessIndex n)) = 1
  rw [actualCode_eq_tbl01 (hN n hn), ← actualCode_eq_tbl01 (hN (n + 1) (by omega))]
  exact payout_of_holds
    (stateSentence_actual_holds 𝗜𝚺₁ halfRound halfRound_computable witnessIndex (n + 1) v hv)

/-! ## The initial-segment condition is sharp: no representatives buy it back -/

/-- **For the point mass at any `rep`, faith on the index pins the representatives of the
actual cells of `⊥` and `⊤` to `0` and `1` on every day `m ≥ 1`.** So on any day `m ≥ 1` where
the LIA rounds `⊥` and `⊤` to the same cell, no `rep` and no world make a point mass an
inhabitant of `determination_B2`'s package on `witnessIndex`: the open condition of
`determination_B2_pointMass` is exactly "the LIA never rounds `⊥` and `⊤` to the same side of
`1/2` on a day `≥ 1`", and the only route around it is a stage-level inhabitant (not built).
Source: this run (audit r2 adversarial N1, probe `PointMassRepSharp.pointMass_faith_forces_rep`)
Kind: P (sharpness of the conditional witness's condition)
Fidelity: exact
Hyps: (a) -/
theorem pointMass_faith_forces_rep (rep : ℕ → ℕ → ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁))
    (hE2 : E2xσIdx σB2 witnessIndex (fixedSystemR rep) (pointMass v)) (m : ℕ) (hm : 1 ≤ m) :
    rep m (roundedBot m) = 0 ∧ rep m (roundedTop m) = 1 := by
  have hq : actualCode 𝗜𝚺₁ halfRound witnessIndex m ∈ fixedStates m := actualCode_mem_fixedStates m
  have hact : actualCode 𝗜𝚺₁ halfRound witnessIndex m =
      Encodable.encode (tbl (roundedBot m) (roundedTop m)) := by
    unfold actualCode; rw [actualTable_eq_tbl]
  have hσ : v.payout (σB2 m (actualCode 𝗜𝚺₁ halfRound witnessIndex m)) = 1 := by
    rw [payout_σB2_fixed v hv m hq, if_pos rfl]
  constructor
  · have h := hE2 (m - 1) m (by omega) _ hq (Encodable.encode (⊥ : Sentence))
      (by simp [witnessIndex]) (by rw [sentenceOfCode_encode]; exact falsum_mem_Sminus _ _)
    rw [sentenceOfCode_encode] at h
    change v.payout (⊥ ⋏ σB2 m _) = (fixedSystemR rep).val m _ ⊥ * v.payout (σB2 m _) at h
    rw [hσ, mul_one, payout_and, payout_of_not_holds (not_holds_falsum v), zero_mul, hact,
      fixedSystemR_val_bot] at h
    exact_mod_cast h.symm
  · have h := hE2 (m - 1) m (by omega) _ hq (Encodable.encode (⊤ : Sentence))
      (by simp [witnessIndex])
      (by rw [sentenceOfCode_encode]; exact Cleanroom.Bli.BliLinkageB.verum_mem_Sminus hm _)
    rw [sentenceOfCode_encode] at h
    change v.payout (⊤ ⋏ σB2 m _) = (fixedSystemR rep).val m _ ⊤ * v.payout (σB2 m _) at h
    rw [hσ, mul_one, payout_and, payout_of_holds (PCWorld.holds_top v), one_mul, hσ, hact,
      fixedSystemR_val_top] at h
    exact_mod_cast h.symm

/-- The converse of `pointMass_faith_forces_rep`: representatives that are `0` at `⊥`'s actual
cell and `1` at `⊤`'s actual cell on every day `m ≥ 1` give the point mass exact faith on the
index.
Source: this run (audit r3 adversarial N1, probe `PointMassRepIff.pointMass_e2xσIdx_of_rep`, adopted)
Kind: L
Fidelity: n/a -/
theorem pointMass_e2xσIdx_of_rep (rep : ℕ → ℕ → ℚ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁))
    (hrep : ∀ m, 1 ≤ m → rep m (roundedBot m) = 0 ∧ rep m (roundedTop m) = 1) :
    E2xσIdx σB2 witnessIndex (fixedSystemR rep) (pointMass v) := by
  intro n m hnm q hq c hc _
  show v.payout (sentenceOfCode c ⋏ σB2 m q) =
    (fixedSystemR rep).val m q (sentenceOfCode c) * v.payout (σB2 m q)
  rw [payout_and, payout_σB2_fixed v hv m hq]
  have hact : actualCode 𝗜𝚺₁ halfRound witnessIndex m =
      Encodable.encode (tbl (roundedBot m) (roundedTop m)) := by
    unfold actualCode; rw [actualTable_eq_tbl]
  by_cases hqa : q = actualCode 𝗜𝚺₁ halfRound witnessIndex m
  · rw [if_pos hqa, mul_one, mul_one, hqa, hact]
    rcases mem_witnessIndex_iff.1 hc with rfl | rfl
    · rw [sentenceOfCode_encode, fixedSystemR_val_bot, payout_of_not_holds (not_holds_falsum v),
        (hrep m (by omega)).1]
      simp
    · rw [sentenceOfCode_encode, fixedSystemR_val_top, payout_of_holds (PCWorld.holds_top v),
        (hrep m (by omega)).2]
      simp
  · rw [if_neg hqa, mul_zero, mul_zero]

/-- **Some representatives make the point mass carry faith on `witnessIndex` iff the LIA never
rounds `⊥` and `⊤` to the same cell on a day `m ≥ 1`.** (→) `pointMass_faith_forces_rep`;
(←) `rep m r := if r = roundedBot m then 0 else 1`. So "never the same side" is the exact gap
for *some* (day-dependent, swapped where needed) representatives, while `Tbl01At` on the
initial segment is the exact gap at `rep01` (`determination_B2_pointMass`'s condition).
Source: this run (audit r3 adversarial N1, probe `PointMassRepIff.pointMass_faith_exists_rep_iff`, adopted)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem pointMass_faith_exists_rep_iff (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP 𝗜𝚺₁)) :
    (∃ rep : ℕ → ℕ → ℚ, E2xσIdx σB2 witnessIndex (fixedSystemR rep) (pointMass v)) ↔
      ∀ m, 1 ≤ m → roundedBot m ≠ roundedTop m := by
  constructor
  · rintro ⟨rep, hE2⟩ m hm heq
    obtain ⟨h0, h1⟩ := pointMass_faith_forces_rep rep v hv hE2 m hm
    rw [heq, h1] at h0
    exact one_ne_zero h0
  · intro h
    refine ⟨fun m r => if r = roundedBot m then 0 else 1,
      pointMass_e2xσIdx_of_rep _ v hv fun m hm => ⟨?_, ?_⟩⟩
    · simp
    · simp [Ne.symm (h m hm)]

end Cleanroom.Bli.BliLinkage
