import Cleanroom.Bli.BliTrajectory.Partition
import Cleanroom.Bli.BliTrajectory.Refutations
import Mathlib.Algebra.BigOperators.Fin

/-!
# `bli-trajectory` · Coherent: the coherence horn of M7 (iii) (repair round 1)

The Notion's claim (ll. 215–225, quoted in [[bli-trajectory-findings]] F-13): "LUV coherence
plus conditional trust … implies *all* the BLI conditions". Read with "conditional trust" as
`FaithMarginal` (ATTRIBUTION-UNVETTED), the claim needs a **coherent** market with faith in the
marginals that still fails constraint 2 (`E2x`). `Refutations.faithMarginal_not_imp_e2x`'s
two-table witness is *not* coherent (it prices `⊥` at `p > 0`; audit r1 adversarial B2, probe
`audit-r1-probes/CoherentBase.lean`), so it refutes bli-slides-015 (b) but not the Notion.

**The witness here is a world mixture on every day** (`cohHistory`): four FAF `PCWorld`s at day
`n` — the atom `cohAtom = atom 0` true or false, crossed with which of the two day-`(n+1)`
candidates holds — with weights `(p+δ)/2, (1−p−δ)/2, (p−δ)/2, (1−p+δ)/2`. So `𝐏_n(cohAtom) = p`,
`𝐏_n(σ_{q₁}) = 𝐏_n(σ_{q₂}) = ½`, `𝐏_n(cohAtom ⋏ σ_{q₁}) = (p+δ)/2`. The candidate tables copy the
day-`n` market (`cohSystem`: `val (n+1) q φ := 𝐏_n(φ)` for both codes), so they are coherent
too, and identical — the point of the (ii) witness, kept. Then `CoherentOn ∅ A (𝐏_n)` for every
`n` and every atom set `A` (`cohHistory_coherent`), `E1x` (base = the market's own small
prices, coherent), `E3`, `E4`, `E5`, `FaithMarginal` — and `¬ E2x` at `(0, 1, q₁, cohAtom)`:
`(p+δ)/2 ≠ p/2` (`faithMarginal_coherent_not_imp_e2x`).

**Scaffold, disclosed.** The day-`n` worlds hold no state atom of a day `≥ n+2` (mass `0` two or
more days ahead), which is what makes `E3` and `FaithMarginal` at `(n, m)`, `m ≥ n+2`, hold with
both sides `0`. A world mixture that charged the same code on every future day would break
`FaithMarginal` at intermediate-day atoms — the F-1 phenomenon (a consistent-trajectory prior
is incompatible with faith on the full scope). Coherence is relative to the empty stage
(`CoherentOn ∅`): pure propositional coherence, FAF's `PCWorld` semantics, no theory.

**Two codes, one table (audit r2 adversarial B1; repair round 2).** `cohSystem`'s two candidates
decode to the *same* table, and `¬ E2x` uses exactly that: `(p+δ)/2 ≠ p/2` is possible only
because two exclusive atoms share the value `p`. In the sources a state *is* its price-list
(`main.tex:431`) and B1's `bliStateSystem` is injective on candidates, so this witness refutes
the implication for `bli-found`'s abstract `StateSystem` under propositional coherence over the
atom encoding (`CoherentOn ∅`: the *empty* stage — the weakest — on every atom set), not under a
reading on which the state atom asserts its table. With two *distinct* tables the conditional is
pinned (`Pinning.two_state_pinning`, `Pinning.two_state_pinning_scope`); the refutation that
survives the injective reading needs three states and is
`TriState.faithMarginal_coherent_distinct_not_imp_e2x`. This file's headline is kept as the
two-state, non-injective form, relabelled `(c)`.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

open Classical

noncomputable section

/-! ## The atom of the witness and the state codes -/

/-- The small atom the witness is uncertain about: `atom 0` (tag `0`, so not a state atom;
`tokenSize = 3`, so small from day `1`).
Source: mandate M7 (iii) (repair round 1)
Kind: D
Fidelity: n/a -/
def cohAtom : Sentence := Formula.atom 0

/-- `cohAtom` is small on every day `≥ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohAtom_smallOn {m : ℕ} (hm : 1 ≤ m) : SmallOn m cohAtom := by
  unfold SmallOn cohAtom
  rw [tokenSize_atom]
  have h := length_natDigits4_le_of_lt_pow (n := 0 + 5) (L := 2) (by norm_num)
  have := four_le_sizeBound hm
  omega

/-- `atomDay 0 = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomDay_zero : atomDay 0 = 0 := by
  simp [atomDay, atomDayBase, cleanroomBaseTag, Nat.unpair_zero]

/-- `cohAtom ∈ Sminus m m` for every `m ≥ 1` (in `E2x`'s scope).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohAtom_mem_Sminus {m : ℕ} (hm : 1 ≤ m) : cohAtom ∈ Sminus m m := by
  rw [mem_Sminus]
  refine ⟨cohAtom_smallOn hm, fun a ha => ?_⟩
  simp only [cohAtom, sentenceAtomCodes_atom, Finset.mem_singleton] at ha
  subst ha
  rw [atomDay_zero]
  omega

/-- The atom code of the state atom `⌜𝑸_m = q⌝`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev stateCode (m q : ℕ) : ℕ := freshAtomCode stateFamily (Nat.pair m q)

/-- `0` is no state code (state codes have tag `> 8`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma zero_ne_stateCode (m q : ℕ) : (0 : ℕ) ≠ stateCode m q := by
  intro h
  have := stateAtom_ne_faf m q _ (by rw [sentenceAtomCodes_stateAtom]; exact Finset.mem_singleton_self _)
  have h' : freshAtomCode stateFamily (Nat.pair m q) = 0 := h.symm
  rw [h', Nat.unpair_zero] at this
  simp at this

/-- State codes are injective in `(m, q)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateCode_inj {m q m' q' : ℕ} : stateCode m q = stateCode m' q' ↔ m = m' ∧ q = q' := by
  constructor
  · intro h
    exact stateAtom_inj.mp (by rw [stateAtom_eq_atom, stateAtom_eq_atom]; exact congrArg _ h)
  · rintro ⟨rfl, rfl⟩; rfl

/-- The two candidate codes of day `m`: `4^{sizeBound m}` and `4^{sizeBound m} + 1` (`twoCodes`).
Source: mandate M7 (ii)/(iii)
Kind: D
Fidelity: n/a -/
def c₁ (m : ℕ) : ℕ := 4 ^ sizeBound m

/-- The second candidate code.
Source: mandate M7 (ii)/(iii)
Kind: D
Fidelity: n/a -/
def c₂ (m : ℕ) : ℕ := 4 ^ sizeBound m + 1

/-- `c₁ ≠ c₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma c₁_ne_c₂ (m : ℕ) : c₁ m ≠ c₂ m := by unfold c₁ c₂; omega

/-- `twoCodes m = {c₁ m, c₂ m}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCodes_eq (m : ℕ) : twoCodes m = {c₁ m, c₂ m} := rfl

/-! ## The four worlds, the weights, the history -/

/-- **The four worlds at day `n`**: `0` = `cohAtom` and `σ_{n+1,c₁}`; `1` = `σ_{n+1,c₁}` only;
`2` = `cohAtom` and `σ_{n+1,c₂}`; `3` = `σ_{n+1,c₂}` only. Every other atom is false — in
particular no state atom of a day `≠ n+1` holds in any of them (the scaffold, disclosed in the
module docstring).
Source: mandate M7 (iii) (repair round 1: audit r1 fidelity B1 / adversarial B2)
Kind: D
Fidelity: n/a -/
def cohWorld (n : ℕ) : Fin 4 → PCWorld
  | 0 => fun a => a = 0 ∨ a = stateCode (n + 1) (c₁ (n + 1))
  | 1 => fun a => a = stateCode (n + 1) (c₁ (n + 1))
  | 2 => fun a => a = 0 ∨ a = stateCode (n + 1) (c₂ (n + 1))
  | 3 => fun a => a = stateCode (n + 1) (c₂ (n + 1))

/-- **The weights** `(p+δ)/2, (1−p−δ)/2, (p−δ)/2, (1−p+δ)/2` — nonnegative and summing to one
when `0 ≤ p − δ` and `p + δ ≤ 1`; all four positive when `δ < p` and `p + δ < 1`.
Source: mandate M7 (iii)
Kind: D
Fidelity: n/a -/
def cohWeight (p δ : ℝ) : Fin 4 → ℝ
  | 0 => (p + δ) / 2
  | 1 => (1 - p - δ) / 2
  | 2 => (p - δ) / 2
  | 3 => (1 - p + δ) / 2

/-- **The coherent witness history**: on every day the mixture of the four worlds.
Source: mandate M7 (iii)
Kind: D
Fidelity: n/a -/
def cohHistory (p δ : ℝ) : History :=
  fun n φ => ∑ i : Fin 4, cohWeight p δ i * (cohWorld n i).payout φ

/-- **The state system of the witness**: codes `twoCodes`, both tables of day `m` equal to the
day-`(m−1)` market (`val m q φ := 𝐏_{m−1}(φ)`; identical tables, as in the (ii) witness — **two
codes, one table**, audit r2 adversarial B1; the distinct-table system is `TriState.triSystem`),
realized state `c₁`. `m − 1` is `Nat` subtraction: `val 0 q φ = 𝐏_0(φ)`, unreachable from every
predicate (all read `val` at `m ≥ 1`) and a coherent world mixture anyway.
Source: mandate M7 (iii)
Kind: D
Fidelity: n/a -/
def cohSystem (p δ : ℝ) : StateSystem where
  states := twoCodes
  val m _ φ := cohHistory p δ (m - 1) φ
  actual m := 4 ^ sizeBound m
  actual_mem _ := by simp [twoCodes]

/-! ## Payouts of the four worlds -/

variable {p δ : ℝ} {n : ℕ}

/-- Payout of `cohAtom`: `1` in worlds `0`, `2`; `0` in worlds `1`, `3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohWorld_payout_cohAtom (n : ℕ) :
    (cohWorld n 0).payout cohAtom = 1 ∧ (cohWorld n 1).payout cohAtom = 0 ∧
      (cohWorld n 2).payout cohAtom = 1 ∧ (cohWorld n 3).payout cohAtom = 0 := by
  simp [PCWorld.payout, cohWorld, cohAtom, zero_ne_stateCode]

/-- Payout of a state atom of a day `≠ n+1`: `0` in every world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohWorld_payout_stateAtom_ne {m : ℕ} (hm : m ≠ n + 1) (q : ℕ) (i : Fin 4) :
    (cohWorld n i).payout (stateAtom m q) = 0 := by
  have h1 : stateCode m q ≠ 0 := (zero_ne_stateCode m q).symm
  have h2 : ∀ q', stateCode m q ≠ stateCode (n + 1) q' := fun q' h => hm (stateCode_inj.mp h).1
  rw [stateAtom_eq_atom]
  fin_cases i <;> simp [PCWorld.payout, cohWorld, h1, h2]

/-- Payout of the day-`(n+1)` candidate atoms: `σ_{c₁}` holds in worlds `0`, `1`; `σ_{c₂}` in
worlds `2`, `3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohWorld_payout_state (n : ℕ) :
    ((cohWorld n 0).payout (stateAtom (n + 1) (c₁ (n + 1))) = 1 ∧
      (cohWorld n 1).payout (stateAtom (n + 1) (c₁ (n + 1))) = 1 ∧
      (cohWorld n 2).payout (stateAtom (n + 1) (c₁ (n + 1))) = 0 ∧
      (cohWorld n 3).payout (stateAtom (n + 1) (c₁ (n + 1))) = 0) ∧
    ((cohWorld n 0).payout (stateAtom (n + 1) (c₂ (n + 1))) = 0 ∧
      (cohWorld n 1).payout (stateAtom (n + 1) (c₂ (n + 1))) = 0 ∧
      (cohWorld n 2).payout (stateAtom (n + 1) (c₂ (n + 1))) = 1 ∧
      (cohWorld n 3).payout (stateAtom (n + 1) (c₂ (n + 1))) = 1) := by
  have h0 : ∀ q, stateCode (n + 1) q ≠ 0 := fun q => (zero_ne_stateCode _ q).symm
  have h12 : stateCode (n + 1) (c₁ (n + 1)) ≠ stateCode (n + 1) (c₂ (n + 1)) :=
    fun h => c₁_ne_c₂ (n + 1) (stateCode_inj.mp h).2
  have h21 : stateCode (n + 1) (c₂ (n + 1)) ≠ stateCode (n + 1) (c₁ (n + 1)) := h12.symm
  simp only [stateAtom_eq_atom]
  simp [PCWorld.payout, cohWorld, h0, h12, h21]

/-! ## The history on the sentences the constraints read -/

/-- `𝐏_n(cohAtom) = p`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_cohAtom (p δ : ℝ) (n : ℕ) : cohHistory p δ n cohAtom = p := by
  obtain ⟨h0, h1, h2, h3⟩ := cohWorld_payout_cohAtom n
  unfold cohHistory
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  simp [cohWeight]; ring

/-- `𝐏_n(σ_{n+1,c₁}) = ½` and `𝐏_n(σ_{n+1,c₂}) = ½`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_state (p δ : ℝ) (n : ℕ) :
    cohHistory p δ n (stateAtom (n + 1) (c₁ (n + 1))) = 1 / 2 ∧
      cohHistory p δ n (stateAtom (n + 1) (c₂ (n + 1))) = 1 / 2 := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := cohWorld_payout_state n
  unfold cohHistory
  constructor
  · rw [Fin.sum_univ_four, a0, a1, a2, a3]; simp [cohWeight]; ring
  · rw [Fin.sum_univ_four, b0, b1, b2, b3]; simp [cohWeight]; ring

/-- `𝐏_n(σ_{m,q}) = 0` for `m ≠ n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_stateAtom_ne (p δ : ℝ) {m : ℕ} (hm : m ≠ n + 1) (q : ℕ) :
    cohHistory p δ n (stateAtom m q) = 0 := by
  unfold cohHistory
  exact Finset.sum_eq_zero fun i _ => by rw [cohWorld_payout_stateAtom_ne hm q i, mul_zero]

/-- `𝐏_n(φ ⋏ σ_{m,q}) = 0` for `m ≠ n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_and_stateAtom_ne (p δ : ℝ) {m : ℕ} (hm : m ≠ n + 1) (q : ℕ) (φ : Sentence) :
    cohHistory p δ n (φ ⋏ stateAtom m q) = 0 := by
  unfold cohHistory
  exact Finset.sum_eq_zero fun i _ => by
    rw [payout_and, cohWorld_payout_stateAtom_ne hm q i, mul_zero, mul_zero]

/-- `𝐏_n(φ ⋏ (σ_{m,q₁} ⋏ σ_{o,q₂})) = 0` for `o ≠ n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_and_two_ne (p δ : ℝ) {o : ℕ} (ho : o ≠ n + 1) (m q₁ q₂ : ℕ) (φ : Sentence) :
    cohHistory p δ n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) = 0 := by
  unfold cohHistory
  exact Finset.sum_eq_zero fun i _ => by
    rw [payout_and, payout_and, cohWorld_payout_stateAtom_ne ho q₂ i, mul_zero, mul_zero, mul_zero]

/-- `𝐏_n(σ_{m,q₁} ⋏ σ_{o,q₂}) = 0` for `o ≠ n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_two_ne (p δ : ℝ) {o : ℕ} (ho : o ≠ n + 1) (m q₁ q₂ : ℕ) :
    cohHistory p δ n (stateAtom m q₁ ⋏ stateAtom o q₂) = 0 := by
  unfold cohHistory
  exact Finset.sum_eq_zero fun i _ => by
    rw [payout_and, cohWorld_payout_stateAtom_ne ho q₂ i, mul_zero, mul_zero]

/-- The joints with the two day-`(n+1)` candidates: `𝐏_n(φ ⋏ σ_{c₁}) = w₀ π₀(φ) + w₁ π₁(φ)` and
`𝐏_n(φ ⋏ σ_{c₂}) = w₂ π₂(φ) + w₃ π₃(φ)`; they sum to `𝐏_n(φ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_and_state (p δ : ℝ) (n : ℕ) (φ : Sentence) :
    cohHistory p δ n (φ ⋏ stateAtom (n + 1) (c₁ (n + 1))) =
        cohWeight p δ 0 * (cohWorld n 0).payout φ + cohWeight p δ 1 * (cohWorld n 1).payout φ ∧
      cohHistory p δ n (φ ⋏ stateAtom (n + 1) (c₂ (n + 1))) =
        cohWeight p δ 2 * (cohWorld n 2).payout φ + cohWeight p δ 3 * (cohWorld n 3).payout φ := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := cohWorld_payout_state n
  unfold cohHistory
  simp only [payout_and]
  constructor
  · rw [Fin.sum_univ_four, a0, a1, a2, a3]; ring
  · rw [Fin.sum_univ_four, b0, b1, b2, b3]; ring

/-- `𝐏_n(φ ⋏ σ_{c₁}) + 𝐏_n(φ ⋏ σ_{c₂}) = 𝐏_n(φ)` — the partition inside the mixture.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_and_state_sum (p δ : ℝ) (n : ℕ) (φ : Sentence) :
    cohHistory p δ n (φ ⋏ stateAtom (n + 1) (c₁ (n + 1))) +
      cohHistory p δ n (φ ⋏ stateAtom (n + 1) (c₂ (n + 1))) = cohHistory p δ n φ := by
  obtain ⟨h1, h2⟩ := cohHistory_and_state p δ n φ
  rw [h1, h2]
  unfold cohHistory
  rw [Fin.sum_univ_four]; ring

/-- Exclusivity of the two day-`(n+1)` candidates: `𝐏_n(σ_{c₁} ⋏ σ_{c₂}) = 0` (and symmetric).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_excl (p δ : ℝ) (n : ℕ) :
    cohHistory p δ n (stateAtom (n + 1) (c₁ (n + 1)) ⋏ stateAtom (n + 1) (c₂ (n + 1))) = 0 ∧
      cohHistory p δ n (stateAtom (n + 1) (c₂ (n + 1)) ⋏ stateAtom (n + 1) (c₁ (n + 1))) = 0 := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩⟩ := cohWorld_payout_state n
  unfold cohHistory
  simp only [payout_and]
  constructor
  · rw [Fin.sum_univ_four, a0, a1, a2, a3, b0, b1, b2, b3]; ring
  · rw [Fin.sum_univ_four, a0, a1, a2, a3, b0, b1, b2, b3]; ring

/-- `𝐏_n(cohAtom ⋏ σ_{n+1,c₁}) = (p+δ)/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cohHistory_cohAtom_and_c₁ (p δ : ℝ) (n : ℕ) :
    cohHistory p δ n (cohAtom ⋏ stateAtom (n + 1) (c₁ (n + 1))) = (p + δ) / 2 := by
  obtain ⟨h0, h1, -, -⟩ := cohWorld_payout_cohAtom n
  rw [(cohHistory_and_state p δ n cohAtom).1, h0, h1]
  simp [cohWeight]

/-! ## Coherence and the constraints -/

/-- **`cohHistory` is a world mixture on every day, hence coherent on every atom set** (relative
to the empty stage): `CoherentOn ∅ A (𝐏_n)` for every `n` and `A`, with the four worlds and the
weights as the certificate.
Source: mandate M7 (iii); `bli-found` `CoherentOn`
Kind: L
Fidelity: exact (every atom set, empty stage — propositional coherence over the atom encoding only; `∅` is the *weakest* stage)
Hyps: (a) `0 ≤ p ± δ ≤ 1` (nonnegative weights) -/
theorem cohHistory_coherent (p δ : ℝ) (h0 : 0 ≤ p - δ) (h0' : 0 ≤ p + δ) (h1 : p + δ ≤ 1)
    (h1' : p - δ ≤ 1) (n : ℕ) (A : Finset ℕ) : CoherentOn ∅ A (cohHistory p δ n) := by
  refine ⟨4, cohWorld n, cohWeight p δ, fun i φ h => by simp at h, ?_, ?_, fun φ _ => rfl⟩
  · intro i; fin_cases i <;> simp [cohWeight] <;> linarith
  · rw [Fin.sum_univ_four]; simp [cohWeight]; ring

/-- `E1x` for the witness with the market's own small prices as the base.
Source: mandate M7 (iii)
Kind: L
Fidelity: exact -/
lemma cohHistory_E1x (p δ : ℝ) : E1x (cohHistory p δ) (cohHistory p δ) := fun _ _ _ => rfl

/-- `E3` for the witness: both sides vanish (no day-`n` world holds a state atom of a day
`≥ n+2`).
Source: mandate M7 (iii)
Kind: L
Fidelity: exact (full scope) -/
lemma cohHistory_E3 (p δ : ℝ) : E3 (cohSystem p δ) (cohHistory p δ) := by
  intro n m o hnm hmo q₁ _ q₂ _ φ _
  have ho : o ≠ n + 1 := by omega
  rw [cohHistory_and_two_ne p δ ho, cohHistory_two_ne p δ ho, mul_zero]

/-- `E4` for the witness: the tables copy the day-`n` market and the masses sum to one.
Source: mandate M7 (iii)
Kind: L
Fidelity: exact -/
lemma cohHistory_E4 (p δ : ℝ) : E4 (cohSystem p δ) (cohHistory p δ) := by
  intro n φ _
  obtain ⟨h1, h2⟩ := cohHistory_state p δ n
  show cohHistory p δ n φ = ∑ q ∈ twoCodes (n + 1),
    cohHistory p δ n (stateAtom (n + 1) q) * cohHistory p δ (n + 1 - 1) φ
  rw [twoCodes_eq, Finset.sum_insert (by simp [c₁_ne_c₂]), Finset.sum_singleton, h1, h2,
    Nat.add_sub_cancel]
  ring

/-- `E5` for the witness: masses `½ + ½` and exclusivity inside every world.
Source: mandate M7 (iii)
Kind: L
Fidelity: exact -/
lemma cohHistory_E5 (p δ : ℝ) : E5 (cohSystem p δ) (cohHistory p δ) := by
  intro n
  obtain ⟨h1, h2⟩ := cohHistory_state p δ n
  obtain ⟨e1, e2⟩ := cohHistory_excl p δ n
  constructor
  · show ∑ q ∈ twoCodes (n + 1), cohHistory p δ n (stateAtom (n + 1) q) = 1
    rw [twoCodes_eq, Finset.sum_insert (by simp [c₁_ne_c₂]), Finset.sum_singleton, h1, h2]; norm_num
  · intro q₁ hq₁ q₂ hq₂ hne
    simp only [cohSystem, twoCodes_eq, Finset.mem_insert, Finset.mem_singleton] at hq₁ hq₂
    rcases hq₁ with rfl | rfl <;> rcases hq₂ with rfl | rfl
    · exact absurd rfl hne
    · exact e1
    · exact e2
    · exact absurd rfl hne

/-- **`FaithMarginal` for the witness.** At `(n, n+1)` both tables price `φ` at `𝐏_n(φ)`, so the
event "`𝑸_{n+1}(φ) = x`" is everything or nothing; when it is everything the joints sum to
`𝐏_n(φ)` (`cohHistory_and_state_sum`) and the masses to `1`. At `(n, m)` with `m ≥ n+2` every
term is `0`.
Source: mandate M7 (iii); bli-slides-015 (ii)
Kind: C
Fidelity: exact (full scope) -/
theorem cohHistory_faithMarginal (p δ : ℝ) : FaithMarginal (cohSystem p δ) (cohHistory p δ) := by
  intro n m hnm φ _ x
  unfold marginalJoint marginalMass
  by_cases hm : m = n + 1
  · subst hm
    have hval : ∀ q, (cohSystem p δ).val (n + 1) q φ = cohHistory p δ n φ := by
      intro q; show cohHistory p δ (n + 1 - 1) φ = _; rw [Nat.add_sub_cancel]
    by_cases hx : x = cohHistory p δ n φ
    · have hfilt : ((cohSystem p δ).states (n + 1)).filter
          (fun q => (cohSystem p δ).val (n + 1) q φ = x) = twoCodes (n + 1) := by
        apply Finset.filter_true_of_mem; intro q _; rw [hval, hx]
      rw [hfilt, twoCodes_eq, Finset.sum_insert (by simp [c₁_ne_c₂]), Finset.sum_singleton,
        Finset.sum_insert (by simp [c₁_ne_c₂]), Finset.sum_singleton,
        cohHistory_and_state_sum, (cohHistory_state p δ n).1, (cohHistory_state p δ n).2, hx]
      ring
    · have hfilt : ((cohSystem p δ).states (n + 1)).filter
          (fun q => (cohSystem p δ).val (n + 1) q φ = x) = ∅ := by
        apply Finset.filter_false_of_mem; intro q _; rw [hval]; exact fun h => hx h.symm
      rw [hfilt]; simp
  · rw [Finset.sum_eq_zero (fun q _ => cohHistory_and_stateAtom_ne p δ hm q φ),
      Finset.sum_eq_zero (fun q _ => cohHistory_stateAtom_ne p δ hm q), mul_zero]

/-- **`E2x` fails for the witness** at `(0, 1, c₁, cohAtom)`: `𝐏_0(cohAtom ⋏ σ_{1,c₁}) = (p+δ)/2`
while `𝑸̂[cohAtom] · 𝐏_0(σ_{1,c₁}) = p · ½`.
Source: mandate M7 (iii)
Kind: L
Fidelity: exact
Hyps: (a) `δ ≠ 0` -/
lemma cohHistory_not_E2x (p δ : ℝ) (hδ : δ ≠ 0) : ¬ E2x (cohSystem p δ) (cohHistory p δ) := by
  intro hE2
  have hq : c₁ 1 ∈ (cohSystem p δ).states 1 := by simp [cohSystem, twoCodes_eq]
  have := hE2 0 1 (by norm_num) _ hq cohAtom (cohAtom_mem_Sminus le_rfl)
  rw [cohHistory_cohAtom_and_c₁, (cohHistory_state p δ 0).1] at this
  have hval : (cohSystem p δ).val 1 (c₁ 1) cohAtom = p := by
    show cohHistory p δ (1 - 1) cohAtom = p; rw [cohHistory_cohAtom]
  rw [hval] at this
  apply hδ; linarith

/-! ## The headline -/

/-- **`faithMarginal_coherent_not_imp_e2x` — coherence plus faith in the marginal does not imply
faith in the state** (the coherence horn of M7 (iii); Notion ll. 215–225, "LUV coherence plus
conditional trust … implies *all* the BLI conditions", ATTRIBUTION-UNVETTED that "conditional
trust" is `FaithMarginal`). Witness: `cohHistory p δ` — on every day a mixture of four FAF
worlds (`cohAtom` true/false × which of two candidates holds), weights
`(p+δ)/2, (1−p−δ)/2, (p−δ)/2, (1−p+δ)/2`; the two candidate tables both copy the day-`n` market
(coherent, and **identical** — two codes, one table, which is what the `¬ E2x` uses; audit r2
adversarial B1); the base is the market's own small prices (coherent). It satisfies
`CoherentOn ∅ A` on every day for every atom set `A` (market, base and every table), `E1x`,
`E3`, `E4`, `E5` and `FaithMarginal` on the **full** scope, and fails `E2x` at
`(0, 1, c₁, cohAtom)`: `(p+δ)/2 ≠ p/2`. N+ on the coordinate that matters: all four worlds
charged (`0 < δ < p`, `p + δ < 1`), two distinct positive-mass states with different interior
conditionals `p ± δ`. Scaffold (disclosed): the day-`n` mixture gives mass `0` to every state of
a day `≥ n+2`. Surviving neighbours: refinement-invariant trust, which *is* `E2x`; and, for two
*distinct* tables, `Pinning.two_state_pinning`/`_scope` (the conditional is pinned). The
refutation under the injective reading (three distinct coherent tables, every world holding
exactly one next-day state) is `TriState.faithMarginal_coherent_distinct_not_imp_e2x`.
Source: Notion ll. 215–225 (bli-paper-060); bli-slides-015 (b); mandate M7 (iii)
Kind: P
Fidelity: weaker: (c) propositional coherence over the state-atom encoding (`CoherentOn ∅`, every atom set, empty stage) in place of "propositional plus LUV coherence"; the state system is non-injective (two codes, one table). The injective version is `TriState.faithMarginal_coherent_distinct_not_imp_e2x`
Hyps: (c) `CoherentOn ∅` for "LUV coherence" (and two codes for one table); (a) `0 < δ`, `δ < p`, `p + δ < 1` (the witness's parameters) -/
theorem faithMarginal_coherent_not_imp_e2x (p δ : ℝ) (hδ : 0 < δ) (h0 : δ < p) (h1 : p + δ < 1) :
    ∃ (S : StateSystem) (Q P : History),
      (∀ n A, CoherentOn ∅ A (P n)) ∧ (∀ n A, CoherentOn ∅ A (Q n)) ∧
      (∀ m q A, CoherentOn ∅ A (S.val m q)) ∧
      E1x Q P ∧ E3 S P ∧ E4 S P ∧ E5 S P ∧ FaithMarginal S P ∧ ¬ E2x S P := by
  have hc : ∀ n A, CoherentOn ∅ A (cohHistory p δ n) :=
    cohHistory_coherent p δ (by linarith) (by linarith) h1.le (by linarith)
  exact ⟨cohSystem p δ, cohHistory p δ, cohHistory p δ, hc, hc, fun m _ A => hc (m - 1) A,
    cohHistory_E1x p δ, cohHistory_E3 p δ, cohHistory_E4 p δ, cohHistory_E5 p δ,
    cohHistory_faithMarginal p δ, cohHistory_not_E2x p δ hδ.ne'⟩

/-- **All four worlds are charged** under the headline's hypotheses (the N+ certificate): every
weight is strictly positive.
Source: mandate M7 (iii) (N+ grading)
Kind: N+
Fidelity: n/a
Hyps: (a) `0 < δ < p`, `p + δ < 1` -/
theorem cohWeight_pos (p δ : ℝ) (hδ : 0 < δ) (h0 : δ < p) (h1 : p + δ < 1) (i : Fin 4) :
    0 < cohWeight p δ i := by
  fin_cases i <;> simp [cohWeight] <;> linarith

end

end Cleanroom.Bli.BliTrajectory
