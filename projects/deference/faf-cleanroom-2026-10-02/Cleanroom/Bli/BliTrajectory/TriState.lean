import Cleanroom.Bli.BliTrajectory.Coherent

/-!
# `bli-trajectory` · TriState: the coherence horn of M7 (iii) with three *distinct* tables
(repair round 2)

Audit r2 (adversarial B1) observed that both `FaithMarginal ⇏ E2x` witnesses
(`Refutations.faithMarginal_not_imp_e2x`, `Coherent.faithMarginal_coherent_not_imp_e2x`) use a
state system whose two candidate codes decode to **the same table**, and proved (probe
`audit-r2-probes/Pinning.lean`, adopted as `Pinning.two_state_pinning`) that with two *distinct*
coherent tables faith in the marginals pins the state conditional. In the sources a state *is*
its price-list (`main.tex:431`: the candidates are `Q ∈ 𝒟_n`), and B1's own `bliStateSystem` is
injective on candidates — so those two refutations live on a freedom of `bli-found`'s abstract
`StateSystem` that the sources' framework does not have.

**This file rebuilds the refutation with three pairwise distinct coherent tables.** Two atoms,
`cohAtom = atom 0` and `triAtom' = atom 1`, cut each day's worlds into three charged cells —
`{a, b}`, `{a}`, `{b}` (the fourth cell, neither, is never charged) — and the three candidates
`triCode m 0, 1, 2` of day `m` carry the tables `t₁ = (½, ¼, ¼)`, `t₂ = (¼, ½, ¼)`,
`t₃ = (¼, ¼, ½)` over the cells. The market's conditionals given the states are the tables
perturbed by a 3-cycle, `c₁ = t₁ + ε·(0, 1, −1)`, `c₂ = t₂ + ε·(−1, 0, 1)`, `c₃ = t₃ + ε·(1, −1, 0)`,
with every state at mass `⅓`. At every event of the cell algebra the states whose *table values
agree* have deviations summing to zero (checked exhaustively in `triHistory_faithMarginal`:
eight events, each with its level sets), so **faith in every marginal holds**, while no state's
conditional is its table: `E2x` fails at `(0, 1, triCode 1 0, cohAtom)`,
`⅓·(¾ + ε) ≠ ¾·⅓`. With two states this is impossible (`Pinning.two_state_pinning` and
`Pinning.two_state_pinning_scope`): the level sets of two distinct additive tables are singletons
on some sentence of every Boolean-closed family, and the deviation must vanish there. Three
states are the first place where an event's level sets can pair the states differently on
different events, which is exactly what the 3-cycle exploits.

**What is coherent here.** The market is on every day a mixture of nine FAF `PCWorld`s
(`triWorld n i j`: holds the day-`(n+1)` candidate atom `i` and the atoms of cell `j`, nothing
else), so `CoherentOn ∅ A (𝐏_n)` for every atom set `A` (empty stage: propositional coherence
over the atom encoding; no theory). **Every world holds exactly one day-`(n+1)` candidate atom**
(`triWorld_unique_state`): the day-`(n+1)` states partition every world, which is the
partition reading of "LUV coherence" (the state atom read as the assertion that *this* table
is the day-`(n+1)` state). The three tables are pairwise distinct as functions
(`triTableVal_ne`) and each is itself a world mixture (`triTableVal_coherent`): table `i`
charges cell `j` with `t_{ij}` and, within the cell, the market's own posterior over the
states. The candidates are large (`triSystem_large`). **Scaffold, disclosed** (as in
`Coherent.lean`, findings F-19): the day-`n` worlds hold no state atom of a day `≥ n+2`, so
`E3` and `FaithMarginal` at `(n, m)`, `m ≥ n+2`, hold with both sides `0` — a world mixture
that charges the same code on every future day breaks `FaithMarginal` at intermediate-day
atoms (the F-1 phenomenon). The tables' values on the day-`m` state atoms themselves are junk
the sources never read (B1's tables give those sentences `0`).

**What this does and does not refute.** Under the reading "conditional trust" = `FaithMarginal`
(ATTRIBUTION-UNVETTED) and "LUV coherence" = a `PCWorld` mixture in which the next day's
candidates partition every world, with distinct coherent tables, the Notion's "LUV coherence
plus conditional trust … implies *all* the BLI conditions" is **refuted** on `bli-found`'s
predicates (`faithMarginal_coherent_distinct_not_imp_e2x`). A stronger reading of LUV coherence
that FAF cannot state (e.g. one that pins the market's conditional on a state to the state's
table — which *is* `E2x`) is not touched; nor is the scaffold's "mass `0` two days ahead".
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

open Classical

noncomputable section

/-! ## Codes, cells, worlds -/

/-- The three candidate codes of day `m`: `4^{sizeBound m} + i` for `i : Fin 3` (`triCode m 0 =
c₁ m`, `triCode m 1 = c₂ m`; the third is `Refutations.threeCodes`' third code).
Source: mandate M7 (iii) (repair round 2: audit r2 adversarial B1)
Kind: D
Fidelity: n/a -/
def triCode (m : ℕ) (i : Fin 3) : ℕ := 4 ^ sizeBound m + i.val

/-- `triCode m 0 = c₁ m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triCode_zero (m : ℕ) : triCode m 0 = c₁ m := rfl

/-- The three codes are distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triCode_injective (m : ℕ) : Function.Injective (triCode m) := fun i j h =>
  Fin.ext (by unfold triCode at h; omega)

/-- The second atom of the witness: `atom 1` (tag `0`, not a state atom).
Source: mandate M7 (iii) (repair round 2)
Kind: D
Fidelity: n/a -/
def triAtom' : Sentence := Formula.atom 1

/-- The atoms each of the three charged cells holds: cell `0` holds `atom 0` and `atom 1`, cell
`1` holds `atom 0` only, cell `2` holds `atom 1` only.
Source: mandate M7 (iii) (repair round 2)
Kind: D
Fidelity: n/a -/
def cellHolds : Fin 3 → ℕ → Prop
  | 0 => fun a => a = 0 ∨ a = 1
  | 1 => fun a => a = 0
  | 2 => fun a => a = 1

/-- A cell holds only the atoms `0` and `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellHolds_le {j : Fin 3} {a : ℕ} (h : cellHolds j a) : a ≤ 1 := by
  fin_cases j <;> simp [cellHolds] at h <;> omega

/-- A state code exceeds `8` (its tag does: `stateAtom_ne_faf`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eight_lt_stateCode (m q : ℕ) : 8 < stateCode m q := by
  have h := stateAtom_ne_faf m q _
    (by rw [sentenceAtomCodes_stateAtom]; exact Finset.mem_singleton_self _)
  exact lt_of_lt_of_le h (Nat.unpair_left_le _)

/-- No cell holds a state code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_cellHolds_stateCode (j : Fin 3) (m q : ℕ) : ¬ cellHolds j (stateCode m q) := fun h => by
  have := cellHolds_le h
  have := eight_lt_stateCode m q
  omega

/-- `1` is no state code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma one_ne_stateCode (m q : ℕ) : (1 : ℕ) ≠ stateCode m q := fun h => by
  have := eight_lt_stateCode m q; omega

/-- **The nine worlds at day `n`**: world `(i, j)` holds the day-`(n+1)` state atom of code
`triCode (n+1) i` and the atoms of cell `j`, and nothing else — in particular no state atom of a
day `≠ n+1` (the scaffold, disclosed in the module docstring).
Source: mandate M7 (iii) (repair round 2)
Kind: D
Fidelity: n/a -/
def triWorld (n : ℕ) (i j : Fin 3) : PCWorld :=
  fun a => a = stateCode (n + 1) (triCode (n + 1) i) ∨ cellHolds j a

/-- **The tables over the cells**: `t₁ = (½, ¼, ¼)`, `t₂ = (¼, ½, ¼)`, `t₃ = (¼, ¼, ½)`.
Source: mandate M7 (iii) (repair round 2)
Kind: D
Fidelity: n/a -/
def triTable : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 1 / 2 | 0, 1 => 1 / 4 | 0, 2 => 1 / 4
  | 1, 0 => 1 / 4 | 1, 1 => 1 / 2 | 1, 2 => 1 / 4
  | 2, 0 => 1 / 4 | 2, 1 => 1 / 4 | 2, 2 => 1 / 2

/-- **The market's conditionals given the states**: the tables perturbed by the 3-cycle,
`c₁ = t₁ + ε(0, 1, −1)`, `c₂ = t₂ + ε(−1, 0, 1)`, `c₃ = t₃ + ε(1, −1, 0)`. Rows and columns both
sum to `1`.
Source: mandate M7 (iii) (repair round 2)
Kind: D
Fidelity: n/a -/
def triCond (ε : ℝ) : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 1 / 2     | 0, 1 => 1 / 4 + ε | 0, 2 => 1 / 4 - ε
  | 1, 0 => 1 / 4 - ε | 1, 1 => 1 / 2     | 1, 2 => 1 / 4 + ε
  | 2, 0 => 1 / 4 + ε | 2, 1 => 1 / 4 - ε | 2, 2 => 1 / 2

/-- **The market**: on every day the mixture of the nine worlds, world `(i, j)` weighted
`⅓ · c_{ij}(ε)`.
Source: mandate M7 (iii) (repair round 2)
Kind: D
Fidelity: n/a -/
def triHistory (ε : ℝ) : History :=
  fun n φ => ∑ i : Fin 3, ∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i j * (triWorld n i j).payout φ

/-- **The table of candidate `i` for day `m`**: the mixture of the day-`(m−1)` worlds with
weights `t_{ij} · c_{i'j}(ε)` — cell `j` with probability `t_{ij}`, and within the cell the
market's own posterior over the states. On a sentence mentioning no day-`m` state atom its value
is `∑_j t_{ij} [cell j ⊨ φ]` (`triTableVal_eq_cells`); its values on the day-`m` state atoms are
junk the sources never read. `m − 1` is `Nat` subtraction: at `m = 0` the table is built from
the day-`0` worlds, and no predicate reads a day-`0` table.
Source: mandate M7 (iii) (repair round 2)
Kind: D
Fidelity: n/a -/
def triTableVal (ε : ℝ) (m : ℕ) (i : Fin 3) (φ : Sentence) : ℝ :=
  ∑ i' : Fin 3, ∑ j : Fin 3, triTable i j * triCond ε i' j * (triWorld (m - 1) i' j).payout φ

/-- The index of a code (`triIdx m (triCode m i) = i`); a non-candidate gets index `0`, so every
code has a coherent table.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def triIdx (m q : ℕ) : Fin 3 :=
  if q = triCode m 1 then 1 else if q = triCode m 2 then 2 else 0

/-- **The three-state system**: candidates `triCode m 0, 1, 2`, tables `triTableVal`, realized
state `triCode m 0 = c₁ m`.
Source: mandate M7 (iii) (repair round 2)
Kind: D
Fidelity: n/a -/
def triSystem (ε : ℝ) : StateSystem where
  states m := Finset.univ.image (triCode m)
  val m q φ := triTableVal ε m (triIdx m q) φ
  actual m := triCode m 0
  actual_mem _ := Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-! ## Bookkeeping -/

variable {ε : ℝ} {n : ℕ}

/-- `triIdx m (triCode m i) = i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triIdx_triCode (m : ℕ) (i : Fin 3) : triIdx m (triCode m i) = i := by
  unfold triIdx
  split_ifs with h1 h2
  · exact (triCode_injective m h1).symm
  · exact (triCode_injective m h2).symm
  · fin_cases i
    · rfl
    · exact absurd rfl h1
    · exact absurd rfl h2

/-- The table of a candidate is `triTableVal` at its index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triSystem_val (m : ℕ) (i : Fin 3) (φ : Sentence) :
    (triSystem ε).val m (triCode m i) φ = triTableVal ε m i φ := by
  show triTableVal ε m (triIdx m (triCode m i)) φ = _
  rw [triIdx_triCode]

/-- A candidate is `triCode m i` for some `i`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_triStates {m q : ℕ} (hq : q ∈ (triSystem ε).states m) : ∃ i, triCode m i = q := by
  have hq' : q ∈ Finset.univ.image (triCode m) := hq
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hq'
  exact ⟨i, hi⟩

/-- Sums over the candidates are sums over `Fin 3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_triStates (m : ℕ) (f : ℕ → ℝ) :
    ∑ q ∈ (triSystem ε).states m, f q = ∑ i : Fin 3, f (triCode m i) := by
  show ∑ q ∈ Finset.univ.image (triCode m), f q = _
  exact Finset.sum_image fun i _ j _ h => triCode_injective m h

/-- Filtered sums over the candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_filter_triStates (m : ℕ) (p : ℕ → Prop) (f : ℕ → ℝ) :
    ∑ q ∈ ((triSystem ε).states m).filter p, f q =
      ∑ i : Fin 3, if p (triCode m i) then f (triCode m i) else 0 := by
  rw [Finset.sum_filter, sum_triStates]

/-- Collapsing a `Fin 3` sum of an indicator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_fin3_ite (i' : Fin 3) (f : Fin 3 → ℝ) :
    (∑ i : Fin 3, if i = i' then f i else 0) = f i' := by
  rw [Finset.sum_ite_eq']; simp

/-- The candidates are large (`stateAtom_large`): no candidate atom is small on any day `≤ m`.
Source: mandate M7 (witnesses over large codes)
Kind: L
Fidelity: exact -/
lemma triSystem_large : LargeStates (triSystem ε) := by
  intro m q hq
  obtain ⟨i, rfl⟩ := mem_triStates hq
  apply stateAtom_large
  apply sizeBound_le_log_of_le
  unfold triCode; omega

/-! ## Payouts of the nine worlds -/

/-- Payout of the day-`(n+1)` candidate atoms: world `(i, j)` holds `σ_{i'}` iff `i = i'`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triWorld_payout_stateAtom (i i' j : Fin 3) :
    (triWorld n i j).payout (stateAtom (n + 1) (triCode (n + 1) i')) =
      if i = i' then 1 else 0 := by
  rw [stateAtom_eq_atom]
  unfold PCWorld.payout
  simp only [PCWorld.holds_atom]
  have hc := not_cellHolds_stateCode j (n + 1) (triCode (n + 1) i')
  by_cases h : i = i'
  · subst h; simp [triWorld]
  · have hne : stateCode (n + 1) (triCode (n + 1) i') ≠ stateCode (n + 1) (triCode (n + 1) i) :=
      fun e => h (triCode_injective _ (stateCode_inj.mp e).2).symm
    simp [triWorld, hne, hc, h]

/-- Payout of a state atom of a day `≠ n+1`: `0` in every world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triWorld_payout_stateAtom_ne {m : ℕ} (hm : m ≠ n + 1) (q : ℕ) (i j : Fin 3) :
    (triWorld n i j).payout (stateAtom m q) = 0 := by
  rw [stateAtom_eq_atom]
  unfold PCWorld.payout
  simp only [PCWorld.holds_atom]
  have hc := not_cellHolds_stateCode j m q
  have hne : stateCode m q ≠ stateCode (n + 1) (triCode (n + 1) i) :=
    fun e => hm (stateCode_inj.mp e).1
  simp [triWorld, hne, hc]

/-- Payout of `cohAtom = atom 0`: `1` in cells `0`, `1`; `0` in cell `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triWorld_payout_cohAtom (i : Fin 3) :
    (triWorld n i 0).payout cohAtom = 1 ∧ (triWorld n i 1).payout cohAtom = 1 ∧
      (triWorld n i 2).payout cohAtom = 0 := by
  have h0 := zero_ne_stateCode (n + 1) (triCode (n + 1) i)
  simp [PCWorld.payout, cohAtom, triWorld, cellHolds, h0]

/-- Payout of `triAtom' = atom 1`: `1` in cells `0`, `2`; `0` in cell `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triWorld_payout_triAtom' (i : Fin 3) :
    (triWorld n i 0).payout triAtom' = 1 ∧ (triWorld n i 1).payout triAtom' = 0 ∧
      (triWorld n i 2).payout triAtom' = 1 := by
  have h1 := one_ne_stateCode (n + 1) (triCode (n + 1) i)
  simp [PCWorld.payout, triAtom', triWorld, cellHolds, h1]

/-- **Substitution**: on a sentence whose atoms all have day `< n+1` (in particular on every
`φ ∈ Sminus (n+1) (n+1)`), the payout of world `(i, j)` does not depend on `i` — the state atom
is the only thing that distinguishes the worlds of one cell.
Source: none: infrastructure (FAF `PCWorld.holds_congr_atomCodes`, `atomDay_stateAtom`)
Kind: L
Fidelity: n/a -/
lemma triWorld_payout_congr {φ : Sentence} (hφ : ∀ a ∈ sentenceAtomCodes φ, atomDay a < n + 1)
    (i i' j : Fin 3) : (triWorld n i j).payout φ = (triWorld n i' j).payout φ := by
  have hne : ∀ a ∈ sentenceAtomCodes φ, ∀ q, a ≠ stateCode (n + 1) q := by
    intro a ha q h
    have h1 := atomDay_stateAtom (n + 1) q a
      (by rw [sentenceAtomCodes_stateAtom, h]; exact Finset.mem_singleton_self _)
    have h2 := hφ a ha
    omega
  have key : (triWorld n i j).Holds φ ↔ (triWorld n i' j).Holds φ := by
    apply PCWorld.holds_congr_atomCodes
    intro a ha
    have := hne a ha
    simp only [triWorld]
    simp [this]
  unfold PCWorld.payout
  simp only [key]

/-- **Every world holds exactly one day-`(n+1)` candidate atom, and no state atom of any other
day** — the day-`(n+1)` states partition every world of the mixture (the partition reading of
"LUV coherence").
Source: mandate M7 (iii) (repair round 2: audit r2 adversarial B1, "LUV coherence")
Kind: L
Fidelity: n/a -/
theorem triWorld_unique_state (n : ℕ) (i j : Fin 3) :
    (triWorld n i j).Holds (stateAtom (n + 1) (triCode (n + 1) i)) ∧
    (∀ i', i' ≠ i → ¬ (triWorld n i j).Holds (stateAtom (n + 1) (triCode (n + 1) i'))) ∧
    (∀ m q, m ≠ n + 1 → ¬ (triWorld n i j).Holds (stateAtom m q)) := by
  have hp : ∀ ψ, (triWorld n i j).Holds ψ ↔ (triWorld n i j).payout ψ = 1 := by
    intro ψ; unfold PCWorld.payout; split_ifs with h <;> simp [h]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp, triWorld_payout_stateAtom]; simp
  · intro i' hi'; rw [hp, triWorld_payout_stateAtom]; simp [Ne.symm hi']
  · intro m q hm; rw [hp, triWorld_payout_stateAtom_ne hm]; norm_num

/-! ## The market on the sentences the constraints read -/

/-- `𝐏_n(σ_{n+1,i}) = ⅓`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triHistory_stateAtom (i : Fin 3) :
    triHistory ε n (stateAtom (n + 1) (triCode (n + 1) i)) = 1 / 3 := by
  unfold triHistory
  simp only [triWorld_payout_stateAtom]
  have h : ∀ i' : Fin 3, (∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i' j * if i' = i then 1 else 0) =
      if i' = i then ∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i' j else 0 := by
    intro i'; split_ifs <;> simp
  simp only [h, sum_fin3_ite]
  fin_cases i <;> simp [Fin.sum_univ_three, triCond] <;> ring

/-- `𝐏_n(φ ⋏ σ_{n+1,i}) = ⅓ ∑_j c_{ij} π_{ij}(φ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triHistory_and_state (i : Fin 3) (φ : Sentence) :
    triHistory ε n (φ ⋏ stateAtom (n + 1) (triCode (n + 1) i)) =
      ∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i j * (triWorld n i j).payout φ := by
  unfold triHistory
  simp only [payout_and, triWorld_payout_stateAtom]
  have h : ∀ i' : Fin 3, (∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i' j *
      ((triWorld n i' j).payout φ * if i' = i then 1 else 0)) =
      if i' = i then ∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i' j * (triWorld n i' j).payout φ
      else 0 := by
    intro i'; split_ifs <;> simp
  simp only [h, sum_fin3_ite]

/-- The same, with the cell payouts read in world `(0, j)` when `φ`'s atoms have day `< n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triHistory_and_state_cells {φ : Sentence}
    (hφ : ∀ a ∈ sentenceAtomCodes φ, atomDay a < n + 1) (i : Fin 3) :
    triHistory ε n (φ ⋏ stateAtom (n + 1) (triCode (n + 1) i)) =
      ∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i j * (triWorld n 0 j).payout φ := by
  rw [triHistory_and_state]
  exact Finset.sum_congr rfl fun j _ => by rw [triWorld_payout_congr hφ i 0 j]

/-- `𝐏_n(σ_{m,q}) = 0` for `m ≠ n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triHistory_stateAtom_ne {m : ℕ} (hm : m ≠ n + 1) (q : ℕ) :
    triHistory ε n (stateAtom m q) = 0 := by
  unfold triHistory; simp [triWorld_payout_stateAtom_ne hm]

/-- `𝐏_n(φ ⋏ σ_{m,q}) = 0` for `m ≠ n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triHistory_and_stateAtom_ne {m : ℕ} (hm : m ≠ n + 1) (q : ℕ) (φ : Sentence) :
    triHistory ε n (φ ⋏ stateAtom m q) = 0 := by
  unfold triHistory; simp [payout_and, triWorld_payout_stateAtom_ne hm]

/-- `𝐏_n(φ ⋏ (σ_{m,q₁} ⋏ σ_{o,q₂})) = 0` for `o ≠ n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triHistory_and_two_ne {o : ℕ} (ho : o ≠ n + 1) (m q₁ q₂ : ℕ) (φ : Sentence) :
    triHistory ε n (φ ⋏ (stateAtom m q₁ ⋏ stateAtom o q₂)) = 0 := by
  unfold triHistory; simp [payout_and, triWorld_payout_stateAtom_ne ho]

/-- `𝐏_n(σ_{m,q₁} ⋏ σ_{o,q₂}) = 0` for `o ≠ n+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triHistory_two_ne {o : ℕ} (ho : o ≠ n + 1) (m q₁ q₂ : ℕ) :
    triHistory ε n (stateAtom m q₁ ⋏ stateAtom o q₂) = 0 := by
  unfold triHistory; simp [payout_and, triWorld_payout_stateAtom_ne ho]

/-- Exclusivity of the day-`(n+1)` candidates inside every world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triHistory_excl {i i' : Fin 3} (h : i ≠ i') :
    triHistory ε n (stateAtom (n + 1) (triCode (n + 1) i) ⋏
      stateAtom (n + 1) (triCode (n + 1) i')) = 0 := by
  unfold triHistory
  simp only [payout_and, triWorld_payout_stateAtom]
  apply Finset.sum_eq_zero; intro k _; apply Finset.sum_eq_zero; intro j _
  by_cases hk : k = i
  · subst hk; simp [h]
  · simp [hk]

/-! ## The tables on the sentences the constraints read -/

/-- The columns of `triCond` sum to `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triCond_col_sum (j : Fin 3) : ∑ i : Fin 3, triCond ε i j = 1 := by
  fin_cases j <;> simp [Fin.sum_univ_three, triCond] <;> ring

/-- **The table on a scoped sentence**: when `φ`'s atoms have day `< n+1`, candidate `i`'s
day-`(n+1)` table gives `φ` the value `∑_j t_{ij} [cell j ⊨ φ]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triTableVal_eq_cells {φ : Sentence}
    (hφ : ∀ a ∈ sentenceAtomCodes φ, atomDay a < n + 1) (i : Fin 3) :
    triTableVal ε (n + 1) i φ = ∑ j : Fin 3, triTable i j * (triWorld n 0 j).payout φ := by
  unfold triTableVal
  rw [Nat.add_sub_cancel]
  have hc : ∀ i' j, (triWorld n i' j).payout φ = (triWorld n 0 j).payout φ :=
    fun i' j => triWorld_payout_congr hφ i' 0 j
  simp only [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i' : Fin 3, triTable i j * triCond ε i' j * (triWorld n 0 j).payout φ
      = (∑ i' : Fin 3, triCond ε i' j) * (triTable i j * (triWorld n 0 j).payout φ) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i' _ => by ring
    _ = triTable i j * (triWorld n 0 j).payout φ := by rw [triCond_col_sum, one_mul]

/-- The tables at `cohAtom`: `t_{i0} + t_{i1}` (`¾, ¾, ½`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triTableVal_cohAtom (m : ℕ) (i : Fin 3) :
    triTableVal ε m i cohAtom = triTable i 0 + triTable i 1 := by
  unfold triTableVal
  have h := fun i' => triWorld_payout_cohAtom (n := m - 1) i'
  simp only [Fin.sum_univ_three]
  rw [(h 0).1, (h 0).2.1, (h 0).2.2, (h 1).1, (h 1).2.1, (h 1).2.2, (h 2).1, (h 2).2.1, (h 2).2.2]
  simp only [triCond]; ring

/-- The tables at `triAtom'`: `t_{i0} + t_{i2}` (`¾, ½, ¾`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triTableVal_triAtom' (m : ℕ) (i : Fin 3) :
    triTableVal ε m i triAtom' = triTable i 0 + triTable i 2 := by
  unfold triTableVal
  have h := fun i' => triWorld_payout_triAtom' (n := m - 1) i'
  simp only [Fin.sum_univ_three]
  rw [(h 0).1, (h 0).2.1, (h 0).2.2, (h 1).1, (h 1).2.1, (h 1).2.2, (h 2).1, (h 2).2.1, (h 2).2.2]
  simp only [triCond]; ring

/-- **The three tables are pairwise distinct** (as functions on sentences): they differ at
`cohAtom` or at `triAtom'`.
Source: mandate M7 (iii) (repair round 2: audit r2 adversarial B1, "two codes, one table")
Kind: P
Fidelity: exact -/
theorem triTableVal_ne (m : ℕ) {i i' : Fin 3} (h : i ≠ i') :
    triTableVal ε m i ≠ triTableVal ε m i' := by
  intro heq
  have h1 := congrFun heq cohAtom
  have h2 := congrFun heq triAtom'
  rw [triTableVal_cohAtom, triTableVal_cohAtom] at h1
  rw [triTableVal_triAtom', triTableVal_triAtom'] at h2
  fin_cases i <;> fin_cases i'
  all_goals first | exact absurd rfl h | (have h12 := And.intro h1 h2; norm_num [triTable] at h12)

/-! ## Coherence -/

/-- A function represented as a nonnegative mixture of nine worlds indexed by `Fin 3 × Fin 3` is
`CoherentOn ∅ A` for every atom set `A`.
Source: none: infrastructure (`bli-found` `CoherentOn`)
Kind: L
Fidelity: n/a -/
lemma coherentOn_of_mixture₃ (p : Sentence → ℝ) (W : Fin 3 → Fin 3 → PCWorld)
    (w : Fin 3 → Fin 3 → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hsum : ∑ i : Fin 3, ∑ j : Fin 3, w i j = 1)
    (hp : ∀ φ, p φ = ∑ i : Fin 3, ∑ j : Fin 3, w i j * (W i j).payout φ) (A : Finset ℕ) :
    CoherentOn ∅ A p := by
  let e : Fin 3 × Fin 3 ≃ Fin 9 := finProdFinEquiv
  refine ⟨9, fun k => W (e.symm k).1 (e.symm k).2, fun k => w (e.symm k).1 (e.symm k).2,
    fun i φ h => by simp at h, fun k => hw _ _, ?_, fun φ _ => ?_⟩
  · calc ∑ k : Fin 9, w (e.symm k).1 (e.symm k).2
        = ∑ p : Fin 3 × Fin 3, w p.1 p.2 :=
          Equiv.sum_comp e.symm (fun p : Fin 3 × Fin 3 => w p.1 p.2)
      _ = ∑ i : Fin 3, ∑ j : Fin 3, w i j := Fintype.sum_prod_type' _
      _ = 1 := hsum
  · rw [hp]
    calc ∑ i : Fin 3, ∑ j : Fin 3, w i j * (W i j).payout φ
        = ∑ p : Fin 3 × Fin 3, w p.1 p.2 * (W p.1 p.2).payout φ := (Fintype.sum_prod_type' _).symm
      _ = ∑ k : Fin 9, w (e.symm k).1 (e.symm k).2 * (W (e.symm k).1 (e.symm k).2).payout φ :=
          (Equiv.sum_comp e.symm
            (fun p : Fin 3 × Fin 3 => w p.1 p.2 * (W p.1 p.2).payout φ)).symm

/-- The conditionals are nonnegative for `0 ≤ ε ≤ ¼`, and positive for `0 < ε < ¼`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triCond_nonneg (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 4) (i j : Fin 3) : 0 ≤ triCond ε i j := by
  fin_cases i <;> fin_cases j <;> simp [triCond] <;> linarith

/-- The rows of `triCond` sum to `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triCond_row_sum (i : Fin 3) : ∑ j : Fin 3, triCond ε i j = 1 := by
  fin_cases i <;> simp [Fin.sum_univ_three, triCond] <;> ring

/-- **The market is a world mixture on every day**: `CoherentOn ∅ A (𝐏_n)` for every `n`, `A`
(empty stage: propositional coherence over the atom encoding, no theory; every atom set).
Source: mandate M7 (iii) (repair round 2); `bli-found` `CoherentOn`
Kind: L
Fidelity: exact (every atom set, empty stage — propositional only)
Hyps: (a) `0 ≤ ε ≤ ¼` (nonnegative weights) -/
theorem triHistory_coherent (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 4) (n : ℕ) (A : Finset ℕ) :
    CoherentOn ∅ A (triHistory ε n) :=
  coherentOn_of_mixture₃ _ (triWorld n) (fun i j => (1 / 3 : ℝ) * triCond ε i j)
    (fun i j => mul_nonneg (by norm_num) (triCond_nonneg h0 h1 i j))
    (by
      show ∑ i : Fin 3, ∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i j = 1
      simp only [← Finset.mul_sum, triCond_row_sum, mul_one]
      norm_num [Fin.sum_univ_three])
    (fun _ => rfl) A

/-- **Every table is a world mixture**: `CoherentOn ∅ A (triTableVal ε m i)` for every `A`.
Source: mandate M7 (iii) (repair round 2); `bli-found` `CoherentOn`
Kind: L
Fidelity: exact (every atom set, empty stage — propositional only)
Hyps: (a) `0 ≤ ε ≤ ¼` -/
theorem triTableVal_coherent (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 4) (m : ℕ) (i : Fin 3) (A : Finset ℕ) :
    CoherentOn ∅ A (triTableVal ε m i) :=
  coherentOn_of_mixture₃ _ (triWorld (m - 1)) (fun i' j => triTable i j * triCond ε i' j)
    (fun i' j => mul_nonneg (by fin_cases i <;> fin_cases j <;> norm_num [triTable])
      (triCond_nonneg h0 h1 i' j))
    (by
      show ∑ i' : Fin 3, ∑ j : Fin 3, triTable i j * triCond ε i' j = 1
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, triCond_col_sum, mul_one]
      fin_cases i <;> norm_num [Fin.sum_univ_three, triTable])
    (fun _ => rfl) A

/-! ## The constraints -/

/-- `E1x` with the market's own small prices as the base.
Source: mandate M7 (iii)
Kind: L
Fidelity: exact -/
lemma triHistory_E1x : E1x (triHistory ε) (triHistory ε) := fun _ _ _ => rfl

/-- `E3`: both sides vanish (no day-`n` world holds a state atom of a day `≥ n+2`).
Source: mandate M7 (iii)
Kind: L
Fidelity: exact (full scope) -/
lemma triHistory_E3 : E3 (triSystem ε) (triHistory ε) := by
  intro n m o hnm hmo q₁ _ q₂ _ φ _
  have ho : o ≠ n + 1 := by omega
  rw [triHistory_and_two_ne ho, triHistory_two_ne ho, mul_zero]

/-- `E4`: the mass-weighted average of the three tables is the market (on **every** sentence —
the tables' within-cell posteriors are the market's own).
Source: mandate M7 (iii)
Kind: L
Fidelity: exact -/
lemma triHistory_E4 : E4 (triSystem ε) (triHistory ε) := by
  intro n φ _
  rw [sum_triStates]
  simp only [triHistory_stateAtom, triSystem_val]
  unfold triTableVal triHistory
  rw [Nat.add_sub_cancel]
  simp only [Fin.sum_univ_three, triTable]
  ring

/-- `E5`: masses `⅓ + ⅓ + ⅓` and exclusivity inside every world.
Source: mandate M7 (iii)
Kind: L
Fidelity: exact -/
lemma triHistory_E5 : E5 (triSystem ε) (triHistory ε) := by
  intro n
  constructor
  · rw [sum_triStates]; simp only [triHistory_stateAtom, Fin.sum_univ_three]; norm_num
  · intro q₁ hq₁ q₂ hq₂ hne
    obtain ⟨i, rfl⟩ := mem_triStates hq₁
    obtain ⟨i', rfl⟩ := mem_triStates hq₂
    exact triHistory_excl fun h => hne (h ▸ rfl)

/-- Faith in the marginal at one sentence, abstractly: if the mass-weighted deviations
`d i` of the conditionals from the tables `t i` sum to zero on every level set of `t`, the
filtered joint equals `x` times the filtered mass (masses `⅓`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma faith_of_levelsets (t d f : Fin 3 → ℝ) (x : ℝ)
    (hf : ∀ i, f i = (1 / 3 : ℝ) * (t i + d i))
    (hlev : (∑ i : Fin 3, if t i = x then d i else 0) = 0) :
    (∑ i : Fin 3, if t i = x then f i else 0) =
      x * ∑ i : Fin 3, if t i = x then (1 / 3 : ℝ) else 0 := by
  have h : ∀ i : Fin 3, (if t i = x then f i else 0) =
      x * (if t i = x then (1 / 3 : ℝ) else 0) + (1 / 3 : ℝ) * (if t i = x then d i else 0) := by
    intro i
    rw [hf i]
    split_ifs with hx
    · rw [hx]; ring
    · ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hlev]
  ring

set_option maxHeartbeats 400000 in
/-- **The level-set check**: on every event of the cell algebra (`v j ∈ {0, 1}` the indicator of
cell `j`), the states whose table values agree have deviations summing to zero — the eight
events, exhaustively.
Source: mandate M7 (iii) (repair round 2)
Kind: P
Fidelity: n/a -/
lemma triLevel (v : Fin 3 → ℝ) (hv : ∀ j, v j = 0 ∨ v j = 1) (x : ℝ) :
    (∑ i : Fin 3, if (∑ j : Fin 3, triTable i j * v j) = x then
      ∑ j : Fin 3, (triCond ε i j - triTable i j) * v j else 0) = 0 := by
  rcases hv 0 with h0 | h0 <;> rcases hv 1 with h1 | h1 <;> rcases hv 2 with h2 | h2 <;>
  simp only [Fin.sum_univ_three, h0, h1, h2, triTable, triCond] <;>
  norm_num <;> (try split_ifs) <;> linarith

/-- **`FaithMarginal` for the witness.** At `(n, n+1)` and `φ ∈ Sminus (n+1) (n+1)`, both the
tables and the conditionals read `φ` through the cells (`triTableVal_eq_cells`,
`triHistory_and_state_cells`), and on each of the eight events of the cell algebra the states
whose table values agree have deviations summing to zero (`triLevel`). At `(n, m)` with
`m ≥ n+2` every term is `0` (the scaffold).
Source: mandate M7 (iii) (repair round 2); bli-slides-015 (ii)
Kind: P
Fidelity: exact (full scope) -/
theorem triHistory_faithMarginal : FaithMarginal (triSystem ε) (triHistory ε) := by
  intro n m hnm φ hφ x
  unfold marginalJoint marginalMass
  by_cases hm : m = n + 1
  · subst hm
    rw [sum_filter_triStates, sum_filter_triStates]
    have hday : ∀ a ∈ sentenceAtomCodes φ, atomDay a < n + 1 := (mem_Sminus.mp hφ).2
    simp only [triSystem_val, triTableVal_eq_cells hday, triHistory_and_state_cells hday,
      triHistory_stateAtom]
    refine faith_of_levelsets (fun i => ∑ j : Fin 3, triTable i j * (triWorld n 0 j).payout φ)
      (fun i => ∑ j : Fin 3, (triCond ε i j - triTable i j) * (triWorld n 0 j).payout φ)
      (fun i => ∑ j : Fin 3, (1 / 3 : ℝ) * triCond ε i j * (triWorld n 0 j).payout φ) x ?_ ?_
    · intro i
      simp only [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · exact triLevel (fun j => (triWorld n 0 j).payout φ)
        (fun j => payout_eq_zero_or_one (triWorld n 0 j) φ) x
  · rw [Finset.sum_eq_zero fun q _ => triHistory_and_stateAtom_ne hm q φ,
      Finset.sum_eq_zero fun q _ => triHistory_stateAtom_ne hm q, mul_zero]

/-- **`E2x` fails for the witness** at `(0, 1, triCode 1 0, cohAtom)`:
`𝐏_0(cohAtom ⋏ σ_{1,0}) = ⅓ (¾ + ε)` while `𝑸̂₀[cohAtom] · 𝐏_0(σ_{1,0}) = ¾ · ⅓`.
Source: mandate M7 (iii)
Kind: L
Fidelity: exact
Hyps: (a) `ε ≠ 0` -/
lemma triHistory_not_E2x (hε : ε ≠ 0) : ¬ E2x (triSystem ε) (triHistory ε) := by
  intro hE2
  have hq : triCode 1 0 ∈ (triSystem ε).states 1 :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hday : ∀ a ∈ sentenceAtomCodes cohAtom, atomDay a < 0 + 1 :=
    (mem_Sminus.mp (cohAtom_mem_Sminus le_rfl)).2
  have := hE2 0 1 (by norm_num) _ hq cohAtom (cohAtom_mem_Sminus le_rfl)
  rw [triHistory_and_state_cells hday, triHistory_stateAtom, triSystem_val,
    triTableVal_eq_cells hday] at this
  obtain ⟨w0, w1, w2⟩ := triWorld_payout_cohAtom (n := 0) 0
  simp only [Fin.sum_univ_three, w0, w1, w2, triTable, triCond] at this
  apply hε; linarith

/-! ## The headline -/

/-- **`faithMarginal_coherent_distinct_not_imp_e2x` — coherence plus faith in the marginal does
not imply faith in the state, with three pairwise distinct coherent tables** (the coherence horn
of M7 (iii) under the injective reading; repair round 2 of audit r2 adversarial B1). Notion
ll. 215–225: "LUV coherence plus conditional trust … implies *all* the BLI conditions";
ATTRIBUTION-UNVETTED that "conditional trust" is `FaithMarginal`; "LUV coherence" read as:
the market is a mixture of FAF `PCWorld`s on every sentence, every world holds exactly one
next-day candidate (`triWorld_unique_state`), every table is itself a world mixture, and
distinct candidates are distinct tables. Witness: `triHistory ε` (nine worlds per day, weights
`⅓ c_{ij}(ε)`, all positive for `0 < ε < ¼`), `triSystem ε` (tables `t_i` over three cells, the
3-cycle perturbation `c_i`). The conclusion lists: coherence of market, base and every table on
every atom set; the tables pairwise distinct; `E1x ∧ E3 ∧ E4 ∧ E5 ∧ FaithMarginal` on the **full**
scope; `¬ E2x` at `(0, 1, triCode 1 0, cohAtom)`. N+ on the coordinate that matters: three
positive-mass states with distinct interior tables, every world charged. Scaffold (disclosed):
the day-`n` mixture gives mass `0` to every state of a day `≥ n+2` (F-19). Surviving
neighbours: `Pinning.two_state_pinning`/`_scope` (two distinct tables *are* pinned), and
refinement-invariant trust, which *is* `E2x`.
Source: Notion ll. 215–225 (bli-paper-060); bli-slides-015 (b); bli-soto-a-009; mandate M7 (iii)
Kind: P
Fidelity: exact (refutation; coherence relative to the empty stage on every atom set; the
partition and injectivity readings of "LUV coherence" built into the witness)
Hyps: (a) `0 < ε`, `ε < ¼` (the witness's parameter) -/
theorem faithMarginal_coherent_distinct_not_imp_e2x (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 4) :
    ∃ (S : StateSystem) (Q P : History),
      (∀ n A, CoherentOn ∅ A (P n)) ∧ (∀ n A, CoherentOn ∅ A (Q n)) ∧
      (∀ m q A, CoherentOn ∅ A (S.val m q)) ∧
      (∀ m, ∀ q ∈ S.states m, ∀ q' ∈ S.states m, q ≠ q' → S.val m q ≠ S.val m q') ∧
      E1x Q P ∧ E3 S P ∧ E4 S P ∧ E5 S P ∧ FaithMarginal S P ∧ ¬ E2x S P := by
  have hc : ∀ n A, CoherentOn ∅ A (triHistory ε n) := triHistory_coherent hε.le hε'.le
  refine ⟨triSystem ε, triHistory ε, triHistory ε, hc, hc,
    fun m q A => triTableVal_coherent hε.le hε'.le m (triIdx m q) A, ?_,
    triHistory_E1x, triHistory_E3, triHistory_E4, triHistory_E5, triHistory_faithMarginal,
    triHistory_not_E2x hε.ne'⟩
  intro m q hq q' hq' hne
  obtain ⟨i, rfl⟩ := mem_triStates hq
  obtain ⟨i', rfl⟩ := mem_triStates hq'
  have hii : i ≠ i' := fun h => hne (h ▸ rfl)
  intro heq
  apply triTableVal_ne (ε := ε) m hii
  funext φ
  have := congrFun heq φ
  rwa [triSystem_val, triSystem_val] at this

/-- **All nine worlds are charged** under the headline's hypotheses (the N+ certificate).
Source: mandate M7 (iii) (N+ grading)
Kind: N+
Fidelity: n/a
Hyps: (a) `0 < ε < ¼` -/
theorem triCond_pos (hε : 0 < ε) (hε' : ε < 1 / 4) (i j : Fin 3) : 0 < triCond ε i j := by
  fin_cases i <;> fin_cases j <;> simp [triCond] <;> linarith

end

end Cleanroom.Bli.BliTrajectory
