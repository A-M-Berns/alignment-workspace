import Cleanroom.Bli.BliExtrapolation.Conditioning
import Cleanroom.Bli.BliExtrapolation.Witnesses
import Cleanroom.Bli.BliExtrapolation.Extension

/-!
# `bli-extrapolation` · ConstraintWitnesses: the constraint-2 / partition witness and the
full-support witness (targets 5b, 5c, 10; repair round 1)

* **`constraint2_witness`** (5b (i) and 5c (iv), N+): a two-price grid `{¼, ¾}` whose price
  events are two atoms `a₀ = atom (e 0)`, `a₁ = atom (e 1)` made exclusive and exhaustive
  **almost everywhere** by the base rule (`twoCellRule`: `a₀` has probability `⅓`; `a₁` has
  probability `0` given `a₀` and `1` given `¬a₀`), not propositionally (the all-true world holds
  both atoms — a conjunct of the theorem says so). Cell masses `⅓`, `⅔`; under the constraint-2
  rule at the level of the large sentence `φ = a₂ = atom (e 2)`, `P(a₀ ∧ a₂) = ¼ · ⅓` and
  `P(a₁ ∧ a₂) = ¾ · ⅔` by `constraint2_definitional`, and `P(a₂) = 7/12` by
  `partition_gives_balance`. This is the shape BLI constraint 2 has (the price events
  `⌜P_{n+1}(φ) = q⌝` are distinct prime sentences, exclusive under the measure and not
  propositionally), which the round-1 audits found the previous atom-valued, all-worlds-exclusive
  statement could not express for two prices.
* **`halving_fullSupport`** / **`halving_pos_of_axConsistent`** (10, N+): the halving base has
  full support on the `Ax`-consistent conjunctions, so `extrapolate_pos_of_axConsistent`'s
  hypothesis package is inhabited and every `Ax`-consistent sentence has positive value there.

Every value is stated for an arbitrary enumeration `e` (the witness does not depend on it).

Sources: PDF 06 p. 1; [[bli-soto-a-2-inventory]] 005 (i)/(iv); mandate targets 5b, 5c, 10;
[[bli-extrapolation-audit-r1-fidelity]] B1/N8; [[bli-extrapolation-audit-r1-adversarial]] B1/§3.4.
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld Finset

/-! ## Values of the first atom under any rule -/

/-- The first enumerated atom's value is the level-`0` conditional.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_atom_zero (e : ℕ ≃ ℕ) (p : CondRule) :
    chainVal e p (Formula.atom (e 0)) = p 0 Fin.elim0 := by
  have h := chainVal_and_atom e p (E := ⊤) (k := 0) (by simp) (p 0 Fin.elim0)
    (fun u _ => Or.inr (by rw [Subsingleton.elim u Fin.elim0]))
  rw [chainVal_top, mul_one] at h
  rw [← h]
  exact chainVal_congr e p fun v => by
    rw [PCWorld.holds_and]
    exact ⟨fun h => ⟨PCWorld.holds_top v, h⟩, fun h => h.2⟩

/-- The negation of the first enumerated atom has value one minus the level-`0` conditional.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_neg_atom_zero (e : ℕ ≃ ℕ) (p : CondRule) :
    chainVal e p (∼Formula.atom (e 0)) = 1 - p 0 Fin.elim0 := by
  have h := chainVal_and_neg_atom e p (E := ⊤) (k := 0) (by simp) (p 0 Fin.elim0)
    (fun u _ => Or.inr (by rw [Subsingleton.elim u Fin.elim0]))
  rw [chainVal_top, mul_one] at h
  rw [← h]
  exact chainVal_congr e p fun v => by
    rw [PCWorld.holds_and]
    exact ⟨fun h => ⟨PCWorld.holds_top v, h⟩, fun h => h.2⟩

/-- A level-`1` world holds the first enumerated atom iff its bit is `true`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_atom_zero_iff (e : ℕ ≃ ℕ) (u : FiniteWorld 1) :
    (enumWorld e u).toPCWorld.Holds (Formula.atom (e 0)) ↔ u 0 = true := by
  rw [PCWorld.holds_atom]
  simp [BoolPCWorld.toPCWorld, enumWorld]

/-! ## The two-cell base rule -/

/-- **The two-cell base rule**: the first atom `a₀` has probability `⅓`; the second atom `a₁`
has probability `0` given `a₀` and `1` given `¬a₀`; every later atom `½`. Under its chain `a₀`
and `a₁` are exclusive and exhaustive **almost everywhere** (the worlds `a₀ ∧ a₁` and
`¬a₀ ∧ ¬a₁` are null) but not propositionally (the all-true world holds both atoms).
Source: mandate 5b (witness); [[bli-soto-a-2-inventory]] 005 (i)
Kind: D
Fidelity: n/a -/
def twoCellRule : CondRule
  | 0, _ => 1 / 3
  | 1, u => if u 0 then 0 else 1
  | _ + 2, _ => 1 / 2

/-- `twoCellRule` takes values in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCellRule_inUnit : twoCellRule.InUnit := by
  intro k u
  match k, u with
  | 0, u => simp only [twoCellRule]; norm_num
  | 1, u => simp only [twoCellRule]; split_ifs <;> norm_num
  | k + 2, u => simp only [twoCellRule]; norm_num

/-- `twoCellRule` at level `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCellRule_zero (u : FiniteWorld 0) : twoCellRule 0 u = 1 / 3 := rfl

/-- `twoCellRule` at level `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCellRule_one (u : FiniteWorld 1) : twoCellRule 1 u = if u 0 then 0 else 1 := rfl

/-- Under `twoCellRule`, `P(a₀) = ⅓`.
Source: mandate 5b (witness)
Kind: N+
Fidelity: n/a -/
lemma twoCell_val_a0 (e : ℕ ≃ ℕ) : chainVal e twoCellRule (Formula.atom (e 0)) = 1 / 3 := by
  rw [chainVal_atom_zero]; rfl

/-- Under `twoCellRule`, `P(¬a₀) = ⅔`.
Source: mandate 5b (witness)
Kind: N+
Fidelity: n/a -/
lemma twoCell_val_neg_a0 (e : ℕ ≃ ℕ) : chainVal e twoCellRule (∼Formula.atom (e 0)) = 2 / 3 := by
  rw [chainVal_neg_atom_zero, twoCellRule_zero]; norm_num

/-- Under `twoCellRule`, `P(a₀ ∧ a₁) = 0`: the two cells are exclusive almost everywhere.
Source: mandate 5b (witness)
Kind: N+
Fidelity: n/a -/
lemma twoCell_val_a0_a1 (e : ℕ ≃ ℕ) :
    chainVal e twoCellRule (Formula.atom (e 0) ⋏ Formula.atom (e 1)) = 0 := by
  have hc : ∀ u : FiniteWorld 1, (enumWorld e u).toPCWorld.Holds (Formula.atom (e 0)) →
      chainPMF twoCellRule 1 u = 0 ∨ twoCellRule 1 u = 0 := by
    intro u hu
    right
    rw [twoCellRule_one, if_pos ((holds_atom_zero_iff e u).mp hu)]
  rw [chainVal_and_atom e twoCellRule (by simp) 0 hc, zero_mul]

/-- Under `twoCellRule`, `P(¬a₀ ∧ a₁) = ⅔`: the second cell is the complement of the first
almost everywhere.
Source: mandate 5b (witness)
Kind: N+
Fidelity: n/a -/
lemma twoCell_val_neg_a0_a1 (e : ℕ ≃ ℕ) :
    chainVal e twoCellRule (∼Formula.atom (e 0) ⋏ Formula.atom (e 1)) = 2 / 3 := by
  have hc : ∀ u : FiniteWorld 1, (enumWorld e u).toPCWorld.Holds (∼Formula.atom (e 0)) →
      chainPMF twoCellRule 1 u = 0 ∨ twoCellRule 1 u = 1 := by
    intro u hu
    right
    rw [PCWorld.holds_neg, holds_atom_zero_iff] at hu
    rw [twoCellRule_one, if_neg hu]
  rw [chainVal_and_atom e twoCellRule (by simp) 1 hc, one_mul, twoCell_val_neg_a0]

/-- Under `twoCellRule`, `P(a₁) = ⅔`.
Source: mandate 5b (witness)
Kind: N+
Fidelity: n/a -/
lemma twoCell_val_a1 (e : ℕ ≃ ℕ) : chainVal e twoCellRule (Formula.atom (e 1)) = 2 / 3 := by
  rw [chainVal_split e twoCellRule (Formula.atom (e 0)), twoCell_val_a0_a1,
    twoCell_val_neg_a0_a1]
  norm_num

/-! ## The two-price grid and its constraint-2 rule -/

/-- The two-price grid `{¼, ¾}`.
Source: mandate 5b (witness)
Kind: D
Fidelity: n/a -/
def twoCellGrid : Finset ℚ := {1 / 4, 3 / 4}

/-- Membership in the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_twoCellGrid (r : ℚ) : r ∈ twoCellGrid ↔ r = 1 / 4 ∨ r = 3 / 4 := by
  simp [twoCellGrid]

/-- The price events: `⌜P(φ) = ¼⌝ := a₀`, `⌜P(φ) = ¾⌝ := a₁` (atoms, as BLI's price events are
prime sentences; exclusive only under the base).
Source: mandate 5b (witness); [[bli-soto-a-2-inventory]] 005 (i)
Kind: D
Fidelity: n/a -/
def twoCellEvent (e : ℕ ≃ ℕ) (r : ℚ) : Sentence :=
  if r = 1 / 4 then Formula.atom (e 0) else Formula.atom (e 1)

/-- The `¼` event is `a₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCellEvent_quarter (e : ℕ ≃ ℕ) : twoCellEvent e (1 / 4) = Formula.atom (e 0) :=
  if_pos rfl

/-- The `¾` event is `a₁`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCellEvent_threeQuarters (e : ℕ ≃ ℕ) : twoCellEvent e (3 / 4) = Formula.atom (e 1) :=
  if_neg (by norm_num)

/-- Both price events have level `≤ 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCellEvent_level (e : ℕ ≃ ℕ) : ∀ r ∈ twoCellGrid, level e (twoCellEvent e r) ≤ 2 := by
  intro r hr
  rcases (mem_twoCellGrid r).mp hr with rfl | rfl
  · rw [twoCellEvent_quarter]; simp
  · rw [twoCellEvent_threeQuarters]; simp

/-- The price events are exclusive almost everywhere under `twoCellRule`.
Source: mandate 5b (witness)
Kind: N+
Fidelity: n/a -/
lemma twoCell_exclusive (e : ℕ ≃ ℕ) : ∀ r ∈ twoCellGrid, ∀ r' ∈ twoCellGrid, r ≠ r' →
    chainVal e twoCellRule (twoCellEvent e r ⋏ twoCellEvent e r') = 0 := by
  intro r hr r' hr' hne
  rcases (mem_twoCellGrid r).mp hr with rfl | rfl <;>
    rcases (mem_twoCellGrid r').mp hr' with rfl | rfl
  · exact absurd rfl hne
  · rw [twoCellEvent_quarter, twoCellEvent_threeQuarters]
    exact twoCell_val_a0_a1 e
  · rw [twoCellEvent_quarter, twoCellEvent_threeQuarters]
    exact (chainVal_congr e twoCellRule fun v => by
      rw [PCWorld.holds_and, PCWorld.holds_and, and_comm]).trans (twoCell_val_a0_a1 e)
  · exact absurd rfl hne

/-- **The witness's constraint-2 rule**: `twoCellRule` below level `2`, the constraint-2 clause
on the grid at level `2` (the large sentence is `a₂ = atom (e 2)`), `twoCellRule` above.
Source: mandate 5b (witness)
Kind: D
Fidelity: n/a -/
def twoCellC2Rule (e : ℕ ≃ ℕ) : CondRule :=
  constraint2Rule e twoCellRule 2 twoCellGrid (twoCellEvent e)

/-- The witness's rule takes values in `[0,1]` (at level `2` the clause sums at most `¼ + ¾`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCellC2Rule_inUnit (e : ℕ ≃ ℕ) : (twoCellC2Rule e).InUnit := by
  intro k u
  by_cases hk : k = 2
  · subst hk
    simp only [twoCellC2Rule, constraint2Rule, if_true, twoCellGrid]
    rw [Finset.sum_pair (by norm_num : (1 / 4 : ℚ) ≠ 3 / 4)]
    split_ifs <;> norm_num
  · simp only [twoCellC2Rule, constraint2Rule, if_neg hk]
    exact twoCellRule_inUnit k u

/-- Below level `2` the witness's rule is the two-cell rule, so sentences of level `≤ 2` keep
their two-cell values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoCellC2Rule_val_of_le (e : ℕ ≃ ℕ) (φ : Sentence) (hφ : level e φ ≤ 2) :
    chainVal e (twoCellC2Rule e) φ = chainVal e twoCellRule φ := by
  apply chainVal_congr_below
  intro j hj
  funext u
  have : j ≠ 2 := by omega
  simp [twoCellC2Rule, constraint2Rule, this]

/-- **`constraint2_witness`** (5b (i) / 5c (iv), N+): the full hypothesis package of
`constraint2_definitional` with a two-price grid, inhabited and exercised. Under the witness's
rule (for any enumeration `e`): the cells `a₀`, `a₁` have masses `⅓`, `⅔` and null
intersection; they are **not** propositionally exclusive (a world holds both); constraint 2
holds on both cells, `P(a₀ ∧ a₂) = ¼ · ⅓` and `P(a₁ ∧ a₂) = ¾ · ⅔`; and the balance
`P(a₂) = ¼ · ⅓ + ¾ · ⅔ = 7/12` follows from `partition_gives_balance` (the cells partition the
mass almost everywhere). Grade N+: two distinct prices, two positive-mass cells of unequal mass,
the a.e. (not propositional) exclusivity clause is what the package needs, and the balance is
not the value `½` a symmetric rule would give.
Source: mandate 5b/5c (witness); [[bli-soto-a-2-inventory]] 005 (i)/(iv);
[[bli-extrapolation-audit-r1-fidelity]] B1/N8
Kind: N+
Fidelity: n/a
Hyps: (a) none (all discharged) -/
theorem constraint2_witness (e : ℕ ≃ ℕ) :
    chainVal e (twoCellC2Rule e) (Formula.atom (e 0)) = 1 / 3 ∧
    chainVal e (twoCellC2Rule e) (Formula.atom (e 1)) = 2 / 3 ∧
    chainVal e (twoCellC2Rule e) (Formula.atom (e 0) ⋏ Formula.atom (e 1)) = 0 ∧
    (∃ v : PCWorld, v.Holds (Formula.atom (e 0)) ∧ v.Holds (Formula.atom (e 1))) ∧
    chainVal e (twoCellC2Rule e) (Formula.atom (e 0) ⋏ Formula.atom (e 2)) = 1 / 4 * (1 / 3) ∧
    chainVal e (twoCellC2Rule e) (Formula.atom (e 1) ⋏ Formula.atom (e 2)) = 3 / 4 * (2 / 3) ∧
    chainVal e (twoCellC2Rule e) (Formula.atom (e 2)) = 7 / 12 := by
  have h0 : chainVal e (twoCellC2Rule e) (Formula.atom (e 0)) = 1 / 3 := by
    rw [twoCellC2Rule_val_of_le e _ (by simp), twoCell_val_a0]
  have h1 : chainVal e (twoCellC2Rule e) (Formula.atom (e 1)) = 2 / 3 := by
    rw [twoCellC2Rule_val_of_le e _ (by simp), twoCell_val_a1]
  have h01 : chainVal e (twoCellC2Rule e) (Formula.atom (e 0) ⋏ Formula.atom (e 1)) = 0 := by
    rw [twoCellC2Rule_val_of_le e _ (by simp), twoCell_val_a0_a1]
  have h10 : chainVal e (twoCellC2Rule e) (Formula.atom (e 1) ⋏ Formula.atom (e 0)) = 0 := by
    rw [twoCellC2Rule_val_of_le e _ (by simp)]
    exact (chainVal_congr e twoCellRule fun v => by
      rw [PCWorld.holds_and, PCWorld.holds_and, and_comm]).trans (twoCell_val_a0_a1 e)
  -- constraint 2 on each cell, from `constraint2_definitional`
  have hc0 : chainVal e (twoCellC2Rule e) (Formula.atom (e 0) ⋏ Formula.atom (e 2)) =
      1 / 4 * chainVal e (twoCellC2Rule e) (Formula.atom (e 0)) := by
    have := constraint2_definitional e twoCellRule_inUnit 2 twoCellGrid (twoCellEvent e)
      (twoCellEvent_level e) (twoCell_exclusive e) (r := 1 / 4)
      ((mem_twoCellGrid _).mpr (Or.inl rfl))
    rwa [twoCellEvent_quarter] at this
  have hc1 : chainVal e (twoCellC2Rule e) (Formula.atom (e 1) ⋏ Formula.atom (e 2)) =
      3 / 4 * chainVal e (twoCellC2Rule e) (Formula.atom (e 1)) := by
    have := constraint2_definitional e twoCellRule_inUnit 2 twoCellGrid (twoCellEvent e)
      (twoCellEvent_level e) (twoCell_exclusive e) (r := 3 / 4)
      ((mem_twoCellGrid _).mpr (Or.inr rfl))
    rwa [twoCellEvent_threeQuarters] at this
  have hc0' := hc0
  have hc1' := hc1
  rw [h0] at hc0'
  rw [h1] at hc1'
  refine ⟨h0, h1, h01, ⟨fun _ => True, (PCWorld.holds_atom _ _).mpr trivial,
    (PCWorld.holds_atom _ _).mpr trivial⟩, hc0', hc1', ?_⟩
  -- the balance through the partition lemma
  have hbal := partition_gives_balance e (twoCellC2Rule_inUnit e) (ι := Bool)
    (fun b => if b then Formula.atom (e 0) else Formula.atom (e 1)) (Formula.atom (e 2))
    (fun b => if b then 1 / 4 else 3 / 4) ?_ ?_ ?_
  · rw [hbal, Fintype.sum_bool]
    show 1 / 4 * chainVal e (twoCellC2Rule e) (Formula.atom (e 0)) +
      3 / 4 * chainVal e (twoCellC2Rule e) (Formula.atom (e 1)) = 7 / 12
    rw [h0, h1]
    norm_num
  · intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · exact h10
    · exact h01
    · exact absurd rfl hij
  · rw [Fintype.sum_bool]
    show chainVal e (twoCellC2Rule e) (Formula.atom (e 0)) +
      chainVal e (twoCellC2Rule e) (Formula.atom (e 1)) = 1
    rw [h0, h1]
    norm_num
  · intro b
    cases b
    · exact hc1
    · exact hc0

/-! ## Full support for the halving base (target 10) -/

open Classical in
/-- **`halving_fullSupport`** (10, N+): the halving base (`½` on both level-`1` worlds) has full
support on the `Ax`-consistent conjunctions, so `extrapolate_pos_of_axConsistent`'s hypothesis
package is inhabited.
Source: mandate target 10; [[bli-extrapolation-audit-r1-adversarial]] §3.4
Kind: N+
Fidelity: n/a -/
theorem halving_fullSupport : FullSupport halvingS freshEnum halvingBase := by
  intro u _
  rw [halvingBase_apply]
  norm_num

open Classical in
/-- Under the halving witness every `Ax`-consistent sentence has positive value — the
non-dogmatism theorem instantiated.
Source: mandate target 10
Kind: N+
Fidelity: n/a -/
theorem halving_pos_of_axConsistent (φ : Sentence) (hφ : AxConsistent halvingS {φ}) :
    0 < extrapolateVal halvingS freshEnum halvingBase φ :=
  extrapolate_pos_of_axConsistent halvingS freshEnum (chainPMF_nonneg halfRule_inUnit 1)
    (chainPMF_sum_one halfRule 1) halving_fullSupport hφ

end Cleanroom.Bli.BliExtrapolation
