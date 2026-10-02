import LogicalInduction.Framework.BooleanWorlds
import Cleanroom.Bli.BliExtrapolation.Syntax
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `bli-extrapolation` · Chain: the conditional-chaining family at the rational pmf level
(target 2a; design decision 4)

PDF 06 p. 1 / PDF 07 "Step 2": a probability on every finite conjunction
`(¬)φ₁ ∧ … ∧ (¬)φ_k` is fixed by choosing, in enumeration order, the conditional
`p_C = P(φ_{k+1} | C)`. Here a **conditional rule** is `CondRule := (k : ℕ) → FiniteWorld k → ℚ`
(values meant in `[0,1]`, the predicate `CondRule.InUnit`), `chainPMF p k` the resulting rational
pmf on `FiniteWorld k`, and `chainVal e p φ` the value of a sentence, the sum of the pmf over the
level-`level e φ` worlds in which `φ` holds. Everything here is finite and rational: projectivity
(`chainPMF_marginal`), the four `GaifmanCoherent` clauses in rational form (`chainVal_top`,
`chainVal_congr`, `chainVal_disjoint_add`, `chainVal_mem_Icc`), the cylinder value
(`chainVal_conj`) and the *conditioning-is-definitional* lemma (`chainVal_and_atom`, the content
of [[bli-soto-a-2-inventory]] 005 (i)/(ii) and the engine of the halving argument of target 4b).

**This file never says "measure".** A `chainPMF` family with projectivity is a finitely additive
content; the σ-additive object is `Measure.lean`'s `chainMeasure`, FAF's `gaifmanMeasure` of the
valuation built here (route α of design decision 4).

Sources: [[bli-soto-a-inventory]] 050; PDF 06 p. 1; PDF 07 p. 2.
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld Finset

/-! ## Conditional rules and the chained pmf -/

/-- **Conditional rule** (design decision 4): the conditional probability `p k u` of the
`(k+1)`-st enumerated atom being true given the level-`k` conjunction `u`. Values are meant in
`[0,1]` (`CondRule.InUnit`); nothing is clamped.
Source: PDF 06 p. 1 ("define the conditional … for some `p`"); [[bli-soto-a-inventory]] 050
Kind: D
Fidelity: exact -/
abbrev CondRule : Type := (k : ℕ) → FiniteWorld k → ℚ

/-- A rule takes values in `[0,1]`.
Source: PDF 06 p. 1 ("all our newly defined `p` are in `[0,1]`")
Kind: D
Fidelity: exact -/
def CondRule.InUnit (p : CondRule) : Prop := ∀ k (u : FiniteWorld k), 0 ≤ p k u ∧ p k u ≤ 1

/-- **The chained pmf**: `chainPMF p 0 = 1`; `chainPMF p (k+1) u` multiplies the mass of the
prefix by `p k (prefix)` if the new literal is positive and by `1 - p k (prefix)` otherwise.
Source: PDF 06 p. 1 (the two displays); PDF 07 p. 2 ("`P(C ∧ ¬φ) := P(C) − P(C ∧ φ)`")
Kind: D
Fidelity: exact -/
def chainPMF (p : CondRule) : (k : ℕ) → FiniteWorld k → ℚ
  | 0, _ => 1
  | k + 1, u =>
      chainPMF p k (Fin.init u) * (if u (Fin.last k) then p k (Fin.init u) else 1 - p k (Fin.init u))

/-- The recursion in `snoc` form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainPMF_snoc (p : CondRule) {k : ℕ} (u : FiniteWorld k) (b : Bool) :
    chainPMF p (k + 1) (Fin.snoc u b) = chainPMF p k u * (if b then p k u else 1 - p k u) := by
  simp [chainPMF, Fin.init_snoc, Fin.snoc_last]

/-- Summing over `FiniteWorld (k+1)` is summing over the prefix and the last bit.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_finiteWorld_succ {k : ℕ} (f : FiniteWorld (k + 1) → ℚ) :
    ∑ u, f u = ∑ u : FiniteWorld k, ∑ b : Bool, f (Fin.snoc u b) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

/-- The level-`0` world type has one element and the sum is the value there.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_finiteWorld_zero (f : FiniteWorld 0 → ℚ) : ∑ u, f u = f Fin.elim0 := by
  rw [Fintype.sum_unique]
  rfl

/-- **Projectivity**: the two extensions of `u` carry the mass of `u`.
Source: PDF 06 p. 1 ("we automatically also define `P(C ∧ ¬φ)`"); [[bli-soto-a-inventory]] 050
("consistent marginals")
Kind: P
Fidelity: exact -/
lemma chainPMF_marginal (p : CondRule) {k : ℕ} (u : FiniteWorld k) :
    ∑ b : Bool, chainPMF p (k + 1) (Fin.snoc u b) = chainPMF p k u := by
  rw [Fintype.sum_bool, chainPMF_snoc, chainPMF_snoc]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

/-- The chained pmf sums to one at every level.
Source: PDF 06 p. 1; [[bli-soto-a-inventory]] 050
Kind: P
Fidelity: exact -/
lemma chainPMF_sum_one (p : CondRule) : ∀ k, ∑ u : FiniteWorld k, chainPMF p k u = 1
  | 0 => by rw [sum_finiteWorld_zero]; rfl
  | k + 1 => by
      rw [sum_finiteWorld_succ]
      simp only [chainPMF_marginal]
      exact chainPMF_sum_one p k

/-- Non-negativity under `InUnit`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainPMF_nonneg {p : CondRule} (hp : p.InUnit) : ∀ k (u : FiniteWorld k), 0 ≤ chainPMF p k u
  | 0, _ => by simp [chainPMF]
  | k + 1, u => by
      simp only [chainPMF]
      apply mul_nonneg (chainPMF_nonneg hp k _)
      split_ifs
      · exact (hp k _).1
      · linarith [(hp k (Fin.init u)).2]

/-- Bounded by one under `InUnit`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainPMF_le_one {p : CondRule} (hp : p.InUnit) (k : ℕ) (u : FiniteWorld k) :
    chainPMF p k u ≤ 1 := by
  rw [← chainPMF_sum_one p k]
  exact Finset.single_le_sum (fun v _ => chainPMF_nonneg hp k v) (Finset.mem_univ u)

/-- **Zero mass is hereditary**: a null prefix has null extensions. The mechanism behind every
"`Ax`-inconsistent conjunctions stay null" claim.
Source: PDF 07 p. 2 ("only had non-zero probability in `Ax`-consistent sentences … immediate by
induction")
Kind: L
Fidelity: exact -/
lemma chainPMF_zero_of_init (p : CondRule) {k : ℕ} (u : FiniteWorld (k + 1))
    (h : chainPMF p k (Fin.init u) = 0) : chainPMF p (k + 1) u = 0 := by
  simp [chainPMF, h]

/-! ## Sentence values -/

/-- The value of `φ` summed at level `n`: the mass of the level-`n` worlds in which `φ` holds.
Source: PDF 06 p. 1 (`P(φ) := Σ_{C ⊨ φ} P(C)`)
Kind: D
Fidelity: exact -/
def chainValAt (e : ℕ ≃ ℕ) (p : CondRule) (n : ℕ) (φ : Sentence) : ℚ :=
  ∑ u : FiniteWorld n, if (enumWorld e u).toPCWorld.Holds φ then chainPMF p n u else 0

/-- **The chained valuation**: `chainValAt` at the sentence's own level.
Source: PDF 06 p. 1 (`P(φ) := Σ_{C ⊨ φ} P(C)`, over the conjunctions containing all of `φ`'s
primes); [[bli-soto-a-inventory]] 050
Kind: D
Fidelity: exact -/
def chainVal (e : ℕ ≃ ℕ) (p : CondRule) (φ : Sentence) : ℚ :=
  chainValAt e p (level e φ) φ

/-- Raising the summation level by one does not change the value (projectivity).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainValAt_succ (e : ℕ ≃ ℕ) (p : CondRule) {n : ℕ} {φ : Sentence} (h : level e φ ≤ n) :
    chainValAt e p (n + 1) φ = chainValAt e p n φ := by
  unfold chainValAt
  rw [sum_finiteWorld_succ]
  apply Finset.sum_congr rfl
  intro u _
  simp only [holds_enumWorld_snoc_iff e u _ h]
  split_ifs
  · exact chainPMF_marginal p u
  · simp

/-- **`chainVal_level_mono`**: summing at any level `≥ level e φ` gives `chainVal e p φ`.
Source: [[bli-soto-a-inventory]] 050 ("well defined (consistent marginals)")
Kind: P
Fidelity: exact -/
lemma chainValAt_eq_of_le (e : ℕ ≃ ℕ) (p : CondRule) {n : ℕ} {φ : Sentence}
    (h : level e φ ≤ n) : chainValAt e p n φ = chainVal e p φ := by
  unfold chainVal
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [← ih (Nat.le_add_right _ _), ← Nat.add_assoc, chainValAt_succ e p (Nat.le_add_right _ _)]

/-- Non-negativity of values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainValAt_nonneg (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) (n : ℕ) (φ : Sentence) :
    0 ≤ chainValAt e p n φ := by
  unfold chainValAt
  apply Finset.sum_nonneg
  intro u _
  split_ifs
  · exact chainPMF_nonneg hp n u
  · exact le_rfl

/-- Values are at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainValAt_le_one (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) (n : ℕ) (φ : Sentence) :
    chainValAt e p n φ ≤ 1 := by
  unfold chainValAt
  rw [← chainPMF_sum_one p n]
  apply Finset.sum_le_sum
  intro u _
  split_ifs
  · exact le_rfl
  · exact chainPMF_nonneg hp n u

/-- `chainVal_mem_Icc`: values lie in `[0,1]` (the `mem_Icc` clause).
Source: PDF 06 p. 1 ("if all `p ∈ [0,1]` then coherent")
Kind: P
Fidelity: exact -/
lemma chainVal_mem_Icc (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) (φ : Sentence) :
    0 ≤ chainVal e p φ ∧ chainVal e p φ ≤ 1 :=
  ⟨chainValAt_nonneg e hp _ φ, chainValAt_le_one e hp _ φ⟩

/-- `chainVal_top`: `⊤` has value one (the `top_eq_one` clause).
Source: PDF 06 p. 1
Kind: P
Fidelity: exact -/
lemma chainVal_top (e : ℕ ≃ ℕ) (p : CondRule) : chainVal e p (⊤ : Sentence) = 1 := by
  unfold chainVal chainValAt
  simp only [PCWorld.holds_top, if_true]
  exact chainPMF_sum_one p _

/-- `chainVal_congr`: worlds-equivalent sentences have equal values (the `congr` clause).
Source: PDF 06 p. 1
Kind: P
Fidelity: exact -/
lemma chainVal_congr (e : ℕ ≃ ℕ) (p : CondRule) {φ ψ : Sentence}
    (h : ∀ v : PCWorld, v.Holds φ ↔ v.Holds ψ) : chainVal e p φ = chainVal e p ψ := by
  rw [← chainValAt_eq_of_le e p (le_max_left (level e φ) (level e ψ)),
    ← chainValAt_eq_of_le e p (le_max_right (level e φ) (level e ψ))]
  unfold chainValAt
  apply Finset.sum_congr rfl
  intro u _
  simp only [h]

/-- `chainVal_disjoint_add`: exclusive sentences add (the `disjoint_add` clause).
Source: PDF 06 p. 1; [[bli-soto-a-inventory]] 050 ("propositionally coherent")
Kind: P
Fidelity: exact -/
lemma chainVal_disjoint_add (e : ℕ ≃ ℕ) (p : CondRule) {φ ψ : Sentence}
    (h : ∀ v : PCWorld, ¬(v.Holds φ ∧ v.Holds ψ)) :
    chainVal e p (φ ⋎ ψ) = chainVal e p φ + chainVal e p ψ := by
  have hφ : level e φ ≤ level e (φ ⋎ ψ) := by simp
  have hψ : level e ψ ≤ level e (φ ⋎ ψ) := by simp
  rw [← chainValAt_eq_of_le e p hφ, ← chainValAt_eq_of_le e p hψ]
  unfold chainVal chainValAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h1 : (enumWorld e u).toPCWorld.Holds φ <;>
    by_cases h2 : (enumWorld e u).toPCWorld.Holds ψ <;> simp [h1, h2, PCWorld.holds_or]
  exact absurd ⟨h1, h2⟩ (h _)

/-- Monotonicity of values along semantic implication.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_mono (e : ℕ ≃ ℕ) {p : CondRule} (hp : p.InUnit) {φ ψ : Sentence}
    (h : ∀ v : PCWorld, v.Holds φ → v.Holds ψ) : chainVal e p φ ≤ chainVal e p ψ := by
  rw [← chainValAt_eq_of_le e p (le_max_left (level e φ) (level e ψ)),
    ← chainValAt_eq_of_le e p (le_max_right (level e φ) (level e ψ))]
  unfold chainValAt
  apply Finset.sum_le_sum
  intro u _
  by_cases h1 : (enumWorld e u).toPCWorld.Holds φ
  · simp [h1, h _ h1]
  · simp only [h1, if_false]
    split_ifs
    · exact chainPMF_nonneg hp _ u
    · exact le_rfl

/-- **The cylinder value**: `conj e u` has value `chainPMF p k u`.
Source: PDF 06 p. 1 (the conjunctions "play the role of boolean worlds")
Kind: P
Fidelity: exact -/
lemma chainVal_conj (e : ℕ ≃ ℕ) (p : CondRule) {k : ℕ} (u : FiniteWorld k) :
    chainVal e p (conj e u) = chainPMF p k u := by
  rw [← chainValAt_eq_of_le e p (level_conj_le e u)]
  unfold chainValAt
  simp only [enumWorld_holds_conj_iff]
  rw [Finset.sum_ite_eq' Finset.univ u (fun w => chainPMF p k w)]
  simp

/-- A sentence whose worlds at some level `≥ level e φ` all carry zero mass has value zero.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_eq_zero_of_le (e : ℕ ≃ ℕ) (p : CondRule) {n : ℕ} {φ : Sentence}
    (hn : level e φ ≤ n)
    (h : ∀ u : FiniteWorld n, (enumWorld e u).toPCWorld.Holds φ → chainPMF p n u = 0) :
    chainVal e p φ = 0 := by
  rw [← chainValAt_eq_of_le e p hn]
  unfold chainValAt
  apply Finset.sum_eq_zero
  intro u _
  split_ifs with hu
  · exact h u hu
  · rfl

/-- Splitting a value along a sentence and its negation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chainVal_split (e : ℕ ≃ ℕ) (p : CondRule) (E φ : Sentence) :
    chainVal e p φ = chainVal e p (E ⋏ φ) + chainVal e p (∼E ⋏ φ) := by
  have h1 : level e φ ≤ max (level e E) (level e φ) := le_max_right _ _
  have h2 : level e (E ⋏ φ) ≤ max (level e E) (level e φ) := by simp
  have h3 : level e (∼E ⋏ φ) ≤ max (level e E) (level e φ) := by simp
  rw [← chainValAt_eq_of_le e p h1, ← chainValAt_eq_of_le e p h2, ← chainValAt_eq_of_le e p h3]
  unfold chainValAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hE : (enumWorld e u).toPCWorld.Holds E <;>
    simp [hE, PCWorld.holds_and, PCWorld.holds_neg]

/-- `enumWorld e (Fin.snoc u b)` holds `atom (e k)` iff `b = true`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_snoc_atom_iff (e : ℕ ≃ ℕ) {k : ℕ} (u : FiniteWorld k) (b : Bool) :
    (enumWorld e (Fin.snoc u b)).toPCWorld.Holds (Formula.atom (e k)) ↔ b = true := by
  rw [PCWorld.holds_atom]
  simp [BoolPCWorld.toPCWorld, enumWorld_snoc_last]

/-- **Conditioning is definitional** ([[bli-soto-a-2-inventory]] 005 (i)/(ii)): if the rule at
level `k` is `c` on every level-`k` world (of positive mass) satisfying an event `E` of level
`≤ k`, then `chainVal (E ⋏ atom (e k)) = c · chainVal E`. This is also the engine of the halving
argument (target 4b): at a level where the agnostic clause fires on every `¬U`-world, the mass of
`¬U ∧ (instances so far) ∧ (new instance)` is exactly half that of `¬U ∧ (instances so far)`.
Source: [[bli-soto-a-2-inventory]] 005; PDF 06 p. 1 (`P("P_{n+1}(φ) = q" ∧ φ) := q · P(…)`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
lemma chainVal_and_atom (e : ℕ ≃ ℕ) (p : CondRule) {E : Sentence} {k : ℕ} (hE : level e E ≤ k)
    (c : ℚ)
    (hc : ∀ u : FiniteWorld k, (enumWorld e u).toPCWorld.Holds E →
      chainPMF p k u = 0 ∨ p k u = c) :
    chainVal e p (E ⋏ Formula.atom (e k)) = c * chainVal e p E := by
  have hlev : level e (E ⋏ Formula.atom (e k)) ≤ k + 1 := by
    simp only [level_and, level_atom, Equiv.symm_apply_apply, max_le_iff]
    exact ⟨hE.trans (Nat.le_succ k), le_rfl⟩
  rw [← chainValAt_eq_of_le e p hlev, ← chainValAt_eq_of_le e p hE]
  unfold chainValAt
  rw [sum_finiteWorld_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.sum_bool]
  simp only [PCWorld.holds_and, holds_enumWorld_snoc_iff e u _ hE, holds_snoc_atom_iff,
    and_true, Bool.false_eq_true, and_false, if_false, add_zero, chainPMF_snoc, if_true]
  split_ifs with hu
  · rcases hc u hu with h | h
    · simp [h]
    · rw [h]; ring
  · simp

/-- The negative-literal companion of `chainVal_and_atom`: `chainVal (E ⋏ ∼atom (e k)) = (1 − c) · chainVal E`.
Source: [[bli-soto-a-2-inventory]] 005
Kind: P
Fidelity: exact -/
lemma chainVal_and_neg_atom (e : ℕ ≃ ℕ) (p : CondRule) {E : Sentence} {k : ℕ}
    (hE : level e E ≤ k) (c : ℚ)
    (hc : ∀ u : FiniteWorld k, (enumWorld e u).toPCWorld.Holds E →
      chainPMF p k u = 0 ∨ p k u = c) :
    chainVal e p (E ⋏ ∼Formula.atom (e k)) = (1 - c) * chainVal e p E := by
  have hlev : level e (E ⋏ ∼Formula.atom (e k)) ≤ k + 1 := by
    simp only [level_and, level_neg, level_atom, Equiv.symm_apply_apply, max_le_iff]
    exact ⟨hE.trans (Nat.le_succ k), le_rfl⟩
  rw [← chainValAt_eq_of_le e p hlev, ← chainValAt_eq_of_le e p hE]
  unfold chainValAt
  rw [sum_finiteWorld_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Fintype.sum_bool]
  simp only [PCWorld.holds_and, PCWorld.holds_neg, holds_enumWorld_snoc_iff e u _ hE,
    holds_snoc_atom_iff, not_true_eq_false, and_false, if_false, Bool.false_eq_true,
    not_false_eq_true, and_true, zero_add, chainPMF_snoc]
  split_ifs with hu
  · rcases hc u hu with h | h
    · simp [h]
    · rw [h]; ring
  · simp

end Cleanroom.Bli.BliExtrapolation
