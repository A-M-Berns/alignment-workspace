import Cleanroom.Found.DpCoreTree.Seed
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Roots

/-!
# Proposition 4 in Bernstein form; the affine collapse under 6′

T8 of [[dp-core-tree-mandate]] (dp-core-027, dp-core-067, dp-cf-056).

Shape: `QueriesExactly B d k` (every path meets `d` exactly `k` times) with `|A_d| = 2` and a
designated action `a`. The family `C_q := C[d ↦ (q, 1−q)]` (other points fixed).

* **Forward** (`nu_twoPoint_eq_bernstein`): `ν_{B,C_q}(X) = ∑_{j ≤ k} b_j · B_{k,j}(q)` with
  `B_{k,j}` Mathlib's `bernsteinPolynomial K k j` and `b_j ∈ [0,1]`; `b_j` is the `X`-mass of the
  leaves with `j` draws of `a`, divided by `C(k,j)` — the pattern decomposition of the leaf law
  (`leafLaw_twoPoint`) grouped by `|S|`. That `b_j ≤ 1` uses `W_j(⊤) = C(k,j)`
  (`sum_offWeight_countDraw`), proved by structural recursion with Pascal's rule.
* **Corollary** (`no_threshold_of_bernstein`): no tree of this shape realises `[q > ½]` on
  `[0,1]`: a polynomial vanishing on `[0, ½]` is zero.
* **Under 6′** (`nu'_twoPoint_affine`): `ν'_{B,C_q}(X) = (1−q) ν'_{B,C[d↦ā]}(X) + q ν'_{B,C[d↦a]}(X)`
  — affine in `q` on every tree (SE-1(b) with two actions), so the realisable functions collapse
  to `{b₀(1−q) + b₁ q}`.

The backward direction (every `b ∈ [0,1]^{k+1}` is realised at `k`) is `bernTree` in
`BernsteinBack.lean`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset Polynomial

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι]
  [DecidableEq Ω]

/-! ### The two-point mixed action -/

/-- The mixed action `(q at a, 1−q at the other action)` on a two-element action type.
Source: [[decision-problems-v2]] Proposition 4 (`A_d = {a, ā}`, `q := C(d)(a)`)
Kind: D -/
def FinDistr.twoPoint {α : Type} [Fintype α] [DecidableEq α] (a : α) (hc : Fintype.card α = 2)
    (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinDistr K α where
  w b := if b = a then q else 1 - q
  nonneg b := by split_ifs <;> linarith
  sum_one := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
    simp only [if_true]
    rw [Finset.sum_congr rfl (fun b hb => if_neg (Finset.ne_of_mem_erase hb))]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hc]
    simp

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem FinDistr.twoPoint_w {α : Type} [Fintype α] [DecidableEq α] (a : α)
    (hc : Fintype.card α = 2) (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : α) :
    (FinDistr.twoPoint a hc q h0 h1).w b = if b = a then q else 1 - q := rfl

namespace Tree

/-- Every path meets `d` exactly `k` times.
Source: [[decision-problems-v2]] Proposition 4 ("query `d` exactly `k` times on every path")
Kind: D -/
def QueriesExactly (B : Tree Ω ι acts K) (d : ι) (k : ℕ) : Prop := ∀ ℓ, count d B ℓ = k

/-- The `C`-part weight of a leaf: its chance weight times the draw weights at points other
than `d`.
Source: [[decision-problems-v2]] Proposition 4 proof ("conditioning on the pattern `S`")
Kind: D -/
def offWeight (C : Proc ι acts K) (d : ι) (B : Tree Ω ι acts K) (ℓ : B.Leaves) : K :=
  chanceWeight B ℓ * (((draws B ℓ).filter fun x => x.1 ≠ d).map fun x => (C x.1).w x.2).prod

/-! ### The pattern decomposition of the leaf law -/

/-- Splitting a list product at the predicate `x.1 = d`.
Source: none: infrastructure
Kind: L -/
theorem prod_map_filter_split (d : ι) (f : (Σ d : ι, acts d) → K) :
    (L : List (Σ d : ι, acts d)) →
      (L.map f).prod = ((L.filter fun x => x.1 ≠ d).map f).prod *
        ((L.filter fun x => x.1 = d).map f).prod
  | [] => by simp
  | x :: L => by
      have ih := prod_map_filter_split d f L
      by_cases hx : x.1 = d
      · simp [List.filter_cons, hx, ih]; ring
      · simp [List.filter_cons, hx, ih]; ring

/-- The product of the two-point weights over the draws at `d`: `q^{#a} (1−q)^{#d − #a}`.
Source: [[decision-problems-v2]] Proposition 4 proof (`q^{|S|}(1−q)^{k−|S|}`)
Kind: L -/
theorem prod_twoPoint_draws (d : ι) (a : acts d) (q : K) :
    (L : List (Σ d : ι, acts d)) → (∀ x ∈ L, x.1 = d) →
      (L.map fun x => if x = ⟨d, a⟩ then q else 1 - q).prod =
        q ^ L.count ⟨d, a⟩ * (1 - q) ^ (L.length - L.count ⟨d, a⟩)
  | [], _ => by simp
  | x :: L, hL => by
      have hcount : L.count ⟨d, a⟩ ≤ L.length := List.count_le_length
      simp only [List.map_cons, List.prod_cons, List.count_cons, List.length_cons]
      rw [prod_twoPoint_draws d a q L fun y hy => hL y (List.mem_cons_of_mem _ hy)]
      by_cases hx : x = ⟨d, a⟩
      · simp only [hx, if_true, beq_self_eq_true]
        rw [pow_succ]
        have : L.length + 1 - (L.count ⟨d, a⟩ + 1) = L.length - L.count ⟨d, a⟩ := by omega
        rw [this]; ring
      · simp only [hx, if_false, beq_iff_eq, add_zero]
        have : L.length + 1 - L.count ⟨d, a⟩ = (L.length - L.count ⟨d, a⟩) + 1 := by omega
        rw [this, pow_succ]; ring

/-- The number of draws at `d` on a path is `#_d`, as a list length.
Source: none: infrastructure
Kind: L -/
theorem length_filter_draws (d : ι) (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    ((draws B ℓ).filter fun x => x.1 = d).length = count d B ℓ := by
  rw [count_eq_draws_count, List.count_eq_length_filter, List.filter_map, List.length_map]
  rfl

/-- **The pattern decomposition**: under `C_q = C[d ↦ (q, 1−q)]`,
`μ(ℓ) = offWeight(ℓ) · q^{j_ℓ} · (1−q)^{#_d(ℓ) − j_ℓ}` with `j_ℓ` the number of `a`-draws on the
path.
Source: [[decision-problems-v2]] Proposition 4 proof
Kind: P -/
theorem leafLaw_twoPoint (C : Proc ι acts K) (d : ι) (a : acts d) (hc : Fintype.card (acts d) = 2)
    (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    leafLaw (C.deviate d (FinDistr.twoPoint a hc q h0 h1)) B ℓ =
      offWeight C d B ℓ * (q ^ countDraw d a B ℓ *
        (1 - q) ^ (count d B ℓ - countDraw d a B ℓ)) := by
  rw [leafLaw_eq_chanceWeight_mul_drawsWeight]
  unfold drawsWeight offWeight countDraw
  rw [prod_map_filter_split d]
  have hall : ∀ x ∈ (draws B ℓ).filter (fun x => x.1 = d), x.1 = d :=
    fun x hx => by simpa using List.of_mem_filter hx
  have e1 : ((draws B ℓ).filter fun x => x.1 ≠ d).map
      (fun x => ((C.deviate d (FinDistr.twoPoint a hc q h0 h1)) x.1).w x.2) =
      ((draws B ℓ).filter fun x => x.1 ≠ d).map (fun x => (C x.1).w x.2) := by
    refine List.map_congr_left fun x hx => ?_
    have hxd : x.1 ≠ d := by simpa using List.of_mem_filter hx
    rw [Proc.deviate_ne _ _ hxd]
  have e2 : ((draws B ℓ).filter fun x => x.1 = d).map
      (fun x => ((C.deviate d (FinDistr.twoPoint a hc q h0 h1)) x.1).w x.2) =
      ((draws B ℓ).filter fun x => x.1 = d).map (fun x => if x = ⟨d, a⟩ then q else 1 - q) := by
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨d', b⟩ := x
    have hd' : d' = d := hall _ hx
    subst hd'
    simp only [Proc.deviate_same, FinDistr.twoPoint_w, Sigma.mk.injEq, heq_eq_eq, true_and]
  rw [e1, e2, prod_twoPoint_draws d a q _ hall, length_filter_draws,
    List.count_filter (by simp)]
  ring

/-- The number of `a`-draws is at most `#_d`.
Source: none: infrastructure
Kind: L -/
theorem countDraw_le_count (d : ι) (a : acts d) (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    countDraw d a B ℓ ≤ count d B ℓ := by
  unfold countDraw
  rw [count_eq_draws_count, List.count, List.count, List.countP_map]
  apply List.countP_mono_left
  intro x _ hx
  simp only [beq_iff_eq, Function.comp] at hx ⊢
  rw [hx]

/-- `offWeight ≥ 0`.
Source: none: infrastructure
Kind: L -/
theorem offWeight_nonneg (C : Proc ι acts K) (d : ι) (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    0 ≤ offWeight C d B ℓ := by
  unfold offWeight
  apply mul_nonneg (chanceWeight_nonneg B ℓ)
  apply List.prod_nonneg
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  exact (C y.1).nonneg y.2

/-! ### `W_j(⊤) = C(k, j)` -/

/-- The total `offWeight` of the leaves with `j` draws of `a`.
Source: [[decision-problems-v2]] Proposition 4 proof ("grouping by `|S|`")
Kind: D -/
def patternMass (C : Proc ι acts K) (d : ι) (a : acts d) (B : Tree Ω ι acts K) (X : Finset Ω)
    (j : ℕ) : K :=
  ∑ ℓ, if world B ℓ ∈ X ∧ countDraw d a B ℓ = j then offWeight C d B ℓ else 0

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem offWeight_leaf (C : Proc ι acts K) (d : ι) (ω : Ω) (r : K)
    (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) : offWeight C d (leaf ω r) ℓ = 1 := by
  simp [offWeight]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem offWeight_chance (C : Proc ι acts K) (d : ι) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) (ℓ : (child i).Leaves) :
    offWeight C d (chance n β child) ⟨i, ℓ⟩ = β.w i * offWeight C d (child i) ℓ := by
  simp [offWeight, mul_assoc]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem offWeight_decision_ne (C : Proc ι acts K) (d d' : ι) (hd : d' ≠ d)
    (child : acts d' → Tree Ω ι acts K) (b : acts d') (ℓ : (child b).Leaves) :
    offWeight C d (decision d' child) ⟨b, ℓ⟩ = (C d').w b * offWeight C d (child b) ℓ := by
  simp [offWeight, List.filter_cons, hd, mul_assoc, mul_left_comm]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem offWeight_decision_eq (C : Proc ι acts K) (d : ι)
    (child : acts d → Tree Ω ι acts K) (b : acts d) (ℓ : (child b).Leaves) :
    offWeight C d (decision d child) ⟨b, ℓ⟩ = offWeight C d (child b) ℓ := by
  simp [offWeight, List.filter_cons]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem countDraw_leaf (d : ι) (a : acts d) (ω : Ω) (r : K)
    (ℓ : (leaf ω r : Tree Ω ι acts K).Leaves) : countDraw d a (leaf ω r) ℓ = 0 := by
  simp [countDraw]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem countDraw_chance (d : ι) (a : acts d) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (i : Fin n) (ℓ : (child i).Leaves) :
    countDraw d a (chance n β child) ⟨i, ℓ⟩ = countDraw d a (child i) ℓ := by
  simp [countDraw]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem countDraw_decision_ne (d d' : ι) (hd : d' ≠ d) (a : acts d)
    (child : acts d' → Tree Ω ι acts K) (b : acts d') (ℓ : (child b).Leaves) :
    countDraw d a (decision d' child) ⟨b, ℓ⟩ = countDraw d a (child b) ℓ := by
  unfold countDraw
  rw [draws_decision, List.count_cons]
  simp [hd]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem countDraw_decision_eq (d : ι) (a : acts d) (child : acts d → Tree Ω ι acts K)
    (b : acts d) (ℓ : (child b).Leaves) :
    countDraw d a (decision d child) ⟨b, ℓ⟩ =
      (if b = a then 1 else 0) + countDraw d a (child b) ℓ := by
  simp only [countDraw, draws_decision, List.count_cons, beq_iff_eq, Sigma.mk.injEq,
    heq_eq_eq, true_and]
  omega

/-- The other action of a two-element action type.
Source: none: infrastructure
Kind: L -/
theorem exists_other {α : Type} [Fintype α] [DecidableEq α] (a : α) (hc : Fintype.card α = 2) :
    ∃ b, b ≠ a ∧ ∀ c, c = a ∨ c = b := by
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a
  refine ⟨b, hb, fun c => ?_⟩
  by_contra hne
  rw [not_or] at hne
  have : 3 ≤ Fintype.card α := by
    have hsub : ({a, b, c} : Finset α) ⊆ Finset.univ := Finset.subset_univ _
    have hcard : ({a, b, c} : Finset α).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hne.2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hb, Ne.symm hne.1⟩
    rw [← hcard, ← Finset.card_univ]
    exact Finset.card_le_card hsub
  omega

/-- The choose function evaluated at `0`: `C(0, j) = [j = 0]`.
Source: none: infrastructure
Kind: L -/
theorem choose_zero_eq (j : ℕ) : (Nat.choose 0 j : K) = if 0 = j then 1 else 0 := by
  cases j <;> simp

/-- **`W_j(⊤) = C(k, j)`**: on a tree querying `d` exactly `k` times on every path, the total
`offWeight` of the leaves with `j` draws of `a` is `C(k, j)`.
Source: [[decision-problems-v2]] Proposition 4 proof ("grouping by `|S|` averages the `c_S`
into `b_j ∈ [0,1]`" — the normaliser)
Kind: P -/
theorem sum_offWeight_countDraw (C : Proc ι acts K) (d : ι) (a : acts d)
    (hc : Fintype.card (acts d) = 2) [∀ d, Nonempty (acts d)] :
    (B : Tree Ω ι acts K) → ∀ k, QueriesExactly B d k → ∀ j,
      (∑ ℓ, if countDraw d a B ℓ = j then offWeight C d B ℓ else 0) = (Nat.choose k j : K)
  | leaf ω r, k, hk, j => by
      have h0 : k = 0 := (hk ()).symm
      subst h0
      simp only [countDraw_leaf, offWeight_leaf]
      show (∑ _ℓ : Unit, if (0 : ℕ) = j then (1 : K) else 0) = _
      rw [choose_zero_eq]; simp
  | chance _ β child, k, hk, j => by
      have ih : ∀ i, (∑ ℓ, if countDraw d a (child i) ℓ = j then offWeight C d (child i) ℓ else 0)
          = (Nat.choose k j : K) :=
        fun i => sum_offWeight_countDraw C d a hc (child i) k (fun ℓ => by simpa using hk ⟨i, ℓ⟩) j
      rw [sum_leaves_chance]
      simp only [countDraw_chance, offWeight_chance, ite_mul_zero_eq, ← Finset.mul_sum, ih,
        ← Finset.sum_mul, β.sum_one, one_mul]
  | decision d' child, k, hk, j => by
      by_cases hd : d' = d
      · subst hd
        -- `k = k' + 1` and every child queries exactly `k'` times
        obtain ⟨ℓ₀⟩ := leaves_nonempty (child (Classical.arbitrary _))
        have hk1 : 1 ≤ k := by
          have := hk ⟨Classical.arbitrary _, ℓ₀⟩
          simp only [count_decision, if_true] at this
          omega
        have hchild : ∀ b, QueriesExactly (child b) d' (k - 1) := by
          intro b ℓ
          have := hk ⟨b, ℓ⟩
          simp only [count_decision, if_true] at this
          omega
        have ih : ∀ b j', (∑ ℓ, if countDraw d' a (child b) ℓ = j' then offWeight C d' (child b) ℓ
            else 0) = (Nat.choose (k - 1) j' : K) :=
          fun b j' => sum_offWeight_countDraw C d' a hc (child b) (k - 1) (hchild b) j'
        obtain ⟨b₀, hb₀, hall⟩ := exists_other a hc
        have huniv : (Finset.univ : Finset (acts d')) = {a, b₀} := by
          ext c; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
          exact hall c
        rw [sum_leaves_decision, huniv, Finset.sum_pair (Ne.symm hb₀)]
        simp only [countDraw_decision_eq, offWeight_decision_eq, eq_self_iff_true, if_true,
          hb₀, if_false, zero_add]
        rw [ih b₀ j]
        cases j with
        | zero =>
          rw [Finset.sum_eq_zero (fun ℓ _ => by rw [if_neg]; omega)]
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          simp
        | succ j' =>
          have e : (∑ ℓ, if 1 + countDraw d' a (child a) ℓ = j' + 1 then offWeight C d' (child a) ℓ
              else 0) = ∑ ℓ, if countDraw d' a (child a) ℓ = j' then offWeight C d' (child a) ℓ
              else 0 := by
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            congr 1
            apply propext
            omega
          rw [e, ih a j']
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_one_sub_one]
          rw [Nat.choose_succ_succ]
          push_cast
          ring
      · have ih : ∀ b, (∑ ℓ, if countDraw d a (child b) ℓ = j then offWeight C d (child b) ℓ else 0)
            = (Nat.choose k j : K) :=
          fun b => sum_offWeight_countDraw C d a hc (child b) k (fun ℓ => by
            have := hk ⟨b, ℓ⟩
            simp only [count_decision, hd, if_false, zero_add] at this
            exact this) j
        rw [sum_leaves_decision]
        simp only [countDraw_decision_ne d d' hd, offWeight_decision_ne C d d' hd, ite_mul_zero_eq,
          ← Finset.mul_sum, ih, ← Finset.sum_mul, (C d').sum_one, one_mul]

/-! ### The Bernstein form -/

/-- The Bernstein coefficient `b_j := W_j(X) / C(k, j)`.
Source: [[decision-problems-v2]] Proposition 4
Kind: D -/
def bernCoeff (C : Proc ι acts K) (d : ι) (a : acts d) (B : Tree Ω ι acts K) (X : Finset Ω)
    (k j : ℕ) : K :=
  patternMass C d a B X j / (Nat.choose k j : K)

/-- Evaluation of Mathlib's Bernstein polynomial.
Source: none: infrastructure (`bernsteinPolynomial R n ν = C (n.choose ν) * X^ν * (1 - X)^(n-ν)`)
Kind: L -/
theorem bernstein_eval (k j : ℕ) (q : K) :
    (bernsteinPolynomial K k j).eval q = (Nat.choose k j : K) * q ^ j * (1 - q) ^ (k - j) := by
  simp [bernsteinPolynomial]

/-- **Proposition 4, forward, Bernstein form**: on a tree querying `d` exactly `k` times on
every path, `ν_{B,C_q}(X) = ∑_{j ≤ k} b_j · B_{k,j}(q)` with `b_j = bernCoeff … k j ∈ [0, 1]`.
Source: [[decision-problems-v2]] Proposition 4 (line 184): "the functions `q ↦ Pr(X)` realizable
… are exactly `{q ↦ ∑_{j=0}^k b_j C(k,j) q^j (1−q)^{k−j} : b_0, …, b_k ∈ [0,1]}`" (⊆ half)
Kind: P
Fidelity: exact (the ⊆ inclusion; `⊇` is `BernsteinBack.lean`)
Hyps: none -/
theorem nu_twoPoint_eq_bernstein (C : Proc ι acts K) (d : ι) (a : acts d)
    (hc : Fintype.card (acts d) = 2) [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) (k : ℕ)
    (hk : QueriesExactly B d k) (X : Finset Ω) (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nu (C.deviate d (FinDistr.twoPoint a hc q h0 h1)) B X =
      ∑ j ∈ Finset.range (k + 1), bernCoeff C d a B X k j * (bernsteinPolynomial K k j).eval q := by
  rw [nu_eq_sum]
  simp only [leafLaw_twoPoint C d a hc q h0 h1 B]
  -- group the leaves by their number of `a`-draws
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (k + 1))
    (g := fun ℓ => countDraw d a B ℓ) (fun ℓ _ => by
      rw [Finset.mem_range]; have := countDraw_le_count d a B ℓ; rw [hk ℓ] at this; omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [bernstein_eval]
  unfold bernCoeff patternMass
  have hchoose : (Nat.choose k j : K) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [show (∑ ℓ, if world B ℓ ∈ X ∧ countDraw d a B ℓ = j then offWeight C d B ℓ else 0) /
      (Nat.choose k j : K) * ((Nat.choose k j : K) * q ^ j * (1 - q) ^ (k - j)) =
      (∑ ℓ, if world B ℓ ∈ X ∧ countDraw d a B ℓ = j then offWeight C d B ℓ else 0) *
        (q ^ j * (1 - q) ^ (k - j)) by field_simp]
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hj' : countDraw d a B ℓ = j
  · rw [if_pos hj']
    by_cases hx : world B ℓ ∈ X
    · rw [if_pos hx, if_pos ⟨hx, hj'⟩, hk ℓ, hj'] <;> ring
    · rw [if_neg hx, if_neg (fun h => hx h.1)] <;> ring
  · rw [if_neg hj', if_neg (fun h => hj' h.2)] <;> ring

/-- `0 ≤ b_j`.
Source: [[decision-problems-v2]] Proposition 4 (`b_j ∈ [0,1]`)
Kind: L -/
theorem bernCoeff_nonneg (C : Proc ι acts K) (d : ι) (a : acts d) (B : Tree Ω ι acts K)
    (X : Finset Ω) (k j : ℕ) : 0 ≤ bernCoeff C d a B X k j := by
  unfold bernCoeff patternMass
  apply div_nonneg
  · exact Finset.sum_nonneg fun ℓ _ => by split_ifs <;> simp [offWeight_nonneg]
  · exact Nat.cast_nonneg _

/-- `b_j ≤ 1`, from `W_j(X) ≤ W_j(⊤) = C(k, j)`.
Source: [[decision-problems-v2]] Proposition 4 (`b_j ∈ [0,1]`)
Kind: P -/
theorem bernCoeff_le_one (C : Proc ι acts K) (d : ι) (a : acts d)
    (hc : Fintype.card (acts d) = 2) [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) (k : ℕ)
    (hk : QueriesExactly B d k) (X : Finset Ω) (j : ℕ) (hj : j ≤ k) :
    bernCoeff C d a B X k j ≤ 1 := by
  unfold bernCoeff patternMass
  have hchoose : (0 : K) < Nat.choose k j := by exact_mod_cast Nat.choose_pos hj
  rw [div_le_one hchoose, ← sum_offWeight_countDraw C d a hc B k hk j]
  apply Finset.sum_le_sum
  intro ℓ _
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd h1.2 h2
  · exact offWeight_nonneg C d B ℓ
  · exact le_rfl

/-- **The forward direction as a polynomial**: `q ↦ ν_{B,C_q}(X)` is the evaluation of the
polynomial `∑_j C(b_j) · B_{k,j}`.
Source: [[decision-problems-v2]] Proposition 4 (line 188: "no exact threshold such as `[q > ½]`
is realizable at any finite `k`")
Kind: C -/
theorem exists_polynomial_nu_twoPoint (C : Proc ι acts K) (d : ι) (a : acts d)
    (hc : Fintype.card (acts d) = 2) [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) (k : ℕ)
    (hk : QueriesExactly B d k) (X : Finset Ω) :
    ∃ P : Polynomial K, ∀ q (h0 : 0 ≤ q) (h1 : q ≤ 1),
      nu (C.deviate d (FinDistr.twoPoint a hc q h0 h1)) B X = P.eval q := by
  refine ⟨∑ j ∈ Finset.range (k + 1), Polynomial.C (bernCoeff C d a B X k j) *
    bernsteinPolynomial K k j, fun q h0 h1 => ?_⟩
  rw [nu_twoPoint_eq_bernstein C d a hc B k hk X q h0 h1, Polynomial.eval_finsetSum]
  simp [Polynomial.eval_mul, Polynomial.eval_C]

/-- **No finite `k` realises a threshold**: no polynomial (hence no tree of the shape) has
`P.eval q = [q > ½]` on `[0, 1]`.
Source: [[decision-problems-v2]] Proposition 4 consequences ("no exact threshold such as
`[q > ½]` is realizable at any finite `k`"); mandate T8 corollary
Kind: P
Fidelity: exact -/
theorem no_threshold_polynomial (P : Polynomial K) :
    ¬ ∀ q : K, 0 ≤ q → q ≤ 1 → P.eval q = (if 1/2 < q then 1 else 0) := by
  intro h
  -- `P` vanishes on `[0, ½]`, an infinite set, so `P = 0`; but `P.eval 1 = 1`.
  have hzero : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.Icc (0 : K) (1/2))
    · intro q hq
      rw [Set.mem_setOf_eq, Polynomial.IsRoot.def, h q hq.1 (by linarith [hq.2]),
        if_neg (not_lt.mpr hq.2)]
    · exact Set.Icc_infinite (by norm_num)
  have := h 1 zero_le_one le_rfl
  rw [hzero, Polynomial.eval_zero, if_pos (by norm_num)] at this
  exact zero_ne_one this

/-- **No tree querying `d` `k` times realises `[q > ½]`**, for any `k`.
Source: [[decision-problems-v2]] Proposition 4 consequences
Kind: C
Hyps: none -/
theorem no_threshold_of_bernstein (C : Proc ι acts K) (d : ι) (a : acts d)
    (hc : Fintype.card (acts d) = 2) [∀ d, Nonempty (acts d)] (B : Tree Ω ι acts K) (k : ℕ)
    (hk : QueriesExactly B d k) (X : Finset Ω) :
    ¬ ∀ q (h0 : 0 ≤ q) (h1 : q ≤ 1),
      nu (C.deviate d (FinDistr.twoPoint a hc q h0 h1)) B X = (if 1/2 < q then 1 else 0) := by
  intro h
  obtain ⟨P, hP⟩ := exists_polynomial_nu_twoPoint C d a hc B k hk X
  apply no_threshold_polynomial P
  intro q h0 h1
  rw [← hP q h0 h1, h q h0 h1]

/-! ### The affine collapse under Definition 6′ -/

/-- **The affine collapse under 6′**: on every tree,
`ν'_{B,C_q}(X) = (1 − q) · ν'_{B,C[d↦ā]}(X) + q · ν'_{B,C[d↦a]}(X)`, so under the shared seed the
functions of `q` realised by a two-action point are affine, `b₀(1−q) + b₁ q` with
`b_i ∈ [0,1]` (`nu'_nonneg`, `nu'_le_one`), whatever `k`: `k` queries of `d` on one path return
one bit. A corollary of `nu'_deviate_sum` on a two-element action type (`exists_other`).
Source: `fable-slop-notes.md` line 86 ("The price"): "Under shared seed, `k` queries of `d` on
one path return one bit, so Proposition 4's realizable functions collapse from degree-`k`
Bernstein polynomials to affine `b₀(1−q) + b₁ q`"; mandate T8
Kind: C
Fidelity: exact (the `⊆` half; the `⊇` half — every `b₀(1−q) + b₁ q` with `b_i ∈ [0,1]`
realised at every `k` — is `bernTree_nu'` in `BernsteinBack.lean`)
Hyps: none -/
theorem nu'_twoPoint_affine (C : Proc ι acts K) (d : ι) (a : acts d)
    (hc : Fintype.card (acts d) = 2) (B : Tree Ω ι acts K) (X : Finset Ω) (q : K) (h0 : 0 ≤ q)
    (h1 : q ≤ 1) :
    ∃ b, b ≠ a ∧
      nu' (C.deviate d (FinDistr.twoPoint a hc q h0 h1)) B X =
        (1 - q) * nu' (C.deviatePure d b) B X + q * nu' (C.deviatePure d a) B X := by
  obtain ⟨b, hb, hall⟩ := exists_other a hc
  refine ⟨b, hb, ?_⟩
  set Cq := C.deviate d (FinDistr.twoPoint a hc q h0 h1) with hCq
  rw [nu'_deviate_sum Cq B d X]
  -- the sum over the two actions
  have huniv : (Finset.univ : Finset (acts d)) = {a, b} := by
    ext c; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hall c
  rw [huniv, Finset.sum_pair (Ne.symm hb)]
  have hCqa : (Cq d).w a = q := by simp [hCq]
  have hCqb : (Cq d).w b = 1 - q := by simp [hCq, hb]
  have hda : Cq.deviatePure d a = C.deviatePure d a := by
    funext d'; by_cases h : d' = d
    · subst h; simp [Proc.deviatePure]
    · simp [Proc.deviatePure, Proc.deviate_ne _ _ h, hCq]
  have hdb : Cq.deviatePure d b = C.deviatePure d b := by
    funext d'; by_cases h : d' = d
    · subst h; simp [Proc.deviatePure]
    · simp [Proc.deviatePure, Proc.deviate_ne _ _ h, hCq]
  rw [hCqa, hCqb, hda, hdb]
  ring

end Tree

end Cleanroom.Found.DpCoreTree
