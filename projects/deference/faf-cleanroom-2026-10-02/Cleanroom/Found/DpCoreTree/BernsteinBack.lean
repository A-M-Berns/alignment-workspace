import Cleanroom.Found.DpCoreTree.Bernstein
import Cleanroom.Found.DpCoreTree.Catalogue
import Cleanroom.Found.DpCoreTree.Tickle
import Cleanroom.Found.DpCoreTree.RootEvents
import Cleanroom.Found.DpCoreTree.SeedMax

/-!
# Proposition 4, backward: every `b ∈ [0,1]^{k+1}` is realised at `k`

The pattern-routing tree `bernTree b k j`: `k` nested `d`-nodes (acts `Bool`, `true` = `a`),
then a coin with weight `b (j + #a-draws)` on the `X`-leaf (`X = {true}`). It queries `d`
exactly `k` times on every path (`bernTree_queriesExactly`) and realises
`q ↦ ∑_{j ≤ k} b_j · B_{k,j}(q)` (`bernTree_nu`), by induction with Pascal's rule
(`bern_sum_succ`).

Under the shared seed (Definition 6′) the same tree realises exactly `(1 − q) b₀ + q b_k`
(`bernTree_nu'`, repair round 1): the `⊇` half of the affine collapse whose `⊆` half is
`nu'_twoPoint_affine`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset Polynomial Tree

/-- The pattern-routing tree with accumulator `j` (the number of `a`-draws so far).
Source: [[decision-problems-v2]] Proposition 4 proof ("Backward: the tree observes the pattern
and routes to a chance node realizing `b_{|S|}`")
Kind: D -/
def bernTree (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) : ℕ → ℕ → Tree Bool Unit (fun _ => Bool) ℚ
  | 0, j => .chance 2 (FinDistr.coin (b j) (hb j).1 (hb j).2) fun i => .leaf (decide (i = 0)) 0
  | n + 1, j => .decision () fun act => bernTree b hb n (if act then j + 1 else j)

/-- The one-point procedure `C(d)(a) = q` on `Bool`-acts.
Source: none: infrastructure
Kind: D -/
def procBool (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Proc Unit (fun _ => Bool) ℚ :=
  fun _ => FinDistr.bool q h0 h1

/-- A leaf tree has one leaf. Source: none: infrastructure. Kind: L -/
theorem card_leaves_leaf' (ω : Bool) (r : ℚ) :
    Fintype.card (Tree.leaf ω r : Tree Bool Unit (fun _ => Bool) ℚ).Leaves = 1 := rfl

/-- `ν` through a decision node.
Source: none: infrastructure
Kind: L -/
theorem nu_decision' {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq Ω] (C : Proc ι acts K) (d : ι)
    (child : acts d → Tree Ω ι acts K) (X : Finset Ω) :
    nu C (decision d child) X = ∑ a, (C d).w a * nu C (child a) X := by
  simp only [nu_eq_sum]
  rw [sum_leaves_decision]
  simp only [world_decision, leafLaw_decision, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ℓ _ => ?_
  split_ifs <;> simp

/-- The pattern-routing tree queries `d` exactly `n` times on every path.
Source: [[decision-problems-v2]] Proposition 4
Kind: L -/
theorem bernTree_queriesExactly (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    (n j : ℕ) → QueriesExactly (bernTree b hb n j) () n
  | 0, j => by
      intro ℓ
      rcases ℓ with ⟨i, _⟩
      rfl
  | n + 1, j => by
      intro ℓ
      rcases ℓ with ⟨act, ℓ⟩
      simp only [bernTree, count_decision, if_true]
      have := bernTree_queriesExactly b hb n (if act then j + 1 else j) ℓ
      omega

/-- The Bernstein sum with accumulator `j`: `∑_{i ≤ n} b(j+i) C(n,i) q^i (1−q)^{n−i}`.
Source: none: infrastructure
Kind: D -/
def bernSum (b : ℕ → ℚ) (n j : ℕ) (q : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), b (j + i) * (Nat.choose n i : ℚ) * q ^ i * (1 - q) ^ (n - i)

/-- **Pascal's rule for the Bernstein sum**: `S(n+1, j) = q · S(n, j+1) + (1−q) · S(n, j)`.
Source: none: infrastructure (Pascal's rule `C(n+1,i+1) = C(n,i) + C(n,i+1)`)
Kind: L -/
theorem bern_sum_succ (b : ℕ → ℚ) (n j : ℕ) (q : ℚ) :
    bernSum b (n + 1) j q = q * bernSum b n (j + 1) q + (1 - q) * bernSum b n j q := by
  unfold bernSum
  -- peel the `i = 0` term of the left side and re-index
  rw [Finset.sum_range_succ' (fun i => b (j + i) * (Nat.choose (n + 1) i : ℚ) * q ^ i *
    (1 - q) ^ (n + 1 - i))]
  -- the `(1 − q) S(n, j)` side: peel `i = 0`
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_range_succ' (fun i => (1 - q) * (b (j + i) * (Nat.choose n i : ℚ) * q ^ i *
    (1 - q) ^ (n - i)))]
  -- the `q S(n, j+1)` side over `range (n+1)`; the left first sum splits by Pascal
  have hsplit : ∀ i ∈ Finset.range (n + 1),
      b (j + (i + 1)) * (Nat.choose (n + 1) (i + 1) : ℚ) * q ^ (i + 1) * (1 - q) ^ (n + 1 - (i + 1)) =
        q * (b (j + 1 + i) * (Nat.choose n i : ℚ) * q ^ i * (1 - q) ^ (n - i)) +
        b (j + (i + 1)) * (Nat.choose n (i + 1) : ℚ) * q ^ (i + 1) * (1 - q) ^ (n - (i + 1)) *
          (if i + 1 ≤ n then (1 - q) else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.choose_succ_succ, Nat.add_sub_add_right]
    have e1 : j + (i + 1) = j + 1 + i := by omega
    rw [e1]
    by_cases hin : i + 1 ≤ n
    · rw [if_pos hin]
      have e2 : n - i = (n - (i + 1)) + 1 := by omega
      rw [e2, pow_succ, pow_succ]
      push_cast
      ring
    · rw [if_neg hin]
      have hi' : i = n := by omega
      subst hi'
      simp [Nat.choose_succ_self]
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- now match the pieces
  have hA : ∑ i ∈ Finset.range (n + 1), q * (b (j + 1 + i) * (Nat.choose n i : ℚ) * q ^ i *
      (1 - q) ^ (n - i)) = q * ∑ i ∈ Finset.range (n + 1), b (j + 1 + i) * (Nat.choose n i : ℚ) *
      q ^ i * (1 - q) ^ (n - i) := by rw [Finset.mul_sum]
  have hB : ∑ i ∈ Finset.range (n + 1), b (j + (i + 1)) * (Nat.choose n (i + 1) : ℚ) * q ^ (i + 1) *
      (1 - q) ^ (n - (i + 1)) * (if i + 1 ≤ n then (1 - q) else 0) =
      ∑ i ∈ Finset.range n, (1 - q) * (b (j + (i + 1)) * (Nat.choose n (i + 1) : ℚ) * q ^ (i + 1) *
        (1 - q) ^ (n - (i + 1))) := by
    rw [Finset.sum_range_succ, if_neg (by omega), mul_zero, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega)]; ring
  rw [hA, hB]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, add_zero, Nat.sub_zero]
  ring

/-- **Proposition 4, backward**: the pattern-routing tree realises the Bernstein sum with the
prescribed coefficients.
Source: [[decision-problems-v2]] Proposition 4 proof ("Backward")
Kind: P -/
theorem bernTree_nu (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (n j : ℕ) → nu (procBool q h0 h1) (bernTree b hb n j) {true} = bernSum b n j q
  | 0, j => by
      simp only [bernTree, bernSum]
      rw [nu_chance]
      simp only [Fin.sum_univ_two]
      simp [nu_eq_sum, FinDistr.coin, card_leaves_leaf']
  | n + 1, j => by
      simp only [bernTree]
      rw [nu_decision', Fintype.sum_bool]
      simp only [procBool, FinDistr.bool_true, FinDistr.bool_false, if_true, if_false,
        Bool.false_eq_true]
      rw [bernTree_nu b hb q h0 h1 n (j + 1), bernTree_nu b hb q h0 h1 n j, bern_sum_succ]

/-- **Proposition 4, backward, Bernstein form**: for every `b ∈ [0,1]^{k+1}` there is a tree
querying `d` exactly `k` times on every path with `ν_{C_q}(X) = ∑_{j ≤ k} b_j · B_{k,j}(q)`.
Source: [[decision-problems-v2]] Proposition 4 (the ⊇ inclusion)
Kind: P
Fidelity: exact (over `ℚ`, acts `Bool`, `X = {true}`)
Hyps: none -/
theorem exists_tree_realising_bernstein (k : ℕ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    ∃ B : Tree Bool Unit (fun _ => Bool) ℚ, QueriesExactly B () k ∧
      ∀ q (h0 : 0 ≤ q) (h1 : q ≤ 1), nu (procBool q h0 h1) B {true} =
        ∑ j ∈ Finset.range (k + 1), b j * (bernsteinPolynomial ℚ k j).eval q := by
  refine ⟨bernTree b hb k 0, bernTree_queriesExactly b hb k 0, fun q h0 h1 => ?_⟩
  rw [bernTree_nu, bernSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bernstein_eval, zero_add]
  ring

/-! ### The `⊇` half of the affine collapse under Definition 6′ -/

/-- On a `Unit`-point tree, `C[d↦a]` is the deterministic procedure playing `a`.
Source: none: infrastructure
Kind: L -/
theorem deviatePure_unit_eq_ofFun (C : Proc Unit (fun _ => Bool) ℚ) (a : Bool) :
    C.deviatePure () a = Proc.ofFun (fun _ => a) := by
  funext d; cases d; simp [Proc.deviatePure, Proc.deviate, Proc.ofFun]

/-- Under the deterministic procedure playing `true`, the pattern-routing tree with accumulator
`j` lands on the coin `b (j + n)`.
Source: [[decision-problems-v2]] Proposition 4 proof (the routing on the pattern)
Kind: L -/
theorem bernTree_nu_ofFun_true (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    (n j : ℕ) → nu (Proc.ofFun fun _ => true) (bernTree b hb n j) {true} = b (j + n)
  | 0, j => by
      simp only [bernTree]
      rw [nu_chance]
      simp only [Fin.sum_univ_two]
      simp [nu_eq_sum, FinDistr.coin, card_leaves_leaf']
  | n + 1, j => by
      simp only [bernTree]
      rw [nu_decision', Fintype.sum_bool]
      simp only [Proc.ofFun, FinDistr.pure_w, if_true, if_false, Bool.false_eq_true, one_mul,
        zero_mul, add_zero]
      rw [bernTree_nu_ofFun_true b hb n (j + 1)]
      congr 1; omega

/-- Under the deterministic procedure playing `false`, the pattern-routing tree with accumulator
`j` lands on the coin `b j`.
Source: [[decision-problems-v2]] Proposition 4 proof (the routing on the pattern)
Kind: L -/
theorem bernTree_nu_ofFun_false (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    (n j : ℕ) → nu (Proc.ofFun fun _ => false) (bernTree b hb n j) {true} = b j
  | 0, j => by
      simp only [bernTree]
      rw [nu_chance]
      simp only [Fin.sum_univ_two]
      simp [nu_eq_sum, FinDistr.coin, card_leaves_leaf']
  | n + 1, j => by
      simp only [bernTree]
      rw [nu_decision', Fintype.sum_bool]
      simp only [Proc.ofFun, FinDistr.pure_w, if_true, if_false, Bool.false_eq_true,
        Bool.true_eq_false, one_mul, zero_mul, zero_add]
      exact bernTree_nu_ofFun_false b hb n j

/-- **The `⊇` half of the affine collapse under 6′**: under the shared seed the pattern-routing
tree realises exactly `(1 − q) b₀ + q b_k` at every `k`, so every affine function with
coefficients in `[0,1]` is realised at every `k ≥ 1` (choose `b₀`, `b_k`; at `k = 0` the two
coefficients coincide and only constants are realised, as under Definition 6), and nothing
else is (`nu'_twoPoint_affine`): `k` queries of `d` on one path return one bit.
Source: `fable-slop-notes.md` line 86 ("The price"); mandate T8; fidelity audit r1 §3.9
Kind: P
Fidelity: exact (over `ℚ`, acts `Bool`, `X = {true}`)
Hyps: none -/
theorem bernTree_nu' (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (k : ℕ) :
    nu' (procBool q h0 h1) (bernTree b hb k 0) {true} = (1 - q) * b 0 + q * b k := by
  rw [nu'_deviate_sum (procBool q h0 h1) (bernTree b hb k 0) () {true}, Fintype.sum_bool,
    deviatePure_unit_eq_ofFun, deviatePure_unit_eq_ofFun, nu'_ofFun, nu'_ofFun,
    bernTree_nu_ofFun_true, bernTree_nu_ofFun_false]
  simp only [procBool, FinDistr.bool_true, FinDistr.bool_false, zero_add]
  ring

end Cleanroom.Found.DpCoreTree
