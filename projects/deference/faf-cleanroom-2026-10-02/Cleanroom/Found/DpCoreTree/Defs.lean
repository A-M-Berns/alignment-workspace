import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Concrete decision problems: the tree type and run semantics (definitions of record)

Package `dp-core-tree` (area `found`), the decision area's root. This file holds the
definitions of record for [[decision-problems-v2]] §3.1 Definitions 5–6 (the finite tree, the
run law `μ_{B,C}`, the objective statistics `ν_{B,C}`, the value `V_B(C)`, `occ(d)`, `#_d`,
point-deviation `C[d ↦ m]`), the shared-seed semantics of Definition 6′ (`cf-workflow/…/seeds.md`
"Definitions carried"), and the path-product spine (`chanceWeight`, `draws`) that every theorem
of the package is proved from. Node addresses live in `Nodes.lean`; Definition 7 (veridicality,
coverage, recording) in `Recording.lean`.

## Modelling choices, disclosed once here

* **Worlds** are a finite type `Ω`; **events** are `Finset Ω`. v2 §0 says nothing turns on the
  pointless regime and every worked example is a finite atomic algebra (worlds = atoms), so
  `Finset Ω` is the algebra of events and `ω ⊨ X` is `ω ∈ X`.
* **Decision points** are a type `ι` with `DecidableEq`; the actions of `d` are a finite
  nonempty type `acts d`. A point's action *events* (`actEv : (d : ι) → acts d → Finset Ω`) and
  observation (`obs : ι → Finset Ω`) are supplied to the theorems that read them (Definition 7)
  as functions on `ι`, with disjointness / non-emptiness as `Prop` hypotheses where a theorem
  needs them. The subjective state `s_d` of Definition 3 is **not** part of this package's point
  data: no theorem here reads it; `dp-calibration` attaches states as a function on `ι`.
  Individuation of points (v2 Remark 2.2 — one triple, one mixed action at every occurrence)
  is carried by `DecidableEq ι`: two nodes carry the same point iff their labels are equal.
* **Scalars** are a linearly ordered field `K` (v2 says `ℝ`; `ℚ` suffices for every source
  number). Payoffs are in `K`. Fidelity: `variant: payoffs in a linearly ordered field`.
* **Distributions** are `FinDistr K α`: a weight function with non-negativity and total mass
  one. A chance node has `n ≥ 1` children by type (`FinDistr K (Fin 0)` is uninhabited); there
  is no junk default.
* **Definition 6′** is rendered *operationally* (route (a) of the mandate): a memoised walk
  carrying the seeds drawn so far (`leafLawSeed`); the product-mixture form (SE-1(a)) is a
  theorem in `Seed.lean`, not the definition. Definitions 6 and 6′ are separate
  definitions; there is no semantics flag inside `leafLaw`.
* `occ d` is an event of the run space `B.Leaves`, not of `Ω` (v2's Proposition 2 lifts it
  into the algebra precisely because it is not there already).
-/

namespace Cleanroom.Found.DpCoreTree

open Finset

universe u

/-- A probability distribution on a finite type, as a weight function with `0 ≤ w a` and
`∑ a, w a = 1`, over a linearly ordered field `K`.
Source: [[decision-problems-v2]] §2 (`Δ(A_d)`), §3.1 Definition 5 (`β_n ∈ Δ(children(n))`)
Kind: D
Fidelity: variant: weights in a linearly ordered field `K` rather than `ℝ` -/
structure FinDistr (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (α : Type) [Fintype α] where
  /-- The weight of each element. -/
  w : α → K
  /-- Weights are non-negative. -/
  nonneg : ∀ a, 0 ≤ w a
  /-- Weights sum to one. -/
  sum_one : ∑ a, w a = 1

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace FinDistr

variable {α : Type} [Fintype α]

/-- Two distributions with the same weights are equal.
Source: none: infrastructure
Kind: L -/
@[ext] theorem ext' {p q : FinDistr K α} (h : ∀ a, p.w a = q.w a) : p = q := by
  cases p; cases q; simp only [mk.injEq]; funext a; exact h a

/-- Every weight is at most one.
Source: none: infrastructure
Kind: L -/
theorem w_le_one (p : FinDistr K α) (a : α) : p.w a ≤ 1 := by
  have := p.sum_one
  calc p.w a ≤ ∑ b, p.w b := Finset.single_le_sum (fun b _ => p.nonneg b) (Finset.mem_univ a)
    _ = 1 := this

/-- The point mass `δ_a`.
Source: [[decision-problems-v2]] §2 Definition 4 ("deterministic if every `C(d)` is a point
mass"), §3.1 Definition 6 (`C[d ↦ a] := C[d ↦ δ_a]`)
Kind: D -/
def pure [DecidableEq α] (a : α) : FinDistr K α where
  w b := if b = a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  sum_one := by simp

/-- Weight of the point mass.
Source: none: infrastructure
Kind: L -/
@[simp] theorem pure_w [DecidableEq α] (a b : α) :
    (pure (K := K) a).w b = if b = a then 1 else 0 := rfl

/-- The uniform distribution on a nonempty finite type.
Source: `seeds.md` SE-2 proof ("with `C` uniform")
Kind: D -/
def uniform [Nonempty α] : FinDistr K α where
  w _ := (Fintype.card α : K)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (Fintype.card α : K) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact mul_inv_cancel₀ this

/-- Weight of the uniform distribution.
Source: none: infrastructure
Kind: L -/
@[simp] theorem uniform_w [Nonempty α] (a : α) :
    (uniform (K := K) (α := α)).w a = (Fintype.card α : K)⁻¹ := rfl

/-- The uniform weight is positive.
Source: none: infrastructure
Kind: L -/
theorem uniform_w_pos [Nonempty α] (a : α) : 0 < (uniform (K := K) (α := α)).w a := by
  simp only [uniform_w]
  have : (0 : K) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  exact inv_pos.mpr this

end FinDistr

/-- A concrete decision problem (v2 Definition 5) as an inductive type: a leaf carries a world
and a payoff; a chance node carries a distribution over its `n ≥ 1` children; a decision node
carries a decision point `d` and one child per action of `d`. Finiteness of the tree is
built in (every value is finitely many constructor applications), as v2 Remark 3.1 says.
Source: [[decision-problems-v2]] §3.1 Definition 5; Remark 3.1 (the inductive rendering)
Kind: D
Fidelity: variant: payoffs in a linearly ordered field `K` (v2: `ℝ`); worlds a finite type;
events `Finset Ω` (see the module docstring) -/
inductive Tree (Ω ι : Type) (acts : ι → Type) (K : Type)
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Type
  | leaf (ω : Ω) (r : K) : Tree Ω ι acts K
  | chance (n : ℕ) (β : FinDistr K (Fin n)) (child : Fin n → Tree Ω ι acts K) : Tree Ω ι acts K
  | decision (d : ι) (child : acts d → Tree Ω ι acts K) : Tree Ω ι acts K

variable {Ω ι : Type} {acts : ι → Type}

namespace Tree

/-- The leaves of a tree, as a type of root-to-leaf paths: a leaf has one, a chance node's
leaves are the leaves of its children tagged by the child index, a decision node's by the action.
Source: [[decision-problems-v2]] §3.1 Definition 5 (`Leaves(B)`)
Kind: D -/
def Leaves : Tree Ω ι acts K → Type
  | leaf _ _ => Unit
  | chance n _ child => Σ i : Fin n, (child i).Leaves
  | decision d child => Σ a : acts d, (child a).Leaves

/-- `Fintype` structure on the leaves, by recursion (the leaf set is finite because the tree is).
Source: none: infrastructure
Kind: D -/
@[reducible] def fintypeLeaves [∀ d, Fintype (acts d)] :
    (B : Tree Ω ι acts K) → Fintype B.Leaves
  | leaf _ _ => inferInstanceAs (Fintype Unit)
  | chance n _ child =>
      haveI : ∀ i, Fintype (child i).Leaves := fun i => fintypeLeaves (child i)
      inferInstanceAs (Fintype (Σ i : Fin n, (child i).Leaves))
  | decision d child =>
      haveI : ∀ a, Fintype (child a).Leaves := fun a => fintypeLeaves (child a)
      inferInstanceAs (Fintype (Σ a : acts d, (child a).Leaves))

instance [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K) : Fintype B.Leaves := fintypeLeaves B

/-- Decidable equality on leaves, by recursion.
Source: none: infrastructure
Kind: D -/
@[reducible] def decEqLeaves [∀ d, DecidableEq (acts d)] :
    (B : Tree Ω ι acts K) → DecidableEq B.Leaves
  | leaf _ _ => inferInstanceAs (DecidableEq Unit)
  | chance n _ child =>
      haveI : ∀ i, DecidableEq (child i).Leaves := fun i => decEqLeaves (child i)
      inferInstanceAs (DecidableEq (Σ i : Fin n, (child i).Leaves))
  | decision d child =>
      haveI : ∀ a, DecidableEq (child a).Leaves := fun a => decEqLeaves (child a)
      inferInstanceAs (DecidableEq (Σ a : acts d, (child a).Leaves))

instance [∀ d, DecidableEq (acts d)] (B : Tree Ω ι acts K) : DecidableEq B.Leaves :=
  decEqLeaves B

/-- The world `λ(ℓ)` at a leaf.
Source: [[decision-problems-v2]] §3.1 Definition 5 (`λ(ℓ)`)
Kind: D -/
def world : (B : Tree Ω ι acts K) → B.Leaves → Ω
  | leaf ω _, _ => ω
  | chance _ _ child, ⟨i, ℓ⟩ => world (child i) ℓ
  | decision _ child, ⟨a, ℓ⟩ => world (child a) ℓ

/-- The payoff `r(ℓ)` at a leaf.
Source: [[decision-problems-v2]] §3.1 Definition 5 (`r(ℓ)`)
Kind: D -/
def payoff : (B : Tree Ω ι acts K) → B.Leaves → K
  | leaf _ r, _ => r
  | chance _ _ child, ⟨i, ℓ⟩ => payoff (child i) ℓ
  | decision _ child, ⟨a, ℓ⟩ => payoff (child a) ℓ

/-- The product of the chance weights on a leaf's root path (the `C`-free factor of the run law).
Source: [[decision-problems-v2]] §3.1 Definition 6 (the chance draws of the walk)
Kind: D -/
def chanceWeight : (B : Tree Ω ι acts K) → B.Leaves → K
  | leaf _ _, _ => 1
  | chance _ β child, ⟨i, ℓ⟩ => β.w i * chanceWeight (child i) ℓ
  | decision _ child, ⟨a, ℓ⟩ => chanceWeight (child a) ℓ

/-- The sequence of `(point, action)` pairs drawn along a leaf's root path, in path order.
Source: [[decision-problems-v2]] §3.1 Definition 6 (the decision draws of the walk);
Proposition 4 (the pattern `S` of `a`-draws)
Kind: D -/
def draws : (B : Tree Ω ι acts K) → B.Leaves → List (Σ d : ι, acts d)
  | leaf _ _, _ => []
  | chance _ _ child, ⟨i, ℓ⟩ => draws (child i) ℓ
  | decision d child, ⟨a, ℓ⟩ => ⟨d, a⟩ :: draws (child a) ℓ

/-- `#_d(ℓ)`: the number of `d`-nodes on the root path to `ℓ`.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`#_d(ℓ)`)
Kind: D -/
def count [DecidableEq ι] (d : ι) : (B : Tree Ω ι acts K) → B.Leaves → ℕ
  | leaf _ _, _ => 0
  | chance _ _ child, ⟨i, ℓ⟩ => count d (child i) ℓ
  | decision d' child, ⟨a, ℓ⟩ => (if d' = d then 1 else 0) + count d (child a) ℓ

/-- `occ(d)`: the leaves whose root path contains a `d`-node — an event of the run space
`B.Leaves`, not of `Ω`.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`occ(d) ⊆ Leaves(B)`)
Kind: D -/
def occ [DecidableEq ι] [∀ d, Fintype (acts d)] (d : ι) (B : Tree Ω ι acts K) :
    Finset B.Leaves :=
  Finset.univ.filter fun ℓ => 0 < count d B ℓ

/-- The points queried somewhere in the tree, computed from the tree.
Source: [[decision-problems-v2]] §3.1 Definition 5 ("A point `d` is *queried* if some node
carries it")
Kind: D -/
def queried [DecidableEq ι] [∀ d, Fintype (acts d)] : Tree Ω ι acts K → Finset ι
  | leaf _ _ => ∅
  | chance _ _ child => Finset.univ.biUnion fun i => queried (child i)
  | decision d child => insert d (Finset.univ.biUnion fun a => queried (child a))

/-- The leaves below a chance node are decidably positive iff every chance weight on the path
is positive: since weights are non-negative, that is `0 < chanceWeight`.
Source: `seeds.md` SE-2 ("a path all of whose chance edges have positive probability")
Kind: D -/
def Positive (B : Tree Ω ι acts K) (ℓ : B.Leaves) : Prop := 0 < chanceWeight B ℓ

/-- Almost fair: no root path contains two nodes carrying the same point (`#_d ≤ 1` on every
leaf, for every `d`).
Source: `seeds.md` SE-2 Corollary ("almost-fair tree"); v2 Definition 21 ("no path contains two
nodes sharing a decision-point")
Kind: D -/
def AlmostFair [DecidableEq ι] (B : Tree Ω ι acts K) : Prop := ∀ d ℓ, count d B ℓ ≤ 1

/-- Nested at `d`: some chance-positive path meets two `d`-nodes, and `d` has at least two
actions (a single-action nested point agrees trivially, SE-2 caveat c3).
Source: `seeds.md` SE-2 ("contains two decision nodes carrying one point `d` with `|A_d| ≥ 2`")
Kind: D -/
def Nested [DecidableEq ι] [∀ d, Fintype (acts d)] (B : Tree Ω ι acts K) (d : ι) : Prop :=
  2 ≤ Fintype.card (acts d) ∧ ∃ ℓ, Positive B ℓ ∧ 2 ≤ count d B ℓ

end Tree

/-- A decision procedure: a mixed action at every point (v2 Definition 4).
Source: [[decision-problems-v2]] §2 Definition 4
Kind: D -/
abbrev Proc (ι : Type) (acts : ι → Type) [∀ d, Fintype (acts d)] (K : Type)
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Type :=
  (d : ι) → FinDistr K (acts d)

namespace Proc

variable [∀ d, Fintype (acts d)]

/-- Point-deviation `C[d ↦ m]`: agrees with `C` except at `d`, where it plays `m`.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`C[d ↦ m]`)
Kind: D -/
def deviate [DecidableEq ι] (C : Proc ι acts K) (d : ι) (m : FinDistr K (acts d)) :
    Proc ι acts K :=
  Function.update C d m

/-- `C[d ↦ a] := C[d ↦ δ_a]` for a pure action.
Source: [[decision-problems-v2]] §3.1 Definition 6 (v2.1 change-log item 23)
Kind: D -/
abbrev deviatePure [DecidableEq ι] [∀ d, DecidableEq (acts d)] (C : Proc ι acts K) (d : ι)
    (a : acts d) : Proc ι acts K :=
  deviate C d (FinDistr.pure a)

/-- The deterministic procedure playing the assignment `π`.
Source: [[decision-problems-v2]] §2 Definition 4 ("deterministic")
Kind: D -/
def ofFun [∀ d, DecidableEq (acts d)] (π : (d : ι) → acts d) : Proc ι acts K :=
  fun d => FinDistr.pure (π d)

/-- A procedure is deterministic if every point's mixed action is a point mass.
Source: [[decision-problems-v2]] §2 Definition 4
Kind: D -/
def IsDeterministic [∀ d, DecidableEq (acts d)] (C : Proc ι acts K) : Prop :=
  ∀ d, ∃ a, C d = FinDistr.pure a

/-- Full support: every action has positive weight at every point.
Source: [[decision-problems-v2]] §7.3 Proposition 11 ("some full-support `C'`")
Kind: D -/
def FullSupport (C : Proc ι acts K) : Prop := ∀ d a, 0 < (C d).w a

/-- Deviation at `d` evaluated at `d`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem deviate_same [DecidableEq ι] (C : Proc ι acts K) (d : ι)
    (m : FinDistr K (acts d)) : deviate C d m d = m := by
  simp [deviate]

/-- Deviation at `d` evaluated elsewhere.
Source: none: infrastructure
Kind: L -/
@[simp] theorem deviate_ne [DecidableEq ι] (C : Proc ι acts K) {d d' : ι}
    (m : FinDistr K (acts d)) (h : d' ≠ d) : deviate C d m d' = C d' := by
  simp [deviate, Function.update_of_ne h]

/-- Weight of the deterministic procedure.
Source: none: infrastructure
Kind: L -/
@[simp] theorem ofFun_w [∀ d, DecidableEq (acts d)] (π : (d : ι) → acts d) (d : ι) (a : acts d) :
    (ofFun (K := K) π d).w a = if a = π d then 1 else 0 := rfl

end Proc

namespace Tree

variable [∀ d, Fintype (acts d)]

/-- **Definition 6, the run law `μ_{B,C}`**: walk from the root; at a chance node draw a child
from `β_n`; at a decision node draw `a ∼ C(d_q)` afresh and independently and follow the
`a`-edge. The mass of a leaf is the product of the weights along its path, by structural
recursion.
Source: [[decision-problems-v2]] §3.1 Definition 6
Kind: D
Fidelity: exact -/
def leafLaw (C : Proc ι acts K) : (B : Tree Ω ι acts K) → B.Leaves → K
  | leaf _ _, _ => 1
  | chance _ β child, ⟨i, ℓ⟩ => β.w i * leafLaw C (child i) ℓ
  | decision d child, ⟨a, ℓ⟩ => (C d).w a * leafLaw C (child a) ℓ

/-- The mass `μ_{B,C}(S)` of a set of leaves.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`μ_{B,C} ∈ Δ(Leaves(B))`)
Kind: D -/
def mass (C : Proc ι acts K) (B : Tree Ω ι acts K) (S : Finset B.Leaves) : K :=
  ∑ ℓ ∈ S, leafLaw C B ℓ

/-- The leaves whose world satisfies the event `X`: `{ℓ : λ(ℓ) ⊨ X}`.
Source: [[decision-problems-v2]] §3.1 Definition 6
Kind: D -/
def worldEv [DecidableEq Ω] (B : Tree Ω ι acts K) (X : Finset Ω) : Finset B.Leaves :=
  Finset.univ.filter fun ℓ => world B ℓ ∈ X

/-- **The objective statistics `ν_{B,C}(X) := μ_{B,C}{ℓ : λ(ℓ) ⊨ X}`.**
Source: [[decision-problems-v2]] §3.1 Definition 6
Kind: D
Fidelity: exact (events are `Finset Ω`) -/
def nu [DecidableEq Ω] (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) : K :=
  mass C B (worldEv B X)

/-- **The value `V_B(C) := 𝔼_{μ_{B,C}}[r]`.**
Source: [[decision-problems-v2]] §3.1 Definition 6
Kind: D
Fidelity: exact -/
def value (C : Proc ι acts K) (B : Tree Ω ι acts K) : K :=
  ∑ ℓ, leafLaw C B ℓ * payoff B ℓ

/-- The product of the draw weights `C(d_q)(a_q)` along a leaf's path.
Source: [[decision-problems-v2]] §3.1 Definition 6
Kind: D -/
def drawsWeight (C : Proc ι acts K) (B : Tree Ω ι acts K) (ℓ : B.Leaves) : K :=
  ((draws B ℓ).map fun x => (C x.1).w x.2).prod

/-- **Definition 6′, operational rendering (route (a))**: a memoised walk. `env d = some a`
means the seed `a_d = a` has already been drawn on this run; at a `d`-node the walk then
follows `a` with weight one (zero on the other edges). `env d = none` means `d` is met for the
first time: draw `a ∼ C(d)` with weight `C(d)(a)`, record it, and continue.
Source: `cf-workflow/phase2-notes/repair/seeds.md` "Definitions carried", Definition 6′
Kind: D
Fidelity: exact (one seed per queried point per run, reused at every node carrying it) -/
def leafLawSeed [DecidableEq ι] [∀ d, DecidableEq (acts d)] (C : Proc ι acts K)
    (env : (d : ι) → Option (acts d)) : (B : Tree Ω ι acts K) → B.Leaves → K
  | leaf _ _, _ => 1
  | chance _ β child, ⟨i, ℓ⟩ => β.w i * leafLawSeed C env (child i) ℓ
  | decision d child, ⟨a, ℓ⟩ =>
      match env d with
      | some a' => if a' = a then leafLawSeed C env (child a) ℓ else 0
      | none => (C d).w a * leafLawSeed C (Function.update env d (some a)) (child a) ℓ

/-- **The shared-seed run law `μ'_{B,C}`** (Definition 6′): the memoised walk started with no
seeds drawn.
Source: `seeds.md` Definition 6′ (`μ'_{B,C}`)
Kind: D -/
def leafLaw' [DecidableEq ι] [∀ d, DecidableEq (acts d)] (C : Proc ι acts K)
    (B : Tree Ω ι acts K) : B.Leaves → K :=
  leafLawSeed C (fun _ => none) B

/-- `ν'_{B,C}`, the world-marginal of the shared-seed law.
Source: `seeds.md` Definition 6′ (`ν'_{B,C}`)
Kind: D -/
def nu' [DecidableEq ι] [∀ d, DecidableEq (acts d)] [DecidableEq Ω] (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (X : Finset Ω) : K :=
  ∑ ℓ ∈ worldEv B X, leafLaw' C B ℓ

/-- `V'_B(C)`, the value under the shared-seed law.
Source: `seeds.md` Definition 6′ (`V'_B(C)`)
Kind: D -/
def value' [DecidableEq ι] [∀ d, DecidableEq (acts d)] (C : Proc ι acts K)
    (B : Tree Ω ι acts K) : K :=
  ∑ ℓ, leafLaw' C B ℓ * payoff B ℓ

/-- The run-level event "some `d`-node on the path took the `a`-edge".
Source: `cf-workflow/phase2-notes/repair/faithful.md` FA-4 (the `drew` coordinate)
Kind: D -/
def drew [DecidableEq ι] [∀ d, DecidableEq (acts d)] (d : ι) (a : acts d)
    (B : Tree Ω ι acts K) : Finset B.Leaves :=
  Finset.univ.filter fun ℓ => (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ

/-- The number of `d`-nodes on the path that took the `a`-edge.
Source: [[decision-problems-v2]] Proposition 4 (`|S|`, the number of `a`-draws)
Kind: D -/
def countDraw [DecidableEq ι] [∀ d, DecidableEq (acts d)] (d : ι) (a : acts d)
    (B : Tree Ω ι acts K) (ℓ : B.Leaves) : ℕ :=
  (draws B ℓ).count ⟨d, a⟩

end Tree

end Cleanroom.Found.DpCoreTree
