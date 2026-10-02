import Cleanroom.Decision.DpCausalConsist.Truncate

/-!
# `dp-causal-consist`: the toolkit for DAGs on three boolean coordinates

Every witness of the package lives on `W3 := Fin 3 → Bool` (coordinates `0 = ℓ`, `1 = m`,
`2 = k`; `pt3 ℓ m k` the point). This file supplies: Bernoulli factors (`bern`), DAGs given by an
adjacency table (`dag3`, with `Digraph.parents` decidable), acyclicity from a rank function
(`isAcyclic_of_rank`) and non-ancestry from it (`not_isAncestor_of_rank`, for `nondesc`
membership), CPDs from a rate table (`cpdOfRate`: node `v`'s Bernoulli rate as a function of
the three coordinates, of which only the parents are read), distributions from a mass table
(`distr3`), and the evaluation lemmas that turn `IsFor`, truncated probabilities and
conditionals into eight-term rational identities for `norm_num`.
-/

namespace Cleanroom.Decision.DpCausalConsist

open FactoredSpaces Finset

/-- The three-coordinate boolean world space. Source: mandate §3.1. Kind: D -/
abbrev W3 : Type := Pt (fun _ : Fin 3 => Bool)

/-- `pt3` is injective coordinatewise. Source: none: infrastructure. Kind: L -/
@[simp] theorem pt3_inj (a b c a' b' c' : Bool) :
    pt3 a b c = pt3 a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    exact ⟨by have := congrFun h 0; simpa using this, by have := congrFun h 1; simpa using this,
      by have := congrFun h 2; simpa using this⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-! ## Bernoulli factors -/

/-- The Bernoulli distribution on `Bool` with `P(true) = p`.
Source: none: infrastructure
Kind: D -/
noncomputable def bern (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distr Bool where
  mass b := if b then p else 1 - p
  nonneg b := by cases b <;> simp <;> linarith
  sum_eq_one := by simp [Fintype.sum_bool]

/-- Mass of `bern`. Source: none: infrastructure. Kind: L -/
@[simp] theorem bern_mass (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) :
    (bern p h0 h1).mass b = if b then p else 1 - p := rfl

/-! ## DAGs on `Fin 3` from an adjacency table -/

/-- The digraph on `Fin 3` with adjacency table `adj` (`adj a b = true` iff `a → b`).
Source: none: infrastructure (Mathlib `Digraph`, FAF's client pattern in `APITests`)
Kind: D -/
def dag3 (adj : Fin 3 → Fin 3 → Bool) : Digraph (Fin 3) := ⟨fun a b => adj a b = true⟩

instance (adj : Fin 3 → Fin 3 → Bool) : DecidableRel (dag3 adj).Adj :=
  fun a b => inferInstanceAs (Decidable (adj a b = true))

/-- Adjacency in `dag3`. Source: none: infrastructure. Kind: L -/
@[simp] theorem dag3_adj (adj : Fin 3 → Fin 3 → Bool) (a b : Fin 3) :
    (dag3 adj).Adj a b ↔ adj a b = true := Iff.rfl

/-- A digraph with a strictly increasing rank along edges is acyclic.
Source: none: infrastructure (FAF's `Examples.lean` rank argument, made a lemma)
Kind: L -/
theorem isAcyclic_of_rank {W : Type} (G : Digraph W) (r : W → ℕ)
    (h : ∀ u v, G.Adj u v → r u < r v) : G.IsAcyclic := by
  intro v hv
  have key : ∀ a b, Relation.TransGen G.Adj a b → r a < r b := by
    intro a b hab
    induction hab with
    | single hab => exact h _ _ hab
    | tail _ hbc ih => exact ih.trans (h _ _ hbc)
  exact lt_irrefl _ (key v v hv)

/-- Under a rank, `u` is not an ancestor of `v` when `r v ≤ r u`.
Source: none: infrastructure
Kind: L -/
theorem not_isAncestor_of_rank {W : Type} (G : Digraph W) (r : W → ℕ)
    (h : ∀ u v, G.Adj u v → r u < r v) {u v : W} (huv : r v ≤ r u) : ¬ G.IsAncestor u v := by
  intro hanc
  have key : ∀ a b, Relation.TransGen G.Adj a b → r a < r b := by
    intro a b hab
    induction hab with
    | single hab => exact h _ _ hab
    | tail _ hbc ih => exact ih.trans (h _ _ hbc)
  exact absurd (key u v hanc) (not_lt.mpr huv)

/-- Membership in `nondesc` from a rank: a coordinate of rank `≤ r m` other than `m`.
Source: none: infrastructure
Kind: L -/
theorem mem_nondesc_of_rank {W : Type} [Fintype W] [DecidableEq W] (G : Digraph W) (r : W → ℕ)
    (h : ∀ u v, G.Adj u v → r u < r v) {m v : W} (hne : v ≠ m) (hr : r v ≤ r m) :
    v ∈ nondesc G m := by
  rw [mem_nondesc]
  exact ⟨hne, not_isAncestor_of_rank G r h hr⟩

/-! ## CPDs from rate tables -/

/-- Read a parent configuration at a coordinate (`false` at a non-parent).
Source: none: infrastructure
Kind: D -/
def readAt {G : Digraph (Fin 3)} [DecidableRel G.Adj] {v : Fin 3}
    (c : ParentVals G (fun _ : Fin 3 => Bool) v) (u : Fin 3) : Bool :=
  if h : u ∈ G.parents v then c ⟨u, h⟩ else false

/-- `readAt` of a point's parent configuration reads the point at the parents.
Source: none: infrastructure
Kind: L -/
theorem readAt_parentConfig (G : Digraph (Fin 3)) [DecidableRel G.Adj] (x : W3) (v u : Fin 3) :
    readAt (parentConfig G (fun _ : Fin 3 => Bool) x v) u
      = if u ∈ G.parents v then x u else false := by
  unfold readAt parentConfig proj
  split_ifs <;> rfl

/-- A rate table: the Bernoulli rate of each node as a function of the three coordinates.
Source: none: infrastructure
Kind: D -/
structure Rate3 where
  /-- `r v ℓ m k` is `P(x_v = 1 | ℓ, m, k)` (only the parents of `v` are read). -/
  r : Fin 3 → Bool → Bool → Bool → ℝ
  /-- Rates are nonnegative. -/
  nonneg : ∀ v a b c, 0 ≤ r v a b c
  /-- Rates are at most one. -/
  le_one : ∀ v a b c, r v a b c ≤ 1

/-- The CPD of a rate table on a DAG: node `v`'s factor at a parent configuration is
`bern (r v ·)` read at the parents (non-parents read `false`).
Source: none: infrastructure (FAF `CPD`)
Kind: D -/
noncomputable def cpdOfRate (G : Digraph (Fin 3)) [DecidableRel G.Adj] (R : Rate3) :
    CPD (G := G) (Val := fun _ : Fin 3 => Bool) :=
  fun v c => bern (R.r v (readAt c 0) (readAt c 1) (readAt c 2)) (R.nonneg _ _ _ _)
    (R.le_one _ _ _ _)

/-- The factor of a rate-table CPD at a point.
Source: none: infrastructure
Kind: L -/
theorem cpdFactor_cpdOfRate (G : Digraph (Fin 3)) [DecidableRel G.Adj] (R : Rate3) (v : Fin 3)
    (x : W3) :
    cpdFactor (cpdOfRate G R) v x =
      if x v then R.r v (if (0 : Fin 3) ∈ G.parents v then x 0 else false)
          (if (1 : Fin 3) ∈ G.parents v then x 1 else false)
          (if (2 : Fin 3) ∈ G.parents v then x 2 else false)
        else 1 - R.r v (if (0 : Fin 3) ∈ G.parents v then x 0 else false)
          (if (1 : Fin 3) ∈ G.parents v then x 1 else false)
          (if (2 : Fin 3) ∈ G.parents v then x 2 else false) := by
  unfold cpdFactor cpdOfRate
  rw [bern_mass, readAt_parentConfig, readAt_parentConfig, readAt_parentConfig]

/-! ## Distributions from a mass table -/

/-- A distribution on `W3` from a mass table `w ℓ m k`.
Source: none: infrastructure
Kind: D -/
noncomputable def distr3 (w : Bool → Bool → Bool → ℝ) (hn : ∀ a b c, 0 ≤ w a b c)
    (hs : w false false false + w false false true + w false true false + w false true true
      + w true false false + w true false true + w true true false + w true true true = 1) :
    Distr W3 where
  mass x := w (x 0) (x 1) (x 2)
  nonneg x := hn _ _ _
  sum_eq_one := by rw [sum_pt3]; exact hs

/-- Mass of `distr3` at a `pt3`. Source: none: infrastructure. Kind: L -/
@[simp] theorem distr3_mass (w : Bool → Bool → Bool → ℝ) (hn) (hs) (a b c : Bool) :
    (distr3 w hn hs).mass (pt3 a b c) = w a b c := rfl

/-- Mass of `distr3` at a point. Source: none: infrastructure. Kind: L -/
theorem distr3_mass' (w : Bool → Bool → Bool → ℝ) (hn) (hs) (x : W3) :
    (distr3 w hn hs).mass x = w (x 0) (x 1) (x 2) := rfl

/-! ## Evaluation lemmas -/

/-- `∏_{v ≠ 1} f v = f 0 · f 2` on `Fin 3`. Source: none: infrastructure. Kind: L -/
theorem prod_erase_one (f : Fin 3 → ℝ) : ∏ v ∈ Finset.univ.erase (1 : Fin 3), f v = f 0 * f 2 := by
  have : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  rw [this, Finset.prod_pair (by decide)]

/-- A probability on `W3` of a decidable event as its eight terms.
Source: none: infrastructure
Kind: L -/
theorem prob3_eq (P : Distr W3) (p : W3 → Prop) [DecidablePred p] :
    P.prob {x | p x} =
      (if p (pt3 false false false) then P.mass (pt3 false false false) else 0)
      + (if p (pt3 false false true) then P.mass (pt3 false false true) else 0)
      + (if p (pt3 false true false) then P.mass (pt3 false true false) else 0)
      + (if p (pt3 false true true) then P.mass (pt3 false true true) else 0)
      + (if p (pt3 true false false) then P.mass (pt3 true false false) else 0)
      + (if p (pt3 true false true) then P.mass (pt3 true false true) else 0)
      + (if p (pt3 true true false) then P.mass (pt3 true true false) else 0)
      + (if p (pt3 true true true) then P.mass (pt3 true true true) else 0) := by
  rw [prob_setOf_eq_sum_ite, sum_pt3]

/-- `IsFor` on `W3` as eight equations. Source: none: infrastructure. Kind: L -/
theorem isFor_iff3 (Γ : CausalStructure (fun _ : Fin 3 => Bool)) (P : Distr W3) :
    Γ.IsFor P ↔ ∀ a b c, P.mass (pt3 a b c)
      = cpdFactor Γ.φ 0 (pt3 a b c) * cpdFactor Γ.φ 1 (pt3 a b c) * cpdFactor Γ.φ 2 (pt3 a b c) := by
  unfold CausalStructure.IsFor
  rw [forall_pt3]
  simp only [Fin.prod_univ_three]

/-- `IsFor` of a rate-table structure as eight equations in the rates (the instance is the
declared one, so `cpdFactor_cpdOfRate` applies).
Source: none: infrastructure
Kind: L -/
theorem isFor_cpdOfRate_iff (G : Digraph (Fin 3)) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (R : Rate3) (P : Distr W3) :
    (⟨G, hG, cpdOfRate G R⟩ : CausalStructure (fun _ : Fin 3 => Bool)).IsFor P ↔
      ∀ a b c, P.mass (pt3 a b c)
        = cpdFactor (cpdOfRate G R) 0 (pt3 a b c) * cpdFactor (cpdOfRate G R) 1 (pt3 a b c)
          * cpdFactor (cpdOfRate G R) 2 (pt3 a b c) := by
  show (∀ x, P.mass x = ∏ v, cpdFactor (cpdOfRate G R) v x) ↔ _
  rw [forall_pt3]
  simp only [Fin.prod_univ_three]

/-- The truncated law of a rate-table structure at `do(m := b)`, `m = 1`, as a mass table.
Source: none: infrastructure
Kind: L -/
theorem truncate_cpdOfRate_mass (G : Digraph (Fin 3)) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (R : Rate3) (b : Bool) (x : W3) :
    ((⟨G, hG, cpdOfRate G R⟩ : CausalStructure (fun _ : Fin 3 => Bool)).truncate 1 b).mass x
      = if x 1 = b then cpdFactor (cpdOfRate G R) 0 x * cpdFactor (cpdOfRate G R) 2 x else 0 := by
  show (truncate hG (cpdOfRate G R) 1 b).mass x = _
  rw [truncate_mass, prod_erase_one]

end Cleanroom.Decision.DpCausalConsist
