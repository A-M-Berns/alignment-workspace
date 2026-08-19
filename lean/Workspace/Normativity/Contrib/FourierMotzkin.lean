/-
# Fourier–Motzkin elimination over ℚ

An executable decision procedure for feasibility of a finite system of rational linear
inequalities **over the reals**.

The point of the file is a single `def` — `feasible` — that runs, together with a proof
that what it computes is exactly real solvability of the system it is handed.  Nothing
here is optimised for speed or generality: the elimination is the textbook one, the data
is lists and rationals, and the trusted surface is meant to be small enough to read.

## The representation

A constraint is `⟨coeffs, const, strict⟩`, read as `∑ i, coeffs[i] * x i ≤ const` when
`strict = false` and `< const` when `strict = true`.  Two deliberate choices:

* **`coeffs` is a plain `List ℚ`, indexed positionally, and its length is not tied to the
  dimension.**  Entries past the dimension are ignored and missing entries read as `0`
  (`List.getD`).  This buys the elimination step a genuine simplification: a constraint
  that does not mention the variable being eliminated is passed through *untouched*, with
  no truncation and no re-indexing, because the satisfaction predicate at the smaller
  dimension already ignores the extra slot.

* **Strict and non-strict are distinct.**  They are not identified, and the elimination
  tracks strictness through every combination: a combined constraint is strict exactly
  when one of its two parents is.  Downstream consumers need the open case.

**Equalities are not a separate form.**  A caller wanting `a · x = b` supplies the two
non-strict constraints `a · x ≤ b` and `(-a) · x ≤ -b`.  The procedure is complete for
that encoding, so nothing is lost.

## Satisfaction lives in ℝ, the data lives in ℚ

`LinCon.Sat` interprets a constraint at a real point.  That is the predicate the callers'
regions are phrased in, and stating it over `ℝ` from the start means the file never needs
the (true, but irrelevant here) fact that a rational system is real-feasible iff it is
rational-feasible.  Everything is proved directly about the real solution set.

## The shape of the argument

`elim d cs` eliminates the **last** coordinate.  Constraints are partitioned by the sign
of that coordinate's coefficient into lower bounds (`< 0`), upper bounds (`> 0`), and
constraints that do not mention it (`= 0`); the output is the untouched ones together with
one combination per (lower, upper) pair.  `elim_sat_iff` says this is exactly projection
along the last coordinate:

    Sat (elim d cs) x ↔ ∃ t, Sat cs (Fin.snoc x t)

`←` is soundness and is a chain of two inequalities.  `→` is completeness: it produces the
witness `t` from a largest lower bound and a smallest upper bound, and the strictness
bookkeeping is the whole content.  When the largest lower bound is *equal* to the smallest
upper bound, the witness must be that common value, and the argument that no strict
constraint is violated there runs through the combined constraint that pairs the offending
strict bound with the extremal bound on the other side.  The four degenerate cases — no
lower bounds, no upper bounds, neither, both — are handled separately and explicitly.

`feasible` iterates `elim` down to dimension zero, where a constraint has an empty sum on
the left and feasibility is the rational comparison `0 ≤ const` or `0 < const`.  It is
structural recursion on the dimension: no well-founded recursion, no `decidable_of_iff`
around a classical instance, no `Classical.choose`.  It runs — the `#eval` block at the
end of the file is the check.

`#print axioms feasible` reports `Classical.choice`, and that is not a defect in this
file: rational multiplication alone reports it, because mathlib's `Mul ℚ` instance is
reached through structures with classical proof fields.  `List.getD` on `ℚ` and
`List.range` are clean; `p * q` is not.  Nothing here can avoid that, and it is inside the
repository's axiom bound.

## Dimension is an explicit argument, not a type index

`LinCon` carries no dimension index.  A phantom index on an `abbrev` would be
uninferable — `cs : List (LinCon (d+1))` would leave `d` unsolved, since the abbrev
ignores it — and a genuine `structure` index would cost the hand-written `Primcodable`
transport this file exists to avoid.  So `lastCoeff`, `combine`, `elim` and `feasible`
take `d` explicitly, and `Sat` reads it off the point `x : Fin d → ℝ`.

## Computability

`feasible_primrec₂ : Primrec₂ fun d cs => feasible d cs` is the headline certificate, and
the quantifier order is the point.  A family `∀ d, Primrec (feasible d)` cannot be used by
a caller whose ambient dimension is computed from its own arguments — which is exactly the
downstream compiler's situation, where the dimension is a fragment length plus a vertex
count, both read off the inputs and both varying by date.  `feasible_primrec` is the fixed
dimension specialisation, derived from it in one line and kept as a separate statement
because most call sites want that form.

`LinCon` is an `abbrev` for `List ℚ × ℚ × Bool` precisely so that `Primcodable` is
inherited and the accessors are literal projections.

Two things need care to get the uniform version.  First, `Primrec.listFilter` fixes its
predicate once and for all, and the elimination's sign test depends on the dimension; the
parametrised replacement here goes through `Primrec.listFilterMap`, which is already
parametrised.  Second, and more substantially, `feasible` is **not** an iteration of a
single function of the constraint list: unrolled it is

    feasible d cs = base (elim 0 (elim 1 (⋯ (elim (d-1) cs))))

with the eliminated dimension counting *down*.  The fix is to iterate on the pair
`(current dimension, current system)`, so that one map `elimStep` — decrement and
eliminate — does the whole descent as `elimStep^[d]` applied to `(d, cs)`.  That is a
plain `Primrec.nat_iterate`, and `feasible_eq_iterate` is the unrolling lemma that
licenses it.

Names are provisional (`AGENTS.md` standard 6).
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import LogicalInduction.Construction.LIACompiler

namespace Workspace.Normativity.Contrib.FourierMotzkin

open LogicalInduction

/-! ## Constraints -/

/-- A rational linear constraint: `⟨coeffs, const, strict⟩` denotes
`∑ i, coeffs[i] * x i ≤ const` if `strict` is `false`, and `< const` if `strict` is `true`.

An `abbrev` of a product rather than a `structure`, so that `Primcodable` is inherited and
the accessors below are literal projections.  Equalities are encoded by the caller as two
non-strict constraints; see the file header. -/
abbrev LinCon : Type := List ℚ × ℚ × Bool

namespace LinCon

/-- The coefficient list, indexed positionally; missing entries read as `0`. -/
abbrev coeffs (c : LinCon) : List ℚ := c.1

/-- The right-hand side. -/
abbrev const (c : LinCon) : ℚ := c.2.1

/-- `true` for `<`, `false` for `≤`. -/
abbrev strict (c : LinCon) : Bool := c.2.2

/-- Build a constraint.  Only for readability at call sites. -/
def of (coeffs : List ℚ) (const : ℚ) (strict : Bool) : LinCon := (coeffs, const, strict)

/-- The left-hand side of the constraint evaluated at a real point of `Fin d → ℝ`.
Coefficients beyond position `d` are ignored, and positions the list does not reach
contribute `0`. -/
def eval {d : ℕ} (c : LinCon) (x : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, ((c.coeffs.getD (i : ℕ) 0 : ℚ) : ℝ) * x i

/-- Satisfaction of a single constraint at a real point. -/
def Sat {d : ℕ} (c : LinCon) (x : Fin d → ℝ) : Prop :=
  if c.strict then c.eval x < (c.const : ℝ) else c.eval x ≤ (c.const : ℝ)

end LinCon

/-- Satisfaction of a finite system: every constraint holds. -/
def Sat {d : ℕ} (cs : List LinCon) (x : Fin d → ℝ) : Prop := ∀ c ∈ cs, c.Sat x

/-! ## The elimination step

`lastCoeff d c` is the coefficient of the coordinate being eliminated — position `d`, the
last one of `Fin (d+1)`. -/

/-- The coefficient of the variable being eliminated. -/
def lastCoeff (d : ℕ) (c : LinCon) : ℚ := c.coeffs.getD d 0

/-- The positional combination `p • l - n • m`, truncated to the first `d` entries.
Truncation is what makes the result a constraint of the smaller dimension on the nose. -/
def comboCoeffs (d : ℕ) (p n : ℚ) (l m : List ℚ) : List ℚ :=
  (List.range d).map fun i => p * l.getD i 0 - n * m.getD i 0

/-- Combine a lower bound `cl` (negative last coefficient) with an upper bound `cu`
(positive last coefficient).  The last coefficient of the result is `0` by construction,
and the result is strict exactly when one of the parents is. -/
def combine (d : ℕ) (cl cu : LinCon) : LinCon :=
  (comboCoeffs d (lastCoeff d cu) (lastCoeff d cl) cl.coeffs cu.coeffs,
   lastCoeff d cu * cl.const - lastCoeff d cl * cu.const,
   cl.strict || cu.strict)

/-- One Fourier–Motzkin step: eliminate the last of `d+1` coordinates. -/
def elim (d : ℕ) (cs : List LinCon) : List LinCon :=
  cs.filter (fun c => decide (lastCoeff d c = 0)) ++
    (cs.filter (fun c => decide (lastCoeff d c < 0))).flatMap fun cl =>
      (cs.filter (fun c => decide (0 < lastCoeff d c))).map fun cu => combine d cl cu

/-- The decision procedure: eliminate coordinates one at a time down to dimension zero,
where a constraint is `0 ≤ const` or `0 < const`. -/
def feasible : ℕ → List LinCon → Bool
  | 0, cs => cs.all fun c => cond c.strict (decide (0 < c.const)) (decide (0 ≤ c.const))
  | d + 1, cs => feasible d (elim d cs)

/-! ## Real-arithmetic scaffolding

Six one-line reorientations of a linear inequality across a division.  They are stated
separately so that the constraint-level lemmas below are pure bookkeeping. -/

private lemma add_mul_le_iff_neg {e a t b : ℝ} (ha : a < 0) :
    e + a * t ≤ b ↔ (b - e) / a ≤ t := by
  rw [div_le_iff_of_neg ha]; constructor <;> intro h <;> linarith

private lemma add_mul_lt_iff_neg {e a t b : ℝ} (ha : a < 0) :
    e + a * t < b ↔ (b - e) / a < t := by
  rw [div_lt_iff_of_neg ha]; constructor <;> intro h <;> linarith

private lemma add_mul_le_iff_pos {e a t b : ℝ} (ha : 0 < a) :
    e + a * t ≤ b ↔ t ≤ (b - e) / a := by
  rw [le_div_iff₀ ha]; constructor <;> intro h <;> linarith

private lemma add_mul_lt_iff_pos {e a t b : ℝ} (ha : 0 < a) :
    e + a * t < b ↔ t < (b - e) / a := by
  rw [lt_div_iff₀ ha]; constructor <;> intro h <;> linarith

private lemma div_le_div_cross {n p bl el bu eu : ℝ} (hn : n < 0) (hp : 0 < p) :
    (bl - el) / n ≤ (bu - eu) / p ↔ p * el - n * eu ≤ p * bl - n * bu := by
  rw [div_le_iff_of_neg hn, div_mul_eq_mul_div, div_le_iff₀ hp]
  constructor <;> intro h <;> linarith

private lemma div_lt_div_cross {n p bl el bu eu : ℝ} (hn : n < 0) (hp : 0 < p) :
    (bl - el) / n < (bu - eu) / p ↔ p * el - n * eu < p * bl - n * bu := by
  rw [div_lt_iff_of_neg hn, div_mul_eq_mul_div, div_lt_iff₀ hp]
  constructor <;> intro h <;> linarith

/-- A nonempty list has an element maximising any function into a linear order. -/
private lemma exists_max_image {α : Type*} {β : Type*} [LinearOrder β] (f : α → β) :
    ∀ l : List α, l ≠ [] → ∃ a ∈ l, ∀ b ∈ l, f b ≤ f a := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _
    rcases eq_or_ne t [] with rfl | ht
    · exact ⟨a, by simp, by simp⟩
    · obtain ⟨c, hc, hmax⟩ := ih ht
      by_cases hac : f c ≤ f a
      · refine ⟨a, by simp, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_rfl
        · exact (hmax y hy).trans hac
      · refine ⟨c, List.mem_cons_of_mem _ hc, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (not_le.mp hac).le
        · exact hmax y hy

/-- A nonempty list has an element minimising any function into a linear order. -/
private lemma exists_min_image {α : Type*} {β : Type*} [LinearOrder β] (f : α → β)
    (l : List α) (h : l ≠ []) : ∃ a ∈ l, ∀ b ∈ l, f a ≤ f b :=
  exists_max_image (β := βᵒᵈ) (fun a => (f a : βᵒᵈ)) l h

/-! ## What one constraint says about the eliminated coordinate -/

/-- Splitting the left-hand side at the last coordinate. -/
private lemma eval_snoc {d : ℕ} (c : LinCon) (x : Fin d → ℝ) (t : ℝ) :
    c.eval (Fin.snoc x t) = c.eval x + ((lastCoeff d c : ℚ) : ℝ) * t := by
  unfold LinCon.eval lastCoeff
  rw [Fin.sum_univ_castSucc]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      simp only [Fin.snoc_castSucc, Fin.val_castSucc]
  · simp only [Fin.snoc_last, Fin.val_last]

/-- The bound the constraint places on the eliminated coordinate, once the remaining
coordinates are fixed at `x`.  Only meaningful when `lastCoeff d c ≠ 0`. -/
private noncomputable def bnd {d : ℕ} (c : LinCon) (x : Fin d → ℝ) : ℝ :=
  ((c.const : ℝ) - c.eval x) / ((lastCoeff d c : ℚ) : ℝ)

/-- A constraint that does not mention the eliminated coordinate says the same thing
before and after the coordinate is supplied. -/
private lemma sat_snoc_zero {d : ℕ} {c : LinCon} (h : lastCoeff d c = 0)
    (x : Fin d → ℝ) (t : ℝ) : c.Sat (Fin.snoc x t) ↔ c.Sat x := by
  unfold LinCon.Sat
  rw [eval_snoc, h]
  simp

/-- A negative last coefficient makes the constraint a lower bound on the coordinate. -/
private lemma sat_snoc_neg {d : ℕ} {c : LinCon} (h : lastCoeff d c < 0)
    (x : Fin d → ℝ) (t : ℝ) :
    c.Sat (Fin.snoc x t) ↔ (if c.strict then bnd c x < t else bnd c x ≤ t) := by
  have h' : ((lastCoeff d c : ℚ) : ℝ) < 0 := by exact_mod_cast h
  unfold LinCon.Sat bnd
  rw [eval_snoc]
  by_cases hs : c.strict = true
  · simp only [if_pos hs]; exact add_mul_lt_iff_neg h'
  · simp only [if_neg hs]; exact add_mul_le_iff_neg h'

/-- A positive last coefficient makes the constraint an upper bound on the coordinate. -/
private lemma sat_snoc_pos {d : ℕ} {c : LinCon} (h : 0 < lastCoeff d c)
    (x : Fin d → ℝ) (t : ℝ) :
    c.Sat (Fin.snoc x t) ↔ (if c.strict then t < bnd c x else t ≤ bnd c x) := by
  have h' : (0 : ℝ) < ((lastCoeff d c : ℚ) : ℝ) := by exact_mod_cast h
  unfold LinCon.Sat bnd
  rw [eval_snoc]
  by_cases hs : c.strict = true
  · simp only [if_pos hs]; exact add_mul_lt_iff_pos h'
  · simp only [if_neg hs]; exact add_mul_le_iff_pos h'

/-! ## What the combined constraint says -/

private lemma getD_comboCoeffs {d : ℕ} (p n : ℚ) (l m : List ℚ) (i : Fin d) :
    (comboCoeffs d p n l m).getD (i : ℕ) 0 = p * l.getD (i : ℕ) 0 - n * m.getD (i : ℕ) 0 := by
  unfold comboCoeffs
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma combine_eval {d : ℕ} (cl cu : LinCon) (x : Fin d → ℝ) :
    (combine d cl cu).eval x
      = ((lastCoeff d cu : ℚ) : ℝ) * cl.eval x - ((lastCoeff d cl : ℚ) : ℝ) * cu.eval x := by
  unfold LinCon.eval
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hg : (combine d cl cu).coeffs.getD (i : ℕ) 0
      = lastCoeff d cu * cl.coeffs.getD (i : ℕ) 0
        - lastCoeff d cl * cu.coeffs.getD (i : ℕ) 0 := getD_comboCoeffs _ _ _ _ i
  rw [hg]
  push_cast
  ring

/-- The combined constraint holds at `x` exactly when the lower bound `cl` imposes lies
below the upper bound `cu` imposes — strictly, if either parent is strict. -/
private lemma combine_sat_iff {d : ℕ} {cl cu : LinCon} (x : Fin d → ℝ)
    (hl : lastCoeff d cl < 0) (hu : 0 < lastCoeff d cu) :
    (combine d cl cu).Sat x ↔
      (if cl.strict || cu.strict then bnd cl x < bnd cu x else bnd cl x ≤ bnd cu x) := by
  have hn : ((lastCoeff d cl : ℚ) : ℝ) < 0 := by exact_mod_cast hl
  have hp : (0 : ℝ) < ((lastCoeff d cu : ℚ) : ℝ) := by exact_mod_cast hu
  have hstrict : (combine d cl cu).strict = (cl.strict || cu.strict) := rfl
  have hconst : (((combine d cl cu).const : ℚ) : ℝ)
      = ((lastCoeff d cu : ℚ) : ℝ) * (cl.const : ℝ)
        - ((lastCoeff d cl : ℚ) : ℝ) * (cu.const : ℝ) := by
    show (((lastCoeff d cu * cl.const - lastCoeff d cl * cu.const : ℚ)) : ℝ) = _
    push_cast
    ring
  unfold LinCon.Sat bnd
  rw [hstrict, combine_eval, hconst]
  by_cases hs : (cl.strict || cu.strict) = true
  · simp only [if_pos hs]; exact (div_lt_div_cross hn hp).symm
  · simp only [if_neg hs]; exact (div_le_div_cross hn hp).symm

/-! ## Membership in the eliminated system -/

private lemma mem_elim_of_zero {d : ℕ} {cs : List LinCon} {c : LinCon}
    (hc : c ∈ cs) (h0 : lastCoeff d c = 0) : c ∈ elim d cs := by
  unfold elim
  exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hc, by simp [h0]⟩))

private lemma mem_elim_combine {d : ℕ} {cs : List LinCon} {cl cu : LinCon}
    (hcl : cl ∈ cs) (hl : lastCoeff d cl < 0) (hcu : cu ∈ cs) (hu : 0 < lastCoeff d cu) :
    combine d cl cu ∈ elim d cs := by
  unfold elim
  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨cl, ?_, ?_⟩))
  · exact List.mem_filter.mpr ⟨hcl, by simp [hl]⟩
  · exact List.mem_map.mpr ⟨cu, List.mem_filter.mpr ⟨hcu, by simp [hu]⟩, rfl⟩

private lemma elim_cases {d : ℕ} {cs : List LinCon} {c : LinCon} (h : c ∈ elim d cs) :
    (c ∈ cs ∧ lastCoeff d c = 0) ∨
      (∃ cl ∈ cs, ∃ cu ∈ cs,
        lastCoeff d cl < 0 ∧ 0 < lastCoeff d cu ∧ c = combine d cl cu) := by
  unfold elim at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl ⟨(List.mem_filter.mp h).1, by simpa using (List.mem_filter.mp h).2⟩
  · obtain ⟨cl, hcl, h⟩ := List.mem_flatMap.mp h
    obtain ⟨cu, hcu, rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨cl, (List.mem_filter.mp hcl).1, cu, (List.mem_filter.mp hcu).1,
      by simpa using (List.mem_filter.mp hcl).2, by simpa using (List.mem_filter.mp hcu).2, rfl⟩

/-! ## The elimination theorem -/

/-- **Fourier–Motzkin, one step.**  Eliminating the last coordinate computes exactly the
projection of the solution set along that coordinate.

`←` is soundness: a witness `t` chains each lower bound through `t` to each upper bound.
`→` is completeness: from the eliminated system one manufactures a `t`. -/
theorem elim_sat_iff {d : ℕ} (cs : List LinCon) (x : Fin d → ℝ) :
    Sat (elim d cs) x ↔ ∃ t : ℝ, Sat cs (Fin.snoc x t) := by
  constructor
  · -- Completeness.
    intro h
    -- Any `t` respecting every lower and upper bound extends `x` to a solution: the
    -- constraints with zero last coefficient are carried into `elim d cs` untouched.
    have hassemble : ∀ t : ℝ,
        (∀ c ∈ cs, lastCoeff d c < 0 → (if c.strict then bnd c x < t else bnd c x ≤ t)) →
        (∀ c ∈ cs, 0 < lastCoeff d c → (if c.strict then t < bnd c x else t ≤ bnd c x)) →
        Sat cs (Fin.snoc x t) := by
      intro t h1 h2 c hc
      rcases lt_trichotomy (lastCoeff d c) 0 with hlt | heq | hgt
      · exact (sat_snoc_neg hlt x t).mpr (h1 c hc hlt)
      · exact (sat_snoc_zero heq x t).mpr (h c (mem_elim_of_zero hc heq))
      · exact (sat_snoc_pos hgt x t).mpr (h2 c hc hgt)
    set L := cs.filter (fun c => decide (lastCoeff d c < 0)) with hLdef
    set U := cs.filter (fun c => decide (0 < lastCoeff d c)) with hUdef
    have hLmem : ∀ c, c ∈ L ↔ (c ∈ cs ∧ lastCoeff d c < 0) := by
      intro c; rw [hLdef, List.mem_filter]; simp
    have hUmem : ∀ c, c ∈ U ↔ (c ∈ cs ∧ 0 < lastCoeff d c) := by
      intro c; rw [hUdef, List.mem_filter]; simp
    -- Every (lower, upper) pair is separated, strictly if either parent is strict.
    have key : ∀ cl ∈ L, ∀ cu ∈ U,
        (if cl.strict || cu.strict then bnd cl x < bnd cu x else bnd cl x ≤ bnd cu x) := by
      intro cl hcl cu hcu
      obtain ⟨hcls, hlneg⟩ := (hLmem cl).mp hcl
      obtain ⟨hcus, hupos⟩ := (hUmem cu).mp hcu
      exact (combine_sat_iff x hlneg hupos).mp
        (h _ (mem_elim_combine hcls hlneg hcus hupos))
    by_cases hLe : L = []
    · by_cases hUe : U = []
      · -- Neither kind of bound: any `t` will do.
        refine ⟨0, hassemble 0 (fun c hc hlt => ?_) (fun c hc hgt => ?_)⟩
        · exact absurd ((hLmem c).mpr ⟨hc, hlt⟩) (by simp [hLe])
        · exact absurd ((hUmem c).mpr ⟨hc, hgt⟩) (by simp [hUe])
      · -- Upper bounds only: go below the smallest of them.
        obtain ⟨c₁, hc₁U, hc₁min⟩ := exists_min_image (fun c => bnd c x) U hUe
        refine ⟨bnd c₁ x - 1, hassemble _ (fun c hc hlt => ?_) (fun c hc hgt => ?_)⟩
        · exact absurd ((hLmem c).mpr ⟨hc, hlt⟩) (by simp [hLe])
        · have := hc₁min c ((hUmem c).mpr ⟨hc, hgt⟩)
          split_ifs <;> linarith
    · by_cases hUe : U = []
      · -- Lower bounds only: go above the largest of them.
        obtain ⟨c₀, hc₀L, hc₀max⟩ := exists_max_image (fun c => bnd c x) L hLe
        refine ⟨bnd c₀ x + 1, hassemble _ (fun c hc hlt => ?_) (fun c hc hgt => ?_)⟩
        · have := hc₀max c ((hLmem c).mpr ⟨hc, hlt⟩)
          split_ifs <;> linarith
        · exact absurd ((hUmem c).mpr ⟨hc, hgt⟩) (by simp [hUe])
      · -- Both kinds present.  Take the largest lower bound and the smallest upper bound.
        obtain ⟨c₀, hc₀L, hc₀max⟩ := exists_max_image (fun c => bnd c x) L hLe
        obtain ⟨c₁, hc₁U, hc₁min⟩ := exists_min_image (fun c => bnd c x) U hUe
        by_cases hgap : bnd c₀ x < bnd c₁ x
        · -- A gap: the midpoint clears every bound strictly.
          refine ⟨(bnd c₀ x + bnd c₁ x) / 2,
            hassemble _ (fun c hc hlt => ?_) (fun c hc hgt => ?_)⟩
          · have := hc₀max c ((hLmem c).mpr ⟨hc, hlt⟩)
            split_ifs <;> linarith
          · have := hc₁min c ((hUmem c).mpr ⟨hc, hgt⟩)
            split_ifs <;> linarith
        · -- No gap.  Then the two extremes coincide, the witness is that common value,
          -- and no strict bound can be sitting on it — pairing such a bound with the
          -- extreme on the other side would have forced a gap.
          rw [not_lt] at hgap
          have hle : bnd c₀ x ≤ bnd c₁ x := by
            have := key c₀ hc₀L c₁ hc₁U
            split_ifs at this <;> linarith
          have heq : bnd c₀ x = bnd c₁ x := le_antisymm hle hgap
          refine ⟨bnd c₀ x, hassemble _ (fun c hc hlt => ?_) (fun c hc hgt => ?_)⟩
          · have hcL : c ∈ L := (hLmem c).mpr ⟨hc, hlt⟩
            have hmax := hc₀max c hcL
            by_cases hs : c.strict = true
            · rw [if_pos hs]
              have hk := key c hcL c₁ hc₁U
              rw [if_pos (by simp [hs])] at hk
              linarith
            · rw [if_neg hs]; exact hmax
          · have hcU : c ∈ U := (hUmem c).mpr ⟨hc, hgt⟩
            have hmin := hc₁min c hcU
            by_cases hs : c.strict = true
            · rw [if_pos hs]
              have hk := key c₀ hc₀L c hcU
              rw [if_pos (by simp [hs])] at hk
              linarith
            · rw [if_neg hs]; linarith
  · -- Soundness.
    rintro ⟨t, ht⟩ c hc
    rcases elim_cases hc with ⟨hcs, h0⟩ | ⟨cl, hcl, cu, hcu, hl, hu, rfl⟩
    · exact (sat_snoc_zero h0 x t).mp (ht c hcs)
    · have h1 := (sat_snoc_neg hl x t).mp (ht cl hcl)
      have h2 := (sat_snoc_pos hu x t).mp (ht cu hcu)
      have h1' : bnd cl x ≤ t := by split_ifs at h1 <;> linarith
      have h2' : t ≤ bnd cu x := by split_ifs at h2 <;> linarith
      refine (combine_sat_iff x hl hu).mpr ?_
      by_cases hor : (cl.strict || cu.strict) = true
      · rw [if_pos hor]
        rcases Bool.or_eq_true _ _ |>.mp hor with hs | hs
        · rw [if_pos hs] at h1; linarith
        · rw [if_pos hs] at h2; linarith
      · rw [if_neg hor]; linarith

/-! ## The decision procedure -/

private lemma feasible_zero_iff (cs : List LinCon) (x : Fin 0 → ℝ) :
    feasible 0 cs = true ↔ Sat cs x := by
  have hpt : ∀ c : LinCon, c.Sat x ↔
      (cond c.strict (decide ((0 : ℚ) < c.const)) (decide ((0 : ℚ) ≤ c.const)) = true) := by
    intro c
    have he : c.eval x = 0 := by unfold LinCon.eval; simp
    unfold LinCon.Sat
    rw [he]
    cases c.strict
    · simp only [Bool.false_eq_true, if_false, cond_false, decide_eq_true_eq]
      exact_mod_cast Iff.rfl
    · simp only [if_true, cond_true, decide_eq_true_eq]
      exact_mod_cast Iff.rfl
  simp only [feasible, List.all_eq_true]
  exact ⟨fun h c hcm => (hpt c).mpr (h c hcm), fun h c hcm => (hpt c).mp (h c hcm)⟩

/-- **The decision procedure is correct.**  `feasible d cs` is `true` exactly when the
system has a real solution. -/
theorem feasible_iff : ∀ (d : ℕ) (cs : List LinCon),
    feasible d cs = true ↔ ∃ x : Fin d → ℝ, Sat cs x
  | 0, cs => by
      constructor
      · intro h; exact ⟨fun i => i.elim0, (feasible_zero_iff cs _).mp h⟩
      · rintro ⟨x, hx⟩; exact (feasible_zero_iff cs x).mpr hx
  | d + 1, cs => by
      rw [show feasible (d + 1) cs = feasible d (elim d cs) from rfl,
        feasible_iff d (elim d cs)]
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨t, ht⟩ := (elim_sat_iff cs x).mp hx
        exact ⟨Fin.snoc x t, ht⟩
      · rintro ⟨y, hy⟩
        refine ⟨Fin.init y, (elim_sat_iff cs (Fin.init y)).mpr ⟨y (Fin.last d), ?_⟩⟩
        rwa [Fin.snoc_init_self]

/-! ## Primitive recursion

At each fixed dimension the recursion on `d` unrolls into a finite composition, so the
certificate is an induction on `d` over primitive recursive list plumbing. -/

private lemma coeffs_primrec : Primrec LinCon.coeffs := Primrec.fst

private lemma const_primrec : Primrec LinCon.const := Primrec.fst.comp Primrec.snd

private lemma strict_primrec : Primrec LinCon.strict := Primrec.snd.comp Primrec.snd

private lemma ratSub_primrec : Primrec₂ fun q r : ℚ => q - r := by
  have h : Primrec fun z : ℚ × ℚ => z.1 + (-1 : ℚ) * z.2 :=
    ratAdd_prim.comp Primrec.fst (ratMul_prim.comp (Primrec.const (-1)) Primrec.snd)
  exact h.to₂.of_eq fun q r => by ring

/-- `List.all` is a `foldr`, which is the shape `Primrec.list_foldr` provides. -/
private lemma all_eq_foldr {α : Type*} (p : α → Bool) :
    ∀ l : List α, l.foldr (fun a b => p a && b) true = l.all p
  | [] => rfl
  | a :: t => by simp [List.all_cons, all_eq_foldr p t]

/-- `ratLE_prim` restated with the `decide` made explicit, so that it composes as an
ordinary `Bool`-valued primitive recursive function rather than as a `PrimrecPred`. -/
private lemma ratLeDec_prim : Primrec₂ fun q r : ℚ => decide (q ≤ r) :=
  PrimrecRel.decide ratLE_prim

private lemma ratLtDec_prim : Primrec₂ fun q r : ℚ => decide (q < r) := by
  have h : Primrec fun z : ℚ × ℚ => !decide (z.2 ≤ z.1) :=
    Primrec.not.comp (ratLeDec_prim.comp Primrec.snd Primrec.fst)
  exact h.to₂.of_eq fun q r => by
    by_cases hqr : q < r
    · simp [hqr, not_le.mpr hqr]
    · simp [hqr, not_lt.mp hqr]

private lemma ratEqDec_prim : Primrec₂ fun q r : ℚ => decide (q = r) :=
  PrimrecRel.decide Primrec.eq

/-- `Primrec.listFilter` takes a predicate fixed once and for all, which is no use once the
dimension is an argument: the sign test the elimination filters on depends on it.  This is
the parametrised form, routed through `Primrec.listFilterMap`, which is already
parametrised. -/
private lemma list_filter_primrec {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).filter (g a) := by
  have h : Primrec fun a => (f a).filterMap fun b => bif g a b then some b else none :=
    Primrec.listFilterMap hf
      (Primrec.cond hg (Primrec.option_some.comp Primrec.snd) (Primrec.const none))
  refine h.of_eq fun a => ?_
  generalize f a = l
  induction l with
  | nil => rfl
  | cons b t ih => cases hb : g a b <;> simp [hb, ih]

/-! ### Uniform in the dimension

Everything below takes the dimension as an *argument* rather than fixing it.  This is the
form the downstream compiler needs: it works at an ambient dimension read off its own
inputs, so a family `∀ d, Primrec (feasible d)` cannot be applied there. -/

private lemma lastCoeff_primrec₂ : Primrec₂ fun (d : ℕ) (c : LinCon) => lastCoeff d c :=
  (Primrec.list_getD (0 : ℚ)).comp (coeffs_primrec.comp Primrec.snd) Primrec.fst

private lemma comboCoeffs_primrec₂ :
    Primrec fun z : ℕ × LinCon × LinCon =>
      comboCoeffs z.1 (lastCoeff z.1 z.2.2) (lastCoeff z.1 z.2.1) z.2.1.coeffs z.2.2.coeffs := by
  -- Projections out of `((d, cl, cu), i)`.
  have hd : Primrec fun w : (ℕ × LinCon × LinCon) × ℕ => w.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hcl : Primrec fun w : (ℕ × LinCon × LinCon) × ℕ => w.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hcu : Primrec fun w : (ℕ × LinCon × LinCon) × ℕ => w.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hstep : Primrec₂ fun (z : ℕ × LinCon × LinCon) (i : ℕ) =>
      lastCoeff z.1 z.2.2 * z.2.1.coeffs.getD i 0
        - lastCoeff z.1 z.2.1 * z.2.2.coeffs.getD i 0 :=
    ratSub_primrec.comp
      (ratMul_prim.comp (lastCoeff_primrec₂.comp hd hcu)
        ((Primrec.list_getD (0 : ℚ)).comp (coeffs_primrec.comp hcl) Primrec.snd))
      (ratMul_prim.comp (lastCoeff_primrec₂.comp hd hcl)
        ((Primrec.list_getD (0 : ℚ)).comp (coeffs_primrec.comp hcu) Primrec.snd))
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst) hstep

private lemma combine_primrec₂ :
    Primrec fun z : ℕ × LinCon × LinCon => combine z.1 z.2.1 z.2.2 := by
  have hd : Primrec fun z : ℕ × LinCon × LinCon => z.1 := Primrec.fst
  have hcl : Primrec fun z : ℕ × LinCon × LinCon => z.2.1 := Primrec.fst.comp Primrec.snd
  have hcu : Primrec fun z : ℕ × LinCon × LinCon => z.2.2 := Primrec.snd.comp Primrec.snd
  have hconst : Primrec fun z : ℕ × LinCon × LinCon =>
      lastCoeff z.1 z.2.2 * z.2.1.const - lastCoeff z.1 z.2.1 * z.2.2.const :=
    ratSub_primrec.comp
      (ratMul_prim.comp (lastCoeff_primrec₂.comp hd hcu) (const_primrec.comp hcl))
      (ratMul_prim.comp (lastCoeff_primrec₂.comp hd hcl) (const_primrec.comp hcu))
  have hstrict : Primrec fun z : ℕ × LinCon × LinCon => (z.2.1.strict || z.2.2.strict) :=
    Primrec.or.comp (strict_primrec.comp hcl) (strict_primrec.comp hcu)
  exact comboCoeffs_primrec₂.pair (hconst.pair hstrict)

/-- **The elimination step is primitive recursive uniformly in the dimension.** -/
theorem elim_primrec₂ : Primrec₂ fun (d : ℕ) (cs : List LinCon) => elim d cs := by
  -- The sign tests, as `Bool`-valued functions of `((d, cs), c)`.
  have hlast : Primrec fun w : (ℕ × List LinCon) × LinCon => lastCoeff w.1.1 w.2 :=
    lastCoeff_primrec₂.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hzeroB : Primrec₂ fun (z : ℕ × List LinCon) (c : LinCon) =>
      decide (lastCoeff z.1 c = 0) := ratEqDec_prim.comp hlast (Primrec.const 0)
  have hnegB : Primrec₂ fun (z : ℕ × List LinCon) (c : LinCon) =>
      decide (lastCoeff z.1 c < 0) := ratLtDec_prim.comp hlast (Primrec.const 0)
  have hposB : Primrec₂ fun (z : ℕ × List LinCon) (c : LinCon) =>
      decide (0 < lastCoeff z.1 c) := ratLtDec_prim.comp (Primrec.const 0) hlast
  have hZ := list_filter_primrec (Primrec.snd (α := ℕ) (β := List LinCon)) hzeroB
  have hL := list_filter_primrec (Primrec.snd (α := ℕ) (β := List LinCon)) hnegB
  have hU := list_filter_primrec (Primrec.snd (α := ℕ) (β := List LinCon)) hposB
  have hinner : Primrec₂ fun (z : ℕ × List LinCon) (cl : LinCon) =>
      (z.2.filter fun c => decide (0 < lastCoeff z.1 c)).map fun cu => combine z.1 cl cu :=
    Primrec.list_map (hU.comp Primrec.fst)
      (combine_primrec₂.comp
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  exact Primrec.list_append.comp hZ (Primrec.list_flatMap hL hinner)

/-! ### The descent as an iteration of one map

`feasible d cs = base (elim 0 (elim 1 (⋯ (elim (d-1) cs))))`: the eliminated dimension
*counts down* as the recursion descends, so this is not an iteration of a single function
of the constraint list alone.  Carrying the pair `(current dimension, current system)` as
the state fixes that — `elimStep` decrements and eliminates in one move, and then the whole
descent is `elimStep^[d]` applied to `(d, cs)`, which `Primrec.nat_iterate` handles. -/

/-- The dimension-zero verdict, named so the unrolling below can refer to it. -/
private def baseVerdict (cs : List LinCon) : Bool :=
  cs.all fun c => cond c.strict (decide (0 < c.const)) (decide (0 ≤ c.const))

/-- One step of the descent, on the state `(current dimension, current system)`. -/
private def elimStep (s : ℕ × List LinCon) : ℕ × List LinCon := (s.1 - 1, elim (s.1 - 1) s.2)

private lemma baseVerdict_primrec : Primrec baseVerdict := by
  have hstep : Primrec fun c : LinCon =>
      cond c.strict (decide ((0 : ℚ) < c.const)) (decide ((0 : ℚ) ≤ c.const)) :=
    Primrec.cond strict_primrec
      (ratLtDec_prim.comp (Primrec.const 0) const_primrec)
      (ratLeDec_prim.comp (Primrec.const 0) const_primrec)
  have hfold : Primrec fun cs : List LinCon => cs.foldr
      (fun c b =>
        cond c.strict (decide ((0 : ℚ) < c.const)) (decide ((0 : ℚ) ≤ c.const)) && b) true :=
    Primrec.list_foldr Primrec.id (Primrec.const true)
      (Primrec.and.comp (hstep.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
  exact hfold.of_eq fun cs => all_eq_foldr _ cs

private lemma elimStep_primrec : Primrec elimStep := by
  have hpred : Primrec fun s : ℕ × List LinCon => s.1 - 1 :=
    Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)
  exact hpred.pair (elim_primrec₂.comp hpred Primrec.snd)

/-- The descent, unrolled: `feasible` is `elimStep` iterated `d` times from the state
`(d, cs)`, read out by the dimension-zero verdict. -/
private lemma feasible_eq_iterate : ∀ (d : ℕ) (cs : List LinCon),
    feasible d cs = baseVerdict (elimStep^[d] (d, cs)).2
  | 0, _ => rfl
  | d + 1, cs => by
      have h1 : feasible (d + 1) cs = feasible d (elim d cs) := rfl
      have h2 : elimStep (d + 1, cs) = (d, elim d cs) := by simp [elimStep]
      rw [h1, feasible_eq_iterate d (elim d cs), Function.iterate_succ_apply, h2]

/-- **The decision procedure is primitive recursive uniformly in the dimension.**  This is
the form a caller whose ambient dimension is computed from its own arguments can use. -/
theorem feasible_primrec₂ : Primrec₂ fun (d : ℕ) (cs : List LinCon) => feasible d cs := by
  have hiter : Primrec fun z : ℕ × List LinCon => elimStep^[z.1] z :=
    Primrec.nat_iterate Primrec.fst Primrec.id (elimStep_primrec.comp Primrec.snd)
  refine (baseVerdict_primrec.comp (Primrec.snd.comp hiter)).of_eq fun z => ?_
  obtain ⟨d, cs⟩ := z
  exact (feasible_eq_iterate d cs).symm

/-- **The decision procedure is primitive recursive** at each fixed dimension.  A
specialisation of `feasible_primrec₂`, kept as a separate statement because it is the form
most call sites want. -/
theorem feasible_primrec : ∀ d : ℕ, Primrec fun cs : List LinCon => feasible d cs :=
  fun d => feasible_primrec₂.comp (Primrec.const d) Primrec.id

/-- The form a caller actually applies: **both** the dimension and the system are computed
from the caller's own argument.  A caller whose ambient dimension is, say,
`dim a = frag a + verts a + 1` supplies a `Primrec dim` built from its own projections and
gets the certificate at that dimension — which is precisely what a family indexed by a
fixed `d` cannot provide. -/
theorem feasible_primrec_comp {α : Type*} [Primcodable α] {dim : α → ℕ}
    {sys : α → List LinCon} (hdim : Primrec dim) (hsys : Primrec sys) :
    Primrec fun a => feasible (dim a) (sys a) :=
  feasible_primrec₂.comp hdim hsys

/-! ## Witnesses

Small systems run through `feasible`.  The third and fourth pair the same coefficients
with different strictness flags, which is what shows that `<` has not been quietly
identified with `≤`. -/

section Witnesses

/-- `x ≤ 0 ∧ x ≥ 1` in one variable — infeasible. -/
def wInfeasible : List LinCon := [LinCon.of [1] 0 false, LinCon.of [-1] (-1) false]

/-- `0 ≤ x ≤ 1` in one variable — feasible. -/
def wFeasible : List LinCon := [LinCon.of [1] 1 false, LinCon.of [-1] 0 false]

/-- `x ≤ 0 ∧ x ≥ 0` — feasible, uniquely at `x = 0`. -/
def wClosed : List LinCon := [LinCon.of [1] 0 false, LinCon.of [-1] 0 false]

/-- `x < 0 ∧ x ≥ 0` — the same system with the upper bound made strict, now infeasible. -/
def wOpen : List LinCon := [LinCon.of [1] 0 true, LinCon.of [-1] 0 false]

/-- `x + y ≤ 1 ∧ x ≥ 0 ∧ y ≥ 0` in two variables — feasible; eliminating `y` produces a
genuine combination `x - 1 ≤ 0` from the first and third constraints. -/
def wTwoSat : List LinCon :=
  [LinCon.of [1, 1] 1 false, LinCon.of [-1, 0] 0 false, LinCon.of [0, -1] 0 false]

/-- `x + y ≤ 0 ∧ x ≥ 1 ∧ y ≥ 1` in two variables — infeasible, and only the combination
of the first and third constraints reveals it. -/
def wTwoUnsat : List LinCon :=
  [LinCon.of [1, 1] 0 false, LinCon.of [-1, 0] (-1) false, LinCon.of [0, -1] (-1) false]

/-- `x = 1 ∧ x ≤ 0`, with the equality encoded as two non-strict inequalities —
infeasible, and the demonstration of the encoding advertised in the header. -/
def wEqUnsat : List LinCon :=
  [LinCon.of [1] 1 false, LinCon.of [-1] (-1) false, LinCon.of [1] 0 false]

#eval feasible 1 wInfeasible   -- false
#eval feasible 1 wFeasible     -- true
#eval feasible 1 wClosed       -- true
#eval feasible 1 wOpen         -- false
#eval feasible 2 wTwoSat       -- true
#eval feasible 2 wTwoUnsat     -- false
#eval feasible 1 wEqUnsat      -- false

/-! `decide` is unavailable on these: rational arithmetic runs through `Nat.gcd`, which the
kernel will not reduce.  The `#eval` results above are the computational check; the two
theorems below are the kernel-checked ones, and they run in the other direction — the
solution set is settled by hand and `feasible_iff` then *pins the Boolean*.  Together they
are the record that `<` has not been identified with `≤`: same coefficients, same
constants, opposite verdicts. -/

/-- `x ≤ 0 ∧ x ≥ 0` has a real solution. -/
theorem wClosed_sat : ∃ x : Fin 1 → ℝ, Sat wClosed x := by
  refine ⟨fun _ => 0, ?_⟩
  intro c hc
  simp only [wClosed, LinCon.of, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp [LinCon.Sat, LinCon.eval]

/-- Making the upper bound strict destroys every real solution. -/
theorem wOpen_unsat : ¬ ∃ x : Fin 1 → ℝ, Sat wOpen x := by
  rintro ⟨x, hx⟩
  have h1 := hx (LinCon.of [1] 0 true) (by simp [wOpen])
  have h2 := hx (LinCon.of [-1] 0 false) (by simp [wOpen])
  simp [LinCon.Sat, LinCon.eval, LinCon.of, LinCon.coeffs, LinCon.const, LinCon.strict] at h1 h2
  linarith

theorem feasible_wClosed : feasible 1 wClosed = true :=
  (feasible_iff 1 wClosed).mpr wClosed_sat

theorem feasible_wOpen : feasible 1 wOpen = false :=
  Bool.not_eq_true _ |>.mp fun h => wOpen_unsat ((feasible_iff 1 wOpen).mp h)

end Witnesses

end Workspace.Normativity.Contrib.FourierMotzkin

#print axioms Workspace.Normativity.Contrib.FourierMotzkin.feasible
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.elim
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.combine
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.elim_sat_iff
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.feasible_iff
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.elim_primrec₂
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.feasible_primrec₂
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.feasible_primrec
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.feasible_primrec_comp
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.wClosed_sat
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.wOpen_unsat
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.feasible_wClosed
#print axioms Workspace.Normativity.Contrib.FourierMotzkin.feasible_wOpen
