/-
# Generating the projector's max–min representation, as a `def`

`ProjectionBridge.exists_rep_repEval` says that each coordinate of the Euclidean projector
onto a rational polytope *is* the `repEval` of some representation the compiler accepts.
It is an existence statement and cannot be anything else, because the family it rests on —
`MaxMinRepresentation.exists_maxMin_representation` — is indexed by
`Finset.univ.filter (fun T => ∃ y ∈ Γ, up y = T)`, an existential over an infinite domain.
Nothing primitive recursive evaluates that.  This file produces the same representation as
a **`def`**, together with the theorem that the `def` is correct.

## What has to be computed

`MaxMinRepresentation.maxMin_of_family` takes the index family as an argument and asks two
things of it: each `S j` *contains* the upper set of some point of the domain (`hsound`),
and each point's upper set *contains* some `S j` (`hcomplete`).  Writing
`up x = {i | f x ≤ g i x}` for the components `g` of the piecewise-affine reading, both
conditions are met by the family of *realised upper sets* — the sets `up y` for `y` ranging
over the domain.  So the whole problem is: decide, for a finite candidate set `T` of
component indices, whether some point realises it.

## Why that is a linear-feasibility question, and how the quadratic terms go away

Fix the polytope `K` by its vertices `v₁ … v_m` and the coordinate `k`.  A point `x`
realises `T` when, writing `q = K.proj x`,

* `q` is a convex combination `q = Σ_j λ_j v_j` of the vertices, and
* `q` satisfies the vertex certificate `⟪x − q, v_i − q⟫ ≤ 0` of
  `RationalPolytope.eq_proj_of_vertexSet` — with *equality* at every vertex carrying
  positive weight, which is what the weights being a genuine minimiser forces — and
* `T` is exactly `{i | q_k ≤ g_i(x)}`.

Read naively this is quadratic: `⟪x − q, v_i − q⟫` multiplies two affine functions of the
unknowns `x` and `λ`.  Introducing the weights `λ` **together with** one auxiliary scalar

    c := ⟪x − q, q⟫

removes both quadratic terms at once, because `⟪x − q, v_i − q⟫ = ⟪x, v_i⟫ − ⟪q, v_i⟫ − c`
and `⟪q, v_i⟫ = Σ_j λ_j ⟪v_j, v_i⟫` is linear in `λ` with *rational constant*
coefficients `G_{ji} = ⟪v_j, v_i⟫`.  Every constraint below is then linear in `(x, λ, c)`,
which is a system `FourierMotzkin.feasible` decides, with `feasible_iff` supplying both
directions.

**`c` is a free variable, not an assumption.**  The system never says `c = ⟪x − q, q⟫`; it
says the residuals `⟪x, v_i⟫ − Σ_j λ_j G_{ji} − c` are `≤ 0` throughout and `= 0` on the
support.  Summing the support's equalities against `λ` — using `Σ_j λ_j = 1` and `λ_j = 0`
off the support — yields `⟪x, q⟫ − ⟪q, q⟫ − c = 0`, so `c` is forced to `⟪x − q, q⟫` and the
relaxation is exact.  That is `cOf_eq_of_holds` below, and it is the step the whole
construction turns on.

**Strict inequalities are load-bearing.**  `λ_j > 0` on the support is what distinguishes a
support from a face containing it, and `g_i(x) < q_k` off `T` is what makes `T` the upper
set rather than merely a subset of it.  `FourierMotzkin` tracks strictness through the
elimination, and the two are never identified here.  Equalities are encoded as two
non-strict constraints, which is the encoding that file documents.

**No active-face index appears.**  With `λ` in the system the projector's own value at `x`
is `Σ_j λ_j (v_j)_k`, already linear, so the system never has to name the piece that is
active at `x`.  `Face.piece` enters only as the list of *components* `g_i`; `Regular`,
`gramInvQ` and `candidate_eq_proj_of_mem_cell` do not enter at all.

## The cost

`projectorFamily` enumerates every pair of a support `S ⊆ {1 … m}` and an upper set
`T ⊆ {1 … N}`, where `N = |faceList K|` is itself `m · 2 ^ m`.  That is `2 ^ m · 2 ^ N`
feasibility tests, each a Fourier–Motzkin elimination — doubly exponential in the number of
vertices.  This is stated, not hidden: the claim being made is computability, and nothing
here is an efficiency claim.

## What is deliberately not done here

No `Primrec` certificate.  `FourierMotzkin.feasible_primrec` fixes the dimension; the
uniform `Primrec₂` version this file's `def`s would need is being proved elsewhere.  The
definitions are nonetheless written to keep that proof plausible — positional
`List.range` / `List.sublists` / `List.getD` plumbing throughout, `List.finRange` rather
than `Finset.toList` over a `Fintype`, and no proof arguments in the data path (which is
why `groupOfList` and `repOfList` are total, where `ProjectionBridge.groupOf` and `repOf`
take a nonemptiness proof).

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ProjectionBridge
import Workspace.Normativity.Contrib.FourierMotzkin

namespace Workspace.Normativity.Contrib.ProjectorGenerator

open scoped RealInnerProductSpace
open LogicalInduction (Sentence)
open Workspace.Normativity.Contrib.RationalPolytope (Pt toPt)
open Workspace.Normativity.Contrib.ProjectionCompiler (Fragment groupEval repEval)
open Workspace.Normativity.Contrib.ProjectionBridge (restrict ofGeom groupOf repOf)

open Workspace.Normativity.Contrib.FourierMotzkin

variable {d m : ℕ}

/-! ## The ambient layout

The unknowns are `(x, λ, c) ∈ ℝ^{d+m+1}`: the point being projected, the barycentric
weights of its projection, and the auxiliary scalar.  They are laid out positionally, so
that a coefficient list is a `List.ofFn` over the single index type `Fin (d + m + 1)` and
`FourierMotzkin`'s `getD` lookup is `List.getElem_ofFn`. -/

/-- The position of the `a`-th coordinate of the point. -/
def embX (d m : ℕ) (a : Fin d) : Fin (d + m + 1) := ⟨a.1, by have := a.2; omega⟩

/-- The position of the `j`-th barycentric weight. -/
def embL (d m : ℕ) (j : Fin m) : Fin (d + m + 1) := ⟨d + j.1, by have := j.2; omega⟩

/-- The position of the auxiliary scalar `c`. -/
def embC (d m : ℕ) : Fin (d + m + 1) := ⟨d + m, by omega⟩

/-- A sum over the ambient index splits into the three blocks. -/
theorem sum_split (d m : ℕ) (f : Fin (d + m + 1) → ℝ) :
    ∑ t, f t = (∑ a : Fin d, f (embX d m a)) + (∑ j : Fin m, f (embL d m j)) + f (embC d m) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_add]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun a _ => congrArg f (Fin.ext (by simp [embX]))
  · exact Finset.sum_congr rfl fun j _ => congrArg f (Fin.ext (by simp [embL]))
  · exact congrArg f (Fin.ext (by simp [embC]))

/-- The coefficient of the ambient variable at each position, from the three blocks. -/
def coeffFn (d m : ℕ) (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc : ℚ) : Fin (d + m + 1) → ℚ :=
  fun t =>
    if h : (t : ℕ) < d then xf ⟨t, h⟩
    else if h' : (t : ℕ) < d + m then lf ⟨(t : ℕ) - d, by omega⟩ else cc

@[simp] theorem coeffFn_embX (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc : ℚ) (a : Fin d) :
    coeffFn d m xf lf cc (embX d m a) = xf a := by
  have h : ((embX d m a : Fin (d + m + 1)) : ℕ) < d := by simp [embX]
  rw [coeffFn, dif_pos h]
  exact congrArg xf (Fin.ext rfl)

@[simp] theorem coeffFn_embL (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc : ℚ) (j : Fin m) :
    coeffFn d m xf lf cc (embL d m j) = lf j := by
  have hj := j.2
  have h1 : ¬ ((embL d m j : Fin (d + m + 1)) : ℕ) < d := by simp [embL]
  have h2 : ((embL d m j : Fin (d + m + 1)) : ℕ) < d + m := by simp [embL]
  rw [coeffFn, dif_neg h1, dif_pos h2]
  congr 1
  exact Fin.ext (by simp [embL])

@[simp] theorem coeffFn_embC (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc : ℚ) :
    coeffFn d m xf lf cc (embC d m) = cc := by
  have h1 : ¬ ((embC d m : Fin (d + m + 1)) : ℕ) < d := by simp [embC]
  have h2 : ¬ ((embC d m : Fin (d + m + 1)) : ℕ) < d + m := by simp [embC]
  rw [coeffFn, dif_neg h1, dif_neg h2]

/-- A constraint of the ambient system, from its three coefficient blocks. -/
def mkCon (d m : ℕ) (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc b : ℚ) (s : Bool) : LinCon :=
  LinCon.of (List.ofFn (coeffFn d m xf lf cc)) b s

/-- **The constraint evaluates blockwise.**  This is the only place the positional layout
is spent; everything downstream reads the three sums. -/
theorem eval_mkCon (d m : ℕ) (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc b : ℚ) (s : Bool)
    (z : Fin (d + m + 1) → ℝ) :
    LinCon.eval (mkCon d m xf lf cc b s) z
      = (∑ a : Fin d, ((xf a : ℚ) : ℝ) * z (embX d m a))
        + (∑ j : Fin m, ((lf j : ℚ) : ℝ) * z (embL d m j))
        + ((cc : ℚ) : ℝ) * z (embC d m) := by
  have hco : ∀ t : Fin (d + m + 1),
      ((mkCon d m xf lf cc b s).coeffs.getD (t : ℕ) 0) = coeffFn d m xf lf cc t := by
    intro t
    show (List.ofFn (coeffFn d m xf lf cc)).getD (t : ℕ) 0 = _
    rw [List.getD_eq_getElem _ _ (by simpa using t.isLt), List.getElem_ofFn]
  rw [LinCon.eval]
  simp only [hco]
  rw [sum_split d m fun t => ((coeffFn d m xf lf cc t : ℚ) : ℝ) * z t]
  simp

/-- Satisfaction of a non-strict constraint of the ambient system. -/
theorem sat_mkCon_le (d m : ℕ) (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc b : ℚ)
    (z : Fin (d + m + 1) → ℝ) :
    LinCon.Sat (mkCon d m xf lf cc b false) z
      ↔ (∑ a : Fin d, ((xf a : ℚ) : ℝ) * z (embX d m a))
        + (∑ j : Fin m, ((lf j : ℚ) : ℝ) * z (embL d m j))
        + ((cc : ℚ) : ℝ) * z (embC d m) ≤ (b : ℝ) := by
  have h : LinCon.Sat (mkCon d m xf lf cc b false) z
      ↔ LinCon.eval (mkCon d m xf lf cc b false) z ≤ (b : ℝ) := Iff.rfl
  rw [h, eval_mkCon]

/-- Satisfaction of a strict constraint of the ambient system. -/
theorem sat_mkCon_lt (d m : ℕ) (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc b : ℚ)
    (z : Fin (d + m + 1) → ℝ) :
    LinCon.Sat (mkCon d m xf lf cc b true) z
      ↔ (∑ a : Fin d, ((xf a : ℚ) : ℝ) * z (embX d m a))
        + (∑ j : Fin m, ((lf j : ℚ) : ℝ) * z (embL d m j))
        + ((cc : ℚ) : ℝ) * z (embC d m) < (b : ℝ) := by
  have h : LinCon.Sat (mkCon d m xf lf cc b true) z
      ↔ LinCon.eval (mkCon d m xf lf cc b true) z < (b : ℝ) := Iff.rfl
  rw [h, eval_mkCon]

/-- A weight block that names one weight. -/
theorem sum_ite_lam (d m : ℕ) (j : Fin m) (r : ℚ) (z : Fin (d + m + 1) → ℝ) :
    (∑ j' : Fin m, (((if j' = j then r else 0 : ℚ)) : ℝ) * z (embL d m j'))
      = (r : ℝ) * z (embL d m j) := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## The polytope's data, positionally

`nv K` vertices and `nf K` enumerated faces.  `comp K k i` is literally the component
`ProjectionBridge` uses — the `k`-th coordinate of the `i`-th enumerated face's rational
piece — so the two developments index the same family. -/

/-- The number of vertices. -/
abbrev nv (K : RationalPolytope d) : ℕ := K.verts.length

/-- The number of enumerated faces, that is, of affine components. -/
abbrev nf (K : RationalPolytope d) : ℕ := (PolyhedralCoverage.faceList K).length

/-- The `j`-th vertex. -/
def vtx (K : RationalPolytope d) (j : Fin (nv K)) : Fin d → ℚ := K.verts.get j

/-- The Gram constant `⟪v_j, v_i⟫`, a rational number. -/
def gram (K : RationalPolytope d) (j i : Fin (nv K)) : ℚ := ∑ a, vtx K j a * vtx K i a

/-- The `i`-th affine component of the `k`-th coordinate of the projector. -/
def comp (K : RationalPolytope d) (k : Fin d) (i : Fin (nf K)) :
    PolyhedralProjection.AffineForm d :=
  ((PolyhedralCoverage.faceList K).get i).piece k

theorem vtx_mem (K : RationalPolytope d) (j : Fin (nv K)) : vtx K j ∈ K.verts :=
  List.get_mem _ _

/-- Every vertex of the region is one of the listed ones. -/
theorem exists_vtx_of_mem_vertexSet (K : RationalPolytope d) {v : Pt d}
    (hv : v ∈ K.vertexSet) : ∃ j : Fin (nv K), toPt (vtx K j) = v := by
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hu
  exact ⟨j, by rw [vtx, hj]⟩

/-! ## The system

Six blocks.  The two `Σ λ = 1` constraints and the two-sided residual constraints are the
equalities, each written as a pair of non-strict inequalities; the support and upper-set
blocks are where the strict forms live.  Both of those blocks emit one constraint per index
whose *content* depends on membership, rather than filtering the index list: it keeps the
membership reasoning to `List.mem_map` over `List.finRange`. -/

/-- `Σ_j λ_j ≤ 1`. -/
def conSumLe (d m : ℕ) : LinCon := mkCon d m 0 (fun _ => 1) 0 1 false

/-- `−Σ_j λ_j ≤ −1`; with `conSumLe` this is `Σ_j λ_j = 1`. -/
def conSumGe (d m : ℕ) : LinCon := mkCon d m 0 (fun _ => -1) 0 (-1) false

/-- `−λ_j ≤ 0`. -/
def conNonneg (d m : ℕ) (j : Fin m) : LinCon :=
  mkCon d m 0 (fun j' => if j' = j then -1 else 0) 0 0 false

/-- `−λ_j < 0` on the support (strict — this is what makes a support a support), and
`λ_j ≤ 0` off it, which with `conNonneg` pins `λ_j = 0`. -/
def conSupport (d m : ℕ) (S : List ℕ) (j : Fin m) : LinCon :=
  if (j : ℕ) ∈ S then mkCon d m 0 (fun j' => if j' = j then -1 else 0) 0 0 true
  else mkCon d m 0 (fun j' => if j' = j then 1 else 0) 0 0 false

/-- `⟪x, v_i⟫ − Σ_j λ_j G_{ji} − c ≤ 0`. -/
def conVertLe (K : RationalPolytope d) (i : Fin (nv K)) : LinCon :=
  mkCon d (nv K) (vtx K i) (fun j => -gram K j i) (-1) 0 false

/-- The reverse inequality on the support, making the residual vanish there; a trivially
satisfied `0 ≤ 0` off it, so that the block is one constraint per vertex. -/
def conVertGe (K : RationalPolytope d) (S : List ℕ) (i : Fin (nv K)) : LinCon :=
  if (i : ℕ) ∈ S then mkCon d (nv K) (fun a => -vtx K i a) (fun j => gram K j i) 1 0 false
  else mkCon d (nv K) 0 0 0 0 false

/-- `Σ_j λ_j (v_j)_k ≤ g_i(x)` for `i` in the candidate upper set, and the strict reverse
off it. -/
def conUpper (K : RationalPolytope d) (k : Fin d) (T : List ℕ) (i : Fin (nf K)) : LinCon :=
  if (i : ℕ) ∈ T then
    mkCon d (nv K) (fun a => -(comp K k i).coeff a) (fun j => vtx K j k) 0 (comp K k i).const false
  else
    mkCon d (nv K) (fun a => (comp K k i).coeff a) (fun j => -vtx K j k) 0
      (-(comp K k i).const) true

/-- **The system.**  Feasible exactly when some point realises the support `S` and the
upper set `T`. -/
def system (K : RationalPolytope d) (k : Fin d) (S T : List ℕ) : List LinCon :=
  conSumLe d (nv K) :: conSumGe d (nv K) ::
    ((List.finRange (nv K)).map (conNonneg d (nv K)) ++
      (List.finRange (nv K)).map (conSupport d (nv K) S) ++
      (List.finRange (nv K)).map (conVertLe K) ++
      (List.finRange (nv K)).map (conVertGe K S) ++
      (List.finRange (nf K)).map (conUpper K k T))

/-! ## Reading a solution

A solution `z` of the system is read as a point, a weight vector and a scalar. -/

/-- The point a solution encodes. -/
def ptOf (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) : Pt d :=
  WithLp.toLp 2 fun a => z (embX d (nv K) a)

/-- The `j`-th barycentric weight a solution encodes. -/
def lamOf (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) (j : Fin (nv K)) : ℝ :=
  z (embL d (nv K) j)

/-- The auxiliary scalar a solution encodes. -/
def cOf (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) : ℝ := z (embC d (nv K))

theorem ptOf_apply (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) (a : Fin d) :
    ptOf K z a = z (embX d (nv K) a) := rfl

/-- The candidate projection a solution encodes: the convex combination of the vertices. -/
def qOf (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) : Pt d :=
  ∑ j, lamOf K z j • toPt (vtx K j)

/-- A finite sum of points is computed coordinatewise. -/
theorem sum_pt_apply {n : ℕ} (f : Fin n → Pt d) (a : Fin d) :
    (∑ j, f j) a = ∑ j, f j a := by
  show (WithLp.ofLp (∑ j, f j)) a = _
  rw [WithLp.ofLp_sum]
  exact Finset.sum_apply a _ _

theorem qOf_apply (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) (a : Fin d) :
    qOf K z a = ∑ j, lamOf K z j * ((vtx K j a : ℚ) : ℝ) := by
  rw [qOf, sum_pt_apply]
  exact Finset.sum_congr rfl fun j _ => by
    rw [PiLp.smul_apply, smul_eq_mul]
    rfl

/-- The residual of the vertex certificate at the `i`-th vertex, as the system writes it. -/
def resid (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) (i : Fin (nv K)) : ℝ :=
  (∑ a, ((vtx K i a : ℚ) : ℝ) * ptOf K z a)
    - (∑ j, lamOf K z j * ((gram K j i : ℚ) : ℝ)) - cOf K z

/-- The value the system assigns to the projector at the encoded point. -/
def lamVal (K : RationalPolytope d) (k : Fin d) (z : Fin (d + nv K + 1) → ℝ) : ℝ :=
  ∑ j, lamOf K z j * ((vtx K j k : ℚ) : ℝ)

theorem lamVal_eq_qOf (K : RationalPolytope d) (k : Fin d) (z : Fin (d + nv K + 1) → ℝ) :
    lamVal K k z = qOf K z k := (qOf_apply K z k).symm

/-- **What the system says**, as a proposition about the encoded data. -/
def Holds (K : RationalPolytope d) (k : Fin d) (S T : List ℕ)
    (z : Fin (d + nv K + 1) → ℝ) : Prop :=
  (∑ j, lamOf K z j) = 1
    ∧ (∀ j, 0 ≤ lamOf K z j)
    ∧ (∀ j : Fin (nv K), (j : ℕ) ∈ S → 0 < lamOf K z j)
    ∧ (∀ j : Fin (nv K), (j : ℕ) ∉ S → lamOf K z j ≤ 0)
    ∧ (∀ i : Fin (nv K), resid K z i ≤ 0)
    ∧ (∀ i : Fin (nv K), (i : ℕ) ∈ S → 0 ≤ resid K z i)
    ∧ (∀ i : Fin (nf K), (i : ℕ) ∈ T → lamVal K k z ≤ (comp K k i).eval (ptOf K z))
    ∧ (∀ i : Fin (nf K), (i : ℕ) ∉ T → (comp K k i).eval (ptOf K z) < lamVal K k z)

/-! ### The six blocks, read back -/

theorem sat_conSumLe (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) :
    LinCon.Sat (conSumLe d (nv K)) z ↔ (∑ j, lamOf K z j) ≤ 1 := by
  rw [conSumLe, sat_mkCon_le]
  simp [lamOf]

theorem sat_conSumGe (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) :
    LinCon.Sat (conSumGe d (nv K)) z ↔ 1 ≤ (∑ j, lamOf K z j) := by
  rw [conSumGe, sat_mkCon_le]
  simp only [Pi.zero_apply, Rat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add,
    Rat.cast_neg, Rat.cast_one, neg_mul, one_mul, add_zero, Finset.sum_neg_distrib]
  constructor <;> intro h <;> [skip; skip] <;>
    simpa [lamOf, neg_le] using h

theorem sat_conNonneg (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ)
    (j : Fin (nv K)) :
    LinCon.Sat (conNonneg d (nv K) j) z ↔ 0 ≤ lamOf K z j := by
  rw [conNonneg, sat_mkCon_le]
  rw [sum_ite_lam]
  simp [lamOf]

theorem sat_conSupport_mem (K : RationalPolytope d) (S : List ℕ)
    (z : Fin (d + nv K + 1) → ℝ) (j : Fin (nv K)) (hj : (j : ℕ) ∈ S) :
    LinCon.Sat (conSupport d (nv K) S j) z ↔ 0 < lamOf K z j := by
  rw [conSupport, if_pos hj, sat_mkCon_lt, sum_ite_lam]
  simp [lamOf, neg_lt]

theorem sat_conSupport_notMem (K : RationalPolytope d) (S : List ℕ)
    (z : Fin (d + nv K + 1) → ℝ) (j : Fin (nv K)) (hj : (j : ℕ) ∉ S) :
    LinCon.Sat (conSupport d (nv K) S j) z ↔ lamOf K z j ≤ 0 := by
  rw [conSupport, if_neg hj, sat_mkCon_le, sum_ite_lam]
  simp [lamOf]

theorem sat_conVertLe (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ)
    (i : Fin (nv K)) :
    LinCon.Sat (conVertLe K i) z ↔ resid K z i ≤ 0 := by
  rw [conVertLe, sat_mkCon_le]
  have h : (∑ j, ((-gram K j i : ℚ) : ℝ) * z (embL d (nv K) j))
      = -(∑ j, z (embL d (nv K) j) * ((gram K j i : ℚ) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by push_cast; ring
  simp only [resid, lamOf, cOf, ptOf_apply]
  rw [h]
  push_cast
  constructor <;> intro hh <;> linarith

theorem sat_conVertGe_mem (K : RationalPolytope d) (S : List ℕ)
    (z : Fin (d + nv K + 1) → ℝ) (i : Fin (nv K)) (hi : (i : ℕ) ∈ S) :
    LinCon.Sat (conVertGe K S i) z ↔ 0 ≤ resid K z i := by
  rw [conVertGe, if_pos hi, sat_mkCon_le]
  have hx : (∑ a, ((-vtx K i a : ℚ) : ℝ) * z (embX d (nv K) a))
      = -(∑ a, ((vtx K i a : ℚ) : ℝ) * z (embX d (nv K) a)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by push_cast; ring
  have h : (∑ j, ((gram K j i : ℚ) : ℝ) * z (embL d (nv K) j))
      = ∑ j, z (embL d (nv K) j) * ((gram K j i : ℚ) : ℝ) :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [resid, lamOf, cOf, ptOf_apply]
  rw [hx, h]
  push_cast
  constructor <;> intro hh <;> linarith

theorem sat_conVertGe_notMem (K : RationalPolytope d) (S : List ℕ)
    (z : Fin (d + nv K + 1) → ℝ) (i : Fin (nv K)) (hi : (i : ℕ) ∉ S) :
    LinCon.Sat (conVertGe K S i) z := by
  rw [conVertGe, if_neg hi]
  refine (sat_mkCon_le d (nv K) 0 0 0 0 z).mpr ?_
  simp

theorem sat_conUpper_mem (K : RationalPolytope d) (k : Fin d) (T : List ℕ)
    (z : Fin (d + nv K + 1) → ℝ) (i : Fin (nf K)) (hi : (i : ℕ) ∈ T) :
    LinCon.Sat (conUpper K k T i) z
      ↔ lamVal K k z ≤ (comp K k i).eval (ptOf K z) := by
  rw [conUpper, if_pos hi, sat_mkCon_le]
  have hx : (∑ a, ((-(comp K k i).coeff a : ℚ) : ℝ) * z (embX d (nv K) a))
      = -(∑ a, (((comp K k i).coeff a : ℚ) : ℝ) * z (embX d (nv K) a)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by push_cast; ring
  have hl : (∑ j, ((vtx K j k : ℚ) : ℝ) * z (embL d (nv K) j)) = lamVal K k z :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [PolyhedralProjection.AffineForm.eval, ptOf_apply]
  rw [hx, hl]
  push_cast
  constructor <;> intro hh <;> linarith

theorem sat_conUpper_notMem (K : RationalPolytope d) (k : Fin d) (T : List ℕ)
    (z : Fin (d + nv K + 1) → ℝ) (i : Fin (nf K)) (hi : (i : ℕ) ∉ T) :
    LinCon.Sat (conUpper K k T i) z
      ↔ (comp K k i).eval (ptOf K z) < lamVal K k z := by
  rw [conUpper, if_neg hi, sat_mkCon_lt]
  have hl : (∑ j, ((-vtx K j k : ℚ) : ℝ) * z (embL d (nv K) j)) = -lamVal K k z := by
    rw [lamVal, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [lamOf]; push_cast; ring
  simp only [PolyhedralProjection.AffineForm.eval, ptOf_apply]
  rw [hl]
  push_cast
  constructor <;> intro hh <;> linarith

/-- **The system says exactly `Holds`.**  Both directions: the forward one is what
soundness reads off a Fourier–Motzkin witness, the backward one is what completeness feeds
to `feasible_iff`. -/
theorem sat_system_iff (K : RationalPolytope d) (k : Fin d) (S T : List ℕ)
    (z : Fin (d + nv K + 1) → ℝ) :
    Sat (system K k S T) z ↔ Holds K k S T z := by
  constructor
  · intro h
    have hmem : ∀ c ∈ system K k S T, LinCon.Sat c z := h
    have h1 : LinCon.Sat (conSumLe d (nv K)) z := hmem _ (by simp [system])
    have h2 : LinCon.Sat (conSumGe d (nv K)) z := hmem _ (by simp [system])
    have hN : ∀ j : Fin (nv K), LinCon.Sat (conNonneg d (nv K) j) z := fun j =>
      hmem _ (by simp only [system, List.mem_cons, List.mem_append]
                 exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl
                   (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)))))))
    have hSup : ∀ j : Fin (nv K), LinCon.Sat (conSupport d (nv K) S j) z := fun j =>
      hmem _ (by simp only [system, List.mem_cons, List.mem_append]
                 exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr
                   (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)))))))
    have hVL : ∀ i : Fin (nv K), LinCon.Sat (conVertLe K i) z := fun i =>
      hmem _ (by simp only [system, List.mem_cons, List.mem_append]
                 exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr
                   (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))))))
    have hVG : ∀ i : Fin (nv K), LinCon.Sat (conVertGe K S i) z := fun i =>
      hmem _ (by simp only [system, List.mem_cons, List.mem_append]
                 exact Or.inr (Or.inr (Or.inl (Or.inr
                   (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))))
    have hU : ∀ i : Fin (nf K), LinCon.Sat (conUpper K k T i) z := fun i =>
      hmem _ (by simp only [system, List.mem_cons, List.mem_append]
                 exact Or.inr (Or.inr (Or.inr
                   (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))))
    refine ⟨le_antisymm ((sat_conSumLe K z).mp h1) ((sat_conSumGe K z).mp h2),
      fun j => (sat_conNonneg K z j).mp (hN j), fun j hj => ?_, fun j hj => ?_,
      fun i => (sat_conVertLe K z i).mp (hVL i), fun i hi => ?_, fun i hi => ?_,
      fun i hi => ?_⟩
    · exact (sat_conSupport_mem K S z j hj).mp (hSup j)
    · exact (sat_conSupport_notMem K S z j hj).mp (hSup j)
    · exact (sat_conVertGe_mem K S z i hi).mp (hVG i)
    · exact (sat_conUpper_mem K k T z i hi).mp (hU i)
    · exact (sat_conUpper_notMem K k T z i hi).mp (hU i)
  · rintro ⟨hsum, hnn, hpos, hzero, hle, hge, hup, hdown⟩
    intro c hc
    simp only [system, List.mem_cons, List.mem_append, List.mem_map, List.mem_finRange] at hc
    rcases hc with rfl | rfl | ((((hc | hc) | hc) | hc) | hc)
    · exact (sat_conSumLe K z).mpr (le_of_eq hsum)
    · exact (sat_conSumGe K z).mpr (ge_of_eq hsum)
    · obtain ⟨j, _, rfl⟩ := hc
      exact (sat_conNonneg K z j).mpr (hnn j)
    · obtain ⟨j, _, rfl⟩ := hc
      by_cases hj : (j : ℕ) ∈ S
      · exact (sat_conSupport_mem K S z j hj).mpr (hpos j hj)
      · exact (sat_conSupport_notMem K S z j hj).mpr (hzero j hj)
    · obtain ⟨i, _, rfl⟩ := hc
      exact (sat_conVertLe K z i).mpr (hle i)
    · obtain ⟨i, _, rfl⟩ := hc
      by_cases hi : (i : ℕ) ∈ S
      · exact (sat_conVertGe_mem K S z i hi).mpr (hge i hi)
      · exact sat_conVertGe_notMem K S z i hi
    · obtain ⟨i, _, rfl⟩ := hc
      by_cases hi : (i : ℕ) ∈ T
      · exact (sat_conUpper_mem K k T z i hi).mpr (hup i hi)
      · exact (sat_conUpper_notMem K k T z i hi).mpr (hdown i hi)

/-! ## The convex hull, as combinations of the *listed* vertices

The certificate needs weights indexed by the vertex list, duplicates and all, in both
directions: soundness needs a combination to be in the region, completeness needs a point
of the region to have one. -/

/-- Convex combinations of the listed vertices. -/
def combSet (K : RationalPolytope d) : Set (Pt d) :=
  {y | ∃ w : Fin (nv K) → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ y = ∑ j, w j • toPt (vtx K j)}

theorem combSet_convex (K : RationalPolytope d) : Convex ℝ (combSet K) := by
  rintro y₁ ⟨w₁, hw₁, hs₁, rfl⟩ y₂ ⟨w₂, hw₂, hs₂, rfl⟩ a b ha hb hab
  refine ⟨fun j => a * w₁ j + b * w₂ j, fun j => add_nonneg (mul_nonneg ha (hw₁ j))
    (mul_nonneg hb (hw₂ j)), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs₁, hs₂,
      mul_one, mul_one, hab]
  · simp only [Finset.smul_sum, smul_smul, add_smul]
    rw [← Finset.sum_add_distrib]

theorem combSet_subset_carrier (K : RationalPolytope d) : combSet K ⊆ K.carrier := by
  rintro y ⟨w, hw, hs, rfl⟩
  exact K.carrier_convex.sum_mem (fun j _ => hw j) hs
    (fun j _ => K.vertexSet_subset_carrier ⟨vtx K j, vtx_mem K j, rfl⟩)

theorem carrier_subset_combSet (K : RationalPolytope d) : K.carrier ⊆ combSet K := by
  refine convexHull_min ?_ (combSet_convex K)
  intro v hv
  obtain ⟨j, rfl⟩ := exists_vtx_of_mem_vertexSet K hv
  refine ⟨fun j' => if j' = j then 1 else 0, fun j' => by positivity, by simp, ?_⟩
  rw [Finset.sum_eq_single j] <;> simp +contextual

/-! ## Soundness: a feasible pair is realised

The auxiliary scalar is forced first — that is the step that makes the linear relaxation
exact — and then the residuals *are* the vertex certificate. -/

/-- The weighted Gram sum is the projection of the candidate onto the vertex. -/
theorem sum_lam_gram (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ)
    (i : Fin (nv K)) :
    (∑ j, lamOf K z j * ((gram K j i : ℚ) : ℝ)) = ∑ a, qOf K z a * ((vtx K i a : ℚ) : ℝ) := by
  have hcast : ∀ j : Fin (nv K), ((gram K j i : ℚ) : ℝ)
      = ∑ a, ((vtx K j a : ℚ) : ℝ) * ((vtx K i a : ℚ) : ℝ) := by
    intro j; rw [gram]; push_cast; rfl
  calc (∑ j, lamOf K z j * ((gram K j i : ℚ) : ℝ))
      = ∑ j, ∑ a, lamOf K z j * ((vtx K j a : ℚ) : ℝ) * ((vtx K i a : ℚ) : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcast j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a, ∑ j, lamOf K z j * ((vtx K j a : ℚ) : ℝ) * ((vtx K i a : ℚ) : ℝ) :=
        Finset.sum_comm
    _ = ∑ a, qOf K z a * ((vtx K i a : ℚ) : ℝ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [qOf_apply, Finset.sum_mul]

theorem resid_eq (K : RationalPolytope d) (z : Fin (d + nv K + 1) → ℝ) (i : Fin (nv K)) :
    resid K z i
      = (∑ a, ((vtx K i a : ℚ) : ℝ) * (ptOf K z a - qOf K z a)) - cOf K z := by
  rw [resid, sum_lam_gram]
  have : (∑ a, ((vtx K i a : ℚ) : ℝ) * (ptOf K z a - qOf K z a))
      = (∑ a, ((vtx K i a : ℚ) : ℝ) * ptOf K z a)
        - ∑ a, qOf K z a * ((vtx K i a : ℚ) : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this]

/-- **The auxiliary scalar is forced.**  It is a free variable of the system, but summing
the support's residual equations against the weights identifies it with `⟪x − q, q⟫`. -/
theorem cOf_eq_of_holds (K : RationalPolytope d) (k : Fin d) (S T : List ℕ)
    {z : Fin (d + nv K + 1) → ℝ} (h : Holds K k S T z) :
    cOf K z = ∑ a, qOf K z a * (ptOf K z a - qOf K z a) := by
  obtain ⟨hsum, hnn, hpos, hzero, hle, hge, -, -⟩ := h
  have hterm : ∀ j : Fin (nv K), lamOf K z j * resid K z j = 0 := by
    intro j
    by_cases hj : (j : ℕ) ∈ S
    · rw [le_antisymm (hle j) (hge j hj), mul_zero]
    · rw [le_antisymm (hzero j hj) (hnn j), zero_mul]
  have hzero' : (∑ j, lamOf K z j * resid K z j) = 0 :=
    Finset.sum_eq_zero fun j _ => hterm j
  have hexp : (∑ j, lamOf K z j * resid K z j)
      = (∑ a, qOf K z a * (ptOf K z a - qOf K z a)) - cOf K z := by
    have step : ∀ j : Fin (nv K), lamOf K z j * resid K z j
        = (∑ a, lamOf K z j * ((vtx K j a : ℚ) : ℝ) * (ptOf K z a - qOf K z a))
          - lamOf K z j * cOf K z := by
      intro j
      rw [resid_eq, mul_sub, Finset.mul_sum]
      exact congrArg₂ _ (Finset.sum_congr rfl fun a _ => by ring) rfl
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => step j,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul, Finset.sum_comm]
    refine congrArg₂ _ (Finset.sum_congr rfl fun a _ => ?_) rfl
    rw [qOf_apply, Finset.sum_mul]
  linarith [hzero', hexp]

/-- **The vertex certificate holds.**  With the scalar forced, the residual at a vertex
*is* the inner product the certificate asks about. -/
theorem inner_eq_resid (K : RationalPolytope d) (k : Fin d) (S T : List ℕ)
    {z : Fin (d + nv K + 1) → ℝ} (h : Holds K k S T z) (i : Fin (nv K)) :
    ⟪ptOf K z - qOf K z, toPt (vtx K i) - qOf K z⟫ = resid K z i := by
  rw [PiLp.inner_apply]
  have hpt : ∀ a : Fin d,
      ⟪(ptOf K z - qOf K z) a, (toPt (vtx K i) - qOf K z) a⟫
        = (ptOf K z a - qOf K z a) * (((vtx K i a : ℚ) : ℝ) - qOf K z a) := by
    intro a
    simp only [PiLp.sub_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial, toPt]
    ring
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hpt a]
  have hsplit : (∑ a, (ptOf K z a - qOf K z a) * (((vtx K i a : ℚ) : ℝ) - qOf K z a))
      = (∑ a, ((vtx K i a : ℚ) : ℝ) * (ptOf K z a - qOf K z a))
        - ∑ a, qOf K z a * (ptOf K z a - qOf K z a) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit, resid_eq, cOf_eq_of_holds K k S T h]

theorem qOf_mem_carrier (K : RationalPolytope d) (k : Fin d) (S T : List ℕ)
    {z : Fin (d + nv K + 1) → ℝ} (h : Holds K k S T z) : qOf K z ∈ K.carrier :=
  combSet_subset_carrier K ⟨lamOf K z, h.2.1, h.1, rfl⟩

/-- **Soundness.**  A solution of the system encodes a point whose projection is exactly
the encoded convex combination. -/
theorem qOf_eq_proj (K : RationalPolytope d) (k : Fin d) (S T : List ℕ)
    {z : Fin (d + nv K + 1) → ℝ} (h : Holds K k S T z) :
    qOf K z = K.proj (ptOf K z) := by
  refine K.eq_proj_of_vertexSet (qOf_mem_carrier K k S T h) ?_
  intro v hv
  obtain ⟨i, rfl⟩ := exists_vtx_of_mem_vertexSet K hv
  rw [inner_eq_resid K k S T h i]
  exact h.2.2.2.2.1 i

theorem proj_eq_lamVal (K : RationalPolytope d) (k : Fin d) (S T : List ℕ)
    {z : Fin (d + nv K + 1) → ℝ} (h : Holds K k S T z) :
    K.proj (ptOf K z) k = lamVal K k z := by
  rw [lamVal_eq_qOf, qOf_eq_proj K k S T h]

/-! ## Completeness: every point realises some pair

The support is the set of strictly positive weights, the upper set is the point's own, and
the scalar is `⟪x − q, q⟫`.  Complementary slackness — a nonpositive family with weighted
sum zero — is what turns the certificate's inequality into an equality on the support. -/

/-- The natural-number index list of a decidable predicate on `Fin n`, as a sublist of
`List.range n`.  Used only inside proofs, to name the support and the upper set. -/
def natsOf (n : ℕ) (P : Fin n → Prop) [DecidablePred P] : List ℕ :=
  (List.range n).filter fun j => if h : j < n then decide (P ⟨j, h⟩) else false

theorem natsOf_sublist (n : ℕ) (P : Fin n → Prop) [DecidablePred P] :
    (natsOf n P).Sublist (List.range n) := List.filter_sublist

theorem mem_natsOf {n : ℕ} {P : Fin n → Prop} [DecidablePred P] (i : Fin n) :
    (i : ℕ) ∈ natsOf n P ↔ P i := by
  rw [natsOf, List.mem_filter]
  simp [i.isLt]

/-- The witness a point supplies for its own pair. -/
def witnessOf (K : RationalPolytope d) (x : Pt d) (w : Fin (nv K) → ℝ)
    (c : ℝ) : Fin (d + nv K + 1) → ℝ :=
  fun t =>
    if h : (t : ℕ) < d then x ⟨t, h⟩
    else if h' : (t : ℕ) < d + nv K then w ⟨(t : ℕ) - d, by omega⟩ else c

theorem witnessOf_embX (K : RationalPolytope d) (x : Pt d) (w : Fin (nv K) → ℝ) (c : ℝ)
    (a : Fin d) : witnessOf K x w c (embX d (nv K) a) = x a := by
  have h : ((embX d (nv K) a : Fin (d + nv K + 1)) : ℕ) < d := by simp [embX]
  rw [witnessOf, dif_pos h]
  exact congrArg (fun i : Fin d => x i) (Fin.ext rfl)

theorem witnessOf_embL (K : RationalPolytope d) (x : Pt d) (w : Fin (nv K) → ℝ) (c : ℝ)
    (j : Fin (nv K)) : witnessOf K x w c (embL d (nv K) j) = w j := by
  have hj := j.2
  have h1 : ¬ ((embL d (nv K) j : Fin (d + nv K + 1)) : ℕ) < d := by simp [embL]
  have h2 : ((embL d (nv K) j : Fin (d + nv K + 1)) : ℕ) < d + nv K := by
    simp [embL]
  rw [witnessOf, dif_neg h1, dif_pos h2]
  congr 1
  exact Fin.ext (by simp [embL])

theorem witnessOf_embC (K : RationalPolytope d) (x : Pt d) (w : Fin (nv K) → ℝ) (c : ℝ) :
    witnessOf K x w c (embC d (nv K)) = c := by
  have h1 : ¬ ((embC d (nv K) : Fin (d + nv K + 1)) : ℕ) < d := by simp [embC]
  have h2 : ¬ ((embC d (nv K) : Fin (d + nv K + 1)) : ℕ) < d + nv K := by simp [embC]
  rw [witnessOf, dif_neg h1, dif_neg h2]

theorem ptOf_witnessOf (K : RationalPolytope d) (x : Pt d) (w : Fin (nv K) → ℝ) (c : ℝ) :
    ptOf K (witnessOf K x w c) = x := by
  have : (fun a : Fin d => witnessOf K x w c (embX d (nv K) a)) = fun a => x a :=
    funext fun a => witnessOf_embX K x w c a
  rw [ptOf, this]

theorem lamOf_witnessOf (K : RationalPolytope d) (x : Pt d) (w : Fin (nv K) → ℝ) (c : ℝ)
    (j : Fin (nv K)) : lamOf K (witnessOf K x w c) j = w j := witnessOf_embL K x w c j

theorem cOf_witnessOf (K : RationalPolytope d) (x : Pt d) (w : Fin (nv K) → ℝ) (c : ℝ) :
    cOf K (witnessOf K x w c) = c := witnessOf_embC K x w c

/-- **Completeness.**  Every point of the ambient space realises a pair `(S, T)`: the
support is the set of strictly positive weights of a barycentric representation of its
projection, and `T` is its own upper set.  The scalar is `⟪x − q, q⟫`, which is what the
system's residual equations force it to be. -/
theorem exists_holds (K : RationalPolytope d) (k : Fin d) (x : Pt d) :
    ∃ (S T : List ℕ) (z : Fin (d + nv K + 1) → ℝ),
      S.Sublist (List.range (nv K)) ∧ T.Sublist (List.range (nf K)) ∧
        Holds K k S T z ∧ ptOf K z = x ∧
        (∀ i : Fin (nf K), (i : ℕ) ∈ T ↔ K.proj x k ≤ (comp K k i).eval x) := by
  classical
  obtain ⟨w, hw, hws, hq⟩ := carrier_subset_combSet K (K.proj_mem x)
  have hqa : ∀ a : Fin d, K.proj x a = ∑ j, w j * ((vtx K j a : ℚ) : ℝ) := by
    intro a
    rw [hq, sum_pt_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [PiLp.smul_apply, smul_eq_mul]; rfl
  -- the certificate value at each vertex, in coordinates
  set A : Fin (nv K) → ℝ :=
    fun i => ∑ a, (x a - K.proj x a) * (((vtx K i a : ℚ) : ℝ) - K.proj x a) with hAdef
  have hAle : ∀ i, A i ≤ 0 := by
    intro i
    have hv := K.proj_variational x (K.vertexSet_subset_carrier ⟨vtx K i, vtx_mem K i, rfl⟩)
    rw [PiLp.inner_apply] at hv
    have hpt : ∀ a : Fin d,
        ⟪(x - K.proj x) a, (toPt (vtx K i) - K.proj x) a⟫
          = (x a - K.proj x a) * (((vtx K i a : ℚ) : ℝ) - K.proj x a) := by
      intro a
      simp only [PiLp.sub_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial, toPt]
      ring
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hpt a] at hv
    exact hv
  -- complementary slackness
  have hAsum : (∑ j, w j * A j) = 0 := by
    have hstep : ∀ a : Fin d, (∑ j, w j * ((((vtx K j a : ℚ) : ℝ)) - K.proj x a)) = 0 := by
      intro a
      rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => (mul_sub (w j) _ _),
        Finset.sum_sub_distrib, ← Finset.sum_mul, hws, one_mul, ← hqa a, sub_self]
    calc (∑ j, w j * A j)
        = ∑ j, ∑ a, (x a - K.proj x a) * (w j * (((vtx K j a : ℚ) : ℝ) - K.proj x a)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hAdef, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ a, ∑ j, (x a - K.proj x a) * (w j * (((vtx K j a : ℚ) : ℝ) - K.proj x a)) :=
          Finset.sum_comm
      _ = 0 := by
          refine Finset.sum_eq_zero fun a _ => ?_
          rw [← Finset.mul_sum, hstep a, mul_zero]
  have hAzero : ∀ j, 0 < w j → A j = 0 := by
    intro j hj
    have hnonpos : ∀ i ∈ (Finset.univ : Finset (Fin (nv K))), w i * A i ≤ 0 :=
      fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw i) (hAle i)
    have hz := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hAsum j (Finset.mem_univ j)
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (ne_of_gt hj)
    · exact h
  -- the witness
  refine ⟨natsOf (nv K) fun j => 0 < w j,
    natsOf (nf K) (fun i => K.proj x k ≤ (comp K k i).eval x),
    witnessOf K x w (∑ a, K.proj x a * (x a - K.proj x a)),
    natsOf_sublist _ _, natsOf_sublist _ _, ?_, ptOf_witnessOf K x w _, ?_⟩
  · -- the eight conditions
    set c : ℝ := ∑ a, K.proj x a * (x a - K.proj x a) with hcdef
    set z : Fin (d + nv K + 1) → ℝ := witnessOf K x w c with hzdef
    have hpt : ptOf K z = x := ptOf_witnessOf K x w c
    have hlam : ∀ j, lamOf K z j = w j := lamOf_witnessOf K x w c
    have hcc : cOf K z = c := cOf_witnessOf K x w c
    have hqOf : ∀ a, qOf K z a = K.proj x a := by
      intro a
      rw [qOf_apply, hqa]
      exact Finset.sum_congr rfl fun j _ => by rw [hlam]
    have hres : ∀ i, resid K z i = A i := by
      intro i
      simp only [hAdef]
      rw [resid_eq, hcc, hcdef]
      have hsplit : (∑ a, (x a - K.proj x a) * (((vtx K i a : ℚ) : ℝ) - K.proj x a))
          = (∑ a, ((vtx K i a : ℚ) : ℝ) * (x a - K.proj x a))
            - ∑ a, K.proj x a * (x a - K.proj x a) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hsplit]
      refine congrArg₂ _ (Finset.sum_congr rfl fun a _ => ?_) rfl
      rw [hpt, hqOf]
    have hlamVal : lamVal K k z = K.proj x k := by
      rw [lamVal_eq_qOf, hqOf]
    refine ⟨?_, fun j => ?_, fun j hj => ?_, fun j hj => ?_, fun i => ?_, fun i hi => ?_,
      fun i hi => ?_, fun i hi => ?_⟩
    · rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hlam j]; exact hws
    · rw [hlam]; exact hw j
    · rw [hlam]; exact (mem_natsOf j).mp hj
    · rw [hlam]; exact le_of_not_gt fun hc => hj ((mem_natsOf j).mpr hc)
    · rw [hres]; exact hAle i
    · rw [hres, hAzero i ((mem_natsOf i).mp hi)]
    · rw [hlamVal, hpt]; exact (mem_natsOf i).mp hi
    · rw [hlamVal, hpt]
      exact lt_of_not_ge fun hc => hi ((mem_natsOf i).mpr hc)
  · intro i; exact mem_natsOf i

/-! ## The family, computed

Every pair of a sublist of the vertex positions and a sublist of the component positions is
tried; the ones that pass `feasible` contribute their upper set.  Doubly exponential, and
a `def`. -/

/-- All candidate `(support, upper set)` pairs. -/
def candidatePairs (K : RationalPolytope d) : List (List ℕ × List ℕ) :=
  (List.range (nv K)).sublists.flatMap fun S =>
    (List.range (nf K)).sublists.map fun T => (S, T)

/-- **The computed index family.**  A `def`: no `Classical.choose` on the path from `K` and
`k` to this list. -/
def projectorFamily (K : RationalPolytope d) (k : Fin d) : List (List ℕ) :=
  ((candidatePairs K).filter fun ST =>
      feasible (d + nv K + 1) (system K k ST.1 ST.2)).map Prod.snd

theorem mem_projectorFamily {K : RationalPolytope d} {k : Fin d} {T : List ℕ}
    (h : T ∈ projectorFamily K k) :
    ∃ S : List ℕ, feasible (d + nv K + 1) (system K k S T) = true := by
  rw [projectorFamily, List.mem_map] at h
  obtain ⟨⟨S, T'⟩, hmem, hT⟩ := h
  rw [List.mem_filter] at hmem
  cases hT
  exact ⟨S, hmem.2⟩

theorem mem_projectorFamily_of {K : RationalPolytope d} {k : Fin d} {S T : List ℕ}
    (hS : S.Sublist (List.range (nv K))) (hT : T.Sublist (List.range (nf K)))
    (hf : feasible (d + nv K + 1) (system K k S T) = true) : T ∈ projectorFamily K k := by
  rw [projectorFamily, List.mem_map]
  refine ⟨(S, T), ?_, rfl⟩
  rw [List.mem_filter]
  refine ⟨?_, hf⟩
  rw [candidatePairs, List.mem_flatMap]
  exact ⟨S, List.mem_sublists.mpr hS,
    List.mem_map.mpr ⟨T, List.mem_sublists.mpr hT, rfl⟩⟩

theorem exists_holds_of_mem_family {K : RationalPolytope d} {k : Fin d} {T : List ℕ}
    (h : T ∈ projectorFamily K k) :
    ∃ (S : List ℕ) (z : Fin (d + nv K + 1) → ℝ), Holds K k S T z := by
  obtain ⟨S, hf⟩ := mem_projectorFamily h
  obtain ⟨z, hz⟩ := (feasible_iff _ _).mp hf
  exact ⟨S, z, (sat_system_iff K k S T z).mp hz⟩

/-- The family is nonempty: apply completeness at the origin. -/
theorem projectorFamily_ne_nil (K : RationalPolytope d) (k : Fin d) :
    projectorFamily K k ≠ [] := by
  obtain ⟨S, T, z, hSs, hTs, hh, -, -⟩ := exists_holds K k 0
  have hmem : T ∈ projectorFamily K k :=
    mem_projectorFamily_of hSs hTs
      ((feasible_iff _ _).mpr ⟨z, (sat_system_iff K k S T z).mpr hh⟩)
  intro hnil
  rw [hnil] at hmem
  simp at hmem

/-- Some component attains the projector's value at every point — the coverage half of
`isPiecewiseAffineOn_proj`. -/
theorem exists_attain (K : RationalPolytope d) (k : Fin d) (x : Pt d) :
    ∃ i : Fin (nf K), K.proj x k = (comp K k i).eval x := by
  obtain ⟨M, Q, cc, hQc, hcov, hQf⟩ := PolyhedralCoverage.isPiecewiseAffineOn_proj K k
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ x))
  refine ⟨cc l, ?_⟩
  have h := hQf l x ⟨hl, Set.mem_univ x⟩
  rwa [PolyhedralCoverage.AffineForm.toAffineMap_apply] at h

/-- A realised upper set is nonempty, because some component attains the value. -/
theorem exists_mem_of_mem_family {K : RationalPolytope d} {k : Fin d} {T : List ℕ}
    (h : T ∈ projectorFamily K k) : ∃ i : Fin (nf K), (i : ℕ) ∈ T := by
  obtain ⟨S, z, hh⟩ := exists_holds_of_mem_family h
  obtain ⟨i, hi⟩ := exists_attain K k (ptOf K z)
  refine ⟨i, ?_⟩
  by_contra hc
  have hlt := hh.2.2.2.2.2.2.2 i hc
  rw [← hi, proj_eq_lamVal K k S T hh] at hlt
  exact lt_irrefl _ hlt

/-! ## From the family to a representation

`ProjectionBridge.groupOf` and `repOf` take a nonemptiness proof, which would put a proof
in the data path.  `groupOfList` and `repOfList` are the same constructions made total; the
two agree on nonempty lists, so the bridge's evaluation lemmas transfer verbatim. -/

/-- The positions of a candidate upper set, as an index list. -/
def idxList (K : RationalPolytope d) (T : List ℕ) : List (Fin (nf K)) :=
  (List.finRange (nf K)).filter fun i => decide ((i : ℕ) ∈ T)

theorem mem_idxList {K : RationalPolytope d} {T : List ℕ} (i : Fin (nf K)) :
    i ∈ idxList K T ↔ (i : ℕ) ∈ T := by
  rw [idxList, List.mem_filter]
  simp

theorem idxList_ne_nil {K : RationalPolytope d} {k : Fin d} {T : List ℕ}
    (h : T ∈ projectorFamily K k) : idxList K T ≠ [] := by
  obtain ⟨i, hi⟩ := exists_mem_of_mem_family h
  intro hc
  have hmem : i ∈ idxList K T := (mem_idxList i).mpr hi
  rw [hc] at hmem
  simp at hmem

/-- A nonempty list of affine forms, indexed, as a group — total, unlike
`ProjectionBridge.groupOf`. -/
def groupOfList {ι : Type*} (A : ι → ProjectionCompiler.AffineForm) :
    List ι → ProjectionCompiler.Group
  | [] => (([], 0), [])
  | i :: t => (A i, t.map A)

/-- A nonempty list of groups, indexed, as a representation — total, unlike
`ProjectionBridge.repOf`. -/
def repOfList {ι : Type*} (G : ι → ProjectionCompiler.Group) :
    List ι → ProjectionCompiler.Rep
  | [] => ((([], 0), []), [])
  | g :: t => (G g, t.map G)

theorem groupOfList_eq {ι : Type*} (A : ι → ProjectionCompiler.AffineForm) (l : List ι)
    (h : l ≠ []) : groupOfList A l = groupOf A l h := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

theorem repOfList_eq {ι : Type*} (G : ι → ProjectionCompiler.Group) (l : List ι)
    (h : l ≠ []) : repOfList G l = repOf G l h := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

theorem groupEval_groupOfList (F : Fragment) {ι : Type*} [DecidableEq ι]
    (A : ι → ProjectionCompiler.AffineForm) (l : List ι) (h : l ≠ [])
    (hne : l.toFinset.Nonempty) (p : Sentence → ℝ) :
    groupEval F (groupOfList A l) p
      = l.toFinset.inf' hne fun i => ProjectionCompiler.AffineForm.evalR F (A i) p := by
  rw [groupOfList_eq A l h]
  exact ProjectionBridge.groupEval_groupOf F A l h hne p

theorem repEval_repOfList (F : Fragment) {ι : Type*} [DecidableEq ι]
    (G : ι → ProjectionCompiler.Group) (l : List ι) (h : l ≠ [])
    (hne : l.toFinset.Nonempty) (p : Sentence → ℝ) :
    repEval F (repOfList G l) p = l.toFinset.sup' hne fun i => groupEval F (G i) p := by
  rw [repOfList_eq G l h]
  exact ProjectionBridge.repEval_repOf F G l h hne p

theorem toFinset_finRange (n : ℕ) :
    (List.finRange n).toFinset = (Finset.univ : Finset (Fin n)) := by
  ext i; simp

/-- Reindexing a `sup'` over `Fin L` along `L = M + 1`. -/
theorem sup'_fin_cast {L M : ℕ} (h : L = M + 1) (φ : Fin L → ℝ)
    (hL : (Finset.univ : Finset (Fin L)).Nonempty) :
    Finset.univ.sup' hL φ
      = Finset.univ.sup' (Finset.univ_nonempty (α := Fin (M + 1)))
          fun j => φ (Fin.cast h.symm j) := by
  refine le_antisymm (Finset.sup'_le _ _ fun j _ => ?_) (Finset.sup'_le _ _ fun j _ => ?_)
  · refine le_of_eq_of_le ?_ (Finset.le_sup' (fun j : Fin (M + 1) => φ (Fin.cast h.symm j))
      (Finset.mem_univ (Fin.cast h j)))
    exact congrArg φ (Fin.ext rfl)
  · exact Finset.le_sup' φ (Finset.mem_univ (Fin.cast h.symm j))

/-- The `i`-th component, in the compiler's coordinates. -/
def compForm (F : Fragment) (K : RationalPolytope F.coords.length)
    (k : Fin F.coords.length) (i : Fin (nf K)) : ProjectionCompiler.AffineForm :=
  ofGeom (comp K k i)

/-- **The computed representation.**  A `def`, mirroring how `exists_rep_repEval` builds
its `Rep` — one group per member of the computed family, one affine form per component in
that member's upper set. -/
def projectorRep (F : Fragment) (K : RationalPolytope F.coords.length)
    (k : Fin F.coords.length) : ProjectionCompiler.Rep :=
  repOfList
    (fun j : Fin (projectorFamily K k).length =>
      groupOfList (compForm F K k) (idxList K ((projectorFamily K k).get j)))
    (List.finRange (projectorFamily K k).length)

/-- **The computable counterpart of `ProjectionBridge.exists_rep_repEval`.**  The `def`
above evaluates to the projector's coordinate at every price vector. -/
theorem repEval_projectorRep (F : Fragment) (K : RationalPolytope F.coords.length)
    (k : Fin F.coords.length) :
    ∀ p : Sentence → ℝ, repEval F (projectorRep F K k) p = K.proj (restrict F p) k := by
  classical
  intro p
  have hfamne : projectorFamily K k ≠ [] := projectorFamily_ne_nil K k
  have hLne : (projectorFamily K k).length ≠ 0 := by
    simpa [List.length_eq_zero_iff] using hfamne
  obtain ⟨M, hM⟩ : ∃ M, (projectorFamily K k).length = M + 1 :=
    ⟨(projectorFamily K k).length - 1,
      (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hLne)).symm⟩
  set L := (projectorFamily K k).length with hLdef
  set Sf : Fin L → Finset (Fin (nf K)) :=
    fun j => (idxList K ((projectorFamily K k).get j)).toFinset with hSf
  have hidxne : ∀ j : Fin L, idxList K ((projectorFamily K k).get j) ≠ [] :=
    fun j => idxList_ne_nil (List.get_mem _ _)
  have hSne : ∀ j : Fin L, (Sf j).Nonempty := by
    intro j
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (hidxne j)
    exact ⟨i, List.mem_toFinset.mpr hi⟩
  have hLpos : (Finset.univ : Finset (Fin L)).Nonempty :=
    ⟨Fin.cast hM.symm 0, Finset.mem_univ _⟩
  -- the max–min representation, from the computed family
  have hmain : K.proj (restrict F p) k
      = Finset.univ.sup' (Finset.univ_nonempty (α := Fin (M + 1)))
          fun j => (Sf (Fin.cast hM.symm j)).inf' (hSne _)
            fun i => (comp K k i).toAffineMap (restrict F p) := by
    refine MaxMinRepresentation.maxMin_of_family (convex_univ)
      (PolyhedralCoverage.isPiecewiseAffineOn_proj K k)
      (fun j => Sf (Fin.cast hM.symm j)) (fun j => hSne _) ?_ ?_ _ (Set.mem_univ _)
    · intro j
      obtain ⟨S, z, hh⟩ :=
        exists_holds_of_mem_family (List.get_mem (projectorFamily K k) (Fin.cast hM.symm j))
      refine ⟨ptOf K z, Set.mem_univ _, fun i hi => ?_⟩
      rw [PolyhedralCoverage.AffineForm.toAffineMap_apply] at hi
      rw [proj_eq_lamVal K k S ((projectorFamily K k).get (Fin.cast hM.symm j)) hh] at hi
      refine List.mem_toFinset.mpr ((mem_idxList i).mpr ?_)
      by_contra hc
      exact absurd hi (not_le_of_gt (hh.2.2.2.2.2.2.2 i hc))
    · intro y _
      obtain ⟨S, T, z, hSs, hTs, hh, hpt, hiff⟩ := exists_holds K k y
      have hTmem : T ∈ projectorFamily K k :=
        mem_projectorFamily_of hSs hTs
          ((feasible_iff _ _).mpr ⟨z, (sat_system_iff K k S T z).mpr hh⟩)
      obtain ⟨j0, hj0⟩ := List.mem_iff_get.mp hTmem
      refine ⟨Fin.cast hM j0, fun i hi => ?_⟩
      have hcast : Fin.cast hM.symm (Fin.cast hM j0) = j0 := Fin.ext rfl
      rw [hcast, hSf] at hi
      rw [PolyhedralCoverage.AffineForm.toAffineMap_apply]
      exact (hiff i).mp (by rw [← hj0]; exact (mem_idxList i).mp (List.mem_toFinset.mp hi))
  -- the compiled side
  have hfr : (List.finRange L) ≠ [] := by
    simpa [List.finRange_eq_nil_iff] using hLne
  have hfrne : (List.finRange L).toFinset.Nonempty := by
    rw [toFinset_finRange]; exact hLpos
  have hrep : repEval F (projectorRep F K k) p
      = Finset.univ.sup' hLpos (fun j : Fin L =>
          (Sf j).inf' (hSne j) fun i => (comp K k i).toAffineMap (restrict F p)) := by
    rw [projectorRep, repEval_repOfList F _ (List.finRange L) hfr hfrne p]
    refine Finset.sup'_congr hfrne (toFinset_finRange L) fun j _ => ?_
    rw [groupEval_groupOfList F (compForm F K k)
      (idxList K ((projectorFamily K k).get j)) (hidxne j) (hSne j) p]
    refine Finset.inf'_congr _ rfl fun i _ => ?_
    rw [compForm, ProjectionBridge.evalR_ofGeom,
      PolyhedralCoverage.AffineForm.toAffineMap_apply]
  rw [hrep, sup'_fin_cast hM]
  exact hmain.symm

/-- The same representation, indexed by membership rather than by position: the form
`ProjectionBridge.exists_repMap_mem` states its conclusion in. -/
def projectorRepMap (F : Fragment) (K : RationalPolytope F.coords.length) :
    Sentence → ProjectionCompiler.Rep :=
  fun φ =>
    if h : F.coords.idxOf φ < F.coords.length then projectorRep F K ⟨_, h⟩ else default

/-- **The membership-indexed map is correct.**  The computable counterpart of
`ProjectionBridge.exists_repMap_mem`. -/
theorem repEval_projectorRepMap (F : Fragment) (K : RationalPolytope F.coords.length) :
    ∀ (p : Sentence → ℝ) (φ : Sentence) (hφ : φ ∈ F.coords),
      repEval F (projectorRepMap F K φ) p
        = K.proj (restrict F p) ⟨F.coords.idxOf φ, List.idxOf_lt_length_of_mem hφ⟩ := by
  intro p φ hφ
  have hlt : F.coords.idxOf φ < F.coords.length := List.idxOf_lt_length_of_mem hφ
  rw [projectorRepMap, dif_pos hlt]
  exact repEval_projectorRep F K ⟨F.coords.idxOf φ, hlt⟩ p

/-! ## Nonvacuity

`AGENTS.md` standard 3: a term inhabiting the hypothesis package.  The package is a
fragment together with a rational polytope of the fragment's dimension, so the witness is
`ProjectionBridge.unitFragment` and the unit segment in its single coordinate. -/

/-- The generator is about something: one priced sentence, and the projection onto the unit
segment in its coordinate, represented for the compiler by a `def`. -/
theorem generator_nonvacuous :
    ∀ (p : Sentence → ℝ) (φ : Sentence) (hφ : φ ∈ ProjectionBridge.unitFragment.coords),
      repEval ProjectionBridge.unitFragment
          (projectorRepMap ProjectionBridge.unitFragment PolyhedralCoverage.unitSegment φ) p
        = PolyhedralCoverage.unitSegment.proj
            (restrict ProjectionBridge.unitFragment p)
            ⟨ProjectionBridge.unitFragment.coords.idxOf φ,
              List.idxOf_lt_length_of_mem hφ⟩ :=
  repEval_projectorRepMap ProjectionBridge.unitFragment PolyhedralCoverage.unitSegment

/-! ## The generator runs

The point of the file is that the definitions above are `def`s that reduce, so the `#eval`s
below are part of the claim and not decoration.  The unit segment in one dimension has two
vertices and hence `2 · 2 ^ 2 = 8` enumerated faces, so the enumeration is `2 ^ 2 · 2 ^ 8`
feasibility tests on systems of eighteen constraints in four variables. -/

-- How many index sets the generator finds for the unit segment.
#eval (projectorFamily PolyhedralCoverage.unitSegment 0).length

-- The index sets themselves, as positions in `faceList`.
#eval projectorFamily PolyhedralCoverage.unitSegment 0

-- The representation the compiler receives: how many trailing groups, and the leading one.
#eval ((projectorRep ProjectionBridge.unitFragment PolyhedralCoverage.unitSegment
    ⟨0, by decide⟩).2.length,
  (projectorRep ProjectionBridge.unitFragment PolyhedralCoverage.unitSegment
    ⟨0, by decide⟩).1)

end Workspace.Normativity.Contrib.ProjectorGenerator

#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sum_split
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.coeffFn_embX
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.coeffFn_embL
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.coeffFn_embC
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.eval_mkCon
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_mkCon_le
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_mkCon_lt
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sum_ite_lam
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.vtx_mem
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.exists_vtx_of_mem_vertexSet
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.ptOf_apply
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sum_pt_apply
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.qOf_apply
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.lamVal_eq_qOf
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conSumLe
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conSumGe
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conNonneg
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conSupport_mem
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conSupport_notMem
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conVertLe
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conVertGe_mem
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conVertGe_notMem
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conUpper_mem
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_conUpper_notMem
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sat_system_iff
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.combSet_convex
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.combSet_subset_carrier
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.carrier_subset_combSet
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sum_lam_gram
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.resid_eq
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.cOf_eq_of_holds
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.inner_eq_resid
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.qOf_mem_carrier
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.qOf_eq_proj
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.proj_eq_lamVal
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.natsOf_sublist
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.mem_natsOf
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.witnessOf_embX
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.witnessOf_embL
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.witnessOf_embC
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.ptOf_witnessOf
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.lamOf_witnessOf
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.cOf_witnessOf
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.exists_holds
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.mem_projectorFamily
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.mem_projectorFamily_of
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.exists_holds_of_mem_family
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.projectorFamily_ne_nil
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.exists_attain
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.exists_mem_of_mem_family
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.mem_idxList
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.idxList_ne_nil
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.groupOfList_eq
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.repOfList_eq
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.groupEval_groupOfList
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.repEval_repOfList
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.toFinset_finRange
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.sup'_fin_cast
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.repEval_projectorRep
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.repEval_projectorRepMap
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.generator_nonvacuous
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.projectorFamily
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.projectorRep
#print axioms Workspace.Normativity.Contrib.ProjectorGenerator.projectorRepMap
