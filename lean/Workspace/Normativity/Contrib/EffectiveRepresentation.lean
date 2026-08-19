/-
# The compiler, as a primitive recursive function of the region's flat data

`ConstraintSchedule.RegionRepresentation.Effective` is the last implementation artifact in
the theorem of record.  It asks for one function

    compile : List Sentence → List (List ℚ) → List Rep

that is `Primrec₂` and that returns, on the day's fragment and the day's flat vertex data,
the day's max–min representation.  `ProjectorGenerator` supplies the *mathematics* of such a
function — `projectorRep` is a `def`, and `repEval_projectorRepMap` says it is correct — but
not the certificate, and for a structural reason that this file is entirely about.

## Why the generator is not already the compiler

`projectorRep` takes a `Fragment` — a list of sentences bundled with a `Nodup` proof — and a
`RationalPolytope F.coords.length` — a list of vertices in a type that *depends on the
fragment*, bundled with a nonemptiness proof.  `Primrec` quantifies over `Primcodable` types,
and neither of those is one: a proof cannot be encoded, and a family of types indexed by an
argument cannot be spoken about at all.  The obstruction is not that the generator is
ineffective; it is that its *type* is not one a computability statement can mention.

So this file does what `ProjectionPrimrec` did one level up, and for the same reason.  Each
construction on the path from `(coords, verts)` to the day's `Rep` is written a second time
over raw, proof-free, non-dependent data — `List ℚ` for a point, `List (List ℚ)` for a
matrix or a vertex list, `ℕ` for an index — and each raw version is proved equal to the
structured one on well-formed input, and `Primrec`.  Nothing new is proved about projection;
the mathematics is `ProjectorGenerator`'s, transported.

## What had to be rebuilt, and how far down

Further than one might guess.  The generator's affine components are
`((PolyhedralCoverage.faceList K).get i).piece k`, and `Face.piece` is built from
`gramInvQ = det⁻¹ • adjugate` — so the raw pipeline bottoms out at a **determinant of a
rational matrix of a size that is not fixed in advance**.  `Matrix.det` is a sum over
`Equiv.Perm (Fin n)`, which is exactly the kind of thing that cannot appear in a `Primrec`
statement, so `detOf : List (List ℚ) → ℚ` is written here by cofactor expansion along the
first row and proved to agree with `Matrix.det` through `Matrix.det_succ_row_zero`.

Its computability is the one place where a plain fold does not suffice: the recursion is on
a *shrinking matrix*, not on a shrinking list, so `Primrec.list_rec` does not apply.
`Primrec.nat_omega_rec'` — recursion along a well-founded measure with a computed list of
recursive-call arguments — is the right instrument, with the measure the number of rows and
the arguments the first-row minors.  Everything above the determinant is then ordinary
`List.range` / `List.map` / `List.foldr` plumbing.

`List.sublists` also has to be shown primitive recursive: the face enumeration and the
generator's candidate `(support, upper set)` pairs are both sublist enumerations.

## What is *not* claimed

No efficiency.  The generator is doubly exponential in the number of vertices and the
determinant adds a factorial factor on top of that; this file certifies that the compiler is
primitive recursive, which is the only thing the logical-inductor construction needs, and
nothing more.

No new mathematics.  Every correctness statement below reduces to
`ProjectorGenerator.repEval_projectorRepMap` through a chain of equalities between raw and
structured data.  In particular `effectiveRepresentation` is a genuine construction:
`Classical.choose` appears nowhere on its definitional path, which is what distinguishes it
from `RationalConstraintSchedule.canonicalRepresentation`.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ConstraintSchedule
import Workspace.Normativity.Contrib.ProjectorGenerator

namespace Workspace.Normativity.Contrib.EffectiveRepresentation

open LogicalInduction
open Workspace.Normativity.Contrib.FourierMotzkin
open Workspace.Normativity.Contrib.ProjectorGenerator

/-! ## Sums over an initial segment

The structured development sums over `Fin n`; the raw one sums a list built by
`List.range`.  These lemmas are the whole of the translation, and every raw definition below
is stated so as to use them. -/

/-- A list sum over `List.range` is a `Finset.range` sum. -/
lemma sum_range_list (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A list sum over `List.range n` is a sum over `Fin n`, when the summands agree. -/
lemma sum_range_eq_univ {n : ℕ} (g : ℕ → ℚ) (f : Fin n → ℚ)
    (h : ∀ i : Fin n, g (i : ℕ) = f i) :
    ((List.range n).map g).sum = ∑ i : Fin n, f i := by
  rw [sum_range_list, ← Fin.sum_univ_eq_sum_range g n]
  exact Finset.sum_congr rfl fun i _ => h i

/-- Reading back an entry of a list built by `List.range`. -/
lemma getD_map_range {α : Type*} (n : ℕ) (f : ℕ → α) (d : α) {j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j d = f j := by
  have hlt : j < ((List.range n).map f).length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map, List.getElem_range]

/-- Reading back an entry of a list built by `List.ofFn`. -/
lemma getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) {j : ℕ} (hj : j < n) :
    (List.ofFn f).getD j d = f ⟨j, hj⟩ := by
  have hlt : j < (List.ofFn f).length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]

/-! ## Sublist enumeration is primitive recursive

`PolyhedralCoverage.faceList` and `ProjectorGenerator.candidatePairs` both enumerate
sublists, so the compiler cannot be effective without this. -/

/-- `List.sublists'` is a `foldr`, hence primitive recursive. -/
lemma sublists'_primrec {α : Type} [Primcodable α] :
    Primrec (List.sublists' : List α → List (List α)) := by
  have hstep : Primrec₂ fun (_ : List α) (p : α × List (List α)) =>
      p.2 ++ p.2.map (fun l => p.1 :: l) := by
    have hsnd : Primrec fun q : List α × (α × List (List α)) => q.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hmap : Primrec fun q : List α × (α × List (List α)) =>
        q.2.2.map (fun l => q.2.1 :: l) :=
      Primrec.list_map hsnd
        (Primrec.list_cons.comp₂ ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left)
          Primrec₂.right)
    exact (Primrec.list_append.comp hsnd hmap).to₂
  have hfun : (fun (a : α) (r : List (List α)) => List.sublists'Aux a r r)
      = fun (a : α) (r : List (List α)) => r ++ r.map (fun l => a :: l) := by
    funext a r
    exact List.sublists'Aux_eq_map a r r
  have h := Primrec.list_foldr Primrec.id (Primrec.const ([[]] : List (List α))) hstep
  refine h.of_eq fun l => ?_
  rw [List.sublists'_eq_sublists'Aux, hfun]
  rfl

/-- `List.sublists` is primitive recursive. -/
lemma sublists_primrec {α : Type} [Primcodable α] :
    Primrec (List.sublists : List α → List (List α)) := by
  have h : Primrec fun l : List α => (List.sublists' l.reverse).map List.reverse :=
    Primrec.list_map (sublists'_primrec.comp Primrec.list_reverse)
      (Primrec.list_reverse.comp₂ Primrec₂.right)
  exact h.of_eq fun l => (List.sublists_eq_sublists' l).symm

/-! ## Deleting a coordinate

`cutAt l j` is `l` with its `j`-th entry removed, written with `take` and `drop` so that
`Primrec.list_take` and `Primrec.list_drop` apply directly.  It is the raw form both of the
column deletion in a cofactor expansion and of `Fin.succAbove` reindexing. -/

/-- The list `l` with its `j`-th entry deleted. -/
def cutAt {α : Type*} (l : List α) (j : ℕ) : List α := l.take j ++ l.drop (j + 1)

lemma length_cutAt {α : Type*} (l : List α) {j : ℕ} (hj : j < l.length) :
    (cutAt l j).length = l.length - 1 := by
  simp only [cutAt, List.length_append, List.length_take, List.length_drop]
  omega

lemma cutAt_primrec {α : Type} [Primcodable α] :
    Primrec₂ (cutAt : List α → ℕ → List α) := by
  have h : Primrec fun p : List α × ℕ => p.1.take p.2 ++ p.1.drop (p.2 + 1) :=
    Primrec.list_append.comp (Primrec.list_take.comp Primrec.snd Primrec.fst)
      (Primrec.list_drop.comp (Primrec.succ.comp Primrec.snd) Primrec.fst)
  exact h.to₂

/-- The numeric value of `Fin.succAbove`: it skips the index `p`. -/
lemma val_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ)
      = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (by simpa [Fin.lt_def] using h1) h2
  · exact absurd (by simpa [Fin.lt_def] using h2) h1
  · rfl

/-- **Deleting a coordinate is `Fin.succAbove` reindexing.**  The bridge between the raw
cofactor expansion and `Matrix.det_succ_row_zero`. -/
lemma cutAt_ofFn {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) (p : Fin (n + 1)) :
    cutAt (List.ofFn f) (p : ℕ) = List.ofFn fun i : Fin n => f (p.succAbove i) := by
  have hp : (p : ℕ) < n + 1 := p.isLt
  have hlenf : (List.ofFn f).length = n + 1 := by simp
  refine List.ext_getElem ?_ ?_
  · rw [length_cutAt _ (by omega), hlenf]
    simp
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    rw [List.getElem_ofFn]
    simp only [cutAt]
    have htake : ((List.ofFn f).take (p : ℕ)).length = (p : ℕ) := by
      rw [List.length_take, hlenf]
      omega
    by_cases hcase : i < (p : ℕ)
    · rw [List.getElem_append_left (by omega)]
      rw [List.getElem_take, List.getElem_ofFn]
      exact congrArg f (Fin.ext (by rw [val_succAbove, if_pos hcase]))
    · rw [List.getElem_append_right (by omega), List.getElem_drop, List.getElem_ofFn]
      refine congrArg f (Fin.ext ?_)
      rw [val_succAbove, if_neg hcase]
      simp only [htake, Fin.val_mk]
      omega

/-! ## The determinant of a rational matrix, as a `def` on raw data

A matrix is a `List (List ℚ)`, one list per row.  `detOf` is the cofactor expansion along
the first row; the fuel argument makes the recursion structural, and is always the number of
rows, so `detOf` is the honest determinant and not a truncation. -/

/-- The cofactor expansion, with fuel. -/
def detAux : ℕ → List (List ℚ) → ℚ
  | 0, _ => 1
  | _ + 1, [] => 1
  | fuel + 1, r :: rs =>
      ((List.range r.length).map fun j =>
        (-1) ^ j * r.getD j 0 * detAux fuel (rs.map fun s => cutAt s j)).sum

/-- **The determinant of a raw rational matrix.** -/
def detOf (M : List (List ℚ)) : ℚ := detAux M.length M

@[simp] lemma detOf_nil : detOf [] = 1 := rfl

/-- The cofactor expansion, as an equation about `detOf` itself. -/
lemma detOf_cons (r : List ℚ) (rs : List (List ℚ)) :
    detOf (r :: rs) = ((List.range r.length).map fun j =>
      (-1) ^ j * r.getD j 0 * detOf (rs.map fun s => cutAt s j)).sum := by
  show detAux (rs.length + 1) (r :: rs) = _
  simp only [detAux]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  congr 1
  show detAux rs.length _ = detAux (List.length _) _
  rw [List.length_map]

/-! ### Agreement with `Matrix.det` -/

/-- A square matrix over `Fin n`, as raw data. -/
def matList {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : List (List ℚ) :=
  List.ofFn fun i => List.ofFn fun j => A i j

@[simp] lemma length_matList {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (matList A).length = n := by simp [matList]

/-- **The raw determinant is the determinant.** -/
theorem detOf_matList : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ), detOf (matList A) = A.det
  | 0, A => by simp [matList, Matrix.det_fin_zero]
  | n + 1, A => by
    have hml : matList A
        = (List.ofFn fun j => A 0 j) :: List.ofFn (fun i : Fin n =>
            List.ofFn fun j : Fin (n + 1) => A i.succ j) := by
      rw [matList, List.ofFn_succ]
    have hlen : (List.ofFn fun j : Fin (n + 1) => A 0 j).length = n + 1 := by simp
    rw [hml, detOf_cons, hlen, Matrix.det_succ_row_zero]
    refine sum_range_eq_univ _ _ fun j => ?_
    have hsub : (List.ofFn (fun i : Fin n =>
          List.ofFn fun j' : Fin (n + 1) => A i.succ j')).map (fun s => cutAt s (j : ℕ))
        = matList (A.submatrix Fin.succ j.succAbove) := by
      rw [matList, List.map_ofFn]
      refine congrArg List.ofFn (funext fun i => ?_)
      exact cutAt_ofFn (fun j' : Fin (n + 1) => A i.succ j') j
    rw [hsub, detOf_matList n (A.submatrix Fin.succ j.succAbove), getD_ofFn _ _ j.isLt]

/-! ### The determinant is primitive recursive

The recursion shrinks the matrix rather than a list, so `Primrec.list_rec` does not apply.
`Primrec.nat_omega_rec'` does: the measure is the number of rows and the recursive-call
arguments are the first-row minors. -/

/-- The first-row minors of a raw matrix: one for each column. -/
def subMats (M : List (List ℚ)) : List (List (List ℚ)) :=
  (List.range M.headI.length).map fun j => M.tail.map fun s => cutAt s j

/-- The cofactor combination, with the minors' determinants supplied. -/
def detCombine (M : List (List ℚ)) (ds : List ℚ) : ℚ :=
  if M.length = 0 then 1
  else ((List.range ds.length).map fun j =>
    (if j % 2 = 0 then (1 : ℚ) else -1) * M.headI.getD j 0 * ds.getD j 0).sum

lemma sign_eq (j : ℕ) : (if j % 2 = 0 then (1 : ℚ) else -1) = (-1) ^ j := by
  rcases Nat.even_or_odd j with h | h
  · rw [if_pos (Nat.even_iff.mp h), h.neg_one_pow]
  · rw [if_neg (by simp [Nat.odd_iff.mp h]), h.neg_one_pow]

/-- The recursion `detOf` satisfies, in the shape `Primrec.nat_omega_rec'` consumes. -/
lemma detCombine_subMats (M : List (List ℚ)) :
    detCombine M ((subMats M).map detOf) = detOf M := by
  cases M with
  | nil => simp [detCombine]
  | cons r rs =>
    have hlen : ((subMats (r :: rs)).map detOf).length = r.length := by
      simp [subMats]
    rw [detCombine, if_neg (by simp), hlen, detOf_cons]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    have hjlt : j < r.length := List.mem_range.mp hj
    have hds : ((subMats (r :: rs)).map detOf).getD j 0
        = detOf (rs.map fun s => cutAt s j) := by
      rw [subMats, List.map_map]
      exact getD_map_range _ _ _ (by simpa using hjlt)
    rw [sign_eq, hds]
    rfl

lemma subMats_nil : subMats ([] : List (List ℚ)) = [] := rfl

lemma subMats_ord (M : List (List ℚ)) : ∀ M' ∈ subMats M, M'.length < M.length := by
  intro M' hM'
  rcases M with _ | ⟨r, rs⟩
  · rw [subMats_nil] at hM'
    simp at hM'
  · simp only [subMats, List.mem_map] at hM'
    obtain ⟨j, -, rfl⟩ := hM'
    simp

lemma subMats_primrec : Primrec subMats := by
  have hbody : Primrec₂ fun (M : List (List ℚ)) (j : ℕ) =>
      M.tail.map fun s => cutAt s j := by
    have h : Primrec fun q : List (List ℚ) × ℕ => q.1.tail.map fun s => cutAt s q.2 := by
      refine Primrec.list_map (Primrec.list_tail.comp Primrec.fst) ?_
      have h2 : Primrec fun z : (List (List ℚ) × ℕ) × List ℚ => cutAt z.2 z.1.2 :=
        cutAt_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
      exact h2.to₂
    exact h.to₂
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.list_headI)) hbody

lemma detCombine_primrec : Primrec₂ detCombine := by
  have hbody : Primrec₂ fun (p : List (List ℚ) × List ℚ) (j : ℕ) =>
      (if j % 2 = 0 then (1 : ℚ) else -1) * (p.1.headI.getD j 0) * (p.2.getD j 0) := by
    have hsign : Primrec fun q : (List (List ℚ) × List ℚ) × ℕ =>
        (if q.2 % 2 = 0 then (1 : ℚ) else -1) :=
      Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
        (Primrec.const 0)) (Primrec.const 1) (Primrec.const (-1))
    have hhead : Primrec fun q : (List (List ℚ) × List ℚ) × ℕ =>
        (q.1.1.headI.getD q.2 0) :=
      (Primrec.list_getD (0 : ℚ)).comp
        (Primrec.list_headI.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
    have hds : Primrec fun q : (List (List ℚ) × List ℚ) × ℕ => (q.1.2.getD q.2 0) :=
      (Primrec.list_getD (0 : ℚ)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact (ratMul_prim.comp (ratMul_prim.comp hsign hhead) hds).to₂
  have hsum : Primrec fun p : List (List ℚ) × List ℚ =>
      ((List.range p.2.length).map fun j =>
        (if j % 2 = 0 then (1 : ℚ) else -1) * (p.1.headI.getD j 0) * (p.2.getD j 0)).sum :=
    ProjectionPrimrec.ratSum_primrec.comp
      (Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)) hbody)
  have hif : Primrec fun p : List (List ℚ) × List ℚ => detCombine p.1 p.2 :=
    Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 0))
      (Primrec.const 1) hsum
  exact hif.to₂

/-- **The raw determinant is primitive recursive.** -/
theorem detOf_primrec : Primrec detOf := by
  refine Primrec.nat_omega_rec' detOf (m := List.length) (l := subMats)
    (g := fun M ds => some (detCombine M ds))
    Primrec.list_length subMats_primrec
    ((Primrec.option_some.comp detCombine_primrec).to₂) subMats_ord ?_
  intro M
  rw [detCombine_subMats]

/-! ## Primitive-recursive combinators used throughout

Every raw definition below is a `List.range` map or a sum of one, so these lemmas carry
almost all of the computability plumbing. -/

lemma ratSub_prim : Primrec₂ fun q r : ℚ => q - r :=
  (ratAdd_prim.comp Primrec.fst (ratMul_prim.comp (Primrec.const (-1)) Primrec.snd)).of_eq
    fun p => by ring

lemma ratNeg_prim : Primrec fun q : ℚ => -q :=
  (ratMul_prim.comp (Primrec.const (-1)) Primrec.id).of_eq fun q => by
    show (-1 : ℚ) * q = -q
    ring

/-- A sum over `List.range`, uniformly in the bound and the summand. -/
lemma sum_range_primrec {α : Type} [Primcodable α] {n : α → ℕ} {g : α → ℕ → ℚ}
    (hn : Primrec n) (hg : Primrec₂ g) :
    Primrec fun a => ((List.range (n a)).map (g a)).sum :=
  ProjectionPrimrec.ratSum_primrec.comp (Primrec.list_map (Primrec.list_range.comp hn) hg)

/-- A list built by `List.range`, uniformly in the bound and the entry. -/
lemma map_range_primrec {α σ : Type} [Primcodable α] [Primcodable σ] {n : α → ℕ}
    {g : α → ℕ → σ} (hn : Primrec n) (hg : Primrec₂ g) :
    Primrec fun a => (List.range (n a)).map (g a) :=
  Primrec.list_map (Primrec.list_range.comp hn) hg

/-- Membership in a list of naturals is a primitive recursive relation. -/
lemma mem_natList_prim : PrimrecRel fun (i : ℕ) (l : List ℕ) => i ∈ l := by
  have h : PrimrecRel fun (i : ℕ) (l : List ℕ) => l.idxOf i < l.length :=
    Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.fst Primrec.snd)
      (Primrec.list_length.comp Primrec.snd)
  exact h.of_eq fun i l => List.idxOf_lt_length_iff

/-! ## List identities the raw/structured bridge runs on -/

/-- A list built by `List.ofFn`, read as a list built by `List.range`. -/
lemma ofFn_eq_map_range {α : Type*} {n : ℕ} (f : Fin n → α) (g : ℕ → α)
    (h : ∀ i : Fin n, f i = g (i : ℕ)) : List.ofFn f = (List.range n).map g := by
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h _

/-- A map over `List.finRange`, read as a map over `List.range`. -/
lemma map_finRange_eq {α : Type*} (n : ℕ) (f : Fin n → α) (g : ℕ → α)
    (h : ∀ i : Fin n, f i = g (i : ℕ)) :
    (List.finRange n).map f = (List.range n).map g := by
  refine List.ext_getElem (by simp) ?_
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  exact h _

lemma map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  rw [map_finRange_eq n Fin.val id fun _ => rfl, List.map_id]

/-- Reading back an entry of a mapped list. -/
lemma getD_map {α β : Type*} (f : α → β) (l : List α) (dv : β) {j : ℕ} (hj : j < l.length) :
    (l.map f).getD j dv = f (l.get ⟨j, hj⟩) := by
  have h : j < (l.map f).length := by simpa using hj
  rw [List.getD_eq_getElem _ _ h, List.getElem_map]
  rfl

/-- `filter` then `map` is one `filterMap`, which is the form `Primrec.listFilterMap`
consumes. -/
lemma filter_map_eq_filterMap {α β : Type*} (p : α → Bool) (f : α → β) (L : List α) :
    (L.filter p).map f = L.filterMap (fun x => if p x then some (f x) else none) := by
  induction L with
  | nil => rfl
  | cons a t ih => by_cases h : p a <;> simp [List.filter_cons, h, ih]

/-! ## Row surgery on a raw matrix

`Matrix.adjugate` is a determinant of a row-replaced matrix, so the raw pipeline needs a raw
`updateRow`.  `setRow` is written positionally rather than with `List.set` so that the
agreement lemma is an `ofFn_eq_map_range` and nothing more. -/

/-- The `i`-th standard basis row of length `n`. -/
def unitRow (n i : ℕ) : List ℚ := (List.range n).map fun t => if t = i then 1 else 0

/-- The raw matrix `G` with its `j`-th row replaced by `v`. -/
def setRow (G : List (List ℚ)) (j : ℕ) (v : List ℚ) : List (List ℚ) :=
  (List.range G.length).map fun r => if r = j then v else G.getD r []

/-- **The adjugate of a raw rational matrix.** -/
def adjOf (G : List (List ℚ)) (i j : ℕ) : ℚ := detOf (setRow G j (unitRow G.length i))

lemma unitRow_eq {n : ℕ} (i : Fin n) :
    unitRow n (i : ℕ) = List.ofFn (Pi.single i (1 : ℚ)) := by
  refine (ofFn_eq_map_range _ _ fun c => ?_).symm
  rw [Pi.single_apply]
  by_cases h : c = i
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hc => h (Fin.ext hc))]

lemma setRow_matList {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (j : Fin n) (v : Fin n → ℚ) :
    setRow (matList A) (j : ℕ) (List.ofFn v) = matList (A.updateRow j v) := by
  have hlen : (matList A).length = n := length_matList A
  have hget : ∀ r : Fin n, (matList A).getD (r : ℕ) [] = List.ofFn fun c => A r c := by
    intro r
    simp only [matList]
    rw [getD_ofFn _ _ r.isLt]
  refine Eq.symm ?_
  simp only [matList, setRow, List.length_ofFn]
  refine ofFn_eq_map_range
    (fun i : Fin n => List.ofFn fun c : Fin n => A.updateRow j v i c)
    (fun r : ℕ => if r = (j : ℕ) then List.ofFn v
      else (List.ofFn fun i : Fin n => List.ofFn fun c : Fin n => A i c).getD r [])
    fun r => ?_
  by_cases h : r = j
  · subst h
    rw [if_pos rfl]
    exact congrArg List.ofFn (funext fun c => by rw [Matrix.updateRow_self])
  · rw [if_neg (fun hc => h (Fin.ext hc))]
    rw [show (List.ofFn fun x : Fin n => List.ofFn fun c : Fin n => A x c).getD (r : ℕ) []
        = List.ofFn (fun c => A r c) from hget r]
    exact congrArg List.ofFn (funext fun c => by rw [Matrix.updateRow_ne h])

/-- **The raw adjugate is the adjugate.** -/
lemma adjOf_matList {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    adjOf (matList A) (i : ℕ) (j : ℕ) = A.adjugate i j := by
  simp only [adjOf, length_matList]
  rw [unitRow_eq i, setRow_matList, detOf_matList, Matrix.adjugate_apply]

lemma unitRow_primrec {α : Type} [Primcodable α] {n i : α → ℕ} (hn : Primrec n)
    (hi : Primrec i) : Primrec fun a => unitRow (n a) (i a) := by
  refine map_range_primrec hn ?_
  have h : Primrec fun q : α × ℕ => if q.2 = i q.1 then (1 : ℚ) else 0 :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (hi.comp Primrec.fst))
      (Primrec.const 1) (Primrec.const 0)
  exact h.to₂

lemma setRow_primrec {α : Type} [Primcodable α] {G : α → List (List ℚ)} {j : α → ℕ}
    {v : α → List ℚ} (hG : Primrec G) (hj : Primrec j) (hv : Primrec v) :
    Primrec fun a => setRow (G a) (j a) (v a) := by
  refine map_range_primrec (Primrec.list_length.comp hG) ?_
  have h : Primrec fun q : α × ℕ =>
      if q.2 = j q.1 then v q.1 else (G q.1).getD q.2 [] :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (hj.comp Primrec.fst))
      (hv.comp Primrec.fst)
      ((Primrec.list_getD ([] : List ℚ)).comp (hG.comp Primrec.fst) Primrec.snd)
  exact h.to₂

lemma adjOf_primrec {α : Type} [Primcodable α] {G : α → List (List ℚ)} {i j : α → ℕ}
    (hG : Primrec G) (hi : Primrec i) (hj : Primrec j) :
    Primrec fun a => adjOf (G a) (i a) (j a) :=
  detOf_primrec.comp
    (setRow_primrec hG hj (unitRow_primrec (Primrec.list_length.comp hG) hi))

/-! ## A face and its affine piece, on raw data

`PolyhedralProjection.Face` is a base vertex together with a list of further vertices, both
functions on `Fin d`.  Flattened, a face is a `List ℚ` and a `List (List ℚ)`, and its
piece — the `det⁻¹ • adjugate` solve — is the run of definitions below. -/

/-- The face's `j`-th spanning direction, coordinate `i`. -/
def dirOf (b : List ℚ) (r : List (List ℚ)) (j i : ℕ) : ℚ :=
  (r.getD j []).getD i 0 - b.getD i 0

/-- The `(j, l)` entry of the face's Gram matrix. -/
def gramEntry (d : ℕ) (b : List ℚ) (r : List (List ℚ)) (j l : ℕ) : ℚ :=
  ((List.range d).map fun i => dirOf b r j i * dirOf b r l i).sum

/-- The face's Gram matrix. -/
def gramMat (d : ℕ) (b : List ℚ) (r : List (List ℚ)) : List (List ℚ) :=
  (List.range r.length).map fun j =>
    (List.range r.length).map fun l => gramEntry d b r j l

/-- The `(j, l)` entry of the inverse Gram matrix, as `adjugate / det`. -/
def gramInvEntry (d : ℕ) (b : List ℚ) (r : List (List ℚ)) (j l : ℕ) : ℚ :=
  adjOf (gramMat d b r) j l / detOf (gramMat d b r)

/-- The `(i, a)` entry of the linear part of the face's candidate map. -/
def coefEntry (d : ℕ) (b : List ℚ) (r : List (List ℚ)) (i a : ℕ) : ℚ :=
  ((List.range r.length).map fun j =>
    dirOf b r j i *
      ((List.range r.length).map fun l =>
        gramInvEntry d b r j l * dirOf b r l a).sum).sum

/-- **The face's affine piece for coordinate `i`**, already in the compiler's syntax. -/
def pieceOf (d : ℕ) (b : List ℚ) (r : List (List ℚ)) (i : ℕ) :
    ProjectionCompiler.AffineForm :=
  ((List.range d).map fun a => coefEntry d b r i a,
    b.getD i 0 - ((List.range d).map fun a => coefEntry d b r i a * b.getD a 0).sum)

/-- A face's base vertex, flattened. -/
def faceBase {d : ℕ} (Φ : PolyhedralProjection.Face d) : List ℚ := List.ofFn Φ.base

/-- A face's further vertices, flattened. -/
def faceRest {d : ℕ} (Φ : PolyhedralProjection.Face d) : List (List ℚ) :=
  Φ.rest.map List.ofFn

@[simp] lemma length_faceRest {d : ℕ} (Φ : PolyhedralProjection.Face d) :
    (faceRest Φ).length = Φ.dim := by
  simp [faceRest, PolyhedralProjection.Face.dim]

lemma dirOf_eq {d : ℕ} (Φ : PolyhedralProjection.Face d) (j : Fin Φ.dim) (i : Fin d) :
    dirOf (faceBase Φ) (faceRest Φ) (j : ℕ) (i : ℕ) = Φ.dirQ j i := by
  have hj : (j : ℕ) < Φ.rest.length := j.isLt
  simp only [dirOf, faceBase, faceRest]
  rw [getD_map _ _ _ hj, getD_ofFn _ _ i.isLt, getD_ofFn _ _ i.isLt]
  rfl

lemma gramEntry_eq {d : ℕ} (Φ : PolyhedralProjection.Face d) (j l : Fin Φ.dim) :
    gramEntry d (faceBase Φ) (faceRest Φ) (j : ℕ) (l : ℕ) = Φ.gramQ j l := by
  simp only [gramEntry]
  show _ = ∑ i, Φ.dirQ j i * Φ.dirQ l i
  refine sum_range_eq_univ _ _ fun i => ?_
  rw [dirOf_eq, dirOf_eq]

lemma gramMat_eq {d : ℕ} (Φ : PolyhedralProjection.Face d) :
    gramMat d (faceBase Φ) (faceRest Φ) = matList Φ.gramQ := by
  simp only [gramMat, matList, length_faceRest]
  refine (ofFn_eq_map_range _ _ fun j => ?_).symm
  refine ofFn_eq_map_range _ _ fun l => ?_
  exact (gramEntry_eq Φ j l).symm

lemma gramInvEntry_eq {d : ℕ} (Φ : PolyhedralProjection.Face d) (j l : Fin Φ.dim) :
    gramInvEntry d (faceBase Φ) (faceRest Φ) (j : ℕ) (l : ℕ) = Φ.gramInvQ j l := by
  simp only [gramInvEntry, gramMat_eq]
  rw [adjOf_matList, detOf_matList]
  show _ = ((Φ.gramQ.det)⁻¹ • Φ.gramQ.adjugate) j l
  rw [Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

lemma coefEntry_eq {d : ℕ} (Φ : PolyhedralProjection.Face d) (i a : Fin d) :
    coefEntry d (faceBase Φ) (faceRest Φ) (i : ℕ) (a : ℕ) = Φ.coefQ i a := by
  simp only [coefEntry, length_faceRest]
  show _ = ∑ j, Φ.dirQ j i * ∑ l, Φ.gramInvQ j l * Φ.dirQ l a
  refine sum_range_eq_univ _ _ fun j => ?_
  rw [dirOf_eq]
  refine congrArg₂ _ rfl ?_
  refine sum_range_eq_univ _ _ fun l => ?_
  rw [gramInvEntry_eq, dirOf_eq]

lemma pieceOf_eq {d : ℕ} (Φ : PolyhedralProjection.Face d) (i : Fin d) :
    pieceOf d (faceBase Φ) (faceRest Φ) (i : ℕ)
      = (List.ofFn (Φ.piece i).coeff, (Φ.piece i).const) := by
  have hcoeff : (List.range d).map (fun a => coefEntry d (faceBase Φ) (faceRest Φ) (i : ℕ) a)
      = List.ofFn (Φ.piece i).coeff :=
    (ofFn_eq_map_range _ _ fun a => (coefEntry_eq Φ i a).symm).symm
  have hconst : (faceBase Φ).getD (i : ℕ) 0
      - ((List.range d).map fun a =>
          coefEntry d (faceBase Φ) (faceRest Φ) (i : ℕ) a * (faceBase Φ).getD a 0).sum
      = (Φ.piece i).const := by
    show _ = Φ.base i - ∑ a, Φ.coefQ i a * Φ.base a
    have hb : (faceBase Φ).getD (i : ℕ) 0 = Φ.base i := by
      simp only [faceBase]; rw [getD_ofFn _ _ i.isLt]
    rw [hb]
    refine congrArg₂ _ rfl ?_
    refine sum_range_eq_univ _ _ fun a => ?_
    have hb' : (faceBase Φ).getD (a : ℕ) 0 = Φ.base a := by
      simp only [faceBase]; rw [getD_ofFn _ _ a.isLt]
    rw [coefEntry_eq, hb']
  simp only [pieceOf]
  rw [hcoeff, hconst]

/-! ### The face constructions are primitive recursive -/

lemma dirOf_primrec {α : Type} [Primcodable α] {b : α → List ℚ} {r : α → List (List ℚ)}
    {j i : α → ℕ} (hb : Primrec b) (hr : Primrec r) (hj : Primrec j) (hi : Primrec i) :
    Primrec fun a => dirOf (b a) (r a) (j a) (i a) :=
  ratSub_prim.comp
    ((Primrec.list_getD (0 : ℚ)).comp ((Primrec.list_getD ([] : List ℚ)).comp hr hj) hi)
    ((Primrec.list_getD (0 : ℚ)).comp hb hi)

lemma gramEntry_primrec {α : Type} [Primcodable α] {d : α → ℕ} {b : α → List ℚ}
    {r : α → List (List ℚ)} {j l : α → ℕ} (hd : Primrec d) (hb : Primrec b)
    (hr : Primrec r) (hj : Primrec j) (hl : Primrec l) :
    Primrec fun a => gramEntry (d a) (b a) (r a) (j a) (l a) := by
  refine sum_range_primrec hd ?_
  have h : Primrec fun q : α × ℕ =>
      dirOf (b q.1) (r q.1) (j q.1) q.2 * dirOf (b q.1) (r q.1) (l q.1) q.2 :=
    ratMul_prim.comp
      (dirOf_primrec (hb.comp Primrec.fst) (hr.comp Primrec.fst) (hj.comp Primrec.fst)
        Primrec.snd)
      (dirOf_primrec (hb.comp Primrec.fst) (hr.comp Primrec.fst) (hl.comp Primrec.fst)
        Primrec.snd)
  exact h.to₂

lemma gramMat_primrec {α : Type} [Primcodable α] {d : α → ℕ} {b : α → List ℚ}
    {r : α → List (List ℚ)} (hd : Primrec d) (hb : Primrec b) (hr : Primrec r) :
    Primrec fun a => gramMat (d a) (b a) (r a) := by
  refine map_range_primrec (Primrec.list_length.comp hr) ?_
  have h : Primrec fun q : α × ℕ =>
      (List.range (r q.1).length).map fun l => gramEntry (d q.1) (b q.1) (r q.1) q.2 l := by
    refine map_range_primrec (Primrec.list_length.comp (hr.comp Primrec.fst)) ?_
    have h2 : Primrec fun z : (α × ℕ) × ℕ =>
        gramEntry (d z.1.1) (b z.1.1) (r z.1.1) z.1.2 z.2 :=
      gramEntry_primrec (hd.comp (Primrec.fst.comp Primrec.fst))
        (hb.comp (Primrec.fst.comp Primrec.fst)) (hr.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact h2.to₂
  exact h.to₂

lemma gramInvEntry_primrec {α : Type} [Primcodable α] {d : α → ℕ} {b : α → List ℚ}
    {r : α → List (List ℚ)} {j l : α → ℕ} (hd : Primrec d) (hb : Primrec b)
    (hr : Primrec r) (hj : Primrec j) (hl : Primrec l) :
    Primrec fun a => gramInvEntry (d a) (b a) (r a) (j a) (l a) :=
  ratDiv_prim.comp (adjOf_primrec (gramMat_primrec hd hb hr) hj hl)
    (detOf_primrec.comp (gramMat_primrec hd hb hr))

lemma coefEntry_primrec {α : Type} [Primcodable α] {d : α → ℕ} {b : α → List ℚ}
    {r : α → List (List ℚ)} {i a' : α → ℕ} (hd : Primrec d) (hb : Primrec b)
    (hr : Primrec r) (hi : Primrec i) (ha : Primrec a') :
    Primrec fun a => coefEntry (d a) (b a) (r a) (i a) (a' a) := by
  refine sum_range_primrec (Primrec.list_length.comp hr) ?_
  have hinner : Primrec fun q : α × ℕ =>
      ((List.range (r q.1).length).map fun l =>
        gramInvEntry (d q.1) (b q.1) (r q.1) q.2 l
          * dirOf (b q.1) (r q.1) l (a' q.1)).sum := by
    refine sum_range_primrec (Primrec.list_length.comp (hr.comp Primrec.fst)) ?_
    have h2 : Primrec fun z : (α × ℕ) × ℕ =>
        gramInvEntry (d z.1.1) (b z.1.1) (r z.1.1) z.1.2 z.2
          * dirOf (b z.1.1) (r z.1.1) z.2 (a' z.1.1) :=
      ratMul_prim.comp
        (gramInvEntry_primrec (hd.comp (Primrec.fst.comp Primrec.fst))
          (hb.comp (Primrec.fst.comp Primrec.fst)) (hr.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (dirOf_primrec (hb.comp (Primrec.fst.comp Primrec.fst))
          (hr.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
          (ha.comp (Primrec.fst.comp Primrec.fst)))
    exact h2.to₂
  have h : Primrec fun q : α × ℕ =>
      dirOf (b q.1) (r q.1) q.2 (i q.1) *
        ((List.range (r q.1).length).map fun l =>
          gramInvEntry (d q.1) (b q.1) (r q.1) q.2 l
            * dirOf (b q.1) (r q.1) l (a' q.1)).sum :=
    ratMul_prim.comp
      (dirOf_primrec (hb.comp Primrec.fst) (hr.comp Primrec.fst) Primrec.snd
        (hi.comp Primrec.fst)) hinner
  exact h.to₂

lemma pieceOf_primrec {α : Type} [Primcodable α] {d : α → ℕ} {b : α → List ℚ}
    {r : α → List (List ℚ)} {i : α → ℕ} (hd : Primrec d) (hb : Primrec b)
    (hr : Primrec r) (hi : Primrec i) :
    Primrec fun a => pieceOf (d a) (b a) (r a) (i a) := by
  have hcoeff : Primrec fun a =>
      (List.range (d a)).map fun x => coefEntry (d a) (b a) (r a) (i a) x := by
    refine map_range_primrec hd ?_
    have h : Primrec fun q : α × ℕ => coefEntry (d q.1) (b q.1) (r q.1) (i q.1) q.2 :=
      coefEntry_primrec (hd.comp Primrec.fst) (hb.comp Primrec.fst) (hr.comp Primrec.fst)
        (hi.comp Primrec.fst) Primrec.snd
    exact h.to₂
  have hsum : Primrec fun a =>
      ((List.range (d a)).map fun x =>
        coefEntry (d a) (b a) (r a) (i a) x * (b a).getD x 0).sum := by
    refine sum_range_primrec hd ?_
    have h : Primrec fun q : α × ℕ =>
        coefEntry (d q.1) (b q.1) (r q.1) (i q.1) q.2 * (b q.1).getD q.2 0 :=
      ratMul_prim.comp
        (coefEntry_primrec (hd.comp Primrec.fst) (hb.comp Primrec.fst) (hr.comp Primrec.fst)
          (hi.comp Primrec.fst) Primrec.snd)
        ((Primrec.list_getD (0 : ℚ)).comp (hb.comp Primrec.fst) Primrec.snd)
    exact h.to₂
  exact Primrec.pair hcoeff
    (ratSub_prim.comp ((Primrec.list_getD (0 : ℚ)).comp hb hi) hsum)


/-! ## The face enumeration on raw data

`PolyhedralCoverage.faceList` pairs each vertex with each sublist of the vertex list.  The
raw form is the same enumeration one level down, over `List (List ℚ)`, and the two agree
once the vertices are flattened.  `List.sublists_map` is the whole of the bridge: taking
sublists commutes with flattening each vertex. -/

/-- The enumerated faces, as raw base/rest pairs. -/
def faceListOf (verts : List (List ℚ)) : List (List ℚ × List (List ℚ)) :=
  (verts.map fun b => verts.sublists.map fun r => (b, r)).flatten

/-- **The raw enumeration is the structured one, flattened.** -/
lemma faceListOf_eq {d : ℕ} (K : RationalPolytope d) :
    faceListOf (K.verts.map List.ofFn)
      = (PolyhedralCoverage.faceList K).map fun Φ => (faceBase Φ, faceRest Φ) := by
  rw [faceListOf, PolyhedralCoverage.faceList, List.map_flatten, List.sublists_map,
    List.map_map, List.map_map]
  refine congrArg List.flatten (List.map_congr_left fun b _ => ?_)
  simp only [Function.comp_apply, List.map_map]
  rfl

/-- The raw enumeration has one entry per enumerated face. -/
lemma length_faceListOf {d : ℕ} (K : RationalPolytope d) :
    (faceListOf (K.verts.map List.ofFn)).length = nf K := by
  rw [faceListOf_eq, List.length_map]

/-- Reading back the `i`-th raw face. -/
lemma getD_faceListOf {d : ℕ} (K : RationalPolytope d) (i : Fin (nf K)) :
    (faceListOf (K.verts.map List.ofFn)).getD (i : ℕ) ([], [])
      = (faceBase ((PolyhedralCoverage.faceList K).get i),
          faceRest ((PolyhedralCoverage.faceList K).get i)) := by
  rw [faceListOf_eq]
  have hlt : (i : ℕ) < ((PolyhedralCoverage.faceList K).map
      fun Φ => (faceBase Φ, faceRest Φ)).length := by simpa using i.isLt
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_map]
  rfl

lemma faceListOf_primrec : Primrec faceListOf := by
  have hinner : Primrec₂ fun (v : List (List ℚ)) (b : List ℚ) =>
      v.sublists.map fun r => (b, r) := by
    have h : Primrec fun z : List (List ℚ) × List ℚ =>
        z.1.sublists.map fun r => (z.2, r) :=
      Primrec.list_map (sublists_primrec.comp Primrec.fst)
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
    exact h.to₂
  exact Primrec.list_flatten.comp (Primrec.list_map Primrec.id hinner)

/-! ## The affine components on raw data

`ProjectorGenerator.comp K k i` is the `k`-th piece of the `i`-th enumerated face, and
`ProjectionBridge.ofGeom` is what puts it in the compiler's syntax.  Since `pieceOf` already
returns that syntax, the raw component is a lookup followed by `pieceOf`. -/

/-- The `i`-th affine component of the `k`-th coordinate, on raw data. -/
def compOf (d : ℕ) (verts : List (List ℚ)) (k i : ℕ) : ProjectionCompiler.AffineForm :=
  pieceOf d ((faceListOf verts).getD i ([], [])).1
    ((faceListOf verts).getD i ([], [])).2 k

/-- **The raw component is the structured one.** -/
lemma compOf_eq {d : ℕ} (K : RationalPolytope d) (k : Fin d) (i : Fin (nf K)) :
    compOf d (K.verts.map List.ofFn) (k : ℕ) (i : ℕ)
      = (List.ofFn (comp K k i).coeff, (comp K k i).const) := by
  rw [compOf, getD_faceListOf]
  exact pieceOf_eq ((PolyhedralCoverage.faceList K).get i) k

lemma compOf_primrec {α : Type} [Primcodable α] {d : α → ℕ} {verts : α → List (List ℚ)}
    {k i : α → ℕ} (hd : Primrec d) (hv : Primrec verts) (hk : Primrec k) (hi : Primrec i) :
    Primrec fun a => compOf (d a) (verts a) (k a) (i a) := by
  have hface : Primrec fun a => (faceListOf (verts a)).getD (i a) ([], []) :=
    (Primrec.list_getD ([], [])).comp (faceListOf_primrec.comp hv) hi
  exact pieceOf_primrec hd (Primrec.fst.comp hface) (Primrec.snd.comp hface) hk


/-! ## The constraint system on raw data

`mkCon` lays the ambient coefficient vector out through `coeffFn`, a three-way `dite` on
the position.  The raw form mirrors that `dite` over `List.range` rather than concatenating
three blocks: the positional shape is what `coeffFn` itself has, so the agreement lemma is
`ofFn_eq_map_range` applied to a case split, with no index arithmetic across appends. -/

/-- The ambient coefficient vector, raw, mirroring `coeffFn` position by position. -/
def coeffListOf (d m : ℕ) (xf lf : List ℚ) (cc : ℚ) : List ℚ :=
  (List.range (d + m + 1)).map fun t =>
    if t < d then xf.getD t 0 else if t < d + m then lf.getD (t - d) 0 else cc

/-- A constraint of the ambient system, raw. -/
def mkConOf (d m : ℕ) (xf lf : List ℚ) (cc b : ℚ) (s : Bool) : LinCon :=
  LinCon.of (coeffListOf d m xf lf cc) b s

/-- **The raw layout is the structured one.** -/
lemma coeffListOf_eq (d m : ℕ) (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc : ℚ) :
    coeffListOf d m (List.ofFn xf) (List.ofFn lf) cc
      = List.ofFn (coeffFn d m xf lf cc) := by
  simp only [coeffListOf]
  refine (ofFn_eq_map_range _ _ fun t => ?_).symm
  rw [coeffFn]
  by_cases h : (t : ℕ) < d
  · rw [dif_pos h, if_pos h, getD_ofFn _ _ h]
  · rw [dif_neg h, if_neg h]
    by_cases h' : (t : ℕ) < d + m
    · rw [dif_pos h', if_pos h', getD_ofFn _ _ (by omega)]
    · rw [dif_neg h', if_neg h']

/-- **The raw constraint is the structured one.** -/
lemma mkConOf_eq (d m : ℕ) (xf : Fin d → ℚ) (lf : Fin m → ℚ) (cc b : ℚ) (s : Bool) :
    mkConOf d m (List.ofFn xf) (List.ofFn lf) cc b s = mkCon d m xf lf cc b s := by
  rw [mkConOf, mkCon, coeffListOf_eq]

lemma coeffListOf_primrec {α : Type} [Primcodable α] {d m : α → ℕ} {xf lf : α → List ℚ}
    {cc : α → ℚ} (hd : Primrec d) (hm : Primrec m) (hx : Primrec xf) (hl : Primrec lf)
    (hc : Primrec cc) :
    Primrec fun a => coeffListOf (d a) (m a) (xf a) (lf a) (cc a) := by
  refine map_range_primrec
    (Primrec.nat_add.comp (Primrec.nat_add.comp hd hm) (Primrec.const 1)) ?_
  have h : Primrec fun q : α × ℕ =>
      if q.2 < d q.1 then (xf q.1).getD q.2 0
      else if q.2 < d q.1 + m q.1 then (lf q.1).getD (q.2 - d q.1) 0 else cc q.1 := by
    refine Primrec.ite (Primrec.nat_lt.comp Primrec.snd (hd.comp Primrec.fst))
      ((Primrec.list_getD (0 : ℚ)).comp (hx.comp Primrec.fst) Primrec.snd) ?_
    refine Primrec.ite
      (Primrec.nat_lt.comp Primrec.snd
        (Primrec.nat_add.comp (hd.comp Primrec.fst) (hm.comp Primrec.fst)))
      ?_ (hc.comp Primrec.fst)
    exact (Primrec.list_getD (0 : ℚ)).comp (hl.comp Primrec.fst)
      (Primrec.nat_sub.comp Primrec.snd (hd.comp Primrec.fst))
  exact h.to₂

lemma mkConOf_primrec {α : Type} [Primcodable α] {d m : α → ℕ} {xf lf : α → List ℚ}
    {cc b : α → ℚ} {sg : α → Bool} (hd : Primrec d) (hm : Primrec m) (hx : Primrec xf)
    (hl : Primrec lf) (hc : Primrec cc) (hb : Primrec b) (hs : Primrec sg) :
    Primrec fun a => mkConOf (d a) (m a) (xf a) (lf a) (cc a) (b a) (sg a) :=
  (coeffListOf_primrec hd hm hx hl hc).pair (hb.pair hs)

/-! ### The blocks

The zero and unit coefficient blocks are `List.range` maps, so `map_range_primrec` carries
them; both membership tests are decided by `mem_natList_prim`. -/

/-- The all-zero block of length `n`. -/
def zeroBlock (n : ℕ) : List ℚ := (List.range n).map fun _ => 0

lemma zeroBlock_eq (n : ℕ) : zeroBlock n = List.ofFn (0 : Fin n → ℚ) :=
  (ofFn_eq_map_range _ _ fun _ => rfl).symm

lemma zeroBlock_primrec {α : Type} [Primcodable α] {n : α → ℕ} (hn : Primrec n) :
    Primrec fun a => zeroBlock (n a) :=
  map_range_primrec hn ((Primrec.const (0 : ℚ)).to₂)

/-- The `j`-th vertex, raw. -/
def vtxOf (verts : List (List ℚ)) (j : ℕ) : List ℚ := verts.getD j []

lemma vtxOf_eq {d : ℕ} (K : RationalPolytope d) (j : Fin (nv K)) :
    vtxOf (K.verts.map List.ofFn) (j : ℕ) = List.ofFn (vtx K j) := by
  rw [vtxOf, getD_map _ _ _ (by simpa using j.isLt)]
  rfl

lemma vtxOf_primrec {α : Type} [Primcodable α] {verts : α → List (List ℚ)} {j : α → ℕ}
    (hv : Primrec verts) (hj : Primrec j) : Primrec fun a => vtxOf (verts a) (j a) :=
  (Primrec.list_getD ([] : List ℚ)).comp hv hj

/-- The Gram constant, raw. -/
def gramOf (d : ℕ) (verts : List (List ℚ)) (j i : ℕ) : ℚ :=
  ((List.range d).map fun a => (vtxOf verts j).getD a 0 * (vtxOf verts i).getD a 0).sum

lemma gramOf_eq {d : ℕ} (K : RationalPolytope d) (j i : Fin (nv K)) :
    gramOf d (K.verts.map List.ofFn) (j : ℕ) (i : ℕ) = gram K j i := by
  rw [gramOf, gram]
  refine sum_range_eq_univ _ _ fun a => ?_
  rw [vtxOf_eq, vtxOf_eq, getD_ofFn _ _ a.isLt, getD_ofFn _ _ a.isLt]

lemma gramOf_primrec {α : Type} [Primcodable α] {d : α → ℕ} {verts : α → List (List ℚ)}
    {j i : α → ℕ} (hd : Primrec d) (hv : Primrec verts) (hj : Primrec j)
    (hi : Primrec i) : Primrec fun a => gramOf (d a) (verts a) (j a) (i a) := by
  refine sum_range_primrec hd ?_
  have h : Primrec fun q : α × ℕ =>
      (vtxOf (verts q.1) (j q.1)).getD q.2 0 * (vtxOf (verts q.1) (i q.1)).getD q.2 0 :=
    ratMul_prim.comp
      ((Primrec.list_getD (0 : ℚ)).comp
        (vtxOf_primrec (hv.comp Primrec.fst) (hj.comp Primrec.fst)) Primrec.snd)
      ((Primrec.list_getD (0 : ℚ)).comp
        (vtxOf_primrec (hv.comp Primrec.fst) (hi.comp Primrec.fst)) Primrec.snd)
  exact h.to₂

/-! ### The six blocks, raw

Each block is the structured constraint with `List.ofFn` pushed inside, so each agreement
lemma is `mkConOf_eq` preceded by rewriting the two coefficient functions.  The strict flags
are copied verbatim: `conSupportOf` is strict on the support and `conUpperOf` is strict off
the upper set, exactly as in `ProjectorGenerator`. -/

/-- `Σ_j λ_j ≤ 1`, raw. -/
def conSumLeOf (d m : ℕ) : LinCon :=
  mkConOf d m (zeroBlock d) ((List.range m).map fun _ => 1) 0 1 false

/-- `−Σ_j λ_j ≤ −1`, raw. -/
def conSumGeOf (d m : ℕ) : LinCon :=
  mkConOf d m (zeroBlock d) ((List.range m).map fun _ => -1) 0 (-1) false

/-- `−λ_j ≤ 0`, raw. -/
def conNonnegOf (d m : ℕ) (j : ℕ) : LinCon :=
  mkConOf d m (zeroBlock d)
    ((List.range m).map fun j' => if j' = j then -1 else 0) 0 0 false

/-- The support block, raw: strict on the support. -/
def conSupportOf (d m : ℕ) (S : List ℕ) (j : ℕ) : LinCon :=
  if j ∈ S then
    mkConOf d m (zeroBlock d)
      ((List.range m).map fun j' => if j' = j then -1 else 0) 0 0 true
  else
    mkConOf d m (zeroBlock d)
      ((List.range m).map fun j' => if j' = j then 1 else 0) 0 0 false

/-- The residual upper bound at vertex `i`, raw. -/
def conVertLeOf (d : ℕ) (verts : List (List ℚ)) (i : ℕ) : LinCon :=
  mkConOf d verts.length (vtxOf verts i)
    ((List.range verts.length).map fun j => -gramOf d verts j i) (-1) 0 false

/-- The reverse residual bound on the support, raw. -/
def conVertGeOf (d : ℕ) (verts : List (List ℚ)) (S : List ℕ) (i : ℕ) : LinCon :=
  if i ∈ S then
    mkConOf d verts.length ((vtxOf verts i).map fun q => -q)
      ((List.range verts.length).map fun j => gramOf d verts j i) 1 0 false
  else
    mkConOf d verts.length (zeroBlock d) (zeroBlock verts.length) 0 0 false

/-- The upper-set block, raw: strict off the upper set. -/
def conUpperOf (d : ℕ) (verts : List (List ℚ)) (k : ℕ) (T : List ℕ) (i : ℕ) : LinCon :=
  if i ∈ T then
    mkConOf d verts.length ((compOf d verts k i).1.map fun q => -q)
      ((List.range verts.length).map fun j => (vtxOf verts j).getD k 0) 0
      (compOf d verts k i).2 false
  else
    mkConOf d verts.length (compOf d verts k i).1
      ((List.range verts.length).map fun j => -(vtxOf verts j).getD k 0) 0
      (-(compOf d verts k i).2) true

/-- **The system, raw.** -/
def systemOf (d : ℕ) (verts : List (List ℚ)) (k : ℕ) (S T : List ℕ) : List LinCon :=
  conSumLeOf d verts.length :: conSumGeOf d verts.length ::
    ((List.range verts.length).map (conNonnegOf d verts.length) ++
      (List.range verts.length).map (conSupportOf d verts.length S) ++
      (List.range verts.length).map (conVertLeOf d verts) ++
      (List.range verts.length).map (conVertGeOf d verts S) ++
      (List.range (faceListOf verts).length).map (conUpperOf d verts k T))

/-! ### Agreement -/

lemma length_vertexData {d : ℕ} (K : RationalPolytope d) :
    (K.verts.map List.ofFn).length = nv K := by simp

lemma map_neg_vtxOf {d : ℕ} (K : RationalPolytope d) (i : Fin (nv K)) :
    (vtxOf (K.verts.map List.ofFn) (i : ℕ)).map (fun q => -q)
      = List.ofFn fun a => -vtx K i a := by
  rw [vtxOf_eq]
  exact List.map_ofFn

lemma conSumLeOf_eq {d : ℕ} (K : RationalPolytope d) :
    conSumLeOf d (nv K) = conSumLe d (nv K) := by
  rw [conSumLeOf, conSumLe, zeroBlock_eq,
    show ((List.range (nv K)).map fun _ : ℕ => (1 : ℚ)) = List.ofFn (fun _ : Fin (nv K) => (1 : ℚ))
      from (ofFn_eq_map_range _ _ fun _ => rfl).symm, mkConOf_eq]

lemma conSumGeOf_eq {d : ℕ} (K : RationalPolytope d) :
    conSumGeOf d (nv K) = conSumGe d (nv K) := by
  rw [conSumGeOf, conSumGe, zeroBlock_eq,
    show ((List.range (nv K)).map fun _ : ℕ => (-1 : ℚ))
        = List.ofFn (fun _ : Fin (nv K) => (-1 : ℚ))
      from (ofFn_eq_map_range _ _ fun _ => rfl).symm, mkConOf_eq]

lemma conNonnegOf_eq {d : ℕ} (K : RationalPolytope d) (j : Fin (nv K)) :
    conNonnegOf d (nv K) (j : ℕ) = conNonneg d (nv K) j := by
  rw [conNonnegOf, conNonneg, zeroBlock_eq,
    show ((List.range (nv K)).map fun j' => if j' = (j : ℕ) then (-1 : ℚ) else 0)
        = List.ofFn (fun j' : Fin (nv K) => if j' = j then (-1 : ℚ) else 0)
      from (ofFn_eq_map_range _ _ fun j' => by
        by_cases h : j' = j
        · rw [if_pos h, if_pos (congrArg Fin.val h)]
        · rw [if_neg h, if_neg (fun hc => h (Fin.ext hc))]).symm, mkConOf_eq]

lemma conSupportOf_eq {d : ℕ} (K : RationalPolytope d) (S : List ℕ) (j : Fin (nv K)) :
    conSupportOf d (nv K) S (j : ℕ) = conSupport d (nv K) S j := by
  rw [conSupportOf, conSupport]
  by_cases h : (j : ℕ) ∈ S
  · rw [if_pos h, if_pos h, zeroBlock_eq,
      show ((List.range (nv K)).map fun j' => if j' = (j : ℕ) then (-1 : ℚ) else 0)
          = List.ofFn (fun j' : Fin (nv K) => if j' = j then (-1 : ℚ) else 0)
        from (ofFn_eq_map_range _ _ fun j' => by
          by_cases hj : j' = j
          · rw [if_pos hj, if_pos (congrArg Fin.val hj)]
          · rw [if_neg hj, if_neg (fun hc => hj (Fin.ext hc))]).symm, mkConOf_eq]
  · rw [if_neg h, if_neg h, zeroBlock_eq,
      show ((List.range (nv K)).map fun j' => if j' = (j : ℕ) then (1 : ℚ) else 0)
          = List.ofFn (fun j' : Fin (nv K) => if j' = j then (1 : ℚ) else 0)
        from (ofFn_eq_map_range _ _ fun j' => by
          by_cases hj : j' = j
          · rw [if_pos hj, if_pos (congrArg Fin.val hj)]
          · rw [if_neg hj, if_neg (fun hc => hj (Fin.ext hc))]).symm, mkConOf_eq]

lemma conVertLeOf_eq {d : ℕ} (K : RationalPolytope d) (i : Fin (nv K)) :
    conVertLeOf d (K.verts.map List.ofFn) (i : ℕ) = conVertLe K i := by
  rw [conVertLeOf, conVertLe, length_vertexData, vtxOf_eq,
    show ((List.range (nv K)).map fun j => -gramOf d (K.verts.map List.ofFn) j (i : ℕ))
        = List.ofFn (fun j : Fin (nv K) => -gram K j i)
      from (ofFn_eq_map_range _ _ fun j => by rw [gramOf_eq]).symm, mkConOf_eq]

lemma conVertGeOf_eq {d : ℕ} (K : RationalPolytope d) (S : List ℕ) (i : Fin (nv K)) :
    conVertGeOf d (K.verts.map List.ofFn) S (i : ℕ) = conVertGe K S i := by
  rw [conVertGeOf, conVertGe, length_vertexData]
  by_cases h : (i : ℕ) ∈ S
  · rw [if_pos h, if_pos h, map_neg_vtxOf,
      show ((List.range (nv K)).map fun j => gramOf d (K.verts.map List.ofFn) j (i : ℕ))
          = List.ofFn (fun j : Fin (nv K) => gram K j i)
        from (ofFn_eq_map_range _ _ fun j => by rw [gramOf_eq]).symm, mkConOf_eq]
  · rw [if_neg h, if_neg h, zeroBlock_eq, zeroBlock_eq, mkConOf_eq]

lemma conUpperOf_eq {d : ℕ} (K : RationalPolytope d) (k : Fin d) (T : List ℕ)
    (i : Fin (nf K)) :
    conUpperOf d (K.verts.map List.ofFn) (k : ℕ) T (i : ℕ) = conUpper K k T i := by
  have hc := compOf_eq K k i
  rw [conUpperOf, conUpper, length_vertexData, hc]
  by_cases h : (i : ℕ) ∈ T
  · rw [if_pos h, if_pos h,
      show (List.ofFn (comp K k i).coeff).map (fun q => -q)
          = List.ofFn (fun a => -(comp K k i).coeff a) from List.map_ofFn,
      show ((List.range (nv K)).map fun j => (vtxOf (K.verts.map List.ofFn) j).getD (k : ℕ) 0)
          = List.ofFn (fun j : Fin (nv K) => vtx K j k)
        from (ofFn_eq_map_range _ _ fun j => by
          rw [vtxOf_eq, getD_ofFn _ _ k.isLt]).symm, mkConOf_eq]
  · rw [if_neg h, if_neg h,
      show ((List.range (nv K)).map fun j =>
            -(vtxOf (K.verts.map List.ofFn) j).getD (k : ℕ) 0)
          = List.ofFn (fun j : Fin (nv K) => -vtx K j k)
        from (ofFn_eq_map_range _ _ fun j => by
          rw [vtxOf_eq, getD_ofFn _ _ k.isLt]).symm, mkConOf_eq]

/-- **The raw system is the structured one.** -/
lemma systemOf_eq {d : ℕ} (K : RationalPolytope d) (k : Fin d) (S T : List ℕ) :
    systemOf d (K.verts.map List.ofFn) (k : ℕ) S T = system K k S T := by
  rw [systemOf, system, length_vertexData, length_faceListOf]
  refine congrArg₂ List.cons (conSumLeOf_eq K) (congrArg₂ List.cons (conSumGeOf_eq K) ?_)
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_) ?_
  · exact (map_finRange_eq (nv K) _ _ fun j => (conNonnegOf_eq K j).symm).symm
  · exact (map_finRange_eq (nv K) _ _ fun j => (conSupportOf_eq K S j).symm).symm
  · exact (map_finRange_eq (nv K) _ _ fun i => (conVertLeOf_eq K i).symm).symm
  · exact (map_finRange_eq (nv K) _ _ fun i => (conVertGeOf_eq K S i).symm).symm
  · exact (map_finRange_eq (nf K) _ _ fun i => (conUpperOf_eq K k T i).symm).symm

/-! ## The family, the representation and the compiler

With the system in hand the rest is assembly.  The one step needing care is that
`projectorRep` indexes its groups by `Fin (family).length` and reads the family back with
`List.get`, while the raw form maps over the family itself; `repOfList_map` and
`groupOfList_map` are what reconcile the two, and `List.ofFn_get` is what says the family is
its own indexed enumeration. -/

/-- The candidate `(support, upper set)` pairs, raw. -/
def candidatePairsOf (verts : List (List ℚ)) : List (List ℕ × List ℕ) :=
  (List.range verts.length).sublists.flatMap fun S =>
    (List.range (faceListOf verts).length).sublists.map fun T => (S, T)

lemma candidatePairsOf_eq {d : ℕ} (K : RationalPolytope d) :
    candidatePairsOf (K.verts.map List.ofFn) = candidatePairs K := by
  rw [candidatePairsOf, candidatePairs, length_vertexData, length_faceListOf]

/-- **The computed family, raw.** -/
def projectorFamilyOf (d : ℕ) (verts : List (List ℚ)) (k : ℕ) : List (List ℕ) :=
  ((candidatePairsOf verts).filter fun ST =>
      feasible (d + verts.length + 1) (systemOf d verts k ST.1 ST.2)).map Prod.snd

lemma projectorFamilyOf_eq {d : ℕ} (K : RationalPolytope d) (k : Fin d) :
    projectorFamilyOf d (K.verts.map List.ofFn) (k : ℕ) = projectorFamily K k := by
  have hpred : (fun ST : List ℕ × List ℕ =>
        feasible (d + (K.verts.map List.ofFn).length + 1)
          (systemOf d (K.verts.map List.ofFn) (k : ℕ) ST.1 ST.2))
      = fun ST : List ℕ × List ℕ => feasible (d + nv K + 1) (system K k ST.1 ST.2) := by
    funext ST
    rw [length_vertexData, systemOf_eq]
  rw [projectorFamilyOf, projectorFamily, hpred, candidatePairsOf_eq]

/-- Filtering a range by membership is filtering the indexed enumeration. -/
private lemma filter_range_map_val (n : ℕ) (T : List ℕ) :
    (List.range n).filter (fun i => decide (i ∈ T))
      = ((List.finRange n).filter fun i : Fin n => decide ((i : ℕ) ∈ T)).map Fin.val := by
  rw [← map_val_finRange n]
  generalize (List.finRange n) = l
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases h : (a : ℕ) ∈ T <;> simp [List.filter_cons, h, ih]

/-- The index list of an upper set, raw. -/
def idxListOf (verts : List (List ℚ)) (T : List ℕ) : List ℕ :=
  (List.range (faceListOf verts).length).filter fun i => decide (i ∈ T)

lemma idxListOf_eq {d : ℕ} (K : RationalPolytope d) (T : List ℕ) :
    idxListOf (K.verts.map List.ofFn) T = (idxList K T).map Fin.val := by
  rw [idxListOf, idxList, length_faceListOf, filter_range_map_val]

lemma groupOfList_map {ι κ : Type*} (A : κ → ProjectionCompiler.AffineForm) (f : ι → κ)
    (l : List ι) : groupOfList A (l.map f) = groupOfList (fun i => A (f i)) l := by
  cases l with
  | nil => rfl
  | cons a t => simp [groupOfList, List.map_map, Function.comp_def]

lemma repOfList_map {ι κ : Type*} (G : κ → ProjectionCompiler.Group) (f : ι → κ)
    (l : List ι) : repOfList G (l.map f) = repOfList (fun i => G (f i)) l := by
  cases l with
  | nil => rfl
  | cons a t => simp [repOfList, List.map_map, Function.comp_def]

/-- A list is its own indexed enumeration. -/
private lemma self_eq_map_get {α : Type*} (l : List α) :
    l = (List.finRange l.length).map l.get := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.ofFn_eq_map]

/-- **The computed representation, raw.** -/
def projectorRepOf (d : ℕ) (verts : List (List ℚ)) (k : ℕ) : ProjectionCompiler.Rep :=
  repOfList
    (fun T : List ℕ => groupOfList (fun i : ℕ => compOf d verts k i) (idxListOf verts T))
    (projectorFamilyOf d verts k)

/-- **The raw representation is the structured one.** -/
lemma projectorRepOf_eq (F : ProjectionCompiler.Fragment)
    (K : RationalPolytope F.coords.length)
    (k : Fin F.coords.length) :
    projectorRepOf F.coords.length (K.verts.map List.ofFn) (k : ℕ) = projectorRep F K k := by
  have hgroup : ∀ T : List ℕ,
      groupOfList (fun i : ℕ => compOf F.coords.length (K.verts.map List.ofFn) (k : ℕ) i)
          (idxListOf (K.verts.map List.ofFn) T)
        = groupOfList (compForm F K k) (idxList K T) := by
    intro T
    rw [idxListOf_eq, groupOfList_map]
    refine congrArg (fun A => groupOfList A (idxList K T)) ?_
    funext i
    exact compOf_eq K k i
  rw [projectorRepOf, projectorRep, projectorFamilyOf_eq]
  conv_lhs => rw [self_eq_map_get (projectorFamily K k)]
  rw [repOfList_map]
  exact congrArg (fun G => repOfList G (List.finRange (projectorFamily K k).length))
    (funext fun j => hgroup _)

/-- The compiler, indexed by the fragment's *length* rather than by the fragment.  Only the
length is ever read, and carrying it as a `ℕ` keeps the effectiveness proof from
elaborating the whole chain at `List Sentence × List (List ℚ)`, where synthesising
`Primcodable` over the four-deep nest that `Rep` unfolds to is what exhausted the
elaborator. -/
def compileLen (len : ℕ) (verts : List (List ℚ)) : List ProjectionCompiler.Rep :=
  (List.range len).map fun k => projectorRepOf len verts k

/-- **The compiler.**  One representation per priced sentence, in the fragment's order. -/
def compileOf (coords : List Sentence) (verts : List (List ℚ)) :
    List ProjectionCompiler.Rep :=
  compileLen coords.length verts

/-! ## The representation a constraint schedule determines

`compileOf` is a total function of raw data, so it gives a `RegionRepresentation` for
*every* schedule, with no choice anywhere on its definitional path.  That is the whole
difference from `RationalConstraintSchedule.canonicalRepresentation`, which is
`noncomputable` because `ProjectionBridge.exists_repMap_mem` is an existence proof. -/

open ConstraintSchedule
open Workspace.Normativity.Contrib.ProjectionEnforcer

/-- **The representation a schedule's own data determines.**  A genuine construction:
`Classical.choose` appears nowhere on the path from `C` to this term. -/
def effectiveRepresentation (C : RationalConstraintSchedule) : RegionRepresentation C where
  reps := fun n => compileOf (C.coords n) (C.vertexData n)
  dflt := default
  reps_eval := by
    intro n φ hφ p
    have hlt : (C.coords n).idxOf φ < (C.coords n).length :=
      List.idxOf_lt_length_of_mem hφ
    have hrep : repAt (C.coords n) (compileOf (C.coords n) (C.vertexData n)) default φ
        = projectorRepOf (C.coords n).length (C.vertexData n) ((C.coords n).idxOf φ) := by
      rw [repAt, compileOf, compileLen, getD_map_range _ _ _ hlt]
    have hgen : projectorRepOf (C.coords n).length (C.vertexData n) ((C.coords n).idxOf φ)
        = projectorRep (C.fragment n) (C.region n) ⟨(C.coords n).idxOf φ, hlt⟩ :=
      projectorRepOf_eq (C.fragment n) (C.region n) ⟨(C.coords n).idxOf φ, hlt⟩
    rw [hrep, hgen, repEval_projectorRep]
    exact (ConstraintSchedule.target_mem (C.fragment n) (C.region n) p hφ).symm

@[simp] lemma reps_effectiveRepresentation (C : RationalConstraintSchedule) (n : ℕ) :
    (effectiveRepresentation C).reps n = compileOf (C.coords n) (C.vertexData n) := rfl

/-! ## Effectiveness

`groupOfList` and `repOfList` take a *function* as their first argument, and a function is
not `Primcodable`, so neither can appear directly in a `Primrec` statement.  Both are
however a `List.map` followed by a head/tail split, and that split is what the certificate
goes through. -/

/-- The head/tail split a group is. -/
def groupOfListL (L : List ProjectionCompiler.AffineForm) : ProjectionCompiler.Group :=
  ((L.head?).getD ([], 0), L.tail)

/-- The head/tail split a representation is. -/
def repOfListL (L : List ProjectionCompiler.Group) : ProjectionCompiler.Rep :=
  ((L.head?).getD (([], 0), []), L.tail)

lemma groupOfList_eq_L {ι : Type*} (A : ι → ProjectionCompiler.AffineForm) (l : List ι) :
    groupOfList A l = groupOfListL (l.map A) := by
  cases l <;> rfl

lemma repOfList_eq_L {ι : Type*} (G : ι → ProjectionCompiler.Group) (l : List ι) :
    repOfList G l = repOfListL (l.map G) := by
  cases l <;> rfl

lemma groupOfListL_primrec : Primrec groupOfListL :=
  (Primrec.option_getD.comp Primrec.list_head? (Primrec.const _)).pair Primrec.list_tail

lemma repOfListL_primrec : Primrec repOfListL :=
  (Primrec.option_getD.comp Primrec.list_head? (Primrec.const _)).pair Primrec.list_tail

/-- **The representation, as a map and two splits.**  The form the certificate consumes. -/
lemma projectorRepOf_eq_L (d : ℕ) (verts : List (List ℚ)) (k : ℕ) :
    projectorRepOf d verts k
      = repOfListL ((projectorFamilyOf d verts k).map fun T =>
          groupOfListL ((idxListOf verts T).map fun i => compOf d verts k i)) := by
  rw [projectorRepOf, repOfList_eq_L]
  exact congrArg repOfListL (List.map_congr_left fun T _ => groupOfList_eq_L _ _)

/-- Filtering by a predicate that depends on the argument.  `Primrec.listFilter` fixes its
predicate, so it is unusable here; `Primrec.listFilterMap` is parametrised. -/
private lemma list_filter_prim {α β : Type*} [Primcodable α] [Primcodable β]
    {l : α → List β} {q : α → β → Bool} (hl : Primrec l) (hq : Primrec₂ q) :
    Primrec fun a => (l a).filter (q a) := by
  have hfm : Primrec fun a =>
      (l a).filterMap fun b => bif q a b then some b else none := by
    refine Primrec.listFilterMap hl ?_
    exact Primrec.cond hq (Primrec.option_some.comp₂ Primrec₂.right) (Primrec.const none)
  refine hfm.of_eq fun a => ?_
  induction l a with
  | nil => rfl
  | cons b t ih =>
    rw [List.filter_cons, List.filterMap_cons]
    cases hqb : q a b <;> simp [hqb, ih]

/-! ### The blocks are effective -/

lemma conSumLeOf_primrec {α : Type} [Primcodable α] {d m : α → ℕ}
    (hd : Primrec d) (hm : Primrec m) : Primrec fun a => conSumLeOf (d a) (m a) :=
  mkConOf_primrec hd hm (zeroBlock_primrec hd)
    (map_range_primrec hm ((Primrec.const (1 : ℚ)).to₂)) (Primrec.const 0)
    (Primrec.const 1) (Primrec.const false)

lemma conSumGeOf_primrec {α : Type} [Primcodable α] {d m : α → ℕ}
    (hd : Primrec d) (hm : Primrec m) : Primrec fun a => conSumGeOf (d a) (m a) :=
  mkConOf_primrec hd hm (zeroBlock_primrec hd)
    (map_range_primrec hm ((Primrec.const (-1 : ℚ)).to₂)) (Primrec.const 0)
    (Primrec.const (-1)) (Primrec.const false)

/-- The unit block `fun j' => if j' = j then c else 0`, effective in `j`. -/
private lemma unitBlock_primrec {α : Type} [Primcodable α] {m : α → ℕ} {j : α → ℕ}
    (c : ℚ) (hm : Primrec m) (hj : Primrec j) :
    Primrec fun a => (List.range (m a)).map fun j' => if j' = j a then c else 0 := by
  refine map_range_primrec hm ?_
  have h : Primrec fun q : α × ℕ => if q.2 = j q.1 then c else (0 : ℚ) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (hj.comp Primrec.fst))
      (Primrec.const c) (Primrec.const 0)
  exact h.to₂

lemma conNonnegOf_primrec {α : Type} [Primcodable α] {d m j : α → ℕ}
    (hd : Primrec d) (hm : Primrec m) (hj : Primrec j) :
    Primrec fun a => conNonnegOf (d a) (m a) (j a) :=
  mkConOf_primrec hd hm (zeroBlock_primrec hd) (unitBlock_primrec (-1) hm hj)
    (Primrec.const 0) (Primrec.const 0) (Primrec.const false)

lemma conSupportOf_primrec {α : Type} [Primcodable α] {d m j : α → ℕ}
    {S : α → List ℕ} (hd : Primrec d) (hm : Primrec m) (hS : Primrec S)
    (hj : Primrec j) : Primrec fun a => conSupportOf (d a) (m a) (S a) (j a) := by
  refine Primrec.ite (mem_natList_prim.comp hj hS) ?_ ?_
  · exact mkConOf_primrec hd hm (zeroBlock_primrec hd) (unitBlock_primrec (-1) hm hj)
      (Primrec.const 0) (Primrec.const 0) (Primrec.const true)
  · exact mkConOf_primrec hd hm (zeroBlock_primrec hd) (unitBlock_primrec 1 hm hj)
      (Primrec.const 0) (Primrec.const 0) (Primrec.const false)

lemma conVertLeOf_primrec {α : Type} [Primcodable α] {d : α → ℕ}
    {verts : α → List (List ℚ)} {i : α → ℕ} (hd : Primrec d) (hv : Primrec verts)
    (hi : Primrec i) : Primrec fun a => conVertLeOf (d a) (verts a) (i a) := by
  have hlen : Primrec fun a => (verts a).length := Primrec.list_length.comp hv
  refine mkConOf_primrec hd hlen (vtxOf_primrec hv hi) ?_ (Primrec.const (-1))
    (Primrec.const 0) (Primrec.const false)
  refine map_range_primrec hlen ?_
  have h : Primrec fun q : α × ℕ => -gramOf (d q.1) (verts q.1) q.2 (i q.1) :=
    ratNeg_prim.comp (gramOf_primrec (hd.comp Primrec.fst) (hv.comp Primrec.fst)
      Primrec.snd (hi.comp Primrec.fst))
  exact h.to₂

lemma conVertGeOf_primrec {α : Type} [Primcodable α] {d : α → ℕ}
    {verts : α → List (List ℚ)} {S : α → List ℕ} {i : α → ℕ} (hd : Primrec d)
    (hv : Primrec verts) (hS : Primrec S) (hi : Primrec i) :
    Primrec fun a => conVertGeOf (d a) (verts a) (S a) (i a) := by
  have hlen : Primrec fun a => (verts a).length := Primrec.list_length.comp hv
  refine Primrec.ite (mem_natList_prim.comp hi hS) ?_ ?_
  · refine mkConOf_primrec hd hlen ?_ ?_ (Primrec.const 1) (Primrec.const 0)
      (Primrec.const false)
    · exact Primrec.list_map (vtxOf_primrec hv hi) (ratNeg_prim.comp₂ Primrec₂.right)
    · refine map_range_primrec hlen ?_
      have h : Primrec fun q : α × ℕ => gramOf (d q.1) (verts q.1) q.2 (i q.1) :=
        gramOf_primrec (hd.comp Primrec.fst) (hv.comp Primrec.fst) Primrec.snd
          (hi.comp Primrec.fst)
      exact h.to₂
  · exact mkConOf_primrec hd hlen (zeroBlock_primrec hd) (zeroBlock_primrec hlen)
      (Primrec.const 0) (Primrec.const 0) (Primrec.const false)

lemma conUpperOf_primrec {α : Type} [Primcodable α] {d : α → ℕ}
    {verts : α → List (List ℚ)} {k : α → ℕ} {T : α → List ℕ} {i : α → ℕ}
    (hd : Primrec d) (hv : Primrec verts) (hk : Primrec k) (hT : Primrec T)
    (hi : Primrec i) : Primrec fun a => conUpperOf (d a) (verts a) (k a) (T a) (i a) := by
  have hlen : Primrec fun a => (verts a).length := Primrec.list_length.comp hv
  have hcomp : Primrec fun a => compOf (d a) (verts a) (k a) (i a) :=
    compOf_primrec hd hv hk hi
  have hvk : Primrec fun a =>
      (List.range (verts a).length).map fun j => (vtxOf (verts a) j).getD (k a) 0 := by
    refine map_range_primrec hlen ?_
    have h : Primrec fun q : α × ℕ => (vtxOf (verts q.1) q.2).getD (k q.1) 0 :=
      (Primrec.list_getD (0 : ℚ)).comp
        (vtxOf_primrec (hv.comp Primrec.fst) Primrec.snd) (hk.comp Primrec.fst)
    exact h.to₂
  have hvkneg : Primrec fun a =>
      (List.range (verts a).length).map fun j => -(vtxOf (verts a) j).getD (k a) 0 := by
    refine map_range_primrec hlen ?_
    have h : Primrec fun q : α × ℕ => -(vtxOf (verts q.1) q.2).getD (k q.1) 0 :=
      ratNeg_prim.comp ((Primrec.list_getD (0 : ℚ)).comp
        (vtxOf_primrec (hv.comp Primrec.fst) Primrec.snd) (hk.comp Primrec.fst))
    exact h.to₂
  refine Primrec.ite (mem_natList_prim.comp hi hT) ?_ ?_
  · exact mkConOf_primrec hd hlen
      (Primrec.list_map (Primrec.fst.comp hcomp) (ratNeg_prim.comp₂ Primrec₂.right))
      hvk (Primrec.const 0) (Primrec.snd.comp hcomp) (Primrec.const false)
  · exact mkConOf_primrec hd hlen (Primrec.fst.comp hcomp) hvkneg (Primrec.const 0)
      (ratNeg_prim.comp (Primrec.snd.comp hcomp)) (Primrec.const true)

/-- **The system is effective.** -/
lemma systemOf_primrec {α : Type} [Primcodable α] {d : α → ℕ}
    {verts : α → List (List ℚ)} {k : α → ℕ} {S T : α → List ℕ} (hd : Primrec d)
    (hv : Primrec verts) (hk : Primrec k) (hS : Primrec S) (hT : Primrec T) :
    Primrec fun a => systemOf (d a) (verts a) (k a) (S a) (T a) := by
  have hlen : Primrec fun a => (verts a).length := Primrec.list_length.comp hv
  have hnf : Primrec fun a => (faceListOf (verts a)).length :=
    Primrec.list_length.comp (faceListOf_primrec.comp hv)
  have h1 : Primrec fun a => (List.range (verts a).length).map
      (conNonnegOf (d a) (verts a).length) :=
    map_range_primrec hlen (conNonnegOf_primrec (hd.comp Primrec.fst)
      (hlen.comp Primrec.fst) Primrec.snd).to₂
  have h2 : Primrec fun a => (List.range (verts a).length).map
      (conSupportOf (d a) (verts a).length (S a)) :=
    map_range_primrec hlen (conSupportOf_primrec (hd.comp Primrec.fst)
      (hlen.comp Primrec.fst) (hS.comp Primrec.fst) Primrec.snd).to₂
  have h3 : Primrec fun a => (List.range (verts a).length).map
      (conVertLeOf (d a) (verts a)) :=
    map_range_primrec hlen (conVertLeOf_primrec (hd.comp Primrec.fst)
      (hv.comp Primrec.fst) Primrec.snd).to₂
  have h4 : Primrec fun a => (List.range (verts a).length).map
      (conVertGeOf (d a) (verts a) (S a)) :=
    map_range_primrec hlen (conVertGeOf_primrec (hd.comp Primrec.fst)
      (hv.comp Primrec.fst) (hS.comp Primrec.fst) Primrec.snd).to₂
  have h5 : Primrec fun a => (List.range (faceListOf (verts a)).length).map
      (conUpperOf (d a) (verts a) (k a) (T a)) :=
    map_range_primrec hnf (conUpperOf_primrec (hd.comp Primrec.fst)
      (hv.comp Primrec.fst) (hk.comp Primrec.fst) (hT.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.list_cons.comp (conSumLeOf_primrec hd hlen)
    (Primrec.list_cons.comp (conSumGeOf_primrec hd hlen)
      (Primrec.list_append.comp (Primrec.list_append.comp
        (Primrec.list_append.comp (Primrec.list_append.comp h1 h2) h3) h4) h5))

/-! ### The family and the compiler are effective -/

lemma candidatePairsOf_primrec : Primrec candidatePairsOf := by
  have houter : Primrec fun verts : List (List ℚ) => (List.range verts.length).sublists :=
    sublists_primrec.comp (Primrec.list_range.comp Primrec.list_length)
  have hinner : Primrec₂ fun (verts : List (List ℚ)) (S : List ℕ) =>
      (List.range (faceListOf verts).length).sublists.map fun T => (S, T) := by
    have h : Primrec fun q : List (List ℚ) × List ℕ =>
        (List.range (faceListOf q.1).length).sublists.map fun T => (q.2, T) :=
      Primrec.list_map
        (sublists_primrec.comp (Primrec.list_range.comp
          (Primrec.list_length.comp (faceListOf_primrec.comp Primrec.fst))))
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
    exact h.to₂
  exact Primrec.list_flatMap houter hinner

lemma projectorFamilyOf_primrec {α : Type} [Primcodable α] {d : α → ℕ}
    {verts : α → List (List ℚ)} {k : α → ℕ} (hd : Primrec d) (hv : Primrec verts)
    (hk : Primrec k) : Primrec fun a => projectorFamilyOf (d a) (verts a) (k a) := by
  have hlen : Primrec fun a => (verts a).length := Primrec.list_length.comp hv
  have hq : Primrec₂ fun (a : α) (ST : List ℕ × List ℕ) =>
      feasible (d a + (verts a).length + 1)
        (systemOf (d a) (verts a) (k a) ST.1 ST.2) := by
    have hdim : Primrec fun q : α × (List ℕ × List ℕ) =>
        d q.1 + (verts q.1).length + 1 :=
      Primrec.nat_add.comp
        (Primrec.nat_add.comp (hd.comp Primrec.fst) (hlen.comp Primrec.fst))
        (Primrec.const 1)
    have hsys : Primrec fun q : α × (List ℕ × List ℕ) =>
        systemOf (d q.1) (verts q.1) (k q.1) q.2.1 q.2.2 :=
      systemOf_primrec (hd.comp Primrec.fst) (hv.comp Primrec.fst) (hk.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    exact (feasible_primrec_comp hdim hsys).to₂
  exact Primrec.list_map (list_filter_prim (candidatePairsOf_primrec.comp hv) hq)
    (Primrec.snd.comp₂ Primrec₂.right)

lemma idxListOf_primrec {α : Type} [Primcodable α] {verts : α → List (List ℚ)}
    {T : α → List ℕ} (hv : Primrec verts) (hT : Primrec T) :
    Primrec fun a => idxListOf (verts a) (T a) := by
  refine list_filter_prim
    (Primrec.list_range.comp
      (Primrec.list_length.comp (faceListOf_primrec.comp hv))) ?_
  have h : Primrec fun q : α × ℕ =>
      if (T q.1).idxOf q.2 < (T q.1).length then true else false :=
    Primrec.ite
      (Primrec.nat_lt.comp
        (Primrec.list_idxOf.comp Primrec.snd (hT.comp Primrec.fst))
        (Primrec.list_length.comp (hT.comp Primrec.fst)))
      (Primrec.const true) (Primrec.const false)
  refine Primrec₂.of_eq h.to₂ fun a i => ?_
  by_cases hm : i ∈ T a
  · rw [if_pos (List.idxOf_lt_length_iff.mpr hm)]
    simp [hm]
  · rw [if_neg fun hc => hm (List.idxOf_lt_length_iff.mp hc)]
    simp [hm]

set_option maxHeartbeats 4000000 in
lemma projectorRepOf_primrec {α : Type} [Primcodable α] {d : α → ℕ}
    {verts : α → List (List ℚ)} {k : α → ℕ} (hd : Primrec d) (hv : Primrec verts)
    (hk : Primrec k) : Primrec fun a => projectorRepOf (d a) (verts a) (k a) := by
  have hbody : Primrec₂ fun (a : α) (T : List ℕ) =>
      groupOfListL ((idxListOf (verts a) T).map
        fun i => compOf (d a) (verts a) (k a) i) := by
    have h : Primrec fun q : α × List ℕ =>
        groupOfListL ((idxListOf (verts q.1) q.2).map
          fun i => compOf (d q.1) (verts q.1) (k q.1) i) := by
      refine groupOfListL_primrec.comp (Primrec.list_map
        (idxListOf_primrec (hv.comp Primrec.fst) Primrec.snd) ?_)
      exact (compOf_primrec (hd.comp (Primrec.fst.comp Primrec.fst))
        (hv.comp (Primrec.fst.comp Primrec.fst))
        (hk.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
    exact h.to₂
  refine (repOfListL_primrec.comp
    (Primrec.list_map (projectorFamilyOf_primrec hd hv hk) hbody)).of_eq fun a => ?_
  exact (projectorRepOf_eq_L (d a) (verts a) (k a)).symm

set_option maxHeartbeats 4000000 in
/-- **The length-indexed compiler is primitive recursive.** -/
theorem compileLen_primrec : Primrec₂ compileLen := by
  have hproj : Primrec₂ fun (q : ℕ × List (List ℚ)) (k : ℕ) =>
      projectorRepOf q.1 q.2 k :=
    (projectorRepOf_primrec
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have h : Primrec fun q : ℕ × List (List ℚ) =>
      (List.range q.1).map fun k => projectorRepOf q.1 q.2 k :=
    map_range_primrec Primrec.fst hproj
  exact h.to₂

/-- **The compiler is primitive recursive.**  The certificate
`RegionRepresentation.Effective` asks for, and the last one outstanding. -/
theorem compileOf_primrec : Primrec₂ compileOf :=
  compileLen_primrec.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd

/-- **The representation is effective.**  This discharges what had been the one
implementation artifact left in the theorem of record. -/
def effectiveRepresentation_effective (C : RationalConstraintSchedule) :
    (effectiveRepresentation C).Effective where
  compile := compileOf
  compileComputable := compileOf_primrec
  reps_eq := fun _ => rfl

end Workspace.Normativity.Contrib.EffectiveRepresentation
