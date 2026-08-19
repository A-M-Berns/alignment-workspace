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

end Workspace.Normativity.Contrib.EffectiveRepresentation
