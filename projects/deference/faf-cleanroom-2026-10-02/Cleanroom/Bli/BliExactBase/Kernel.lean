import Cleanroom.Bli.BliExactBase.Linked
import Cleanroom.Bli.BliLinkage.AttemptA.InstanceB2

/-!
# `bli-exact-base` — K7d: the world-weight kernel (Route W), by shape

**The self-reference, and its dissolution.** On a segment day `n` the linked base must price its
*own* day-`(n+1)` cell literals at the superbelief's cell masses. Those literals are quotation
atoms whose index nests the program code of the base's cell quote
(`spliceCellSentence H t … m c r = Formula.atom (litIdx code m c r)`, `spliceCellSentence_eq_atom`),
and the code is whatever `BooleanQuoteCode.ofComputable` chooses for the table `t` — so a table
defined "as the marginal of a mixture that sets its own literal atoms" would be defined in terms
of its own program code: a fixed point that only the recursion theorem, with the table
*uniformly computable in the code*, could supply (the mandate's "data by choice, not
computation" rules that out; findings F16). This module takes a different route. The kernel
mixture on day `n` overrides, inside every world, **every stage-fresh atom of the day-`(n+1)`
cell-literal shape** `litIdx e (n+1) c r` for the three segment coordinates `c` and the two cells
`r` — for every code `e` at once (`LitShape`, `slice`). The table is then a function of the stage,
the day and the index only; it never reads its own code; and the base's own literals are among
the overridden atoms, because every atom of that shape is fresh at stage `n` (`litIdx_fresh`: the
quotation input `⟨e, ⟨n+1, ⟨c, r⟩⟩⟩` exceeds `n`, and `theoremDP`'s stage `n` names only events
`≤ n`, `QuoteLane.quotationClaimCode_fresh_of_lt`). The price of this obliviousness is dogmatism
about *other* programs' day-`(n+1)` literals of the same shape, small sentences the stage has not
decided; `Linked.linked_literal_dogmatic` shows the base's own uncharged literal is already
priced `0` by any such package, so no non-dogmatism that the package could have had is lost.

**The kernel.** Candidates: the eight tables `tbl3 x y z` over `segmentIndex = [⌜freshCoord⌝,
⌜⊥⌝, ⌜⊤⌝]` with cells in `{0, 1}` (`kStates`; the state system `kSystem rep01`). Two are charged,
`1/2` each: `q₁ = tbl3 1 0 1` (`freshCoord` in the `1` cell) and `q₀ = tbl3 0 0 1`. Their slices
are the given family `W` of stage-consistent worlds, each world overridden to the candidate's
pattern, with `freshCoord` set true (`q₁`) or false (`q₀`); the day-`n` market `kMix` is the
uniform mixture over the two slices. By construction: a stage mixture on every algebra
(`kMix_coherentOn`), the partition (`kMix_partitionAt`), faith at every segment coordinate on
every candidate (`kMix_faith`), `SpuriousEntails` and `ValuesAtRep` on the grid
(`kSystem_spuriousEntails`, `kSystem_valuesAtRep`), two distinct charged candidates
(`kMix_two_charged`), `freshCoord` at `1/2`. The no-net-update identity is then `bli-linkage`'s
engine `nnu_day` applied, at the splice, in `Segment.lean`.
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB
open Cleanroom.Bli.BliLinkage.AttemptA.B2 (rep01)

namespace Kernel

/-! ## The literal atoms, by shape -/

/-- The atom index of the day-`m` cell literal of the coordinate with code `c` and cell `r`
under the cell quote code `e`: FAF's quotation atom of the folded input `⟨e, ⟨m, ⟨c, r⟩⟩⟩`.
Source: FAF `quoteAtom`, `quotationClaimCode`; mandate § 3 (a)
Kind: D
Fidelity: exact -/
noncomputable def litIdx (e m c r : ℕ) : ℕ :=
  quotationClaimCode universalQuotePos universalQuoteNeg (Nat.pair e (Nat.pair m (Nat.pair c r)))

/-- The splice's cell literal is the atom `litIdx code m c r` of its cell quote code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceCellSentence_eq_atom (H : ℕ) (t : ℕ → Sentence → ℚ) (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (m c r : ℕ) :
    spliceCellSentence H t round hround m c r =
      Formula.atom (litIdx (spliceCellQuote H t round hround).code m c r) := rfl

/-- `litIdx` is injective in all four arguments.
Source: none: infrastructure (`Nat.pair_eq_pair`)
Kind: L
Fidelity: n/a -/
lemma litIdx_inj {e m c r e' m' c' r' : ℕ} (h : litIdx e m c r = litIdx e' m' c' r') :
    e = e' ∧ m = m' ∧ c = c' ∧ r = r' := by
  simpa [litIdx, quotationClaimCode, Nat.pair_eq_pair] using h

/-- **Every atom of day-`m` literal shape is fresh at every stage `n < m` of `paperDP T`**,
whatever its code: the quotation input exceeds `n`.
Source: `QuoteLane.quotationClaimCode_fresh_of_lt`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem litIdx_fresh (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] {n m : ℕ} (hnm : n < m)
    (e c r : ℕ) : ∀ φ ∈ (paperDP T).D n, litIdx e m c r ∉ sentenceAtomCodes φ :=
  quotationClaimCode_fresh_of_lt T
    (lt_of_lt_of_le hnm ((Nat.left_le_pair m _).trans (Nat.right_le_pair e _)))

/-- The atom index of `freshCoord`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev freshCode : ℕ := freshAtomCode freshFamily (Nat.pair 0 0)

/-- `freshCoord` is the atom `freshCode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshCoord_eq_atom : freshCoord = Formula.atom freshCode := rfl

/-- No literal atom (tag `2`) is `freshCode` (tag `19`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma litIdx_ne_freshCode (e m c r : ℕ) : litIdx e m c r ≠ freshCode := by
  intro h
  have := congrArg (fun a => a.unpair.1) h
  simp [litIdx, quotationClaimCode, freshFamily, cleanroomBaseTag] at this

/-- `freshCoord` is not `⊥`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshCoord_ne_falsum : freshCoord ≠ (⊥ : Sentence) := fun h => by
  have := congrArg sentenceAtomCodes h
  simp [freshCoord_eq_atom] at this

/-- `freshCoord` is not `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshCoord_ne_verum : freshCoord ≠ (⊤ : Sentence) := fun h => by
  have := congrArg sentenceAtomCodes h
  simp [freshCoord_eq_atom] at this

/-- The three segment codes are pairwise distinct (`⌜freshCoord⌝ ≠ ⌜⊥⌝`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma encode_freshCoord_ne_falsum :
    Encodable.encode freshCoord ≠ Encodable.encode (⊥ : Sentence) :=
  fun h => freshCoord_ne_falsum (Encodable.encode_injective h)

/-- `⌜freshCoord⌝ ≠ ⌜⊤⌝`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma encode_freshCoord_ne_verum :
    Encodable.encode freshCoord ≠ Encodable.encode (⊤ : Sentence) :=
  fun h => freshCoord_ne_verum (Encodable.encode_injective h)

/-! ## The candidate tables and the state system -/

/-- The candidate table `(x, y, z)`: the cells of `freshCoord`, `⊥`, `⊤`, in the order of
`segmentIndex`.
Source: mandate § 4 (the candidates over the segment index)
Kind: D
Fidelity: exact -/
def tbl3 (x y z : ℕ) : List (ℕ × ℕ) :=
  [(Encodable.encode freshCoord, x), (Encodable.encode (⊥ : Sentence), y),
    (Encodable.encode (⊤ : Sentence), z)]

/-- `tbl3` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tbl3_inj {x y z x' y' z' : ℕ} (h : tbl3 x y z = tbl3 x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  simpa [tbl3] using h

/-- The entry of a candidate table at `⌜freshCoord⌝`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_tbl3_fresh (x y z : ℕ) : entryOf (Encodable.encode freshCoord) (tbl3 x y z) = some x := by
  simp [tbl3, entryOf]

/-- The entry of a candidate table at `⌜⊥⌝`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_tbl3_bot (x y z : ℕ) :
    entryOf (Encodable.encode (⊥ : Sentence)) (tbl3 x y z) = some y := by
  simp [tbl3, entryOf, freshCoord_ne_falsum]

/-- The entry of a candidate table at `⌜⊤⌝`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma entryOf_tbl3_top (x y z : ℕ) :
    entryOf (Encodable.encode (⊤ : Sentence)) (tbl3 x y z) = some z := by
  simp [tbl3, entryOf, freshCoord_ne_verum]

/-- **The eight candidate codes**: the tables over the segment index with cells in `{0, 1}`.
Source: mandate § 4 ("make `S.states` your finite candidate set, not the whole grid")
Kind: D
Fidelity: exact -/
def kStates : Finset ℕ :=
  ((range 2 ×ˢ range 2 ×ˢ range 2).image fun p : ℕ × ℕ × ℕ =>
    Encodable.encode (tbl3 p.1 p.2.1 p.2.2))

/-- Membership in the candidate set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_kStates {q : ℕ} :
    q ∈ kStates ↔ ∃ x y z, x ≤ 1 ∧ y ≤ 1 ∧ z ≤ 1 ∧ q = Encodable.encode (tbl3 x y z) := by
  simp only [kStates, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨x, y, z, ⟨hx, hy, hz⟩, rfl⟩
    exact ⟨x, y, z, by omega, by omega, by omega, rfl⟩
  · rintro ⟨x, y, z, hx, hy, hz, rfl⟩
    exact ⟨x, y, z, ⟨by omega, by omega, by omega⟩, rfl⟩

/-- A sum over the candidate codes is a sum over the eight triples.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_kStates (f : ℕ → ℝ) :
    ∑ q ∈ kStates, f q =
      ∑ x ∈ range 2, ∑ y ∈ range 2, ∑ z ∈ range 2, f (Encodable.encode (tbl3 x y z)) := by
  unfold kStates
  rw [Finset.sum_image]
  · simp only [Finset.sum_product]
  · intro p _ p' _ h
    obtain ⟨h1, h2, h3⟩ := tbl3_inj (Encodable.encode_injective h)
    exact Prod.ext h1 (Prod.ext h2 h3)

/-- **The kernel's state system** with representatives `rep`: the eight candidates on every day,
valuing a coordinate at the representative of the cell its table lists (`0` off the table). The
`actual` field is the constant candidate `tbl3 1 0 1`; nothing in the package reads it (`nnu_day`
does not) — the realized rounded pattern of the splice is `Segment.linked_actual_cells` on
`n + 1 < H` and `Segment.spliceCell` at the boundary, where it may differ.
Source: mandate § 4; bli-found `StateSentence.b2StateSystem` (the valuation rule)
Kind: D
Fidelity: exact -/
noncomputable def kSystem (rep : ℕ → ℕ → ℚ) : StateSystem where
  states _ := kStates
  val m q φ := ((((entryOf (Encodable.encode φ) (tableOfCode q)).map (rep m)).getD 0 : ℚ) : ℝ)
  actual _ := Encodable.encode (tbl3 1 0 1)
  actual_mem _ := mem_kStates.2 ⟨1, 0, 1, le_rfl, zero_le_one, le_rfl, rfl⟩

/-- The kernel system's value at `freshCoord`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kSystem_val_fresh (rep : ℕ → ℕ → ℚ) (m x y z : ℕ) :
    (kSystem rep).val m (Encodable.encode (tbl3 x y z)) freshCoord = (rep m x : ℝ) := by
  simp [kSystem, entryOf_tbl3_fresh]

/-- The kernel system's value at `⊥`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kSystem_val_bot (rep : ℕ → ℕ → ℚ) (m x y z : ℕ) :
    (kSystem rep).val m (Encodable.encode (tbl3 x y z)) ⊥ = (rep m y : ℝ) := by
  simp [kSystem, entryOf_tbl3_bot]

/-- The kernel system's value at `⊤`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kSystem_val_top (rep : ℕ → ℕ → ℚ) (m x y z : ℕ) :
    (kSystem rep).val m (Encodable.encode (tbl3 x y z)) ⊤ = (rep m z : ℝ) := by
  simp [kSystem, entryOf_tbl3_top]

/-- **A cell family whose literals are the shape atoms of the code `e`** — `spliceCF` at its own
cell quote code (`spliceCF_litAtoms`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def LitAtoms {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (e : ℕ) : Prop :=
  ∀ m φ r, C.literal m φ r = Formula.atom (litIdx e m (Encodable.encode φ) r)

/-- The splice's cell family has the shape atoms of its cell quote code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceCF_litAtoms (H : ℕ) (t : ℕ → Sentence → ℚ) (round : ℕ → ℚ → ℕ)
    (hround : Computable fun p : ℕ × ℚ => round p.1 p.2) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) :
    LitAtoms (spliceCF H t round hround cells hcells rep) (spliceCellQuote H t round hround).code :=
  fun _ _ _ => rfl

/-- The cell literal under any cell quote code `q` is the atom `litIdx q.code m c r`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceCellSentenceQ_eq_atom (H : ℕ) (t : ℕ → Sentence → ℚ) (round : ℕ → ℚ → ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t round)) (m c r : ℕ) :
    spliceCellSentenceQ H t round q m c r = Formula.atom (litIdx q.code m c r) := rfl

/-- The splice's cell family under any cell quote code `q` has the shape atoms of `q`
(repair round 2: the code as a parameter).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceCFq_litAtoms (H : ℕ) (t : ℕ → Sentence → ℚ) (round : ℕ → ℚ → ℕ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H t round)) (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, round m x ∈ cells m) (rep : ℕ → ℕ → ℚ) :
    LitAtoms (spliceCFq H t round q cells hcells rep) q.code :=
  fun _ _ _ => rfl

/-- A world holds the state sentence of `tbl3 x y z` iff it holds the three literals.
Source: none: infrastructure (bli-linkage `InstanceB2.holds_stateOf_tbl`)
Kind: L
Fidelity: n/a -/
lemma holds_stateOf_tbl3 {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (m x y z : ℕ) (v : PCWorld) :
    v.Holds (stateOf C m (Encodable.encode (tbl3 x y z))) ↔
      v.Holds (C.literal m freshCoord x) ∧ v.Holds (C.literal m ⊥ y) ∧
        v.Holds (C.literal m ⊤ z) := by
  rw [holds_stateOf, tableOfCode_encode]
  simp [tbl3]

/-- **`SpuriousEntails` on the kernel grid**: a candidate with a literal it does not list at one of
the three coordinates entails the candidate with that coordinate's cell replaced (propositional;
no freshness needed).
Source: bli-linkage `InstanceB2.fixedStates_spuriousEntails` (the same shape, three coordinates)
Kind: L
Fidelity: n/a -/
theorem kSystem_spuriousEntails {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (rep : ℕ → ℕ → ℚ)
    (n : ℕ) :
    SpuriousEntails (stateOf C) C.literal (kSystem rep) segmentIndex twoCells n := by
  intro q hq c hc r hr hne
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := mem_kStates.1 (by simpa [kSystem] using hq)
  have hr1 : r ≤ 1 := by
    simp only [twoCells, Finset.mem_insert, Finset.mem_singleton] at hr; omega
  rw [tableOfCode_encode] at hne
  simp only [segmentIndex, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · rw [entryOf_tbl3_fresh] at hne
    have hxr : x ≠ r := fun h => hne (by rw [h])
    refine ⟨Encodable.encode (tbl3 r y z), ?_, ?_, ?_⟩
    · show _ ∈ kStates
      exact mem_kStates.2 ⟨r, y, z, hr1, hy, hz, rfl⟩
    · intro h; rw [Encodable.encode_inj] at h; exact hxr (tbl3_inj h).1.symm
    · intro v hs hl
      rw [holds_stateOf_tbl3] at hs ⊢
      rw [sentenceOfCode_encode] at hl
      exact ⟨hl, hs.2⟩
  · rw [entryOf_tbl3_bot] at hne
    have hyr : y ≠ r := fun h => hne (by rw [h])
    refine ⟨Encodable.encode (tbl3 x r z), ?_, ?_, ?_⟩
    · show _ ∈ kStates
      exact mem_kStates.2 ⟨x, r, z, hx, hr1, hz, rfl⟩
    · intro h; rw [Encodable.encode_inj] at h; exact hyr (tbl3_inj h).2.1.symm
    · intro v hs hl
      rw [holds_stateOf_tbl3] at hs ⊢
      rw [sentenceOfCode_encode] at hl
      exact ⟨hs.1, hl, hs.2.2⟩
  · rw [entryOf_tbl3_top] at hne
    have hzr : z ≠ r := fun h => hne (by rw [h])
    refine ⟨Encodable.encode (tbl3 x y r), ?_, ?_, ?_⟩
    · show _ ∈ kStates
      exact mem_kStates.2 ⟨x, y, r, hx, hy, hr1, rfl⟩
    · intro h; rw [Encodable.encode_inj] at h; exact hzr (tbl3_inj h).2.2.symm
    · intro v hs hl
      rw [holds_stateOf_tbl3] at hs ⊢
      rw [sentenceOfCode_encode] at hl
      exact ⟨hs.1, hs.2.1, hl⟩

/-- **`ValuesAtRep` on the kernel grid** for a cell family with cells `twoCells` and
representatives `rep01`: every candidate values every segment coordinate at the representative
of the cell it lists.
Source: bli-linkage `InstanceB2.fixedSystem_valuesAtRep`
Kind: L
Fidelity: n/a -/
theorem kSystem_valuesAtRep {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲)
    (hcells : ∀ m, C.cells m = twoCells m) (hrep : ∀ m r, C.rep m r = rep01 m r) (n : ℕ) :
    ValuesAtRep C (kSystem rep01) segmentIndex n := by
  intro q hq c hc
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := mem_kStates.1 (by simpa [kSystem] using hq)
  have h2 : ∀ a, a ≤ 1 → a ∈ C.cells (n + 1) := fun a ha => by
    rw [hcells]; simp only [twoCells, Finset.mem_insert, Finset.mem_singleton]; omega
  simp only [segmentIndex, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨x, h2 x hx, by rw [tableOfCode_encode, entryOf_tbl3_fresh],
      by rw [sentenceOfCode_encode, kSystem_val_fresh, hrep]⟩
  · exact ⟨y, h2 y hy, by rw [tableOfCode_encode, entryOf_tbl3_bot],
      by rw [sentenceOfCode_encode, kSystem_val_bot, hrep]⟩
  · exact ⟨z, h2 z hz, by rw [tableOfCode_encode, entryOf_tbl3_top],
      by rw [sentenceOfCode_encode, kSystem_val_top, hrep]⟩

/-! ## The slice worlds: override by shape -/

/-- **Day-`m` literal shape** for the segment's three coordinates and two cells, under any code.
Source: this module (the dissolution of the self-reference; header)
Kind: D
Fidelity: exact -/
def LitShape (m a : ℕ) : Prop :=
  ∃ e, ∃ c ∈ segmentIndex m, ∃ r, r ≤ 1 ∧ a = litIdx e m c r

/-- An atom no sentence of `D` mentions.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def FreshAt (D : Finset Sentence) (a : ℕ) : Prop := ∀ φ ∈ D, a ∉ sentenceAtomCodes φ

/-- The literal atoms the candidate `tbl3 x y z` makes true at day `m`, under any code.
Source: this module
Kind: D
Fidelity: exact -/
def PatTrue (m x y z a : ℕ) : Prop :=
  ∃ e, a = litIdx e m (Encodable.encode freshCoord) x ∨
    a = litIdx e m (Encodable.encode (⊥ : Sentence)) y ∨
    a = litIdx e m (Encodable.encode (⊤ : Sentence)) z

open Classical in
/-- **The slice world of the candidate `(x, y, z)`**: `v` with `freshCoord`'s atom set to `b` and
every `D`-fresh atom of day-`m` literal shape set to the candidate's pattern, whatever its code.
Source: mandate § 4 (Route W: "each slice … its day-`(n+1)` literal atoms set to `q`'s cells");
this module (by shape)
Kind: D
Fidelity: variant: overrides every code's literal atoms of the shape, not only the base's own (header) -/
noncomputable def slice (D : Finset Sentence) (m x y z : ℕ) (b : Prop) (v : PCWorld) : PCWorld :=
  fun a => if a = freshCode then b else
    if LitShape m a ∧ FreshAt D a then PatTrue m x y z a else v a

/-- The slice at `freshCode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma slice_fresh (D : Finset Sentence) (m x y z : ℕ) (b : Prop) (v : PCWorld) :
    slice D m x y z b v freshCode ↔ b := by
  simp [slice]

/-- The slice at a fresh atom of literal shape.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma slice_lit {D : Finset Sentence} {m : ℕ} {a : ℕ} (hs : LitShape m a) (hf : FreshAt D a)
    (hne : a ≠ freshCode) (x y z : ℕ) (b : Prop) (v : PCWorld) :
    slice D m x y z b v a ↔ PatTrue m x y z a := by
  simp [slice, hne, hs, hf]

/-- The slice elsewhere is `v`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma slice_other {D : Finset Sentence} {m : ℕ} {a : ℕ} (hne : a ≠ freshCode)
    (h : ¬ (LitShape m a ∧ FreshAt D a)) (x y z : ℕ) (b : Prop) (v : PCWorld) :
    slice D m x y z b v a ↔ v a := by
  simp [slice, hne, h]

/-- **A slice of a `D`-consistent world is `D`-consistent** (when `freshCode` is `D`-fresh): the
override touches no atom of any sentence of `D`.
Source: mandate § 4 ("consistency with `D n` survives the override by `StageFresh` and
`holds_congr_atomCodes`"); `Mixing.free_atom_undecided` (the mechanism)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem slice_consistent {D : Finset Sentence} (hfr : FreshAt D freshCode) {m x y z : ℕ}
    {b : Prop} {v : PCWorld} (hv : v.ConsistentWith D) :
    (slice D m x y z b v).ConsistentWith D := by
  intro φ hφ
  refine (PCWorld.holds_congr_atomCodes φ fun a ha => ?_).1 (hv φ hφ)
  have hne : a ≠ freshCode := fun h => hfr φ hφ (h ▸ ha)
  exact (slice_other hne (fun h => h.2 φ hφ ha) x y z b v).symm

/-- A slice holds `freshCoord` iff its bit is set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma slice_holds_fresh (D : Finset Sentence) (m x y z : ℕ) (b : Prop) (v : PCWorld) :
    (slice D m x y z b v).Holds freshCoord ↔ b := by
  rw [freshCoord_eq_atom, PCWorld.holds_atom]
  exact slice_fresh D m x y z b v

/-- The pattern at a literal atom, by injectivity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma patTrue_litIdx_iff (e m x y z c r : ℕ) :
    PatTrue m x y z (litIdx e m c r) ↔
      (c = Encodable.encode freshCoord ∧ r = x) ∨
        (c = Encodable.encode (⊥ : Sentence) ∧ r = y) ∨
        (c = Encodable.encode (⊤ : Sentence) ∧ r = z) := by
  constructor
  · rintro ⟨e', h | h | h⟩
    · exact Or.inl ⟨(litIdx_inj h).2.2.1, (litIdx_inj h).2.2.2⟩
    · exact Or.inr (Or.inl ⟨(litIdx_inj h).2.2.1, (litIdx_inj h).2.2.2⟩)
    · exact Or.inr (Or.inr ⟨(litIdx_inj h).2.2.1, (litIdx_inj h).2.2.2⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨e, Or.inl rfl⟩
    · exact ⟨e, Or.inr (Or.inl rfl)⟩
    · exact ⟨e, Or.inr (Or.inr rfl)⟩

/-- A slice holds a fresh literal atom of a segment coordinate iff the candidate lists that cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma slice_holds_lit {D : Finset Sentence} {m e c r : ℕ} (hc : c ∈ segmentIndex m) (hr : r ≤ 1)
    (hf : FreshAt D (litIdx e m c r)) (x y z : ℕ) (b : Prop) (v : PCWorld) :
    (slice D m x y z b v).Holds (Formula.atom (litIdx e m c r)) ↔
      (c = Encodable.encode freshCoord ∧ r = x) ∨
        (c = Encodable.encode (⊥ : Sentence) ∧ r = y) ∨
        (c = Encodable.encode (⊤ : Sentence) ∧ r = z) := by
  rw [PCWorld.holds_atom, slice_lit ⟨e, c, hc, r, hr, rfl⟩ hf (litIdx_ne_freshCode _ _ _ _),
    patTrue_litIdx_iff]

/-- **In the slice of `(x, y, z)`, the state sentence of `tbl3 x' y' z'` holds iff the candidates
coincide** (cells `≤ 1`; the six literal atoms of the family's code fresh at `D`).
Source: mandate § 4 ("`stateOf … q` holds exactly in the worlds of `W_q`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem slice_holds_state {𝒲 : PCWorld → Prop} {C : CellFamily 𝒲} {e : ℕ} (hC : LitAtoms C e)
    {D : Finset Sentence} {m : ℕ}
    (hf : ∀ c ∈ segmentIndex m, ∀ r ≤ 1, FreshAt D (litIdx e m c r))
    {x' y' z' : ℕ} (hx : x' ≤ 1) (hy : y' ≤ 1) (hz : z' ≤ 1) (x y z : ℕ) (b : Prop)
    (v : PCWorld) :
    (slice D m x y z b v).Holds (stateOf C m (Encodable.encode (tbl3 x' y' z'))) ↔
      (x' = x ∧ y' = y ∧ z' = z) := by
  have hcf : Encodable.encode freshCoord ∈ segmentIndex m := by simp [segmentIndex]
  have hcb : Encodable.encode (⊥ : Sentence) ∈ segmentIndex m := by simp [segmentIndex]
  have hct : Encodable.encode (⊤ : Sentence) ∈ segmentIndex m := by simp [segmentIndex]
  rw [holds_stateOf_tbl3, hC, hC, hC,
    slice_holds_lit hcf hx (hf _ hcf _ hx), slice_holds_lit hcb hy (hf _ hcb _ hy),
    slice_holds_lit hct hz (hf _ hct _ hz)]
  simp [freshCoord_ne_falsum, freshCoord_ne_verum, freshCoord_ne_falsum.symm,
    freshCoord_ne_verum.symm]

/-! ## The kernel mixture -/

/-- **The kernel family**: the true slice of `tbl3 1 0 1` and the false slice of `tbl3 0 0 1`
over every member of the given family.
Source: mandate § 4 (Route W)
Kind: D
Fidelity: exact -/
noncomputable def kWorld (D : Finset Sentence) (m : ℕ) {k : ℕ} (W : Fin k → PCWorld) :
    Fin k × Bool → PCWorld
  | (i, true) => slice D m 1 0 1 True (W i)
  | (i, false) => slice D m 0 0 1 False (W i)

/-- **The kernel market on one day**: the uniform mixture over the kernel family (weights
`1 / (2k)`), on every sentence.
Source: mandate § 4 (`P n := ∑_c μ c · ρ_{q_c}`)
Kind: D
Fidelity: exact -/
noncomputable def kMix (D : Finset Sentence) (m : ℕ) {k : ℕ} (W : Fin k → PCWorld)
    (φ : Sentence) : ℝ :=
  ∑ x : Fin k × Bool, (1 / (2 * (k : ℝ))) * (kWorld D m W x).payout φ

/-- The kernel market as an exact rational table.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def kMixRat (D : Finset Sentence) (m : ℕ) {k : ℕ} (W : Fin k → PCWorld)
    (φ : Sentence) : ℚ :=
  ∑ x : Fin k × Bool, (1 / (2 * (k : ℚ))) * (kWorld D m W x).payoutRat φ

/-- The rational table casts to the real market.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kMixRat_cast (D : Finset Sentence) (m : ℕ) {k : ℕ} (W : Fin k → PCWorld) (φ : Sentence) :
    ((kMixRat D m W φ : ℚ) : ℝ) = kMix D m W φ := by
  simp [kMixRat, kMix, PCWorld.payout_eq_ratCast]

/-- The rational table lies in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kMixRat_mem_Icc (D : Finset Sentence) (m : ℕ) {k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld)
    (φ : Sentence) : 0 ≤ kMixRat D m W φ ∧ kMixRat D m W φ ≤ 1 := by
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (by positivity) (payoutRat_nonneg' _ _)
  · calc kMixRat D m W φ ≤ ∑ _x : Fin k × Bool, (1 / (2 * (k : ℚ))) * 1 :=
          Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left (payoutRat_le_one' _ _) (by positivity)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_bool, nsmul_eq_mul]
          have h2 : ((k * 2 : ℕ) : ℚ) = 2 * k := by push_cast; ring
          rw [h2]; field_simp

/-- A mixture over any finite index type is a stage mixture (`CoherentOn`) on every algebra.
Source: none: infrastructure (bli-found `Constraints.CoherentOn` reindexed)
Kind: L
Fidelity: n/a -/
lemma coherentOn_of_fintype {ι : Type*} [Fintype ι] {D : Finset Sentence} (A : Finset ℕ)
    (W : ι → PCWorld) (w : ι → ℝ) (hW : ∀ i, (W i).ConsistentWith D) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) : CoherentOn D A (fun φ => ∑ i, w i * (W i).payout φ) := by
  refine ⟨Fintype.card ι, fun j => W ((Fintype.equivFin ι).symm j),
    fun j => w ((Fintype.equivFin ι).symm j), fun j => hW _, fun j => hw0 _, ?_, fun φ _ => ?_⟩
  · rw [← hw1]
    exact Equiv.sum_comp (Fintype.equivFin ι).symm w
  · exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => w i * (W i).payout φ)).symm

/-- **The kernel market is a stage mixture on every algebra**, from a family of `D`-consistent
worlds, when `freshCode` is `D`-fresh.
Source: mandate § 4 ("coherence … by construction")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem kMix_coherentOn {D : Finset Sentence} (hfr : FreshAt D freshCode) (m : ℕ) {k : ℕ}
    (hk : 0 < k) {W : Fin k → PCWorld} (hW : ∀ i, (W i).ConsistentWith D) (A : Finset ℕ) :
    CoherentOn D A (kMix D m W) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold kMix
  refine coherentOn_of_fintype A (kWorld D m W) (fun _ => 1 / (2 * (k : ℝ))) ?_
    (fun _ => by positivity) ?_
  · rintro ⟨i, _ | _⟩
    · exact slice_consistent hfr (hW i)
    · exact slice_consistent hfr (hW i)
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul]
    have h2 : ((k * 2 : ℕ) : ℝ) = 2 * k := by push_cast; ring
    rw [h2]; field_simp

/-- The kernel value when the two slices have constant payouts.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kMix_eq_avg {D : Finset Sentence} {m k : ℕ} (hk : 0 < k) {W : Fin k → PCWorld}
    {φ : Sentence} {a b : ℝ} (hT : ∀ i, (slice D m 1 0 1 True (W i)).payout φ = a)
    (hF : ∀ i, (slice D m 0 0 1 False (W i)).payout φ = b) :
    kMix D m W φ = (a + b) / 2 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold kMix
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, kWorld, hT, hF, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- A payout through an equivalence of the truth condition.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_eq_ite {v : PCWorld} {φ : Sentence} {p : Prop} [Decidable p] (h : v.Holds φ ↔ p) :
    v.payout φ = if p then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp]; exact payout_of_holds (h.2 hp)
  · rw [if_neg hp]; exact payout_of_not_holds fun hh => hp (h.1 hh)

/-- The kernel value through equivalences of the truth conditions in the two slices.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kMix_eq_ite {D : Finset Sentence} {m k : ℕ} (hk : 0 < k) {W : Fin k → PCWorld}
    {φ : Sentence} {pT pF : Prop} [Decidable pT] [Decidable pF]
    (hT : ∀ i, (slice D m 1 0 1 True (W i)).Holds φ ↔ pT)
    (hF : ∀ i, (slice D m 0 0 1 False (W i)).Holds φ ↔ pF) :
    kMix D m W φ = ((if pT then 1 else 0) + (if pF then 1 else 0)) / 2 :=
  kMix_eq_avg hk (fun i => payout_eq_ite (hT i)) (fun i => payout_eq_ite (hF i))

/-- The kernel prices `freshCoord` at `1/2`.
Source: mandate § 2 (the uncertain coordinate priced strictly inside), § 4
Kind: L
Fidelity: n/a -/
lemma kMix_fresh (D : Finset Sentence) (m : ℕ) {k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld) :
    kMix D m W freshCoord = 1 / 2 := by
  rw [kMix_eq_ite hk (pT := True) (pF := False) (fun i => slice_holds_fresh D m 1 0 1 True (W i))
    (fun i => slice_holds_fresh D m 0 0 1 False (W i))]
  norm_num

/-- No world holds `⊥`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_holds_falsum (v : PCWorld) : ¬ v.Holds (⊥ : Sentence) := fun h => h

/-- The kernel prices `⊤` at `1` and `⊥` at `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma kMix_top_bot (D : Finset Sentence) (m : ℕ) {k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld) :
    kMix D m W ⊤ = 1 ∧ kMix D m W ⊥ = 0 := by
  constructor
  · rw [kMix_eq_ite hk (pT := True) (pF := True) (fun i => by simp [PCWorld.holds_top])
      (fun i => by simp [PCWorld.holds_top])]
    norm_num
  · rw [kMix_eq_ite hk (pT := False) (pF := False) (fun i => ⟨not_holds_falsum _, False.elim⟩)
      (fun i => ⟨not_holds_falsum _, False.elim⟩)]
    norm_num

/-- **The kernel's mass on each candidate**: `1/2` on `tbl3 1 0 1` and on `tbl3 0 0 1`, `0` on the
other six.
Source: mandate § 4 (`μ`)
Kind: L
Fidelity: n/a -/
lemma kMix_state {𝒲 : PCWorld → Prop} {C : CellFamily 𝒲} {e : ℕ} (hC : LitAtoms C e)
    {D : Finset Sentence} {m : ℕ} (hf : ∀ c ∈ segmentIndex m, ∀ r ≤ 1, FreshAt D (litIdx e m c r))
    {k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld) {x y z : ℕ} (hx : x ≤ 1) (hy : y ≤ 1)
    (hz : z ≤ 1) :
    kMix D m W (stateOf C m (Encodable.encode (tbl3 x y z))) =
      (if x = 1 ∧ y = 0 ∧ z = 1 then 1 / 2 else 0) + (if x = 0 ∧ y = 0 ∧ z = 1 then 1 / 2 else 0) := by
  rw [kMix_eq_ite hk (fun i => slice_holds_state hC hf hx hy hz 1 0 1 True (W i))
    (fun i => slice_holds_state hC hf hx hy hz 0 0 1 False (W i))]
  split_ifs <;> norm_num

/-- The two charged candidates.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def q₁ : ℕ := Encodable.encode (tbl3 1 0 1)

/-- The second charged candidate.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def q₀ : ℕ := Encodable.encode (tbl3 0 0 1)

/-- The two charged candidates are distinct codes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma q₁_ne_q₀ : q₁ ≠ q₀ := by
  intro h
  have := tbl3_inj (Encodable.encode_injective h)
  omega

/-- **The partition on the kernel**: the candidates' masses sum to one and distinct candidates
are exclusive in the kernel's measure.
Source: mandate § 4 ("partition … by construction"); bli-found `E5σ` (one day)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem kMix_partitionAt {𝒲 : PCWorld → Prop} {C : CellFamily 𝒲} {e : ℕ} (hC : LitAtoms C e)
    {D : Finset Sentence} {m : ℕ} (hf : ∀ c ∈ segmentIndex m, ∀ r ≤ 1, FreshAt D (litIdx e m c r))
    {k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld) (rep : ℕ → ℕ → ℚ) :
    PartitionAt (stateOf C) (kSystem rep) (kMix D m W) m where
  mass := by
    show ∑ q ∈ kStates, _ = 1
    rw [sum_kStates]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [kMix_state hC hf hk W le_rfl le_rfl le_rfl, kMix_state hC hf hk W le_rfl le_rfl zero_le_one,
      kMix_state hC hf hk W le_rfl zero_le_one le_rfl, kMix_state hC hf hk W le_rfl zero_le_one zero_le_one,
      kMix_state hC hf hk W zero_le_one le_rfl le_rfl, kMix_state hC hf hk W zero_le_one le_rfl zero_le_one,
      kMix_state hC hf hk W zero_le_one zero_le_one le_rfl,
      kMix_state hC hf hk W zero_le_one zero_le_one zero_le_one]
    norm_num
  excl := by
    intro qa hqa qb hqb hne
    obtain ⟨xa, ya, za, hxa, hya, hza, rfl⟩ := mem_kStates.1 (by simpa [kSystem] using hqa)
    obtain ⟨xb, yb, zb, hxb, hyb, hzb, rfl⟩ := mem_kStates.1 (by simpa [kSystem] using hqb)
    have key : ∀ (x y z : ℕ) (b : Prop) (v : PCWorld),
        ¬ (slice D m x y z b v).Holds
          (stateOf C m (Encodable.encode (tbl3 xa ya za)) ⋏
            stateOf C m (Encodable.encode (tbl3 xb yb zb))) := by
      intro x y z b v h
      rw [PCWorld.holds_and, slice_holds_state hC hf hxa hya hza,
        slice_holds_state hC hf hxb hyb hzb] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩ := h
      exact hne rfl
    rw [kMix_eq_ite hk (pT := False) (pF := False) (fun i => ⟨key _ _ _ _ _, False.elim⟩)
      (fun i => ⟨key _ _ _ _ _, False.elim⟩)]
    norm_num

/-- **Two distinct candidates are charged `1/2` each.**
Source: mandate § 4 (the N+ clause: "two distinct charged candidates")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem kMix_two_charged {𝒲 : PCWorld → Prop} {C : CellFamily 𝒲} {e : ℕ} (hC : LitAtoms C e)
    {D : Finset Sentence} {m : ℕ} (hf : ∀ c ∈ segmentIndex m, ∀ r ≤ 1, FreshAt D (litIdx e m c r))
    {k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld) :
    q₁ ∈ kStates ∧ q₀ ∈ kStates ∧ q₁ ≠ q₀ ∧
      kMix D m W (stateOf C m q₁) = 1 / 2 ∧ kMix D m W (stateOf C m q₀) = 1 / 2 := by
  refine ⟨mem_kStates.2 ⟨1, 0, 1, le_rfl, zero_le_one, le_rfl, rfl⟩,
    mem_kStates.2 ⟨0, 0, 1, zero_le_one, zero_le_one, le_rfl, rfl⟩, q₁_ne_q₀, ?_, ?_⟩
  · rw [q₁, kMix_state hC hf hk W le_rfl zero_le_one le_rfl]; norm_num
  · rw [q₀, kMix_state hC hf hk W zero_le_one zero_le_one le_rfl]; norm_num

/-- **Faith at every segment coordinate on every candidate**: `kMix (φ_c ⋏ σ_q) = val_q(φ_c) ·
kMix σ_q` for `c ∈ segmentIndex` and `q ∈ kStates`, at `rep01`. Uncharged candidates: both sides
`0`. Charged: `freshCoord` is certain inside its slice (`rep01 1 = 1`, `rep01 0 = 0`), `⊥` never
holds, `⊤` always.
Source: mandate § 4 ("faith … by construction"); bli-linkage `E2xσIdx` (one day, per candidate)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem kMix_faith {𝒲 : PCWorld → Prop} {C : CellFamily 𝒲} {e : ℕ} (hC : LitAtoms C e)
    {D : Finset Sentence} {m : ℕ} (hf : ∀ c ∈ segmentIndex m, ∀ r ≤ 1, FreshAt D (litIdx e m c r))
    {k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld) {c : ℕ} (hc : c ∈ segmentIndex m) {q : ℕ}
    (hq : q ∈ (kSystem rep01).states m) :
    kMix D m W (sentenceOfCode c ⋏ stateOf C m q) =
      (kSystem rep01).val m q (sentenceOfCode c) * kMix D m W (stateOf C m q) := by
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := mem_kStates.1 (by simpa [kSystem] using hq)
  rw [kMix_state hC hf hk W hx hy hz]
  simp only [segmentIndex, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · rw [sentenceOfCode_encode, kSystem_val_fresh,
      kMix_eq_ite hk (pT := x = 1 ∧ y = 0 ∧ z = 1) (pF := False)
        (fun i => by rw [PCWorld.holds_and, slice_holds_fresh, slice_holds_state hC hf hx hy hz]; simp)
        (fun i => by rw [PCWorld.holds_and, slice_holds_fresh, slice_holds_state hC hf hx hy hz]; simp)]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hy with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hz with rfl | rfl <;> norm_num [rep01]
  · rw [sentenceOfCode_encode, kSystem_val_bot,
      kMix_eq_ite hk (pT := False) (pF := False)
        (fun i => ⟨fun h => not_holds_falsum _ ((PCWorld.holds_and _ _ _).1 h).1, False.elim⟩)
        (fun i => ⟨fun h => not_holds_falsum _ ((PCWorld.holds_and _ _ _).1 h).1, False.elim⟩)]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hy with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hz with rfl | rfl <;> norm_num [rep01]
  · rw [sentenceOfCode_encode, kSystem_val_top,
      kMix_eq_ite hk (pT := x = 1 ∧ y = 0 ∧ z = 1) (pF := x = 0 ∧ y = 0 ∧ z = 1)
        (fun i => by rw [holds_top_and, slice_holds_state hC hf hx hy hz])
        (fun i => by rw [holds_top_and, slice_holds_state hC hf hx hy hz])]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hy with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hz with rfl | rfl <;> norm_num [rep01]

end Kernel

end Cleanroom.Bli.BliExactBase
