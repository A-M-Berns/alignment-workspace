import Cleanroom.Bli.BliAssemble.Coding

/-!
# `bli-assemble` · SmallList: the computable enumeration of the day-`n` small sentences (target 0)

`smallList n : List Sentence` is a **computable** list — a plain `def` in a file with no
`noncomputable section` and no `open Classical`, so Lean's compiler must accept it — with
`(smallList n).toFinset = smallSet n` (`smallList_toFinset`), `Nodup` (`smallList_nodup`) and sorted
by FAF code (`smallList_pairwise`). This is the mandate's target-0 definition of record,
`bli-found`'s unlanded stretch S1, and the shared leaf of targets 5 and 6 (repair round 1).

Route: not the mandate's converse size bound `encode φ ≤ g (tokenSize φ)` (which would need the
`Encodable` instance's pairing arithmetic) but the structural recursion already inside
`bli-found`'s finiteness proof `finite_tokenSize_le`: a sentence of token size `≤ K + 1` is an atom
`a < 4 ^ (K + 1)`, `⊥`, or one of `⋏`/`⋎`/`🡒` over two sentences of token size `≤ K`.
`sentencesUpTo K` enumerates that superset by recursion on `K`
(`mem_sentencesUpTo_of_tokenSize_le`); `smallList n` filters it by the decidable `SmallOn n`,
deduplicates, and merge-sorts by `Encodable.encode`.

* `smallSorted_map_val` — the alignment with `Coding.lean`'s `smallSorted m` (`Finset.sort` of the
  noncomputable `smallSet` under `bli-superbelief`'s `encLE`): the two lists agree, hence
  `writeOutDigits_eq_smallList`: the write-out digit list is the numerators along `smallList m`.
  That makes the coding of record computable *from the table's values*; what target 5 still needs
  is the rest of the re-pricing (`grid` as a list of numerator vectors, `chainProbH` over it, the
  tent kernels) — see [[bli-assemble-handoff]].

`List.range (4 ^ (K + 1))` is astronomically long at `K = sizeBound n = 2 ^ 2 ^ n`: this is
computability in Mathlib's sense, which is what target 5's `ComputableTable` asks; it is not
polynomial time, and target 6's oracle cannot enumerate this list (it must read `|S m|` off the
write-out code's digits instead, `writeOutCode_card_le_log`).

Sources: mandate target 0 (`smallList`); `bli-found` report § Stretch S1; `bli-found` `Size.lean`
(`finite_tokenSize_le`).
-/

namespace Cleanroom.Bli.BliAssemble

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliSuperbelief

/-! ## The structural enumeration -/

/-- **A computable list containing every sentence of token size `≤ K`** (a superset, with the
shape of `bli-found`'s `finite_tokenSize_le`): nothing at `K = 0`; at `K + 1`, the atoms
`a < 4 ^ (K + 1)`, `⊥`, and `⋏`/`⋎`/`🡒` over `sentencesUpTo K`.
Source: mandate target 0 (`smallList`); `bli-found` `finite_tokenSize_le`
Kind: D
Fidelity: n/a -/
def sentencesUpTo : ℕ → List Sentence
  | 0 => []
  | K + 1 =>
      ((List.range (4 ^ (K + 1))).map fun a => (Formula.atom a : Sentence)) ++ [(⊥ : Sentence)] ++
        ((sentencesUpTo K).flatMap fun φ => (sentencesUpTo K).map fun ψ => φ ⋏ ψ) ++
        ((sentencesUpTo K).flatMap fun φ => (sentencesUpTo K).map fun ψ => φ ⋎ ψ) ++
        ((sentencesUpTo K).flatMap fun φ => (sentencesUpTo K).map fun ψ => φ 🡒 ψ)

/-- **Every sentence of token size `≤ K` is in `sentencesUpTo K`** — the finiteness proof's case
analysis, run as a membership proof.
Source: mandate target 0; `bli-found` `finite_tokenSize_le`
Kind: P
Fidelity: n/a -/
theorem mem_sentencesUpTo_of_tokenSize_le :
    ∀ (K : ℕ) (φ : Sentence), tokenSize φ ≤ K → φ ∈ sentencesUpTo K
  | 0, φ, h => absurd h (by have := one_le_tokenSize φ; omega)
  | K + 1, φ, h => by
    cases φ with
    | atom a =>
        have h1 := lt_pow_length_natDigits4 (a + 5)
        have h2 : (natDigits4 (a + 5)).length + 1 ≤ K + 1 := by simpa using h
        have ha : a < 4 ^ (K + 1) :=
          calc a < a + 5 := by omega
            _ < 4 ^ (natDigits4 (a + 5)).length := h1
            _ ≤ 4 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simp only [sentencesUpTo, List.mem_append, List.mem_map, List.mem_range,
          List.mem_singleton]
        exact Or.inl (Or.inl (Or.inl (Or.inl ⟨a, ha, rfl⟩)))
    | falsum =>
        simp only [sentencesUpTo, List.mem_append, List.mem_singleton]
        exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
    | and φ ψ =>
        rw [show (Formula.and φ ψ : Sentence) = φ ⋏ ψ from rfl, tokenSize_and] at h
        have hφ := mem_sentencesUpTo_of_tokenSize_le K φ (by have := one_le_tokenSize ψ; omega)
        have hψ := mem_sentencesUpTo_of_tokenSize_le K ψ (by have := one_le_tokenSize φ; omega)
        simp only [sentencesUpTo, List.mem_append, List.mem_flatMap, List.mem_map]
        exact Or.inl (Or.inl (Or.inr ⟨φ, hφ, ψ, hψ, rfl⟩))
    | or φ ψ =>
        rw [show (Formula.or φ ψ : Sentence) = φ ⋎ ψ from rfl, tokenSize_or] at h
        have hφ := mem_sentencesUpTo_of_tokenSize_le K φ (by have := one_le_tokenSize ψ; omega)
        have hψ := mem_sentencesUpTo_of_tokenSize_le K ψ (by have := one_le_tokenSize φ; omega)
        simp only [sentencesUpTo, List.mem_append, List.mem_flatMap, List.mem_map]
        exact Or.inl (Or.inr ⟨φ, hφ, ψ, hψ, rfl⟩)
    | imp φ ψ =>
        rw [show (Formula.imp φ ψ : Sentence) = φ 🡒 ψ from rfl, tokenSize_imp] at h
        have hφ := mem_sentencesUpTo_of_tokenSize_le K φ (by have := one_le_tokenSize ψ; omega)
        have hψ := mem_sentencesUpTo_of_tokenSize_le K ψ (by have := one_le_tokenSize φ; omega)
        simp only [sentencesUpTo, List.mem_append, List.mem_flatMap, List.mem_map]
        exact Or.inr ⟨φ, hφ, ψ, hψ, rfl⟩

/-! ## The list of record -/

/-- **The day-`n` small sentences as a computable list**: `sentencesUpTo (sizeBound n)` filtered
by the decidable `SmallOn n`, deduplicated, and merge-sorted by FAF code (`Encodable.encode`).
Source: mandate target 0 (`smallList`); `bli-found` report § Stretch S1
Kind: D
Fidelity: exact -/
def smallList (n : ℕ) : List Sentence :=
  (((sentencesUpTo (sizeBound n)).filter fun φ => decide (SmallOn n φ)).dedup).mergeSort
    fun φ ψ => decide (Encodable.encode φ ≤ Encodable.encode ψ)

/-- Membership in `smallList n` is `SmallOn n`.
Source: mandate target 0
Kind: L
Fidelity: n/a -/
theorem mem_smallList {n : ℕ} {φ : Sentence} : φ ∈ smallList n ↔ SmallOn n φ := by
  unfold smallList
  rw [List.mem_mergeSort, List.mem_dedup, List.mem_filter, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨mem_sentencesUpTo_of_tokenSize_le _ _ h, h⟩⟩

/-- **`smallList n` enumerates `smallSet n`** — the mandate's `smallList_toFinset`.
Source: mandate target 0 (`smallList_toFinset`)
Kind: P
Fidelity: exact -/
theorem smallList_toFinset (n : ℕ) : (smallList n).toFinset = smallSet n := by
  ext φ
  rw [List.mem_toFinset, mem_smallList, mem_smallSet]

/-- `smallList n` has no duplicates.
Source: mandate target 0 (`Nodup`)
Kind: L
Fidelity: n/a -/
theorem smallList_nodup (n : ℕ) : (smallList n).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_dedup _)

/-- `smallList n` is sorted by FAF code.
Source: mandate target 0 ("sorted by FAF code")
Kind: L
Fidelity: n/a -/
theorem smallList_pairwise (n : ℕ) :
    (smallList n).Pairwise fun φ ψ => Encodable.encode φ ≤ Encodable.encode ψ := by
  have h := List.pairwise_mergeSort
    (le := fun φ ψ : Sentence => decide (Encodable.encode φ ≤ Encodable.encode ψ))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_iff] at hab hbc ⊢
      omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_iff]
      omega)
    (((sentencesUpTo (sizeBound n)).filter fun φ => decide (SmallOn n φ)).dedup)
  exact h.imp fun hab => decide_eq_true_iff.mp hab

/-- `smallList n` has `|S n|` entries.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem smallList_length (n : ℕ) : (smallList n).length = (smallSet n).card := by
  rw [← smallList_toFinset, List.toFinset_card_of_nodup (smallList_nodup n)]

/-! ## Alignment with the sorted small sentences of `Coding.lean` -/

/-- FAF-code order on sentences is antisymmetric (`Encodable.encode` is injective).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance encodeLE_antisymm :
    Std.Antisymm fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ :=
  ⟨fun _ _ h₁ h₂ => Encodable.encode_injective (le_antisymm h₁ h₂)⟩

/-- **`smallSorted m` is `smallList m`** (as lists of sentences): both are duplicate-free
enumerations of `smallSet m` sorted by FAF code, so they are the same list.
Source: mandate target 0 ("agrees with `bli-superbelief`'s `Finset.sort` under `encLE`")
Kind: P
Fidelity: exact -/
theorem smallSorted_map_val (m : ℕ) : (smallSorted m).map Subtype.val = smallList m := by
  have hnd : ((smallSorted m).map Subtype.val).Nodup :=
    (Finset.sort_nodup _ _).map Subtype.val_injective
  have hfin : ((smallSorted m).map Subtype.val).toFinset = (smallList m).toFinset := by
    rw [smallList_toFinset]
    ext φ
    rw [List.mem_toFinset, List.mem_map, mem_smallSet]
    constructor
    · rintro ⟨x, -, rfl⟩
      exact mem_smallSet.mp x.2
    · intro h
      exact ⟨⟨φ, mem_smallSet.mpr h⟩, mem_smallSorted m _, rfl⟩
  have hperm := List.perm_of_nodup_nodup_toFinset_eq hnd (smallList_nodup m) hfin
  have h₁ : ((smallSorted m).map Subtype.val).Pairwise
      fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ :=
    List.pairwise_map.mpr
      (Finset.pairwise_sort (r := encLE smallIndex m) (s := (Finset.univ : Finset ↥(smallIndex.S m))))
  exact hperm.eq_of_pairwise' h₁ (smallList_pairwise m)

/-- **The write-out digit list is computable from the table's values**: the grid numerators along
`smallList m`, then the terminating `1`.
Source: mandate target 0 (`writeOutCoding`: "computable in Lean's sense given `smallList`")
Kind: L
Fidelity: exact -/
theorem writeOutDigits_eq_smallList (𝓜 : Mesh) (m : ℕ) (Q : Table smallIndex m) :
    writeOutDigits 𝓜 m Q =
      ((smallList m).map fun φ =>
        if h : φ ∈ smallIndex.S m then gridNumer (𝓜.d m) (Q ⟨φ, h⟩) else 0) ++ [1] := by
  unfold writeOutDigits
  rw [← smallSorted_map_val, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  rw [Function.comp_apply, dif_pos x.2]

end Cleanroom.Bli.BliAssemble
