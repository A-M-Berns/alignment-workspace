import Cleanroom.Bli.BliCoherentMm.AttemptA.Accept

/-!
# `bli-coherent-mm` (attempt A) · Maker: the coherent and interior market makers (D4, T2(b)–(e), T3)

**Angle A's search by enumeration.** A total enumeration of rational weight vectors
(`decodeWeights`: decode a `List ℚ` through Mathlib's `Encodable`, read it off through
`Fintype.equivFin`; every vector occurs at its own code, `decodeWeights_encodeWeights`), and a
generic "first accepted candidate" (`firstAccepted P hex`, FAF's own `MarketMaker` idiom: a
`Nat.find` on the decidable candidate predicate, total by the existence theorem):

* **D4** `coherentMarketMaker T past D B S hS hW hε` — `ofWeights S` of
  `coherentWeights …`, the first enumerated world measure accepted by D3 at `ε`; and
  `interiorCoherentMarketMaker` with `interiorWeights …`, the first accepted **with full support
  on `WD D B`** (T3's existence theorem gives totality). Both `noncomputable` as FAF's
  `MarketMaker` is (the `Nat.find`); both expose their weights (`B3` needs the measure).
* **T2(b)** `coherentMarketMaker_accepts`, `coherentMarketMaker_isWorldMeasure`,
  `coherentMarketMaker_quote_eq_pi`, `coherentMarketMaker_coherent` (the marginal is a world
  marginal on `S` and the quote is that marginal on `S`: `CoherentQuoteOn`), the `CoherentOn`
  packaging for `PCInductor`, and the two-axiom reading.
* **T2(c)** `coherentMarketMaker_respects_true/false`: decided sentences priced at their truth.
* **T2(e)** `coherentMarketMakerSmall`: the `S = smallSet n` instance (same theorems; its only
  open part is computability, not existence).
* **T3** `interior_accepts`, `interior_fullSupport`, `interior_coherent`, `interior_nonDogmatic`,
  `interior_decided_at_truth`, `interior_D_ND_day` (the `D_ND` clause of `bli-found` at day `n`
  over `smallSet n`).

Sources: [[bli-coherent-mm-mandate]] D4, T2(b)–(e), T3; [[bli-program]] §3.8.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## The enumeration of rational weight vectors -/

/-- Decode candidate number `k` as a rational weight vector on `FiniteWorld B`: decode a
`List ℚ` and read coordinate `u` at position `Fintype.equivFin u` (default `0`).
`noncomputable` only because Mathlib's `Fintype.equivFin` (the enumeration *order* of the
finite worlds) is chosen through `Trunc`; the decoding and the acceptance test are exact
rational arithmetic (attempt report, §D4).
Source: [[bli-coherent-mm-mandate]] §Attempt angles (A)
Kind: D
Fidelity: exact -/
noncomputable def decodeWeights (B : ℕ) (k : ℕ) : Option (FiniteWorld B → ℚ) :=
  (Encodable.decode (α := List ℚ) k).map fun l u =>
    l.getD (Fintype.equivFin (FiniteWorld B) u) 0

/-- The code of a weight vector: the code of its coordinate list in `equivFin` order.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def encodeWeights {B : ℕ} (w : FiniteWorld B → ℚ) : ℕ :=
  Encodable.encode (List.ofFn fun i : Fin (Fintype.card (FiniteWorld B)) =>
    w ((Fintype.equivFin (FiniteWorld B)).symm i))

/-- **The enumeration is total**: every weight vector occurs at its own code.
Source: [[bli-coherent-mm-mandate]] §Attempt angles (A) ("a total enumeration")
Kind: L
Fidelity: n/a -/
lemma decodeWeights_encodeWeights {B : ℕ} (w : FiniteWorld B → ℚ) :
    decodeWeights B (encodeWeights w) = some w := by
  unfold decodeWeights encodeWeights
  rw [Encodable.encodek, Option.map_some]
  congr 1
  funext u
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (Fin.isLt _)]
  simp

/-! ## The first accepted candidate -/

section Search

variable {B : ℕ} (P : (FiniteWorld B → ℚ) → Prop) [DecidablePred P]

/-- Candidate `k` decodes to an accepted weight vector.
Source: FAF `MarketMakerCandidateAccepts`
Kind: D
Fidelity: exact -/
def CandidateAccepts (k : ℕ) : Prop := ∃ w, decodeWeights B k = some w ∧ P w

/-- Decidable: decode, then test (FAF's `MarketMakerCandidateAccepts.instDecidable`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
noncomputable instance instDecidableCandidateAccepts (k : ℕ) : Decidable (CandidateAccepts P k) :=
  match h : decodeWeights B k with
  | none => isFalse fun ⟨_, hw, _⟩ => by rw [h] at hw; cases hw
  | some w => decidable_of_iff (P w)
      ⟨fun ha => ⟨w, h, ha⟩, fun ⟨w', hw', ha⟩ => by rw [h] at hw'; cases hw'; exact ha⟩

omit [DecidablePred P] in
/-- Some candidate is accepted, given an accepted vector.
Source: FAF `exists_marketMakerCandidateAccepts`
Kind: L
Fidelity: n/a -/
lemma exists_candidateAccepts (hex : ∃ w, P w) : ∃ k, CandidateAccepts P k := by
  obtain ⟨w, hw⟩ := hex
  exact ⟨encodeWeights w, w, decodeWeights_encodeWeights w, hw⟩

/-- The index of the first accepted candidate (`Nat.find`; FAF's `marketMakerIndex`).
Source: FAF `marketMakerIndex`
Kind: D
Fidelity: exact -/
noncomputable def searchIndex (hex : ∃ w, P w) : ℕ := Nat.find (exists_candidateAccepts P hex)

/-- **The first accepted candidate**, decoded.
Source: FAF `MarketMaker` (the "first accepted candidate" idiom)
Kind: D
Fidelity: exact -/
noncomputable def firstAccepted (hex : ∃ w, P w) : FiniteWorld B → ℚ :=
  Classical.choose (Nat.find_spec (exists_candidateAccepts P hex))

/-- The first accepted candidate decodes at the search index and is accepted.
Source: FAF `marketMakerIndex_spec`
Kind: L
Fidelity: n/a -/
lemma firstAccepted_spec (hex : ∃ w, P w) :
    decodeWeights B (searchIndex P hex) = some (firstAccepted P hex) ∧ P (firstAccepted P hex) :=
  Classical.choose_spec (Nat.find_spec (exists_candidateAccepts P hex))

/-- The first accepted candidate is accepted.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma firstAccepted_accepts (hex : ∃ w, P w) : P (firstAccepted P hex) :=
  (firstAccepted_spec P hex).2

/-- No earlier candidate is accepted: the search returns the **first** one.
Source: FAF `Nat.find_min`
Kind: L
Fidelity: n/a -/
lemma searchIndex_min (hex : ∃ w, P w) {k : ℕ} (hk : k < searchIndex P hex) :
    ¬ CandidateAccepts P k :=
  Nat.find_min (exists_candidateAccepts P hex) hk

end Search

/-! ## D4: the coherent market maker -/

section Maker

variable {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
  (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
  (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε)

/-- **D4. The weights of the coherent market maker**: the first enumerated rational world
measure over `D` whose candidate table on `S` is accepted at `ε` in every `D`-consistent world.
Exposed as a definition of record (B3 needs the measure, not only its marginal).
Source: [[bli-coherent-mm-mandate]] D4
Kind: D
Fidelity: exact -/
noncomputable def coherentWeights : FiniteWorld B → ℚ :=
  firstAccepted (CoherentAccepts T past D B S ε) (exists_coherentAccepts T past D B S hS hW hε)

/-- The maker's weights are coherently accepted.
Source: [[bli-coherent-mm-mandate]] T2(b)
Kind: L
Fidelity: exact -/
lemma coherentWeights_accepts : CoherentAccepts T past D B S ε (coherentWeights T past D B S hS hW hε) :=
  firstAccepted_accepts _ _

/-- The maker's weights are a world measure over `D`.
Source: [[bli-coherent-mm-mandate]] T2(b)
Kind: L
Fidelity: exact -/
lemma coherentWeights_isWorldMeasure : IsWorldMeasure (coherentWeights T past D B S hS hW hε) D :=
  (coherentWeights_accepts T past D B S hS hW hε).1

/-- **D4. The coherent market maker**: the candidate state of `coherentWeights` on `S` — entries
`(φ, π w φ)` for `φ ∈ S`. Not FAF's `MarketMaker` renamed: a `Nat.find` over *world measures*
with the *consistent-world* check (`CoherentAccepts`).
Source: [[bli-coherent-mm-mandate]] D4; [[bli-program]] §3.8, §4 row M2
Kind: D
Fidelity: exact -/
noncomputable def coherentMarketMaker : RationalBeliefState :=
  ofWeights S (coherentWeights T past D B S hS hW hε) (coherentWeights_isWorldMeasure T past D B S hS hW hε)

/-- **T2(b). The maker's quote on `S` is the marginal of its weights.**
Source: [[bli-coherent-mm-mandate]] D4 (`coherentMarketMaker_quote_eq_pi`)
Kind: L
Fidelity: exact -/
lemma coherentMarketMaker_quote_eq_pi {φ : Sentence} (hφ : φ ∈ S) :
    (coherentMarketMaker T past D B S hS hW hε).quote φ =
      marginal (coherentWeights T past D B S hS hW hε) φ :=
  ofWeights_quote_of_mem _ hφ

/-- **T2(b). The coherent market maker is accepted in every `D`-consistent world**: the exact
rational value of `T` on FAF's `candidateRationalHistory past n (coherentMarketMaker …)` is
`≤ ε` in every `u ∈ WD D B`. Scope: over `D`-consistent worlds, on `S ⊇ mentionedSet T`.
Source: [[bli-coherent-mm-mandate]] T2(b); [[bli-program]] §4 row M2
Kind: C
Fidelity: exact
Hyps: (a) `hS`, `hW`, `hε` — discharged in `Contrast.lean`/`Witness.lean` -/
theorem coherentMarketMaker_accepts :
    ∀ u ∈ WD D B,
      T.marketValueRat (candidateRationalHistory past n (coherentMarketMaker T past D B S hS hW hε))
        u.payoutRat ≤ ε :=
  (coherentAccepts_iff T past D B S ε (coherentWeights_isWorldMeasure T past D B S hS hW hε)).mp
    (coherentWeights_accepts T past D B S hS hW hε)

/-- The maker's weights are a world measure (restated at the maker).
Source: [[bli-coherent-mm-mandate]] T2(b)
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_isWorldMeasure :
    IsWorldMeasure (coherentWeights T past D B S hS hW hε) D :=
  coherentWeights_isWorldMeasure T past D B S hS hW hε

/-- **A quote is coherent on `S` relative to `D` over `B` atoms** when it agrees on `S` with the
marginal of a world measure over `D` (the shape of `bli-finite`'s `CoherentOn`, for a quote
defined on all sentences; the quote off `S` is unconstrained).
Source: [[bli-coherent-mm-mandate]] T2(b); bli-finite `CoherentOn`
Kind: D
Fidelity: exact -/
def CoherentQuoteOn (V : Sentence → ℚ) (S D : Finset Sentence) (B : ℕ) : Prop :=
  ∃ w : FiniteWorld B → ℚ, IsWorldMeasure w D ∧ ∀ φ ∈ S, V φ = marginal w φ

/-- **T2(b). The coherent market maker's table is coherent on `S`**: on `S` its quote is the
marginal of its (world-measure) weights. The `IsWorldMarginal` form of the mandate holds for the
full marginal `π (coherentWeights …)` (`isWorldMarginal_marginal`), of which the quote is the
restriction to `S` — a finite-support `RationalBeliefState` quotes `0` off `S`, so it cannot
itself be a marginal on `GenBy S` (attempt report, finding on T2(b)'s shape).
Source: [[bli-coherent-mm-mandate]] T2(b); [[bli-program]] §4 row M2
Kind: C
Fidelity: variant: coherence stated as agreement with a world marginal on `S` (see docstring)
Hyps: (a) -/
theorem coherentMarketMaker_coherent :
    CoherentQuoteOn (coherentMarketMaker T past D B S hS hW hε).quote S D B :=
  ⟨coherentWeights T past D B S hS hW hε, coherentWeights_isWorldMeasure T past D B S hS hW hε,
    fun _ hφ => coherentMarketMaker_quote_eq_pi T past D B S hS hW hε hφ⟩

/-- The maker's marginal is a world marginal on `S` (the mandate's `IsWorldMarginal` form, for
the full marginal function).
Source: [[bli-coherent-mm-mandate]] T2(b)
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_isWorldMarginal :
    IsWorldMarginal (marginal (coherentWeights T past D B S hS hW hε)) S D B :=
  isWorldMarginal_marginal (coherentWeights_isWorldMeasure T past D B S hS hW hε) S

/-- The two-axiom reading: the maker's marginal satisfies `bli-finite`'s `TwoAxiomCoherent` on
`GenBy S` (through `twoAxiom_of_worldMarginal`).
Source: [[bli-coherent-mm-mandate]] T2(b); bli-finite `twoAxiom_of_worldMarginal`
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_twoAxiom :
    TwoAxiomCoherent (marginal (coherentWeights T past D B S hS hW hε)) S D :=
  twoAxiom_of_worldMarginal (coherentMarketMaker_isWorldMarginal T past D B S hS hW hε)

/-- **The `CoherentOn` packaging** (for `PCInductor`): any rational history whose day-`m` table on
`𝒮.S m` is the marginal of a world measure over `D` is `CoherentOn` at day `m` in `bli-finite`'s
sense.
Source: [[bli-coherent-mm-mandate]] T2(b) ("the `CoherentOn` form over a `SmallIndex`")
Kind: L
Fidelity: exact -/
theorem coherentOn_actualTable_of_marginal (𝒮 : SmallIndex) (m : ℕ) (Q : RatHistory)
    {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence} (hw : IsWorldMeasure w D)
    (hQ : ∀ φ ∈ 𝒮.S m, Q m φ = marginal w φ) : CoherentOn (actualTable 𝒮 Q m) D B :=
  ⟨w, hw.1, hw.2.1, hw.2.2, fun φ => hQ φ.1 φ.2⟩

/-- **T2(c). The coherent maker respects the stage**: a sentence of `S` true in every
`D`-consistent world is quoted `1` (Soto's Def 3; automatic for a marginal over `D`-consistent
worlds).
Source: [[bli-coherent-mm-mandate]] T2(c); Soto PDF 05 Def 3; [[bli-program]] §3.8
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_respects_true {φ : Sentence} (hφ : φ ∈ S)
    (h : ∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) :
    (coherentMarketMaker T past D B S hS hW hε).quote φ = 1 := by
  rw [coherentMarketMaker_quote_eq_pi T past D B S hS hW hε hφ]
  exact marginal_of_decided_true (coherentWeights_isWorldMeasure T past D B S hS hW hε) h

/-- **T2(c), dual**: a sentence of `S` false in every `D`-consistent world is quoted `0`.
Source: [[bli-coherent-mm-mandate]] T2(c); Soto PDF 05 Def 3
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_respects_false {φ : Sentence} (hφ : φ ∈ S)
    (h : ∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) :
    (coherentMarketMaker T past D B S hS hW hε).quote φ = 0 := by
  rw [coherentMarketMaker_quote_eq_pi T past D B S hS hW hε hφ]
  exact marginal_of_decided_false (coherentWeights_isWorldMeasure T past D B S hS hW hε) h

/-- The maker's quote is its weights' marginal on the past-and-day candidate history (the day-`n`
cell on `S`), for the entry point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem candidateRationalHistory_coherentMarketMaker :
    candidateRationalHistory past n (coherentMarketMaker T past D B S hS hW hε) =
      candidateTable past n S (coherentWeights T past D B S hS hW hε) :=
  candidateRationalHistory_ofWeights past n S _ _

end Maker

/-! ## T2(e): the `smallSet` variant -/

/-- **T2(e). The coherent market maker on all of `smallSet n`**: T2 is parametric in `S`, so the
instance `S = smallSet n` is the same theorem with `hS : mentionedSet T ⊆ smallSet n` (from
`bli-overlay`'s `firm_mentioned_small`, from `N₀` on). Its *existence* is not open; only the
cost of the `2^B` worlds over the atoms of `smallSet n` is (Known issue 4).
Source: [[bli-coherent-mm-mandate]] T2(e); [[bli-program]] §2.7 (the "(variant)")
Kind: D
Fidelity: exact -/
noncomputable abbrev coherentMarketMakerSmall {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
    (hS : mentionedSet T ⊆ smallSet n) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)
    {ε : ℚ} (hε : 0 < ε) : RationalBeliefState :=
  coherentMarketMaker T past D B (smallSet n) hS hW hε

/-- T2(b) at the `smallSet` variant: accepted in every `D`-consistent world.
Source: [[bli-coherent-mm-mandate]] T2(e)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem coherentMarketMakerSmall_accepts {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
    (hS : mentionedSet T ⊆ smallSet n) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)
    {ε : ℚ} (hε : 0 < ε) :
    ∀ u ∈ WD D B,
      T.marketValueRat (candidateRationalHistory past n (coherentMarketMakerSmall T past D B hS hW hε))
        u.payoutRat ≤ ε :=
  coherentMarketMaker_accepts T past D B (smallSet n) hS hW hε

/-- T2(b) at the `smallSet` variant: coherent on all of `smallSet n`.
Source: [[bli-coherent-mm-mandate]] T2(e)
Kind: C
Fidelity: variant: as `coherentMarketMaker_coherent`
Hyps: (a) -/
theorem coherentMarketMakerSmall_coherent {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
    (hS : mentionedSet T ⊆ smallSet n) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)
    {ε : ℚ} (hε : 0 < ε) :
    CoherentQuoteOn (coherentMarketMakerSmall T past D B hS hW hε).quote (smallSet n) D B :=
  coherentMarketMaker_coherent T past D B (smallSet n) hS hW hε

/-! ## T3: the interior, truth-respecting maker -/

/-- **D3, interior clause**: coherently accepted with full support on the `D`-consistent worlds.
Source: [[bli-coherent-mm-mandate]] D4 (`interiorCoherentMarketMaker`)
Kind: D
Fidelity: exact -/
def CoherentAcceptsFull {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) (w : FiniteWorld B → ℚ) : Prop :=
  (∀ u ∈ WD D B, 0 < w u) ∧ CoherentAccepts T past D B S ε w

/-- Decidable, as `CoherentAccepts`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
instance instDecidableCoherentAcceptsFull {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) (w : FiniteWorld B → ℚ) :
    Decidable (CoherentAcceptsFull T past D B S ε w) := by
  unfold CoherentAcceptsFull
  infer_instance

section Interior

variable {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
  (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
  (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε)

/-- **D4. The weights of the interior maker**: the first enumerated world measure over `D` with
full support on `WD D B` accepted at `ε` (totality from T3(a)).
Source: [[bli-coherent-mm-mandate]] D4
Kind: D
Fidelity: exact -/
noncomputable def interiorWeights : FiniteWorld B → ℚ :=
  firstAccepted (CoherentAcceptsFull T past D B S ε)
    (exists_coherentAccepts_fullSupport T past D B S hS hW hε)

/-- The interior weights are accepted with full support.
Source: [[bli-coherent-mm-mandate]] T3
Kind: L
Fidelity: exact -/
lemma interiorWeights_spec : CoherentAcceptsFull T past D B S ε (interiorWeights T past D B S hS hW hε) :=
  firstAccepted_accepts _ _

/-- The interior weights are a world measure over `D`.
Source: [[bli-coherent-mm-mandate]] T3
Kind: L
Fidelity: exact -/
lemma interiorWeights_isWorldMeasure : IsWorldMeasure (interiorWeights T past D B S hS hW hε) D :=
  (interiorWeights_spec T past D B S hS hW hε).2.1

/-- **D4. The interior, truth-respecting coherent market maker**: `ofWeights S` of
`interiorWeights …`.
Source: [[bli-coherent-mm-mandate]] D4; [[bli-program]] §3.8 ("interior, truth-respecting variant")
Kind: D
Fidelity: exact -/
noncomputable def interiorCoherentMarketMaker : RationalBeliefState :=
  ofWeights S (interiorWeights T past D B S hS hW hε) (interiorWeights_isWorldMeasure T past D B S hS hW hε)

/-- The interior maker's quote on `S` is the marginal of its weights.
Source: [[bli-coherent-mm-mandate]] D4
Kind: L
Fidelity: exact -/
lemma interior_quote_eq_pi {φ : Sentence} (hφ : φ ∈ S) :
    (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ =
      marginal (interiorWeights T past D B S hS hW hε) φ :=
  ofWeights_quote_of_mem _ hφ

/-- **T3. The interior maker is accepted in every `D`-consistent world** at `ε`.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_accepts`)
Kind: C
Fidelity: exact
Hyps: (a) `hS`, `hW`, `hε` -/
theorem interior_accepts :
    ∀ u ∈ WD D B,
      T.marketValueRat (candidateRationalHistory past n (interiorCoherentMarketMaker T past D B S hS hW hε))
        u.payoutRat ≤ ε :=
  (coherentAccepts_iff T past D B S ε (interiorWeights_isWorldMeasure T past D B S hS hW hε)).mp
    (interiorWeights_spec T past D B S hS hW hε).2

/-- The interior maker's weights are coherently accepted (D3 form, for the recursion).
Source: [[bli-coherent-mm-mandate]] T3
Kind: L
Fidelity: exact -/
theorem interior_coherentAccepts :
    CoherentAccepts T past D B S ε (interiorWeights T past D B S hS hW hε) :=
  (interiorWeights_spec T past D B S hS hW hε).2

/-- **T3. Full support**: every `D`-consistent world over `B` atoms has positive weight.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_fullSupport`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem interior_fullSupport : ∀ u ∈ WD D B, 0 < interiorWeights T past D B S hS hW hε u :=
  (interiorWeights_spec T past D B S hS hW hε).1

/-- **T3. The interior maker is coherent on `S`.**
Source: [[bli-coherent-mm-mandate]] T3 (`interior_coherent`)
Kind: C
Fidelity: variant: as `coherentMarketMaker_coherent`
Hyps: (a) -/
theorem interior_coherent :
    CoherentQuoteOn (interiorCoherentMarketMaker T past D B S hS hW hε).quote S D B :=
  ⟨interiorWeights T past D B S hS hW hε, interiorWeights_isWorldMeasure T past D B S hS hW hε,
    fun _ hφ => interior_quote_eq_pi T past D B S hS hW hε hφ⟩

/-- **T3. Non-dogmatism of a full-support marginal**: a sentence held by some `D`-consistent world
and refuted by another is priced strictly inside `(0,1)`.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_nonDogmatic`), the engine
Kind: P
Fidelity: exact -/
theorem nonDogmatic_of_fullSupport {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (hfull : ∀ u ∈ WD D B, 0 < w u) {φ : Sentence}
    (h1 : ∃ u ∈ WD D B, (worldOf u).Holds φ) (h2 : ∃ u ∈ WD D B, ¬ (worldOf u).Holds φ) :
    0 < marginal w φ ∧ marginal w φ < 1 := by
  obtain ⟨u₁, hu₁, h₁⟩ := h1
  obtain ⟨u₂, hu₂, h₂⟩ := h2
  constructor
  · exact marginal_pos_of_holds hw (hfull u₁ hu₁) h₁
  · have hneg : 0 < marginal w (∼φ) :=
      marginal_pos_of_holds hw (hfull u₂ hu₂) ((PCWorld.holds_neg _ _).mpr h₂)
    have hsum := marginal_neg_add hw φ
    linarith

/-- **T3. The interior maker is non-dogmatic on undecided sentences**: a sentence of `S` held by
some `D`-consistent world and refuted by another is quoted strictly inside `(0,1)`. Decided
sentences are at `0`/`1` (`interior_decided_at_truth`): "full support" is on worlds, not "every
sentence in `(0,1)`".
Source: [[bli-coherent-mm-mandate]] T3 (`interior_nonDogmatic`); [[bli-program]] §3.8
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem interior_nonDogmatic {φ : Sentence} (hφ : φ ∈ S)
    (h1 : ∃ u ∈ WD D B, (worldOf u).Holds φ) (h2 : ∃ u ∈ WD D B, ¬ (worldOf u).Holds φ) :
    0 < (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ ∧
      (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ < 1 := by
  rw [interior_quote_eq_pi T past D B S hS hW hε hφ]
  exact nonDogmatic_of_fullSupport (interiorWeights_isWorldMeasure T past D B S hS hW hε)
    (interior_fullSupport T past D B S hS hW hε) h1 h2

/-- **T3. The interior maker prices decided sentences at their truth** (T2(c) again).
Source: [[bli-coherent-mm-mandate]] T3 (`interior_decided_at_truth`)
Kind: L
Fidelity: exact -/
theorem interior_decided_at_truth {φ : Sentence} (hφ : φ ∈ S) :
    ((∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) →
      (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ = 1) ∧
    ((∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) →
      (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ = 0) := by
  constructor
  · intro h
    rw [interior_quote_eq_pi T past D B S hS hW hε hφ]
    exact marginal_of_decided_true (interiorWeights_isWorldMeasure T past D B S hS hW hε) h
  · intro h
    rw [interior_quote_eq_pi T past D B S hS hW hε hφ]
    exact marginal_of_decided_false (interiorWeights_isWorldMeasure T past D B S hS hW hε) h

end Interior

/-- **The `D_ND` clause for a full-support marginal**, `PCWorld` form: every sentence within the
atom bound is decided true by `D`, decided false by `D`, or priced strictly inside `(0,1)`
(restrict the `PCWorld` witnesses to `B` atoms).
Source: [[bli-coherent-mm-mandate]] T3 (`interior_D_ND_day`); bli-found `D_ND`
Kind: C
Fidelity: exact
Hyps: (a) `hB` (atom bound on `D` and `φ`) -/
theorem trichotomy_of_fullSupport {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (hfull : ∀ u ∈ WD D B, 0 < w u) (hD : ∀ φ ∈ D, atomBound φ ≤ B)
    {φ : Sentence} (hφ : atomBound φ ≤ B) :
    (∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) ∨
    (∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) ∨
    (0 < marginal w φ ∧ marginal w φ < 1) := by
  by_cases h1 : ∀ v : PCWorld, v.ConsistentWith D → v.Holds φ
  · exact Or.inl h1
  by_cases h2 : ∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  simp only [not_forall, not_not] at h1 h2
  obtain ⟨v₂, hv₂, hv₂φ⟩ := h1
  obtain ⟨v₁, hv₁, hv₁φ⟩ := h2
  apply nonDogmatic_of_fullSupport hw hfull
  · exact ⟨_, restrict_mem_WD hD hv₁, (holds_worldOf_restrict v₁ hφ).mpr hv₁φ⟩
  · exact ⟨_, restrict_mem_WD hD hv₂, fun h => hv₂φ ((holds_worldOf_restrict v₂ hφ).mp h)⟩

/-- **T3. `interior_D_ND_day`: the interior maker on `S = smallSet n` satisfies the day-`n` clause
of `bli-found`'s `D_ND`** — every small sentence is decided true by `D`, decided false by `D`, or
quoted strictly inside `(0,1)` — given the atom bound on `smallSet n ∪ D`. The customers'
(`bli-superbelief` E6/L5) entry point.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_D_ND_day`); bli-found `D_ND`
Kind: C
Fidelity: exact (the day-`n` clause of `D_ND`, with the quote in place of `Q n`)
Hyps: (a) `hB`, `hS`, `hW`, `hε` -/
theorem interior_D_ND_day {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (hB : ∀ φ ∈ smallSet n ∪ D, atomBound φ ≤ B)
    (hS : mentionedSet T ⊆ smallSet n) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)
    {ε : ℚ} (hε : 0 < ε) :
    ∀ φ ∈ smallSet n,
      (∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) ∨
      (∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) ∨
      (0 < (interiorCoherentMarketMaker T past D B (smallSet n) hS hW hε).quote φ ∧
        (interiorCoherentMarketMaker T past D B (smallSet n) hS hW hε).quote φ < 1) := by
  intro φ hφ
  rw [interior_quote_eq_pi T past D B (smallSet n) hS hW hε hφ]
  exact trichotomy_of_fullSupport (interiorWeights_isWorldMeasure T past D B (smallSet n) hS hW hε)
    (interior_fullSupport T past D B (smallSet n) hS hW hε)
    (fun ψ hψ => hB ψ (Finset.mem_union_right _ hψ)) (hB φ (Finset.mem_union_left _ hφ))

end Cleanroom.Bli.BliCoherentMm.AttemptA
