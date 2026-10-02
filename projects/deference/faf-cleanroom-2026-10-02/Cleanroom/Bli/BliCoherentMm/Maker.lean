import Cleanroom.Bli.BliCoherentMm.Accept
import Cleanroom.Bli.BliCoherentMm.AttemptA.Maker
import Cleanroom.Bli.BliCoherentMm.AttemptB.Interior

/-!
# `bli-coherent-mm` · Maker (reconciled): D4 the coherent and interior market makers, T2(b)–(e),
T3 — and attempt B's grid maker, accepted by the record's D3

**D4 of record: attempt A's makers** — `coherentMarketMaker` / `coherentWeights`, the **first
accepted candidate of a total enumeration** of rational weight vectors (`Nat.find` on the
decidable `CoherentAccepts`, FAF's own "first accepted candidate" idiom, the mandate's primary
description of D4), and `interiorCoherentMarketMaker` / `interiorWeights`, the same with full
support on `WD D B`. Attempt B's makers — the real fixed point *chosen* (`Classical.choose`)
and **rounded** at a mesh found by `Nat.find` — are kept as the **grid variant of record**
(`gridCoherentMarketMaker`, `gridInteriorCoherentMarketMaker`): their weights lie on the grid
`(1/mesh)·ℕ` (`gridCoherentWeights_mem_grid`), the `coherentGrid` shape `bli-measure` asks for.
Both makers are proved **accepted by the record's D3** (`coherentWeights_accepts`,
`gridCoherentWeights_accepts`): the two attempts' makers choose different candidates and pass
the same test — the mandate's cross-check.

Why attempt A's is of record (tie-break: no new axioms on either side, zero `(c)` clauses on
either side, so "definitional stand-ins counted"): attempt A's candidate is found by a search
whose acceptance test is a `Decidable` instance, and its only classical element is the
enumeration order (`Fintype.equivFin`, findings F10); attempt B's candidate is a rounding of a
`Classical.choose`-selected real vector, with the `clamp01` device inside `ofWeights`. Both
are `noncomputable`, as FAF's `MarketMaker` is.

Coherence of a *quote* is stated as `CoherentQuoteOn` (agreement with a world marginal on `S`),
not as `bli-finite`'s `IsWorldMarginal` of the quote on `GenBy S` (a finite-support state quotes
`0` off `S`, so the latter is unsatisfiable — findings F7/F-B2, found by both attempts); the
`IsWorldMarginal` form holds for the maker's full marginal (`coherentMarketMaker_isWorldMarginal`).

Sources: [[bli-coherent-mm-mandate]] D4, T2(b)–(e), T3; [[bli-program]] §3.8, §4 row M2.
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## Coherence of a quote -/

/-- **Coherence of a quote on `S`** (the statement shape of record for T2(b), T3, T6): `V`
agrees on `S` with the marginal of some world measure over `D` on `B` atoms. The
`IsWorldMarginal` form on `GenBy S` is unsatisfiable by a finite-support state (findings F7).
Source: [[bli-coherent-mm-mandate]] T2(b); bli-finite `CoherentOn`
Kind: D
Fidelity: variant: agreement with a world marginal on `S` (see the module docstring) -/
abbrev CoherentQuoteOn (V : Sentence → ℚ) (S D : Finset Sentence) (B : ℕ) : Prop :=
  AttemptA.CoherentQuoteOn V S D B

/-- **The `CoherentOn` packaging** (for `PCInductor` and `bli-measure`): a rational history
whose day-`m` table on `𝒮.S m` is the marginal of a world measure over `D` is `CoherentOn` at
day `m` in `bli-finite`'s sense.
Source: [[bli-coherent-mm-mandate]] T2(b) ("the `CoherentOn` form over a `SmallIndex`")
Kind: L
Fidelity: exact -/
theorem coherentOn_actualTable_of_marginal (𝒮 : SmallIndex) (m : ℕ) (Q : RatHistory)
    {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence} (hw : IsWorldMeasure w D)
    (hQ : ∀ φ ∈ 𝒮.S m, Q m φ = marginal w φ) : CoherentOn (actualTable 𝒮 Q m) D B :=
  AttemptA.coherentOn_actualTable_of_marginal 𝒮 m Q hw hQ

/-! ## D4: the coherent market maker (attempt A's enumeration search) -/

section Maker

variable {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
  (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
  (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε)

/-- **D4 (of record). The weights of the coherent market maker**: the first enumerated rational
world measure over `D` whose candidate table on `S` is accepted at `ε` in every `D`-consistent
world — the day's world measure (B3's customer object).
Source: [[bli-coherent-mm-mandate]] D4
Kind: D
Fidelity: exact -/
noncomputable abbrev coherentWeights : FiniteWorld B → ℚ :=
  AttemptA.coherentWeights T past D B S hS hW hε

/-- **D4 (of record). The coherent market maker**: the candidate state of `coherentWeights` on
`S`. Not FAF's `MarketMaker` renamed: a `Nat.find` over *world measures* with the
*consistent-world* check.
Source: [[bli-coherent-mm-mandate]] D4; [[bli-program]] §3.8, §4 row M2
Kind: D
Fidelity: exact -/
noncomputable abbrev coherentMarketMaker : RationalBeliefState :=
  AttemptA.coherentMarketMaker T past D B S hS hW hε

/-- The maker's weights are coherently accepted (D3 form).
Source: [[bli-coherent-mm-mandate]] T2(b)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem coherentWeights_accepts :
    CoherentAccepts T past D B S ε (coherentWeights T past D B S hS hW hε) :=
  AttemptA.coherentWeights_accepts T past D B S hS hW hε

/-- **T2(b). The maker's weights are a world measure over `D`.**
Source: [[bli-coherent-mm-mandate]] T2(b)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem coherentMarketMaker_isWorldMeasure :
    IsWorldMeasure (coherentWeights T past D B S hS hW hε) D :=
  AttemptA.coherentWeights_isWorldMeasure T past D B S hS hW hε

/-- **T2(b). The maker's quote on `S` is the marginal of its weights.**
Source: [[bli-coherent-mm-mandate]] D4 (`coherentMarketMaker_quote_eq_pi`)
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_quote_eq_pi {φ : Sentence} (hφ : φ ∈ S) :
    (coherentMarketMaker T past D B S hS hW hε).quote φ =
      marginal (coherentWeights T past D B S hS hW hε) φ :=
  AttemptA.coherentMarketMaker_quote_eq_pi T past D B S hS hW hε hφ

/-- **T2(b) (headline, M2). The coherent market maker is accepted in every `D`-consistent
world**: the exact rational value of `T` on FAF's `candidateRationalHistory past n
(coherentMarketMaker …)` is `≤ ε` in every `u ∈ WD D B`. Scope: over `D`-consistent worlds, on
`S ⊇ mentionedSet T`.
Source: [[bli-coherent-mm-mandate]] T2(b); [[bli-program]] §4 row M2
Kind: C
Fidelity: exact
Hyps: (a) `hS`, `hW`, `hε` — discharged in `Contrast.lean` / `Witness.lean` -/
theorem coherentMarketMaker_accepts :
    ∀ u ∈ WD D B,
      T.marketValueRat (candidateRationalHistory past n (coherentMarketMaker T past D B S hS hW hε))
        u.payoutRat ≤ ε :=
  AttemptA.coherentMarketMaker_accepts T past D B S hS hW hε

/-- **T2(b) (headline, M2). The coherent market maker's table is coherent on `S`**: on `S` its
quote is the marginal of its world-measure weights.
Source: [[bli-coherent-mm-mandate]] T2(b); [[bli-program]] §4 row M2
Kind: C
Fidelity: variant: coherence as agreement with a world marginal on `S` (findings F7)
Hyps: (a) -/
theorem coherentMarketMaker_coherent :
    CoherentQuoteOn (coherentMarketMaker T past D B S hS hW hε).quote S D B :=
  AttemptA.coherentMarketMaker_coherent T past D B S hS hW hε

/-- The maker's full marginal is a world marginal on `S` (the mandate's `IsWorldMarginal` form,
for the marginal function).
Source: [[bli-coherent-mm-mandate]] T2(b)
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_isWorldMarginal :
    IsWorldMarginal (marginal (coherentWeights T past D B S hS hW hε)) S D B :=
  AttemptA.coherentMarketMaker_isWorldMarginal T past D B S hS hW hε

/-- The two-axiom reading on `GenBy S` (bli-finite's `twoAxiom_of_worldMarginal`).
Source: [[bli-coherent-mm-mandate]] T2(b); bli-paper-030
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_twoAxiom :
    TwoAxiomCoherent (marginal (coherentWeights T past D B S hS hW hε)) S D :=
  AttemptA.coherentMarketMaker_twoAxiom T past D B S hS hW hε

/-- **T2(c). The maker respects the stage** (Soto's Def 3): a sentence of `S` true in every
`D`-consistent world is quoted `1` — automatic for a marginal over `D`-consistent worlds.
Source: [[bli-coherent-mm-mandate]] T2(c); Soto PDF 05 Def 3; [[bli-program]] §3.8
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_respects_true {φ : Sentence} (hφ : φ ∈ S)
    (h : ∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) :
    (coherentMarketMaker T past D B S hS hW hε).quote φ = 1 :=
  AttemptA.coherentMarketMaker_respects_true T past D B S hS hW hε hφ h

/-- **T2(c), dual.** A sentence of `S` false in every `D`-consistent world is quoted `0`.
Source: [[bli-coherent-mm-mandate]] T2(c)
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_respects_false {φ : Sentence} (hφ : φ ∈ S)
    (h : ∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) :
    (coherentMarketMaker T past D B S hS hW hε).quote φ = 0 :=
  AttemptA.coherentMarketMaker_respects_false T past D B S hS hW hε hφ h

end Maker

/-! ## T2(e): the `smallSet` variant -/

/-- **T2(e). The coherent market maker on all of `smallSet n`**: T2 is parametric in `S`; this
is the instance `S = smallSet n`. Its *existence* is not open; only the cost of the `2^B`
worlds over the atoms of `smallSet n` is (Known issue 4).
Source: [[bli-coherent-mm-mandate]] T2(e); [[bli-program]] §2.7
Kind: D
Fidelity: exact -/
noncomputable abbrev coherentMarketMakerSmall {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
    (hS : mentionedSet T ⊆ smallSet n) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)
    {ε : ℚ} (hε : 0 < ε) : RationalBeliefState :=
  AttemptA.coherentMarketMakerSmall T past D B hS hW hε

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
      T.marketValueRat
        (candidateRationalHistory past n (coherentMarketMakerSmall T past D B hS hW hε))
        u.payoutRat ≤ ε :=
  AttemptA.coherentMarketMakerSmall_accepts T past D B hS hW hε

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
  AttemptA.coherentMarketMakerSmall_coherent T past D B hS hW hε

/-! ## T3: the interior, truth-respecting maker -/

/-- **D3, interior clause**: coherently accepted with full support on the `D`-consistent
worlds. Decidable.
Source: [[bli-coherent-mm-mandate]] D4 (`interiorCoherentMarketMaker`)
Kind: D
Fidelity: exact -/
abbrev CoherentAcceptsFull {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) (w : FiniteWorld B → ℚ) : Prop :=
  AttemptA.CoherentAcceptsFull T past D B S ε w

section Interior

variable {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
  (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
  (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε)

/-- **D4 (of record). The weights of the interior maker**: the first enumerated world measure
over `D` with full support on `WD D B` accepted at `ε`.
Source: [[bli-coherent-mm-mandate]] D4
Kind: D
Fidelity: exact -/
noncomputable abbrev interiorWeights : FiniteWorld B → ℚ :=
  AttemptA.interiorWeights T past D B S hS hW hε

/-- **D4 (of record). The interior, truth-respecting coherent market maker**: `ofWeights S` of
`interiorWeights` — non-dogmatic on every sentence of `S` undecided by `D`, decided sentences at
their truth.
Source: [[bli-coherent-mm-mandate]] D4; [[bli-program]] §3.8
Kind: D
Fidelity: exact -/
noncomputable abbrev interiorCoherentMarketMaker : RationalBeliefState :=
  AttemptA.interiorCoherentMarketMaker T past D B S hS hW hε

/-- The interior weights are a world measure over `D`.
Source: [[bli-coherent-mm-mandate]] T3
Kind: L
Fidelity: exact -/
theorem interiorWeights_isWorldMeasure : IsWorldMeasure (interiorWeights T past D B S hS hW hε) D :=
  AttemptA.interiorWeights_isWorldMeasure T past D B S hS hW hε

/-- The interior maker's quote on `S` is the marginal of its weights.
Source: [[bli-coherent-mm-mandate]] D4
Kind: L
Fidelity: exact -/
theorem interior_quote_eq_pi {φ : Sentence} (hφ : φ ∈ S) :
    (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ =
      marginal (interiorWeights T past D B S hS hW hε) φ :=
  AttemptA.interior_quote_eq_pi T past D B S hS hW hε hφ

/-- **T3. The interior maker is accepted in every `D`-consistent world** at `ε`.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_accepts`)
Kind: C
Fidelity: exact
Hyps: (a) `hS`, `hW`, `hε` -/
theorem interior_accepts :
    ∀ u ∈ WD D B,
      T.marketValueRat
        (candidateRationalHistory past n (interiorCoherentMarketMaker T past D B S hS hW hε))
        u.payoutRat ≤ ε :=
  AttemptA.interior_accepts T past D B S hS hW hε

/-- The interior weights are coherently accepted (D3 form, for the recursion).
Source: [[bli-coherent-mm-mandate]] T3
Kind: L
Fidelity: exact -/
theorem interior_coherentAccepts :
    CoherentAccepts T past D B S ε (interiorWeights T past D B S hS hW hε) :=
  AttemptA.interior_coherentAccepts T past D B S hS hW hε

/-- **T3. Full support**: every `D`-consistent world over `B` atoms has positive weight.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_fullSupport`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem interior_fullSupport : ∀ u ∈ WD D B, 0 < interiorWeights T past D B S hS hW hε u :=
  AttemptA.interior_fullSupport T past D B S hS hW hε

/-- **T3. The interior maker is coherent on `S`.**
Source: [[bli-coherent-mm-mandate]] T3 (`interior_coherent`)
Kind: C
Fidelity: variant: as `coherentMarketMaker_coherent`
Hyps: (a) -/
theorem interior_coherent :
    CoherentQuoteOn (interiorCoherentMarketMaker T past D B S hS hW hε).quote S D B :=
  AttemptA.interior_coherent T past D B S hS hW hε

/-- **T3 (headline, M2). The interior maker is non-dogmatic on undecided sentences**: a
sentence of `S` held by some `D`-consistent world and refuted by another is quoted strictly
inside `(0,1)`. Decided sentences are at `0`/`1` (`interior_decided_at_truth`): "full support"
is on worlds, not "every sentence in `(0,1)`".
Source: [[bli-coherent-mm-mandate]] T3 (`interior_nonDogmatic`); [[bli-program]] §3.8
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem interior_nonDogmatic {φ : Sentence} (hφ : φ ∈ S)
    (h1 : ∃ u ∈ WD D B, (worldOf u).Holds φ) (h2 : ∃ u ∈ WD D B, ¬ (worldOf u).Holds φ) :
    0 < (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ ∧
      (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ < 1 :=
  AttemptA.interior_nonDogmatic T past D B S hS hW hε hφ h1 h2

/-- **T3. The interior maker prices decided sentences at their truth** (T2(c) again).
Source: [[bli-coherent-mm-mandate]] T3 (`interior_decided_at_truth`)
Kind: L
Fidelity: exact -/
theorem interior_decided_at_truth {φ : Sentence} (hφ : φ ∈ S) :
    ((∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) →
      (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ = 1) ∧
    ((∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) →
      (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ = 0) :=
  AttemptA.interior_decided_at_truth T past D B S hS hW hε hφ

/-- **T3, the `D_ND` clause at day `n` on a general sentence set `S`** (attempt B's shape,
proved over the record maker): every `φ ∈ S` within the atom bound is decided true by `D`,
decided false by `D`, or quoted strictly inside `(0,1)`.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_D_ND_day`); bli-found `D_ND`
Kind: C
Fidelity: exact (one day; the quote in place of `Q n`)
Hyps: (a) `hD`, `hBS` (atom bounds on `D` and `S`), `hS`, `hW`, `hε` -/
theorem interior_D_ND_day_on (hD : ∀ ψ ∈ D, atomBound ψ ≤ B) (hBS : ∀ φ ∈ S, atomBound φ ≤ B) :
    ∀ φ ∈ S,
      (∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) ∨
      (∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) ∨
      (0 < (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ ∧
        (interiorCoherentMarketMaker T past D B S hS hW hε).quote φ < 1) := by
  intro φ hφ
  rw [interior_quote_eq_pi T past D B S hS hW hε hφ]
  exact AttemptA.trichotomy_of_fullSupport (interiorWeights_isWorldMeasure T past D B S hS hW hε)
    (interior_fullSupport T past D B S hS hW hε) hD (hBS φ hφ)

end Interior

/-- **T3. Non-dogmatism of a full-support marginal** (the engine): a sentence held by some
`D`-consistent world and refuted by another is priced strictly inside `(0,1)`.
Source: [[bli-coherent-mm-mandate]] T3
Kind: P
Fidelity: exact -/
theorem nonDogmatic_of_fullSupport {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (hfull : ∀ u ∈ WD D B, 0 < w u) {φ : Sentence}
    (h1 : ∃ u ∈ WD D B, (worldOf u).Holds φ) (h2 : ∃ u ∈ WD D B, ¬ (worldOf u).Holds φ) :
    0 < marginal w φ ∧ marginal w φ < 1 :=
  AttemptA.nonDogmatic_of_fullSupport hw hfull h1 h2

/-- **The `D_ND` trichotomy for a full-support marginal**, `PCWorld` form.
Source: [[bli-coherent-mm-mandate]] T3 (`interior_D_ND_day`); bli-found `D_ND`
Kind: C
Fidelity: exact
Hyps: (a) `hD`, `hφ` (atom bounds) -/
theorem trichotomy_of_fullSupport {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (hfull : ∀ u ∈ WD D B, 0 < w u) (hD : ∀ φ ∈ D, atomBound φ ≤ B)
    {φ : Sentence} (hφ : atomBound φ ≤ B) :
    (∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) ∨
    (∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) ∨
    (0 < marginal w φ ∧ marginal w φ < 1) :=
  AttemptA.trichotomy_of_fullSupport hw hfull hD hφ

/-- **T3. `interior_D_ND_day` (of record): the interior maker on `S = smallSet n` satisfies the
day-`n` clause of `bli-found`'s `D_ND`** — every small sentence is decided true by `D`, decided
false by `D`, or quoted strictly inside `(0,1)` — given the atom bound on `smallSet n ∪ D`. The
entry point of `bli-superbelief` (E6/L5).
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
        (interiorCoherentMarketMaker T past D B (smallSet n) hS hW hε).quote φ < 1) :=
  AttemptA.interior_D_ND_day T past D B hB hS hW hε

/-! ## The grid variant of record: attempt B's rounded fixed point, accepted by the record's D3 -/

section Grid

variable {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
  (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
  (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)
  (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ) (hε : 0 < ε)

/-- **The accepted mesh** of attempt B's maker: the first `d` (by `Nat.find`) at which the real
fixed point rounded at `1/d` is a world measure accepted at `ε`.
Source: [[bli-coherent-mm-mandate]] D4 (angle B)
Kind: D
Fidelity: exact -/
noncomputable abbrev gridCoherentMesh : ℕ := AttemptB.coherentMesh T past D B hB hW S hS ε hε

/-- **D4, grid variant of record: the coherent weights on the grid** — attempt B's rounded fixed
point, every coordinate a multiple of `1 / gridCoherentMesh` (`gridCoherentWeights_mem_grid`),
`bli-finite`'s `worldWeights`/`coherentGrid` shape for `bli-measure`.
Source: [[bli-coherent-mm-mandate]] D4 (angle B), §Lifecycle (the `coherentGrid`-shaped candidate)
Kind: D
Fidelity: exact -/
noncomputable abbrev gridCoherentWeights : FiniteWorld B → ℚ :=
  AttemptB.coherentWeights T past D B hB hW S hS ε hε

/-- **D4, grid variant: the coherent market maker on the grid** (attempt B's), the candidate
state of `gridCoherentWeights` on `S`.
Source: [[bli-coherent-mm-mandate]] D4 (angle B)
Kind: D
Fidelity: exact (attempt B's `ofWeights` clamps; the clamp is the identity on a world measure) -/
noncomputable abbrev gridCoherentMarketMaker : RationalBeliefState :=
  AttemptB.coherentMarketMaker T past D B hB hW S hS ε hε

/-- The grid weights are a world measure over `D`.
Source: [[bli-coherent-mm-mandate]] T2(b) (grid variant)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem gridCoherentWeights_isWorldMeasure :
    IsWorldMeasure (gridCoherentWeights T past D B hB hW S hS ε hε) D :=
  AttemptB.coherentWeights_isWorldMeasure T past D B hB hW S hS ε hε

/-- **The two makers accept the same predicate (the mandate's cross-check)**: attempt B's grid
weights are accepted by the **record's** D3 — the test attempt A's maker passes — although the
two makers' candidates differ (one is the first enumerated accepted vector, the other a rounded
fixed point).
Source: [[bli-coherent-mm-mandate]] §Deliverables ("the two makers accept the same predicate (D3)")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem gridCoherentWeights_accepts :
    CoherentAccepts T past D B S ε (gridCoherentWeights T past D B hB hW S hS ε hε) :=
  (coherentAccepts_iff_attemptB T past D B S ε
    (gridCoherentWeights_isWorldMeasure T past D B hB hW S hS ε hε) hS).mpr
    (AttemptB.coherentMarketMaker_accepts T past D B hB hW S hS ε hε)

/-- **The grid shape**: every grid weight is `k / gridCoherentMesh` for a natural `k`.
Source: [[bli-coherent-mm-mandate]] §Attempt angles (B); bli-finite `worldWeights`/`coherentGrid`
Kind: L
Fidelity: exact -/
theorem gridCoherentWeights_mem_grid (u : FiniteWorld B) :
    ∃ k : ℕ, gridCoherentWeights T past D B hB hW S hS ε hε u =
      (k : ℚ) / gridCoherentMesh T past D B hB hW S hS ε hε :=
  AttemptB.coherentWeights_mem_grid T past D B hB hW S hS ε hε u

/-- The grid maker's quote on `S` is the marginal of its weights.
Source: [[bli-coherent-mm-mandate]] D4 (`coherentMarketMaker_quote_eq_pi`, grid variant)
Kind: L
Fidelity: exact -/
theorem gridCoherentMarketMaker_quote_eq_pi {φ : Sentence} (hφ : φ ∈ S) :
    (gridCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ =
      marginal (gridCoherentWeights T past D B hB hW S hS ε hε) φ :=
  AttemptB.coherentMarketMaker_quote_eq_pi T past D B hB hW S hS ε hε hφ

/-- **T2(b), grid variant: the grid maker is coherent on `S`** in the record's sense.
Source: [[bli-coherent-mm-mandate]] T2(b) (grid variant)
Kind: C
Fidelity: variant: as `coherentMarketMaker_coherent`
Hyps: (a) -/
theorem gridCoherentMarketMaker_coherent :
    CoherentQuoteOn (gridCoherentMarketMaker T past D B hB hW S hS ε hε).quote S D B :=
  ⟨gridCoherentWeights T past D B hB hW S hS ε hε,
    gridCoherentWeights_isWorldMeasure T past D B hB hW S hS ε hε,
    fun _ hφ => gridCoherentMarketMaker_quote_eq_pi T past D B hB hW S hS ε hε hφ⟩

/-- **D4, grid variant: the interior weights on the grid** — attempt B's fixed point mixed with
the uniform measure and rounded, with full support on `WD D B`.
Source: [[bli-coherent-mm-mandate]] D4 (interior variant, angle B)
Kind: D
Fidelity: exact -/
noncomputable abbrev gridInteriorWeights : FiniteWorld B → ℚ :=
  AttemptB.interiorWeights T past D B hB hW S hS ε hε

/-- **D4, grid variant: the interior coherent market maker on the grid** (attempt B's).
Source: [[bli-coherent-mm-mandate]] D4 (interior variant, angle B)
Kind: D
Fidelity: exact -/
noncomputable abbrev gridInteriorCoherentMarketMaker : RationalBeliefState :=
  AttemptB.interiorCoherentMarketMaker T past D B hB hW S hS ε hε

/-- The grid interior weights are a world measure over `D`.
Source: [[bli-coherent-mm-mandate]] T3 (grid variant)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem gridInteriorWeights_isWorldMeasure :
    IsWorldMeasure (gridInteriorWeights T past D B hB hW S hS ε hε) D :=
  AttemptB.interior_isWorldMeasure T past D B hB hW S hS ε hε

/-- **The grid interior maker is accepted by the record's D3** (cross-check, interior variant).
Source: [[bli-coherent-mm-mandate]] §Deliverables (cross-check); T3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem gridInteriorWeights_accepts :
    CoherentAccepts T past D B S ε (gridInteriorWeights T past D B hB hW S hS ε hε) :=
  (coherentAccepts_iff_attemptB T past D B S ε
    (gridInteriorWeights_isWorldMeasure T past D B hB hW S hS ε hε) hS).mpr
    (AttemptB.interior_accepts T past D B hB hW S hS ε hε)

/-- **T3, grid variant: full support on `WD D B`.**
Source: [[bli-coherent-mm-mandate]] T3 (grid variant)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem gridInteriorWeights_fullSupport :
    ∀ u ∈ WD D B, 0 < gridInteriorWeights T past D B hB hW S hS ε hε u := by
  intro u hu
  rw [WD_eq_attemptB] at hu
  exact AttemptB.interior_fullSupport T past D B hB hW S hS ε hε u hu

/-- The grid interior maker's quote on `S` is the marginal of its weights.
Source: [[bli-coherent-mm-mandate]] D4 (grid variant)
Kind: L
Fidelity: exact -/
theorem gridInteriorCoherentMarketMaker_quote_eq_pi {φ : Sentence} (hφ : φ ∈ S) :
    (gridInteriorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ =
      marginal (gridInteriorWeights T past D B hB hW S hS ε hε) φ :=
  AttemptB.interior_quote_eq_pi T past D B hB hW S hS ε hε hφ

/-- **T3, grid variant: non-dogmatism** on sentences of `S` undecided by `D`.
Source: [[bli-coherent-mm-mandate]] T3 (grid variant)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem gridInterior_nonDogmatic {φ : Sentence} (hφ : φ ∈ S)
    (h1 : ∃ u ∈ WD D B, (worldOf u).Holds φ) (h2 : ∃ u ∈ WD D B, ¬ (worldOf u).Holds φ) :
    0 < (gridInteriorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ ∧
      (gridInteriorCoherentMarketMaker T past D B hB hW S hS ε hε).quote φ < 1 := by
  rw [gridInteriorCoherentMarketMaker_quote_eq_pi T past D B hB hW S hS ε hε hφ]
  exact nonDogmatic_of_fullSupport (gridInteriorWeights_isWorldMeasure T past D B hB hW S hS ε hε)
    (gridInteriorWeights_fullSupport T past D B hB hW S hS ε hε) h1 h2

end Grid

end Cleanroom.Bli.BliCoherentMm
