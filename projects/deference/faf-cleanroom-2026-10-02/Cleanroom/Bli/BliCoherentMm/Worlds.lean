import Cleanroom.Bli.BliCoherentMm.AttemptA.Worlds
import Cleanroom.Bli.BliCoherentMm.AttemptB.Accept

/-!
# `bli-coherent-mm` · Worlds (reconciled): D1 the `D`-consistent worlds, D2 world measures,
marginals, candidate states — and the cross-check that the two attempts built the same objects

**Definitions of record: attempt A's** (`AttemptA.WD`, `AttemptA.IsWorldMeasure`,
`AttemptA.marginal`, `AttemptA.ofWeights`, `AttemptA.candidateTable`), re-exported here under the
package namespace. Attempt B built the same objects under other names (`worldsOf`,
`IsWorldMeasure D B w`, `piTable`, `ofWeights S w` with a `clamp01` totality device): this file
proves the identifications — the world sets are equal (`WD_eq_attemptB`, two `Decidable`
instances of the same filter), the measure predicates are the same proposition
(`isWorldMeasure_iff_attemptB`, by `Iff.rfl`), the price tables are the same term
(`marginal_eq_attemptB`, by `rfl`), and the candidate states quote the same function
(`ofWeights_quote_eq_attemptB`), so FAF's candidate histories of the two candidate states
coincide (`candidateTable_eq_attemptB`). These are what let every attempt-B theorem transport
to the record in the later files.

Why attempt A's are of record: the terms are identical where both attempts define them; where
they differ, A's `ofWeights S w hw` carries the `[0,1]` range as a proof (through
`bli-overlay`'s `restrictState`) where B's `ofWeights S w` clamps (`clamp01`, the identity on
world measures — a disclosed totality device), and A's `candidateTable` is the mandate's D3
table as a function of the weights alone. Zero `(c)` clauses on either side; the tie-break is
"no definitional device".

Sources: [[bli-coherent-mm-mandate]] D1, D2, §Deliverables (the reconciler's cross-check).
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## D1: the `D`-consistent worlds -/

/-- **D1 (of record). The `D`-consistent worlds over `B` atoms**
`{u : FiniteWorld B | (worldOf u).ConsistentWith D}`, a `Finset`. Meaningful under
`hB : ∀ φ ∈ D, atomBound φ ≤ B` (atoms `≥ B` read `false` in `worldOf u`).
Source: [[bli-coherent-mm-mandate]] D1
Kind: D
Fidelity: exact -/
abbrev WD (D : Finset Sentence) (B : ℕ) : Finset (FiniteWorld B) := AttemptA.WD D B

/-- Membership in `WD`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_WD {D : Finset Sentence} {B : ℕ} {u : FiniteWorld B} :
    u ∈ WD D B ↔ (worldOf u).ConsistentWith D :=
  AttemptA.mem_WD

/-- **The two attempts' D1 agree**: attempt B's `worldsOf D B` is the record's `WD D B` (the
same filter under two `Decidable` instances).
Source: [[bli-coherent-mm-mandate]] §Deliverables (reconciler cross-check)
Kind: L
Fidelity: exact -/
theorem WD_eq_attemptB (D : Finset Sentence) (B : ℕ) : WD D B = AttemptB.worldsOf D B := by
  ext u
  rw [mem_WD, AttemptB.mem_worldsOf]

/-- The restriction of a `PCWorld` consistent with `D` to `B` atoms lies in `WD D B`, provided
`D` is within the atom bound.
Source: [[bli-coherent-mm-mandate]] T1 (restriction)
Kind: L
Fidelity: n/a -/
theorem restrict_mem_WD {D : Finset Sentence} {B : ℕ} (hB : ∀ φ ∈ D, atomBound φ ≤ B)
    {v : PCWorld} (hv : v.ConsistentWith D) : FiniteWorld.restrict (ofPCWorld v) B ∈ WD D B :=
  AttemptA.restrict_mem_WD hB hv

/-- A `D`-consistent `PCWorld` yields a `D`-consistent finite world over any atom bound covering
`D` (the discharge of `hW` from FAF's `hworld`).
Source: [[bli-coherent-mm-mandate]] D1 (`hW`)
Kind: L
Fidelity: n/a -/
theorem exists_consistent_of_pcWorld {D : Finset Sentence} {B : ℕ}
    (hB : ∀ φ ∈ D, atomBound φ ≤ B) (h : ∃ v : PCWorld, v.ConsistentWith D) :
    ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D :=
  AttemptA.exists_consistent_of_pcWorld hB h

/-! ## D2: world measures and their marginals -/

/-- **D2 (of record). A world measure**: a rational probability on `FiniteWorld B` supported on
the `D`-consistent worlds — the witness shape of `bli-finite`'s `IsWorldMarginal`. Decidable.
Source: [[bli-coherent-mm-mandate]] D2; Soto PDF 05 Def 1
Kind: D
Fidelity: exact -/
abbrev IsWorldMeasure {B : ℕ} (w : FiniteWorld B → ℚ) (D : Finset Sentence) : Prop :=
  AttemptA.IsWorldMeasure w D

/-- **The two attempts' D2 agree**: attempt B's `IsWorldMeasure D B w` is the record's
`IsWorldMeasure w D` (the same proposition, arguments permuted).
Source: [[bli-coherent-mm-mandate]] §Deliverables (reconciler cross-check)
Kind: L
Fidelity: exact -/
theorem isWorldMeasure_iff_attemptB {B : ℕ} (w : FiniteWorld B → ℚ) (D : Finset Sentence) :
    IsWorldMeasure w D ↔ AttemptB.IsWorldMeasure D B w :=
  Iff.rfl

/-- A world measure in attempt B's shape (for feeding attempt B's lemmas).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsWorldMeasure.toB {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) : AttemptB.IsWorldMeasure D B w :=
  hw

/-- **D2 (of record). The marginal (price table) of a weight vector**:
`π w φ := ∑ u, w u * u.payoutRat φ`.
Source: [[bli-coherent-mm-mandate]] D2; Soto PDF 05 Def 1
Kind: D
Fidelity: exact -/
abbrev marginal {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) : ℚ := AttemptA.marginal w φ

/-- **The two attempts' price tables agree**: attempt B's `piTable` is the record's `marginal`,
term for term.
Source: [[bli-coherent-mm-mandate]] §Deliverables (reconciler cross-check)
Kind: L
Fidelity: exact -/
theorem marginal_eq_attemptB {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) :
    marginal w φ = AttemptB.piTable w φ :=
  rfl

/-- A world measure's marginal is in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem marginal_mem_Icc {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (φ : Sentence) : 0 ≤ marginal w φ ∧ marginal w φ ≤ 1 :=
  ⟨AttemptA.marginal_nonneg hw φ, AttemptA.marginal_le_one hw φ⟩

/-- A world measure's marginals of `φ` and `∼φ` sum to one (the two-axiom `neg_add`).
Source: [[bli-coherent-mm-mandate]] T4; bli-finite `TwoAxiomCoherent.neg_add`
Kind: L
Fidelity: exact -/
theorem marginal_neg_add {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (φ : Sentence) : marginal w φ + marginal w (∼φ) = 1 :=
  AttemptA.marginal_neg_add hw φ

/-- The marginal of a world measure is a world marginal on every algebra (`bli-finite`'s
`IsWorldMarginal`).
Source: [[bli-coherent-mm-mandate]] D2; [[bli-finite-report]]
Kind: L
Fidelity: exact -/
theorem isWorldMarginal_marginal {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (A : Finset Sentence) : IsWorldMarginal (marginal w) A D B :=
  AttemptA.isWorldMarginal_marginal hw A

/-- **Decided sentences are priced at their truth by every world measure** (true case): a
sentence true in every `D`-consistent `PCWorld` has marginal `1`. Soto's Def 3 ("respects `D̄`")
as a consequence of Def 1's support condition.
Source: [[bli-coherent-mm-mandate]] T2(c); Soto PDF 05 Def 3
Kind: L
Fidelity: exact -/
theorem marginal_of_decided_true {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) : marginal w φ = 1 :=
  AttemptA.marginal_of_decided_true hw h

/-- Decided sentences at their truth, false case.
Source: [[bli-coherent-mm-mandate]] T2(c)
Kind: L
Fidelity: exact -/
theorem marginal_of_decided_false {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) : marginal w φ = 0 :=
  AttemptA.marginal_of_decided_false hw h

/-! ## D2: candidate states and the candidate table -/

/-- **D2 (of record). The candidate belief state** of a world measure on `S`: entries
`(φ, π w φ)` for `φ ∈ S`, quote `0` off `S`; the range is a proof, never a clamp.
Source: [[bli-coherent-mm-mandate]] D2
Kind: D
Fidelity: exact -/
noncomputable abbrev ofWeights (S : Finset Sentence) {B : ℕ} (w : FiniteWorld B → ℚ)
    {D : Finset Sentence} (hw : IsWorldMeasure w D) : RationalBeliefState :=
  AttemptA.ofWeights S w hw

/-- On `S` the candidate quotes the marginal.
Source: [[bli-coherent-mm-mandate]] D2
Kind: L
Fidelity: exact -/
theorem ofWeights_quote_of_mem {S : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    {D : Finset Sentence} (hw : IsWorldMeasure w D) {φ : Sentence} (hφ : φ ∈ S) :
    (ofWeights S w hw).quote φ = marginal w φ :=
  AttemptA.ofWeights_quote_of_mem hw hφ

/-- Off `S` the candidate quotes `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ofWeights_quote_of_not_mem {S : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    {D : Finset Sentence} (hw : IsWorldMeasure w D) {φ : Sentence} (hφ : φ ∉ S) :
    (ofWeights S w hw).quote φ = 0 :=
  AttemptA.ofWeights_quote_of_not_mem hw hφ

/-- **The two attempts' candidate states quote the same function** (for a world measure; attempt
B's `clamp01` is the identity there).
Source: [[bli-coherent-mm-mandate]] §Deliverables (reconciler cross-check)
Kind: L
Fidelity: exact -/
theorem ofWeights_quote_eq_attemptB (S : Finset Sentence) {B : ℕ} {w : FiniteWorld B → ℚ}
    {D : Finset Sentence} (hw : IsWorldMeasure w D) (φ : Sentence) :
    (ofWeights S w hw).quote φ = (AttemptB.ofWeights S w).quote φ := by
  by_cases hφ : φ ∈ S
  · rw [ofWeights_quote_of_mem hw hφ, AttemptB.ofWeights_quote_of_mem hw.toB hφ]
    rfl
  · rw [ofWeights_quote_of_not_mem hw hφ, AttemptB.ofWeights_quote_of_not_mem _ hφ]

/-- **D2/D3 (of record). The candidate table** of a weight vector on `S` against a past: day `n`
reads `π w` on `S` and `0` off `S`, days `≠ n` read the past — a function of `w` alone.
Source: [[bli-coherent-mm-mandate]] D2, D3
Kind: D
Fidelity: exact -/
abbrev candidateTable (past : List RationalBeliefState) (n : ℕ) (S : Finset Sentence) {B : ℕ}
    (w : FiniteWorld B → ℚ) : ℕ → Sentence → ℚ :=
  AttemptA.candidateTable past n S w

/-- The candidate table is FAF's `candidateRationalHistory` of the candidate state.
Source: [[bli-coherent-mm-mandate]] D3
Kind: L
Fidelity: exact -/
theorem candidateRationalHistory_ofWeights (past : List RationalBeliefState) (n : ℕ)
    (S : Finset Sentence) {B : ℕ} (w : FiniteWorld B → ℚ) {D : Finset Sentence}
    (hw : IsWorldMeasure w D) :
    candidateRationalHistory past n (ofWeights S w hw) = candidateTable past n S w :=
  AttemptA.candidateRationalHistory_ofWeights past n S w hw

/-- The candidate table on day `n`, on `S`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem candidateTable_self_of_mem (past : List RationalBeliefState) (n : ℕ)
    {S : Finset Sentence} {B : ℕ} (w : FiniteWorld B → ℚ) {φ : Sentence} (hφ : φ ∈ S) :
    candidateTable past n S w n φ = marginal w φ :=
  AttemptA.candidateTable_self_of_mem past n w hφ

/-- The candidate table on a day `≠ n` is the past.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem candidateTable_of_ne (past : List RationalBeliefState) {n k : ℕ} (hk : k ≠ n)
    (S : Finset Sentence) {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) :
    candidateTable past n S w k φ = rationalHistory past k φ :=
  AttemptA.candidateTable_of_ne past hk S w φ

/-- **The two attempts' candidate histories agree**: for a world measure, the record's candidate
table is FAF's `candidateRationalHistory` of attempt B's candidate state. This is the bridge
along which attempt B's acceptance theorems transport to the record's D3 (`Accept.lean`).
Source: [[bli-coherent-mm-mandate]] §Deliverables (reconciler cross-check)
Kind: L
Fidelity: exact -/
theorem candidateTable_eq_attemptB (past : List RationalBeliefState) (n : ℕ)
    (S : Finset Sentence) {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) :
    candidateTable past n S w = candidateRationalHistory past n (AttemptB.ofWeights S w) := by
  rw [← candidateRationalHistory_ofWeights past n S w hw]
  unfold candidateRationalHistory
  congr 1
  funext φ
  exact ofWeights_quote_eq_attemptB S hw φ

end Cleanroom.Bli.BliCoherentMm
