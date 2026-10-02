import Cleanroom.Bli.BliCoherentMm.Worlds
import Cleanroom.Bli.BliCoherentMm.AttemptA.Accept
import Cleanroom.Bli.BliCoherentMm.AttemptB.Interior

/-!
# `bli-coherent-mm` · Accept (reconciled): D3 coherent acceptance, T2(a) and T3(a) existence,
T2(d) the customer's entry point — and the cross-check of the two attempts' acceptance predicates

**D3 of record: attempt A's `CoherentAccepts`** — `w` is a world measure over `D` **and** the
exact rational value of `T` on the candidate table (`π w` on `S`, `0` off `S`, the past on
days `< n`) is `≤ ε` **in every `D`-consistent world over `B` atoms**; decidable. Attempt B's
predicate bundles the other side condition (`mentionedSet T ⊆ S`) and leaves the measure
condition outside. The mandate's D3 is the bound alone "together with `S ⊇ mentionedSet T`
(as a hypothesis or a field)" and filters by `IsWorldMeasure` in D4; both attempts bundle one
side condition. Attempt A's is of record because "coherent acceptance" then means what the
words say — the candidate is coherent (a world measure) and accepted — and `S ⊇ mentionedSet T`
is a property of `(T, S)`, not of the candidate, so it belongs with the existence theorems.

**The cross-check the mandate asks for** ("the two makers accept the same predicate (D3) even
where their chosen candidates differ"): `coherentAccepts_iff_attemptB` — for a world measure
and `S ⊇ mentionedSet T`, the two attempts' acceptance predicates are equivalent, cell for cell
(`WD_eq_attemptB`, `candidateTable_eq_attemptB`). Every attempt-B acceptance theorem transports
along it; the existence theorems are given by both routes (`exists_coherentAccepts` by attempt
A's density argument, `exists_coherentAccepts_viaB` by attempt B's rounding — the latter needs
the atom bound `hB`, the former does not).

Sources: [[bli-coherent-mm-mandate]] D3, T2(a), T2(d), T3; [[bli-program]] §3.8.
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## D3: coherent acceptance -/

/-- **D3 (of record). Coherent acceptance.** `w` is a world measure over `D` and the exact
rational value of `T` on `candidateTable past n S w` is at most `ε` **in every `D`-consistent
world over `B` atoms** — never over FAF's all-Boolean support tables (`Contrast.lean`). Use with
`S ⊇ mentionedSet T`. Decidable (a finite scan of `WD D B` by exact rational arithmetic).
Source: [[bli-coherent-mm-mandate]] D3; Soto PDF 05 Thm 2 ("`B(W) ≤ 0` for all `W`")
Kind: D
Fidelity: exact -/
abbrev CoherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) (w : FiniteWorld B → ℚ) : Prop :=
  AttemptA.CoherentAccepts T past D B S ε w

/-- A coherently accepted weight vector is a world measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CoherentAccepts.isWorldMeasure {n : ℕ} {T : Strategy n} {past : List RationalBeliefState}
    {D : Finset Sentence} {B : ℕ} {S : Finset Sentence} {ε : ℚ} {w : FiniteWorld B → ℚ}
    (h : CoherentAccepts T past D B S ε w) : IsWorldMeasure w D :=
  h.1

/-- The bound clause of coherent acceptance.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CoherentAccepts.bound {n : ℕ} {T : Strategy n} {past : List RationalBeliefState}
    {D : Finset Sentence} {B : ℕ} {S : Finset Sentence} {ε : ℚ} {w : FiniteWorld B → ℚ}
    (h : CoherentAccepts T past D B S ε w) :
    ∀ u ∈ WD D B, T.marketValueRat (candidateTable past n S w) u.payoutRat ≤ ε :=
  h.2

/-- D3 in the mandate's FAF-facing shape: for a world measure, acceptance is the bound on FAF's
`candidateRationalHistory past n (ofWeights S w hw)` in every `D`-consistent world.
Source: [[bli-coherent-mm-mandate]] D3
Kind: L
Fidelity: exact -/
theorem coherentAccepts_iff {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure w D) :
    CoherentAccepts T past D B S ε w ↔
      ∀ u ∈ WD D B,
        T.marketValueRat (candidateRationalHistory past n (ofWeights S w hw)) u.payoutRat ≤ ε :=
  AttemptA.coherentAccepts_iff T past D B S ε hw

/-- **The two attempts accept the same predicate** (the mandate's reconciler cross-check): for a
world measure `w` and `S ⊇ mentionedSet T`, attempt A's `CoherentAccepts` (the record's) and
attempt B's are equivalent — the same worlds (`WD_eq_attemptB`), the same candidate history
(`candidateTable_eq_attemptB`), the same bound. Each attempt's maker is therefore accepted by
the other's test, although their chosen candidates differ (`Maker.lean`).
Source: [[bli-coherent-mm-mandate]] §Deliverables ("cross-checks that the two makers accept the same predicate (D3)")
Kind: L
Fidelity: exact -/
theorem coherentAccepts_iff_attemptB {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure w D) (hS : mentionedSet T ⊆ S) :
    CoherentAccepts T past D B S ε w ↔ AttemptB.CoherentAccepts T past D B S ε w := by
  constructor
  · intro h
    refine ⟨hS, fun u hu => ?_⟩
    have hu' : u ∈ WD D B := by rw [WD_eq_attemptB]; exact hu
    have hb := h.2 u hu'
    rw [← candidateTable_eq_attemptB past n S hw]
    exact hb
  · intro h
    refine ⟨hw, fun u hu => ?_⟩
    have hu' : u ∈ WD D B := hu
    rw [WD_eq_attemptB] at hu'
    have hb := h.2 u hu'
    rw [← candidateTable_eq_attemptB past n S hw] at hb
    exact hb

/-! ## T2(a), T3(a): accepted world measures exist -/

/-- **T2(a) (of record). Coherent acceptance is satisfiable**: for every `ε > 0` there is a
rational world measure over `D` whose candidate table **on `S ⊇ mentionedSet T`** has value
`≤ ε` **in every `D`-consistent world**. Attempt A's route: T1's fixed point, the accepted
region is open, a rational simplex point nearby. No atom bound is needed.
Source: [[bli-coherent-mm-mandate]] T2(a); [[bli-program]] §4 row M2
Kind: P
Fidelity: exact
Hyps: (a) `hS` (the candidate table is the table `T` reads), `hW` (nonempty simplex), `hε` -/
theorem exists_coherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε) :
    ∃ w : FiniteWorld B → ℚ, CoherentAccepts T past D B S ε w :=
  AttemptA.exists_coherentAccepts T past D B S hS hW hε

/-- **T2(a), attempt B's independent route** to the record statement: the real fixed point
rounded on a mesh found by search (`gridRound`, `exists_meshAccepted`), transported along the
acceptance cross-check. Attempt B's argument uses the atom bound `hB` (through its headline
T1), which attempt A's does not need.
Source: [[bli-coherent-mm-mandate]] T2(a), §Attempt angles (B); §Deliverables (cross-check)
Kind: P
Fidelity: exact
Hyps: (a) `hS`, `hB`, `hW`, `hε` -/
theorem exists_coherentAccepts_viaB {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (hS : mentionedSet T ⊆ S)
    (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε) :
    ∃ w : FiniteWorld B → ℚ, CoherentAccepts T past D B S ε w := by
  obtain ⟨w, hw, hacc⟩ := AttemptB.exists_coherentAccepts T past D B hB hW S hS hε
  exact ⟨w, (coherentAccepts_iff_attemptB T past D B S ε hw hS).mpr hacc⟩

/-- **T3(a) (of record). An accepted world measure with full support on `WD D B` exists** for
every `ε > 0`, at the same `ε`: mix `t · uniform` into the fixed point for a small `t > 0`
(inside the open accepted region), then a rational point nearby keeping every coordinate
positive. The content of the interior variant is full support on worlds (decided sentences stay
at `0`/`1`).
Source: [[bli-coherent-mm-mandate]] T3; [[bli-program]] §3.8 ("mix in `ε_n` times the uniform measure")
Kind: P
Fidelity: exact
Hyps: (a) `hS`, `hW`, `hε` -/
theorem exists_coherentAccepts_fullSupport {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ) (S : Finset Sentence)
    (hS : mentionedSet T ⊆ S) (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ}
    (hε : 0 < ε) :
    ∃ w : FiniteWorld B → ℚ, (∀ u ∈ WD D B, 0 < w u) ∧ CoherentAccepts T past D B S ε w :=
  AttemptA.exists_coherentAccepts_fullSupport T past D B S hS hW hε

/-- **T3(a), attempt B's independent route** (mix with the uniform measure at weight `1/(N+1)`,
round at mesh `(N+1)²`, search `N`), transported to the record statement.
Source: [[bli-coherent-mm-mandate]] T3, §Attempt angles (B); §Deliverables (cross-check)
Kind: P
Fidelity: exact
Hyps: (a) `hS`, `hB`, `hW`, `hε` -/
theorem exists_coherentAccepts_fullSupport_viaB {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ) (S : Finset Sentence)
    (hS : mentionedSet T ⊆ S) (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) {ε : ℚ} (hε : 0 < ε) :
    ∃ w : FiniteWorld B → ℚ, (∀ u ∈ WD D B, 0 < w u) ∧ CoherentAccepts T past D B S ε w := by
  obtain ⟨w, hw, hfull, hacc⟩ :=
    AttemptB.exists_coherentAccepts_fullSupport T past D B hB hW S hS hε
  refine ⟨w, fun u hu => hfull u ?_, (coherentAccepts_iff_attemptB T past D B S ε hw hS).mpr hacc⟩
  rw [WD_eq_attemptB] at hu
  exact hu

/-! ## T2(d): the customer's entry point -/

/-- **T2(d) (of record). The customer's entry point.** A coherently accepted weight vector
bounds the strategy's value by `ε` **in every `PCWorld` consistent with `D`**, on any real
history `P` agreeing with the candidate table on every cell `T` mentions (days `≤ n`); the atom
bound is needed only on `T.support ∪ D`. The coherent twin of `bli-overlay`'s
`dayValue_le_of_accepted_state`, whose all-Boolean hypothesis no coherent table can meet.
Source: [[bli-coherent-mm-mandate]] T2(d); [[bli-overlay-mandate]] T3(b)
Kind: L
Fidelity: exact
Hyps: (a) `hB`, `hacc`, `hagree` -/
theorem dayValue_le_of_coherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence)
    (hB : ∀ φ ∈ T.support ∪ D, atomBound φ ≤ B) {ε : ℚ} {w : FiniteWorld B → ℚ}
    (hacc : CoherentAccepts T past D B S ε w) (P : History)
    (hagree : ∀ φ, MentionedBy T φ → ∀ k ≤ n, P k φ = (candidateTable past n S w k φ : ℝ)) :
    ∀ v : PCWorld, v.ConsistentWith D → T.value P v.payout ≤ (ε : ℝ) :=
  AttemptA.dayValue_le_of_coherentAccepts T past D B S hB hacc P hagree

/-- **T2(d), split form**: agreement given separately on the mentioned past cells and on the
mentioned day-`n` cells (`P n φ = π w φ`; needs `S ⊇ mentionedSet T`).
Source: [[bli-coherent-mm-mandate]] T2(d)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem dayValue_le_of_coherentAccepts_split {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ) (S : Finset Sentence)
    (hS : mentionedSet T ⊆ S) (hB : ∀ φ ∈ T.support ∪ D, atomBound φ ≤ B) {ε : ℚ}
    {w : FiniteWorld B → ℚ} (hacc : CoherentAccepts T past D B S ε w) (P : History)
    (hpast : ∀ φ, MentionedBy T φ → ∀ k < n, P k φ = (rationalHistory past k φ : ℝ))
    (hnow : ∀ φ, MentionedBy T φ → P n φ = (marginal w φ : ℝ)) :
    ∀ v : PCWorld, v.ConsistentWith D → T.value P v.payout ≤ (ε : ℝ) :=
  AttemptA.dayValue_le_of_coherentAccepts_split T past D B S hS hB hacc P hpast hnow

end Cleanroom.Bli.BliCoherentMm
