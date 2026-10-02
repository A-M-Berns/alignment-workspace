import Cleanroom.Bli.BliOverlay
import Cleanroom.Bli.BliFinite

/-!
# `bli-coherent-mm` (attempt A) · Worlds: the `D`-consistent worlds, world measures, marginals

**D1 and D2 of the mandate**, over FAF's `FiniteWorld B` read as a `PCWorld` through
`bli-finite`'s `worldOf`. Nothing here is a headline.

* **D1** `WD D B` — the finite worlds over `B` atoms consistent with the stage `D` (a `Finset`
  by `Finset.univ.filter`; consistency is decidable through `eval`).
* **D2** `IsWorldMeasure w D` — a rational probability on `FiniteWorld B` supported on `WD D B`
  (exactly the witness shape of `bli-finite`'s `IsWorldMarginal`); `marginal w φ` — its price
  table `∑ u, w u * u.payoutRat φ` (the mandate's `π w φ`); `ofWeights S w hw` — the
  `RationalBeliefState` with entries `(φ, marginal w φ)` for `φ ∈ S` (quote `0` off `S`), built
  with `bli-overlay`'s `restrictState` so the range is a *proof*, not a clamp.
* The restriction bridge between `PCWorld`s consistent with `D` and `WD D B` (`restrict_mem_WD`,
  `value_payout_eq_restrict`), used by every `PCWorld`-form statement in the package.
* The consequences of being a marginal over `D`-consistent worlds: unit range, `φ`/`∼φ` add to
  one, decided sentences priced at their truth (T2(c), `marginal_of_decided_true/false`).

Sources: [[bli-coherent-mm-mandate]] D1, D2, T2(c); [[bli-program]] §2.7, §3.8.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## D1: the `D`-consistent finite worlds -/

/-- Consistency of a finite world with a finite stage is decided by `eval` on the stage's
sentences (so `WD` is a `Finset.filter` without classical choice).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance instDecidableWorldOfConsistentWith {B : ℕ} (u : FiniteWorld B) (D : Finset Sentence) :
    Decidable ((worldOf u).ConsistentWith D) :=
  decidable_of_iff (∀ φ ∈ D, eval u.toBoolPCWorld φ = true)
    (forall_congr' fun _ => imp_congr_right fun _ => eval_eq_true_iff_holds _ _)

/-- **D1. The `D`-consistent worlds over `B` atoms**: `{u : FiniteWorld B | (worldOf u).ConsistentWith D}`.
Meaningful under `hB : ∀ φ ∈ D, atomBound φ ≤ B` (atoms `≥ B` read `false` in `worldOf u`).
Source: [[bli-coherent-mm-mandate]] D1
Kind: D
Fidelity: exact -/
def WD (D : Finset Sentence) (B : ℕ) : Finset (FiniteWorld B) :=
  Finset.univ.filter fun u => (worldOf u).ConsistentWith D

/-- Membership in `WD`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_WD {D : Finset Sentence} {B : ℕ} {u : FiniteWorld B} :
    u ∈ WD D B ↔ (worldOf u).ConsistentWith D := by
  simp [WD]

/-- With the empty stage every finite world is consistent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_WD_empty {B : ℕ} (u : FiniteWorld B) : u ∈ WD ∅ B := by
  rw [mem_WD]
  intro φ hφ
  simp at hφ

/-! ## The restriction bridge -/

/-- The restriction of a `PCWorld` consistent with `D` to `B` atoms is in `WD D B`, provided `D`
is within the atom bound.
Source: [[bli-coherent-mm-mandate]] T1 (restriction); bli-finite `holds_worldOf_restrict`
Kind: L
Fidelity: n/a -/
lemma restrict_mem_WD {D : Finset Sentence} {B : ℕ} (hB : ∀ φ ∈ D, atomBound φ ≤ B)
    {v : PCWorld} (hv : v.ConsistentWith D) : FiniteWorld.restrict (ofPCWorld v) B ∈ WD D B := by
  rw [mem_WD]
  intro φ hφ
  exact (holds_worldOf_restrict v (hB φ hφ)).mpr (hv φ hφ)

/-- If no finite world over `B` atoms is consistent with `D` (and `D` is within the bound), no
`PCWorld` is: the fallback branch of the recursion is vacuous for FAF's `Exploits`.
Source: [[bli-coherent-mm-mandate]] T6 (the fallback)
Kind: L
Fidelity: n/a -/
lemma exists_consistent_of_pcWorld {D : Finset Sentence} {B : ℕ} (hB : ∀ φ ∈ D, atomBound φ ≤ B)
    (h : ∃ v : PCWorld, v.ConsistentWith D) : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D := by
  obtain ⟨v, hv⟩ := h
  exact ⟨_, mem_WD.mp (restrict_mem_WD hB hv)⟩

/-- The real payout table of a finite world: the cast of `payoutRat`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def payoutReal {B : ℕ} (u : FiniteWorld B) : Sentence → ℝ :=
  fun φ => (u.payoutRat φ : ℝ)

/-- `payoutReal u = (worldOf u).payout`.
Source: FAF `FiniteWorld.payoutRat_eq_toPCWorld`, `PCWorld.payout_eq_ratCast`
Kind: L
Fidelity: n/a -/
lemma payoutReal_eq_payout {B : ℕ} (u : FiniteWorld B) : payoutReal u = (worldOf u).payout := by
  funext φ
  unfold payoutReal
  rw [FiniteWorld.payoutRat_eq_toPCWorld, ← PCWorld.payout_eq_ratCast]

/-- On a sentence within the atom bound, the restricted world's real payout is the world's payout.
Source: FAF `FiniteWorld.payoutRat_restrict_ofPCWorld`
Kind: L
Fidelity: n/a -/
lemma payoutReal_restrict (v : PCWorld) {B : ℕ} {φ : Sentence} (hφ : atomBound φ ≤ B) :
    payoutReal (FiniteWorld.restrict (ofPCWorld v) B) φ = v.payout φ := by
  unfold payoutReal
  rw [FiniteWorld.payoutRat_restrict_ofPCWorld v B φ hφ, PCWorld.payout_eq_ratCast]

/-- **A strategy's value in a `PCWorld` is its value in the world's restriction to `B` atoms**,
when every traded sentence is within the bound (`value_eq_of_world_eqOn_support`).
Source: [[bli-coherent-mm-mandate]] T1 (restriction step)
Kind: L
Fidelity: n/a -/
lemma value_payout_eq_restrict {n : ℕ} (T : Strategy n) (P : History) (v : PCWorld) {B : ℕ}
    (hB : ∀ φ ∈ T.support, atomBound φ ≤ B) :
    T.value P v.payout = T.value P (payoutReal (FiniteWorld.restrict (ofPCWorld v) B)) :=
  T.value_eq_of_world_eqOn_support _ _ _ fun φ hφ => (payoutReal_restrict v (hB φ hφ)).symm

/-! ## D2: world measures and their marginals -/

/-- **D2. A world measure**: a rational probability on `FiniteWorld B` supported on the
`D`-consistent worlds — exactly the witness of `bli-finite`'s `IsWorldMarginal`.
Source: [[bli-coherent-mm-mandate]] D2
Kind: D
Fidelity: exact -/
def IsWorldMeasure {B : ℕ} (w : FiniteWorld B → ℚ) (D : Finset Sentence) : Prop :=
  (∀ u, 0 ≤ w u) ∧ ∑ u, w u = 1 ∧ ∀ u, w u ≠ 0 → (worldOf u).ConsistentWith D

/-- `IsWorldMeasure` is decidable (finite conjunctions, exact rational arithmetic, decidable
consistency): the acceptance test of D3 is a decidable predicate.
Source: [[bli-coherent-mm-mandate]] D3 ("decidable for the search")
Kind: L
Fidelity: n/a -/
instance instDecidableIsWorldMeasure {B : ℕ} (w : FiniteWorld B → ℚ) (D : Finset Sentence) :
    Decidable (IsWorldMeasure w D) := by
  unfold IsWorldMeasure
  infer_instance

/-- **D2. The marginal (price table) of a world weight vector**: `π w φ := ∑ u, w u * u.payoutRat φ`.
Source: [[bli-coherent-mm-mandate]] D2; bli-finite `marginalOf`
Kind: D
Fidelity: exact -/
def marginal {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) : ℚ :=
  ∑ u, w u * u.payoutRat φ

open Classical in
/-- The marginal is the mass of the worlds holding the sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma marginal_eq_sum_filter {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) :
    marginal w φ = ∑ u ∈ Finset.univ.filter (fun u : FiniteWorld B => (worldOf u).Holds φ), w u := by
  unfold marginal
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  rw [payoutRat_eq_ite]
  split_ifs <;> simp

/-- Marginals of a world measure are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma marginal_nonneg {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (φ : Sentence) : 0 ≤ marginal w φ :=
  Finset.sum_nonneg fun u _ => mul_nonneg (hw.1 u) (payoutRat_nonneg u φ)

/-- Marginals of a world measure are at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma marginal_le_one {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (φ : Sentence) : marginal w φ ≤ 1 := by
  calc marginal w φ ≤ ∑ u, w u :=
        Finset.sum_le_sum fun u _ => mul_le_of_le_one_right (hw.1 u) (payoutRat_le_one u _)
    _ = 1 := hw.2.1

/-- `π w φ + π w (∼φ) = 1` for a world measure: the two-axiom coherence of a marginal, in the form
the contrast T4 needs.
Source: [[bli-coherent-mm-mandate]] T4(b); bli-finite `TwoAxiomCoherent.neg_add`
Kind: L
Fidelity: exact -/
lemma marginal_neg_add {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (φ : Sentence) : marginal w φ + marginal w (∼φ) = 1 := by
  unfold marginal
  rw [← Finset.sum_add_distrib, ← hw.2.1]
  apply Finset.sum_congr rfl
  intro u _
  rw [payoutRat_eq_ite, payoutRat_eq_ite, PCWorld.holds_neg]
  by_cases h : (worldOf u).Holds φ <;> simp [h]

/-- The marginal of a world measure is a world marginal on any `A` (the full function `π w`, not a
finite-support quote: see the attempt report, finding on T2(b)'s shape).
Source: [[bli-coherent-mm-mandate]] T2(b)
Kind: L
Fidelity: exact -/
lemma isWorldMarginal_marginal {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) (A : Finset Sentence) : IsWorldMarginal (marginal w) A D B :=
  ⟨w, hw.1, hw.2.1, hw.2.2, fun _ _ => rfl⟩

/-- **T2(c), the engine. A sentence true in every `D`-consistent world is priced `1`** by every
world measure over `D`: Soto's "respects `D̄`" (PDF 05 Def 3) is a *consequence* of being a
marginal over `D`-consistent worlds, not a domain restriction.
Source: [[bli-coherent-mm-mandate]] T2(c); Soto PDF 05 Def 3; [[bli-program]] §3.8
Kind: L
Fidelity: exact -/
lemma marginal_of_decided_true {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) : marginal w φ = 1 := by
  unfold marginal
  rw [← hw.2.1]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : w u = 0
  · rw [hu, zero_mul]
  · rw [payoutRat_of_holds (h _ (hw.2.2 u hu)), mul_one]

/-- **T2(c), dual. A sentence false in every `D`-consistent world is priced `0`.**
Source: [[bli-coherent-mm-mandate]] T2(c); Soto PDF 05 Def 3
Kind: L
Fidelity: exact -/
lemma marginal_of_decided_false {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) : marginal w φ = 0 := by
  unfold marginal
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : w u = 0
  · rw [hu, zero_mul]
  · rw [payoutRat_of_not_holds (h _ (hw.2.2 u hu)), mul_zero]

/-- Positivity of a marginal from one positive-weight world holding the sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma marginal_pos_of_holds {B : ℕ} {w : FiniteWorld B → ℚ} {D : Finset Sentence}
    (hw : IsWorldMeasure w D) {φ : Sentence} {u : FiniteWorld B} (hu : 0 < w u)
    (hφ : (worldOf u).Holds φ) : 0 < marginal w φ := by
  unfold marginal
  apply Finset.sum_pos' (fun u' _ => mul_nonneg (hw.1 u') (payoutRat_nonneg u' φ))
  exact ⟨u, Finset.mem_univ u, by rw [payoutRat_of_holds hφ, mul_one]; exact hu⟩

/-! ## D2: the candidate state -/

/-- **D2. The candidate belief state** of a world measure on the sentence set `S`: entries
`(φ, π w φ)` for `φ ∈ S` (keys nodup from `S.toList`), quote `0` off `S`. The `[0,1]` range is
proved from `hw` (`bli-overlay`'s `restrictState`), never clamped.
Source: [[bli-coherent-mm-mandate]] D2
Kind: D
Fidelity: exact -/
noncomputable def ofWeights (S : Finset Sentence) {B : ℕ} (w : FiniteWorld B → ℚ) {D : Finset Sentence}
    (hw : IsWorldMeasure w D) : RationalBeliefState :=
  BliOverlay.AttemptA.restrictState S (marginal w) fun φ => ⟨marginal_nonneg hw φ, marginal_le_one hw φ⟩

/-- On `S` the candidate quotes the marginal.
Source: [[bli-coherent-mm-mandate]] D2 (`coherentMarketMaker_quote_eq_pi` shape)
Kind: L
Fidelity: exact -/
lemma ofWeights_quote_of_mem {S : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    {D : Finset Sentence} (hw : IsWorldMeasure w D) {φ : Sentence} (hφ : φ ∈ S) :
    (ofWeights S w hw).quote φ = marginal w φ :=
  BliOverlay.AttemptA.restrictState_quote_of_mem hφ

/-- The candidate's support is `S`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ofWeights_support {S : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    {D : Finset Sentence} (hw : IsWorldMeasure w D) : (ofWeights S w hw).support = S := by
  ext φ
  simp [ofWeights, BliOverlay.AttemptA.restrictState, RationalBeliefState.support]

/-- Off `S` the candidate quotes `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ofWeights_quote_of_not_mem {S : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    {D : Finset Sentence} (hw : IsWorldMeasure w D) {φ : Sentence} (hφ : φ ∉ S) :
    (ofWeights S w hw).quote φ = 0 :=
  RationalBeliefState.quote_eq_zero_of_not_mem _ (by rw [ofWeights_support]; exact hφ)

/-- **The candidate table** of a weight vector on `S` against a past: day `n` reads `π w` on `S`
and `0` off `S`, days `≠ n` read the past. Stated for *any* `w` (no range proof needed), so that
the acceptance predicate D3 is a predicate on `w` alone; `candidateRationalHistory_ofWeights`
identifies it with FAF's `candidateRationalHistory past n (ofWeights S w hw)`.
Source: [[bli-coherent-mm-mandate]] D2, D3
Kind: D
Fidelity: exact -/
def candidateTable (past : List RationalBeliefState) (n : ℕ) (S : Finset Sentence) {B : ℕ}
    (w : FiniteWorld B → ℚ) : ℕ → Sentence → ℚ :=
  Function.update (rationalHistory past) n fun φ => if φ ∈ S then marginal w φ else 0

/-- The candidate table is FAF's candidate history of the candidate state.
Source: [[bli-coherent-mm-mandate]] D3
Kind: L
Fidelity: exact -/
lemma candidateRationalHistory_ofWeights (past : List RationalBeliefState) (n : ℕ)
    (S : Finset Sentence) {B : ℕ} (w : FiniteWorld B → ℚ) {D : Finset Sentence}
    (hw : IsWorldMeasure w D) :
    candidateRationalHistory past n (ofWeights S w hw) = candidateTable past n S w := by
  unfold candidateRationalHistory candidateTable
  congr 1
  funext φ
  by_cases hφ : φ ∈ S
  · rw [if_pos hφ, ofWeights_quote_of_mem hw hφ]
  · rw [if_neg hφ, ofWeights_quote_of_not_mem hw hφ]

/-- The candidate table on day `n`, on `S`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma candidateTable_self_of_mem (past : List RationalBeliefState) (n : ℕ) {S : Finset Sentence}
    {B : ℕ} (w : FiniteWorld B → ℚ) {φ : Sentence} (hφ : φ ∈ S) :
    candidateTable past n S w n φ = marginal w φ := by
  simp [candidateTable, hφ]

/-- The candidate table on a day `≠ n` is the past.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma candidateTable_of_ne (past : List RationalBeliefState) {n k : ℕ} (hk : k ≠ n)
    (S : Finset Sentence) {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) :
    candidateTable past n S w k φ = rationalHistory past k φ := by
  simp [candidateTable, Function.update_of_ne hk]

end Cleanroom.Bli.BliCoherentMm.AttemptA
