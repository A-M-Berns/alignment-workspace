import Cleanroom.Bli.BliFinite.DeFinetti
import Cleanroom.Bli.BliFinite.Round

/-!
# `bli-finite` · CoherenceExamples: the three coherence findings (T2 N−, T3 N+, T3 N−)

* `twoAxiom_signed_counterexample` (**N−**, bli-paper-030's flag): the paper's two axioms
  *without* non-negativity admit a signed valuation (`V p = 2`, `V (∼p) = −1`), so the clause
  the definition of record adds is needed.
* `twoAxiom_on_given_sentences_only_not_coherent` (**N+**, the program's F4 witness): the three
  clauses quantified over the *given* sentences only are vacuous — `A = {p, q, p ⋏ q}`,
  `V = (1, 1, 0)` passes them (no tautology, no disjoint pair in `A`) and is not a world
  marginal for any atom bound. The definition of record quantifies over `GenBy A`.
* `roundTo_not_coherent` (**N−**, bli-paper-033 / bli-slides-008): coordinatewise rounding does
  not preserve coherence — the coherent table `(3/10, 3/10, 6/10)` on
  `{p ⋏ ∼q, ∼p ⋏ q, (p ⋏ ∼q) ⋎ (∼p ⋏ q)}` rounds (`d = 2`) to `(1/2, 1/2, 1/2)`, which no
  world distribution produces (disjoint additivity fails). This refutes the *coordinatewise*
  reading of "`D_n` … maintaining propositional consistency"; the paper does not say which
  rounding it means (ATTRIBUTION-UNVETTED that coordinatewise was intended); the surviving
  reading is `WorldRound.lean`.
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction LO.Propositional Finset BoolPCWorld Classical

/-- The atom `p`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev pA : Sentence := Formula.atom 0
/-- The atom `q`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev qA : Sentence := Formula.atom 1

/-- The world in which every atom is false.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def falseWorld : PCWorld := fun _ => False

/-- The world in which every atom is true.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def trueWorld : PCWorld := fun _ => True

/-- The all-false world is consistent with the empty stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma falseWorld_consistent (D : Finset Sentence) (h : D = ∅) : falseWorld.ConsistentWith D := by
  subst h; intro φ hφ; simp at hφ

/-- The all-true world is consistent with the empty stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma trueWorld_consistent (D : Finset Sentence) (h : D = ∅) : trueWorld.ConsistentWith D := by
  subst h; intro φ hφ; simp at hφ

/-- The rational truth indicator of a world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def indQ (v : PCWorld) (φ : Sentence) : ℚ := if v.Holds φ then 1 else 0

/-- The indicator of a disjoint disjunction is the sum of the indicators.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma indQ_or_of_disjoint (v : PCWorld) {φ ψ : Sentence} (h : ¬ v.Holds (φ ⋏ ψ)) :
    indQ v (φ ⋎ ψ) = indQ v φ + indQ v ψ := by
  rw [PCWorld.holds_and] at h
  unfold indQ
  rw [PCWorld.holds_or]
  by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ <;> simp_all

/-! ## N−: the two axioms without non-negativity admit signed valuations -/

/-- **Signed counterexample (bli-paper-030's flag).** `V := 2·[trueWorld ⊨ ·] − [falseWorld ⊨ ·]`
satisfies the paper's two axioms verbatim (tautologies price 1, disjoint disjunctions add) on
`GenBy {p}` — indeed on every sentence — with `V p = 2` and `V (∼p) = −1`; so the paper's pair
does not imply the `[0,1]` range, and `TwoAxiomCoherent`'s non-negativity clause is not
redundant.
Source: bli-paper-030 (flag: the definition should say prices lie in `[0,1]`)
Kind: N-
Fidelity: exact (degenerate by nature: a two-world signed mixture)
Hyps: (a) none -/
theorem twoAxiom_signed_counterexample :
    ∃ V : Sentence → ℚ, TwoAxiomNoNonneg V {pA} ∅ ∧ V pA = 2 ∧ V (∼pA) = -1 ∧
      ¬ TwoAxiomCoherent V {pA} ∅ := by
  refine ⟨fun φ => 2 * indQ trueWorld φ - indQ falseWorld φ, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro φ _ ht
    have h1 := ht trueWorld (trueWorld_consistent _ rfl)
    have h0 := ht falseWorld (falseWorld_consistent _ rfl)
    simp only [indQ, if_pos h1, if_pos h0]
    norm_num
  · intro φ ψ _ _ hc
    have h1 := hc trueWorld (trueWorld_consistent _ rfl)
    have h0 := hc falseWorld (falseWorld_consistent _ rfl)
    simp only [indQ_or_of_disjoint _ h1, indQ_or_of_disjoint _ h0]
    ring
  · simp [indQ, trueWorld, falseWorld]
  · simp [indQ, trueWorld, falseWorld]
  · intro hV
    have := hV.1 (∼pA) (GenBy.base (by simp)).neg
    norm_num [indQ, trueWorld, falseWorld] at this

/-! ## N+: the axioms on the given sentences only are vacuous -/

/-- **The "on the given sentences only" reading is vacuous (the program's F4 witness).**
`A = {p, q, p ⋏ q}` with `V = (1, 1, 0)` satisfies all three clauses when they are quantified
over `A` alone (no sentence of `A` is a tautology, no two are disjoint), lies in `[0,1]`, and
is not the marginal of any world distribution for any atom bound `B`. The definition of record
(`TwoAxiomCoherent`) quantifies over `GenBy A`, where `V` fails (`p ⋎ q` and `p ⋏ q`).
Source: bli-soto-a-001 ("the two readings coincide" — only over the generated algebra);
[[bli-program]] §4 row ★F4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem twoAxiom_on_given_sentences_only_not_coherent :
    ∃ (V : Sentence → ℚ) (A : Finset Sentence),
      TwoAxiomOnGiven V A ∅ ∧ (∀ φ ∈ A, 0 ≤ V φ ∧ V φ ≤ 1) ∧
      ∀ B : ℕ, ¬ ∃ w : FiniteWorld B → ℚ, (∀ u, 0 ≤ w u) ∧ ∑ u, w u = 1 ∧
        ∀ φ ∈ A, V φ = ∑ u, w u * u.payoutRat φ := by
  have hpne : pA ≠ pA ⋏ qA := fun h => by cases h
  have hqne : qA ≠ pA ⋏ qA := fun h => by cases h
  have hfalse : ∀ φ ∈ ({pA, qA, pA ⋏ qA} : Finset Sentence), ¬ falseWorld.Holds φ := by
    intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl | rfl
    · simp [falseWorld]
    · simp [falseWorld]
    · rw [PCWorld.holds_and]; simp [falseWorld]
  have htrue : ∀ φ ∈ ({pA, qA, pA ⋏ qA} : Finset Sentence), trueWorld.Holds φ := by
    intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl | rfl
    · simp [trueWorld]
    · simp [trueWorld]
    · rw [PCWorld.holds_and]; simp [trueWorld]
  refine ⟨fun φ => if φ = pA ⋏ qA then 0 else 1, {pA, qA, pA ⋏ qA}, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro φ _; dsimp only; split_ifs <;> norm_num
  · intro φ hφ ht
    exact absurd (ht falseWorld (falseWorld_consistent _ rfl)) (hfalse φ hφ)
  · intro φ hφ ψ hψ hc
    exfalso
    apply hc trueWorld (trueWorld_consistent _ rfl)
    rw [PCWorld.holds_and]
    exact ⟨htrue φ hφ, htrue ψ hψ⟩
  · intro φ _; dsimp only; split_ifs <;> norm_num
  · rintro B ⟨w, hw0, hw1, hV⟩
    have hp := hV pA (by simp)
    have hq := hV qA (by simp)
    have hpq := hV (pA ⋏ qA) (by simp)
    dsimp only at hp hq hpq
    rw [if_neg hpne] at hp
    rw [if_neg hqne] at hq
    rw [if_pos rfl] at hpq
    have key : ∀ χ : Sentence, (1 : ℚ) = ∑ u, w u * u.payoutRat χ →
        ∀ u, w u * u.payoutRat χ = w u := by
      intro χ h u
      have hle : ∀ u ∈ (Finset.univ : Finset (FiniteWorld B)), w u * u.payoutRat χ ≤ w u :=
        fun u _ => mul_le_of_le_one_right (hw0 u) (payoutRat_le_one u χ)
      exact (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [← h, hw1]) u (Finset.mem_univ u)
    have hp' := key pA hp
    have hq' := key qA hq
    have hall : ∀ u : FiniteWorld B, w u * u.payoutRat (pA ⋏ qA) = w u := by
      intro u
      by_cases h : (worldOf u).Holds (pA ⋏ qA)
      · rw [payoutRat_of_holds h, mul_one]
      · rw [PCWorld.holds_and, not_and_or] at h
        have hwu : w u = 0 := by
          rcases h with h | h
          · rw [← hp' u, payoutRat_of_not_holds h, mul_zero]
          · rw [← hq' u, payoutRat_of_not_holds h, mul_zero]
        rw [hwu, zero_mul]
    rw [Finset.sum_congr rfl (fun u _ => hall u), hw1] at hpq
    exact zero_ne_one hpq

/-! ## N−: coordinatewise rounding does not preserve coherence (bli-paper-033) -/

/-- The three-sentence index of the rounding counterexample (constant in the day).
Source: bli-paper-033; mandate T2
Kind: D
Fidelity: n/a -/
def roundIndex : SmallIndex :=
  ⟨fun _ => {pA ⋏ ∼qA, ∼pA ⋏ qA, (pA ⋏ ∼qA) ⋎ (∼pA ⋏ qA)}, fun _ => Finset.Subset.refl _⟩

/-- The coherent table `(3/10, 3/10, 6/10)`.
Source: mandate T2
Kind: D
Fidelity: n/a -/
def roundTable : Table roundIndex 0 :=
  fun φ => if φ.1 = pA ⋏ ∼qA then 3 / 10 else if φ.1 = ∼pA ⋏ qA then 3 / 10 else 6 / 10

/-- The world `p ∧ ¬q` on two atoms.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wPnQ : FiniteWorld 2 := ![true, false]
/-- The world `¬p ∧ q` on two atoms.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wnPQ : FiniteWorld 2 := ![false, true]
/-- The world `p ∧ q` on two atoms.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wPQ : FiniteWorld 2 := ![true, true]

/-- Payout of an explicit two-atom world on an explicit sentence, by evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wPnQ_1 : wPnQ.payoutRat (pA ⋏ ∼qA) = 1 := by decide
/-- Payout of an explicit two-atom world on an explicit sentence, by evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wPnQ_2 : wPnQ.payoutRat (∼pA ⋏ qA) = 0 := by decide
/-- Payout of an explicit two-atom world on an explicit sentence, by evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wPnQ_3 : wPnQ.payoutRat ((pA ⋏ ∼qA) ⋎ (∼pA ⋏ qA)) = 1 := by decide
/-- Payout of an explicit two-atom world on an explicit sentence, by evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wnPQ_1 : wnPQ.payoutRat (pA ⋏ ∼qA) = 0 := by decide
/-- Payout of an explicit two-atom world on an explicit sentence, by evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wnPQ_2 : wnPQ.payoutRat (∼pA ⋏ qA) = 1 := by decide
/-- Payout of an explicit two-atom world on an explicit sentence, by evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wnPQ_3 : wnPQ.payoutRat ((pA ⋏ ∼qA) ⋎ (∼pA ⋏ qA)) = 1 := by decide
/-- Payout of an explicit two-atom world on an explicit sentence, by evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wPQ_1 : wPQ.payoutRat (pA ⋏ ∼qA) = 0 := by decide
/-- Payout of an explicit two-atom world on an explicit sentence, by evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wPQ_2 : wPQ.payoutRat (∼pA ⋏ qA) = 0 := by decide
/-- Payout of an explicit two-atom world on an explicit sentence, by evaluation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wPQ_3 : wPQ.payoutRat ((pA ⋏ ∼qA) ⋎ (∼pA ⋏ qA)) = 0 := by decide

/-- The world weights `3/10, 3/10, 4/10` on `p∧¬q`, `¬p∧q`, `p∧q`.
Source: mandate T2
Kind: D
Fidelity: n/a -/
def roundWeights (u : FiniteWorld 2) : ℚ :=
  (if u = wPnQ then 3 / 10 else 0) + (if u = wnPQ then 3 / 10 else 0) + (if u = wPQ then 4 / 10 else 0)

/-- Distinctness of the example worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wPnQ_ne_wnPQ : wPnQ ≠ wnPQ := by decide
/-- Distinctness of the example worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wPnQ_ne_wPQ : wPnQ ≠ wPQ := by decide
/-- Distinctness of the example worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wnPQ_ne_wPQ : wnPQ ≠ wPQ := by decide

/-- The table `(3/10, 3/10, 6/10)` is coherent (world weights `3/10, 3/10, 4/10`).
Source: mandate T2
Kind: L
Fidelity: n/a -/
lemma roundTable_coherent : CoherentOn roundTable ∅ 2 := by
  refine ⟨roundWeights, ?_, ?_, ?_, ?_⟩
  · intro u; unfold roundWeights; split_ifs <;> norm_num
  · unfold roundWeights
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    norm_num
  · intro u _ φ hφ; simp at hφ
  · rintro ⟨φ, hφ⟩
    simp only [roundIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
    have e : ∀ χ : Sentence, ∑ u, roundWeights u * u.payoutRat χ =
        3 / 10 * wPnQ.payoutRat χ + 3 / 10 * wnPQ.payoutRat χ + 4 / 10 * wPQ.payoutRat χ := by
      intro χ
      unfold roundWeights
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [e]
    rcases hφ with rfl | rfl | rfl
    · rw [payout_wPnQ_1, payout_wnPQ_1, payout_wPQ_1]
      simp only [roundTable]; norm_num
    · rw [payout_wPnQ_2, payout_wnPQ_2, payout_wPQ_2]
      simp only [roundTable, if_neg (show (∼pA ⋏ qA : Sentence) ≠ pA ⋏ ∼qA from fun h => by cases h)]
      norm_num
    · rw [payout_wPnQ_3, payout_wnPQ_3, payout_wPQ_3]
      simp only [roundTable,
        if_neg (show ((pA ⋏ ∼qA) ⋎ (∼pA ⋏ qA) : Sentence) ≠ pA ⋏ ∼qA from fun h => by cases h),
        if_neg (show ((pA ⋏ ∼qA) ⋎ (∼pA ⋏ qA) : Sentence) ≠ ∼pA ⋏ qA from fun h => by cases h)]
      norm_num

/-- Rounding the table to `d = 2` gives `(1/2, 1/2, 1/2)`.
Source: mandate T2
Kind: L
Fidelity: n/a -/
lemma roundTo_roundTable (φ : ↥(roundIndex.S 0)) : roundTo 2 roundTable φ = 1 / 2 := by
  unfold roundTo roundVal
  have h3 : ⌈clamp01 (3 / 10 : ℚ) * (2 : ℕ) - 1 / 2⌉ = 1 := by
    rw [clamp01_eq_self (by norm_num), Int.ceil_eq_iff]; push_cast; constructor <;> norm_num
  have h6 : ⌈clamp01 (6 / 10 : ℚ) * (2 : ℕ) - 1 / 2⌉ = 1 := by
    rw [clamp01_eq_self (by norm_num), Int.ceil_eq_iff]; push_cast; constructor <;> norm_num
  unfold roundTable
  split_ifs
  · rw [h3]; norm_num
  · rw [h3]; norm_num
  · rw [h6]; norm_num

/-- The rounded table is not coherent: any world distribution gives the disjunction of the two
exclusive conjunctions the sum of their prices, and `1/2 ≠ 1/2 + 1/2`.
Source: bli-paper-033 (the flag), bli-slides-008
Kind: L
Fidelity: n/a -/
lemma roundTo_roundTable_not_coherent : ¬ CoherentOn (roundTo 2 roundTable) ∅ 2 := by
  rintro ⟨w, -, -, -, ht⟩
  have h1 := ht ⟨pA ⋏ ∼qA, by simp [roundIndex]⟩
  have h2 := ht ⟨∼pA ⋏ qA, by simp [roundIndex]⟩
  have h3 := ht ⟨(pA ⋏ ∼qA) ⋎ (∼pA ⋏ qA), by simp [roundIndex]⟩
  rw [roundTo_roundTable] at h1 h2 h3
  have hdisj : ∀ u : FiniteWorld 2, ¬ (worldOf u).Holds ((pA ⋏ ∼qA) ⋏ (∼pA ⋏ qA)) := by
    intro u h
    rw [PCWorld.holds_and, PCWorld.holds_and, PCWorld.holds_and, PCWorld.holds_neg,
      PCWorld.holds_neg] at h
    exact h.2.1 h.1.1
  have : ∑ u, w u * u.payoutRat ((pA ⋏ ∼qA) ⋎ (∼pA ⋏ qA)) =
      ∑ u, w u * u.payoutRat (pA ⋏ ∼qA) + ∑ u, w u * u.payoutRat (∼pA ⋏ qA) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [payoutRat_or_of_disjoint (hdisj u), mul_add]
  rw [← h3, ← h1, ← h2] at this
  norm_num at this

/-- **Coordinatewise rounding does not preserve coherence (refutation of the coordinatewise
reading of bli-paper-033).** The table `(3/10, 3/10, 6/10)` on
`{p ⋏ ∼q, ∼p ⋏ q, (p ⋏ ∼q) ⋎ (∼p ⋏ q)}` is coherent; its coordinatewise rounding to `d = 2` is
`(1/2, 1/2, 1/2)`, which is not. The paper's "`D_n` … maintaining propositional consistency" is
therefore false if `D_n` rounds coordinates (ATTRIBUTION-UNVETTED that this was intended); the
surviving reading rounds the world distribution (`worldRound`, `WorldRound.lean`).
Source: bli-paper-033 (`main.tex:427`); bli-slides-008
Kind: N-
Fidelity: refutes the coordinatewise reading; the paper does not say which rounding it means
(ATTRIBUTION-UNVETTED)
Hyps: (a) none -/
theorem roundTo_not_coherent :
    CoherentOn roundTable ∅ 2 ∧ ¬ CoherentOn (roundTo 2 roundTable) ∅ 2 :=
  ⟨roundTable_coherent, roundTo_roundTable_not_coherent⟩

end Cleanroom.Bli.BliFinite
