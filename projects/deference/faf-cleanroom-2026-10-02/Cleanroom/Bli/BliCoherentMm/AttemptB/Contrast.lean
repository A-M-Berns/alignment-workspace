import Cleanroom.Bli.BliCoherentMm.AttemptB.Interior

/-!
# `bli-coherent-mm` (attempt B) · Contrast: witnesses and the FAF contrast (T4(a)–(c))

* **T4(a), `marketMaker_incoherent_on_pair`** (the contrast; a theorem about FAF): on the
  strategy `T_pair` buying one share of `φ` and one of `∼φ` at constant coefficients, every
  state FAF's `MarketMakerAccepts` accepts at `ε < 1` has `quote φ + quote (∼φ) ≥ 2 − ε > 1`
  — the acceptance clause at the Boolean table `b ≡ true` (both `φ` and `∼φ` "true"). Hence
  FAF's `MarketMaker T_pair past ε` is not a world marginal on `{φ, ∼φ}` relative to any stage
  (`marketMaker_not_worldMarginal_on_pair`): a marginal has `V φ + V (∼φ) = 1`. This is
  bli-slides-044's gap made exact ("FAF's construction is not exactly coherent at finite
  times") and Soto's PDF 05 fn. 1. Kind N− for FAF's maker / finding of record.
* **T4(b)**: on the same `T_pair`, *every* world measure makes the strategy's value exactly `0`
  in every finite world (`pair_coherent_value_eq_zero`), so the coherent maker is accepted at
  every `ε > 0` and prices `quote φ + quote (∼φ) = 1` (`coherentMarketMaker_pair_sum`); the
  interior maker at `D = ∅`, `φ = atom a`, `B = a + 1` prices `φ` strictly inside `(0, 1)`
  (`interior_pair_atom_nonDogmatic`) with `|W_∅| = 2^(a+1) ≥ 2`. N+ for T2/T3.
* **T4(c)**: the price-responsive strategy `T_resp` buying `1 − 2·price(φ)` shares of `φ` is
  coherently accepted at `ε` only at prices within `ε` of `1/2`
  (`coherentAccepts_responsive_near_half`): T1's fixed point is not a boundary artifact.

T4(d) (the hypothesis package over `paperDP 𝗜𝚺₁`) is in `Witness.lean`.

Sources: [[bli-coherent-mm-mandate]] T4; Soto PDF 05 fn. 1 (bli-soto-a-044); bli-slides-044.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptB

open LogicalInduction LogicalInduction.BoolPCWorld LO.Propositional Cleanroom.Bli.BliFound
  Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliFinite Finset

noncomputable section

/-! ## The pair strategy -/

/-- **`T_pair`**: buy one share of `φ` and one of `∼φ` at constant coefficients (`EF.const 1`,
rank `0`).
Source: [[bli-coherent-mm-mandate]] T4(a); Soto PDF 05 fn. 1
Kind: D
Fidelity: exact -/
def pairStrategy (n : ℕ) (φ : Sentence) : Strategy n where
  trades := [(EF.const 1, φ), (EF.const 1, ∼φ)]
  rank_le := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [EF.rank]

/-- `φ` is traded by `T_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairStrategy_mem_support_left (n : ℕ) (φ : Sentence) : φ ∈ (pairStrategy n φ).support :=
  Strategy.snd_mem_support _ (p := (EF.const 1, φ)) (by simp [pairStrategy])

/-- `∼φ` is traded by `T_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairStrategy_mem_support_right (n : ℕ) (φ : Sentence) :
    ∼φ ∈ (pairStrategy n φ).support :=
  Strategy.snd_mem_support _ (p := (EF.const 1, ∼φ)) (by simp [pairStrategy])

/-- `T_pair` mentions exactly `φ` and `∼φ` (constant coefficients query no prices).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mentionedBy_pairStrategy_iff (n : ℕ) (φ ψ : Sentence) :
    MentionedBy (pairStrategy n φ) ψ ↔ ψ = φ ∨ ψ = ∼φ := by
  constructor
  · rintro (⟨e, he⟩ | ⟨p, hp, k, hk⟩)
    · simp only [pairStrategy, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at he
      rcases he with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · simp only [pairStrategy, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl <;> simp [EF.priceQueries] at hk
  · rintro (rfl | rfl)
    · exact Or.inl ⟨EF.const 1, by simp [pairStrategy]⟩
    · exact Or.inl ⟨EF.const 1, by simp [pairStrategy]⟩

/-- The exact rational value of `T_pair`: `(w φ − Q n φ) + (w (∼φ) − Q n (∼φ))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairStrategy_marketValueRat (n : ℕ) (φ : Sentence) (Q : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) :
    (pairStrategy n φ).marketValueRat Q w = (w φ - Q n φ) + (w (∼φ) - Q n (∼φ)) := by
  simp [pairStrategy, Strategy.marketValueRat, EF.denoteRat, EF.denoteRatWith]

/-- A finite world's payouts of `φ` and `∼φ` sum to `1`.
Source: FAF `PCWorld.holds_neg`
Kind: L
Fidelity: n/a -/
lemma payoutRat_add_neg {B : ℕ} (u : FiniteWorld B) (φ : Sentence) :
    u.payoutRat φ + u.payoutRat (∼φ) = 1 := by
  rw [payoutRat_eq_ite, payoutRat_eq_ite, PCWorld.holds_neg]
  by_cases h : (worldOf u).Holds φ <;> simp [h]

/-- A world measure's prices of `φ` and `∼φ` sum to `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma piTable_add_neg {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (φ : Sentence) : piTable w φ + piTable w (∼φ) = 1 := by
  unfold piTable
  rw [← sum_add_distrib, ← hw.2.1]
  apply sum_congr rfl
  intro u _
  rw [← mul_add, payoutRat_add_neg, mul_one]

/-- A world marginal on an algebra containing `φ` and `∼φ` prices them to sum `1`
(bli-finite's `TwoAxiomCoherent.neg_add`, re-proved from the marginal directly).
Source: bli-paper-030 (the two axioms)
Kind: L
Fidelity: n/a -/
lemma worldMarginal_add_neg {V : Sentence → ℚ} {A D : Finset Sentence} {B : ℕ}
    (h : IsWorldMarginal V A D B) {φ : Sentence} (hφ : φ ∈ A) (hnφ : ∼φ ∈ A) :
    V φ + V (∼φ) = 1 := by
  obtain ⟨w, hw0, hw1, hwD, hV⟩ := h
  rw [hV φ (GenBy.base hφ), hV (∼φ) (GenBy.base hnφ), ← sum_add_distrib, ← hw1]
  apply sum_congr rfl
  intro u _
  rw [← mul_add, payoutRat_add_neg, mul_one]

/-! ## T4(a): FAF's maker is forced incoherent on `T_pair` -/

/-- **T4(a), the clause.** Every state FAF's `MarketMakerAccepts` accepts against `T_pair` at
`ε` has `quote φ + quote (∼φ) ≥ 2 − ε`: the acceptance test ranges over **all** Boolean tables on
the support, including the one in which both `φ` and `∼φ` pay `1`.
Source: [[bli-coherent-mm-mandate]] T4(a); Soto PDF 05 fn. 1; bli-slides-044
Kind: P
Fidelity: exact
Hyps: (a) `h` — FAF's acceptance predicate, applied -/
theorem marketMakerAccepts_pair_sum_ge {n : ℕ} {φ : Sentence} (past : List RationalBeliefState)
    (ε : ℚ) (Bs : RationalBeliefState) (h : MarketMakerAccepts (pairStrategy n φ) past ε Bs) :
    2 - ε ≤ Bs.quote φ + Bs.quote (∼φ) := by
  have h2 := h.2 (fun _ => true)
  rw [pairStrategy_marketValueRat] at h2
  simp only [supportBitWorldRat, candidateRationalHistory, Function.update_self,
    pairStrategy_mem_support_left, pairStrategy_mem_support_right, dite_true, if_true] at h2
  linarith

/-- **T4(a) (headline; finding of record). FAF's `MarketMaker` is provably incoherent on
`T_pair` at every finite time**: for `ε < 1`, its output prices `φ` and `∼φ` to a sum above `1`
(indeed `≥ 2 − ε`). bli-slides-044's gap ("FAF's construction is not exactly coherent at finite
times"), as a theorem.
Source: [[bli-coherent-mm-mandate]] T4(a); Soto PDF 05 fn. 1 (bli-soto-a-044); bli-slides-044
Kind: N-
Fidelity: exact (for FAF's own maker and acceptance predicate)
Hyps: (a) `hε1 : ε < 1` (FAF's `marketMakerError n < 1` always) -/
theorem marketMaker_incoherent_on_pair (n : ℕ) (φ : Sentence) (past : List RationalBeliefState)
    {ε : ℚ} (hε : 0 < ε) (hε1 : ε < 1) :
    1 < (MarketMaker (pairStrategy n φ) past ε hε).quote φ +
      (MarketMaker (pairStrategy n φ) past ε hε).quote (∼φ) := by
  have := marketMakerAccepts_pair_sum_ge past ε _ (MarketMaker_accepts (pairStrategy n φ) past ε hε)
  linarith

/-- **T4(a), marginal form.** FAF's `MarketMaker` on `T_pair` at `ε < 1` is not a world marginal
on `{φ, ∼φ}` relative to any stage `D` and any atom bound `B`.
Source: [[bli-coherent-mm-mandate]] T4(a)
Kind: N-
Fidelity: exact
Hyps: (a) -/
theorem marketMaker_not_worldMarginal_on_pair (n : ℕ) (φ : Sentence)
    (past : List RationalBeliefState) {ε : ℚ} (hε : 0 < ε) (hε1 : ε < 1) (D : Finset Sentence)
    (B : ℕ) :
    ¬ IsWorldMarginal (MarketMaker (pairStrategy n φ) past ε hε).quote {φ, ∼φ} D B := by
  intro h
  have h1 := worldMarginal_add_neg h (φ := φ) (by simp) (by simp)
  have h2 := marketMaker_incoherent_on_pair n φ past hε hε1
  linarith

/-- The same at FAF's day-`n` error `marketMakerError n = 2^{-(n+1)} < 1`: the maker that LIA
would run on a trader playing `T_pair` on day `n` is incoherent on that day.
Source: [[bli-coherent-mm-mandate]] T4(a)
Kind: N-
Fidelity: exact
Hyps: (a) -/
theorem marketMaker_incoherent_on_pair_error (n : ℕ) (φ : Sentence)
    (past : List RationalBeliefState) :
    1 < (MarketMaker (pairStrategy n φ) past (marketMakerError n) (marketMakerError_pos n)).quote φ
      + (MarketMaker (pairStrategy n φ) past (marketMakerError n)
          (marketMakerError_pos n)).quote (∼φ) := by
  apply marketMaker_incoherent_on_pair
  unfold marketMakerError
  rw [div_lt_one (by positivity)]
  exact one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)

/-! ## T4(b): the coherent makers on `T_pair` -/

/-- **T4(b). Every world measure makes `T_pair` worthless**: its exact value on the candidate
history, in every finite world, is `0` (`payout φ + payout (∼φ) = 1 = π φ + π (∼φ)`). So the
coherent acceptance test is passed at every `ε > 0`, with room to spare.
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem pair_coherent_value_eq_zero {n : ℕ} {φ : Sentence} {D : Finset Sentence} {B : ℕ}
    {S : Finset Sentence} {w : FiniteWorld B → ℚ} (hw : IsWorldMeasure D B w) (hφ : φ ∈ S)
    (hnφ : ∼φ ∈ S) (past : List RationalBeliefState) (u : FiniteWorld B) :
    (pairStrategy n φ).marketValueRat (candidateRationalHistory past n (ofWeights S w))
      (fun ψ => u.payoutRat ψ) = 0 := by
  rw [pairStrategy_marketValueRat]
  simp only [candidateRationalHistory, Function.update_self]
  rw [ofWeights_quote_of_mem hw hφ, ofWeights_quote_of_mem hw hnφ]
  have h1 := payoutRat_add_neg u φ
  have h2 := piTable_add_neg hw φ
  linarith

/-- **T4(b). Every world measure is coherently accepted on `T_pair` at every `ε ≥ 0`** (on any
`S ⊇ {φ, ∼φ}`).
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem pair_coherentAccepts {n : ℕ} {φ : Sentence} {D : Finset Sentence} {B : ℕ}
    {S : Finset Sentence} {w : FiniteWorld B → ℚ} (hw : IsWorldMeasure D B w)
    (hS : mentionedSet (pairStrategy n φ) ⊆ S) (past : List RationalBeliefState) {ε : ℚ}
    (hε : 0 ≤ ε) : CoherentAccepts (pairStrategy n φ) past D B S ε w := by
  have hφ : φ ∈ S := hS (mem_mentionedSet_iff.mpr ((mentionedBy_pairStrategy_iff n φ φ).mpr (Or.inl rfl)))
  have hnφ : ∼φ ∈ S := hS (mem_mentionedSet_iff.mpr ((mentionedBy_pairStrategy_iff n φ _).mpr (Or.inr rfl)))
  refine ⟨hS, fun u _ => ?_⟩
  rw [pair_coherent_value_eq_zero hw hφ hnφ past u]
  exact hε

/-- **T4(b). The coherent maker on `T_pair` prices `φ` and `∼φ` to sum exactly `1`** — the
contrast with `marketMaker_incoherent_on_pair`, on the same strategy.
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) `hB`, `hW` (any stage with a consistent world and an atom bound covering `φ`) -/
theorem coherentMarketMaker_pair_sum (n : ℕ) (φ : Sentence) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ)
    (hB : ∀ ψ ∈ mentionedSet (pairStrategy n φ) ∪ D, atomBound ψ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D) (ε : ℚ) (hε : 0 < ε) :
    (coherentMarketMaker (pairStrategy n φ) past D B hB hW (mentionedSet (pairStrategy n φ))
        (Finset.Subset.refl _) ε hε).quote φ +
      (coherentMarketMaker (pairStrategy n φ) past D B hB hW (mentionedSet (pairStrategy n φ))
        (Finset.Subset.refl _) ε hε).quote (∼φ) = 1 := by
  have hφ : φ ∈ mentionedSet (pairStrategy n φ) :=
    mem_mentionedSet_iff.mpr ((mentionedBy_pairStrategy_iff n φ φ).mpr (Or.inl rfl))
  have hnφ : ∼φ ∈ mentionedSet (pairStrategy n φ) :=
    mem_mentionedSet_iff.mpr ((mentionedBy_pairStrategy_iff n φ _).mpr (Or.inr rfl))
  rw [coherentMarketMaker_quote_eq_pi _ _ _ _ _ _ _ _ _ _ hφ,
    coherentMarketMaker_quote_eq_pi _ _ _ _ _ _ _ _ _ _ hnφ]
  exact piTable_add_neg (coherentWeights_isWorldMeasure _ _ _ _ _ _ _ _ _ _) φ

/-! ## T4(b), the interior maker on an atom at the empty stage: `|W_∅| = 2^(a+1) ≥ 2` -/

/-- Every finite world is consistent with the empty stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma consistentWith_empty {B : ℕ} (u : FiniteWorld B) : (worldOf u).ConsistentWith ∅ :=
  fun ψ h => by simp at h

/-- The atom bound of a negation is the atom bound of the sentence (`∼φ = φ 🡒 ⊥`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomBound_neg (φ : Sentence) : atomBound (∼φ) = atomBound φ := by
  show atomBound (φ 🡒 ⊥) = atomBound φ
  simp [atomBound]

/-- The atom bound package for `T_pair` on `atom a` at the empty stage, with `B = a + 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pair_atom_hB (n a : ℕ) :
    ∀ ψ ∈ mentionedSet (pairStrategy n (Formula.atom a)) ∪ (∅ : Finset Sentence),
      atomBound ψ ≤ a + 1 := by
  intro ψ hψ
  rw [Finset.union_empty, mem_mentionedSet_iff, mentionedBy_pairStrategy_iff] at hψ
  rcases hψ with rfl | rfl
  · simp [atomBound]
  · rw [atomBound_neg]; simp [atomBound]

/-- The all-true finite world holds `atom a` (for `a < B`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldOf_const_true_holds_atom {B a : ℕ} (ha : a < B) :
    (worldOf (fun _ : Fin B => true)).Holds (Formula.atom a) := by
  show FiniteWorld.toBoolPCWorld (fun _ : Fin B => true) a = true
  simp [FiniteWorld.toBoolPCWorld, ha]

/-- The all-false finite world fails `atom a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldOf_const_false_not_holds_atom {B a : ℕ} :
    ¬ (worldOf (fun _ : Fin B => false)).Holds (Formula.atom a) := by
  show ¬ FiniteWorld.toBoolPCWorld (fun _ : Fin B => false) a = true
  simp [FiniteWorld.toBoolPCWorld]

/-- **T4(b), interior (N+ for T3).** On `T_pair` at `φ = atom a`, the empty stage and
`B = a + 1` (so `|W_∅| = 2^(a+1) ≥ 2` and `φ` is undecided), the interior maker prices `φ`
strictly inside `(0, 1)`, at every `ε > 0`.
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: exact
Hyps: (a) — `hB` is `pair_atom_hB`, `hW` the all-false world -/
theorem interior_pair_atom_nonDogmatic (n a : ℕ) (past : List RationalBeliefState) (ε : ℚ)
    (hε : 0 < ε) :
    0 < (interiorCoherentMarketMaker (pairStrategy n (Formula.atom a)) past ∅ (a + 1)
        (pair_atom_hB n a) ⟨fun _ => false, consistentWith_empty _⟩
        (mentionedSet (pairStrategy n (Formula.atom a))) (Finset.Subset.refl _) ε hε).quote
          (Formula.atom a) ∧
      (interiorCoherentMarketMaker (pairStrategy n (Formula.atom a)) past ∅ (a + 1)
        (pair_atom_hB n a) ⟨fun _ => false, consistentWith_empty _⟩
        (mentionedSet (pairStrategy n (Formula.atom a))) (Finset.Subset.refl _) ε hε).quote
          (Formula.atom a) < 1 := by
  apply interior_nonDogmatic
  · exact mem_mentionedSet_iff.mpr ((mentionedBy_pairStrategy_iff n _ _).mpr (Or.inl rfl))
  · exact ⟨fun _ => true, mem_worldsOf.mpr (consistentWith_empty _),
      worldOf_const_true_holds_atom (Nat.lt_succ_self a)⟩
  · exact ⟨fun _ => false, mem_worldsOf.mpr (consistentWith_empty _),
      worldOf_const_false_not_holds_atom⟩

/-- `W_∅ (a+1)` has `2^(a+1)` elements (the witness is not a one-world simplex).
Source: [[bli-coherent-mm-mandate]] T3 traps ("the N+ needs `|W_D| ≥ 2`")
Kind: N+
Fidelity: n/a -/
theorem card_worldsOf_empty (B : ℕ) : (worldsOf ∅ B).card = 2 ^ B := by
  have : worldsOf ∅ B = Finset.univ := by
    ext u
    simp [consistentWith_empty u]
  rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-! ## T4(c): a price-responsive strategy accepts only prices near `1/2` -/

/-- **`T_resp`**: buy `1 − 2 · price(φ, n)` shares of `φ` (a feature with a `price` leaf of rank
`n`). It sells when `φ` is priced above `1/2` and buys below.
Source: [[bli-coherent-mm-mandate]] T4(c)
Kind: D
Fidelity: exact -/
def responsiveStrategy (n : ℕ) (φ : Sentence) : Strategy n where
  trades := [(EF.add (EF.const 1) (EF.mul (EF.const (-2)) (EF.price φ n)), φ)]
  rank_le := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    simp [EF.rank]

/-- The exact rational value of `T_resp`: `(1 − 2 Q n φ) * (w φ − Q n φ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma responsiveStrategy_marketValueRat (n : ℕ) (φ : Sentence) (Q : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) :
    (responsiveStrategy n φ).marketValueRat Q w = (1 + (-2) * Q n φ) * (w φ - Q n φ) := by
  simp [responsiveStrategy, Strategy.marketValueRat, EF.denoteRat, EF.denoteRatWith]

/-- `T_resp` mentions `φ` (as a traded sentence).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma responsiveStrategy_mentions (n : ℕ) (φ : Sentence) : MentionedBy (responsiveStrategy n φ) φ :=
  Or.inl ⟨EF.add (EF.const 1) (EF.mul (EF.const (-2)) (EF.price φ n)), by simp [responsiveStrategy]⟩

/-- **T4(c). Only prices within `ε` of `1/2` are coherently accepted on `T_resp`** (for a world
measure, at a sentence some `D`-consistent world holds and some fails): if `p := π w φ` is
accepted at `ε ≥ 0` then `|p − 1/2| ≤ ε`. At `ε → 0` the accepted coherent price is exactly
`1/2`: T1's fixed point is a genuine interior solution, not a boundary artifact.
Source: [[bli-coherent-mm-mandate]] T4(c)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem coherentAccepts_responsive_near_half {n : ℕ} {φ : Sentence} {D : Finset Sentence}
    {B : ℕ} {S : Finset Sentence} {w : FiniteWorld B → ℚ} (hw : IsWorldMeasure D B w)
    (past : List RationalBeliefState) {ε : ℚ} (hε : 0 ≤ ε)
    (hacc : CoherentAccepts (responsiveStrategy n φ) past D B S ε w)
    (h1 : ∃ u ∈ worldsOf D B, (worldOf u).Holds φ)
    (h0 : ∃ u ∈ worldsOf D B, ¬ (worldOf u).Holds φ) :
    |piTable w φ - 1 / 2| ≤ ε := by
  have hφ : φ ∈ S := hacc.1 (mem_mentionedSet_iff.mpr (responsiveStrategy_mentions n φ))
  obtain ⟨u₁, hu₁, hφ₁⟩ := h1
  obtain ⟨u₀, hu₀, hφ₀⟩ := h0
  have ha₁ := hacc.2 u₁ hu₁
  have ha₀ := hacc.2 u₀ hu₀
  rw [responsiveStrategy_marketValueRat] at ha₁ ha₀
  simp only [candidateRationalHistory, Function.update_self] at ha₁ ha₀
  rw [ofWeights_quote_of_mem hw hφ] at ha₁ ha₀
  rw [payoutRat_of_holds hφ₁] at ha₁
  rw [payoutRat_of_not_holds hφ₀] at ha₀
  have hp0 := piTable_nonneg hw φ
  have hp1 := piTable_le_one hw φ
  set p := piTable w φ with hp
  rw [abs_le]
  constructor
  · -- `1/2 − p ≤ ε`: if `p < 1/2` then `(1 − 2p)(1 − p) ≤ ε` with `1 − p ≥ 1/2`
    by_cases hlt : p < 1 / 2
    · nlinarith
    · have := not_lt.mp hlt; linarith
  · -- `p − 1/2 ≤ ε`: if `p > 1/2` then `(2p − 1) p ≤ ε` with `p ≥ 1/2`
    by_cases hgt : 1 / 2 < p
    · nlinarith
    · have := not_lt.mp hgt; linarith

end

end Cleanroom.Bli.BliCoherentMm.AttemptB
