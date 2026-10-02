import Cleanroom.Bli.BliCoherentMm.AttemptA.Maker

/-!
# `bli-coherent-mm` (attempt A) · Contrast: witnesses and the FAF contrast (T4(a)–(c))

* **T4(a), the contrast** (`marketMakerAccepts_pair_sum_ge`, `marketMaker_incoherent_on_pair`,
  `marketMakerStates_pair_incoherent`): on the strategy `pairStrategy a n` buying one share of
  `φ := atom a` and one of `∼φ` (constant coefficients, rank `0`), every table accepted by FAF's
  `MarketMakerAccepts` at `ε < 1` has `quote φ + quote (∼φ) ≥ 2 − ε > 1` — the acceptance clause
  at the Boolean table `b ≡ true` (both "true" at once) — so FAF's `MarketMaker` and every
  `marketMakerStates` of the trader playing this strategy are **not coherent** on `{φ, ∼φ}`
  (a marginal has `π φ + π (∼φ) = 1`). This is bli-slides-044's gap made exact and Soto's PDF 05
  fn. 1. Kind N− for FAF's maker (a finding of record); `coherent_pair_not_marketMakerAccepts`
  shows the coherent maker's table is rejected by FAF's all-Boolean test: the two predicates are
  different objects, not relabellings.
* **T4(b), N+ for T2/T3** on the same strategy: the coherent maker returns
  `quote φ + quote (∼φ) = 1` (`coherent_pair_sum_one`), is accepted in every consistent world
  (`coherent_pair_accepts`), the simplex has `2^B ≥ 2` worlds (`card_WD_empty`), and the interior
  maker quotes `φ ∈ (0,1)` (`interior_pair_quote_mem_Ioo`; `D = ∅`, `φ` undecided).
* **T4(c), the price-responsive strategy** `responsiveStrategy a n` (coefficient `1 − 2·price φ n`,
  a `price` leaf): every coherently accepted price of `φ` is within `ε` of `1/2`
  (`responsive_accepted_near_half`) — T1's fixed point is not a boundary artifact.

`Witness.lean` adds T4(d) (the package over `paperDP 𝗜𝚺₁`).

Sources: [[bli-coherent-mm-mandate]] T4; Soto PDF 05 fn. 1 (bli-soto-a-044); bli-slides-044.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## The pair strategy -/

/-- **`T_pair`**: buy one share of `atom a` and one of `∼atom a`, constant coefficients (rank `0`).
Source: [[bli-coherent-mm-mandate]] T4(a); Soto PDF 05 fn. 1
Kind: D
Fidelity: exact -/
def pairStrategy (a n : ℕ) : Strategy n where
  trades := [(EF.const 1, Formula.atom a), (EF.const 1, ∼(Formula.atom a))]
  rank_le := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [EF.rank]

/-- The trade list of `T_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairStrategy_trades (a n : ℕ) :
    (pairStrategy a n).trades = [(EF.const 1, Formula.atom a), (EF.const 1, ∼(Formula.atom a))] :=
  rfl

/-- `atom a` is traded by `T_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atom_mem_support_pair (a n : ℕ) : Formula.atom a ∈ (pairStrategy a n).support := by
  simp [pairStrategy, Strategy.support]

/-- `∼atom a` is traded by `T_pair`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma neg_atom_mem_support_pair (a n : ℕ) : ∼(Formula.atom a) ∈ (pairStrategy a n).support := by
  simp [pairStrategy, Strategy.support]

/-! ## T4(a): FAF's acceptance forces incoherence on the pair -/

/-- **T4(a), the engine.** Every table `MarketMakerAccepts`-accepted at `ε` against `T_pair` has
`quote φ + quote (∼φ) ≥ 2 − ε`: the acceptance clause at the Boolean support table `b ≡ true`.
Source: [[bli-coherent-mm-mandate]] T4(a); Soto PDF 05 fn. 1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem marketMakerAccepts_pair_sum_ge (a n : ℕ) (past : List RationalBeliefState) (ε : ℚ)
    (Bs : RationalBeliefState) (h : MarketMakerAccepts (pairStrategy a n) past ε Bs) :
    2 - ε ≤ Bs.quote (Formula.atom a) + Bs.quote (∼(Formula.atom a)) := by
  have hb := h.2 (fun _ => true)
  have e1 : supportBitWorldRat (pairStrategy a n) (fun _ => true) (Formula.atom a) = 1 := by
    simp [supportBitWorldRat, atom_mem_support_pair a n]
  have e2 : supportBitWorldRat (pairStrategy a n) (fun _ => true) (∼(Formula.atom a)) = 1 := by
    simp [supportBitWorldRat, neg_atom_mem_support_pair a n]
  simp only [Strategy.marketValueRat, pairStrategy_trades, EF.denoteRat, EF.denoteRatWith, e1, e2,
    candidateRationalHistory, Function.update_self, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hb
  linarith

/-- **T4(a). FAF's acceptance at `ε < 1` is incoherent on the pair**: no table accepted by
`MarketMakerAccepts` against `T_pair` at `ε < 1` is coherent on `{φ, ∼φ}` (for any stage `D` and
atom bound `B`), since a world marginal has `π φ + π (∼φ) = 1 < 2 − ε`.
Source: [[bli-coherent-mm-mandate]] T4(a); bli-slides-044; Soto PDF 05 fn. 1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem marketMaker_incoherent_on_pair (a n : ℕ) (past : List RationalBeliefState) {ε : ℚ}
    (hε1 : ε < 1) (Bs : RationalBeliefState) (h : MarketMakerAccepts (pairStrategy a n) past ε Bs)
    (D : Finset Sentence) (B : ℕ) :
    ¬ CoherentQuoteOn Bs.quote {Formula.atom a, ∼(Formula.atom a)} D B := by
  rintro ⟨w, hw, hV⟩
  have hsum := marketMakerAccepts_pair_sum_ge a n past ε Bs h
  rw [hV _ (Finset.mem_insert_self _ _),
    hV _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), marginal_neg_add hw] at hsum
  linarith

/-- **T4(a) at FAF's `MarketMaker`**: `MarketMaker T_pair past ε hε` is not coherent on
`{φ, ∼φ}` for any `ε < 1`.
Source: [[bli-coherent-mm-mandate]] T4(a)
Kind: N-
Fidelity: n/a (a finding of record about FAF's construction)
Hyps: (a) -/
theorem MarketMaker_pair_incoherent (a n : ℕ) (past : List RationalBeliefState) {ε : ℚ}
    (hε : 0 < ε) (hε1 : ε < 1) (D : Finset Sentence) (B : ℕ) :
    ¬ CoherentQuoteOn (MarketMaker (pairStrategy a n) past ε hε).quote
      {Formula.atom a, ∼(Formula.atom a)} D B :=
  marketMaker_incoherent_on_pair a n past hε1 _ (MarketMaker_accepts _ _ _ _) D B

/-- The trader playing `T_pair` every day.
Source: [[bli-coherent-mm-mandate]] T4(a)
Kind: D
Fidelity: exact -/
def pairTrader (a : ℕ) : Trader := ⟨fun n => pairStrategy a n⟩

/-- `marketMakerError n < 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma marketMakerError_lt_one (n : ℕ) : marketMakerError n < 1 := by
  unfold marketMakerError
  rw [div_lt_one (pow_pos (by norm_num) _)]
  exact one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)

/-- **T4(a) at FAF's recursive market**: every day's state of `marketMakerStates (pairTrader a)`
is incoherent on `{φ, ∼φ}` — FAF's construction is not exactly coherent at any finite time on
this trader.
Source: [[bli-coherent-mm-mandate]] T4(a); bli-slides-044 ("not exactly coherent at finite times")
Kind: N-
Fidelity: n/a (a finding of record about FAF's construction)
Hyps: (a) -/
theorem marketMakerStates_pair_incoherent (a n : ℕ) (D : Finset Sentence) (B : ℕ) :
    ¬ CoherentQuoteOn (marketMakerStates (pairTrader a) n).quote
      {Formula.atom a, ∼(Formula.atom a)} D B := by
  have hacc : MarketMakerAccepts (pairStrategy a n) (marketMakerPast (marketMakerStates (pairTrader a)) n)
      (marketMakerError n) (marketMakerStates (pairTrader a) n) := by
    rw [marketMakerStates]
    exact MarketMaker_accepts _ _ _ _
  exact marketMaker_incoherent_on_pair a n _ (marketMakerError_lt_one n) _ hacc D B

/-! ## T4(b): the coherent maker on the pair (N+ for T2/T3) -/

/-- The empty stage: every finite world is consistent, so `hW` is free.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma hW_empty (B : ℕ) : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith ∅ :=
  ⟨fun _ => true, mem_WD.mp (mem_WD_empty _)⟩

/-- **The simplex over the empty stage has `2^B` worlds** (`≥ 2` for `B ≥ 1`): the witness is not
a one-world simplex.
Source: [[bli-coherent-mm-mandate]] T4(b) ("`|W_D| = 2^B ≥ 2`")
Kind: L
Fidelity: n/a -/
lemma card_WD_empty (B : ℕ) : (WD ∅ B).card = 2 ^ B := by
  have h : WD ∅ B = Finset.univ := Finset.eq_univ_of_forall mem_WD_empty
  rw [h, Finset.card_univ]
  simp

/-- The world with every atom true holds `atom a` (for `a < B`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_atom_allTrue {a B : ℕ} (hB : a < B) :
    (worldOf (fun _ => true : FiniteWorld B)).Holds (Formula.atom a) := by
  simp [worldOf, BoolPCWorld.toPCWorld, FiniteWorld.toBoolPCWorld, hB]

/-- The world with every atom false refutes `atom a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_holds_atom_allFalse {a B : ℕ} :
    ¬ (worldOf (fun _ => false : FiniteWorld B)).Holds (Formula.atom a) := by
  simp [worldOf, BoolPCWorld.toPCWorld, FiniteWorld.toBoolPCWorld]

section Pair

variable (a n : ℕ) (past : List RationalBeliefState) (B : ℕ) {ε : ℚ} (hε : 0 < ε)

/-- **T4(b). The coherent maker on `T_pair` quotes `φ` and `∼φ` to one** — on the same strategy on
which FAF's maker is forced to `≥ 2 − ε`. Stage `D = ∅`, `S = mentionedSet T_pair`.
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: n/a
Hyps: (a) `hε` only; `hS` is `subset_rfl`, `hW` is `hW_empty` -/
theorem coherent_pair_sum_one :
    (coherentMarketMaker (pairStrategy a n) past ∅ B (mentionedSet (pairStrategy a n))
      subset_rfl (hW_empty B) hε).quote (Formula.atom a) +
    (coherentMarketMaker (pairStrategy a n) past ∅ B (mentionedSet (pairStrategy a n))
      subset_rfl (hW_empty B) hε).quote (∼(Formula.atom a)) = 1 := by
  rw [coherentMarketMaker_quote_eq_pi _ _ _ _ _ _ _ _
      (support_subset_mentionedSet _ (atom_mem_support_pair a n)),
    coherentMarketMaker_quote_eq_pi _ _ _ _ _ _ _ _
      (support_subset_mentionedSet _ (neg_atom_mem_support_pair a n))]
  exact marginal_neg_add (coherentWeights_isWorldMeasure _ _ _ _ _ _ _ _) _

/-- **T4(b). The coherent maker on `T_pair` is accepted in every world** (the general theorem at
the witness; `D = ∅`, so every finite world is consistent).
Source: [[bli-coherent-mm-mandate]] T4(b)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem coherent_pair_accepts :
    ∀ u : FiniteWorld B,
      (pairStrategy a n).marketValueRat
        (candidateRationalHistory past n (coherentMarketMaker (pairStrategy a n) past ∅ B
          (mentionedSet (pairStrategy a n)) subset_rfl (hW_empty B) hε)) u.payoutRat ≤ ε :=
  fun u => coherentMarketMaker_accepts _ _ _ _ _ _ _ _ u (mem_WD_empty u)

/-- **The two predicates are different objects**: the coherent maker's table on `T_pair` is
*rejected* by FAF's all-Boolean `MarketMakerAccepts` at every `ε < 1` (it is accepted by D3 at
every `ε > 0`).
Source: [[bli-coherent-mm-mandate]] T4(a) (fake-success trap), D3
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem coherent_pair_not_marketMakerAccepts (hε1 : ε < 1) :
    ¬ MarketMakerAccepts (pairStrategy a n) past ε
      (coherentMarketMaker (pairStrategy a n) past ∅ B (mentionedSet (pairStrategy a n))
        subset_rfl (hW_empty B) hε) := by
  intro h
  have hsum := marketMakerAccepts_pair_sum_ge a n past ε _ h
  rw [coherent_pair_sum_one a n past B hε] at hsum
  linarith

/-- **T4(b). The interior maker on `T_pair` quotes `φ` strictly inside `(0,1)`** (`a < B`; `φ` is
undecided by `D = ∅`: the all-true world holds it, the all-false world refutes it).
Source: [[bli-coherent-mm-mandate]] T4(b); T3
Kind: N+
Fidelity: n/a
Hyps: (a) `hB : a < B` (the atom is within the bound), `hε` -/
theorem interior_pair_quote_mem_Ioo (hB : a < B) :
    0 < (interiorCoherentMarketMaker (pairStrategy a n) past ∅ B (mentionedSet (pairStrategy a n))
      subset_rfl (hW_empty B) hε).quote (Formula.atom a) ∧
    (interiorCoherentMarketMaker (pairStrategy a n) past ∅ B (mentionedSet (pairStrategy a n))
      subset_rfl (hW_empty B) hε).quote (Formula.atom a) < 1 :=
  interior_nonDogmatic _ _ _ _ _ _ _ _ (support_subset_mentionedSet _ (atom_mem_support_pair a n))
    ⟨fun _ => true, mem_WD_empty _, holds_atom_allTrue hB⟩
    ⟨fun _ => false, mem_WD_empty _, not_holds_atom_allFalse⟩

end Pair

/-! ## T4(c): a price-responsive strategy -/

/-- **The responsive strategy**: buy `1 − 2·price (atom a) n` shares of `atom a` (a `price` leaf
of rank `n`).
Source: [[bli-coherent-mm-mandate]] T4(c)
Kind: D
Fidelity: exact -/
def responsiveStrategy (a n : ℕ) : Strategy n where
  trades := [(EF.add (EF.const 1) (EF.mul (EF.const (-2)) (EF.price (Formula.atom a) n)),
    Formula.atom a)]
  rank_le := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    simp [EF.rank]

/-- **T4(c). Every coherently accepted price of `atom a` against the responsive strategy is within
`ε` of `1/2`**: in the all-true world the value is `(1 − 2p)(1 − p)`, in the all-false world
`(1 − 2p)(−p)`; both `≤ ε` forces `|p − 1/2| ≤ ε`. T1's fixed point is not a boundary artifact.
Source: [[bli-coherent-mm-mandate]] T4(c)
Kind: N+
Fidelity: n/a
Hyps: (a) `hB : a < B`, `hS : atom a ∈ S`, `hacc` -/
theorem responsive_accepted_near_half (a n : ℕ) (past : List RationalBeliefState) (B : ℕ)
    (hB : a < B) (S : Finset Sentence) (hS : Formula.atom a ∈ S) {ε : ℚ}
    {w : FiniteWorld B → ℚ} (hacc : CoherentAccepts (responsiveStrategy a n) past ∅ B S ε w) :
    |marginal w (Formula.atom a) - 1 / 2| ≤ ε := by
  have hT : FiniteWorld.payoutRat (fun _ => true : FiniteWorld B) (Formula.atom a) = 1 :=
    payoutRat_of_holds (holds_atom_allTrue hB)
  have hF : FiniteWorld.payoutRat (fun _ => false : FiniteWorld B) (Formula.atom a) = 0 :=
    payoutRat_of_not_holds not_holds_atom_allFalse
  have h1 := hacc.2 (fun _ => true) (mem_WD_empty _)
  have h0 := hacc.2 (fun _ => false) (mem_WD_empty _)
  simp only [Strategy.marketValueRat, responsiveStrategy, EF.denoteRat, EF.denoteRatWith,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hT, hF,
    candidateTable_self_of_mem past n w hS] at h1 h0
  have hp0 := marginal_nonneg hacc.1 (Formula.atom a)
  have hp1 := marginal_le_one hacc.1 (Formula.atom a)
  set p := marginal w (Formula.atom a) with hp
  rw [abs_le]
  by_cases hhalf : p ≤ 1 / 2
  · constructor <;> nlinarith
  · rw [not_le] at hhalf
    constructor <;> nlinarith

end Cleanroom.Bli.BliCoherentMm.AttemptA
