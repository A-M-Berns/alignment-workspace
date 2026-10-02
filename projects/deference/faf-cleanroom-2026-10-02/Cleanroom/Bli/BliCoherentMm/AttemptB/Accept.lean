import Cleanroom.Bli.BliCoherentMm.AttemptB.FixedPoint

/-!
# `bli-coherent-mm` (attempt B) · Accept: world measures, coherent acceptance, the coherent
market maker (D2–D4, T2)

* **D2** `IsWorldMeasure D B w` (rational, nonnegative, mass `1`, supported on `W_D B`),
  `piTable w φ := ∑ u, w u * u.payoutRat φ` (exactly bli-finite's `IsWorldMarginal` witness
  shape), `ofWeights S w : RationalBeliefState` with entries `(φ, π w φ)` for `φ ∈ S` and quote
  `0` off `S`. (`ofWeights` clamps `π w φ` to `[0,1]` to be total in `w`; for a world measure the
  clamp is the identity, `ofWeights_quote_of_mem`.)
* **D3** `CoherentAccepts T past D B S ε w`: `S ⊇ mentionedSet T` and, for every `u ∈ W_D B`,
  `T.marketValueRat (candidateRationalHistory past n (ofWeights S w)) u.payoutRat ≤ ε`. Decidable
  (finite `W_D`, exact rational arithmetic). **Over `D`-consistent worlds only** — never over all
  Boolean tables on the support (T4 shows that predicate is unsatisfiable by coherent `w`).
* **The real/rational bridge** `worldValue_cast_eq`: the real value of `T` on the history of the
  cast weights, in a finite world, is the cast of the rational acceptance value — through
  `Strategy.value_eq_marketRatCast` and `bli-overlay`'s locality congruence (the candidate state
  quotes `0` off `S`, the real table `priceOf` does not; `T` only reads `S ⊇ mentionedSet T`).
* **Angle B's rounding** `gridRound u₀ d p`: floor every `p u · d`, hand the whole deficit to the
  anchor `u₀` — every coordinate is in `(1/d)·ℕ`, within `card ι / d` of `p` (the explicit,
  one-sided "floor and dump" rounding; no classical choice beyond `Nat.floor` on reals).
* **T2(a)** `exists_meshAccepted` / `exists_coherentAccepts`: for every `ε > 0` some mesh `d`
  makes the rounded fixed point a world measure accepted at `ε` (continuity of the finitely many
  world values at `p*`, `exists_delta_of_fixed`, plus the rounding error `< δ`).
* **D4 / T2(b)** `coherentMesh` (`Nat.find` on `MeshAccepted`), `coherentWeights`,
  `coherentMarketMaker := ofWeights S coherentWeights`, with `coherentMarketMaker_accepts`,
  `coherentWeights_isWorldMeasure`, `coherentMarketMaker_quote_eq_pi`,
  `coherentMarketMaker_coherent` (the marginal form, on the extended table `piTable`, which the
  quote equals on `S`), `coherentMarketMaker_coherentOn` (bli-finite's `CoherentOn` over the
  constant index with day set `S`), `coherentWeights_mem_grid` (the `(1/d)·ℕ` grid shape B3
  wants).
* **T2(c)** `coherentMarketMaker_respects` / `_respects_false`: a sentence decided (true/false)
  by `D` is priced at its truth — a *consequence* of being a marginal over `D`-consistent worlds.
* **T2(d)** `dayValue_le_of_coherentAccepts`: the customer's entry point (coherent twin of
  `bli-overlay`'s `dayValue_le_of_accepted_state`), over `D`-consistent `PCWorld`s.
* **T2(e)** `coherentMarketMakerSmall`: the `S = smallSet n` instance.

Sources: [[bli-coherent-mm-mandate]] D2–D4, T2, §Attempt angles (B); Soto PDF 05 Def 1, Def 3,
Def 8 (bli-soto-a-043); [[bli-program]] §3.8, §4 row M2.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptB

open LogicalInduction LogicalInduction.BoolPCWorld LO.Propositional Cleanroom.Bli.BliFound
  Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliFinite Finset

/- `Finset.toList` (the entry order of `ofWeights`) is noncomputable, as in `bli-overlay`'s
`restrictState`; the makers are `Nat.find`s on existence theorems, as FAF's `MarketMaker` is.
The decision procedures below are decidable propositions whose *instances* are therefore
noncomputable terms — the search is a mathematical object here, not a program. -/
noncomputable section

/-! ## D2: rational world measures and their price tables -/

/-- **D2. A (rational) world measure on `W_D B`**: nonnegative, mass `1`, supported on the
`D`-consistent worlds.
Source: [[bli-coherent-mm-mandate]] D2; Soto PDF 05 Def 1 (bli-soto-a-043)
Kind: D
Fidelity: exact -/
def IsWorldMeasure (D : Finset Sentence) (B : ℕ) (w : FiniteWorld B → ℚ) : Prop :=
  (∀ u, 0 ≤ w u) ∧ ∑ u, w u = 1 ∧ ∀ u, w u ≠ 0 → (worldOf u).ConsistentWith D

/-- Being a world measure is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance instDecidableIsWorldMeasure (D : Finset Sentence) (B : ℕ) (w : FiniteWorld B → ℚ) :
    Decidable (IsWorldMeasure D B w) := by
  unfold IsWorldMeasure; infer_instance

/-- **D2. The price table of a weight vector**: `π w φ := ∑ u, w u * payoutRat_u φ` — Soto's
`P_n(φ) := ∑_{W ⊨ φ} P_n(W)`, and exactly the witness shape of bli-finite's `IsWorldMarginal`.
Source: [[bli-coherent-mm-mandate]] D2; Soto PDF 05 Def 1
Kind: D
Fidelity: exact -/
def piTable {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) : ℚ :=
  ∑ u, w u * u.payoutRat φ

/-- A world measure's prices are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma piTable_nonneg {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (φ : Sentence) : 0 ≤ piTable w φ :=
  sum_nonneg fun u _ => mul_nonneg (hw.1 u) (payoutRat_nonneg u φ)

/-- A world measure's prices are at most one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma piTable_le_one {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (φ : Sentence) : piTable w φ ≤ 1 :=
  calc piTable w φ ≤ ∑ u, w u :=
        sum_le_sum fun u _ => mul_le_of_le_one_right (hw.1 u) (payoutRat_le_one u φ)
    _ = 1 := hw.2.1

/-- A world measure's prices lie in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma piTable_mem_Icc {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (φ : Sentence) : 0 ≤ piTable w φ ∧ piTable w φ ≤ 1 :=
  ⟨piTable_nonneg hw φ, piTable_le_one hw φ⟩

/-- **The price table of a world measure is a world marginal on every algebra** (bli-finite's
`IsWorldMarginal`, hence `TwoAxiomCoherent` by `twoAxiom_of_worldMarginal`).
Source: [[bli-coherent-mm-mandate]] D2; [[bli-finite-report]] (`IsWorldMarginal`)
Kind: L
Fidelity: exact -/
theorem piTable_isWorldMarginal {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (A : Finset Sentence) : IsWorldMarginal (piTable w) A D B :=
  ⟨w, hw.1, hw.2.1, hw.2.2, fun _ _ => rfl⟩

/-- **D2. The candidate belief state** of weights `w` on the sentence set `S`: entries
`(φ, π w φ)` for `φ ∈ S` (keys `S.toList`, duplicate-free), quote `0` off `S`. The entry value
is clamped to `[0,1]` so the state is total in `w`; for a world measure the clamp is the
identity (`ofWeights_quote_of_mem`) — the only use.
Source: [[bli-coherent-mm-mandate]] D2
Kind: D
Fidelity: exact (for world measures; `clamp01` is a totality device, disclosed) -/
def ofWeights (S : Finset Sentence) {B : ℕ} (w : FiniteWorld B → ℚ) : RationalBeliefState where
  entries := S.toList.map fun φ => (φ, clamp01 (piTable w φ))
  keys_nodup := by
    rw [List.map_map]
    simpa [Function.comp_def] using S.nodup_toList
  bounded := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨φ, _, rfl⟩ := hp
    exact ⟨clamp01_nonneg _, clamp01_le_one _⟩

/-- Lookup off the key list is `0` (FAF keeps this `private`; re-proved).
Source: none: infrastructure (FAF API request: `quoteFromEntries_eq_zero`)
Kind: L
Fidelity: n/a -/
lemma quoteFromEntries_map_eq_zero (f : Sentence → ℚ) :
    ∀ (l : List Sentence) {φ : Sentence}, φ ∉ l →
      quoteFromEntries (l.map fun ψ => (ψ, f ψ)) φ = 0
  | [], _, _ => rfl
  | ψ :: rest, φ, hφ => by
      simp only [List.mem_cons, not_or] at hφ
      simp [hφ.1, quoteFromEntries_map_eq_zero f rest hφ.2]

/-- On `S`, the candidate state quotes `π w` (for a world measure).
Source: [[bli-coherent-mm-mandate]] D2
Kind: L
Fidelity: n/a -/
lemma ofWeights_quote_of_mem {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) {S : Finset Sentence} {φ : Sentence} (hφ : φ ∈ S) :
    (ofWeights S w).quote φ = piTable w φ := by
  unfold ofWeights RationalBeliefState.quote
  simp only
  rw [Cleanroom.Bli.BliOverlay.AttemptA.quoteFromEntries_map_eq S.nodup_toList _
    (Finset.mem_toList.mpr hφ)]
  exact clamp01_eq_self (piTable_mem_Icc hw φ)

/-- Off `S`, the candidate state quotes `0`.
Source: [[bli-coherent-mm-mandate]] D2
Kind: L
Fidelity: n/a -/
lemma ofWeights_quote_of_not_mem {B : ℕ} (w : FiniteWorld B → ℚ) {S : Finset Sentence}
    {φ : Sentence} (hφ : φ ∉ S) : (ofWeights S w).quote φ = 0 := by
  unfold ofWeights RationalBeliefState.quote
  simp only
  exact quoteFromEntries_map_eq_zero _ S.toList fun h => hφ (Finset.mem_toList.mp h)

/-! ## D3: coherent acceptance -/

/-- **D3. Coherent acceptance**: `S ⊇ mentionedSet T`, and in every `D`-consistent finite world
`u` the exact rational value of `T` on the candidate history (days `< n` from `past`, day `n`
the table `π w` on `S`) at the payouts of `u` is at most `ε`. Decidable. Checked **over
`D`-consistent worlds only** — never over all Boolean tables on `T.support`, which is FAF's
`MarketMakerAccepts` and is unsatisfiable by coherent `w` in general (T4(a)).
Source: [[bli-coherent-mm-mandate]] D3; Soto PDF 05 Thm 2 ("B(W) ≤ 0 for all W")
Kind: D
Fidelity: exact -/
def CoherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) (w : FiniteWorld B → ℚ) : Prop :=
  mentionedSet T ⊆ S ∧ ∀ u ∈ worldsOf D B,
    T.marketValueRat (candidateRationalHistory past n (ofWeights S w))
      (fun φ => u.payoutRat φ) ≤ ε

/-- Coherent acceptance is decidable (a `Finset` inclusion and a scan of `W_D B` by exact
rational arithmetic) — the search predicate.
Source: [[bli-coherent-mm-mandate]] D3
Kind: D
Fidelity: n/a -/
instance instDecidableCoherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) (w : FiniteWorld B → ℚ) :
    Decidable (CoherentAccepts T past D B S ε w) := by
  unfold CoherentAccepts; infer_instance

/-! ## The real/rational bridge -/

/-- A finite world's real payout is the cast of its rational payout.
Source: FAF `eval_eq_true_iff_holds` (through bli-finite's `payoutRat_eq_ite`)
Kind: L
Fidelity: n/a -/
lemma payout_eq_cast_payoutRat {B : ℕ} (u : FiniteWorld B) (φ : Sentence) :
    (worldOf u).payout φ = (u.payoutRat φ : ℝ) := by
  rw [payoutRat_eq_ite]
  unfold PCWorld.payout
  split_ifs <;> simp

/-- The real price table of cast weights is the cast of the rational price table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma priceOf_cast {B : ℕ} (w : FiniteWorld B → ℚ) (φ : Sentence) :
    priceOf (fun u => (w u : ℝ)) φ = (piTable w φ : ℝ) := by
  unfold priceOf piTable
  push_cast
  simp only [payout_eq_cast_payoutRat]

/-- **The bridge.** For a world measure `w` and `S ⊇ mentionedSet T`, the real value of `T` on
the history of the cast weights (`fixedHistory`, which prices *every* sentence by `priceOf`), in
the finite world `u`, is the cast of the rational acceptance value on the candidate history
(which prices only `S`): the two histories agree on every cell `T` mentions.
Source: [[bli-coherent-mm-mandate]] T2(a) ("the value only reads mentioned cells")
Kind: L
Fidelity: n/a -/
lemma worldValue_cast_eq {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    {D : Finset Sentence} {B : ℕ} {S : Finset Sentence} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (hS : mentionedSet T ⊆ S) (u : FiniteWorld B) :
    worldValue T past (fun u => (w u : ℝ)) u =
      (T.marketValueRat (candidateRationalHistory past n (ofWeights S w))
        (fun φ => u.payoutRat φ) : ℝ) := by
  unfold worldValue
  rw [← Strategy.value_eq_marketRatCast T
    (fun d φ => (candidateRationalHistory past n (ofWeights S w) d φ : ℝ)) _ (fun _ _ => rfl)
    (worldOf u).payout (fun φ => u.payoutRat φ) (fun φ => payout_eq_cast_payoutRat u φ)]
  apply Cleanroom.Bli.BliOverlay.Strategy.value_eq_of_eqOn_mentioned
  intro φ hφ k hk
  rcases Nat.lt_or_eq_of_le hk with hlt | rfl
  · simp [fixedHistory, candidateRationalHistory, Function.update_of_ne (Nat.ne_of_lt hlt),
      beliefHistory]
  · simp only [fixedHistory, candidateRationalHistory, Function.update_self]
    rw [priceOf_cast, ofWeights_quote_of_mem hw (hS (mem_mentionedSet_iff.mpr hφ))]

/-- Real acceptance (value `≤ ε` in every `D`-consistent finite world on the history of the cast
weights) gives coherent acceptance.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coherentAccepts_of_real {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    {D : Finset Sentence} {B : ℕ} {S : Finset Sentence} {ε : ℚ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) (hS : mentionedSet T ⊆ S)
    (h : ∀ u ∈ worldsOf D B, worldValue T past (fun u => (w u : ℝ)) u ≤ (ε : ℝ)) :
    CoherentAccepts T past D B S ε w := by
  refine ⟨hS, fun u hu => ?_⟩
  have h' := h u hu
  rw [worldValue_cast_eq T past hw hS u] at h'
  exact_mod_cast h'

/-! ## Angle B's rounding: floor and dump -/

section Rounding

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Floor-and-dump rounding** of a real weight vector at mesh `d`: every `p u · d` is floored,
and the whole deficit `d − ∑ ⌊p u d⌋` goes to the anchor `u₀`. Values in `(1/d)·ℕ`.
Source: [[bli-coherent-mm-mandate]] §Attempt angles (B) ("round the real fixed point")
Kind: D
Fidelity: variant: one-sided (floor) rounding with the deficit on one coordinate, error
`≤ card ι / d` — not bli-finite's `remainderRound` (which takes rational input) -/
noncomputable def gridRound (u₀ : ι) (d : ℕ) (p : ι → ℝ) : ι → ℚ :=
  fun u => (⌊p u * d⌋₊ : ℚ) / d + if u = u₀ then ((d - ∑ v, ⌊p v * d⌋₊ : ℕ) : ℚ) / d else 0

/-- The real cast of a rounded coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cast_gridRound (u₀ : ι) (d : ℕ) (p : ι → ℝ) (u : ι) :
    (gridRound u₀ d p u : ℝ) = (⌊p u * d⌋₊ : ℝ) / d +
      if u = u₀ then ((d - ∑ v, ⌊p v * d⌋₊ : ℕ) : ℝ) / d else 0 := by
  unfold gridRound
  split_ifs <;> push_cast <;> ring

/-- Rounded weights are nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridRound_nonneg (u₀ : ι) (d : ℕ) (p : ι → ℝ) (u : ι) : 0 ≤ gridRound u₀ d p u := by
  unfold gridRound
  apply add_nonneg (by positivity)
  split_ifs <;> positivity

/-- Rounded weights are multiples of `1/d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridRound_mem_grid (u₀ : ι) (d : ℕ) (p : ι → ℝ) (u : ι) :
    ∃ k : ℕ, gridRound u₀ d p u = (k : ℚ) / d := by
  unfold gridRound
  split_ifs
  · exact ⟨⌊p u * d⌋₊ + (d - ∑ v, ⌊p v * d⌋₊), by push_cast; ring⟩
  · exact ⟨⌊p u * d⌋₊, by ring⟩

omit [DecidableEq ι] in
/-- The floors of a probability vector at mesh `d` sum to at most `d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_floor_le {d : ℕ} (p : ι → ℝ) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∑ u, p u = 1) :
    ∑ v, ⌊p v * d⌋₊ ≤ d := by
  have h : ((∑ v, ⌊p v * d⌋₊ : ℕ) : ℝ) ≤ d := by
    push_cast
    calc ∑ v, (⌊p v * d⌋₊ : ℝ) ≤ ∑ v, p v * d :=
          sum_le_sum fun v _ => Nat.floor_le (mul_nonneg (hp0 v) (Nat.cast_nonneg d))
      _ = d := by rw [← sum_mul, hp1, one_mul]
  exact_mod_cast h

omit [DecidableEq ι] in
/-- The floors of a probability vector at mesh `d` sum to at least `d − card ι`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma deficit_le_card {d : ℕ} (p : ι → ℝ) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∑ u, p u = 1) :
    ((d - ∑ v, ⌊p v * d⌋₊ : ℕ) : ℝ) ≤ Fintype.card ι := by
  have h1 : ∑ v, (p v * d - 1) ≤ ∑ v, (⌊p v * d⌋₊ : ℝ) :=
    sum_le_sum fun v _ => by linarith [Nat.lt_floor_add_one (p v * d)]
  rw [sum_sub_distrib, ← sum_mul, hp1, one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one] at h1
  rw [Nat.cast_sub (sum_floor_le p hp0 hp1)]
  push_cast
  linarith

/-- Rounded weights sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridRound_sum (u₀ : ι) {d : ℕ} (hd : 0 < d) (p : ι → ℝ) (hp0 : ∀ u, 0 ≤ p u)
    (hp1 : ∑ u, p u = 1) : ∑ u, gridRound u₀ d p u = 1 := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold gridRound
  rw [sum_add_distrib]
  simp only [sum_ite_eq', mem_univ, if_true]
  rw [← sum_div, ← Nat.cast_sum, Nat.cast_sub (sum_floor_le p hp0 hp1), ← add_div,
    div_eq_one_iff_eq hdq]
  ring

/-- Every rounded weight is at least `p u − 1/d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridRound_ge (u₀ : ι) {d : ℕ} (hd : 0 < d) (p : ι → ℝ) (u : ι) :
    p u - 1 / d ≤ (gridRound u₀ d p u : ℝ) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [cast_gridRound]
  have h1 : p u - 1 / d ≤ (⌊p u * d⌋₊ : ℝ) / d := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hdr]
    linarith [Nat.lt_floor_add_one (p u * d)]
  have h2 : (0 : ℝ) ≤ if u = u₀ then ((d - ∑ v, ⌊p v * d⌋₊ : ℕ) : ℝ) / d else 0 := by
    split_ifs <;> positivity
  linarith

/-- Every rounded weight is at most `p u + card ι / d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridRound_le (u₀ : ι) {d : ℕ} (hd : 0 < d) (p : ι → ℝ) (hp0 : ∀ u, 0 ≤ p u)
    (hp1 : ∑ u, p u = 1) (u : ι) :
    (gridRound u₀ d p u : ℝ) ≤ p u + Fintype.card ι / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [cast_gridRound]
  have h1 : (⌊p u * d⌋₊ : ℝ) / d ≤ p u := by
    rw [div_le_iff₀ hdr]
    exact Nat.floor_le (mul_nonneg (hp0 u) hdr.le)
  have h2 : (if u = u₀ then ((d - ∑ v, ⌊p v * d⌋₊ : ℕ) : ℝ) / d else 0) ≤
      Fintype.card ι / d := by
    split_ifs
    · exact div_le_div_of_nonneg_right (deficit_le_card p hp0 hp1) hdr.le
    · positivity
  linarith

end Rounding

/-! ## The acceptance region is open at the fixed point -/

/-- **Continuity at the fixed point.** If every `D`-consistent world value is `≤ 0` at `q*`, then
for every `ε > 0` there is `δ > 0` such that every `q` within `δ` of `q*` in every coordinate has
every `D`-consistent world value `< ε`. (The finitely many world values are continuous in the
weights; the acceptance region is a finite intersection of open half-spaces.)
Source: [[bli-coherent-mm-mandate]] T2(a) ("by continuity"); FAF `exists_rationalPriceVector_good`
(the pattern)
Kind: L
Fidelity: n/a -/
lemma exists_delta_of_fixed {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (q : ↥(worldsOf D B) → ℝ)
    (hle : ∀ u : ↥(worldsOf D B), worldValue T past (extWeights D B q) u.1 ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q' : ↥(worldsOf D B) → ℝ, (∀ u, |q' u - q u| < δ) →
      ∀ u : ↥(worldsOf D B), worldValue T past (extWeights D B q') u.1 < ε := by
  let U : Set (↥(worldsOf D B) → ℝ) :=
    ⋂ u : ↥(worldsOf D B), (fun q' => worldValue T past (extWeights D B q') u.1) ⁻¹' Set.Iio ε
  have hU : IsOpen U := isOpen_iInter_of_finite fun u =>
    isOpen_Iio.preimage ((continuous_worldValue T past u.1).comp (continuous_extWeights D B))
  have hq : q ∈ U := by
    rw [Set.mem_iInter]
    intro u
    exact lt_of_le_of_lt (hle u) hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU q hq
  refine ⟨δ, hδ, fun q' hq' u => ?_⟩
  have hmem : q' ∈ Metric.ball q δ := by
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro u
    rw [Real.dist_eq]
    exact hq' u
  have h := hball hmem
  rw [Set.mem_iInter] at h
  exact h u

/-! ## D4: the rounded fixed point; the search over the mesh -/

/-- Rational zero-extension of weights on `W_D B` to all finite worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def extWeightsQ (D : Finset Sentence) (B : ℕ) (w : ↥(worldsOf D B) → ℚ) : FiniteWorld B → ℚ :=
  fun u => if h : u ∈ worldsOf D B then w ⟨u, h⟩ else 0

/-- The cast of the rational extension is the real extension of the cast.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cast_extWeightsQ (D : Finset Sentence) (B : ℕ) (w : ↥(worldsOf D B) → ℚ) :
    (fun u => (extWeightsQ D B w u : ℝ)) = extWeights D B (fun u => (w u : ℝ)) := by
  funext u
  unfold extWeightsQ extWeights
  split_ifs <;> simp

/-- The rational extension has the mass of `w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_extWeightsQ (D : Finset Sentence) (B : ℕ) (w : ↥(worldsOf D B) → ℚ) :
    ∑ u, extWeightsQ D B w u = ∑ u : ↥(worldsOf D B), w u := by
  rw [← sum_subset (subset_univ (worldsOf D B)) (fun u _ hu => by simp [extWeightsQ, hu])]
  rw [← sum_coe_sort (worldsOf D B)]
  apply sum_congr rfl
  intro u _
  simp [extWeightsQ, u.2]

/-- The rational extension is supported on `W_D B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extWeightsQ_support (D : Finset Sentence) (B : ℕ) (w : ↥(worldsOf D B) → ℚ)
    (u : FiniteWorld B) (h : extWeightsQ D B w u ≠ 0) : (worldOf u).ConsistentWith D := by
  by_contra hcon
  apply h
  unfold extWeightsQ
  rw [dif_neg (fun hm => hcon (mem_worldsOf.mp hm))]

/-- The rational extension at a consistent world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extWeightsQ_of_mem (D : Finset Sentence) (B : ℕ) (w : ↥(worldsOf D B) → ℚ)
    {u : FiniteWorld B} (hu : u ∈ worldsOf D B) : extWeightsQ D B w u = w ⟨u, hu⟩ := by
  simp [extWeightsQ, hu]

/-! ## T2(c): decided sentences are priced at their truth -/

/-- A sentence true in every `D`-consistent world is priced `1` by every world measure on `W_D`.
Source: [[bli-coherent-mm-mandate]] T2(c); Soto PDF 05 Def 3 ("respects `D̄`")
Kind: L
Fidelity: exact -/
theorem piTable_eq_one_of_decided {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) : piTable w φ = 1 := by
  unfold piTable
  rw [← hw.2.1]
  apply sum_congr rfl
  intro u _
  by_cases hu : w u = 0
  · rw [hu, zero_mul]
  · rw [payoutRat_of_holds (h _ (hw.2.2 u hu)), mul_one]

/-- A sentence false in every `D`-consistent world is priced `0` by every world measure on `W_D`.
Source: [[bli-coherent-mm-mandate]] T2(c)
Kind: L
Fidelity: exact -/
theorem piTable_eq_zero_of_decided_false {D : Finset Sentence} {B : ℕ} {w : FiniteWorld B → ℚ}
    (hw : IsWorldMeasure D B w) {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) : piTable w φ = 0 := by
  unfold piTable
  apply sum_eq_zero
  intro u _
  by_cases hu : w u = 0
  · rw [hu, zero_mul]
  · rw [payoutRat_of_not_holds (h _ (hw.2.2 u hu)), mul_zero]

section Maker

variable {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
  (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
  (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)

include hB hW

/-- **The real coherent fixed point, chosen** (T1's witness).
Source: [[bli-coherent-mm-mandate]] D4 (angle B: "the rounded fixed point")
Kind: D
Fidelity: exact -/
noncomputable def fixedPointWeights : FiniteWorld B → ℝ :=
  Classical.choose (coherent_fixed_point T past D B hB hW)

/-- The chosen fixed point is a real world measure with every `D`-consistent world value `≤ 0`.
Source: [[bli-coherent-mm-mandate]] T1
Kind: L
Fidelity: n/a -/
lemma fixedPointWeights_spec :
    IsRealWorldMeasure D B (fixedPointWeights T past D B hB hW) ∧
      ∀ u ∈ worldsOf D B, worldValue T past (fixedPointWeights T past D B hB hW) u ≤ 0 := by
  have h := Classical.choose_spec (coherent_fixed_point T past D B hB hW)
  exact ⟨h.1, h.2.1⟩

/-- The fixed point restricted to `W_D B`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def fixedPointSub : ↥(worldsOf D B) → ℝ :=
  fun u => fixedPointWeights T past D B hB hW u.1

/-- The fixed point is the extension of its restriction (it is supported on `W_D B`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extWeights_fixedPointSub :
    extWeights D B (fixedPointSub T past D B hB hW) = fixedPointWeights T past D B hB hW := by
  funext u
  unfold extWeights fixedPointSub
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (mem_worldsOf.mpr ((fixedPointWeights_spec T past D B hB hW).1.2.2 u (Ne.symm hne)))

/-- The restricted fixed point is a probability vector on `W_D B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fixedPointSub_mem :
    fixedPointSub T past D B hB hW ∈ stdSimplex ℝ ↥(worldsOf D B) := by
  have hspec := (fixedPointWeights_spec T past D B hB hW).1
  refine ⟨fun u => hspec.1 u.1, ?_⟩
  have h := sum_extWeights D B (fixedPointSub T past D B hB hW)
  rw [extWeights_fixedPointSub, hspec.2.1] at h
  exact h.symm

/-- The anchor world (a `D`-consistent world, from `hW`) receiving the rounding deficit.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def anchor : ↥(worldsOf D B) :=
  ⟨Classical.choose hW, mem_worldsOf.mpr (Classical.choose_spec hW)⟩

/-- **The mesh-`d` candidate**: the fixed point rounded at mesh `d` (angle B), extended by zero.
Source: [[bli-coherent-mm-mandate]] D4 (angle B)
Kind: D
Fidelity: exact -/
noncomputable def meshCandidate (d : ℕ) : FiniteWorld B → ℚ :=
  extWeightsQ D B (gridRound (anchor D B hW) d (fixedPointSub T past D B hB hW))

/-- **The search predicate** (angle B): mesh `d > 0` whose candidate is a world measure accepted
at `ε` on `S`.
Source: [[bli-coherent-mm-mandate]] D4 (angle B: "`Nat.find` on … accepted at `ε`")
Kind: D
Fidelity: exact -/
def MeshAccepted (S : Finset Sentence) (ε : ℚ) (d : ℕ) : Prop :=
  0 < d ∧ IsWorldMeasure D B (meshCandidate T past D B hB hW d) ∧
    CoherentAccepts T past D B S ε (meshCandidate T past D B hB hW d)

/-- The search predicate is decidable (positivity, a world-measure check, coherent acceptance).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance instDecidableMeshAccepted (S : Finset Sentence) (ε : ℚ) :
    DecidablePred (MeshAccepted T past D B hB hW S ε) := fun _ => by
  unfold MeshAccepted; infer_instance

/-- The mesh candidate is a world measure at every positive mesh.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma meshCandidate_isWorldMeasure {d : ℕ} (hd : 0 < d) :
    IsWorldMeasure D B (meshCandidate T past D B hB hW d) := by
  have hmem := fixedPointSub_mem T past D B hB hW
  refine ⟨fun u => ?_, ?_, fun u hu => extWeightsQ_support D B _ u hu⟩
  · unfold meshCandidate extWeightsQ
    split_ifs
    · exact gridRound_nonneg _ _ _ _
    · exact le_rfl
  · unfold meshCandidate
    rw [sum_extWeightsQ]
    exact gridRound_sum _ hd _ hmem.1 hmem.2

/-- **T2(a), search form. Some mesh is accepted**: for every `ε > 0` and `S ⊇ mentionedSet T`,
there is a mesh `d` whose rounded fixed point is a world measure coherently accepted at `ε`.
Source: [[bli-coherent-mm-mandate]] T2(a); FAF `exists_rationalPriceVector_good` (the pattern)
Kind: P
Fidelity: exact
Hyps: (a) `hS` (the sentence set covers the mentioned set), (a) `hε`, (a) `hB`, (a) `hW` -/
theorem exists_meshAccepted (S : Finset Sentence) (hS : mentionedSet T ⊆ S) {ε : ℚ}
    (hε : 0 < ε) : ∃ d, MeshAccepted T past D B hB hW S ε d := by
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hle : ∀ u : ↥(worldsOf D B),
      worldValue T past (extWeights D B (fixedPointSub T past D B hB hW)) u.1 ≤ 0 := by
    rw [extWeights_fixedPointSub]
    exact fun u => (fixedPointWeights_spec T past D B hB hW).2 u.1 u.2
  obtain ⟨δ, hδ, hδspec⟩ := exists_delta_of_fixed T past D B _ hle hεr
  set c : ℝ := Fintype.card ↥(worldsOf D B) + 1 with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨d, hd⟩ := exists_nat_gt (c / δ)
  have hdr : (0 : ℝ) < d := lt_trans (div_pos hcpos hδ) hd
  have hdpos : 0 < d := by exact_mod_cast hdr
  have hcd : c / d < δ := by
    rw [div_lt_iff₀ hdr]
    rw [div_lt_iff₀ hδ] at hd
    linarith
  have hmem := fixedPointSub_mem T past D B hB hW
  refine ⟨d, hdpos, meshCandidate_isWorldMeasure T past D B hB hW hdpos, ?_⟩
  apply coherentAccepts_of_real T past (meshCandidate_isWorldMeasure T past D B hB hW hdpos) hS
  intro u hu
  unfold meshCandidate
  rw [cast_extWeightsQ]
  refine (hδspec _ (fun v => ?_) ⟨u, hu⟩).le
  rw [abs_sub_lt_iff]
  have h1 := gridRound_ge (anchor D B hW) hdpos (fixedPointSub T past D B hB hW) v
  have h2 := gridRound_le (anchor D B hW) hdpos (fixedPointSub T past D B hB hW) hmem.1 hmem.2 v
  have h3 : (Fintype.card ↥(worldsOf D B) : ℝ) / d ≤ c / d :=
    div_le_div_of_nonneg_right (by rw [hc]; linarith) hdr.le
  have h4 : (1 : ℝ) / d ≤ c / d :=
    div_le_div_of_nonneg_right (by rw [hc]; linarith [(Nat.cast_nonneg (Fintype.card ↥(worldsOf D B)) : (0:ℝ) ≤ _)]) hdr.le
  constructor <;> linarith

/-- **T2(a). Coherent acceptance is satisfiable**: for every `ε > 0` there is a world measure
accepted at `ε` on `S ⊇ mentionedSet T`.
Source: [[bli-coherent-mm-mandate]] T2(a); [[bli-program]] §4 row M2
Kind: P
Fidelity: exact
Hyps: (a) `hS`, `hε`, `hB`, `hW` — all discharged by the mesh search -/
theorem exists_coherentAccepts (S : Finset Sentence) (hS : mentionedSet T ⊆ S) {ε : ℚ}
    (hε : 0 < ε) :
    ∃ w : FiniteWorld B → ℚ, IsWorldMeasure D B w ∧ CoherentAccepts T past D B S ε w := by
  obtain ⟨d, _, hmeas, hacc⟩ := exists_meshAccepted T past D B hB hW S hS hε
  exact ⟨_, hmeas, hacc⟩

/-- **D4. The accepted mesh**: the first mesh (by `Nat.find`, as FAF's `marketMakerIndex`) whose
rounded fixed point is accepted at `ε` on `S`.
Source: [[bli-coherent-mm-mandate]] D4 (angle B)
Kind: D
Fidelity: exact -/
noncomputable def coherentMesh (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ)
    (hε : 0 < ε) : ℕ :=
  Nat.find (exists_meshAccepted T past D B hB hW S hS hε)

/-- **D4 (definition of record). The coherent weights**: the fixed point rounded at the accepted
mesh — the day-`n` *world measure* (B3's customer object).
Source: [[bli-coherent-mm-mandate]] D4 (`coherentWeights`)
Kind: D
Fidelity: exact -/
noncomputable def coherentWeights (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ)
    (hε : 0 < ε) : FiniteWorld B → ℚ :=
  meshCandidate T past D B hB hW (coherentMesh T past D B hB hW S hS ε hε)

/-- **D4 (definition of record). The coherent market maker**: the candidate state of the
coherent weights on `S`. Noncomputable (a `Nat.find` on `exists_meshAccepted`), as FAF's
`MarketMaker` is; not FAF's `MarketMaker` (that is a `Nat.find` over rational belief states
checked against all Boolean support tables — T4(a) shows the two disagree on `T_pair`).
Source: [[bli-coherent-mm-mandate]] D4; Soto PDF 05 Def 8 ("approximate the fixed point")
Kind: D
Fidelity: exact -/
noncomputable def coherentMarketMaker (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ)
    (hε : 0 < ε) : RationalBeliefState :=
  ofWeights S (coherentWeights T past D B hB hW S hS ε hε)

variable (S : Finset Sentence) (hS : mentionedSet T ⊆ S) (ε : ℚ) (hε : 0 < ε)

/-- The accepted mesh is accepted.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coherentMesh_spec : MeshAccepted T past D B hB hW S ε (coherentMesh T past D B hB hW S hS ε hε) :=
  Nat.find_spec (exists_meshAccepted T past D B hB hW S hS hε)

/-- The accepted mesh is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coherentMesh_pos : 0 < coherentMesh T past D B hB hW S hS ε hε :=
  (coherentMesh_spec T past D B hB hW S hS ε hε).1

/-- **T2(b). The coherent weights are a world measure.**
Source: [[bli-coherent-mm-mandate]] T2(b) (`coherentMarketMaker_isWorldMeasure`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem coherentWeights_isWorldMeasure :
    IsWorldMeasure D B (coherentWeights T past D B hB hW S hS ε hε) :=
  (coherentMesh_spec T past D B hB hW S hS ε hε).2.1

/-- **T2(b). The coherent market maker is coherently accepted** at `ε` in every `D`-consistent
world (the `Nat.find` specification).
Source: [[bli-coherent-mm-mandate]] T2(b) (`coherentMarketMaker_accepts`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem coherentMarketMaker_accepts :
    CoherentAccepts T past D B S ε (coherentWeights T past D B hB hW S hS ε hε) :=
  (coherentMesh_spec T past D B hB hW S hS ε hε).2.2

/-- **T2(b). The maker's quote is the marginal of its weights** on `S`.
Source: [[bli-coherent-mm-mandate]] D4 (`coherentMarketMaker_quote_eq_pi`)
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_quote_eq_pi {φ : Sentence} (hφ : φ ∈ S) :
    (coherentMarketMaker T past D B hB hW S hS ε hε).quote φ =
      piTable (coherentWeights T past D B hB hW S hS ε hε) φ :=
  ofWeights_quote_of_mem (coherentWeights_isWorldMeasure T past D B hB hW S hS ε hε) hφ

/-- The maker quotes `0` off `S`.
Source: [[bli-coherent-mm-mandate]] D2
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_quote_of_not_mem {φ : Sentence} (hφ : φ ∉ S) :
    (coherentMarketMaker T past D B hB hW S hS ε hε).quote φ = 0 :=
  ofWeights_quote_of_not_mem _ hφ

/-- **T2(b). The coherent market maker's table is a world marginal on `S`**: the extended table
`piTable coherentWeights` is `IsWorldMarginal … S D B` (on the whole Boolean algebra generated
by `S`), and the maker's quote *is* that table on `S`. (The quote itself is `0` off `S`, so the
quote is not a marginal on compound sentences outside `S` — the marginal form is stated for the
extended table, the coherence-on-`S` form is `coherentMarketMaker_coherentOn`.)
Source: [[bli-coherent-mm-mandate]] T2(b) (`coherentMarketMaker_coherent`); [[bli-program]] §4 M2
Kind: C
Fidelity: variant: `IsWorldMarginal` of the extended table `piTable w`, plus quote = table on
`S` (the literal `IsWorldMarginal quote S D B` is false off `S`, see the report)
Hyps: (a) -/
theorem coherentMarketMaker_coherent :
    IsWorldMarginal (piTable (coherentWeights T past D B hB hW S hS ε hε)) S D B ∧
      ∀ φ ∈ S, (coherentMarketMaker T past D B hB hW S hS ε hε).quote φ =
        piTable (coherentWeights T past D B hB hW S hS ε hε) φ :=
  ⟨piTable_isWorldMarginal (coherentWeights_isWorldMeasure T past D B hB hW S hS ε hε) S,
    fun _ hφ => coherentMarketMaker_quote_eq_pi T past D B hB hW S hS ε hε hφ⟩

/-- The constant small index with day set `S` (so bli-finite's `CoherentOn` can be stated for
the day-`n` table restricted to `S`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def constIndex (S : Finset Sentence) : SmallIndex := ⟨fun _ => S, fun _ => Finset.Subset.refl S⟩

/-- **T2(b), `CoherentOn` form.** The maker's quote, as a day-`n` table over `S`, is
`CoherentOn … D B` in bli-finite's sense (a marginal of a `D`-consistent world measure on `S`).
Source: [[bli-coherent-mm-mandate]] T2(b) ("the `CoherentOn` form over a `SmallIndex`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem coherentMarketMaker_coherentOn :
    CoherentOn (𝒮 := constIndex S) (m := n)
      (fun φ => (coherentMarketMaker T past D B hB hW S hS ε hε).quote φ.1) D B := by
  have hw := coherentWeights_isWorldMeasure T past D B hB hW S hS ε hε
  exact ⟨_, hw.1, hw.2.1, hw.2.2, fun φ =>
    coherentMarketMaker_quote_eq_pi T past D B hB hW S hS ε hε φ.2⟩

/-- **T2(b), two-axiom form.** The extended table satisfies Appendix B's two coherence axioms
plus non-negativity on `GenBy S`, relative to `D` (bli-finite's `twoAxiom_of_worldMarginal`).
Source: [[bli-coherent-mm-mandate]] T2(b); bli-paper-030
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem coherentMarketMaker_twoAxiom :
    TwoAxiomCoherent (piTable (coherentWeights T past D B hB hW S hS ε hε)) S D :=
  twoAxiom_of_worldMarginal (coherentMarketMaker_coherent T past D B hB hW S hS ε hε).1

/-- **The grid shape** (B3's `coherentGrid` candidate): every coherent weight is a multiple of
`1 / coherentMesh`.
Source: [[bli-coherent-mm-mandate]] §Attempt angles (B) ("bli-finite's `worldWeights`/`coherentGrid` shape")
Kind: L
Fidelity: exact -/
theorem coherentWeights_mem_grid (u : FiniteWorld B) :
    ∃ k : ℕ, coherentWeights T past D B hB hW S hS ε hε u =
      (k : ℚ) / coherentMesh T past D B hB hW S hS ε hε := by
  unfold coherentWeights meshCandidate extWeightsQ
  split_ifs
  · exact gridRound_mem_grid _ _ _ _
  · exact ⟨0, by simp⟩

/-! ## T2(c): the maker respects the stage -/

/-- **T2(c). The maker respects the stage** (Soto's Def 3): a sentence of `S` true in every
`D`-consistent world is quoted `1` — a consequence of being a marginal over `D`-consistent
worlds, not an extra constraint (program §3.8).
Source: [[bli-coherent-mm-mandate]] T2(c); Soto PDF 05 Def 3; [[bli-program]] §3.8
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_respects {φ : Sentence} (hφ : φ ∈ S)
    (h : ∀ v : PCWorld, v.ConsistentWith D → v.Holds φ) :
    (coherentMarketMaker T past D B hB hW S hS ε hε).quote φ = 1 := by
  rw [coherentMarketMaker_quote_eq_pi T past D B hB hW S hS ε hε hφ]
  exact piTable_eq_one_of_decided (coherentWeights_isWorldMeasure T past D B hB hW S hS ε hε) h

/-- **T2(c), dual.** A sentence of `S` false in every `D`-consistent world is quoted `0`.
Source: [[bli-coherent-mm-mandate]] T2(c)
Kind: L
Fidelity: exact -/
theorem coherentMarketMaker_respects_false {φ : Sentence} (hφ : φ ∈ S)
    (h : ∀ v : PCWorld, v.ConsistentWith D → ¬ v.Holds φ) :
    (coherentMarketMaker T past D B hB hW S hS ε hε).quote φ = 0 := by
  rw [coherentMarketMaker_quote_eq_pi T past D B hB hW S hS ε hε hφ]
  exact piTable_eq_zero_of_decided_false
    (coherentWeights_isWorldMeasure T past D B hB hW S hS ε hε) h

end Maker

/-! ## T2(d): the customer's entry point -/

/-- **T2(d). The customer's entry point** (the coherent twin of `bli-overlay`'s
`dayValue_le_of_accepted_state`, whose all-Boolean-tables hypothesis a coherent maker cannot
meet). Coherent acceptance of `w` at `ε` bounds `T`'s value by `ε`, **in every `PCWorld`
consistent with `D`**, on any real history `P` agreeing with the candidate history on every cell
`T` mentions (days `≤ n`). Needs the atom bound (to restrict the world) but not that `w` is a
measure.
Source: [[bli-coherent-mm-mandate]] T2(d); [[bli-overlay-mandate]] T3(b)
Kind: L
Fidelity: exact
Hyps: (a) `hB`; `hagree` is what "the strategy evaluated on the history itself" means -/
theorem dayValue_le_of_coherentAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (D : Finset Sentence) (B : ℕ) (S : Finset Sentence) (ε : ℚ) (w : FiniteWorld B → ℚ)
    (hB : ∀ φ ∈ mentionedSet T ∪ D, atomBound φ ≤ B)
    (hacc : CoherentAccepts T past D B S ε w) (P : History)
    (hagree : ∀ φ, MentionedBy T φ → ∀ k ≤ n,
      P k φ = (candidateRationalHistory past n (ofWeights S w) k φ : ℝ)) :
    ∀ v : PCWorld, v.ConsistentWith D → T.value P v.payout ≤ (ε : ℝ) := by
  intro v hv
  have hmem := restrict_mem_worldsOf (fun φ hφ => hB φ (Finset.mem_union_right _ hφ)) hv
  have hrat := hacc.2 _ hmem
  have hcast : T.value (fun d φ => (candidateRationalHistory past n (ofWeights S w) d φ : ℝ))
      (worldOf (FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B)).payout =
      (T.marketValueRat (candidateRationalHistory past n (ofWeights S w))
        (fun φ => (FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B).payoutRat φ) : ℝ) :=
    Strategy.value_eq_marketRatCast T _ _ (fun _ _ => rfl) _ _
      (fun φ => payout_eq_cast_payoutRat _ φ)
  have h1 : T.value (fun d φ => (candidateRationalHistory past n (ofWeights S w) d φ : ℝ))
      (worldOf (FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) B)).payout ≤ (ε : ℝ) := by
    rw [hcast]
    exact_mod_cast hrat
  rw [value_restrict_eq T _ (atomBound_support_le hB) v] at h1
  rw [Cleanroom.Bli.BliOverlay.Strategy.value_eq_of_eqOn_mentioned T P _ v.payout
    (fun φ hφ k hk => hagree φ hφ k hk)]
  exact h1

/-! ## T2(e): the `smallSet` variant -/

/-- **T2(e). The coherent market maker on `S = smallSet n`** (the plan's "coherence on all of
`smallSet n`"): the same maker at the day's small sentences. Its existence is T2(a) verbatim;
only the cost of the enumeration (`2^B` worlds over the atoms of `smallSet n`) is a
computability/complexity question (Known issue 4). Needs `mentionedSet T ⊆ smallSet n` (F2 for
the firm from `N₀` on).
Source: [[bli-coherent-mm-mandate]] T2(e); [[bli-program]] §2.7
Kind: D
Fidelity: exact -/
noncomputable abbrev coherentMarketMakerSmall {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (D : Finset Sentence) (B : ℕ)
    (hB : ∀ φ ∈ mentionedSet T ∪ smallSet n ∪ D, atomBound φ ≤ B)
    (hW : ∃ u : FiniteWorld B, (worldOf u).ConsistentWith D)
    (hS : mentionedSet T ⊆ smallSet n) (ε : ℚ) (hε : 0 < ε) : RationalBeliefState :=
  coherentMarketMaker T past D B
    (fun φ hφ => hB φ (by
      rcases Finset.mem_union.mp hφ with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_right _ h)) hW (smallSet n) hS ε hε

end

end Cleanroom.Bli.BliCoherentMm.AttemptB
