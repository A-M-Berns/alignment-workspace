import Cleanroom.Bli.BliCoherentMm.Maker
import Cleanroom.Bli.BliCoherentMm.Waived
import Cleanroom.Bli.BliCoherentMm.AttemptA.Recursion
import Cleanroom.Bli.BliCoherentMm.AttemptB.Recursion

/-!
# `bli-coherent-mm` · Recursion (reconciled): D5 the propositionally coherent overlaid market, T6

**The construction-facing file** (plan §0.5). **D5 of record: attempt A's recursion** `pcRec`
— `bli-overlay`'s restricted-past pattern with the **interior coherent market maker** in place
of FAF's `MarketMaker`: on day `n` the firm is built from the coherent overlaid table of the
days `< n` (`pcFirmStrat`, never from `liaStates`), the maker runs on that firm against the
restricted past at stage `DP.D n`, atom bound `B n = (S n ∪ DP.D n).sup atomBound + 1` and
tolerance `marketMakerError n`, on the **priced set** `S n = mentionedSet (pcFirmStrat n) ∪ X n`
— parametric in `X`: the record instance is `X = noX` (`∅` every day, the mandate's D5), the
`smallSet` variant is `X = smallSet` (T2(e), `pcOverlaySmall_coherent`). On a day whose stage
has no consistent world over the day's atoms (FAF's `DeductiveProcess` has no consistency
field) the core is a fixed fallback; every stage-relative statement about such a day is vacuous.

Why attempt A's: attempt B's recursion is the same construction with attempt B's (grid)
interior maker and the priced set fixed to the mentioned set; A's is parametric in the priced
set (so the `smallSet` variant is an instance, not a second file) and states `D_PC_mentioned`
in `bli-found`'s shape. The two recursions are **different markets** (the makers choose
different candidates), so there is no state-level cross-check as in `bli-overlay`; the
cross-check here is at the level of the headlines: attempt B's recursion is kept as the **grid
variant** (`pcHistoryGrid`), its two headlines are restated over the record's vocabulary, and
**both recursions inhabit the record's `PCInductor`** (`pcInductor`, `pcInductorGrid`).

Headlines (T6, M3): `pcOverlay_no_ec_trader_exploits` (no efficiently computable trader
exploits the coherent overlaid market, every `DP`, `ov`, `X`), `pcOverlay_coherent_mentioned`
(exactly coherent on the priced set on every day whose stage has a consistent world),
non-dogmatism, monotonicity on decided sentences, `D_PC_mentioned`. **`ComputableMarket` is
open**: the assembly lemma assumes it, `PCInductor` has no computability field, and nothing in
this package or its dependents may cite `pcHistory` as a logical inductor.

Sources: [[bli-coherent-mm-mandate]] D5, T6; [[bli-program]] §2.7, §3.3, §3.8, §4 row M3,
§7 items 3 and 8.
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## D5: the recursion of record -/

/-- The record's priced-set parameter: nothing beyond the firm's mentioned set (`X n = ∅`).
Source: [[bli-coherent-mm-mandate]] D5 ("the set of record is `mentionedSet n`")
Kind: D
Fidelity: exact -/
abbrev noX : ℕ → Finset Sentence := fun _ => ∅

section Record

variable (DP : DeductiveProcess) (ov : Overlay) (X : ℕ → Finset Sentence)

/-- **D5 (of record). The coherent overlaid recursion**: one `PCDayRecord` per day (core state,
atom bound, core weights, overlaid quote with its range), well-founded on the day.
Source: [[bli-coherent-mm-mandate]] D5; [[bli-program]] §3.3 (ii), §3.8
Kind: D
Fidelity: exact -/
noncomputable abbrev pcRec : ℕ → AttemptA.PCDayRecord := AttemptA.pcRec DP ov X

/-- **The core state** of day `n` (the interior maker's output, or the fallback).
Source: [[bli-coherent-mm-mandate]] D5 (`pcCoreState`)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcCoreState (n : ℕ) : RationalBeliefState := AttemptA.pcCoreState DP ov X n

/-- **The day-`n` atom bound** `B n`.
Source: [[bli-coherent-mm-mandate]] D5 (`B n`)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcAtoms (n : ℕ) : ℕ := AttemptA.pcAtoms DP ov X n

/-- **The core's world measure** of day `n` (exposed: `bli-measure` needs the measure, not only
its marginal).
Source: [[bli-coherent-mm-mandate]] D5 (`pcCoreWeights`)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcCoreWeights (n : ℕ) : FiniteWorld (pcAtoms DP ov X n) → ℚ :=
  AttemptA.pcCoreWeights DP ov X n

/-- **The coherent overlaid table**: the core quote on the day's priced set, the overlay
elsewhere.
Source: [[bli-coherent-mm-mandate]] D5 (`pcQuote`)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcQuote : ℕ → Sentence → ℚ := AttemptA.pcQuote DP ov X

/-- **The coherent overlaid market**: the real history obtained by casting `pcQuote`.
Source: [[bli-coherent-mm-mandate]] D5 (`pcHistory`)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcHistory : History := AttemptA.pcHistory DP ov X

/-- **The firm's day-`n` strategy**: the trading firm built from the coherent overlaid table
(`pcFirmStrat_eq`: the strategy `tradingFirmTrader DP (pcQuote DP ov X)` plays on day `n`).
Source: [[bli-coherent-mm-mandate]] D5 (`pcFirmStrat`); [[bli-program]] §7 item 3
Kind: D
Fidelity: exact -/
noncomputable abbrev pcFirmStrat (n : ℕ) : Strategy n := AttemptA.pcFirmStrat DP ov X n

/-- **The day's priced set** `S n = mentionedSet (pcFirmStrat n) ∪ X n`.
Source: [[bli-coherent-mm-mandate]] D5
Kind: D
Fidelity: exact -/
noncomputable abbrev pcSet (n : ℕ) : Finset Sentence := AttemptA.pcSet DP ov X n

/-- `pcQuote` is in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pcQuote_range : ∀ k φ, 0 ≤ pcQuote DP ov X k φ ∧ pcQuote DP ov X k φ ≤ 1 :=
  AttemptA.pcQuote_range DP ov X

/-- The `def:market` range clause for the coherent overlaid market (no clamp).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pcHistory_range : ∀ day φ, 0 ≤ pcHistory DP ov X day φ ∧ pcHistory DP ov X day φ ≤ 1 :=
  AttemptA.pcHistory_range DP ov X

/-- The recursion's firm strategy is the static firm's day-`n` strategy (the wrong-market guard).
Source: [[bli-coherent-mm-mandate]] T6; [[bli-program]] §7 item 3
Kind: L
Fidelity: exact -/
theorem pcFirmStrat_eq (n : ℕ) :
    pcFirmStrat DP ov X n = (tradingFirmTrader DP (pcQuote DP ov X)).strat n :=
  AttemptA.pcFirmStrat_eq DP ov X n

/-- `B n = (S n ∪ DP.D n).sup atomBound + 1`.
Source: [[bli-coherent-mm-mandate]] D5 (`B n`)
Kind: L
Fidelity: exact -/
theorem pcAtoms_eq_sup (n : ℕ) :
    pcAtoms DP ov X n = (pcSet DP ov X n ∪ DP.D n).sup atomBound + 1 :=
  AttemptA.pcAtoms_eq_sup DP ov X n

/-- Every priced and every stage sentence is within the day's atom bound (`hB`, discharged).
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: n/a -/
theorem pcAtoms_bound (n : ℕ) : ∀ φ ∈ pcSet DP ov X n ∪ DP.D n, atomBound φ ≤ pcAtoms DP ov X n :=
  AttemptA.pcAtoms_bound DP ov X n

/-- On the priced set the overlaid quote is the core quote.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
theorem pcQuote_of_mem (n : ℕ) {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n) :
    pcQuote DP ov X n φ = (pcCoreState DP ov X n).quote φ :=
  AttemptA.pcQuote_of_mem DP ov X n hφ

/-- Off the priced set the overlaid quote is the overlay.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
theorem pcQuote_of_not_mem (n : ℕ) {φ : Sentence} (hφ : φ ∉ pcSet DP ov X n) :
    pcQuote DP ov X n φ =
      ov.val n (List.ofFn fun i : Fin n => (pcRec DP ov X i).core) (pcCoreState DP ov X n) φ :=
  AttemptA.pcQuote_of_not_mem DP ov X n hφ

/-- **The core state of a day whose stage has a consistent world is the interior coherent
market maker** on the day's firm against the restricted past (the recursion-to-record tie;
attempt A's day-level names).
Source: [[bli-coherent-mm-mandate]] T6 (`pcCoreState`)
Kind: L
Fidelity: exact -/
theorem pcCoreState_eq_interior (n : ℕ)
    (hW : ∃ u : FiniteWorld (AttemptA.pcDayAtoms DP X n (AttemptA.pcPrev DP ov X n)),
      (worldOf u).ConsistentWith (DP.D n)) :
    pcCoreState DP ov X n =
      interiorCoherentMarketMaker (AttemptA.pcDayStrat DP n (AttemptA.pcPrev DP ov X n))
        (AttemptA.pcPast DP ov X n) (DP.D n) (AttemptA.pcDayAtoms DP X n (AttemptA.pcPrev DP ov X n))
        (AttemptA.pcDaySet DP X n (AttemptA.pcPrev DP ov X n)) Finset.subset_union_left hW
        (marketMakerError_pos n) :=
  AttemptA.pcCoreState_eq_interior DP ov X n hW

/-! ## T6: no efficiently computable trader exploits the coherent overlaid market -/

/-- **T6, the day bound.** The firm's day-`n` strategy — built from and evaluated on the
coherent overlaid history — has value at most `marketMakerError n` **in every world consistent
with `DP.D n`** (T2(d) at the day's core, with agreement on the mentioned cells).
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_firm_dayValue_le`); [[bli-program]] §3.3 (i)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pcOverlay_firm_dayValue_le (n : ℕ) :
    ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (pcFirmStrat DP ov X n).value (pcHistory DP ov X) v.payout ≤ (marketMakerError n : ℝ) :=
  AttemptA.pcOverlay_firm_dayValue_le DP ov X n

/-- **T6. The firm does not exploit the coherent overlaid market** (T0 with `W = ∅`).
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_firm_not_exploited`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pcOverlay_firm_not_exploited :
    ¬ (tradingFirmTrader DP (pcQuote DP ov X)).Exploits (pcHistory DP ov X) DP :=
  AttemptA.pcOverlay_firm_not_exploited DP ov X

/-- **T6 (headline, M3, load-bearing). No efficiently computable trader exploits the coherent
overlaid market**, for every process `DP`, overlay `ov` and priced-set parameter `X` (FAF's
`trading_firm_dominance` on `pcOverlay_firm_not_exploited`). Scope: the `noExploit` half of the
criterion; **`ComputableMarket (pcHistory DP ov X)` is not established**.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_no_ec_trader_exploits`); [[bli-program]] §4 row M3
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance` is FAF's theorem, applied; `ov.range` is a field -/
theorem pcOverlay_no_ec_trader_exploits (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (pcHistory DP ov X) DP :=
  AttemptA.pcOverlay_no_ec_trader_exploits DP ov X Tr hTr

/-! ## T6: exact coherence on the priced set, every day -/

/-- **T6 (headline, M3, load-bearing). The coherent overlaid market is exactly coherent on its
priced set every day**: on a day `n` whose stage has a consistent world, `pcCoreWeights n` is a
world measure over `DP.D n` on `B n` atoms and the day-`n` quote of every
`φ ∈ pcSet n = mentionedSet (pcFirmStrat n) ∪ X n` is its marginal. Conditional on the stage:
FAF's `DeductiveProcess` admits stages with no consistent world (findings F8/F-B9), on which
nothing is coherent in the world-marginal sense and nothing is claimed.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_coherent_mentioned`); [[bli-program]] §4 row M3
Kind: C
Fidelity: variant: coherence as agreement with a world marginal on the priced set (F7),
conditional on the stage having a consistent world (F8)
Hyps: (a) `hcons` (the stage has a consistent `PCWorld`; from `paperDP_hworld` at the witness) -/
theorem pcOverlay_coherent_mentioned (n : ℕ) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsWorldMeasure (pcCoreWeights DP ov X n) (DP.D n) ∧
      ∀ φ ∈ pcSet DP ov X n, pcQuote DP ov X n φ = marginal (pcCoreWeights DP ov X n) φ :=
  AttemptA.pcOverlay_coherent_mentioned DP ov X n hcons

/-- The coherence headline in the `CoherentQuoteOn` form.
Source: [[bli-coherent-mm-mandate]] T6
Kind: L
Fidelity: as `pcOverlay_coherent_mentioned` -/
theorem pcOverlay_coherentQuoteOn (n : ℕ) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    CoherentQuoteOn (pcQuote DP ov X n) (pcSet DP ov X n) (DP.D n) (pcAtoms DP ov X n) :=
  AttemptA.pcOverlay_coherentQuoteOn DP ov X n hcons

/-- **`pcCoreState_quote_eq_pi`**: the core state quotes the exposed measure's marginal on the
priced set (on a day with a consistent world) — `bli-measure`'s entry point.
Source: [[bli-coherent-mm-mandate]] T6 (`pcCoreState_quote_eq_pi`)
Kind: L
Fidelity: exact -/
theorem pcCoreState_quote_eq_pi (n : ℕ) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n) :
    (pcCoreState DP ov X n).quote φ = marginal (pcCoreWeights DP ov X n) φ :=
  AttemptA.pcCoreState_quote_eq_pi DP ov X n hcons hφ

/-- The core's measure has full support on the stage's consistent worlds (on a day with a
consistent world).
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_nonDogmatic`)
Kind: L
Fidelity: exact -/
theorem pcCoreWeights_fullSupport (n : ℕ) (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ u ∈ WD (DP.D n) (pcAtoms DP ov X n), 0 < pcCoreWeights DP ov X n u :=
  AttemptA.pcCoreWeights_fullSupport DP ov X n hcons

/-- **T6. Non-dogmatism**: a priced sentence held by some world consistent with `DP.D n` and
refuted by another is quoted strictly inside `(0,1)` on day `n`.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_nonDogmatic`); T3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pcOverlay_nonDogmatic (n : ℕ) {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n)
    (h1 : ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ)
    (h2 : ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ) :
    0 < pcQuote DP ov X n φ ∧ pcQuote DP ov X n φ < 1 :=
  AttemptA.pcOverlay_nonDogmatic DP ov X n hφ h1 h2

/-- **T6. Monotone on decided sentences**: a sentence decided (true, resp. false) by `DP.D m`
is, on every later day `n ≥ m` with a consistent world on which it is priced, quoted `1`
(resp. `0`) — `DP.mono_le` plus T2(c).
Source: [[bli-coherent-mm-mandate]] T6 (`pcQuote_decided_monotone`)
Kind: C
Fidelity: exact
Hyps: (a) `hcons` -/
theorem pcQuote_decided_monotone {m n : ℕ} (hmn : m ≤ n)
    (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {φ : Sentence} (hφ : φ ∈ pcSet DP ov X n) :
    ((∀ v : PCWorld, v.ConsistentWith (DP.D m) → v.Holds φ) → pcQuote DP ov X n φ = 1) ∧
    ((∀ v : PCWorld, v.ConsistentWith (DP.D m) → ¬ v.Holds φ) → pcQuote DP ov X n φ = 0) :=
  ⟨fun h => AttemptA.pcQuote_decided_true DP ov X hmn hcons hφ h,
    fun h => AttemptA.pcQuote_decided_false DP ov X hmn hcons hφ h⟩

/-- **The assembly lemma (Kind L).** The coherent overlaid market is a logical inductor **if**
it is a computable market — `ComputableMarket` is **assumed**, as in FAF's
`lia_isLogicalInductor_of_computableMarket`; nothing in this package establishes it. Ledger:
`partial: computability open`.
Source: [[bli-coherent-mm-mandate]] T6 (assembly); [[bli-program]] §7 item 8
Kind: L
Fidelity: weaker: `ComputableMarket (pcHistory DP ov X)` is a hypothesis, not proved
Hyps: (b) `hmarket : ComputableMarket (pcHistory DP ov X)` — assumed (open); (a) `hDP` -/
theorem pcOverlay_isLogicalInductor_of_computableMarket (hDP : ComputableDeductiveProcess DP)
    (hmarket : ComputableMarket (pcHistory DP ov X)) : IsLogicalInductor (pcHistory DP ov X) DP :=
  AttemptA.pcOverlay_isLogicalInductor_of_computableMarket DP ov X hDP hmarket

end Record

/-! ## `D_PC` on the mentioned set -/

/-- **`D_PC_mentioned`**: a rational table is, on every day, the marginal on the day's firm's
mentioned set of a finite mixture of `PCWorld`s consistent with the stage — `bli-found`'s
`CoherentOn` witness shape, restricted from "all sentences within an atom set" to the mentioned
sentences. `D_PC` of record (over all of `smallSet n`'s sentences) is **not** established; the
gap is the quantifier over sentences.
Source: [[bli-coherent-mm-mandate]] T6 (`D_PC_mentioned`); bli-found `D_PC`
Kind: D
Fidelity: variant: mentioned set in place of `smallSet n`'s atom closure -/
abbrev D_PC_mentioned (Q : ℕ → Sentence → ℚ) (DP : DeductiveProcess) : Prop :=
  AttemptA.D_PC_mentioned Q DP

/-- **T6. The coherent overlaid table satisfies `D_PC_mentioned`** whenever every stage has a
consistent world.
Source: [[bli-coherent-mm-mandate]] T6 (`D_PC_mentioned`)
Kind: C
Fidelity: variant: mentioned set (see `D_PC_mentioned`)
Hyps: (a) `hcons` -/
theorem pcOverlay_D_PC_mentioned (DP : DeductiveProcess) (ov : Overlay) (X : ℕ → Finset Sentence)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    D_PC_mentioned (pcQuote DP ov X) DP :=
  AttemptA.pcOverlay_D_PC_mentioned DP ov X hcons

/-! ## `PCInductor` -/

/-- **D5 (of record). A propositionally coherent inductor** (modulo computability) over `DP`: an
exactly rational `[0,1]` table that is, every day, the marginal on its own firm's mentioned set
of a world measure over the day's stage (within an atom bound), and that no efficiently
computable trader exploits. **`marketComputable` is not a field**: it is the separate open
predicate `ComputableMarket`; an inhabitant is **not** a logical inductor.
Source: [[bli-coherent-mm-mandate]] D5; [[bli-program]] §2.7, §7 item 8
Kind: D
Fidelity: variant: `coh` as agreement with a world marginal on the mentioned set; no `li` field -/
abbrev PCInductor (DP : DeductiveProcess) := AttemptA.PCInductor DP

/-- **T6. `PCInductor DP` is inhabited** by the coherent overlaid recursion, for every overlay
and priced-set parameter, whenever every stage of `DP` has a consistent world. Ledger:
"inhabited; `ComputableMarket` open".
Source: [[bli-coherent-mm-mandate]] T6 (`PCInductor`); [[bli-program]] §4 row M3
Kind: C
Fidelity: variant: as `PCInductor`
Hyps: (a) `hcons` (every stage has a consistent `PCWorld`; `paperDP_hworld` at the witness) -/
noncomputable abbrev pcInductor (DP : DeductiveProcess) (ov : Overlay) (X : ℕ → Finset Sentence)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : PCInductor DP :=
  AttemptA.pcInductor DP ov X hcons

/-- The inhabitant's table is the recursion's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pcInductor_Q (DP : DeductiveProcess) (ov : Overlay) (X : ℕ → Finset Sentence)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (pcInductor DP ov X hcons).Q = pcQuote DP ov X :=
  rfl

/-- **The `smallSet` variant (T2(e), `pcOverlaySmall`)**: with `X = smallSet` the recursion is
coherent on all of `smallSet n` every day (an instance of the record theorem).
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlaySmall`), T2(e)
Kind: C
Fidelity: exact (instance)
Hyps: (a) `hcons` -/
theorem pcOverlaySmall_coherent (DP : DeductiveProcess) (ov : Overlay) (n : ℕ)
    (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsWorldMeasure (pcCoreWeights DP ov smallSet n) (DP.D n) ∧
      ∀ φ ∈ smallSet n, pcQuote DP ov smallSet n φ = marginal (pcCoreWeights DP ov smallSet n) φ :=
  AttemptA.pcOverlaySmall_coherent DP ov n hcons

/-! ## The grid variant: attempt B's recursion (the grid interior maker, priced set the
mentioned set) -/

section Grid

variable (DP : DeductiveProcess) (ov : Overlay)

/-- **The grid coherent overlaid table** (attempt B's recursion: the grid interior maker on the
firm's mentioned set against the restricted past).
Source: [[bli-coherent-mm-mandate]] D5 (angle B)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcQuoteGrid : ℕ → Sentence → ℚ := AttemptB.pcQuote DP ov

/-- **The grid coherent overlaid market**.
Source: [[bli-coherent-mm-mandate]] D5 (angle B)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcHistoryGrid : History := AttemptB.pcHistory DP ov

/-- The grid recursion's day-`n` firm.
Source: [[bli-coherent-mm-mandate]] D5 (angle B)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcFirmStratGrid (n : ℕ) : Strategy n := AttemptB.pcFirmStrat DP ov n

/-- The grid recursion's day-`n` atom bound.
Source: [[bli-coherent-mm-mandate]] D5 (angle B)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcAtomsGrid (n : ℕ) : ℕ := AttemptB.pcB DP ov n

/-- The grid recursion's day-`n` core weights.
Source: [[bli-coherent-mm-mandate]] D5 (angle B)
Kind: D
Fidelity: exact -/
noncomputable abbrev pcCoreWeightsGrid (n : ℕ) : FiniteWorld (pcAtomsGrid DP ov n) → ℚ :=
  AttemptB.pcCoreWeights DP ov n

/-- **T6, grid variant: no efficiently computable trader exploits the grid coherent overlaid
market** (attempt B's headline, the same statement shape as the record's).
Source: [[bli-coherent-mm-mandate]] T6; §Deliverables (cross-check)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pcOverlayGrid_no_ec_trader_exploits :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (pcHistoryGrid DP ov) DP :=
  AttemptB.pcOverlay_no_ec_trader_exploits DP ov

/-- **T6, grid variant: exact coherence on the mentioned set** on every day whose stage has a
consistent world, in the record's vocabulary (attempt B's headline transported).
Source: [[bli-coherent-mm-mandate]] T6; §Deliverables (cross-check)
Kind: C
Fidelity: variant: as `pcOverlay_coherent_mentioned`
Hyps: (a) `hcons` -/
theorem pcOverlayGrid_coherent_mentioned (n : ℕ)
    (hcons : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsWorldMeasure (pcCoreWeightsGrid DP ov n) (DP.D n) ∧
      ∀ φ ∈ mentionedSet (pcFirmStratGrid DP ov n),
        pcQuoteGrid DP ov n φ = marginal (pcCoreWeightsGrid DP ov n) φ :=
  ⟨AttemptB.pcCoreWeights_isWorldMeasure DP ov n ((AttemptB.stageInhabited_iff DP ov n).mpr hcons),
    (AttemptB.pcOverlay_coherent_mentioned DP ov n hcons).2⟩

/-- **Both recursions inhabit the record's `PCInductor`**: attempt B's grid recursion is a
second inhabitant of `PCInductor DP` (the cross-check at the level of the structure; the two
markets differ, since the makers choose different candidates).
Source: [[bli-coherent-mm-mandate]] T6 (`PCInductor`); §Deliverables (cross-check)
Kind: C
Fidelity: variant: as `PCInductor`
Hyps: (a) `hcons` -/
noncomputable def pcInductorGrid (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    PCInductor DP where
  Q := pcQuoteGrid DP ov
  range := AttemptB.pcQuote_range DP ov
  coh n := ⟨pcAtomsGrid DP ov n, pcCoreWeightsGrid DP ov n,
    (pcOverlayGrid_coherent_mentioned DP ov n (hcons n)).1, AttemptB.pcB_spec DP ov n,
    (pcOverlayGrid_coherent_mentioned DP ov n (hcons n)).2⟩
  noExploit := AttemptB.pcOverlay_no_ec_trader_exploits DP ov

end Grid

end Cleanroom.Bli.BliCoherentMm
