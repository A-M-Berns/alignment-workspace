import Cleanroom.Bli.BliCoherentMm.AttemptB.Interior
import Cleanroom.Bli.BliCoherentMm.AttemptB.Waived

/-!
# `bli-coherent-mm` (attempt B) · Recursion: the propositionally coherent overlaid market and
`PCInductor` (D5, T6; construction-facing, M3)

`bli-overlay`'s recursion with the **interior coherent maker** in place of FAF's `MarketMaker`.
Per day `n`, from the previous records `prev : Fin n → DayRecord`:

* `pcStrat DP n prev := TradingFirmAt DP (prevTable n prev) n` — the firm **built from the
  coherent overlaid table** of the days `< n`;
* `pcAtomBound DP n prev := (mentionedSet (pcStrat …) ∪ DP.D n).sup atomBound + 1`;
* `pcPast` — the restricted past on the mentioned set (`bli-overlay`'s `restrictedPast`);
* `pcCore DP n prev` — the interior maker on the mentioned set against the restricted past at
  stage `DP.D n` and error `marketMakerError n`, **when the stage has a consistent world over
  `pcAtomBound` atoms**, else the empty state (FAF's `DeductiveProcess` has no consistency
  field; in that branch every stage-relative bound is vacuous, `not_stageInhabited_vacuous`);
* `pcStep` — the day quote: the core quote on the mentioned set, the overlay `ov` elsewhere.

Of record: `pcRec`, `pcCoreState`, `pcQuote`, `pcHistory`, `pcFirmStrat`, `pcB`,
`pcCoreWeights` (the day-`n` world measure, B3's object) with `pcCoreState_quote_eq_pi`.

Headlines (all over `D`-consistent worlds; `StageInhabited` ⇔ the stage has a consistent
`PCWorld`, `stageInhabited_iff`):
* `pcOverlay_firm_dayValue_le` — the firm's day-`n` value on the coherent overlaid history is
  `≤ marketMakerError n` in every world consistent with `DP.D n` (T2(d) + agreement on
  mentioned cells);
* `pcOverlay_firm_not_exploited` (T0 with `W = ∅`);
* **`pcOverlay_no_ec_trader_exploits`** — no efficiently computable trader exploits the coherent
  overlaid market (`trading_firm_dominance`);
* **`pcOverlay_coherent_mentioned`** — on every day whose stage is inhabited, the day table is
  the marginal of a `D`-consistent world measure on the day's mentioned set (`IsWorldMarginal` of
  the extended table; the `CoherentOn` form `pcOverlay_coherentOn`);
* `pcOverlay_nonDogmatic`, `pcQuote_decided_monotone`;
* `pcOverlay_isLogicalInductor_of_computableMarket` — **`ComputableMarket` assumed** (Kind L;
  ledger `partial: computability open`); `PCInductor DP` inhabited by `pcInductor DP ov`.

Nothing here makes the coherent overlaid market a logical inductor: `ComputableMarket
(pcHistory DP ov)` is open (program §7 item 8; the `noExploit`/`marketComputable` split).

Sources: [[bli-coherent-mm-mandate]] D5, T6; [[bli-program]] §2.7, §3.3, §4 row M3, §7
items 3/8; [[bli-overlay-report]] (the recursion pattern).
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptB

open LogicalInduction LogicalInduction.BoolPCWorld LO.Propositional Cleanroom.Bli.BliFound
  Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliFinite Finset
open Cleanroom.Bli.BliOverlay.AttemptA (DayRecord prevTable prevTable_range prevTable_of_lt
  restrictedPast rationalHistory_restrictedPast restrictedPast_congr)

noncomputable section

/-! ## D5: one day of the coherent recursion -/

/-- The fallback state (quote `0` everywhere), used only on a day whose stage has no consistent
world over the day's atoms.
Source: [[bli-coherent-mm-mandate]] T6 ("any fixed fallback state")
Kind: D
Fidelity: exact -/
def emptyState : RationalBeliefState := ⟨[], List.nodup_nil, fun _ h => by simp at h⟩

/-- **D5. The day-`n` firm strategy of the recursion**: the trading firm built from the coherent
overlaid table of the days `< n` (never from `liaStates`).
Source: [[bli-coherent-mm-mandate]] D5, T6; [[bli-program]] §7 item 3
Kind: D
Fidelity: exact -/
def pcStrat (DP : DeductiveProcess) (n : ℕ) (prev : Fin n → DayRecord) : Strategy n :=
  TradingFirmAt DP (prevTable n prev) n

/-- **D5. The day-`n` atom bound** `B n`: one above the largest atom bound over the mentioned
set and the stage.
Source: [[bli-coherent-mm-mandate]] D5
Kind: D
Fidelity: exact -/
def pcAtomBound (DP : DeductiveProcess) (n : ℕ) (prev : Fin n → DayRecord) : ℕ :=
  (mentionedSet (pcStrat DP n prev) ∪ DP.D n).sup atomBound + 1

/-- The day-`n` atom bound covers the mentioned set and the stage (`hB`, discharged).
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: n/a -/
lemma pcAtomBound_spec (DP : DeductiveProcess) (n : ℕ) (prev : Fin n → DayRecord) :
    ∀ φ ∈ mentionedSet (pcStrat DP n prev) ∪ DP.D n, atomBound φ ≤ pcAtomBound DP n prev :=
  fun _ hφ => le_trans (Finset.le_sup hφ) (Nat.le_succ _)

/-- **D5. The restricted past** fed to the maker on day `n`.
Source: [[bli-coherent-mm-mandate]] D5; [[bli-overlay-mandate]] §Attempt angles (A)
Kind: D
Fidelity: exact -/
def pcPast (DP : DeductiveProcess) (n : ℕ) (prev : Fin n → DayRecord) :
    List RationalBeliefState :=
  restrictedPast (mentionedSet (pcStrat DP n prev)) (prevTable n prev) (prevTable_range n prev) n

/-- **D5. The day-`n` core state**: the interior coherent maker on the mentioned set against
the restricted past, at stage `DP.D n` and error `marketMakerError n`, when the stage has a
consistent world over `pcAtomBound` atoms; the empty state otherwise.
Source: [[bli-coherent-mm-mandate]] D5, T6
Kind: D
Fidelity: exact -/
def pcCore (DP : DeductiveProcess) (n : ℕ) (prev : Fin n → DayRecord) : RationalBeliefState :=
  if hW : ∃ u : FiniteWorld (pcAtomBound DP n prev), (worldOf u).ConsistentWith (DP.D n) then
    interiorCoherentMarketMaker (pcStrat DP n prev) (pcPast DP n prev) (DP.D n)
      (pcAtomBound DP n prev) (pcAtomBound_spec DP n prev) hW (mentionedSet (pcStrat DP n prev))
      (Finset.Subset.refl _) (marketMakerError n) (marketMakerError_pos n)
  else emptyState

/-- **D5. The day-`n` core weights**: the interior maker's world measure (zero if the stage is
uninhabited).
Source: [[bli-coherent-mm-mandate]] D5 (`pcCoreWeights`)
Kind: D
Fidelity: exact -/
def pcCoreW (DP : DeductiveProcess) (n : ℕ) (prev : Fin n → DayRecord) :
    FiniteWorld (pcAtomBound DP n prev) → ℚ :=
  if hW : ∃ u : FiniteWorld (pcAtomBound DP n prev), (worldOf u).ConsistentWith (DP.D n) then
    interiorWeights (pcStrat DP n prev) (pcPast DP n prev) (DP.D n)
      (pcAtomBound DP n prev) (pcAtomBound_spec DP n prev) hW (mentionedSet (pcStrat DP n prev))
      (Finset.Subset.refl _) (marketMakerError n) (marketMakerError_pos n)
  else fun _ => 0

/-- One step of the coherent recursion: the core state, and the overlaid quote (core quote on
the mentioned set, `ov` elsewhere).
Source: [[bli-coherent-mm-mandate]] D5
Kind: D
Fidelity: exact -/
def pcStep (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (prev : Fin n → DayRecord) :
    DayRecord where
  core := pcCore DP n prev
  quote φ := if φ ∈ mentionedSet (pcStrat DP n prev) then (pcCore DP n prev).quote φ
    else ov.val n (List.ofFn fun i => (prev i).core) (pcCore DP n prev) φ
  range φ := by
    by_cases h : φ ∈ mentionedSet (pcStrat DP n prev)
    · rw [if_pos h]
      exact (pcCore DP n prev).quote_mem_Icc φ
    · rw [if_neg h]
      exact ov.range _ _ _ _

/-- **D5. The coherent overlaid recursion** (well-founded on the day).
Source: [[bli-coherent-mm-mandate]] D5; [[bli-program]] §3.3 (ii)
Kind: D
Fidelity: exact -/
def pcRec (DP : DeductiveProcess) (ov : Overlay) : ℕ → DayRecord
  | n => pcStep DP ov n (fun i : Fin n => pcRec DP ov i)
termination_by n => n
decreasing_by exact i.isLt

/-- **The core state** of day `n`.
Source: [[bli-coherent-mm-mandate]] D5 (`pcCoreState`)
Kind: D
Fidelity: exact -/
def pcCoreState (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : RationalBeliefState :=
  (pcRec DP ov n).core

/-- **The coherent overlaid table**.
Source: [[bli-coherent-mm-mandate]] D5 (`pcQuote`)
Kind: D
Fidelity: exact -/
def pcQuote (DP : DeductiveProcess) (ov : Overlay) : ℕ → Sentence → ℚ :=
  fun n φ => (pcRec DP ov n).quote φ

/-- **The coherent overlaid market**: the real history obtained by casting `pcQuote`.
Source: [[bli-coherent-mm-mandate]] D5 (`pcHistory`)
Kind: D
Fidelity: exact -/
def pcHistory (DP : DeductiveProcess) (ov : Overlay) : History :=
  fun n φ => (pcQuote DP ov n φ : ℝ)

/-- **The firm's day-`n` strategy**: the trading firm built from the coherent overlaid table.
Source: [[bli-coherent-mm-mandate]] D5 (`pcFirmStrat`)
Kind: D
Fidelity: exact -/
def pcFirmStrat (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : Strategy n :=
  TradingFirmAt DP (pcQuote DP ov) n

/-- **The day-`n` atom bound** of the recursion.
Source: [[bli-coherent-mm-mandate]] D5 (`B n`)
Kind: D
Fidelity: exact -/
abbrev pcB (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : ℕ :=
  pcAtomBound DP n (fun i : Fin n => pcRec DP ov i)

/-- **The day-`n` core weights** of the recursion (B3's world measure).
Source: [[bli-coherent-mm-mandate]] D5 (`pcCoreWeights`)
Kind: D
Fidelity: exact -/
def pcCoreWeights (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : FiniteWorld (pcB DP ov n) → ℚ :=
  pcCoreW DP n (fun i : Fin n => pcRec DP ov i)

/-- **The stage is inhabited** over the day's atoms: some finite world on `pcB n` atoms is
consistent with `DP.D n`.
Source: [[bli-coherent-mm-mandate]] T6 ("when `hW` holds")
Kind: D
Fidelity: exact -/
abbrev StageInhabited (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) : Prop :=
  ∃ u : FiniteWorld (pcB DP ov n), (worldOf u).ConsistentWith (DP.D n)

/-! ## The identities of D5 -/

/-- `pcQuote` is in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcQuote_range (DP : DeductiveProcess) (ov : Overlay) :
    ∀ k φ, 0 ≤ pcQuote DP ov k φ ∧ pcQuote DP ov k φ ≤ 1 :=
  fun k φ => (pcRec DP ov k).range φ

/-- `pcHistory` is a `[0,1]` history (the `def:market` range clause).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcHistory_range (DP : DeductiveProcess) (ov : Overlay) :
    ∀ day φ, 0 ≤ pcHistory DP ov day φ ∧ pcHistory DP ov day φ ≤ 1 := by
  intro d φ
  unfold pcHistory
  exact ⟨by exact_mod_cast (pcQuote_range DP ov d φ).1,
    by exact_mod_cast (pcQuote_range DP ov d φ).2⟩

/-- The real market is the cast of the exact rational table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcHistory_eq_quote_cast (DP : DeductiveProcess) (ov : Overlay) (day : ℕ) (φ : Sentence) :
    pcHistory DP ov day φ = (pcQuote DP ov day φ : ℝ) := rfl

/-- The recursion's equation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcRec_unfold (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    pcRec DP ov n = pcStep DP ov n (fun i : Fin n => pcRec DP ov i) := by
  rw [pcRec]

/-- The previous-records table is the coherent overlaid table on days `< n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prevTable_pcRec (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) {k : ℕ} (hk : k < n)
    (φ : Sentence) :
    prevTable n (fun i : Fin n => pcRec DP ov i) k φ = pcQuote DP ov k φ := by
  rw [prevTable_of_lt n _ hk]
  rfl

/-- **The recursion's day-`n` strategy is `pcFirmStrat`**: the firm reads only days `< n`
(FAF's `TradingFirmAt_eq_of_eq_prefix`).
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
lemma pcStrat_eq_firmStrat (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    pcStrat DP n (fun i : Fin n => pcRec DP ov i) = pcFirmStrat DP ov n := by
  unfold pcStrat pcFirmStrat
  apply TradingFirmAt_eq_of_eq_prefix
  intro k hk φ
  exact prevTable_pcRec DP ov n hk φ

/-- The day-`n` record's core, unfolded one step.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcRec_core (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    (pcRec DP ov n).core = pcCore DP n (fun i : Fin n => pcRec DP ov i) := by
  rw [pcRec_unfold]
  rfl

/-- The day-`n` record's quote, unfolded one step.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pcRec_quote (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (φ : Sentence) :
    (pcRec DP ov n).quote φ =
      if φ ∈ mentionedSet (pcStrat DP n (fun i : Fin n => pcRec DP ov i)) then
        (pcCore DP n (fun i : Fin n => pcRec DP ov i)).quote φ
      else ov.val n (List.ofFn fun i : Fin n => (pcRec DP ov i).core)
        (pcCore DP n (fun i : Fin n => pcRec DP ov i)) φ := by
  conv_lhs => rw [pcRec_unfold]
  rfl

/-- The coherent overlaid quote, as a case split on the mentioned set.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
lemma pcQuote_eq_ite (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (φ : Sentence) :
    pcQuote DP ov n φ =
      if φ ∈ mentionedSet (pcFirmStrat DP ov n) then (pcCoreState DP ov n).quote φ
      else ov.val n (List.ofFn fun i : Fin n => pcCoreState DP ov i) (pcCoreState DP ov n) φ := by
  unfold pcQuote
  rw [pcRec_quote, pcStrat_eq_firmStrat, ← pcRec_core]
  rfl

/-- On the mentioned set, the coherent overlaid quote is the core quote.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
lemma pcQuote_of_mem (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} {φ : Sentence}
    (h : φ ∈ mentionedSet (pcFirmStrat DP ov n)) :
    pcQuote DP ov n φ = (pcCoreState DP ov n).quote φ := by
  rw [pcQuote_eq_ite, if_pos h]

/-- Off the mentioned set, the coherent overlaid quote is the overlay.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
lemma pcQuote_of_not_mem (DP : DeductiveProcess) (ov : Overlay) {n : ℕ} {φ : Sentence}
    (h : φ ∉ mentionedSet (pcFirmStrat DP ov n)) :
    pcQuote DP ov n φ =
      ov.val n (List.ofFn fun i : Fin n => pcCoreState DP ov i) (pcCoreState DP ov n) φ := by
  rw [pcQuote_eq_ite, if_neg h]

/-- The day-`n` atom bound covers the firm's mentioned set and the stage.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: n/a -/
lemma pcB_spec (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    ∀ φ ∈ mentionedSet (pcFirmStrat DP ov n) ∪ DP.D n, atomBound φ ≤ pcB DP ov n := by
  rw [← pcStrat_eq_firmStrat]
  exact pcAtomBound_spec DP n _

/-- **The stage is inhabited iff it has a consistent `PCWorld`** (the atom bound covers `DP.D n`,
so a consistent `PCWorld` restricts to a consistent finite world, and a finite world is one).
Source: [[bli-coherent-mm-mandate]] T6
Kind: L
Fidelity: exact -/
theorem stageInhabited_iff (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    StageInhabited DP ov n ↔ ∃ v : PCWorld, v.ConsistentWith (DP.D n) := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨worldOf u, hu⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, mem_worldsOf.mp (restrict_mem_worldsOf
      (fun φ hφ => pcB_spec DP ov n φ (Finset.mem_union_right _ hφ)) hv)⟩

/-- On an uninhabited day, no `PCWorld` is consistent with the stage: every stage-relative
statement about that day is vacuous.
Source: [[bli-coherent-mm-mandate]] T6 ("in that branch every stage-relative bound is vacuous")
Kind: L
Fidelity: n/a -/
lemma not_stageInhabited_vacuous (DP : DeductiveProcess) (ov : Overlay) (n : ℕ)
    (h : ¬ StageInhabited DP ov n) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) : False :=
  h ((stageInhabited_iff DP ov n).mpr ⟨v, hv⟩)

/-! ## The core state and its weights on an inhabited day -/

section Inhabited

variable (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (hW : StageInhabited DP ov n)

/-- Membership in the firm's mentioned set, transported to the recursion's strategy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_mentionedSet_pcStrat {φ : Sentence} (h : φ ∈ mentionedSet (pcFirmStrat DP ov n)) :
    φ ∈ mentionedSet (pcStrat DP n (fun i : Fin n => pcRec DP ov i)) := by
  rw [pcStrat_eq_firmStrat]; exact h

include hW

/-- On an inhabited day the core state is the interior maker (the `dite` resolves).
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
lemma pcCoreState_eq :
    pcCoreState DP ov n = interiorCoherentMarketMaker (pcStrat DP n (fun i : Fin n => pcRec DP ov i))
      (pcPast DP n (fun i : Fin n => pcRec DP ov i)) (DP.D n) (pcB DP ov n)
      (pcAtomBound_spec DP n _) hW (mentionedSet (pcStrat DP n (fun i : Fin n => pcRec DP ov i)))
      (Finset.Subset.refl _) (marketMakerError n) (marketMakerError_pos n) := by
  unfold pcCoreState
  rw [pcRec_core]
  unfold pcCore
  rw [dif_pos hW]

/-- On an inhabited day the core weights are the interior weights.
Source: [[bli-coherent-mm-mandate]] D5
Kind: L
Fidelity: exact -/
lemma pcCoreWeights_eq :
    pcCoreWeights DP ov n = interiorWeights (pcStrat DP n (fun i : Fin n => pcRec DP ov i))
      (pcPast DP n (fun i : Fin n => pcRec DP ov i)) (DP.D n) (pcB DP ov n)
      (pcAtomBound_spec DP n _) hW (mentionedSet (pcStrat DP n (fun i : Fin n => pcRec DP ov i)))
      (Finset.Subset.refl _) (marketMakerError n) (marketMakerError_pos n) := by
  unfold pcCoreWeights pcCoreW
  rw [dif_pos hW]

/-- **The core weights are a `D`-consistent world measure** on an inhabited day.
Source: [[bli-coherent-mm-mandate]] T6 (`pcCoreWeights`)
Kind: C
Fidelity: exact
Hyps: (a) `hW` -/
theorem pcCoreWeights_isWorldMeasure : IsWorldMeasure (DP.D n) (pcB DP ov n) (pcCoreWeights DP ov n) := by
  rw [pcCoreWeights_eq DP ov n hW]
  exact interior_isWorldMeasure _ _ _ _ _ _ _ _ _ _

/-- **Full support** of the core weights on the `D`-consistent worlds.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_nonDogmatic`)
Kind: C
Fidelity: exact
Hyps: (a) `hW` -/
theorem pcCoreWeights_fullSupport :
    ∀ u ∈ worldsOf (DP.D n) (pcB DP ov n), 0 < pcCoreWeights DP ov n u := by
  rw [pcCoreWeights_eq DP ov n hW]
  exact interior_fullSupport _ _ _ _ _ _ _ _ _ _

/-- **`pcCoreState_quote_eq_pi`**: on the mentioned set, the core quote is the marginal of the
core weights.
Source: [[bli-coherent-mm-mandate]] D5, T6 (`pcCoreState_quote_eq_pi`)
Kind: L
Fidelity: exact -/
theorem pcCoreState_quote_eq_pi {φ : Sentence} (hφ : φ ∈ mentionedSet (pcFirmStrat DP ov n)) :
    (pcCoreState DP ov n).quote φ = piTable (pcCoreWeights DP ov n) φ := by
  rw [pcCoreState_eq DP ov n hW, pcCoreWeights_eq DP ov n hW]
  exact interior_quote_eq_pi _ _ _ _ _ _ _ _ _ _ (mem_mentionedSet_pcStrat DP ov n hφ)

/-- On the mentioned set, the coherent overlaid quote is the marginal of the core weights.
Source: [[bli-coherent-mm-mandate]] T6
Kind: L
Fidelity: exact -/
theorem pcQuote_eq_pi {φ : Sentence} (hφ : φ ∈ mentionedSet (pcFirmStrat DP ov n)) :
    pcQuote DP ov n φ = piTable (pcCoreWeights DP ov n) φ := by
  rw [pcQuote_of_mem DP ov hφ]
  exact pcCoreState_quote_eq_pi DP ov n hW hφ

/-- The core weights are coherently accepted by the recursion's strategy against the restricted
past at `marketMakerError n`.
Source: [[bli-coherent-mm-mandate]] T6
Kind: L
Fidelity: exact -/
theorem pcCoreWeights_accepts :
    CoherentAccepts (pcStrat DP n (fun i : Fin n => pcRec DP ov i))
      (pcPast DP n (fun i : Fin n => pcRec DP ov i)) (DP.D n) (pcB DP ov n)
      (mentionedSet (pcStrat DP n (fun i : Fin n => pcRec DP ov i))) (marketMakerError n)
      (pcCoreWeights DP ov n) := by
  rw [pcCoreWeights_eq DP ov n hW]
  exact interior_accepts _ _ _ _ _ _ _ _ _ _

end Inhabited

/-! ## T6: the coherent overlaid market is exploited by no e.c. trader -/

/-- **T6, the day bound.** The firm's day-`n` strategy has value at most `marketMakerError n`
on the coherent overlaid history in every world consistent with `DP.D n`: on an inhabited day,
T2(d) for the core weights plus agreement on mentioned cells (days `< n` by the restriction,
day `n` because the overlaid quote is the core quote on the mentioned set); on an uninhabited
day there is no such world.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_firm_dayValue_le`)
Kind: C
Fidelity: exact (over `DP.D n`-consistent worlds)
Hyps: (a) -/
theorem pcOverlay_firm_dayValue_le (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) :
    ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      (pcFirmStrat DP ov n).value (pcHistory DP ov) v.payout ≤ (marketMakerError n : ℝ) := by
  intro v hv
  by_cases hW : StageInhabited DP ov n
  · have h := dayValue_le_of_coherentAccepts (pcStrat DP n (fun i : Fin n => pcRec DP ov i))
      (pcPast DP n (fun i : Fin n => pcRec DP ov i)) (DP.D n) (pcB DP ov n)
      (mentionedSet (pcStrat DP n (fun i : Fin n => pcRec DP ov i))) (marketMakerError n)
      (pcCoreWeights DP ov n) (pcAtomBound_spec DP n _) (pcCoreWeights_accepts DP ov n hW)
      (pcHistory DP ov) ?_ v hv
    · rwa [pcStrat_eq_firmStrat] at h
    · intro φ hφ k hk
      rw [pcHistory_eq_quote_cast]
      congr 1
      have hφ' : φ ∈ mentionedSet (pcFirmStrat DP ov n) := by
        rw [← pcStrat_eq_firmStrat]; exact mem_mentionedSet_iff.mpr hφ
      rcases Nat.lt_or_eq_of_le hk with hlt | rfl
      · rw [candidateRationalHistory, Function.update_of_ne (Nat.ne_of_lt hlt)]
        unfold pcPast
        rw [rationalHistory_restrictedPast hlt (mem_mentionedSet_iff.mpr hφ)]
        exact (prevTable_pcRec DP ov n hlt φ).symm
      · rw [candidateRationalHistory, Function.update_self]
        rw [pcQuote_of_mem DP ov hφ', pcCoreState_eq DP ov _ hW, pcCoreWeights_eq DP ov _ hW]
        unfold interiorCoherentMarketMaker
        rfl
  · exact absurd hv (fun hv => not_stageInhabited_vacuous DP ov n hW v hv)

/-- **T6. The firm does not exploit the coherent overlaid market**: T0 with `W = ∅`.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_firm_not_exploited`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pcOverlay_firm_not_exploited (DP : DeductiveProcess) (ov : Overlay) :
    ¬ (tradingFirmTrader DP (pcQuote DP ov)).Exploits (pcHistory DP ov) DP :=
  firm_not_exploits_of_coherentAccepted_off_finite DP (pcQuote DP ov) (pcQuote_range DP ov) ∅
    (fun n _ v hv => pcOverlay_firm_dayValue_le DP ov n v hv)

/-- **T6 (headline, M3). No efficiently computable trader exploits the coherent overlaid
market**, for every process `DP` and every overlay `ov`: an exploiting e.c. trader would make
the static firm on the coherent overlaid table exploit it (FAF's `trading_firm_dominance`),
and the firm does not. The market is exactly coherent on each day's mentioned set
(`pcOverlay_coherent_mentioned`); `ComputableMarket` is **not** established here.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_no_ec_trader_exploits`); [[bli-program]] §4 M3
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance` is FAF's theorem, applied; `ov.range` is a field of D2 -/
theorem pcOverlay_no_ec_trader_exploits (DP : DeductiveProcess) (ov : Overlay) :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (pcHistory DP ov) DP :=
  no_ec_trader_exploits_of_firm_coherentAccepted_off_finite DP (pcQuote DP ov)
    (pcQuote_range DP ov) ∅ (fun n _ v hv => pcOverlay_firm_dayValue_le DP ov n v hv)

/-! ## T6: exact coherence on the mentioned set, every inhabited day -/

/-- **T6 (headline, M3). The coherent overlaid market is exactly coherent on the day's
mentioned set**: on every day whose stage has a consistent world, the day-`n` table is, on
`mentionedSet (pcFirmStrat n)`, the marginal of the `DP.D n`-consistent world measure
`pcCoreWeights n` (the extended table `piTable` is `IsWorldMarginal` on the whole Boolean
algebra generated by the mentioned set).
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_coherent_mentioned`); [[bli-program]] §2.7
Kind: C
Fidelity: variant: `IsWorldMarginal` of the extended table `piTable (pcCoreWeights n)` plus
quote = table on the mentioned set (the quote itself is the overlay off the mentioned set)
Hyps: (a) `hW` (the stage has a consistent world; automatic for `paperDP`) -/
theorem pcOverlay_coherent_mentioned (DP : DeductiveProcess) (ov : Overlay) (n : ℕ)
    (hW : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsWorldMarginal (piTable (pcCoreWeights DP ov n)) (mentionedSet (pcFirmStrat DP ov n))
        (DP.D n) (pcB DP ov n) ∧
      ∀ φ ∈ mentionedSet (pcFirmStrat DP ov n),
        pcQuote DP ov n φ = piTable (pcCoreWeights DP ov n) φ := by
  have hW' := (stageInhabited_iff DP ov n).mpr hW
  exact ⟨piTable_isWorldMarginal (pcCoreWeights_isWorldMeasure DP ov n hW') _,
    fun _ hφ => pcQuote_eq_pi DP ov n hW' hφ⟩

/-- **T6, `CoherentOn` form**: the day-`n` table restricted to the mentioned set is
`CoherentOn … (DP.D n) (pcB n)` in bli-finite's sense.
Source: [[bli-coherent-mm-mandate]] T6 ("the `CoherentOn`-of-`actualTable` form")
Kind: C
Fidelity: exact
Hyps: (a) `hW` -/
theorem pcOverlay_coherentOn (DP : DeductiveProcess) (ov : Overlay) (n : ℕ)
    (hW : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    CoherentOn (𝒮 := constIndex (mentionedSet (pcFirmStrat DP ov n))) (m := n)
      (fun φ => pcQuote DP ov n φ.1) (DP.D n) (pcB DP ov n) := by
  have hW' := (stageInhabited_iff DP ov n).mpr hW
  have hw := pcCoreWeights_isWorldMeasure DP ov n hW'
  exact ⟨_, hw.1, hw.2.1, hw.2.2, fun φ => pcQuote_eq_pi DP ov n hW' φ.2⟩

/-- **T6. Non-dogmatism of the coherent overlaid market**: a mentioned sentence some
`DP.D n`-consistent finite world holds and some fails is priced strictly inside `(0, 1)`.
Source: [[bli-coherent-mm-mandate]] T6 (`pcOverlay_nonDogmatic`)
Kind: C
Fidelity: exact
Hyps: (a) `hW` -/
theorem pcOverlay_nonDogmatic (DP : DeductiveProcess) (ov : Overlay) (n : ℕ)
    (hW : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {φ : Sentence}
    (hφ : φ ∈ mentionedSet (pcFirmStrat DP ov n))
    (h1 : ∃ u ∈ worldsOf (DP.D n) (pcB DP ov n), (worldOf u).Holds φ)
    (h0 : ∃ u ∈ worldsOf (DP.D n) (pcB DP ov n), ¬ (worldOf u).Holds φ) :
    0 < pcQuote DP ov n φ ∧ pcQuote DP ov n φ < 1 := by
  have hW' := (stageInhabited_iff DP ov n).mpr hW
  rw [pcQuote_eq_pi DP ov n hW' hφ]
  exact ⟨piTable_pos_of_exists_holds (pcCoreWeights_isWorldMeasure DP ov n hW')
      (pcCoreWeights_fullSupport DP ov n hW') h1,
    piTable_lt_one_of_exists_not_holds (pcCoreWeights_isWorldMeasure DP ov n hW')
      (pcCoreWeights_fullSupport DP ov n hW') h0⟩

/-- **T6. Decided sentences stay at their truth** (`pcQuote_decided_monotone`): a sentence true
in every world consistent with `DP.D m` is, on every later inhabited day `n ≥ m` on which it is
mentioned, priced exactly `1` (`DP.mono` plus T2(c)); dually `0`.
Source: [[bli-coherent-mm-mandate]] T6 (`pcQuote_decided_monotone`)
Kind: C
Fidelity: exact
Hyps: (a) `hW` -/
theorem pcQuote_decided_monotone (DP : DeductiveProcess) (ov : Overlay) {m n : ℕ} (hmn : m ≤ n)
    (hW : ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {φ : Sentence}
    (hφ : φ ∈ mentionedSet (pcFirmStrat DP ov n)) :
    ((∀ v : PCWorld, v.ConsistentWith (DP.D m) → v.Holds φ) → pcQuote DP ov n φ = 1) ∧
    ((∀ v : PCWorld, v.ConsistentWith (DP.D m) → ¬ v.Holds φ) → pcQuote DP ov n φ = 0) := by
  have hW' := (stageInhabited_iff DP ov n).mpr hW
  rw [pcQuote_eq_pi DP ov n hW' hφ]
  have hw := pcCoreWeights_isWorldMeasure DP ov n hW'
  constructor
  · intro h
    exact piTable_eq_one_of_decided hw fun v hv => h v fun ψ hψ => hv ψ (DP.mono_le hmn hψ)
  · intro h
    exact piTable_eq_zero_of_decided_false hw fun v hv => h v fun ψ hψ => hv ψ (DP.mono_le hmn hψ)

/-! ## The assembly lemma and `PCInductor` -/

/-- **Assembly lemma (Kind L).** The coherent overlaid market is a logical inductor **if** it is
a computable market — the computability is *assumed*, exactly as in FAF's
`lia_isLogicalInductor_of_computableMarket` and `bli-overlay`'s assembly lemma; nothing in this
package establishes `ComputableMarket (pcHistory DP ov)`. Ledger: `partial: computability open`.
Source: [[bli-coherent-mm-mandate]] T6 (assembly); [[bli-program]] §7 item 8
Kind: L
Fidelity: weaker: `ComputableMarket (pcHistory DP ov)` is a hypothesis, not proved
Hyps: (b) `hmarket : ComputableMarket (pcHistory DP ov)` — assumed (OPEN); (a) `hDP` is the
process's computability, the criterion's own hypothesis -/
theorem pcOverlay_isLogicalInductor_of_computableMarket (DP : DeductiveProcess) (ov : Overlay)
    (hDP : ComputableDeductiveProcess DP) (hmarket : ComputableMarket (pcHistory DP ov)) :
    IsLogicalInductor (pcHistory DP ov) DP where
  marketComputable := hmarket
  processComputable := hDP
  noExploit := pcOverlay_no_ec_trader_exploits DP ov

/-- **D5. A propositionally coherent inductor** (program §2.7, without the computability
field): a real market `P` that is the cast of an exact rational table `Q`; on every day whose
stage has a consistent world, `Q n` is, on the day's coherent set `S n`, the marginal of a
`DP.D n`-consistent world measure over `B n` atoms; and no efficiently computable trader
exploits `P`. `marketComputable` is **not** a field — it is the separate open predicate
`ComputableMarket P`.
Source: [[bli-coherent-mm-mandate]] D5 (`PCInductor`); [[bli-program]] §2.7, §7 item 8
Kind: D
Fidelity: exact (the computability clause deliberately omitted and left open) -/
structure PCInductor (DP : DeductiveProcess) where
  /-- The market. -/
  P : History
  /-- Its exact rational table. -/
  Q : ℕ → Sentence → ℚ
  /-- The market is the cast of the table. -/
  P_eq : ∀ n φ, P n φ = (Q n φ : ℝ)
  /-- The day's coherent sentence set. -/
  S : ℕ → Finset Sentence
  /-- The day's atom bound. -/
  B : ℕ → ℕ
  /-- Exact coherence on `S n`, every inhabited day. -/
  coh : ∀ n, (∃ v : PCWorld, v.ConsistentWith (DP.D n)) →
    ∃ w : FiniteWorld (B n) → ℚ, IsWorldMeasure (DP.D n) (B n) w ∧ ∀ φ ∈ S n, Q n φ = piTable w φ
  /-- No efficiently computable trader exploits the market. -/
  noExploit : ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits P DP

/-- **`PCInductor DP` is inhabited** by the coherent overlaid market, for every process and
overlay, with `S n := mentionedSet (pcFirmStrat n)` and `B n := pcB n`. **`ComputableMarket
(pcHistory DP ov)` is open**: this is not a logical inductor until that is settled.
Source: [[bli-coherent-mm-mandate]] T6 (`PCInductor`); [[bli-program]] §4 row M3
Kind: C
Fidelity: exact (inhabited; `ComputableMarket` open)
Hyps: (a) -/
def pcInductor (DP : DeductiveProcess) (ov : Overlay) : PCInductor DP where
  P := pcHistory DP ov
  Q := pcQuote DP ov
  P_eq := fun _ _ => rfl
  S := fun n => mentionedSet (pcFirmStrat DP ov n)
  B := pcB DP ov
  coh := fun n hW => ⟨pcCoreWeights DP ov n,
    pcCoreWeights_isWorldMeasure DP ov n ((stageInhabited_iff DP ov n).mpr hW),
    (pcOverlay_coherent_mentioned DP ov n hW).2⟩
  noExploit := pcOverlay_no_ec_trader_exploits DP ov

end

end Cleanroom.Bli.BliCoherentMm.AttemptB
