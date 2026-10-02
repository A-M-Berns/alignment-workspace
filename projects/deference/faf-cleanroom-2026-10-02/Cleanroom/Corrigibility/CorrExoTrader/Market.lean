import Cleanroom.Corrigibility.CorrExoTrader.Defs
import LogicalInduction.Construction.LIA

/-!
# `corr-exo-trader` · Market: the exo-market of record and the fixed point with an exogenous summand (T1)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 2 of the
layout. Construction-touching (imports FAF's `Construction/LIA`, hence `TradingFirm` → `Budgeter`
→ `MarketMaker` → `Brouwer`); theorem files import this one.

**The exo-market of record** (decision 2) mirrors FAF's `liaStates` recursion with the demand
joined into the day action: on day `n`, the market maker's fixed point is taken against
`Strategy.join [TF_n(past), H_n]` — the firm's day strategy on the realized prefix plus the
exogenous demand's. **`H` is in the fixed point, not in the firm**: the firm's budgeter sees only
the enumerated e.c. traders, which is the source's "include `H` in the fixed point but not in the
supertrader" exactly. No new fixed-point infrastructure is needed: FAF's `fixed_point_lemma` and
`MarketMaker` quantify over an *arbitrary* day strategy, and the join is one.

* `exoStates`, `exoQuote`, `exoHistory`, `exoTrader`; the identification
  `exoHistory_eq_marketMakerHistory` (prefix invariance, `TradingFirmAt_eq_of_eq_prefix`), the
  range and cast facts `trading_firm_dominance` takes, and the sanity identity
  `exoHistory_noDemand : exoHistory DP noDemand = liaHistory DP` (the source's "the original
  LIC is the case `H = 0`" at the level of the market).
* **T1.3** `exo_day_value_le`: the day trade `TF_n + H_n` has value `≤ 2^{-(n+1)}` in every p.c.
  world — FAF's `marketMaker_day_value_le` transported along the identification; and the pure
  form `exists_fixedPoint_with_demand` (`fixed_point_lemma` at a joined strategy).
* **T1.4** `push_pins_day_price` / `push_pins_marketMaker_price`: a push of `k > 0` shares of an
  atom against an otherwise empty day strategy pins the day price to `1` (exactly, for any fixed
  point of `fixed_point_lemma`'s kind) or to `≥ 1 − ε/k` (for FAF's `MarketMaker` output). The
  unpushed contrast (`unpushed_interior`) is in `Undecided.lean`.

**Disclosure (decision 3).** No `IsLogicalInductor (exoHistory DP H) DP` is claimed anywhere: an
arbitrary `H` makes the market non-computable, and for computable `H` the certificate is a compiler
project (`Open.lean`, T2.5). Market-level statements are over `NoEcExploit`.

**Trap avoided (T1.4).** Nothing is claimed about `exoHistory`'s value on `u` beyond the inequality
`≥ 1 − ε/k` on a day whose firm strategy is empty: `MarketMaker` is the first accepted candidate of
an enumeration and has no closed form.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional

/-! ## The exo-market recursion -/

/-- **The exo-market's rational states**: day `n` is the market maker's fixed point against the
trading firm run on the realized prefix *joined with the exogenous demand's day strategy*.
FAF's `liaStates` with `H.strat n` as a second summand of the day action.
Source: line 93 ("the LIA picks `P_n` as the fixed point at which the total trade — now `TF_n + H_n` — has no plausible upside"); mandate decision 2
Kind: D
Fidelity: exact -/
noncomputable def exoStates (DP : DeductiveProcess) (H : ExoDemand) : ℕ → RationalBeliefState
  | n =>
      let past := List.ofFn fun i : Fin n => exoStates DP H i
      MarketMaker (Strategy.join [(TradingFirm DP).action n past, H.strat n]) past
        (marketMakerError n) (marketMakerError_pos n)
termination_by n => n
decreasing_by exact i.isLt

/-- The exo-market's exact rational quote table.
Source: mandate decision 2
Kind: D
Fidelity: exact -/
noncomputable def exoQuote (DP : DeductiveProcess) (H : ExoDemand) : ℕ → Sentence → ℚ :=
  fun n => (exoStates DP H n).quote

/-- **The exo-market of record**: the real-valued history induced by the exo-states.
Source: mandate decision 2
Kind: D
Fidelity: exact -/
noncomputable def exoHistory (DP : DeductiveProcess) (H : ExoDemand) : History :=
  fun n => (exoStates DP H n).toValuation

/-- The static trader the exo-market faces: the complete-table firm `TradingFirmAt DP (exoQuote DP H)`
joined with the demand, day by day.
Source: mandate decision 2
Kind: D
Fidelity: exact -/
noncomputable def exoTrader (DP : DeductiveProcess) (H : ExoDemand) : Trader where
  strat n := Strategy.join [TradingFirmAt DP (exoQuote DP H) n, H.strat n]

/-- The exo-market's prices lie in `[0, 1]` (the `hP` hypothesis of `trading_firm_dominance`).
Source: mandate T1.2
Kind: L
Fidelity: exact -/
lemma exoHistory_range (DP : DeductiveProcess) (H : ExoDemand) (day : ℕ) (φ : Sentence) :
    0 ≤ exoHistory DP H day φ ∧ exoHistory DP H day φ ≤ 1 :=
  (exoStates DP H day).toValuation_mem_Icc φ

/-- The real exo-market is definitionally the cast of its rational quote table (the `hQ`
hypothesis of `trading_firm_dominance`).
Source: mandate T1.2
Kind: L
Fidelity: exact -/
lemma exoHistory_eq_quote_cast (DP : DeductiveProcess) (H : ExoDemand) (day : ℕ) (φ : Sentence) :
    exoHistory DP H day φ = (exoQuote DP H day φ : ℝ) := rfl

/-- On a day strictly inside the prefix, the rational history of the exo-prefix is the exo-quote.
Source: none: infrastructure (FAF's `rationalHistory_liaPast`)
Kind: L
Fidelity: n/a -/
lemma rationalHistory_exoPast (DP : DeductiveProcess) (H : ExoDemand) {n day : ℕ}
    (hday : day < n) (φ : Sentence) :
    rationalHistory (List.ofFn fun i : Fin n => exoStates DP H i) day φ = exoQuote DP H day φ := by
  simp [rationalHistory, exoQuote, hday]

/-- Prefix invariance: the firm's adaptive day action on the realized exo-prefix is its static
complete-table day action at the exo-quote.
Source: none: infrastructure (FAF's `TradingFirmAt_eq_of_eq_prefix`)
Kind: L
Fidelity: n/a -/
lemma tradingFirm_action_exoPast (DP : DeductiveProcess) (H : ExoDemand) (n : ℕ) :
    (TradingFirm DP).action n (List.ofFn fun i : Fin n => exoStates DP H i) =
      TradingFirmAt DP (exoQuote DP H) n := by
  show TradingFirmAt DP (rationalHistory _) n = TradingFirmAt DP (exoQuote DP H) n
  apply TradingFirmAt_eq_of_eq_prefix
  intro day hday φ
  exact rationalHistory_exoPast DP H hday φ

/-- **Identification with FAF's generic MarketMaker recursion**: the exo-states are
`marketMakerStates (exoTrader DP H)`.
Source: mandate T1.2 (FAF's `liaStates_eq_marketMakerStates` with the summand)
Kind: L
Fidelity: exact -/
lemma exoStates_eq_marketMakerStates (DP : DeductiveProcess) (H : ExoDemand) (n : ℕ) :
    exoStates DP H n = marketMakerStates (exoTrader DP H) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpast :
          (List.ofFn fun i : Fin n => exoStates DP H i) =
            List.ofFn fun i : Fin n => marketMakerStates (exoTrader DP H) i := by
        apply List.ext_getElem
        · simp
        · intro i hi₁ hi₂
          simp only [List.getElem_ofFn]
          exact ih i (by simpa using hi₁)
      rw [exoStates, marketMakerStates]
      change MarketMaker
          (Strategy.join [(TradingFirm DP).action n
            (List.ofFn fun i : Fin n => exoStates DP H i), H.strat n])
          (List.ofFn fun i : Fin n => exoStates DP H i)
          (marketMakerError n) (marketMakerError_pos n) =
        MarketMaker
          (Strategy.join [TradingFirmAt DP (exoQuote DP H) n, H.strat n])
          (List.ofFn fun i : Fin n => marketMakerStates (exoTrader DP H) i)
          (marketMakerError n) (marketMakerError_pos n)
      rw [tradingFirm_action_exoPast, hpast]

/-- **The market form of the identification**: `exoHistory DP H = marketMakerHistory (exoTrader DP H)`.
Source: mandate T1.2
Kind: L
Fidelity: exact -/
theorem exoHistory_eq_marketMakerHistory (DP : DeductiveProcess) (H : ExoDemand) :
    exoHistory DP H = marketMakerHistory (exoTrader DP H) := by
  funext n φ
  rw [exoHistory, marketMakerHistory, exoStates_eq_marketMakerStates]

/-! ## `H = 0` recovers the LIA market -/

/-- Joining the empty strategy changes nothing (`Strategy.ext`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Strategy.join_zero {n : ℕ} (S : Strategy n) :
    Strategy.join [S, Trader.zero.strat n] = S := by
  apply Strategy.ext
  simp [Strategy.join, Trader.zero]

/-- With no demand the exo-states are FAF's `liaStates`.
Source: line 95 ("The original LIC is the case `H = 0`"); mandate T1.2
Kind: T
Fidelity: exact -/
lemma exoStates_noDemand (DP : DeductiveProcess) (n : ℕ) :
    exoStates DP noDemand n = liaStates DP n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpast :
          (List.ofFn fun i : Fin n => exoStates DP noDemand i) =
            List.ofFn fun i : Fin n => liaStates DP i := by
        apply List.ext_getElem
        · simp
        · intro i hi₁ hi₂
          simp only [List.getElem_ofFn]
          exact ih i (by simpa using hi₁)
      rw [exoStates, liaStates]
      change MarketMaker
          (Strategy.join [(TradingFirm DP).action n
            (List.ofFn fun i : Fin n => exoStates DP noDemand i), noDemand.strat n])
          (List.ofFn fun i : Fin n => exoStates DP noDemand i)
          (marketMakerError n) (marketMakerError_pos n) =
        MarketMaker
          ((TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i))
          (List.ofFn fun i : Fin n => liaStates DP i)
          (marketMakerError n) (marketMakerError_pos n)
      rw [hpast]
      show MarketMaker (Strategy.join [_, Trader.zero.strat n]) _ _ _ = _
      rw [Strategy.join_zero]

/-- **The original LIC is the case `H = 0`, at the level of the market**: the exo-market with no
demand is FAF's `liaHistory`.
Source: line 95; mandate T1.2
Kind: T
Fidelity: exact -/
theorem exoHistory_noDemand (DP : DeductiveProcess) : exoHistory DP noDemand = liaHistory DP := by
  funext n φ
  rw [exoHistory, liaHistory, exoStates_noDemand]

/-! ## T1.3 — the fixed point with the exogenous summand -/

/-- **The pure form** (the plan's first target): FAF's `fixed_point_lemma` at a day strategy that
is the join of an internal strategy `T` and a demand `Hn` — a `[0,1]` valuation supported on the
joined support, against which the *total* day trade `T + Hn` has nonpositive value in every p.c.
world. The summand reading is literal: nothing is assumed of `Hn` beyond being a `Strategy n`
(continuity and per-day boundedness are built into `EF`).
Source: line 93, 95 ("preservation should follow whenever `H_n` is a continuous, per-day-bounded strategy so the fixed point exists"); mandate T1.3
Kind: L (audit r2 fidelity N4: a one-term application of `fixed_point_lemma` at the join)
Fidelity: exact
Hyps: (a) -/
theorem exists_fixedPoint_with_demand {n : ℕ} (T Hn : Strategy n) (prior : History) :
    ∃ V : Valuation,
      (∀ φ, 0 ≤ V φ ∧ V φ ≤ 1) ∧
      (∀ φ, φ ∉ (Strategy.join [T, Hn]).support → V φ = 0) ∧
      ∀ v : PCWorld, (Strategy.join [T, Hn]).value (Function.update prior n V) v.payout ≤ 0 :=
  fixed_point_lemma (Strategy.join [T, Hn]) prior

/-- **T1.3 — the day trade `TF_n + H_n` has no plausible upside** beyond the market maker's error
allowance: in every p.c. world, its value against the exo-market is `≤ 2^{-(n+1)}`. FAF's
`marketMaker_day_value_le` transported along `exoHistory_eq_marketMakerHistory`. Single-market.
The real work is the identification `exoStates_eq_marketMakerStates` (strong induction with prefix
invariance); this statement is FAF's theorem at the exo-trader (kind C, audit r1 N3).
Source: line 93 ("`TF_n + H_n` has no plausible upside each day"); corr-core-040(i); bli-soto-b-056; mandate T1.3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exo_day_value_le (DP : DeductiveProcess) (H : ExoDemand) (n : ℕ) (v : PCWorld) :
    ((exoTrader DP H).strat n).value (exoHistory DP H) v.payout ≤ (marketMakerError n : ℝ) := by
  rw [exoHistory_eq_marketMakerHistory]
  exact marketMaker_day_value_le (exoTrader DP H) n v

/-- The day trade split into its two summands: `TF_n`'s value plus `H_n`'s value is `≤ 2^{-(n+1)}`.
Source: mandate T1.3
Kind: L
Fidelity: exact -/
theorem exo_day_value_split_le (DP : DeductiveProcess) (H : ExoDemand) (n : ℕ) (v : PCWorld) :
    (TradingFirmAt DP (exoQuote DP H) n).value (exoHistory DP H) v.payout +
      (H.strat n).value (exoHistory DP H) v.payout ≤ (marketMakerError n : ℝ) := by
  have h := exo_day_value_le DP H n v
  rwa [show (exoTrader DP H).strat n = Strategy.join [TradingFirmAt DP (exoQuote DP H) n, H.strat n]
    from rfl, Strategy.join_two_value] at h

/-- The exo-trader (firm + demand) is not exploited by the market it generates, for any process —
FAF's `marketMaker_not_exploited` at the exo-trader. (A statement about the *sum*; the firm alone
is bounded in `GenLic.lean`.)
Source: mandate T1.3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exoTrader_not_exploited (DP : DeductiveProcess) (H : ExoDemand) :
    ¬ (exoTrader DP H).Exploits (exoHistory DP H) DP := by
  rw [exoHistory_eq_marketMakerHistory]
  exact marketMaker_not_exploited (exoTrader DP H) DP

/-! ## T1.4 — a push moves the price -/

/-- The world holding every atom.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def worldAll : PCWorld := fun _ => True

/-- `worldAll` holds every atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma worldAll_holds_atom (a : ℕ) : worldAll.Holds (Formula.atom a) := by
  rw [PCWorld.holds_atom]; trivial

/-- The value of a day strategy that is the empty internal strategy joined with a single trade
of `k` shares of `φ`: `k · (w φ − V n φ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma join_empty_single_value {n : ℕ} (hZ : Strategy n) (hZt : hZ.trades = [])
    (Hn : Strategy n) (k : ℚ) (φ : Sentence) (hHn : Hn.trades = [(EF.const k, φ)])
    (V : History) (w : Valuation) :
    (Strategy.join [hZ, Hn]).value V w = (k : ℝ) * (w φ - V n φ) := by
  simp [Strategy.join, Strategy.value, hZt, hHn]

/-- **A push pins the day price (exact form, from the statement of `fixed_point_lemma` alone).** If
the day strategy is the empty internal strategy joined with a demand buying `k > 0` shares of the
atom `u`, then *every* `[0,1]` valuation `V` against which the joined trade has nonpositive value in
every p.c. world has `V u = 1`: in the world holding `u` the value is `k · (1 − V u) ≤ 0`.
Source: line 93 ("`H_n` buying … moves the price along the internal traders' supply curve" — here with no internal supply); mandate T1.4
Kind: L (non-vacuity check for T1: a contrast lemma, not a witness of a hypothesis package)
Fidelity: exact (the unopposed day; the opposed day is `push_pins_marketMaker_price`'s `≥ 1 − ε/k`)
Hyps: (a) -/
theorem push_pins_day_price {n : ℕ} (u : ℕ) (k : ℚ) (hk : 0 < k)
    (hZ : Strategy n) (hZt : hZ.trades = [])
    (Hn : Strategy n) (hHn : Hn.trades = [(EF.const k, Formula.atom u)])
    (prior : History) (V : Valuation) (hV : ∀ φ, 0 ≤ V φ ∧ V φ ≤ 1)
    (hfix : ∀ v : PCWorld,
      (Strategy.join [hZ, Hn]).value (Function.update prior n V) v.payout ≤ 0) :
    V (Formula.atom u) = 1 := by
  have h := hfix worldAll
  rw [join_empty_single_value hZ hZt Hn k _ hHn] at h
  simp only [Function.update_self] at h
  rw [PCWorld.payout, if_pos (worldAll_holds_atom u)] at h
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : 1 ≤ V (Formula.atom u) := by
    by_contra hlt
    have hlt' : V (Formula.atom u) < 1 := lt_of_not_ge hlt
    have : 0 < (k : ℝ) * (1 - V (Formula.atom u)) := mul_pos hk' (by linarith)
    linarith
  exact le_antisymm (hV _).2 h1

/-- **The pinned fixed point exists**: `fixed_point_lemma` at the pushed day strategy returns a
valuation with `V u = 1`.
Source: mandate T1.4
Kind: L (non-vacuity check for T1)
Fidelity: exact
Hyps: (a) -/
theorem exists_pinned_fixedPoint {n : ℕ} (u : ℕ) (k : ℚ) (hk : 0 < k)
    (hZ : Strategy n) (hZt : hZ.trades = [])
    (Hn : Strategy n) (hHn : Hn.trades = [(EF.const k, Formula.atom u)]) (prior : History) :
    ∃ V : Valuation, (∀ φ, 0 ≤ V φ ∧ V φ ≤ 1) ∧
      (∀ v : PCWorld, (Strategy.join [hZ, Hn]).value (Function.update prior n V) v.payout ≤ 0) ∧
      V (Formula.atom u) = 1 := by
  obtain ⟨V, hV, _, hfix⟩ := exists_fixedPoint_with_demand hZ Hn prior
  exact ⟨V, hV, hfix, push_pins_day_price u k hk hZ hZt Hn hHn prior V hV hfix⟩

/-- **A push pins FAF's `MarketMaker` output to within `ε/k` of `1`.** Against the empty internal
strategy joined with a demand buying `k > 0` shares of the atom `u`, the market maker's accepted
rational state prices `u` at `≥ 1 − ε/k` (`MarketMaker_worldValue_le` in the support world with
the `u`-bit set). Nothing more is claimed about the output: `MarketMaker` is the first accepted
candidate of an enumeration and has no closed form.
Source: line 93; mandate T1.4 ("with the market maker's `ε`")
Kind: L (non-vacuity check for T1)
Fidelity: exact
Hyps: (a) -/
theorem push_pins_marketMaker_price {n : ℕ} (u : ℕ) (k : ℚ) (hk : 0 < k)
    (hZ : Strategy n) (hZt : hZ.trades = [])
    (Hn : Strategy n) (hHn : Hn.trades = [(EF.const k, Formula.atom u)])
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) :
    1 - (ε : ℝ) / k ≤
      (MarketMaker (Strategy.join [hZ, Hn]) past ε hε).toValuation (Formula.atom u) := by
  set T := Strategy.join [hZ, Hn] with hT
  have hmem : Formula.atom u ∈ T.support := by
    apply Strategy.snd_mem_support T (p := (EF.const k, Formula.atom u))
    simp [T, Strategy.join, hZt, hHn]
  have h := MarketMaker_worldValue_le T past ε hε (fun _ => true)
  rw [join_empty_single_value hZ hZt Hn k _ hHn] at h
  simp only [Function.update_self] at h
  rw [show supportBitWorld T (fun _ => true) (Formula.atom u) = 1 by
    simp [supportBitWorld, hmem]] at h
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 : 1 - (MarketMaker T past ε hε).toValuation (Formula.atom u) ≤ (ε : ℝ) / k := by
    rw [le_div_iff₀ hk']
    linarith
  linarith

end Cleanroom.Corrigibility.CorrExoTrader
