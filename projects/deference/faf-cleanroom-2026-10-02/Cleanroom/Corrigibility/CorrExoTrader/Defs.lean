import Cleanroom.Li.LiProjection.Subst
import LogicalInduction.Framework.Affine

/-!
# `corr-exo-trader` · Defs: definitions of record

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 1 of the
layout. Light: FAF's `Criterion`/`Affine` plus `bli-found`'s fresh-atom registry (through
`li-projection`'s `Subst`, for `AtomFreeSentence`/`AtomFreeProcess`).

* **Fresh atoms** (family `6`, registry row "exogenous-trader atoms"): `exoAtom k :=
  freshAtom 6 (Nat.pair 0 (Nat.pair 0 k))` — day `0` first (registry rule), sub-family `0`, index
  `k`. The undecidable utility atom is `utilityAtom := exoAtom 0`. Freshness relative to FAF's
  processes is `freshAtom_ne_faf` + `paperDP_cleanroomFree`; relative to families `0`–`5` and `7`
  it is `freshAtom_injective`.
* **The exogenous demand is a `Trader`** (decision 1 of the mandate): `ExoDemand := Trader`.
  No computability, efficiency or budget is required of it — the source's "it needn't be e.c."
  The day-wise sum of two traders is `Trader.join` (FAF's `Strategy.join`).
* **`NoEcExploit P DP`** — the no-exploit predicate (decision 3): `∀ T, EfficientlyComputable T →
  ¬ T.Exploits P DP`, which is `IsLogicalInductor.noExploit` and nothing more. Every market-level
  statement of this package is over it, because the exo-market with an arbitrary `H` is not a
  `ComputableMarket`, so `IsLogicalInductor` (which bundles the computability certificates) is
  not available and FAF's `lic_*` property theorems do not apply to it as typed.
* **Mark-to-market names** (T7): `markToMarket T P n` (world-independent) and
  `openExposure T P v n` (the open position priced at today's price); the decomposition theorem
  is in `Undecided.lean`.
* **`constBuyer φ c`**: the trader buying `c` shares of `φ` every day (coefficient a constant, not
  a price feature — the Occam trader that "likes the stock regardless of return").

Scope: every market-level statement in this package is **single-market** (one market, one process,
one exogenous participant; no `H`/`A` pair).
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection

/-! ## Fresh atoms of family 6 -/

/-- The atom code of the `k`-th exogenous-trader atom: family `6`, payload
`Nat.pair 0 (Nat.pair 0 k)` (day `0`, sub-family `0`, index `k`).
Source: mandate header ("Fresh atoms"); `bli-found` registry row `6`
Kind: D
Fidelity: n/a -/
def exoAtomCode (k : ℕ) : ℕ := freshAtomCode 6 (Nat.pair 0 (Nat.pair 0 k))

/-- The `k`-th exogenous-trader atom.
Source: mandate header ("Fresh atoms")
Kind: D
Fidelity: n/a -/
def exoAtom (k : ℕ) : Sentence := Formula.atom (exoAtomCode k)

/-- `exoAtom k` is the registry's `freshAtom 6 ⟨0, ⟨0, k⟩⟩`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exoAtom_eq_freshAtom (k : ℕ) : exoAtom k = freshAtom 6 (Nat.pair 0 (Nat.pair 0 k)) := rfl

/-- The exo-atom codes are injective in `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exoAtomCode_injective : Function.Injective exoAtomCode := by
  intro k k' h
  have := (freshAtomCode_inj.mp h).2
  have := (Nat.pair_eq_pair.mp this).2
  exact (Nat.pair_eq_pair.mp this).2

/-- Every exo-atom code carries a tag above FAF's own families (`8 < tag`).
Source: mandate header ("freshness relative to FAF's processes")
Kind: L
Fidelity: n/a -/
lemma exoAtomCode_ne_faf (k : ℕ) : 8 < (exoAtomCode k).unpair.1 :=
  freshAtomCode_tag_gt 6 _

/-- **The undecidable utility atom** `u := exoAtom 0`. The source's `u` is a LUV whose threshold
sentences `⌜u > p⌝` are pushed; here the single threshold sentence is rendered as the atom itself
(`li-splice-condition` owns the LUV form of corr-core-034 — cite it, do not redefine).
Source: mandate decision 4
Kind: D
Fidelity: variant: one atom in place of the LUV's threshold family -/
def utilityAtom : Sentence := exoAtom 0

/-- The code of the utility atom.
Source: mandate decision 4
Kind: D
Fidelity: n/a -/
def utilityAtomCode : ℕ := exoAtomCode 0

/-- `utilityAtom = Formula.atom utilityAtomCode`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma utilityAtom_eq : utilityAtom = Formula.atom utilityAtomCode := rfl

/-- A cleanroom-free sentence (every atom in FAF's own vocabulary) is free of every exo-atom.
Source: mandate decision 4 (`AtomFreeProcess u DP` for every FAF process)
Kind: L
Fidelity: exact -/
lemma atomFreeSentence_exo_of_cleanroomFree {φ : Sentence} (h : CleanroomFreeSentence φ) (k : ℕ) :
    AtomFreeSentence (exoAtomCode k) φ :=
  h.freshAtomCode_notMem 6 _

/-- A cleanroom-free process (e.g. `paperDP T`, by `bli-found`'s `paperDP_cleanroomFree`) is free
of every exo-atom: the utility atom is **undecided at every stage** of such a process.
Source: mandate decision 4
Kind: L
Fidelity: exact -/
lemma atomFreeProcess_exo_of_cleanroomFree {DP : DeductiveProcess} (h : CleanroomFreeProcess DP)
    (k : ℕ) : AtomFreeProcess (exoAtomCode k) DP :=
  fun n φ hφ => atomFreeSentence_exo_of_cleanroomFree (h n φ hφ) k

/-- A sentence tag-free for family `6`'s tag is free of every exo-atom (so the other families'
atoms — state, policy, action, ledger, projection, obstruction — never collide with them).
Source: mandate header (freshness relative to families `0`–`5`)
Kind: L
Fidelity: exact -/
lemma atomFreeSentence_exo_of_tagFree {φ : Sentence} (h : TagFreeSentence (cleanroomBaseTag + 6) φ)
    (k : ℕ) : AtomFreeSentence (exoAtomCode k) φ :=
  h.freshAtomCode_notMem _

/-- A process tag-free for family `6`'s tag is free of every exo-atom.
Source: mandate header
Kind: L
Fidelity: exact -/
lemma atomFreeProcess_exo_of_tagFree {DP : DeductiveProcess}
    (h : TagFreeProcess (cleanroomBaseTag + 6) DP) (k : ℕ) :
    AtomFreeProcess (exoAtomCode k) DP :=
  fun n φ hφ => atomFreeSentence_exo_of_tagFree (h n φ hφ) k

/-! ## The exogenous demand -/

/-- **The exogenous demand is a trader** (decision 1): a day-indexed family of `Strategy n`, i.e.
finite lists of `(EF × Sentence)` with coefficients of rank `≤ n`. No computability, efficiency
or budget is required — the source's "it needn't be e.c." It may read past prices (features of
rank `≤ n`), so "buy while the price is below the target" is expressible. What an `EF` cannot
express is an arbitrary continuous function of the day's prices not built from `max`, `+`, `×`,
constants and prices (findings).
Source: [[2026-09-14__bli-thread-conditioning-vs-prior-overrides__claude-ai-paste]] line 73, 95; mandate decision 1
Kind: D
Fidelity: exact (FAF's own trader type; continuity and per-day boundedness hold by construction) -/
abbrev ExoDemand : Type := Trader

/-- The absent demand: FAF's `Trader.zero` (no trades on any day). `exoHistory DP noDemand =
liaHistory DP` is the source's "the original LIC is the case `H = 0`" (`Market.lean`).
Source: line 95 ("The original LIC is the case `H = 0`")
Kind: D
Fidelity: exact -/
def noDemand : ExoDemand := Trader.zero

/-- The day-wise sum of two traders: on day `n`, `Strategy.join [A.strat n, B.strat n]`.
Source: mandate decision 1 (`Strategy.join [T, H.strat n]` as the day strategy)
Kind: D
Fidelity: exact -/
def Trader.join (A B : Trader) : Trader where
  strat n := Strategy.join [A.strat n, B.strat n]

/-- The value of a joined day strategy is the sum of the two values.
Source: none: infrastructure (FAF's `join_value` at two summands)
Kind: L
Fidelity: n/a -/
lemma Strategy.join_two_value {n : ℕ} (S T : Strategy n) (V : History) (w : Valuation) :
    (Strategy.join [S, T]).value V w = S.value V w + T.value V w := by
  rw [Strategy.join_value]
  simp

/-- The net worth of a joined trader is the sum of the net worths.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Trader.join_netWorth (A B : Trader) (P : History) (v : PCWorld) (n : ℕ) :
    (Trader.join A B).netWorth P v n = A.netWorth P v n + B.netWorth P v n := by
  unfold Trader.netWorth
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Strategy.join_two_value _ _ _ _

/-! ## The no-exploit predicate -/

/-- **No efficiently computable trader exploits `P` relative to `DP`** — `IsLogicalInductor.noExploit`
and nothing more. The exo-market with an arbitrary demand is not a `ComputableMarket`, so
`IsLogicalInductor` (which bundles `marketComputable` and `processComputable`) is not available
for it, and FAF's `lic_*` property theorems — which take the class — **do not apply to the
exo-market as typed**. Every market-level theorem of this package is stated over this predicate
and proved directly over `Trader.Exploits`.
Source: mandate decision 3
Kind: D
Fidelity: weaker: the criterion's semantic clause alone, without the two computability certificates -/
def NoEcExploit (P : History) (DP : DeductiveProcess) : Prop :=
  ∀ T : Trader, EfficientlyComputable T → ¬ T.Exploits P DP

/-- Every logical inductor satisfies the no-exploit predicate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma IsLogicalInductor.noEcExploit (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] : NoEcExploit P DP :=
  hLI.noExploit

/-! ## The constant buyer -/

/-- The trader buying `c` shares of `φ` every day: its coefficient is the **constant** `c`, not a
price feature — it "likes the stock" regardless of return (Abram's Occam reading, line 105).
Source: line 105, 113 (the Occam trader); mandate T6.1
Kind: D
Fidelity: exact -/
def constBuyer (φ : Sentence) (c : ℚ) : Trader where
  strat _ := { trades := [(EF.const c, φ)], rank_le := by simp }

/-- The constant buyer's day value: `c · (w φ − P n φ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constBuyer_value (φ : Sentence) (c : ℚ) (P : History) (w : Valuation) (n : ℕ) :
    ((constBuyer φ c).strat n).value P w = (c : ℝ) * (w φ - P n φ) := by
  simp [constBuyer, Strategy.value]

/-- The constant buyer's net worth: `∑_{i ≤ n} c · (v.payout φ − P i φ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constBuyer_netWorth (φ : Sentence) (c : ℚ) (P : History) (v : PCWorld) (n : ℕ) :
    (constBuyer φ c).netWorth P v n = ∑ i ∈ Finset.range (n + 1), (c : ℝ) * (v.payout φ - P i φ) := by
  unfold Trader.netWorth
  refine Finset.sum_congr rfl fun i _ => ?_
  exact constBuyer_value φ c P v.payout i

/-! ## Mark-to-market names (T7) -/

/-- **Mark-to-market**: the trader's positions through day `n`, each repriced at day `n`'s price:
`∑_{i ≤ n} ∑_{(e,φ) ∈ trades_i} e(P) · (P n φ − P i φ)`. World-independent.
Source: line 105/115 (what pays on undecidables); mandate T7.1
Kind: D
Fidelity: exact -/
noncomputable def markToMarket (T : Trader) (P : History) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (((T.strat i).trades).map (fun p => p.1.denote P * (P n p.2 - P i p.2))).sum

/-- **Open exposure**: the current position priced against the world at today's price:
`∑_{i ≤ n} ∑_{(e,φ) ∈ trades_i} e(P) · (v.payout φ − P n φ)`.
Source: mandate T7.1
Kind: D
Fidelity: exact -/
noncomputable def openExposure (T : Trader) (P : History) (v : PCWorld) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (((T.strat i).trades).map (fun p => p.1.denote P * (v.payout p.2 - P n p.2))).sum

end Cleanroom.Corrigibility.CorrExoTrader
