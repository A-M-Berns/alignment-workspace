import Cleanroom.Corrigibility.CorrExoTrader.Defs
import LogicalInduction.Properties.Support.Exploitation
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Framework.Machine.SentenceMachine
import LogicalInduction.Framework.Asymptotics

/-!
# `corr-exo-trader` · FrontRun: predictable landings are already priced — asymptotically, with no claim about any single push (T3)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 4 of the
layout. No `Construction.*` import: the theorem is over **any** market satisfying the no-exploit
predicate `NoEcExploit`, with the exo-market instance in `Instances.lean` (T3.2).

The source (line 77, Consequence 2): "A trader who predicts that `T_H` will push `⌜u > 0.7⌝` from
`0.5` to `0.7` tomorrow buys today and sells tomorrow, so the LIC forces prices toward where the
humans will push them before the push, whenever the push is efficiently predictable." — "a
corrigible agent already believes what it expects to be legitimately taught" as a theorem shape.

* **The front-running trader** `frontRunner φ q δ`: on day `n` it takes `c_n` shares of `φ n`,
  where `c_n = ramp((q_n − δ − P_n(φ_n))/δ) − ramp((P_n(φ_n) − q_n − δ)/δ) ∈ [−1, 1]` — buys when
  the price is at least `δ` below the predicted level `q_n`, sells when it is at least `δ` above,
  fully (`|c_n| = 1`) at distance `2δ`; on day `n + 1` it closes the position (`−c_n` shares of
  `φ n`, a rank-`n` coefficient, legal on day `n + 1`). Its round trip is **world-independent**:
  `c_n · (P_{n+1}(φ_n) − P_n(φ_n))` (`roundTrip_value_eq`, shared with T7), and its net worth is
  that sum plus one open position (`frontRunner_netWorth`).
* **The e.c. certificate** `frontRunner_ec`, from FAF's machine capstones: the coefficient is built
  from constants, `max`, `+`, `×` and the price leaf (`MachineSpliceStream.serialize_*`,
  `.serialize_price`, `.serialize_const_write` on `MachineRatCodes.toMachineDigits`), the two
  trade frames from `MachineSpliceStream.tradeSlot` (at the identity ruler and at `n − 1`), the
  day-`0`/day-`n+1` split by `MachineSpliceStream.ifZero`, and `MachineSpliceStream.ec`. Never by
  substitution (`li-projection`'s OPEN route). Hypotheses: `MachineSentenceCodes φ`,
  `MachineRatCodes q` — FAF's own "e.c. sequence" classes.
* **T3.1 `frontRun_asympEq`** (kind P, load-bearing): over any `[0,1]`-market `P` with
  `NoEcExploit P DP` and a consistent world at every stage, if `P_{n+1}(φ_n) ≈ₙ q_n` (the push
  lands at the e.c.-predictable level) then `P_n(φ_n) ≈ₙ q_n` (it was already priced in). Proof:
  if not, some `ε > 0` has `|P_n(φ_n) − q_n| ≥ ε` infinitely often; with `δ ≤ ε/2` the trader's
  round trips are eventually all `≥ 0` and `≥ δ/2` on those days, so its plausible assessments are
  bounded below and unbounded above — exploitation, contradicting `hNE`.

**Fidelity (disclosed): `variant: conditional on the push landing`.** The hypothesis
`P_{n+1}(φ_n) ≈ₙ q_n` is the source's own premise ("the pushed price `q_n`") and *bakes in that the
push succeeds*: whether a push lands against the firm's budget-capped opposition is T10.1 (OPEN);
the retraction of Consequence 1 (line 85/93) is why this cannot be assumed away. **Asymptotic**:
`AsympEq` ignores every finite prefix, so the theorem says nothing about any *single* push being
absorbed "before" it arrives (the source's temporal claim is the rate T3.4, not attempted; see the
section "What T3.1 says on a constant sentence" below). The `H = 0` self-push instance is *related
to*, not an instance of, FAF's `lic_no_expected_net_update` (`thm:ceu`, `Properties/SelfTrust.lean`:
today's price equals today's *expectation* of the future price; T3.1 is about the realized next-day
price landing at an e.c. schedule — neither yields the other without "the expectation of an
e.c.-predictable future price is the predicted value", which is not in the package).

**`hworld` is necessary**: over a process with an inconsistent stage, `Trader.Exploits` is refutable
for every trader (finitely many plausible assessments), so `NoEcExploit` holds of every market and
the conclusion would fail; FAF's property theorems all take it.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional Filter Topology

/-! ## The round trip -/

/-- **The round trip is world-independent**: buying `e` shares at `p₀` and selling them at `p₁`
nets `e · (p₁ − p₀)` whatever the payout `w` — the pure-arithmetic core shared by T3 and T7.
Source: line 77 ("buys today and sells tomorrow"); mandate T3.1 (`roundTrip_value_eq`)
Kind: L
Fidelity: exact -/
theorem roundTrip_value_eq (e p₀ p₁ w : ℝ) : e * (w - p₀) - e * (w - p₁) = e * (p₁ - p₀) := by
  ring

/-! ## The coefficient features -/

/-- The buy ramp: `clip₀₁((q_n − δ − P_n(φ_n)) / δ)` — `1` at least `2δ` below the predicted level,
`0` from `δ` below it.
Source: mandate T3.1 (the `gradualEntry`-style ramp)
Kind: D
Fidelity: exact -/
def rampBelow (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (n : ℕ) : EF :=
  clip01 (.mul (.add (.const (q n)) (.add (.const (-δ)) (.mul (.const (-1)) (.price (φ n) n))))
    (.const (1 / δ)))

/-- The sell ramp: `clip₀₁((P_n(φ_n) − q_n − δ) / δ)` — `1` at least `2δ` above the predicted level,
`0` from `δ` above it.
Source: mandate T3.1 ("symmetrically sell when `P_n φ_n > q_n + δ`")
Kind: D
Fidelity: exact -/
def rampAbove (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (n : ℕ) : EF :=
  clip01 (.mul (.add (.price (φ n) n) (.add (.const (-δ)) (.mul (.const (-1)) (.const (q n)))))
    (.const (1 / δ)))

/-- The front-runner's day-`n` coefficient `c_n := rampBelow − rampAbove ∈ [−1, 1]`.
Source: mandate T3.1
Kind: D
Fidelity: exact -/
def frCoef (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (n : ℕ) : EF :=
  .add (rampBelow φ q δ n) (.mul (.const (-1)) (rampAbove φ q δ n))

/-- `rampBelow` denotes `max 0 (min 1 ((q_n − δ − P_n(φ_n)) · (1/δ)))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rampBelow_denote (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (n : ℕ) (P : History) :
    (rampBelow φ q δ n).denote P =
      max 0 (min 1 (((q n : ℝ) - δ - P n (φ n)) * (1 / (δ : ℝ)))) := by
  simp only [rampBelow, clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const,
    EF.denote_price, Pi.mul_apply, Pi.add_apply]
  congr 2
  push_cast
  ring

/-- `rampAbove` denotes `max 0 (min 1 ((P_n(φ_n) − δ − q_n) · (1/δ)))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rampAbove_denote (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (n : ℕ) (P : History) :
    (rampAbove φ q δ n).denote P =
      max 0 (min 1 ((P n (φ n) - δ - (q n : ℝ)) * (1 / (δ : ℝ)))) := by
  simp only [rampAbove, clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const,
    EF.denote_price, Pi.mul_apply, Pi.add_apply]
  congr 2
  push_cast
  ring

/-- `frCoef` denotes `rampBelow − rampAbove`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frCoef_denote (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (n : ℕ) (P : History) :
    (frCoef φ q δ n).denote P = (rampBelow φ q δ n).denote P - (rampAbove φ q δ n).denote P := by
  simp only [frCoef, EF.denote, EF.denoteWith]
  push_cast
  ring

/-- The ramps lie in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma clipVal_mem_Icc (x : ℝ) : 0 ≤ max 0 (min 1 x) ∧ max 0 (min 1 x) ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- `|c_n| ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma abs_frCoef_le_one (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (n : ℕ) (P : History) :
    |(frCoef φ q δ n).denote P| ≤ 1 := by
  rw [frCoef_denote, rampBelow_denote, rampAbove_denote]
  obtain ⟨h1, h2⟩ := clipVal_mem_Icc (((q n : ℝ) - δ - P n (φ n)) * (1 / (δ : ℝ)))
  obtain ⟨h3, h4⟩ := clipVal_mem_Icc ((P n (φ n) - δ - (q n : ℝ)) * (1 / (δ : ℝ)))
  rw [abs_le]
  constructor <;> linarith

/-- A positive coefficient means the price is more than `δ` below the predicted level.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frCoef_pos_imp (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ) (n : ℕ) (P : History)
    (h : 0 < (frCoef φ q δ n).denote P) : P n (φ n) < (q n : ℝ) - δ := by
  rw [frCoef_denote, rampBelow_denote, rampAbove_denote] at h
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨h3, _⟩ := clipVal_mem_Icc ((P n (φ n) - δ - (q n : ℝ)) * (1 / (δ : ℝ)))
  have hrb : 0 < max 0 (min 1 (((q n : ℝ) - δ - P n (φ n)) * (1 / (δ : ℝ)))) := by linarith
  have harg : 0 < ((q n : ℝ) - δ - P n (φ n)) * (1 / (δ : ℝ)) := by
    by_contra hle
    rw [not_lt] at hle
    have : min 1 (((q n : ℝ) - δ - P n (φ n)) * (1 / (δ : ℝ))) ≤ 0 := le_trans (min_le_right _ _) hle
    rw [max_eq_left this] at hrb
    exact lt_irrefl _ hrb
  have hinv : (0 : ℝ) < 1 / (δ : ℝ) := by positivity
  have := pos_of_mul_pos_left harg hinv.le
  linarith

/-- A negative coefficient means the price is more than `δ` above the predicted level.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frCoef_neg_imp (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ) (n : ℕ) (P : History)
    (h : (frCoef φ q δ n).denote P < 0) : (q n : ℝ) + δ < P n (φ n) := by
  rw [frCoef_denote, rampBelow_denote, rampAbove_denote] at h
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨h1, _⟩ := clipVal_mem_Icc (((q n : ℝ) - δ - P n (φ n)) * (1 / (δ : ℝ)))
  have hra : 0 < max 0 (min 1 ((P n (φ n) - δ - (q n : ℝ)) * (1 / (δ : ℝ)))) := by linarith
  have harg : 0 < (P n (φ n) - δ - (q n : ℝ)) * (1 / (δ : ℝ)) := by
    by_contra hle
    rw [not_lt] at hle
    have : min 1 ((P n (φ n) - δ - (q n : ℝ)) * (1 / (δ : ℝ))) ≤ 0 := le_trans (min_le_right _ _) hle
    rw [max_eq_left this] at hra
    exact lt_irrefl _ hra
  have hinv : (0 : ℝ) < 1 / (δ : ℝ) := by positivity
  have := pos_of_mul_pos_left harg hinv.le
  linarith

/-- At least `2δ` below the predicted level the coefficient is exactly `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frCoef_eq_one (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ) (n : ℕ) (P : History)
    (h : P n (φ n) ≤ (q n : ℝ) - 2 * δ) : (frCoef φ q δ n).denote P = 1 := by
  rw [frCoef_denote, rampBelow_denote, rampAbove_denote]
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hb : 1 ≤ ((q n : ℝ) - δ - P n (φ n)) * (1 / (δ : ℝ)) := by
    rw [← div_eq_mul_one_div, le_div_iff₀ hδ']
    linarith
  have ha : (P n (φ n) - δ - (q n : ℝ)) * (1 / (δ : ℝ)) ≤ 0 := by
    rw [← div_eq_mul_one_div, div_nonpos_iff]
    right
    exact ⟨by linarith, hδ'.le⟩
  rw [min_eq_left hb, max_eq_right zero_le_one,
    max_eq_left (le_trans (min_le_right _ _) ha)]
  ring

/-- At least `2δ` above the predicted level the coefficient is exactly `−1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frCoef_eq_neg_one (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ) (n : ℕ) (P : History)
    (h : (q n : ℝ) + 2 * δ ≤ P n (φ n)) : (frCoef φ q δ n).denote P = -1 := by
  rw [frCoef_denote, rampBelow_denote, rampAbove_denote]
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have ha : 1 ≤ (P n (φ n) - δ - (q n : ℝ)) * (1 / (δ : ℝ)) := by
    rw [← div_eq_mul_one_div, le_div_iff₀ hδ']
    linarith
  have hb : ((q n : ℝ) - δ - P n (φ n)) * (1 / (δ : ℝ)) ≤ 0 := by
    rw [← div_eq_mul_one_div, div_nonpos_iff]
    right
    exact ⟨by linarith, hδ'.le⟩
  rw [min_eq_left ha, max_eq_right zero_le_one,
    max_eq_left (le_trans (min_le_right _ _) hb)]
  ring

/-- The coefficient has rank `≤ n` (one price leaf at day `n`, constants otherwise).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frCoef_rank_le (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (n : ℕ) :
    (frCoef φ q δ n).rank ≤ n := by
  simp [frCoef, rampBelow, rampAbove, clip01, efMin, EF.rank]

/-! ## The front-running trader -/

/-- **The front-running trader.** Day `0`: `c_0` shares of `φ 0`. Day `n + 1`: `c_{n+1}` shares of
`φ (n+1)` and `−c_n` shares of `φ n` (closing yesterday's position; `c_n` has rank `n ≤ n + 1`).
Source: line 77 ("buys today and sells tomorrow"); mandate T3.1
Kind: D
Fidelity: exact (two-sided: buys below, sells above) -/
def frontRunner (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) : Trader where
  strat n :=
    match n with
    | 0 => { trades := [(frCoef φ q δ 0, φ 0)]
             rank_le := by
               intro p hp
               rw [List.mem_singleton] at hp
               subst hp
               exact frCoef_rank_le φ q δ 0 }
    | n + 1 => { trades := [(frCoef φ q δ (n + 1), φ (n + 1)),
                            (.mul (.const (-1)) (frCoef φ q δ n), φ n)]
                 rank_le := by
                   intro p hp
                   simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                   rcases hp with rfl | rfl
                   · exact frCoef_rank_le φ q δ (n + 1)
                   · simp only [EF.rank_mul, EF.rank_const, Nat.zero_max]
                     exact le_trans (frCoef_rank_le φ q δ n) (Nat.le_succ n) }

/-- The round-trip gain of the position opened on day `i`: `c_i · (P_{i+1}(φ_i) − P_i(φ_i))`.
World-independent.
Source: mandate T3.1
Kind: D
Fidelity: exact -/
noncomputable def frGain (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (P : History) (i : ℕ) : ℝ :=
  (frCoef φ q δ i).denote P * (P (i + 1) (φ i) - P i (φ i))

/-- The closed round trips through day `n`: `∑_{i < n} frGain i` — the front-runner's
mark-to-market.
Source: mandate T3.1
Kind: D
Fidelity: exact -/
noncomputable def frSum (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (P : History) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, frGain φ q δ P i

/-- Day `0` value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frontRunner_value_zero (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (P : History) (w : Valuation) :
    ((frontRunner φ q δ).strat 0).value P w =
      (frCoef φ q δ 0).denote P * (w (φ 0) - P 0 (φ 0)) := by
  simp [frontRunner, Strategy.value]

/-- Day `n + 1` value: the new position minus the closing of yesterday's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frontRunner_value_succ (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (P : History) (w : Valuation)
    (n : ℕ) :
    ((frontRunner φ q δ).strat (n + 1)).value P w =
      (frCoef φ q δ (n + 1)).denote P * (w (φ (n + 1)) - P (n + 1) (φ (n + 1))) -
        (frCoef φ q δ n).denote P * (w (φ n) - P (n + 1) (φ n)) := by
  simp only [frontRunner, Strategy.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, EF.denote, EF.denoteWith]
  push_cast
  ring

/-- **The front-runner's net worth** is its closed round trips plus one open position:
`netWorth_n = ∑_{i<n} c_i (P_{i+1}(φ_i) − P_i(φ_i)) + c_n (w(φ_n) − P_n(φ_n))`.
Source: mandate T3.1
Kind: L
Fidelity: exact -/
theorem frontRunner_netWorth (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (P : History) (v : PCWorld)
    (n : ℕ) :
    (frontRunner φ q δ).netWorth P v n =
      frSum φ q δ P n + (frCoef φ q δ n).denote P * (v.payout (φ n) - P n (φ n)) := by
  induction n with
  | zero =>
      simp [Trader.netWorth, frSum, frontRunner_value_zero]
  | succ n ih =>
      unfold Trader.netWorth at ih ⊢
      rw [Finset.sum_range_succ, ih, frontRunner_value_succ]
      simp only [frSum, frGain, Finset.sum_range_succ]
      ring

/-! ## The e.c. certificate -/

/-- **The front-runner is efficiently computable** (FAF's `def:ec`), from the machine capstones:
coefficient stream from `serialize_const` / `serialize_const_write` (on `MachineRatCodes.toMachineDigits`)
/ `serialize_price` / `serialize_add` / `serialize_mul` / `serialize_clip01`, trade frames from
`tradeSlot` at the identity ruler and at `n − 1`, the day-`0` / day-`n+1` split by `ifZero`, and
`MachineSpliceStream.ec`. No substitution.
Source: line 77 ("whenever the push is efficiently predictable"); mandate T3.1 ("this certificate is the real work")
Kind: P
Fidelity: exact
Hyps: (a): `MachineSentenceCodes φ`, `MachineRatCodes q` are FAF's own e.c.-sequence classes -/
theorem frontRunner_ec (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) (q : ℕ → ℚ)
    (hq : MachineRatCodes q) (δ : ℚ) : EfficientlyComputable (frontRunner φ q δ) := by
  have hqc : MachineSpliceStream (fun n => (EF.const (q n)).serialize) :=
    MachineSpliceStream.serialize_const_write hq.toMachineDigits
  have hprice : MachineSpliceStream (fun n => (EF.price (φ n) n).serialize) :=
    MachineSpliceStream.serialize_price hφ UnaryRuler.id (MachineDigits.ofUnaryRuler UnaryRuler.id)
  have hcd : MachineSpliceStream (fun _ : ℕ => (EF.const (-δ)).serialize) :=
    MachineSpliceStream.serialize_const (-δ)
  have hc1 : MachineSpliceStream (fun _ : ℕ => (EF.const (-1)).serialize) :=
    MachineSpliceStream.serialize_const (-1)
  have hcinv : MachineSpliceStream (fun _ : ℕ => (EF.const (1 / δ)).serialize) :=
    MachineSpliceStream.serialize_const (1 / δ)
  have hrb : MachineSpliceStream (fun n => (rampBelow φ q δ n).serialize) :=
    MachineSpliceStream.serialize_clip01
      (MachineSpliceStream.serialize_mul
        (MachineSpliceStream.serialize_add hqc
          (MachineSpliceStream.serialize_add hcd (MachineSpliceStream.serialize_mul hc1 hprice)))
        hcinv)
  have hra : MachineSpliceStream (fun n => (rampAbove φ q δ n).serialize) :=
    MachineSpliceStream.serialize_clip01
      (MachineSpliceStream.serialize_mul
        (MachineSpliceStream.serialize_add hprice
          (MachineSpliceStream.serialize_add hcd (MachineSpliceStream.serialize_mul hc1 hqc)))
        hcinv)
  have hcoef : MachineSpliceStream (fun n => (frCoef φ q δ n).serialize) :=
    MachineSpliceStream.serialize_add hrb (MachineSpliceStream.serialize_mul hc1 hra)
  have hpred : UnaryRuler (fun n : ℕ => n - 1) := UnaryRuler.id.sub (UnaryRuler.const 1)
  have hframe₀ : MachineSpliceStream (fun n => [6, Encodable.encode (φ n)]) :=
    (MachineSpliceStream.tradeSlot hφ UnaryRuler.id).of_eq (fun _ => rfl)
  have hframe₁ : MachineSpliceStream (fun n => [6, Encodable.encode (φ (n - 1))]) :=
    (MachineSpliceStream.tradeSlot hφ hpred).of_eq (fun _ => rfl)
  have hsell : MachineSpliceStream
      (fun n => (EF.mul (EF.const (-1)) (frCoef φ q δ (n - 1))).serialize) :=
    MachineSpliceStream.serialize_mul hc1 (hcoef.comp hpred)
  have hs₀ : MachineSpliceStream
      (fun n => (frCoef φ q δ n).serialize ++ [6, Encodable.encode (φ n)]) :=
    hcoef.append hframe₀
  have hs₁ : MachineSpliceStream
      (fun n => (frCoef φ q δ n).serialize ++ [6, Encodable.encode (φ n)] ++
        ((EF.mul (EF.const (-1)) (frCoef φ q δ (n - 1))).serialize ++
          [6, Encodable.encode (φ (n - 1))])) :=
    (hcoef.append hframe₀).append (hsell.append hframe₁)
  refine MachineSpliceStream.ec _
    ((MachineSpliceStream.ifZero hs₀ hs₁ UnaryRuler.id).of_eq fun n => ?_)
  cases n with
  | zero => simp [frontRunner, serializeTrades]
  | succ n => simp [frontRunner, serializeTrades]

/-! ## Exploitation from a world-independent core -/

/-- **Exploitation from a decomposition.** A trader whose net worth is, in every world, within `1`
of a world-independent sequence `S` that is bounded below and unbounded above exploits the market
(given a consistent world at every stage). The engine of T3.1.
Source: none: infrastructure (FAF's `exploits_of_bddBelow_of_unbounded` behind a decomposition)
Kind: L
Fidelity: n/a -/
theorem exploits_of_decomposition (T : Trader) (P : History) (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (S : ℕ → ℝ) (C : ℝ)
    (hdiff : ∀ (n : ℕ) (v : PCWorld), |T.netWorth P v n - S n| ≤ 1)
    (hlow : ∀ n, -C ≤ S n) (hunb : ∀ B : ℝ, ∃ n, B < S n) : T.Exploits P DP := by
  apply exploits_of_bddBelow_of_unbounded T P DP (C + 1)
  · rintro x ⟨n, v, _, rfl⟩
    have h := abs_le.mp (hdiff n v)
    linarith [hlow n]
  · intro B
    obtain ⟨n, hn⟩ := hunb (B + 1)
    obtain ⟨v, hv⟩ := hworld n
    refine ⟨T.netWorth P v n, ⟨n, v, hv, rfl⟩, ?_⟩
    have h := abs_le.mp (hdiff n v)
    linarith

/-! ## T3.1 — front-running -/

/-- Each round trip is at least `−1` on a `[0,1]`-market (`|c_i| ≤ 1`, price moves in `[−1, 1]`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frGain_ge_neg_one (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (P : History)
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (i : ℕ) : -1 ≤ frGain φ q δ P i := by
  unfold frGain
  have hc := abs_le.mp (abs_frCoef_le_one φ q δ i P)
  have h1 := hrange (i + 1) (φ i)
  have h2 := hrange i (φ i)
  nlinarith

/-- Once the landing is within `δ/2` of the prediction, a round trip never loses.
Source: mandate T3.1 (proof sketch)
Kind: L
Fidelity: n/a -/
lemma frGain_nonneg (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ) (P : History) (i : ℕ)
    (hland : |P (i + 1) (φ i) - q i| < (δ : ℝ) / 2) : 0 ≤ frGain φ q δ P i := by
  unfold frGain
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hl := abs_lt.mp hland
  rcases lt_trichotomy ((frCoef φ q δ i).denote P) 0 with hc | hc | hc
  · have hx := frCoef_neg_imp φ q δ hδ i P hc
    exact mul_nonneg_of_nonpos_of_nonpos hc.le (by linarith)
  · rw [hc, zero_mul]
  · have hx := frCoef_pos_imp φ q δ hδ i P hc
    exact mul_nonneg hc.le (by linarith)

/-- Once the landing is within `δ/2` of the prediction, a day at distance `≥ 2δ` from it gains at
least `δ/2` on the round trip.
Source: mandate T3.1 (proof sketch)
Kind: L
Fidelity: n/a -/
lemma frGain_ge_of_far (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (hδ : 0 < δ) (P : History) (i : ℕ)
    (hland : |P (i + 1) (φ i) - q i| < (δ : ℝ) / 2)
    (hfar : 2 * (δ : ℝ) ≤ |P i (φ i) - q i|) : (δ : ℝ) / 2 ≤ frGain φ q δ P i := by
  unfold frGain
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hl := abs_lt.mp hland
  rcases le_abs'.mp hfar with h | h
  · rw [frCoef_eq_one φ q δ hδ i P (by linarith)]
    linarith
  · rw [frCoef_eq_neg_one φ q δ hδ i P (by linarith)]
    linarith

/-- The round-trip sum is bounded below by `−min n N₀` when round trips are nonnegative from `N₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frSum_ge (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (P : History)
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (N₀ : ℕ)
    (hnn : ∀ i, N₀ ≤ i → 0 ≤ frGain φ q δ P i) (n : ℕ) :
    -((min n N₀ : ℕ) : ℝ) ≤ frSum φ q δ P n := by
  induction n with
  | zero => simp [frSum]
  | succ n ih =>
      unfold frSum at ih ⊢
      rw [Finset.sum_range_succ]
      by_cases h : n < N₀
      · have hmin : min (n + 1) N₀ = n + 1 := Nat.min_eq_left h
        have hmin' : min n N₀ = n := Nat.min_eq_left h.le
        rw [hmin]
        rw [hmin'] at ih
        have := frGain_ge_neg_one φ q δ P hrange n
        push_cast
        linarith
      · have h' : N₀ ≤ n := Nat.le_of_not_lt h
        have hmin : min (n + 1) N₀ = N₀ := Nat.min_eq_right (by omega)
        have hmin' : min n N₀ = N₀ := Nat.min_eq_right h'
        rw [hmin]
        rw [hmin'] at ih
        have := hnn n h'
        linarith

/-- The round-trip sum is monotone from `N₀` on when round trips are nonnegative from `N₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frSum_mono (φ : ℕ → Sentence) (q : ℕ → ℚ) (δ : ℚ) (P : History) (N₀ : ℕ)
    (hnn : ∀ i, N₀ ≤ i → 0 ≤ frGain φ q δ P i) {n m : ℕ} (hn : N₀ ≤ n) (hnm : n ≤ m) :
    frSum φ q δ P n ≤ frSum φ q δ P m := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
      unfold frSum at ih ⊢
      rw [Finset.sum_range_succ]
      have := hnn m (le_trans hn hm)
      linarith

/-- **T3.1 — front-running.** Over any `[0,1]`-market `P` that no e.c. trader exploits (relative to a
process with a consistent world at every stage): for an e.c. sentence family `φ` and an e.c.
rational schedule `q`, if tomorrow's price of today's sentence lands at the schedule,
`P_{n+1}(φ_n) ≈ₙ q_n`, then today's price is already there, `P_n(φ_n) ≈ₙ q_n`. "A corrigible agent
already believes what it expects to be legitimately taught", as a theorem shape — **asymptotically**:
`AsympEq` ignores every finite prefix, so this says nothing about any *single* push being absorbed
"before" it arrives (the source's temporal claim is the rate T3.4, not attempted); on a constant
sentence its content is a constraint on the landings that are possible at all
(`landing_increments_vanish`). The exploiting trader is `frontRunner φ q δ` with its certificate
`frontRunner_ec`. Single-market.
Source: line 77 (Consequence 2); corr-core-043; bli-soto-b-057; audit row 2.4; mandate T3.1
Kind: P
Fidelity: variant: conditional on the push landing — the hypothesis `P_{n+1}(φ_n) ≈ₙ q_n` is the source's own premise ("the pushed price `q_n`") and bakes in that the push succeeds (whether it does, against the firm's budgeted opposition, is T10.1 OPEN); asymptotic (no single-push claim); the `H = 0` self-push instance is *related to*, not an instance of, FAF's `lic_no_expected_net_update` (`thm:ceu`)
Hyps: (a) throughout: `hNE` is the no-exploit predicate (derived for the exo-market by `noEcExploit_of_boundedLoss`), `hworld`/`hrange` are the standard market hypotheses, `hφ`/`hq` are FAF's e.c.-sequence classes, `hland` is the premise -/
theorem frontRun_asympEq (P : History) (DP : DeductiveProcess) (hNE : NoEcExploit P DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ) (q : ℕ → ℚ) (hq : MachineRatCodes q)
    (hland : AsympEq (fun n => P (n + 1) (φ n)) (fun n => (q n : ℝ))) :
    AsympEq (fun n => P n (φ n)) (fun n => (q n : ℝ)) := by
  by_contra hnot
  -- the failure: some `ε` is exceeded infinitely often
  have hfreq : ∃ ε : ℝ, 0 < ε ∧ ∀ N, ∃ n, N ≤ n ∧ ε ≤ |P n (φ n) - q n| := by
    unfold AsympEq at hnot
    rw [Metric.tendsto_atTop] at hnot
    simp only [not_forall, not_exists, not_lt, Real.dist_eq, sub_zero] at hnot
    obtain ⟨ε, hε, h⟩ := hnot
    exact ⟨ε, hε, fun N => by
      obtain ⟨n, hn, h'⟩ := h N
      exact ⟨n, hn, h'⟩⟩
  obtain ⟨ε, hε, hfreq⟩ := hfreq
  -- a rational `δ ∈ (0, ε/2]`
  obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℚ, 0 < δ ∧ (δ : ℝ) ≤ ε / 2 := by
    obtain ⟨δ, h1, h2⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 2 by linarith)
    exact ⟨δ, by exact_mod_cast h1, h2.le⟩
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  -- the landing is within `δ/2` from `N₀` on
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n, N₀ ≤ n → |P (n + 1) (φ n) - q n| < (δ : ℝ) / 2 := by
    unfold AsympEq at hland
    rw [Metric.tendsto_atTop] at hland
    obtain ⟨N, hN⟩ := hland ((δ : ℝ) / 2) (by positivity)
    exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
  have hnn : ∀ i, N₀ ≤ i → 0 ≤ frGain φ q δ P i :=
    fun i hi => frGain_nonneg φ q δ hδ0 P i (hN₀ i hi)
  -- the trader exploits
  apply hNE (frontRunner φ q δ) (frontRunner_ec φ hφ q hq δ)
  apply exploits_of_decomposition _ P DP hworld (frSum φ q δ P) N₀
  · intro n v
    rw [frontRunner_netWorth, add_sub_cancel_left, abs_mul]
    have hc := abs_frCoef_le_one φ q δ n P
    have hp := hrange n (φ n)
    have hw := payout_mem_Icc v (φ n)
    have hd : |v.payout (φ n) - P n (φ n)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc |(frCoef φ q δ n).denote P| * |v.payout (φ n) - P n (φ n)|
        ≤ 1 * 1 := mul_le_mul hc hd (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro n
    have h := frSum_ge φ q δ P hrange N₀ hnn n
    have hmin : ((min n N₀ : ℕ) : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast min_le_right n N₀
    linarith
  · -- unbounded above: `k` far days from `N₀` on contribute `k · δ/2`
    have hstep : ∀ k : ℕ, ∃ n, N₀ ≤ n ∧ -(N₀ : ℝ) + k * ((δ : ℝ) / 2) ≤ frSum φ q δ P n := by
      intro k
      induction k with
      | zero =>
          refine ⟨N₀, le_rfl, ?_⟩
          have h := frSum_ge φ q δ P hrange N₀ hnn N₀
          simp only [min_self] at h
          simpa using h
      | succ k ih =>
          obtain ⟨n, hn, hsum⟩ := ih
          obtain ⟨m, hm, hfar⟩ := hfreq n
          have hfar' : 2 * (δ : ℝ) ≤ |P m (φ m) - q m| := le_trans (by linarith) hfar
          have hgain := frGain_ge_of_far φ q δ hδ0 P m (hN₀ m (le_trans hn hm)) hfar'
          have hmono := frSum_mono φ q δ P N₀ hnn hn hm
          refine ⟨m + 1, by omega, ?_⟩
          unfold frSum at hmono hsum ⊢
          rw [Finset.sum_range_succ]
          push_cast
          linarith
    intro B
    obtain ⟨k, hk⟩ := exists_nat_gt ((B + N₀) / ((δ : ℝ) / 2))
    obtain ⟨n, _, hsum⟩ := hstep k
    refine ⟨n, ?_⟩
    have hpos : (0 : ℝ) < (δ : ℝ) / 2 := by positivity
    have hk' : B + N₀ < k * ((δ : ℝ) / 2) := by
      rwa [div_lt_iff₀ hpos] at hk
    linarith

/-! ## What T3.1 says on a constant sentence — and what it does not (repair round 1)

On a *constant* sentence family the asymptotic statement cannot see any single push: `AsympEq`
ignores every finite prefix, and against an eventually-constant schedule the premise and the
conclusion are the same proposition for every history (`asympEq_shift_iff_of_eventuallyConst`).
The content of T3.1 on a fixed sentence is a constraint on the *landings that are possible at
all*: a schedule that tomorrow's price tracks must have vanishing increments
(`landing_increments_vanish`), so an e.c. schedule with non-vanishing increments is refuted as a
landing on every no-exploit market (`no_landing_of_increments`; the alternating schedule in
`Instances.lean`). The rate at which a single push is absorbed (T3.4) is not an asymptotic
statement and is not attempted (findings F7). -/

/-- **On a constant sentence against an eventually-constant schedule, T3.1's premise and
conclusion coincide for every history** — both say the price converges to the schedule's eventual
value, and limits are shift-invariant. This is why the one-jump witness `frontRun_witness`
(`Instances.lean`) is graded N−: it inhabits T3.1's hypothesis package but does not exercise the
exploitation argument (audit r1, B1).
Source: audit r1 B1 (both lenses); mandate T3.2
Kind: L
Fidelity: n/a -/
theorem asympEq_shift_iff_of_eventuallyConst (P : History) (ψ : Sentence) (q : ℕ → ℚ) (N : ℕ)
    (hq : ∀ n, N ≤ n → q n = q N) :
    AsympEq (fun n => P (n + 1) ψ) (fun n => (q n : ℝ)) ↔
      AsympEq (fun n => P n ψ) (fun n => (q n : ℝ)) := by
  have key : ∀ f : ℕ → ℝ, AsympEq f (fun n => (q n : ℝ)) ↔ Tendsto f atTop (𝓝 (q N : ℝ)) := by
    intro f
    unfold AsympEq
    have h1 : (fun n => f n - (q n : ℝ)) =ᶠ[atTop] (fun n => f n - (q N : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      rw [hq n hn]
    rw [Filter.tendsto_congr' h1]
    exact tendsto_sub_nhds_zero_iff
  rw [key, key]
  exact Filter.tendsto_add_atTop_iff_nat (f := fun n => P n ψ) 1

/-- **T3.1 on a constant sentence: a predictable landing must have vanishing increments.** Over
any `[0,1]`-market no e.c. trader exploits (consistent world at every stage), if tomorrow's price
of the fixed sentence `ψ` tracks the e.c. schedule `q`, then `q_{n+1} − q_n → 0`. This is the
content of `frontRun_asympEq` on a constant family — what it constrains is which schedules can be
landings at all, not when a given push is absorbed.
Source: line 77 (Consequence 2) read on a fixed sentence; audit r1 B1 (the content form)
Kind: C
Fidelity: variant: constant sentence family; conditional on the landing (as T3.1)
Hyps: (a) as T3.1 -/
theorem landing_increments_vanish (P : History) (DP : DeductiveProcess) (hNE : NoEcExploit P DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (ψ : Sentence) (q : ℕ → ℚ) (hq : MachineRatCodes q)
    (hland : AsympEq (fun n => P (n + 1) ψ) (fun n => (q n : ℝ))) :
    Tendsto (fun n => (q (n + 1) : ℝ) - q n) atTop (𝓝 0) := by
  have hc := frontRun_asympEq P DP hNE hworld hrange (fun _ => ψ) (MachineSentenceCodes.const ψ)
    q hq hland
  unfold AsympEq at hc hland
  have hc' : Tendsto (fun n => P (n + 1) ψ - (q (n + 1) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun n => P n ψ - (q n : ℝ)) 1).mpr hc
  have h := hland.sub hc'
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards with n
  ring

/-- **The refutation shape**: an e.c. schedule whose increments stay `≥ ε > 0` is *not* a landing
on any no-exploit market — tomorrow's price of a fixed sentence cannot track it. The non-vacuity
check of T3.1 on a constant sentence is this impossibility (its instance at the alternating
schedule is `no_landing_altSchedule`, `Instances.lean`), not an inhabitation.
Source: audit r1 B1; mandate T3.2
Kind: C
Fidelity: variant: constant sentence family (contrapositive of `landing_increments_vanish`)
Hyps: (a) as T3.1; `hinc` is the non-vanishing of the increments -/
theorem no_landing_of_increments (P : History) (DP : DeductiveProcess) (hNE : NoEcExploit P DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (ψ : Sentence) (q : ℕ → ℚ) (hq : MachineRatCodes q)
    (ε : ℝ) (hε : 0 < ε) (hinc : ∀ n, ε ≤ |(q (n + 1) : ℝ) - q n|) :
    ¬ AsympEq (fun n => P (n + 1) ψ) (fun n => (q n : ℝ)) := by
  intro hland
  have h := landing_increments_vanish P DP hNE hworld hrange ψ q hq hland
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h ε hε
  have := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at this
  exact absurd (hinc N) (not_le.mpr this)

/-! ## `hworld` is necessary (findings F9.2, now checked) -/

/-- **Over a process with an inconsistent stage, no trader exploits any `[0,1]`-market**: once some
`D n₀` has no model, no later stage has one (`DeductiveProcess.mono_le`), so every plausible
assessment comes from a day `< n₀` and is bounded by the partial magnitude through day `n₀`
(`Trader.abs_netWorth_le_partialMagnitude`). Hence `NoEcExploit` holds of every such market, and
T3.1's conclusion would fail without `hworld` — the reason the hypothesis was added to the
mandate's signature (F9.2).
Source: findings F9.2; audit r1 N7 (fidelity)
Kind: L
Fidelity: n/a -/
theorem not_exploits_of_inconsistent_stage (P : History) (DP : DeductiveProcess)
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n₀ : ℕ)
    (hinc : ∀ v : PCWorld, ¬ v.ConsistentWith (DP.D n₀)) (T : Trader) : ¬ T.Exploits P DP := by
  rintro ⟨_, hnot⟩
  apply hnot
  refine ⟨∑ i ∈ Finset.range (n₀ + 1), (T.strat i).magnitude P, ?_⟩
  rintro x ⟨n, v, hv, rfl⟩
  have hn : n < n₀ :=
    lt_of_not_ge fun hge => hinc v (fun φ hφ => hv φ (DP.mono_le hge hφ))
  calc T.netWorth P v n ≤ |T.netWorth P v n| := le_abs_self _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (T.strat i).magnitude P :=
        T.abs_netWorth_le_partialMagnitude P v hrange n
    _ ≤ ∑ i ∈ Finset.range (n₀ + 1), (T.strat i).magnitude P := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_range] at hi ⊢
          omega
        · intro i _ _
          exact Strategy.magnitude_nonneg _ _

/-- `NoEcExploit` holds of every `[0,1]`-market over a process with an inconsistent stage.
Source: findings F9.2
Kind: L
Fidelity: n/a -/
theorem noEcExploit_of_inconsistent_stage (P : History) (DP : DeductiveProcess)
    (hrange : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n₀ : ℕ)
    (hinc : ∀ v : PCWorld, ¬ v.ConsistentWith (DP.D n₀)) : NoEcExploit P DP :=
  fun T _ => not_exploits_of_inconsistent_stage P DP hrange n₀ hinc T

end Cleanroom.Corrigibility.CorrExoTrader
