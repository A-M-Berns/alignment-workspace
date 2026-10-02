import Cleanroom.Corrigibility.CorrExoTrader.Defs
import LogicalInduction.Construction.Budgeter

/-!
# `corr-exo-trader` · Budget: budget exhaustion of a standing Occam position (T6)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 5 of the
layout. Imports FAF's `Construction/Budgeter` only (not `LIA`). Over FAF's own `budgetedTrader` /
`priorBudgetBreach` / `BudgeterAt`.

The source (line 113, the corrected form after the retraction of line 75's "unopposed"): "a
standing Occam position against a persistent push consumes budget monotonically and is exhausted
after finite exposure; it is refinanced only by round-trips, which require the price to
oscillate."

* **T6.1 `occam_exhausted`** (kind P, load-bearing): the Occam trader `constBuyer φ c` (buys `c > 0`
  shares of `φ` daily, coefficient a *constant* — "likes the stock regardless of return", line 105)
  with budget `b : ℕ` (unrestricted; `b = 0` is consistent), against any rational quote table `Q` that from day `N` on prices `φ` at
  `≥ p + δ > 0`, on a process with a `¬φ`-world plausible at every stage: FAF's bankruptcy test
  `priorBudgetBreach` is `true` from an explicit day `M := N + ⌈b / (c(p+δ))⌉ + 1` on, hence the
  budgeted position is the empty strategy forever after (`occam_silenced`). The bridge between the
  finite bit-table scan and the semantic plausible-world test is FAF's
  `priorBudgetBreach_eq_false_iff`, used in its negative direction.
* **T6.2** the N− contrast and the monotonicity: with zero prices the raw `¬φ`-worth does not fall
  (`occam_worth_const_of_zero_price`); for the pure buyer the `¬φ`-worth is antitone in the day
  (`occam_worth_antitone`) — it is never refinanced, because a constant buyer never sells. The
  source's "refinanced only by round-trips" is a statement about *all* traders; its rendering
  for a trader that does sell is the mark-to-market decomposition (`Undecided.lean`). Fidelity
  weaker.
* **T6.3** (finding, in `corr-exo-trader-findings.md`): Consequence 1 as first stated (line 75) was
  retracted; only the corrected decomposition is formalized; T6.1's ledger row quotes line 113.

Hypotheses of T6.1: all (a) at instantiation — `hQ0` (prices nonnegative) holds for every
`RationalBeliefState` quote table (e.g. `exoQuote`), `hundec` is derived from freshness exactly as
`li-projection`'s `exists_consistent_not_holds_atom` does (for `φ := utilityAtom` over a
cleanroom-free process), and `hpush` is the persistent push itself.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional

/-- The real history cast from a rational quote table.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def castHistory (Q : ℕ → Sentence → ℚ) : History := fun n φ => (Q n φ : ℝ)

/-- `castHistory Q` is the cast of `Q` (the `hQ` hypothesis of FAF's budgeter lemmas).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma castHistory_eq (Q : ℕ → Sentence → ℚ) (n : ℕ) (φ : Sentence) :
    castHistory Q n φ = (Q n φ : ℝ) := rfl

/-- In a world refuting `φ`, the constant buyer's net worth is `−c · ∑_{i ≤ n} Q i φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma constBuyer_netWorth_refuting (φ : Sentence) (c : ℚ) (Q : ℕ → Sentence → ℚ) (v : PCWorld)
    (hv : ¬ v.Holds φ) (n : ℕ) :
    (constBuyer φ c).netWorth (castHistory Q) v n =
      -((c : ℝ) * ∑ i ∈ Finset.range (n + 1), (Q i φ : ℝ)) := by
  rw [constBuyer_netWorth, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PCWorld.payout, if_neg hv, castHistory_eq]
  ring

/-- Under a persistent push `Q i φ ≥ p + δ` from day `N` on, with nonnegative prices before, the
cumulative price through day `m ≥ N` is at least `(m + 1 − N) · (p + δ)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_price_ge_of_push (φ : Sentence) (Q : ℕ → Sentence → ℚ) (hQ0 : ∀ m, 0 ≤ Q m φ)
    (p δ : ℚ) (N : ℕ) (hpush : ∀ m, N ≤ m → p + δ ≤ Q m φ) (m : ℕ) :
    ((m + 1 - N : ℕ) : ℚ) * (p + δ) ≤ ∑ i ∈ Finset.range (m + 1), Q i φ := by
  have hsub : Finset.Ico N (m + 1) ⊆ Finset.range (m + 1) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    exact Finset.mem_range.mpr hi.2
  calc ((m + 1 - N : ℕ) : ℚ) * (p + δ)
      = (Finset.Ico N (m + 1)).card • (p + δ) := by
        rw [Nat.card_Ico, nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.Ico N (m + 1), Q i φ := by
        apply Finset.card_nsmul_le_sum
        intro i hi
        exact hpush i (Finset.mem_Ico.mp hi).1
    _ ≤ ∑ i ∈ Finset.range (m + 1), Q i φ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hQ0 i)

/-! ## T6.1 — the Occam position is exhausted after finite exposure -/

/-- **T6.1 — budget exhaustion.** The Occam trader `constBuyer φ c` (`c > 0` shares of `φ` daily,
constant coefficient) with budget `b : ℕ` (unrestricted — `hb : 0 < b` was dropped, F9.3), against a rational quote table `Q` with nonnegative
`φ`-prices that from day `N` on are `≥ p + δ` (`p ≥ 0`, `δ > 0`), on a process with a `¬φ`-world
plausible at every stage: FAF's bankruptcy test `priorBudgetBreach DP (constBuyer φ c) b Q n` is
`true` for every `n ≥ N + ⌈b / (c (p + δ))⌉₊ + 1`. In the `¬φ`-world the raw worth falls by at
least `c (p + δ)` a day from `N`, reaching `−b` by day `N + ⌈b / (c(p+δ))⌉₊`; FAF's
`priorBudgetBreach_eq_false_iff` (negative direction) turns the semantic breach into the scan's
verdict. "Likes the stock regardless of return": the coefficient is the constant `c`, not a price
feature. **The push enters only as the price floor `hpush`** (audit r1): no demand, no direction
and no dynamics appear in the statement — any positive floor exhausts the buyer
(`occam_exhausted_of_floor`; the constant `½` table, `occam_exhausted_half_table`), so this is a
fact about FAF's budgeter on a standing position in an undecidable, and "persistent pressure
*wins*" (the price goes where the push wants) is T10.1, OPEN. **Side of the push**: this trader
*buys* `φ`; the source's opposer of an upward push on `u` is the instance `φ := ∼u`
(`occam_exhausted_opposer`), whose floor hypothesis says the pushed price of `∼u` stays `≥ p + δ`.
Source: line 113 ("a standing Occam position against a persistent push consumes budget monotonically and is exhausted after finite exposure"); corr-core-049; bli-soto-b-056; mandate T6.1
Kind: P
Fidelity: exact (the day `M` is explicit; the "push" is a price floor)
Hyps: (a) at instantiation: `hQ0` holds for every `RationalBeliefState` quote table; `hundec` from freshness (`exists_consistent_not_holds_atom`); `hpush` is the push -/
theorem occam_exhausted (DP : DeductiveProcess) (φ : Sentence) (c : ℚ) (hc : 0 < c)
    (b : ℕ) (Q : ℕ → Sentence → ℚ) (hQ0 : ∀ m, 0 ≤ Q m φ)
    (hundec : ∀ m, ∃ v : PCWorld, v.ConsistentWith (DP.D m) ∧ ¬ v.Holds φ)
    (p δ : ℚ) (hp : 0 ≤ p) (hδ : 0 < δ) (N : ℕ) (hpush : ∀ m, N ≤ m → p + δ ≤ Q m φ) :
    ∀ n, N + ⌈(b : ℚ) / (c * (p + δ))⌉₊ + 1 ≤ n →
      priorBudgetBreach DP (constBuyer φ c) b Q n = true := by
  intro n hn
  set K := ⌈(b : ℚ) / (c * (p + δ))⌉₊ with hK
  set m := N + K with hm
  have hmn : m < n := by omega
  obtain ⟨v, hv, hvφ⟩ := hundec m
  have hpos : 0 < c * (p + δ) := mul_pos hc (by linarith)
  -- the semantic breach at day `m` in the `¬φ`-world
  have hworth : (constBuyer φ c).netWorth (castHistory Q) v m ≤ -(b : ℝ) := by
    rw [constBuyer_netWorth_refuting φ c Q v hvφ m]
    have hsum := sum_price_ge_of_push φ Q hQ0 p δ N hpush m
    have hcard : ((m + 1 - N : ℕ) : ℚ) = (K : ℚ) + 1 := by
      rw [hm, show N + K + 1 - N = K + 1 by omega]
      push_cast
      rfl
    rw [hcard] at hsum
    have hKge : (b : ℚ) / (c * (p + δ)) ≤ (K : ℚ) := Nat.le_ceil _
    have hb : (b : ℚ) ≤ (K : ℚ) * (c * (p + δ)) := by
      rwa [div_le_iff₀ hpos] at hKge
    have hmul : (b : ℚ) ≤ c * ∑ i ∈ Finset.range (m + 1), Q i φ := by
      calc (b : ℚ) ≤ (K : ℚ) * (c * (p + δ)) := hb
        _ ≤ ((K : ℚ) + 1) * (c * (p + δ)) := by nlinarith [hpos]
        _ = c * (((K : ℚ) + 1) * (p + δ)) := by ring
        _ ≤ c * ∑ i ∈ Finset.range (m + 1), Q i φ := by
            exact mul_le_mul_of_nonneg_left hsum hc.le
    have hmulR : (b : ℝ) ≤ (c : ℝ) * ∑ i ∈ Finset.range (m + 1), (Q i φ : ℝ) := by
      exact_mod_cast hmul
    linarith
  -- the scan agrees with the semantic test
  by_contra hfalse
  have hfalse' : priorBudgetBreach DP (constBuyer φ c) b Q n = false :=
    Bool.eq_false_iff.mpr hfalse
  have hsafe := (priorBudgetBreach_eq_false_iff DP (constBuyer φ c) b (castHistory Q) Q
    (fun _ _ => rfl) n).mp hfalse' m hmn v hv
  linarith

/-- Once the bankruptcy test fires, FAF's budgeter plays the empty strategy.
Source: none: infrastructure (`BudgeterAt`'s `if` branch, `Budgeter.lean`)
Kind: L
Fidelity: n/a -/
lemma BudgeterAt_eq_empty_of_breach (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) (h : priorBudgetBreach DP Tr b Q n = true) :
    BudgeterAt DP Tr b Q n = ⟨[], by simp⟩ := by
  simp [BudgeterAt, h]

/-- **The budgeted Occam position is silent forever after `M`**: from day
`M := N + ⌈b / (c (p + δ))⌉₊ + 1` on, the budgeted trader's day strategy is the empty strategy,
so its day value is `0` against every history in every world.
Source: line 113 ("exhausted after finite exposure"); mandate T6.1
Kind: C
Fidelity: exact
Hyps: (a) as `occam_exhausted` -/
theorem occam_silenced (DP : DeductiveProcess) (φ : Sentence) (c : ℚ) (hc : 0 < c)
    (b : ℕ) (Q : ℕ → Sentence → ℚ) (hQ0 : ∀ m, 0 ≤ Q m φ)
    (hundec : ∀ m, ∃ v : PCWorld, v.ConsistentWith (DP.D m) ∧ ¬ v.Holds φ)
    (p δ : ℚ) (hp : 0 ≤ p) (hδ : 0 < δ) (N : ℕ) (hpush : ∀ m, N ≤ m → p + δ ≤ Q m φ) :
    ∀ n, N + ⌈(b : ℚ) / (c * (p + δ))⌉₊ + 1 ≤ n →
      (budgetedTrader DP (constBuyer φ c) b Q).strat n = ⟨[], by simp⟩ ∧
      ∀ (P : History) (w : Valuation),
        ((budgetedTrader DP (constBuyer φ c) b Q).strat n).value P w = 0 := by
  intro n hn
  have hbr := occam_exhausted DP φ c hc b Q hQ0 hundec p δ hp hδ N hpush n hn
  have hstrat : (budgetedTrader DP (constBuyer φ c) b Q).strat n = ⟨[], by simp⟩ :=
    BudgeterAt_eq_empty_of_breach DP _ b Q n hbr
  refine ⟨hstrat, fun P w => ?_⟩
  rw [hstrat]
  simp [Strategy.value]

/-! ## T6.2 — the contrasts -/

/-- **The zero-price contrast**: with the `φ`-price identically `0` the constant buyer's `¬φ`-worth
does not fall — it is `0` on every day (no exposure, no exhaustion). Kind L (audit r2 fidelity
N4): a `simp` lemma that inhabits no hypothesis package, not a non-vacuity witness.
Source: line 113 (the push-free contrast); mandate T6.2
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem occam_worth_const_of_zero_price (φ : Sentence) (c : ℚ) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ m, Q m φ = 0) (v : PCWorld) (hv : ¬ v.Holds φ) (n : ℕ) :
    (constBuyer φ c).netWorth (castHistory Q) v n = 0 := by
  rw [constBuyer_netWorth_refuting φ c Q v hv n]
  simp [hQ]

/-- **The pure buyer is never refinanced**: in a world refuting `φ`, with nonnegative prices, the
constant buyer's net worth is antitone in the day — it can only fall. (A constant *buyer* never
sells, so no round trip ever closes a position; the source's "refinanced only by round-trips"
concerns traders that do sell, and for those the gain of a closed position is its mark-to-market
— `Undecided.lean`.)
Source: line 113 ("consumes budget monotonically … refinanced only by round-trips"); mandate T6.2
Kind: L
Fidelity: weaker: one trader (the constant buyer), one world type (refuting `φ`)
Hyps: (a) -/
theorem occam_worth_antitone (φ : Sentence) (c : ℚ) (hc : 0 ≤ c) (Q : ℕ → Sentence → ℚ)
    (hQ0 : ∀ m, 0 ≤ Q m φ) (v : PCWorld) (hv : ¬ v.Holds φ) (n : ℕ) :
    (constBuyer φ c).netWorth (castHistory Q) v (n + 1) ≤
      (constBuyer φ c).netWorth (castHistory Q) v n := by
  rw [constBuyer_netWorth_refuting φ c Q v hv, constBuyer_netWorth_refuting φ c Q v hv,
    Finset.sum_range_succ]
  have h0 : (0 : ℝ) ≤ (Q (n + 1) φ : ℝ) := by exact_mod_cast hQ0 (n + 1)
  have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  nlinarith

/-! ## Repair round 1 — the opposer's side, and the push as a mere floor -/

/-- **T6.1, the opposer's side.** The Occam trader that *opposes* an upward push on `φ` buys `∼φ`
(sells `φ`) — the source's "standing Occam position against a persistent push" (line 113). Its
exhaustion hypothesis reads `p + δ ≤ Q m (∼φ)` from `N` on: the push does not drive the price of
`∼φ` below `p + δ` (for a coherent table, the pushed price of `φ` stays `≤ 1 − p − δ`). In a
`φ`-world, plausible at every stage, the opposer's worth falls by `≥ c(p+δ)` a day and FAF's
bankruptcy test fires from the explicit day on. **Qualification of line 113**: if the push drives
`P(φ) → 1`, the opposer's daily loss `c · P_i(∼φ)` may be summable and exhaustion is *not*
guaranteed by this theorem.
Source: line 113 ("a standing Occam position against a persistent push"); audit r1 N1 (fidelity)
Kind: C
Fidelity: exact (T6.1 at `∼φ`; the push hypothesis is a floor on the price of `∼φ`)
Hyps: (a) as T6.1; `hplaus` (a `φ`-world plausible at every stage) from freshness at instantiation -/
theorem occam_exhausted_opposer (DP : DeductiveProcess) (φ : Sentence) (c : ℚ) (hc : 0 < c)
    (b : ℕ) (Q : ℕ → Sentence → ℚ) (hQ0 : ∀ m, 0 ≤ Q m (∼φ))
    (hplaus : ∀ m, ∃ v : PCWorld, v.ConsistentWith (DP.D m) ∧ v.Holds φ)
    (p δ : ℚ) (hp : 0 ≤ p) (hδ : 0 < δ) (N : ℕ) (hpush : ∀ m, N ≤ m → p + δ ≤ Q m (∼φ)) :
    ∀ n, N + ⌈(b : ℚ) / (c * (p + δ))⌉₊ + 1 ≤ n →
      priorBudgetBreach DP (constBuyer (∼φ) c) b Q n = true :=
  occam_exhausted DP (∼φ) c hc b Q hQ0
    (fun m => by
      obtain ⟨v, hv, hvφ⟩ := hplaus m
      exact ⟨v, hv, by rw [PCWorld.holds_neg]; exact fun h => h hvφ⟩)
    p δ hp hδ N hpush

/-- **The push enters T6.1 only as a price floor** (audit r1, N1 adversarial): any positive floor
`η` on the `φ`-price — no demand, no dynamics, no direction — exhausts the constant buyer from day
`⌈b / (cη)⌉₊ + 1` on. T6.1 is therefore a fact about FAF's budgeter on a standing position in an
undecidable; "pressure wins" (the price goes where the push wants) is T10.1, OPEN.
Source: audit r1 N1 (adversarial); line 113
Kind: N−
Fidelity: exact (T6.1 at `N = 0`, `p = 0`)
Hyps: (a) -/
theorem occam_exhausted_of_floor (DP : DeductiveProcess) (φ : Sentence) (c : ℚ) (hc : 0 < c)
    (b : ℕ) (Q : ℕ → Sentence → ℚ)
    (hundec : ∀ m, ∃ v : PCWorld, v.ConsistentWith (DP.D m) ∧ ¬ v.Holds φ)
    (η : ℚ) (hη : 0 < η) (hfloor : ∀ m, η ≤ Q m φ) :
    ∀ n, ⌈(b : ℚ) / (c * η)⌉₊ + 1 ≤ n → priorBudgetBreach DP (constBuyer φ c) b Q n = true := by
  intro n hn
  exact occam_exhausted DP φ c hc b Q (fun m => le_trans hη.le (hfloor m)) hundec 0 η le_rfl hη 0
    (fun m _ => by have := hfloor m; linarith) n (by simpa using hn)

/-- The constant `½` table — no demand at all — exhausts the Occam buyer: the honest N− inhabitation
of T6.1's hypothesis package.
Source: audit r1 N1 (adversarial)
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem occam_exhausted_half_table (DP : DeductiveProcess) (φ : Sentence) (c : ℚ) (hc : 0 < c)
    (b : ℕ) (hundec : ∀ m, ∃ v : PCWorld, v.ConsistentWith (DP.D m) ∧ ¬ v.Holds φ) :
    ∀ n, ⌈(b : ℚ) / (c * (1 / 2))⌉₊ + 1 ≤ n →
      priorBudgetBreach DP (constBuyer φ c) b (fun _ _ => (1 / 2 : ℚ)) n = true :=
  occam_exhausted_of_floor DP φ c hc b _ hundec (1 / 2) (by norm_num) (fun _ => le_rfl)

end Cleanroom.Corrigibility.CorrExoTrader
