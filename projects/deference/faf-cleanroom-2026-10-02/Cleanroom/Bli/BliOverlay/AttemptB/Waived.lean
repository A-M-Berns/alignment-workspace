import Cleanroom.Bli.BliOverlay.AttemptB.Subst
import LogicalInduction.Construction.TradingFirm

/-!
# `bli-overlay` (attempt B) · Waived: the waived-days lemma (T3)

* **T3(a)** `not_exploits_of_dayValue_le_off_finite` — a trader whose day-`n` value on a
  `[0,1]` history is at most `marketMakerError n = 2^{-(n+1)}` in **every** p.c. world, on
  every day outside a finite set `W`, does not exploit that history relative to any process:
  its net worth is at most `1 + ∑_{i ∈ W} absBound_i` in every world on every day, so its
  plausible assessments are bounded above. Kind P; no hypothesis is assumed beyond the
  finiteness of `W` and the range clause (needed for `Strategy.abs_value_le`).
* **T3(b)** `dayValue_le_of_accepts` — the acceptance bridge: a strategy accepted by the market
  maker against `past` with candidate `B` has value `≤ ε` in every p.c. world **on any history
  that agrees with the candidate history on every cell the strategy mentions**. The agreement
  hypothesis is the wrong-market trap made explicit.
  `dayValue_le_of_accepted_state` is the same lemma with the agreement split into the past
  cells (`= rationalHistory past`) and the day-`n` cells (`= B.quote`): the customer's entry
  point (any accepted day state, any market maker that produces one).
  `dayValue_le_of_accepted_state_subst` is angle B's form: acceptance of the **substituted**
  strategy (`Strategy.substPast`) against `past`.
* **T3(c)** `no_ec_trader_exploits_of_firm_accepted_off_finite` — (a) at FAF's static firm
  `tradingFirmTrader DP Q` plus `trading_firm_dominance`: no efficiently computable trader
  exploits an exactly-rational `[0,1]` table on which the firm's day strategy is bounded by the
  error allowance off a finite set of days. Kind C.
-/

namespace Cleanroom.Bli.BliOverlay.AttemptB

open LogicalInduction Cleanroom.Bli.BliFound

/-! ## T3(a): the waived-days lemma -/

/-- **T3(a). The waived-days lemma.** If on every day `n` outside a finite set `W` the trader's
day strategy has value at most `marketMakerError n` on `P` in every p.c. world (no consistency
with the process needed), and `P` is a `[0,1]` history, then the trader does not exploit `P`
relative to any deductive process: every plausible assessment is at most
`1 + ∑_{i ∈ W} (Tr.strat i).absBound`.
Source: [[bli-overlay-mandate]] T3(a); [[bli-program]] §3.3 (iii)
Kind: P
Fidelity: exact
Hyps: (a) — `hP` is the `def:market` range clause (a definition-level condition on `P`), `hacc` is the day bound the lemma is about; nothing is a cited theorem -/
theorem not_exploits_of_dayValue_le_off_finite (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld,
      (Tr.strat n).value P v.payout ≤ (marketMakerError n : ℝ)) :
    ¬ Tr.Exploits P DP := by
  intro hEx
  apply hEx.2
  refine ⟨1 + ∑ i ∈ W, ((Tr.strat i).absBound : ℝ), ?_⟩
  rintro x ⟨n, v, _, rfl⟩
  unfold Trader.netWorth
  have hday : ∀ i, (Tr.strat i).value P v.payout ≤
      (marketMakerError i : ℝ) + (if i ∈ W then ((Tr.strat i).absBound : ℝ) else 0) := by
    intro i
    by_cases hi : i ∈ W
    · rw [if_pos hi]
      have h1 := (Tr.strat i).abs_value_le P hP v.payout (fun φ => payout_mem_Icc v φ)
      have h2 : (0 : ℝ) < marketMakerError i := by exact_mod_cast marketMakerError_pos i
      have h3 := le_abs_self ((Tr.strat i).value P v.payout)
      linarith
    · rw [if_neg hi, add_zero]
      exact hacc i hi v
  calc ∑ i ∈ Finset.range (n + 1), (Tr.strat i).value P v.payout
      ≤ ∑ i ∈ Finset.range (n + 1),
          ((marketMakerError i : ℝ) + (if i ∈ W then ((Tr.strat i).absBound : ℝ) else 0)) :=
        Finset.sum_le_sum (fun i _ => hday i)
    _ = ∑ i ∈ Finset.range (n + 1), (marketMakerError i : ℝ) +
          ∑ i ∈ Finset.range (n + 1), (if i ∈ W then ((Tr.strat i).absBound : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ 1 + ∑ i ∈ W, ((Tr.strat i).absBound : ℝ) := by
        apply add_le_add (sum_marketMakerError_lt_one n).le
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          exact (Finset.mem_filter.mp hi).2
        · intro i _ _
          exact_mod_cast (Tr.strat i).absBound_nonneg

/-! ## T3(b): the acceptance bridge -/

open Classical in
/-- **T3(b). The acceptance bridge.** A day-`n` strategy accepted by the market maker against
`past` with candidate `B` (at allowance `ε`) has value at most `ε` in every p.c. world, on any
history `P` that agrees with the candidate history `candidateRationalHistory past n B` on every
cell `(k, φ)` with `k ≤ n` and `φ` mentioned by the strategy. The acceptance says nothing about
`P` without that agreement (the wrong-market trap, made a hypothesis).
Source: [[bli-overlay-mandate]] T3(b)
Kind: L
Fidelity: exact -/
theorem dayValue_le_of_accepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (ε : ℚ) (B : RationalBeliefState) (hacc : MarketMakerAccepts T past ε B) (P : History)
    (hagree : ∀ φ, MentionedBy T φ → ∀ k ≤ n,
      P k φ = (candidateRationalHistory past n B k φ : ℝ)) :
    ∀ v : PCWorld, T.value P v.payout ≤ (ε : ℝ) := by
  intro v
  let b : ↥T.support → Bool := fun ψ => decide (v.Holds ψ)
  have hmm := hacc.worldValue_le b
  have hworld : T.value (Function.update (beliefHistory past) n B.toValuation)
      (supportBitWorld T b) =
      T.value (Function.update (beliefHistory past) n B.toValuation) v.payout := by
    apply T.value_eq_of_world_eqOn_support
    intro φ hφ
    exact supportBitWorld_pcWorld_eq T v φ hφ
  have hhist : T.value (Function.update (beliefHistory past) n B.toValuation) v.payout =
      T.value P v.payout := by
    apply Strategy.value_eq_of_eqOn_mentioned T
    intro φ hφ k hk
    rw [hagree φ hφ k hk]
    exact (congrFun (congrFun (candidateHistory_cast past n B) k) φ).symm
  rw [hworld, hhist] at hmm
  exact hmm

/-- **The customer's entry point.** `dayValue_le_of_accepts` with the agreement split: on the
mentioned past cells `P` reads the past (`rationalHistory past`), on the mentioned day-`n`
cells it reads the accepted state's quote. Any market maker that produces a
`MarketMakerAccepts`-accepted day state `B` for the day strategy `T` gets the day bound on any
history that carries `past` and `B` at the mentioned cells — `bli-coherent-mm`'s M2 fixed
point included.
Source: [[bli-overlay-mandate]] §Lifecycle (`dayValue_le_of_accepted_state`); T3(b)
Kind: L
Fidelity: exact -/
theorem dayValue_le_of_accepted_state {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (ε : ℚ) (B : RationalBeliefState) (hacc : MarketMakerAccepts T past ε B) (P : History)
    (hpast : ∀ φ, MentionedBy T φ → ∀ k < n, P k φ = (rationalHistory past k φ : ℝ))
    (hnow : ∀ φ, MentionedBy T φ → P n φ = (B.quote φ : ℝ)) :
    ∀ v : PCWorld, T.value P v.payout ≤ (ε : ℝ) := by
  apply dayValue_le_of_accepts T past ε B hacc P
  intro φ hφ k hk
  rcases lt_or_eq_of_le hk with hlt | rfl
  · rw [hpast φ hφ k hlt]
    simp only [candidateRationalHistory, Function.update_of_ne hlt.ne]
  · rw [hnow φ hφ]
    simp [candidateRationalHistory]

/-- **Angle B's form of the entry point.** Acceptance of the **past-substituted** strategy
`Strategy.substPast Q T` against `past` (the recursion's acceptance in angle B) bounds `T`'s value on any
history that reads `Q` at the mentioned past cells and `B.quote` at the mentioned day-`n` cells.
Source: [[bli-overlay-mandate]] §Attempt angles (B); §Lifecycle
Kind: L
Fidelity: exact -/
theorem dayValue_le_of_accepted_state_subst {n : ℕ} (T : Strategy n) (Q : ℕ → Sentence → ℚ)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState)
    (hacc : MarketMakerAccepts (Strategy.substPast Q T) past ε B) (P : History)
    (hpast : ∀ φ, MentionedBy T φ → ∀ k < n, P k φ = (Q k φ : ℝ))
    (hnow : ∀ φ, MentionedBy T φ → P n φ = (B.quote φ : ℝ)) :
    ∀ v : PCWorld, T.value P v.payout ≤ (ε : ℝ) := by
  intro v
  have h := dayValue_le_of_accepts (Strategy.substPast Q T) past ε B hacc
    (fun d φ => (candidateRationalHistory past n B d φ : ℝ)) (fun _ _ _ _ => rfl) v
  rw [Strategy.value_substPast] at h
  have heq : T.value (EF.pastView n Q (fun d φ => (candidateRationalHistory past n B d φ : ℝ)))
      v.payout = T.value P v.payout := by
    apply Strategy.value_eq_of_eqOn_mentioned T
    intro φ hφ k hk
    rcases lt_or_eq_of_le hk with hlt | rfl
    · rw [EF.pastView_of_lt hlt, hpast φ hφ k hlt]
    · rw [EF.pastView_self, hnow φ hφ]
      simp [candidateRationalHistory]
  rw [heq] at h
  exact h

/-! ## T3(c): the firm corollary -/

/-- **T3(c). No e.c. trader exploits a firm-bounded table off finitely many days.** For an
exactly-rational `[0,1]` table `Q` on which FAF's trading firm's day-`n` strategy
`TradingFirmAt DP Q n` (built from the whole table `Q`) has value at most `marketMakerError n`
in every p.c. world for every `n` outside a finite `W`, no efficiently computable trader
exploits `Q` relative to `DP`: T3(a) at `tradingFirmTrader DP Q`, then
`trading_firm_dominance`.
Source: [[bli-overlay-mandate]] T3(c); [[bli-program]] §3.3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) — `trading_firm_dominance` is FAF's theorem, applied; `hQ` is the range clause; `hacc` is the day bound -/
theorem no_ec_trader_exploits_of_firm_accepted_off_finite (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, 0 ≤ Q day φ ∧ Q day φ ≤ 1) (W : Finset ℕ)
    (hacc : ∀ n ∉ W, ∀ v : PCWorld,
      (TradingFirmAt DP Q n).value (fun d φ => (Q d φ : ℝ)) v.payout ≤
        (marketMakerError n : ℝ)) :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (fun d φ => (Q d φ : ℝ)) DP := by
  intro Tr hTr hEx
  have hP : ∀ day φ, (0 : ℝ) ≤ (Q day φ : ℝ) ∧ (Q day φ : ℝ) ≤ 1 := fun day φ =>
    ⟨by exact_mod_cast (hQ day φ).1, by exact_mod_cast (hQ day φ).2⟩
  have hfirm := trading_firm_dominance DP (fun d φ => (Q d φ : ℝ)) hP Q (fun _ _ => rfl) Tr hTr hEx
  exact not_exploits_of_dayValue_le_off_finite (tradingFirmTrader DP Q) _ DP hP W hacc hfirm

end Cleanroom.Bli.BliOverlay.AttemptB
