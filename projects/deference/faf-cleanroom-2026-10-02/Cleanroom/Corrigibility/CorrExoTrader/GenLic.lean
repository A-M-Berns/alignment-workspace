import Cleanroom.Corrigibility.CorrExoTrader.Market

/-!
# `corr-exo-trader` · GenLic: the generalised LIC over the exo-market (T2)

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 3 of the
layout. Imports `Market` (hence FAF's construction); single-market throughout.

The source's conjecture (line 95): "include `H` in the fixed point but not in the supertrader …
for every e.c. trader `T`, `Value_n(T) ≤ c_T + Loss_n(H)` in plausible-value terms … The original
LIC is the case `H = 0` … I haven't checked this against the budgeter details."

What is proved here:

* **`exoLoss DP H v n := −(H.netWorth (exoHistory DP H) v n)`** — the demand's cumulative loss in
  world `v` through day `n` (a loss is positive). Well-defined once `H` is a `Trader`, which
  answers bli-soto-b-056's ill-posedness flag.
* **T2.1 `exo_finiteHorizon_bound`** (kind C; was P before audit r1 N3): in every p.c. world, every day, the *firm's* net
  worth against the exo-market is `≤ 1 + Loss_n(H)` (strictly `< 1 + Loss_n(H)`). This is the
  finite-horizon generalised LIC for the firm with `c = 1`: T1.3 summed over `i ≤ n` with FAF's
  geometric budget `sum_marketMakerError_lt_one`, the join's net worth splitting by `join_value`.
* **T2.2 `budgeted_value_le_loss`** (kind C): the individual-trader form the sketch supports —
  for every e.c. `T` (enumeration index `j`) and every budget `r + 1`, the *gated, budgeted*
  component's net worth is `≤ (3 + Loss_n(H)) / w_{j, r+1}` in every plausible world, from FAF's
  `tradingFirmTrader_residual_floor`. Fidelity **weaker** than the source's display: gated and
  budgeted `T`, multiplicative constant `1/w`. The source's coefficient-one form for an unbudgeted
  `T` is **refuted** in `Undecided.lean` (`genLic_coefficientOne_refuted`): an unbudgeted e.c.
  trader's plausible values need not be bounded above at all, even at `H = 0`.
* **T2.3 `noEcExploit_of_boundedLoss`** (kind C, load-bearing): if the demand's plausible loss is
  bounded, no e.c. trader exploits the exo-market. The hypothesis is about `H`'s loss, the
  conclusion about every e.c. trader (different objects — not a squeeze). Proof: T2.1 bounds the
  firm's plausible assessments above, so the firm does not exploit; `trading_firm_dominance`
  then refutes exploitation by every e.c. trader.
* **T2.4 `netWorth_sub_netWorth_of_agree_on_traded`** (kind L): "`H`'s loss on an undecidable is
  never realised in cash" — two worlds agreeing on every sentence `H` trades except `u` value its
  position differently exactly by its `u`-coefficients times the payout difference; see
  `Undecided.lean` for the mark-to-market form. **Repair round 2** (audit r2 adversarial B1): the
  first version quantified the agreement over *every* sentence other than `u`, which forces
  agreement on `u` through `∼u` (`agree_off_forces_agree`) and made the statement `0 = 0`; the
  traded-sentence form is the one of record, with N− `constBuyer_agree_on_traded` and N+
  `joinBuyers_agree_on_traded`.

Every hypothesis is grade (a). The non-vacuity witnesses for T2.3 (`noDemand`, N−; a finitely
supported push, N+) are in `Witnesses.lean`.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional

/-! ## The demand's loss -/

/-- **The demand's cumulative plausible loss**: `Loss_n(H) v := −(H.netWorth (exoHistory DP H) v n)`,
so that a loss is positive. Well-defined because `H` is a `Trader` (bli-soto-b-056's flag).
Source: line 95 ("`Loss_n(H)` is `H`'s cumulative plausible loss"); mandate T2
Kind: D
Fidelity: exact -/
noncomputable def exoLoss (DP : DeductiveProcess) (H : ExoDemand) (v : PCWorld) (n : ℕ) : ℝ :=
  -(H.netWorth (exoHistory DP H) v n)

/-- The firm's and the demand's net worths against the exo-market sum to the exo-trader's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma firm_add_demand_netWorth (DP : DeductiveProcess) (H : ExoDemand) (v : PCWorld) (n : ℕ) :
    (tradingFirmTrader DP (exoQuote DP H)).netWorth (exoHistory DP H) v n +
      H.netWorth (exoHistory DP H) v n = (exoTrader DP H).netWorth (exoHistory DP H) v n := by
  unfold Trader.netWorth
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show _ = (Strategy.join [TradingFirmAt DP (exoQuote DP H) i, H.strat i]).value _ _
  rw [Strategy.join_two_value]
  rfl

/-- The exo-trader's plausible net worth is below `1` on every day (FAF's
`marketMaker_netWorth_lt_one` at the exo-trader).
Source: mandate T2.1
Kind: L
Fidelity: exact -/
lemma exoTrader_netWorth_lt_one (DP : DeductiveProcess) (H : ExoDemand) (v : PCWorld) (n : ℕ) :
    (exoTrader DP H).netWorth (exoHistory DP H) v n < 1 := by
  rw [exoHistory_eq_marketMakerHistory]
  exact marketMaker_netWorth_lt_one (exoTrader DP H) v n

/-! ## T2.1 — the finite-horizon generalised LIC for the firm -/

/-- **T2.1 — the finite-horizon generalised LIC** (strict form): in every p.c. world and on every
day, the trading firm's net worth against the exo-market is `< 1 + Loss_n(H)`. T1.3 summed over
`i ≤ n` against FAF's geometric error budget. The constant is `c = 1`. FAF's
`marketMaker_netWorth_lt_one` at the join with one `linarith` to move `H.netWorth` across (kind C,
audit r1 N3).
Source: line 95 (the conjecture, finite-horizon form); corr-core-041; mandate T2.1
Kind: C
Fidelity: exact (for the firm; the individual-trader form is T2.2)
Hyps: (a) -/
theorem exo_finiteHorizon_bound_lt (DP : DeductiveProcess) (H : ExoDemand) (n : ℕ) (v : PCWorld) :
    (tradingFirmTrader DP (exoQuote DP H)).netWorth (exoHistory DP H) v n <
      1 + exoLoss DP H v n := by
  have h := firm_add_demand_netWorth DP H v n
  have hlt := exoTrader_netWorth_lt_one DP H v n
  unfold exoLoss
  linarith

/-- **T2.1 — the finite-horizon generalised LIC** (the mandate's display): the firm's net worth
against the exo-market is `≤ 1 + Loss_n(H)` in every p.c. world, every day. **Scope** (audit r1 N2/N4):
the hypothesis-free bound holds for every demand, but T2.3's bounded-loss hypothesis excludes the
persistent push (`persistent_push_unbounded_loss`, `Instances.lean`): the exploitation form covers
finitely-supported or self-financing demands, the persistent push of T6/T10 is covered by this
finite-horizon form with `Loss` growing.
Source: line 95; corr-core-041; mandate T2.1
Kind: C
Fidelity: exact (for the firm)
Hyps: (a) -/
theorem exo_finiteHorizon_bound (DP : DeductiveProcess) (H : ExoDemand) (n : ℕ) (v : PCWorld) :
    (tradingFirmTrader DP (exoQuote DP H)).netWorth (exoHistory DP H) v n ≤
      1 + exoLoss DP H v n :=
  (exo_finiteHorizon_bound_lt DP H n v).le

/-! ## T2.2 — the individual-trader form the sketch supports -/

/-- **T2.2 — the budgeted-component bound.** For every e.c. trader `T`, with enumeration index `j`
(`exists_enumeratedTrader_eq`), and every positive budget `r + 1`: the gated, budgeted component
`Budgeter(T.gate j, r + 1)` has net worth `≤ (3 + Loss_n(H)) / w_{j, r+1}` against the exo-market
in every plausible world, where `w_{j,b} = 2^{-(j+1+b)}` is FAF's firm weight. From
`tradingFirmTrader_residual_floor` (the firm keeps the floor `−2` after removing one weighted
component) and T2.1.
Source: line 95 (`Value_n(T) ≤ c_T + Loss_n(H)`); corr-core-041; mandate T2.2
Kind: C
Fidelity: weaker: the trader is gated at its enumeration index and budgeted, and the loss enters with the multiplicative constant `1/w_{j,r+1}` — not the source's coefficient `1` for an unbudgeted `T` (refuted, `Undecided.lean`)
Hyps: (a) -/
theorem budgeted_value_le_loss (DP : DeductiveProcess) (H : ExoDemand) (T : Trader)
    (hT : EfficientlyComputable T) :
    ∃ j : ℕ, enumeratedTrader j = T ∧
      ∀ (r n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
        (budgetedTrader DP (T.gate j) (r + 1) (exoQuote DP H)).netWorth (exoHistory DP H) v n ≤
          (3 + exoLoss DP H v n) / (tradingFirmWeight j (r + 1) : ℝ) := by
  obtain ⟨j, hj⟩ := exists_enumeratedTrader_eq T hT
  refine ⟨j, hj, fun r n v hv => ?_⟩
  have hres := tradingFirmTrader_residual_floor DP (exoHistory DP H) (exoHistory_range DP H)
    (exoQuote DP H) (exoHistory_eq_quote_cast DP H) j r n v hv
  have hraw : firmRawTrader j = T.gate j := by
    unfold firmRawTrader
    rw [hj]
  rw [hraw] at hres
  have hfirm := exo_finiteHorizon_bound DP H n v
  have hw : 0 < (tradingFirmWeight j (r + 1) : ℝ) := by exact_mod_cast tradingFirmWeight_pos _ _
  rw [le_div_iff₀ hw]
  linarith

/-! ## T2.3 — the contrapositive: bounded push loss ⟹ no e.c. trader exploits -/

/-- Under a uniform bound on the demand's plausible loss, the firm's plausible assessments
against the exo-market are bounded above, so the firm does not exploit it.
Source: mandate T2.3 (proof shape)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem firm_not_exploits_of_boundedLoss (DP : DeductiveProcess) (H : ExoDemand) (B : ℝ)
    (hB : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → exoLoss DP H v n ≤ B) :
    ¬ (tradingFirmTrader DP (exoQuote DP H)).Exploits (exoHistory DP H) DP := by
  intro hEx
  apply hEx.2
  refine ⟨1 + B, ?_⟩
  rintro x ⟨n, v, hv, rfl⟩
  exact le_trans (exo_finiteHorizon_bound DP H n v) (by linarith [hB n v hv])

/-- **T2.3 — the useful form of the generalised LIC**: if the exogenous demand's plausible loss is
bounded (uniformly over days and plausible worlds), then **no efficiently computable trader
exploits the exo-market**. The hypothesis is about `H`; the conclusion is about every e.c. trader.
Composition of T2.1 (the firm's assessments are bounded above by `1 + B`, so the firm does not
exploit) with FAF's Trading Firm Dominance (`trading_firm_dominance`: an exploiting e.c. trader
would make the firm exploit). Single-market.
Source: line 95 (the conjecture's contrapositive); corr-core-041 flags ("the more useful form"); mandate T2.3
Kind: C
Fidelity: exact (the exploitation reading of the conjecture; the plausible-value display is T2.2 / refuted)
Hyps: (a) -/
theorem noEcExploit_of_boundedLoss (DP : DeductiveProcess) (H : ExoDemand)
    (hB : ∃ B : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) → exoLoss DP H v n ≤ B) :
    NoEcExploit (exoHistory DP H) DP := by
  obtain ⟨B, hB⟩ := hB
  intro T hT hEx
  exact firm_not_exploits_of_boundedLoss DP H B hB
    (trading_firm_dominance DP (exoHistory DP H) (exoHistory_range DP H) (exoQuote DP H)
      (exoHistory_eq_quote_cast DP H) T hT hEx)

/-- The `H = 0` instance of T2.3 is FAF's `lia_no_efficient_trader_exploits`: with no demand the
loss is `0` and the exo-market is `liaHistory`.
Source: line 95 ("The original LIC is the case `H = 0`"); mandate T2.3
Kind: L
Fidelity: exact -/
theorem noEcExploit_liaHistory (DP : DeductiveProcess) : NoEcExploit (liaHistory DP) DP := by
  rw [← exoHistory_noDemand]
  exact noEcExploit_of_boundedLoss DP noDemand ⟨0, fun n v _ => by
    simp [exoLoss, noDemand]⟩

/-! ## T2.4 — the loss on an undecidable is never realised in cash

**Repair round 2** (audit r2 adversarial B1). The first version of T2.4 took "two worlds agreeing on
*every* sentence other than `φ`" as its hypothesis. No two distinct propositional worlds do that:
`∼φ ≠ φ` and `payout (∼φ) = 1 − payout φ`, so agreement off `φ` forces agreement on `φ`
(`agree_off_forces_agree`), the two payout functions coincide (`agree_off_payout_eq`), and both
sides of the old conclusion were `0`. The statement of record is now the *traded-sentence* form:
agreement only on the sentences the trader actually trades through day `n`, other than `φ`. -/

/-- Agreement of two worlds on every sentence other than `φ` forces agreement on `φ`: take
`ψ := ∼φ`. The reason the universal form of T2.4 was vacuous (audit r2 adversarial B1).
Source: audit r2 adversarial B1
Kind: L
Fidelity: n/a -/
theorem agree_off_forces_agree (v v' : PCWorld) (φ : Sentence)
    (hagree : ∀ ψ, ψ ≠ φ → v.payout ψ = v'.payout ψ) : v.payout φ = v'.payout φ := by
  have hne : (∼φ) ≠ φ := by
    intro h
    have hiff := PCWorld.holds_neg worldAll φ
    rw [h] at hiff
    by_cases hv : worldAll.Holds φ
    · exact hiff.mp hv hv
    · exact hv (hiff.mpr hv)
  have h := hagree (∼φ) hne
  unfold PCWorld.payout at h ⊢
  rw [PCWorld.holds_neg, PCWorld.holds_neg] at h
  by_cases hv : v.Holds φ <;> by_cases hv' : v'.Holds φ <;> simp [hv, hv'] at h ⊢

/-- Hence "two worlds differing only on `φ`" have equal payout functions — they do not exist in
propositional semantics.
Source: audit r2 adversarial B1
Kind: L
Fidelity: n/a -/
theorem agree_off_payout_eq (v v' : PCWorld) (φ : Sentence)
    (hagree : ∀ ψ, ψ ≠ φ → v.payout ψ = v'.payout ψ) : v.payout = v'.payout := by
  funext ψ
  by_cases h : ψ = φ
  · subst h; exact agree_off_forces_agree v v' ψ hagree
  · exact hagree ψ h

/-- **T2.4 — the demand's net worth across the two verdicts on a sentence.** Two worlds that agree
on every sentence the trader trades through day `n` except `φ` value its position identically on
those sentences: the difference of its net worths is `∑_{i ≤ n} (shares of φ bought on day i) ·
(v.payout φ − v'.payout φ)`. On an undecided `φ` both verdicts are plausible (`hboth` of
`confined_not_exploits_const`), so the demand's "loss" is a matter of which plausible world prices
its open `φ`-position — never a settled cash amount. Stated for any trader; the mark-to-market
form is `Undecided.lean`'s `netWorth_eq_markToMarket_add_openExposure`. **Repair round 2**: the
hypothesis is the traded-sentence agreement; the universal form was vacuous
(`agree_off_payout_eq`). Inhabited non-trivially by `joinBuyers_agree_on_traded` (N+).
Source: line 95 ("`H`'s 'loss' on an undecidable is never realised in cash"); mandate T2.4; audit r2 adversarial B1
Kind: L
Fidelity: exact (agreement on the traded sentences; the universal form is unsatisfiable by distinct worlds)
Hyps: (a) -/
theorem netWorth_sub_netWorth_of_agree_on_traded (T : Trader) (P : History) (v v' : PCWorld)
    (φ : Sentence) (n : ℕ)
    (hagree : ∀ i ∈ Finset.range (n + 1), ∀ p ∈ (T.strat i).trades, p.2 ≠ φ →
      v.payout p.2 = v'.payout p.2) :
    T.netWorth P v n - T.netWorth P v' n =
      ∑ i ∈ Finset.range (n + 1),
        (((T.strat i).trades.filter (fun p => p.2 = φ)).map (fun p => p.1.denote P)).sum *
          (v.payout φ - v'.payout φ) := by
  unfold Trader.netWorth
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Strategy.value]
  have hagree' := hagree i hi
  generalize (T.strat i).trades = l at hagree'
  induction l with
  | nil => simp
  | cons p rest ih =>
      have hrest : ∀ p ∈ rest, p.2 ≠ φ → v.payout p.2 = v'.payout p.2 :=
        fun p hp => hagree' p (List.mem_cons_of_mem _ hp)
      have ih' := ih hrest
      by_cases hp : p.2 = φ
      · have hp' : v.payout p.2 - v'.payout p.2 = v.payout φ - v'.payout φ := by rw [hp]
        rw [List.filter_cons_of_pos (by simp [hp])]
        simp only [List.map_cons, List.sum_cons]
        linear_combination ih' + p.1.denote P * hp'
      · have hp' : v.payout p.2 - v'.payout p.2 = 0 := by
          rw [hagree' p List.mem_cons_self hp, sub_self]
        rw [List.filter_cons_of_neg (by simp [hp])]
        simp only [List.map_cons, List.sum_cons]
        linear_combination ih' + p.1.denote P * hp'

/-- The world holding every atom except `a`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def worldExcept (a : ℕ) : PCWorld := fun i => i ≠ a

/-- **N− for T2.4**: the constant buyer of `atom a` trades nothing but `atom a`, so the
traded-agreement hypothesis holds *vacuously* for any two worlds — which may therefore differ on
`a`. Degenerate (no traded sentence is actually agreed on); the N+ is `joinBuyers_agree_on_traded`.
Source: audit r2 adversarial B1 (probe `AgreeOffVacuous.lean`, adopted)
Kind: N−
Fidelity: exact
Hyps: (a) -/
theorem constBuyer_agree_on_traded (a : ℕ) (c : ℚ) (v v' : PCWorld) (n : ℕ) :
    ∀ i ∈ Finset.range (n + 1), ∀ p ∈ ((constBuyer (Formula.atom a) c).strat i).trades,
      p.2 ≠ Formula.atom a → v.payout p.2 = v'.payout p.2 := by
  intro i _ p hp hne
  simp [constBuyer] at hp
  exact absurd (congrArg Prod.snd hp) hne

/-- **N+ for T2.4**: the trader buying `c` shares of `atom a` and `c'` shares of `atom b` daily
(`a ≠ b`), against the all-true world and the world holding everything but `a`: the two worlds
agree on the traded sentence `atom b` (the hypothesis is exercised, not vacuous) and differ on
`atom a` by payout `1`, so T2.4 gives a net-worth difference of `∑_{i ≤ n} c`, not `0`.
Source: audit r2 adversarial B1
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem joinBuyers_agree_on_traded (a b : ℕ) (hab : a ≠ b) (c c' : ℚ) (n : ℕ) :
    (∀ i ∈ Finset.range (n + 1),
      ∀ p ∈ ((Trader.join (constBuyer (Formula.atom a) c) (constBuyer (Formula.atom b) c')).strat
        i).trades, p.2 ≠ Formula.atom a → worldAll.payout p.2 = (worldExcept a).payout p.2) ∧
    worldAll.payout (Formula.atom a) - (worldExcept a).payout (Formula.atom a) = 1 := by
  refine ⟨?_, ?_⟩
  · intro i _ p hp hne
    simp [Trader.join, Strategy.join, constBuyer] at hp
    rcases hp with h | h
    · exact absurd (congrArg Prod.snd h) hne
    · rw [h]
      simp [PCWorld.payout, worldAll, worldExcept, hab.symm]
  · simp [PCWorld.payout, worldAll, worldExcept]

end Cleanroom.Corrigibility.CorrExoTrader
