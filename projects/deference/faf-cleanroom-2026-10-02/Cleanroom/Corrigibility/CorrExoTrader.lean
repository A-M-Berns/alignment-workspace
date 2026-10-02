import Cleanroom.Corrigibility.CorrExoTrader.Defs
import Cleanroom.Corrigibility.CorrExoTrader.Market
import Cleanroom.Corrigibility.CorrExoTrader.GenLic
import Cleanroom.Corrigibility.CorrExoTrader.FrontRun
import Cleanroom.Corrigibility.CorrExoTrader.Budget
import Cleanroom.Corrigibility.CorrExoTrader.Undecided
import Cleanroom.Corrigibility.CorrExoTrader.Constraint
import Cleanroom.Corrigibility.CorrExoTrader.Reflect
import Cleanroom.Corrigibility.CorrExoTrader.Witnesses
import Cleanroom.Corrigibility.CorrExoTrader.WitnessReflect
import Cleanroom.Corrigibility.CorrExoTrader.Instances
import Cleanroom.Corrigibility.CorrExoTrader.Open

/-!
# `corr-exo-trader`: exogenous demand in the market — front-running, wireheading and the unlearnable constraint

Root module of the package `Cleanroom.Corrigibility.CorrExoTrader`; dependents import this one
name. Mandate: `run/wp/corr-exo-trader/corr-exo-trader-mandate.md`; report, findings, ledger and
open list beside it. Scope: **single-market** throughout (one market, one process, one exogenous
participant); the reflection-side statements are over one history and a `StateSystem`.

* `Defs` — fresh atoms of family `6` (`exoAtom`, `utilityAtom := exoAtom 0`), `ExoDemand := Trader`,
  `noDemand`, `Trader.join`, `NoEcExploit`, `constBuyer`, the mark-to-market names.
* `Market` (T1) — the exo-market of record `exoStates`/`exoQuote`/`exoHistory`/`exoTrader` (the
  demand joined into the market maker's day action, not into the firm), its identification with
  FAF's `marketMakerHistory`, `H = 0` recovers `liaHistory`; **T1.3** `exo_day_value_le`; **T1.4**
  a push pins the day price (`push_pins_day_price`, `push_pins_marketMaker_price`).
* `GenLic` (T2) — `exoLoss`; **T2.1** `exo_finiteHorizon_bound` (the firm's net worth `≤ 1 +
  Loss_n(H)`, kind C); **T2.2** `budgeted_value_le_loss` (`≤ (3 + Loss)/w` for the gated budgeted
  component); **T2.3** `noEcExploit_of_boundedLoss` (bounded-loss demands only — the landed
  persistent push is outside it, `persistent_push_unbounded_loss` in `Instances`); T2.4
  `netWorth_sub_netWorth_of_agree_on_traded` (L; repair round 2 replaced the vacuous universal
  form, `agree_off_forces_agree`).
* `FrontRun` (T3) — the two-sided ramp front-runner, its e.c. certificate `frontRunner_ec`,
  **T3.1** `frontRun_asympEq` over any `NoEcExploit` market — an *asymptotic* statement that says
  nothing about any single push; its content on a constant sentence `landing_increments_vanish` /
  `no_landing_of_increments`; `asympEq_shift_iff_of_eventuallyConst` (why the one-jump witness is
  N−); `hworld`'s necessity, vacuity half: `noEcExploit_of_inconsistent_stage`.
* `Budget` (T6) — **T6.1** `occam_exhausted` / `occam_silenced` over FAF's `priorBudgetBreach`
  with the explicit day (the "push" enters only as a price floor; `occam_exhausted_of_floor`,
  N− `occam_exhausted_half_table`); **T6.2** `occam_worth_const_of_zero_price` (L),
  `occam_worth_antitone`.
* `Undecided` (T7) — **T7.1** `netWorth_eq_markToMarket_add_openExposure` (L),
  `undecided_profit_is_markToMarket` (C; at most two points); `unpushed_interior`; the refutation
  `genLic_coefficientOne_refuted(_ec)`; **T7.2** `u_price_converges_of_inductor`.
* `Constraint` (T8) — **T8.1** `SelfCausedInvariant`, `PushInvariant` (satisfied by every
  demand-blind map; the meaningful object is `PushInvariantOver` in `Open`); **T8.2**
  `constraint_lic_compatible` (L modulo li-projection's OPEN (A); no demand enters the statement);
  the sanity lemma `pinnedMarket_pushInvariant` (T, modulo (A)).
* `Reflect` (T4, T5, T9) — **T4.1** `E2xAct`, `E5Act` (definitions of record; the scoped clause is
  the identity modulo faith, `e5Act_scoped_iff_identity`); T4.2 `wirehead_identity_li` (S, not a
  headline); **T4.4** `incentive_eq_weight_difference`; `valueAlpha`/`valueBeta`/`valueGamma`;
  **T5.2** `beta_no_manipulation_incentive` (`beta_no_voi` folded in, S); **T5.3**
  `gamma_diff_eq`, `gamma_eq_alpha_of_uncaused`; **T9.1** `Implementation`, `FaithfulOn`,
  `LegitimateState`; **T9.2** `pointwise_argmax_optimal_of_independent`; **T9.3** `HcModel`,
  `HcCommitment` (all four policies plus a correlation clause since repair round 2), `HcRealized`
  (no inhabitant shown); **T9.4** `degenerate_collapses_split`.
* `Witnesses` — T2.3 N− (`exoLoss_noDemand`) and N+ (`pushOnce`, `noEcExploit_pushOnce`); T9.2
  `dependence_breaks_pointwise`; T9.3 `hcWitness_commitment` (`hcWitness_stopWhenPressed_optimal`,
  `hcWitness_press_correlated`) and the press-independent counter-model to the two-policy
  definition, `hcIndep` (`hcIndep_alwaysStop_better`, `hcIndep_not_commitment`).
* `WitnessReflect` — the LI-level N+ for T4/T5: `pushSystem`, `pushHist`, `pushHist_e2xAct`,
  `pushHist_e5Act`, `pushHist_alpha_push_gt_honest`, `pushHist_beta_indifferent` (contrast only;
  `pushHist_prices_falsum_action` discloses the incoherence).
* `Instances` — **T3.2** `frontRun_exo`, its N− `frontRun_witness` (modulo (A)) and N−
  `frontRun_exo_witness_theorem` (no OPEN); the refutation-shaped content check `altSchedule`,
  `no_landing_altSchedule(_lia/_exo)` (C) and its reach over an inductor
  (`landing_increments_vanish_of_inductor`, `frontRun_const_family_iff_of_inductor`); `hworld`'s
  necessity as a counter-model, `frontRun_fails_without_hworld` (`lagHist` over `falsumDP`); T6.1
  for the opposer `occam_exhausted_opposer(_utilityAtom)`, `occam_exhausted_half_table_utilityAtom`,
  and T2.3's regime boundary `persistent_push_unbounded_loss`; **T11.1** `exhausted_vs_invariant`
  (L, a juxtaposition).
* `Open` — the OPEN statements of record: T2.5 `exoHistory_computableMarket_of_ec` (with
  `exo_isLogicalInductor_of_boundedLoss`, `exo_u_price_converges`), T8.3
  `selfCausedInvariant_compatible`, `pushInvariantOver_compatible` (with `PushInvariantOver`),
  T10.1 `persistent_push_steers` (the two-sided `persistentReactive q`),
  `genLic_boundedBelow_pointwise`; and `retract` (T10.2, D).

Repair history: round 1 (audit r1) regraded `frontRun_witness` N−, `pinnedMarket_pushInvariant` T,
`wirehead_identity_li` S and added the alternating-schedule refutation, the opposer, the regime
boundary and two OPEN statements; round 2 (audit r2) replaced the vacuous T2.4, strengthened
`HcCommitment`, made `persistentReactive` two-sided, adopted the auditors' probes and corrected the
Kind labels and docstrings named in the audits. See [[corr-exo-trader-report]].
-/
