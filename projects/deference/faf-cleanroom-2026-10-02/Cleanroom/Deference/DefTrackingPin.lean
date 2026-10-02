import Cleanroom.Deference.DefTrackingPin.Defs
import Cleanroom.Deference.DefTrackingPin.Pin
import Cleanroom.Deference.DefTrackingPin.Uniform
import Cleanroom.Deference.DefTrackingPin.Atoms
import Cleanroom.Deference.DefTrackingPin.Deferred
import Cleanroom.Deference.DefTrackingPin.Column
import Cleanroom.Deference.DefTrackingPin.Encoding
import Cleanroom.Deference.DefTrackingPin.Relabel
import Cleanroom.Deference.DefTrackingPin.Usm
import Cleanroom.Deference.DefTrackingPin.Witnesses

/-!
# `def-tracking-pin`: tracking and pinning — settlement forces timely prices, over FAF

Root module of the package `Cleanroom.Deference.DefTrackingPin`. The corpus's Computable LUV
Tracking / Pinning / Vanishing lemma (anson-042) stated over FAF's objects for arbitrary e.c.
LUV families, with its **eventual / convergent / timely** grades separated and the one clause the
corpus hides — generability of the target in FAF's one trader class — explicit as the (c) `hz`.
Mandate: `run/wp/def-tracking-pin/def-tracking-pin-mandate.md`; report, findings and ledger beside
it. Every statement is one-way (a fixed market, a reader over the ledger-augmented process); the
sealed-sibling target is `li-coupled-pair`'s and is not formalized here.

* `Defs`: settlement facts (`determinedVia_mem_Icc`, `determinedVia_expectApprox_near` — T8 (i)'s
  mesh error), the mesh family's price bound, T7's plumbing (`abs_sub_le_of_abs_le_of_abs_le`,
  `asympEq_restrict_of_near`).
* `Pin`: the engine `pin_tendsto_of_polySequence` and its one-sided halves
  `pin_asympLE_of_polySequence` / `pin_asympGE_of_polySequence`; **T3** `pinning_tendsto` /
  `pinning_ofTendsto`, one-sided `pinning_asympLE` / `pinning_asympGE` (eventual bounds, no limit)
  (convergent target, grade (a)); **T2** `pinning_fixed` / `_asympEq` / `_expectInf` (fixed LUV,
  the snapshot identity, grade (a)); **T1** `pinning_ofApprox` (the approximant form, `hz` (c)),
  `pinning_ofMachineApprox`, `pinning_exact`, `pinning_approximants_agree`; the one-sided forms at
  the paper's premise; `pinning_ledger` (= `li-quote-lane`'s `readability_ofApprox`).
* `Uniform`: the `∀ j` forms the dependents compose with.
* `Atoms`: **T4** `ledger_atom_learned` (`hpat` (c), the timely strengthening),
  `atom_eventually_learned` (the source's own eventual grade, (a)), `OneWayPair.atom_learned`,
  `ledger_atom_learned_ofTendsto` ((a) instance); the eventual provability induction
  `provind_eventually_true` / `_false`; `ledgerLuv_gt_sentenceCodes`.
* `Deferred`: **T5** `deferredTable`, `deferredProcess`, `deferredReader`, `deferredSchedule`;
  `deferredTable_computable`, `deferredProcess_computable`, `deferred_inductor`,
  `deferredProcess_hworld`, `deferred_determined`; the honest T1 `deferred_tracking_any` /
  `deferred_tracking` (any reader / FAF's LIA; `hz` (c)); `deferred_snapshot_any` /
  `deferred_snapshot`. Not a `OneWayPair` (findings F-H). The only file importing
  `Construction.LIACompiler` (via `li-quote-lane`'s `OneWay`).
* `Column`: **T6** `deferredTable_tendsto_limitingBelief`, `deferred_column_tracking`,
  `deferred_column_tendsto`, `deferred_column_decided` (any reader over the deferred process; the
  `_lia` instances at FAF's LIA); `limitingBelief_eq_one_of_decided` / `_zero_of_refuted`;
  `trivialPredictor_error_tendsto_zero`, `thm3_unconditional` (anson-2-022 Theorem 3 with its
  predictor hypothesis bypassed — the source's cumulative "asymptotically calibrated" is neither
  assumed nor discharged; findings F-D); `deferred_diagonal_subsequence` (T6 stretch, the literal
  diagonal reading, proved at repair round 2 through `columnPad` and the one-sided T3 forms).
* `Encoding`: **T8** `contract`, `contract_value_near`, `ledger_profile`, `realPayoutWorth`,
  `meshWorth`, `meshWorth_sub_realPayoutWorth_le(_of_bounded)`.
* `Relabel`: **T9** `realPayoutWorth_copy` (T), the OPEN `relabel_not_inductor` (direction unknown;
  `computableMarket_relabel` / `relabel_only_noExploit_can_fail` show only `noExploit` can fail),
  `claim2_fixed_sentence` (grade (a), any reader) and `_lia`.
* `Usm`: **T10** `limitingBelief_logLoss_bounded`.
* `Witnesses`: `pinning_unpair` (T1, N+), `paperDeferredProcess` / `paperDeferredReader` /
  `paperDeferred_inductor` / `paperDeferred_column_tendsto` / `paperDeferred_snapshot` (T5/T6/T2,
  N+), `pinning_harmonic_tendsto` (T3 at a verified non-constant table, N+),
  `atom_learned_harmonic` (T4 (a), N+), `atom_learned_unpair_live` (T4's `hpat` at a live
  pattern, N+), `atom_learned_harmonic_const` (N−), `deferred_tracking_constLookahead`
  (`deferred_tracking`'s full package at a constant lookahead, N−).
-/
