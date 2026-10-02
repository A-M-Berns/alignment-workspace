import Cleanroom.Deference.DefDoseResponse.Defs
import Cleanroom.Deference.DefDoseResponse.Arms
import Cleanroom.Deference.DefDoseResponse.Audit
import Cleanroom.Deference.DefDoseResponse.Advisor
import Cleanroom.Deference.DefDoseResponse.Steering
import Cleanroom.Deference.DefDoseResponse.Variants
import Cleanroom.Deference.DefDoseResponse.Thinned
import Cleanroom.Deference.DefDoseResponse.Sampling
import Cleanroom.Deference.DefDoseResponse.Coin
import Cleanroom.Deference.DefDoseResponse.Randomized
import Cleanroom.Deference.DefDoseResponse.Open
import Cleanroom.Deference.DefDoseResponse.Witnesses

/-!
# `def-dose-response` — Dose-response: arms, audits, thinned forcing and steering

Root module of the package `Cleanroom.Deference.DefDoseResponse` ([[def-dose-response-mandate]]).
The dose-response note's audit design ([[dose-response]]) assembled over FAF with the arms as real
markets: `k` copies of one advisee algorithm — `li-projection`'s projection of FAF's LIA over a
`li-quote-lane` exposure ledger — compared by an auditor on a protected fresh atom. Files, in
dependency order:

* `Defs` — the design of record (D1–D3, D5): exposure ledger, realized dose, testimony, response,
  the jump-target identity (∗), the arm as one `def` on a ledger, the audit statistics.
* `Arms` — T6: the exposure ledger as a FAF process; `arm_isLogicalInductor` (modulo
  `li-projection`'s OPEN rewriters, the only thing any "arm is an inductor" rests on);
  `non_attribution` as an equality of FAF markets; the susceptibility/push confound.
* `Audit` — T3: `audit_sound` (every battery), `audit_complete` (uniform), `audit_exact`, for
  arbitrary inductors over arbitrary processes; T3.5 `decided_content_auto_passes` with the
  destinations derived.
* `Advisor` — D4: the committed stream `quoteStream` (FAF's `expectQuoteAt`), the steered advisor
  as a finite patch (an inductor exactly; exact prescription at mesh-exact `v`; finding F6), the
  mirror-ledger pinning.
* `Steering` — T2: dose-graded destinations with the expectation form derived from the base
  criterion alone (`indicatorOf_expect_eq`), `production_quote_tendsto` (b-half),
  `cross_arm_audit_fires` (d), memory asymmetry (Cor T2.1); the `lic_expectation_indicator` route.
* `Variants` — T2.5 dose compensation (finding F5: the note's `v_i = ½ + s/p̂_i` gives `½ + γs`),
  T7.6 presence-triggered steering is invisible.
* `Thinned` — T1 over `fa-forcing-trader`: the thinned gate, `thinned_agreement`,
  `thinned_forcing_gated`, the limit-point grade, Cor T1.1 as a definitional lemma, the D6 ramp
  identity; finding F1 recorded.
* `Sampling` — T4: Lemma 4.2 over FAF's `PseudorandomFrequency`, Cor T1.2.
* `Randomized` — T5 (partial): the i.i.d. coin measure (the constant coin a null event), the
  countable intersection over `li-pseudorandom`'s enumeration (proved), the Kronecker reduction and
  the `piLE`-predictability of the weights (proved, repair round 1), the a.s. convergence of the
  normalized martingale (OPEN), the strong law and the headline
  `randomization_justifies_tameness` composed from them, the LIA instance.
* `Open` — the two-way closure (T2.OPEN, under the design's admissibility hypotheses),
  unrestricted thinned forcing (T7.1), and the N+ rows locating the thinning step's failure
  (lookahead speed, not sparsity).
* `Witnesses` — the paper arms over `paperDP 𝗜𝚺₁` (destinations `3/4`, `5/8`, audit limit `1/8`),
  the grade-(a) soundness witness, the steered advisor over the mirror ledger, the thinned
  same-market instance on the even schedule (N−), T4's package at the `truthStar` coin.

Every statement is **one-way** except the OPEN `twoWay_closure_exists`. Repair round 1
(2026-10-01) is recorded in [[def-dose-response-report]] § Repair round 1.
-/
