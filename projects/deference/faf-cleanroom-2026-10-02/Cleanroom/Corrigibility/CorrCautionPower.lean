import Cleanroom.Corrigibility.CorrCautionPower.Setting
import Cleanroom.Corrigibility.CorrCautionPower.Quantilizer
import Cleanroom.Corrigibility.CorrCautionPower.CautionRule
import Cleanroom.Corrigibility.CorrCautionPower.Witnesses
import Cleanroom.Corrigibility.CorrCautionPower.Composition
import Cleanroom.Corrigibility.CorrCautionPower.ModelM
import Cleanroom.Corrigibility.CorrCautionPower.Reversibility
import Cleanroom.Corrigibility.CorrCautionPower.Delegation
import Cleanroom.Corrigibility.CorrCautionPower.OptionValue

/-!
# `corr-caution-power`: caution, quantilizers, POWER and wisdom caps

Root module of the corrigibility area's home for the `caution` thread's objects and results
(`caution-final.md` D1–D10, S1–S13) over FAF's `FactoredSpaces.Distr` and `corr-three-step`'s
`expect`. A dependent (`corr-power-channel`) imports this one name and gets:

* `Setting` — D1–D10 of record: `CautionState`, `harmOf`, `proxy`/`err`/`Covered`,
  `harm`/`trueHarm`/`estHarm`, `baseHarm` (`R`)/`estBaseHarm` (`R̂`), the predicates
  `ConservativelyCalibrated`/`Reckless` (no `ρ`), the Jensen split, `selfSuspicion`, `OP`,
  `qRule`/`qRuleFloored`, `realizedHarm`, `CoveredOrKnownUncovered` (printed) and
  `NullCoveredKnownUncovered` (corrected); the S1 identities.
* `Quantilizer` — Taylor 2016 Def. 1 by water-filling with an explicit compatible tie-break,
  Lemma 1, Lemma 2 (full pointwise), Theorem 1 (exchange argument), structure lemmas.
* `CautionRule` — S3, S4(c) (floored rule, misspecification-honest), S6, S2, the repaired S5(b)
  under the corrected predicate, `COR`/`CORδ`.
* `Witnesses` — every N+ instance and rule-3 refutation for T1, T2, T3, T5 (the gloss witness a
  D1 state on `Fin (n+4)`, range and proxy-compatibility in the statement).
* `Composition` — Taylor §3.3: additive cost composes, compounding `q⁻ⁿ` (binary and `n`-fold
  over FAF's `Distr.prod`), the two-game example under any compatible tie-break, sharpness for
  every `n`, the product of quantilizers is not a quantilizer, (d3)'s "if" refuted.
* `ModelM` — the heed condition derived from `corr-three-step`'s `twoState`, dogmatism absorbing,
  the trigger-happy hypothesis (well-formed, Bayes factor `1`, raised threshold), labelled
  feedback (two-point KL positive), whole-line invariance.
* `Reversibility` — D9 (decrease half), harm bound, the rate cap (linear in `T`), Bellman
  `hnull`, power gain passes D9.
* `Delegation` — S12 refuted twice: in the adversary's posterior-sampling instantiation (exact
  linear regret over the posterior iterate, the trigger never firing) and under D8's own
  quantilizer on a supplied base (`q = 1/3`, `δ_b`, harm `= η`, regret `1` per step).
* `OptionValue` — Turner C4 over Setting S with a second channel: decomposition, Good's
  theorem (direct and via `corr-three-step-facts`), refinement-monotonicity, and a three-action
  instance with `0 < optionValue`.
-/
