import Cleanroom.Corrigibility.CorrLiShutdown.Setting
import Cleanroom.Corrigibility.CorrLiShutdown.Calibrated
import Cleanroom.Corrigibility.CorrLiShutdown.Dichotomy
import Cleanroom.Corrigibility.CorrLiShutdown.Identity
import Cleanroom.Corrigibility.CorrLiShutdown.Intercept
import Cleanroom.Corrigibility.CorrLiShutdown.Pairs
import Cleanroom.Corrigibility.CorrLiShutdown.Legitimacy
import Cleanroom.Corrigibility.CorrLiShutdown.Map
import Cleanroom.Corrigibility.CorrLiShutdown.WitnessesA
import Cleanroom.Corrigibility.CorrLiShutdown.Reports
import Cleanroom.Corrigibility.CorrLiShutdown.SignedError
import Cleanroom.Corrigibility.CorrLiShutdown.Collision
import Cleanroom.Corrigibility.CorrLiShutdown.WitnessesB
import Cleanroom.Corrigibility.CorrLiShutdown.PaperPair
import Cleanroom.Corrigibility.CorrLiShutdown.WitnessesC
import Cleanroom.Corrigibility.CorrLiShutdown.Paradox
import Cleanroom.Corrigibility.CorrLiShutdown.Drift
/-!
# `corr-li-shutdown`: the shutdown thesis over logical induction
Root module of the package `Cleanroom.Corrigibility.CorrLiShutdown`; dependents import this one
name. Mandate: `run/wp/corr-li-shutdown/corr-li-shutdown-mandate.md`; report, findings and
ledger beside it. Scope: **one-way** throughout — the agent reads the overseers' press as a
decided ledger atom; the overseers never read the agent.
* `Setting` (T3): `ShutdownPair`, `pressAtom`, `proxy`, `uDef`, `uCom` with their generability
  theorems, `toyX`, `rho`/`rhoHat`, the ledgers as day predicates, `PressReadable`.
* `Pairs`: `ShutdownPair.ofOneWayPair` (roles swapped), `ShutdownPair.ofTable` / `.ofTables`
  (any computable press table; imports `LiQuoteLane.OneWay`, as `PaperPair` imports
  `LiQuoteLane.Witnesses`).
* `Identity` (T1): the two-option identity on the toy family, the LI threshold, the agreement
  of the two press forms.
* `Calibrated` (T4): calibrated obedience over the ramp, split by ledger; full limits under
  good feedback; the hybrid iff; the finite-press lemma.
* `Dichotomy` (T5): the mass-fraction lemma, the defiance dichotomy, Cor. 4.1/4.3, the
  base-rate identity.
* `Legitimacy` (T2): no generable legitimacy predicate has forced content; the legitimacy
  weight; reading (a) of T2(b) stated OPEN over the current-day weight quote
  (`decidedWeight_factors_open`, the wiki's open-problems item 4; repair round 3).
* `Paradox` (T2(c)): the exact (hard-indicator) self-trust inequality **fails** on FAF's
  paradoxical family (`exact_selfTrust_refuted`, P; round 0's OPEN, proved in repair round 2
  through the two-share affine family `χ_n + ∼χ_n` and `thm:provind` on `χ_n ⋏ ∼χ_n`).
* `Intercept` (T7): the Bernoulli lemma, the budgeted wealth chain, the record inequality.
* `Map` (T8, T9, T20): Self-Trust is anticipation; the thesis sentence is `cee`; the finite
  tower identity.
* `WitnessesA`: the no-T7 witnesses (tag-0 `atomDP`, always-press overseer).
* `Reports` (T12, T17): trust in reports; non-dogmatism and no-FUD.
* `SignedError` (T6): the realized signed error is unbounded (core P), the dichotomy
  `BddAbove → T → −∞` and the trichotomy under the two-sided ramp clause (P/C); the two-sided
  form over the Lean's clause is **refuted** (`signedError_two_sided_refuted`, audit r2); FAF
  form resting on the OPEN certificate and **vacuous** at `succ` (F17).
* `Collision` (F17): good feedback at `succDeferral` is never pseudorandom — the FAF-facing T6
  package is unsatisfiable (P).
* `WitnessesB`: full-package witnesses for the feedback rows (`dropDayZero`, a weighting that
  vanishes on day `0` by construction, generability a theorem), T5(⇐) and T1(b) (N−).
* `PaperPair`: the inductor-overseer shutdown pair over FAF's paper process, same-day ledger
  (`paperShutdownPair`, N+ as a definition); T1(c) instantiated on the paper pairs.
* `WitnessesC`: the content witness (decision 6(ii)) over the **ledgered** diagonal
  (`truthStarL`, pseudorandom relative to the agent's own ledgered market, (a)); T4(a)/(b)'s
  packages inhabited with the realized wrongness tending to `p` (N+, `partial` on the ledgered
  analogue of `li-pseudorandom` T7, taken as a hypothesis; stated OPEN, unused).
* `Drift` (T6, repair round 3): F11's drift instance built — the barrier walk `driftExcess` and
  the Boolean stream `driftTruth` of density `1/2` with `T → −∞`; the trichotomy's two-sided
  package is inhabited in its first two cases (`signedError_trichotomy_atBot_realized`,
  `signedError_trichotomy_atTop_realized`, N+; audit r3 adversarial B1).
-/
