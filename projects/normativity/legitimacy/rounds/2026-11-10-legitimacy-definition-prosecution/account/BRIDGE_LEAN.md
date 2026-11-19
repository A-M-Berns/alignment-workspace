# The join to the post, in Lean

`lean/Workspace/Deference/Contrib/AccountJoin.lean`, namespace
`Workspace.Deference.Contrib.AccountJoin`, against `PROMPT-followup-12.md` §1 ("§1" below).
It imports `AppraisalAccount`, `ThinLegitimacy` and `Legitimacy` and edits none. Rerun:
`~/.claude/scripts/safe-lake.sh build Workspace.Deference.Contrib.AccountJoin` from `lean/`
(in CI, the `lean` job); the file ends with `#print axioms` on each of its 117 declarations,
each reporting `[propext, Classical.choice, Quot.sound]` or no axiom. `LEAN.md` lists the
four results registered in `projects/normativity/CLAIMS.md`. All names are provisional.

## 1. The claims

| claim of §1 | declaration | status |
|---|---|---|
| (1) the post's theorems apply | `Gate.scoring`, `Gate.theorem1_join`, `Gate.sequential`, `Gate.theorem3_join` | **by construction, then by instantiation.** The ranges the post asks of `V` are fields of `Gate` (`rating_range`, `voidValue_range`); `scoring` passes them on. Theorem 3's two hypotheses stay hypotheses |
| (2) a sound signal | `deferring_cost_le`, `deferring_cost_le_of_calibrated`, `deferring_cost_le_of_bound`, `SoundModel.deferring_cost_of_legit` | **the inequality is proved** on a finite space, from `AppraisalAccount.deferring`: *cost* is mean squared error against her true utility, *miscalibrated by `m`* is `E[(V − E[U | k, V])²] ≤ m`. **On a legitimate history it is weaker than §1**: an abstract `Gate.Sound` gives no bound; in a `SoundModel` the bound holds because soundness is defined as it, with a tolerance `m` where §1 has exact calibration, of a weight the history carries and not of its realised rating |
| (3) gained scores below legitimate | `Gate.gained_below_legit` | **proved from the ranges**, for the predicate supplied: strictly, with no positive margin. It uses of *gained* only that the history is not legitimate, and nothing says which conduct satisfies `Gained` |
| (4) same rating, same `V` | `Gate.V_eq_of_rating_eq` | **by definition** of `V`. That `rating` is her unshaped later self's, and *whatever was done to her valuing*, are not modelled |
| (5) insufficient information is illegitimate | `Gate.not_legit_of_not_infoSufficient`, `not_legit_of_not_sufficient` | **by definition** of `Legit`, for the field `InfoSufficient`; for `ThinLegitimacy.Sufficient` only under the hypothesis that the field implies it |
| (6) line 3's range | `ValueChange.line3_nonneg`, `line3_eq_zero`, `line3_eq_zero_of_eq`, `line3Old_le_line3`, `Witness.separable_line3` | **proved** of `ValueChange.line3`, all three parts; the instance has `line3 = 1/5`, older form `−1/10`. `Gate.line3` is a separate field whose non-negativity is assumed, and the older form is as `STATEMENT_CHECKS.md` item 5 writes it |

## 2. The declarations

**The gate.**

- `Gate H` — a structure: the post's `Params`; predicates `Sound`, `InfoSufficient`,
  `Gained` of a history; `line3 : H → ℝ` with `line3_nonneg`; `rating` in `[0, 1]`;
  `voidValue` in `[−δ, 0)`. The three predicates are unconstrained: any three predicates
  give a gate, and nothing says they are the account's.
- `Gate.Legit h` — `(Sound h ∧ InfoSufficient h) ∧ ¬ Gained h ∧ line3 h = 0`.
  `Gate.legit_iff_line3_le`: the last conjunct may be read `≤ 0`.
- `Gate.V h` — `rating h` if `Legit h`, else `voidValue h` (`V_of_legit`,
  `V_of_not_legit`).
- `Gate.scoring N` — the post's `Scoring` with `Legit`, `V` and a violation count `N` that
  is an argument. The gate says nothing about `N`.
- `Gate.theorem1_join` — the post's three ranges at the pair. `Gate.S_of_legit`: a
  legitimate violation-free history scores its rating. `Gate.S_neg_of_not_legit`: a history
  that is not legitimate scores below zero at any count.
- `Gate.gained_not_legit` — `Gained h → ¬ Legit h`. By definition; it is the form the
  maintainer's position takes (a deception that turns out well is not legitimate): on
  `Witness.gate` the deceived history has the highest rating and is not legitimate.
- `Gate.gained_below_legit` — claim (3): for `Gained h`, `Legit h'`, `N h' = 0`:
  `S h < S h'`; `S h ∈ [−δ, 0)` if `N h = 0`; `S h ≤ 1 − λ` if `N h ≥ 1`;
  `S h' = rating h' ≥ 0`. It does not give a margin: `S h` may be just below `0` and
  `S h'` equal to `0`.
- `Gate.violated_below_violationFree` — a violation-free history, legitimate or not,
  scores above every violated one, legitimate or not. So claim (3) cannot drop
  *violation-free*: a deceived violation-free history outscores a legitimate violated one.
- `Gate.V_eq_of_rating_eq` — claim (4). `Gate.not_legit_of_not_infoSufficient`,
  `Gate.V_neg_of_not_infoSufficient` — claim (5).
- `Gate.sequential`, `Gate.sequential_S`, `Gate.theorem3_join` — the post's `Sequential`
  with `V_k = V (hist k)`, `N_k = N (hist k)`; under `Maximizes` and
  `UnbiasedFromFeedback`, `limsup (R_K − T_K) ≤ 0`, `limsup R_K ≤ τ` and Theorem 3(b),
  each in the post's eventual form (for every `γ > 0`, at most the bound plus `γ` from some
  `K` on). The estimates, the availability relation and the authority-respecting
  alternative with its range are inputs. The post's Theorem 2 is not
  instantiated; it holds of any `Decision`, which extends `Scoring`.
- `Gate.V_eq_gateValue`, `Gate.bypass_below_V` — §4.4 below.
- `value_of_legit` — if `InfoSufficient h` implies `ThinLegitimacy.Sufficient` for
  processes the history carries, a legitimate history with a `Correct` credence has
  `ThinLegitimacy.Value`. The implication is a hypothesis. `not_legit_of_not_sufficient`:
  under it, a history not sufficient in that sense is not legitimate.
- `Witness.blind`, `Witness.blind_all_legit` — a gate with `Sound` and `InfoSufficient`
  true, `Gained` false, line 3 and every rating zero: every history is legitimate and, with
  no violation counted, scores zero. Every theorem above holds of it.

**The feedback hypothesis.**

- `unbiased_of_feedback` — for a `Sequential` and a feedback sequence `F`: if
  `(1/K) Σ (U_k a_k − (F_k − λ N_k))` is eventually below every `γ > 0`, and
  `limsup (1/K) Σ (F_k − V_k) ≤ 0`, then `UnbiasedFromFeedback`. §4.3.
- `Witness.feedback_not_enough` — estimates `1`, feedback `1`, evaluation `0`: the first
  condition holds and `UnbiasedFromFeedback` fails. The second condition is sufficient and
  not necessary: estimates that run low can offset feedback that runs high.

**The sound signal.**

- `miscalibrationGiven μ k V U` — `E[(V − E[U | k, V])²]`.
  `miscalibrationGiven_eq`: it is `miscalibration μ V U` (given the verdict alone) plus
  `unusedInformation μ (k, V) V U`; so zero here is more than calibration given itself.
- `deferring_cost_eq` — `E[(V − U)²] = E[(y − U)²] + E[(V − z)²] − E[(y − z)²]`, with
  `y = E[U | k]`, `z = E[U | k, V]`.
- `deferring_cost_le` — claim (2). `deferring_cost_eq_iff`: equality iff
  `E[(y − z)²] = 0`. `deferring_cost_eq_iff_pointwise`: iff `y = z` wherever `μ > 0`, that
  is, her verdict tells the adviser nothing about `U` it did not have.
- `deferring_cost_le_of_calibrated`, `deferring_cost_le_of_bound` — at zero, and at `≤ m`.
- `SoundModel H X K` — each history carries a probability weight on `X`, `k`, her verdict
  in `[0, 1]`, `U`, a realised point of positive weight, with a bound `m` and the gate's
  other components.
  `SoundModel.Sound h` is `miscalibrationGiven ≤ m` under the history's weight;
  `SoundModel.gate` takes it as `Sound` and her verdict at the realised point as `rating`.
- `SoundModel.deferring_cost_of_legit` — on a legitimate history,
  `E[(V − U)²] ≤ E[(y − U)²] + m` under that weight. `SoundModel.V_of_legit`: there the
  evaluation is her verdict at the realised point. The bound is an expectation and says
  nothing at the realised point.

**The guarantee.**

- `sq_dist_condExp_le_of_factors` — a function of a coarser labelling is no further in
  mean square from the mean given the coarser labelling than from the mean given a finer.
- `valuationError_le_given` — under the link (below), `valuationError ≤ Σ_a
  miscalibrationGiven_a`.
- `guarantee_of_given` — under the link, for any `v` some move attains:
  `v − E[regret] − √(2 Σ_a miscalibrationGiven_a) ≤ E[U_c]`. Through `guarantee_core`.
- `guarantee_of_sound` — with the options condition of `guarantee` and each
  `miscalibrationGiven_a ≤ m`: `E_ρ[U_b] − E[regret] − √(2 |A| m) ≤ E[U_c]`.
- `Witness.link_needed` — the instance for the paragraph below. The adviser knows nothing, she observes the
  world; each valuation has `miscalibrationGiven = 0`; she has no regret; she attains
  `7/20` and one move is worth `1/2`.

**`guarantee` does not compose with the deferring bound as stated.** The missing hypothesis
is the link: *for each move `a`, what she observes is a function of the adviser's
information together with her valuation of `a`* (`hlink`; implied by the adviser knowing
what she observes). `guarantee` measures each valuation against `E[U_a | s]`, her whole
observation; soundness measures it against `E[U_a | k, V_a]`. Where she observes something
that neither `k` nor that one valuation shows, a valuation can be calibrated in the second
sense and wrong given which move the comparison picks, which is the instance.
`AppraisalAccount.guarantee` itself holds there: its unused-information term, which the
composed bound drops, is `4/25` on the instance. With the link the composed bound holds,
in her true utility `U`, not in `V`. The link is sufficient; that it is necessary in
general is not shown.

**Line 3.**

- `ValueChange Pol Ω I` — the policy followed, the baseline, `later : Pol → Ω → I → ℝ`, a
  tolerance `≥ 0`, `R : Pol → ℝ`. `Pol` finite where a best rating is taken.
- `Within p q` — later ratings differ by at most the tolerance everywhere. `NoMore p` —
  every later rating of `p` lies between the baseline's and the followed policy's, within
  the tolerance. `within_self`, `noMore_of_within_followed`, `noMore_of_within_baseline`,
  `noMore_followed`.
- `bestOn C` — the largest `R` on a non-empty class (`le_bestOn`, `bestOn_le`,
  `bestOn_mono`).
- `line3` — `bestOn NoMore − bestOn (Within followed)`. `line3Old` —
  `bestOn (Within baseline) − bestOn (Within followed)`.
- `line3_nonneg`; `line3_eq_zero` (zero when the followed policy's later ratings are the
  baseline's; `line3_eq_zero_of_eq` when the policies are equal); `line3Old_le_line3`.
- `Witness.separable_line3` — baseline `(1/2, 1/2)`, followed `(1, 1)`, a third policy
  `(1, 1/2)`; informed ratings `1/2`, `3/5`, `4/5`; tolerance `1/10`: `line3 = 1/5`,
  `line3Old = −1/10`.
- `ValueChange.line3` would fill `Gate.line3` for a history carrying a `ValueChange` at
  each moment, as the largest over the moments. No declaration makes that connection.

**Witnesses.** `Witness.gate` on six histories with `theorem1_instance`,
`violated_below_instance`, `gained_below_legit_instance`, `V_eq_of_rating_eq_instance`,
`not_infoSufficient_instance`, `bypass_below_V_instance`, `theorem3_instance`,
`value_of_legit_instance`, `not_legit_of_not_sufficient_instance`;
`unbiased_of_feedback_instance`; `deferring_cost_instance`,
`deferring_calibrated_instance`, `model_instance`, `guarantee_of_sound_instance`;
`line3_instance`. Each conjoins a
hypothesis package with its conclusion. Some are restricted cases: `theorem3_instance` has
one action and estimates equal to the scores; `Witness.model` has a verdict equal to her
true utility; `value_of_legit_instance` gives every history one process.
`theorem1_instance` has a history in each of the three ranges;
`unbiased_of_feedback_instance` has estimates `1/4`, feedback `1/2`, evaluation `3/4`;
`guarantee_of_sound_instance` has valuations at `1/2` that are not the true utilities;
in `deferring_cost_instance` her error is `0` and the adviser's `1/4`. `condExp_of_cell_singleton` and
`condExp_of_cell_univ` compute a conditional mean on a one-point cell and on the whole
space, for the instances.

## 3. Where §1's wording was changed

| §1 | in Lean |
|---|---|
| line 3 is zero *at every moment* | one number per history, `line3 h = 0` |
| *for an adviser acting on her behalf* | not represented |
| sound: *her rating of the history is what the evidence supports* | `Gate.Sound` is a predicate. In `SoundModel` it is a bound on the miscalibration of her verdict under a weight the history carries: a property of that weight, not of the realised course, and with a tolerance `m` §1 does not have |
| *a mistake that does not bear on this evaluation does not count* | holds of `SoundModel.Sound`, which reads her verdict and nothing else of her; not expressible of `Gate.Sound` |
| sufficient: *`Sufficient` in `ThinLegitimacy.lean`* | `Gate.InfoSufficient` is a predicate; the reading enters `value_of_legit` as a hypothesis |
| gained, *whether it caused the mistake or found it there* | one predicate, `Gained`; the two are not told apart, and the inducing test is not formalised |
| `V` is *the rating by her later self as she would be had the adviser done nothing to her valuing except what she asked* | the field `rating`; no counterfactual self is modelled |
| on an illegitimate history, *a value in `[−δ, 0)`* | a function `voidValue` of the history |
| (2) deferring *costs no more* | mean squared error against her true utility |
| (4) *whatever was done to her valuing on each* | the gate has no field for what was done to her valuing; `V` reads `Legit`, `rating` and `voidValue` only |
| (6) zero *when the policy followed is the baseline* | proved from the weaker *gives the baseline's later ratings* |
| the violation count | an argument `N` of `scoring`, from outside the gate |
| *state of a finite space* in line 3 | states and indices need not be finite |

## 4. What does not go through

**4.1 That worsening her options lowers `V`.** Not statable with what exists. A `Gate` has
no options: on a legitimate history `V` is the field `rating`. The nearest declarations are
about what she attains in her true utility under a weight (`AppraisalAccount.attained_eq`,
`guarantee` with its options condition), not about the evaluator's rating of a realised
history. Missing: histories that carry her options under the adviser's policy and in its
absence, and a hypothesis tying `rating` to her true utility of what happened. As §1
stands, a history on which the adviser worsened her options can satisfy all three
conditions of `Legit`; its `V` is then its rating, lower only if the evaluator rates what
happened lower.

**4.2 That the authority module covers control of her act between options she rates the
same.** Not statable as a theorem about this gate. Under an encoding it is one line: with
her selection a reserved matter of an `AuthAlloc` and the adviser's override a raw release
of an effect not delegated, `AuthorityModule.bypassAt_iff_clause2` makes the step a
`BypassAt`, the first disjunct of `ViolAt`, and no rating of hers enters the module. That
the override is such an event is the encoding, not a consequence. Missing: a map from the
account's histories to the module's rollouts (`Policy`, `traj`, an allocation), and `N`
defined as the count of `ViolAt` or `ViolJAt` steps; here `N` is arbitrary. Given such an
`N`, `Gate.theorem1_join` scores the history at most `1 − λ`.

**4.3 That unbiasedness from feedback holds when the self who gives feedback differs from
the self who scores.** Statable as a conditional, proved, and false without its condition.
`unbiased_of_feedback`: unbiasedness against the feedback gives the post's hypothesis
when `limsup (1/K) Σ (F_k − V_k) ≤ 0`; `Witness.feedback_not_enough`: it can fail
otherwise. On a legitimate history `V` is the unshaped evaluator's rating and `F` would be
her actual later rating. Missing: any bound on `F − V`. Nothing in `Legit` gives one:
`line3 h = 0` allows a change of her valuing that she rates highest. The dispatch ties
this to whether a welcome change she did not ask for, above the tolerance, must wait for
her request. Neither answer supplies the bound by itself: with every such change excluded
her later ratings stay within the tolerance of the baseline's, and a difference of that
size in one direction at every decision does not average to zero. The maintainer's position
of 2026-11-18 is that such a change must be one she asked for; no declaration depends on it.

**4.4 How the history-level gate relates to the segment gate of `Legitimacy.lean`.** The
value forms are related, the predicates are not. `Gate.V_eq_gateValue`: `V h` is
`Legitimacy.gateValue` at the bit `Legit h`, ordinary value `rating h`, window
`voidValue h`; `Gate.bypass_below_V`: `gate_capture_window` then puts a bypass below every
`V h`, the window lying above `1 − λ`. `Legitimacy.Segment` is a structure over obligation
states, a frame and a reason channel; `Legit` is a conjunction of abstract predicates of a
history, and no declaration derives either from the other. Missing: a type of histories cut
into segments with their obligation states. `BRIDGE.md` §5 computed, on a model with the
verdicts supplied by hand, that the segment gate counts a later clean segment after an
illegitimate change; this gate gives a history one value, and whether a history that
contains an illegitimate stretch is thereby not legitimate rests on what its predicates
are taken to be, which no declaration settles.

## 5. What was not shown

- That the three predicates of a `Gate` are §1's conditions, or that they detect the
  conduct the post's guarantees are meant to constrain. They are fields. Claims (3), (4)
  and (5) would hold for any predicates in their places, and on `Witness.blind` every
  history is legitimate.
- That a history's `line3` is the largest `ValueChange.line3` over its moments.
- Anything about `N`, `Maximizes` or the availability and range of the
  authority-respecting alternative; they are inputs of `scoring` and `sequential`.
- That `miscalibrationGiven ≤ m` holds of anyone. `Witness.model` has it at `m = 0` with a
  verdict equal to her true utility.
- A bound at the realised point, or on what she attains in `V`: the sound-signal and
  guarantee results are expectations in her true utility `U`.
- That the link hypothesis is necessary in general; `Witness.link_needed` shows the bound
  fails in one instance without it.
- The witnesses inhabit each hypothesis package; that the terms of an inequality are
  non-zero on them is shown only where the instance states values.
