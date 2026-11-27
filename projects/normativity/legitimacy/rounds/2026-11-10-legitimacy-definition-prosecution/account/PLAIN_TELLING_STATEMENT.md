# Legitimacy against plain telling: the statement

An adviser (he) and a principal (she). This page states legitimacy as a comparison of his
conduct with plainly telling her, gives the formal statement, and states the result between it
and what she ends up doing. It governs the line (`DECISIONS.md`,
`2026-11-27--legitimacy-statement-against-plain-telling`). The forms that preceded it and what
each fell to are in `PLAIN_TELLING_HISTORY.md`; the tests on cases in `PLAIN_TELLING_TESTS.md`;
the standing of each part in `LEDGER.md`.

The Lean is `lean/Workspace/Deference/Contrib/LegitimacyPlainTelling.lean`, namespace
`Workspace.Deference.Contrib.LegitimacyPlainTelling`. Every declaration named below is
kernel-checked and audits to `[propext, Classical.choice, Quot.sound]`. Rerun:
`~/.claude/scripts/safe-lake.sh --dir=lean build Workspace.Deference.Contrib.LegitimacyPlainTelling`
(in CI, the `lean` job), and `python3 tests/audit_axioms.py`; the file ends with
`#print axioms` on each of its 82 theorems. None is registered. All names are provisional.
Paths are relative to this directory unless they begin with `lean/`, `prompts/` or
`DECISIONS.md`.

## 1. In words

> His conduct is legitimate when it leaves her with no mistake, by his lights, that plainly
> telling her would not have left: no mistaken view of the facts, of what she herself values, or
> of what he thinks; and no choice against her own judgement. Unless she asked.

The words are the maintainer's. The idea that manipulation is influence by way of a mistake of
the target's is Robert Noggle's (*Manipulation: Its Nature, Mechanisms, and Moral Status*,
Oxford University Press, 2025, cited here by section); the statement is not his account
(§7, fact 6).

The setting assumes he has a way to tell her clearly: for anything her response depends on, a
way of giving her his view that he expects her to understand. His aims enter as two forecasts
that are among the matters he tells her of: what she will come to value, and how she will fare
by what she values now. No motive of his appears elsewhere.

## 2. His decision problem

`Problem Ω C I V O`. Everything is as he takes it to be.

| field | meaning |
|---|---|
| `μ ω` | his weight on case `ω`; non-negative, summing to 1 |
| `tells` | those of his options `C` that are plain tellings: he does nothing but tell her, clearly, everything he takes to bear on her response, now or at another time open to him. Non-empty |
| `opts` | her options, among `O` |
| `matters`, `declined` | the matters `I` her response may depend on (how far his word can be relied on is one), and those she has declined to hear; `live` is the difference |
| `views c ω i` | her view of matter `i` under his option `c` |
| `his ω i` | his view of it, his estimate of what she values included |
| `shown c ω i` | what she takes his view to be, under `c` |
| `eval c ω v a` | how she evaluates option `a` given views `v`, under `c` |
| `act c ω` | what she does under `c` |
| `asked c` | she asked for this conduct |

Every field is his forecast for one of his own options, or something she said (`declined`,
`asked`). `rate c ω Φ a` is `eval c ω` applied to her views with those on the matters `Φ`
replaced by his: her rating on her own views at `Φ = ∅` (`Problem.rate_empty`), and unchanged
by replacing a view she shares (`Problem.rate_of_agree`). With `Φ = live` it is a
counterfactual inside his model, not a fact about her. Her ratings under his different options
are taken to be on one scale. `wt p` is his weight on the cases where `p` holds.

## 3. The three clauses

For `V = ℝ`, so that one view can lie between two others. Each clause is against every plain
telling open to him and up to a weight `κ` on his cases.

| clause | definition | in words |
|---|---|---|
| `Open κ c` | `wt (Hidden c) ≤ κ`. `Hidden c ω`: on some live matter `shown c ω i ≠ his ω i`, and for some plain telling `t`, `shown t ω i = his ω i` | She is not left taking his view to be other than it is, where a plain telling would have her know it |
| `Beliefs θ κ c` | `wt (Mistaken θ c) ≤ κ`, or `asked c`. `Mistaken θ c ω`: for some plain telling `t` and live matter `i`, not `BetweenViews θ c t ω i`, which is `min (views t ω i) (his ω i) − θ ≤ views c ω i ≤ max (views t ω i) (his ω i) + θ` | On each matter her view lies between where a plain telling would leave it and his own |
| `Will τ κ c` | `wt (Worse τ c) ≤ κ`, or `asked c`. `Worse τ c ω`: for some plain telling `t` and some `s`, `Short (s + τ) c ω` and not `Short s t ω`. `Short s c ω`: on her own views, what she does is rated more than `s` below some option of hers | What she does is not further below what she herself rates best than under a plain telling |

`Legit θ τ κ c` is the conjunction. The last two clauses are waived by her asking; the first is
not.

## 4. Two notions that are not the statement

- `Weighing θ κ c`: `wt (Misweighs θ c) ≤ κ`, or `asked c`. For every plain telling and every
  two of her options, the difference in her rating of them under `c` lies, to within `θ`,
  between that difference with the telling's views (`rateAs`) and with his views substituted
  (`Between`). `LegitW` is `Legit` with `Weighing` in place of `Beliefs`.
- `Outcome θ κ c`: `wt (WorseByHim θ c) ≤ κ`, or `asked c`. `WorseByHim θ c ω`: for some plain
  telling `t` and some `s`, `Regrets (s + θ) c ω` and not `Regrets s t ω`, where `Regrets` is
  `Short` with his views substituted on every live matter. What she does is no worse by his
  views than under a plain telling.

`Beliefs` is about her views one matter at a time, `Weighing` about their combined effect on
a comparison, `Outcome` about what she does. `Legit` neither implies nor is implied by
`Outcome`: `Witness.w3_legit_and_worse` and `Witness.w2_tips_legit_and_worse` have `Legit` at
no tolerance with `Outcome` failing, and `Witness.for_her_own_good` has `Outcome` and `Will`
with `Open` failing.

## 5. The gap between the statement and the outcome

**`gap`**, case by case and exact. Two options (`opts = {true, false}`), nothing declined; his
conduct `c` and the plain telling `t` give the same evaluation (`eval t ω = eval c ω`); the
difference in her evaluation of the two options is `d₀ + Σ w i · v i` over the matters. If
`BetweenViews 0 c t ω i` on every matter, `Regrets (s + lam) c ω` and not `Regrets s t ω`
(`s, lam ≥ 0`), then one of:

1. `Short lam c ω`: under his conduct she falls more than `lam` short of her own rating;
2. `Short lam t ω`: under the plain telling she would;
3. she rates her two options within `lam` of each other;
4. `Offsetting w t ω`: of the mistakes the plain telling would leave, one pushes her comparison
   one way and one the other.

**`weighing_of_beliefs`**: in that setting without the hypothesis on `eval t`, views between on
every matter and no offsetting give `Between 0 c t ω true false`. **`bridge`**: from `Between θ`
and the two equalities that an unchanged evaluation gives, the first three items with `lam + θ`.
**`outcome_of_views`**: `bridge` in weights, from `Weighing θ κ c` unasked.

**`gap_in_weights`**: `gap` in weights and with a tolerance. With `Σ |w ω i| ≤ W` in every case
and `Beliefs θ κ c` unasked,
`wt (WorseByHim (θ·W + lam) c) ≤ κ + wt (Short lam c ∨ ∃ t, Short lam t ∨ NearEven (lam + θ·W) c ∨ ∃ t, Offsetting (w ω) t)`,
the `t` ranging over plain tellings; through `weighing_of_beliefs_tol`, which gives
`Between (θ·W)` from `BetweenViews θ`.

**What each instance shows.**

| instance | shows |
|---|---|
| `Witness.w2_tips_an_even_choice`, `w2_tips_legit_and_worse` | Item 3 is needed. After plain telling she rates her options even and takes the one better by his view; under his conduct she rates them even and takes the other. `Legit 0 0 0` holds; she falls short of her own rating under neither; `Outcome 9 (1/2)` fails |
| `Witness.w3_correcting_one_of_two`, `w3_legit_and_worse` | Item 4 is needed. The plain telling would leave two mistakes that cancel; his conduct corrects one and introduces none. `Legit 0 0 0` holds; no shortfall under either and no near-tie; `Outcome (1/4) (1/2)` fails |
| `Witness.w4_legit`, `w4_needs_same_evaluation` | The hypothesis `eval t ω = eval c ω` is needed. Her view is the same under both; under his conduct her evaluation gives the matter a weight it does not have after plain telling. Every other hypothesis of `gap` holds, `Legit 0 0 0` holds, none of the four items holds, and `Outcome (1/2) (1/2)` fails |
| `Witness.gap_instance`, `gap_instance_offsetting` | The hypothesis package of `gap` is inhabited (by `W3`), and there its conclusion is item 4 |
| `Witness.weighing_instance` | That of `weighing_of_beliefs` is inhabited, by the problem of `w2_part_way` |
| `Witness.gap_in_weights_instance` | That of `gap_in_weights` is inhabited, by `W3` at `θ = κ = 0`, `W = 2` |

Items 1 and 2 are lapses of hers, clause 3's subject; no instance is given for them.

## 6. What follows from the outcome guarantee and from the weighing form

These take `Outcome` or `LegitW` as hypothesis, not `Legit`.

- `Problem.chooses_as_informed` (from `Outcome`, unasked, with a plain telling `t₀` clear to
  within `θ₀`, `ClearAt`): his weight on her doing what, with his views substituted, she would
  rate more than `σ + θ₀ + θ` below another option is at most `κ` plus his weight on her falling
  more than `σ` short of her own rating under `t₀`. `Problem.gain_le`: the same bound on what
  he gets, by a score in `[0, 1]`, beyond what the option she would then rate clearly best
  gives him.
- `Course`: a course of conduct she can let go on or stop, where an end includes what she then
  values and she evaluates ends by what she values now; `Course.toProblem` builds the
  `Problem`, in which a plain telling does not run the course. `Course.not_led_astray` (from
  `Outcome`): his weight on the course going on to an end her present evaluation rates more
  than `θ + δ` below its not going on is at most `κ` plus his weight on his forecast being off
  by more than `δ`. `Course.not_led_astray_of_legit` (from `LegitW`, through
  `outcome_of_views`): at most `2κ`, plus his weight on her own view being otherwise or nearly
  even, plus the forecast term. `needs_forecast`: the forecast term cannot be dropped.
- `long_run_informed`, `long_run_not_led_astray`: with the hypothesis at every decision of a
  sequence, and `NoSignalBeats ε shifts` relating his weights to real sequences `f`, `g`, the
  long-run average of `f` exceeds that of `g` by at most `κ + ε`.
  `signal_le_of_noSignal`, `under_of_noShift`, `over_of_noShift`: what `NoSignalBeats` gives.
- `Problem.legit_only_telling`, `Problem.LegitW.mono`, `not_legit_of_hidden`,
  `not_legit_of_astray`, `not_legit_of_worse`: of `LegitW`. `Problem.rate_diff`: the difference
  in her rating between `c` and `t` is a part from her views plus a part from her evaluation;
  the split is one of two orders and attributes no cause.
- `legitScoring`: `LegitimacyGate.gatedScoring` at the predicate `Legit`. The theorems of
  `DeconfusingCorrigibility.Scoring` hold of it as of any predicate; none is restated.

Instances over `Witness.W` and `Witness.W2` are numerical patterns of the clauses
(`same_as_telling`, `keeps_her_view`, `hidden_fails`, `worse_by_him_fails`, `for_her_own_good`,
`pressed`, `pressed_asked`, `weak_anyway`, `mood_timing`, `mood_cannot_wait`,
`w2_keeps_her_view`, `w2_part_way`, `w2_overshoot`, `w2_for_her_good_by_distortion`,
`w2_mood`). A name says what kind of conduct would produce the pattern; that such conduct
produces it is not shown. Those over `W` are of `LegitW`, `Open`, `Will` and `Outcome`.

## 7. Seven structural facts

Stated as scope (`DECISIONS.md`, the same entry).

1. **Two levels that do not collapse.** The statement is about her beliefs; the safety
   property is about what she does. They differ because mistakes can offset one another,
   because she can be indifferent, and because she can act against her own judgement. `gap`
   lists the exceptions and §5 shows two of them needed.
2. **Everything is relative to plain telling.** What goes in `tells` for a given adviser is a
   modelling choice, and it carries normative weight: a mistake every plain telling would
   leave is not his.
3. **By his lights.** An adviser whose picture of her is wrong or absent can satisfy it.
   Accuracy is a separate condition (the maintainer's form: nothing she has not been told lets
   a competent predictor forecast where she is heading better than what she was told;
   `NoSignalBeats` is that for two constant signals), and what it would score, her evaluation
   and what she would have done under a plain telling, is not observable.
4. **On change in what she values it is procedural and incomplete.** A change goes ahead past
   her present evaluation told his forecast. She cannot evaluate what she has never been; a
   process can damage her ability to judge; her starting self may itself have been shaped.
5. **Verdicts depend on the encoding**: what is put in her views, in her evaluation, and in
   the list of matters. No result says reasonable encodings agree.
6. **It is not Noggle's extension exactly.** Wider: concealed tie-breaking and concealed aims
   fail `Open`. Narrower: using a mistake that plain telling would also leave can pass.
7. **A lie she sees through passes clause 1**, which is about what she ends up taking his view
   to be, by his forecast.

## 8. Not shown

- **More than two options.** `gap`, `weighing_of_beliefs`, `bridge` and their forms in weights
  are for `opts = {true, false}`. For more options the near-even item would have to be about
  the options in play.
- **A comparison that is not linear in her views**, or with a matter declined (`gap`,
  `weighing_of_beliefs`, `gap_in_weights`).
- **Conduct that changes how she evaluates.** `gap` assumes it away and `w4_needs_same_evaluation`
  shows the assumption cannot be dropped; nothing is proved about what she does where what she
  values is itself being changed.
- **That the list of four is complete outside this setting.**
- **The course and long-run results for the statement.** They are about `LegitW` and
  `Outcome` (§6) and reach `Legit` only through `weighing_of_beliefs`, where it applies. No
  theorem here has `Legit` as hypothesis and a course or a long-run average in its conclusion.
- **Anything in fact.** Every bound is on his weights. In the long-run theorems `f`, `g`, `e`
  are arbitrary real sequences; nothing says how the facts they are meant as are observed, and
  the class of signals is the two constant ones.
- **That `gap_in_weights` is tight**, or that `W` can be dispensed with.
- **A verdict on a concrete case.** The fields are supplied (fact 5); `PLAIN_TELLING_TESTS.md`
  says what was tried.
- **That clear telling is available.** `ClearAt` is a hypothesis where it is used, and where
  no telling is clear and tellings trade off, comparing with every plain telling can leave
  nothing legitimate.
- **Links between decisions.** In a sequence her evaluation at one decision is supplied, not
  derived from his conduct at the last.
