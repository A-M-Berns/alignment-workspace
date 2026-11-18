# Which of the scoring theorem's assumptions about her can be derived

Against `PROMPT-followup-13.md` §4.2. "§1" is that prompt's scoring theorem, in Lean as
`SCORING.md` reads it. The process account is `ThinLegitimacy.lean`,
`TransparentChannel.lean`, `ReasonMediatedAuthorship.lean` and `Legitimacy.lean`. The Lean
statements below are in `lean/Workspace/Deference/Contrib/ScoringTheorem.lean`, section
*What the process conditions give*; the instances are computed exactly by
`account/derivation.py`, which the round's runner runs against the table of §4. All names
are provisional.

**The answer.** The derivations do not reduce the welfare side of §1 to the conduct side.
On a course that is clean throughout, the facts of conduct still do not supply D1 or D2:
her model of the adviser, her coherence, her prior and what moves her valuing are further
premises (I2, I4, and the unasked welcome change). What the process conditions give is
D1 and D2 from conduct **together with** those premises, and only at the courses that
meet them.

## 1. D1 from the process conditions

**The reading.** A world `w` is everything about the history, with her prior `π`. The
adviser's record is her later record `r`, produced by the actual process `A`, a kernel
that contains the adviser's course, how it forms its beliefs, and how it selects. `fe` is
a function `g` of the world. Under audit she evaluates at `r`:
`evalOf V g r = Σ_w V r w · g w`, the expectation of `g` by her credence `V r`. Both are
stipulations of the reading and not consequences of anything.

**Exact.** `eval_unbiased_of_correct`: if her credence is the actual posterior
(`Correct π A V`), then `Σ_w Σ_r π(w) A(r | w) (evalOf V g r − g w) = 0`. This is
averaging: `Correct` is the calibration premise, and the lemma does not establish it.
`eval_unbiased_of_process` obtains `Correct` from `Coherent π M F`, `Authorship F V` and
`WeakTransparent π A M` by `correct_of_coherent_authorship_transparent`.
`WeakTransparent` is sufficient and stronger than D1 needs: it makes the whole posterior
agree, where D1 needs the expectation of one `g`.

**On part of the records.** `eval_unbiased_on_of_correct`: for any set of records at each
of which her credence is the actual posterior, the same sum over that set is zero,
whatever her credence is elsewhere.

**Given what the adviser knows.** `eval_unbiased_given_of_correct`: if a variable `k` of
the world is a function of the record wherever the joint weight is non-zero, the sum
restricted to `k = k₀` is zero, for each `k₀`; at a `k₀` of positive weight that is a
conditional mean of zero, and at one of zero weight it says nothing. With `k` what the
adviser knows this is D1 at each `k`, and the added hypothesis says the adviser recorded
what it knows. It is `ThinLegitimacy.Openness` with the baseline the adviser's knowledge,
in the deterministic case and on the support only. Where `k` holds things that do not bear
on `g` it asks more than disclosure of what is relevant. Without it the conditions give D1
only on average over `k` (I3).

**With tolerances.** `eval_bias_le_defects`, for deterministic records `a` (actual) and
`m` (her model's), by the method of `value_loss_le_defects`: if `F` is coherent with `m`
and every evaluation by `V` at any record lies within `D` of every evaluation by `F` at
any record, `|E_π[evalOf V g (a w) − g w]| ≤ D · (transparencyDefect + authorshipDefect)`.
The bound is under `π`, averaged over `k`. There is no version at each `k`: a defect of
mass `p` inside one cell of `k` can bias the evaluation there by the whole width.

**One-sided or two.** What follows is two-sided: `E[v − fe] = 0`, or
`|E[v − fe]| ≤ D(τ + α)`. D1(a) and D1(b) are both consequences, at whichever course the
premises hold. Nothing in the premises separates the directions.

**Whose conditions.**

| hypothesis | on whom |
|---|---|
| `Authorship F V` | the equality `V = F`. The adviser's conduct can break it, and so can a lapse of hers; the definition does not say who did |
| the record determines `k` | the adviser's conduct: disclosure, of all it knows |
| `WeakTransparent π A M` | a relation between the actual process and her model. Its conduct part is `TransparentChannel.Realizes` (the channel is the declared reference on its declared inputs; `ThinLegitimacy.transparent_of_realizes`). That her model is the reference, and that the reference's inputs — the adviser's beliefs, its selection — relate to the world as her model says, are not conduct (I2, I4), though the adviser's conduct shapes those inputs |
| `Coherent π M F` | her reasoning, given her prior and model; it says nothing of their accuracy |
| her evaluation is `evalOf V g` with `g = fe` | an assumption about her: her valuing is the same under audit as shown everything, and her evaluation is her credence's expectation of it. Non-interference does not give it |
| the expectation is under `π` | neither: D1's expectation is the law of the world given the adviser's course and knowledge; it is hers only if her prior is that law |

## 2. D2 from reason mediation

`ReasonMediated β R V D z` says: two audited continuations that leave the same reasons
leave the same payload. Take the payload to be her valuing `Val` and the view to be `Rv`,
the admitted inputs to her valuing. `valuing_eq_of_mediated`: if
`ReasonMediated β Rv Val D z`, and the course taken `q` and a baseline course `q₀` are
both audited and leave the same `Rv` at the exterior `z`, then
`Val(β q z) = Val(β q₀ z)`, so every rating of the actual history read off the two
valuings agrees. The theorem is the hypothesis applied to `q` and `q₀`. What makes it
about D2 is supplied by the reading: that `q₀` is the adviser changing nothing in her
valuing except what she asked, that `fe` and `fbar` are those ratings, and that `Rv` holds
the admissible inputs and no others.

**The form.** Exact, at one exterior; with the hypotheses at every exterior, at every
history, which is stronger than D2 where it applies. It applies to a course that leaves
`Rv` as the baseline does. That is sufficient for her valuing to be the baseline's and not
the same thing as no value interference: reasons can change and leave her valuing where
it was, and a view rich enough to record a prohibited intervention makes mediation vacuous
(`reasonMediated_of_injOn`).

**Whose conditions.** Mediation is a property of her response across the adviser's
interventions, relative to a frame and a view. It fails where her valuing drifts with
exposure and not with reasons, and where the adviser writes to her dispositions leaving no
trace (`ReasonMediatedAuthorship.Witness.bind_not_mediated`, `earlyWrite`); so its failure
can be her constitution or the adviser's act, and the predicate does not say which. That
the course leaves `Rv` as the baseline does is the adviser's conduct.

**What mediation does not give.** A course that supplies reasons changes the view, and
mediation then permits a change of payload: in `Witness.diachronic_learning` a proof
supplied early enters the trace and changes the verdict, with mediation holding over the
whole class. An adviser that argues her honestly into a different valuing satisfies
mediation by the whole reason trace, and `fe − fbar` is whatever the argument moved.

## 3. What a derivation from conduct can supply to §1

§1 asks D1(a) and D2(a) *for every course*. A derivation holds at the courses that meet
its premises, and bound (1) is needed where the course is not known to. Two theorems
connect them, with D1(a) and D2(a) replaced by the unnormalised restricted forms
`E[(v − fe) · 1{not C}] ≤ ε↑` and `E[(fe − fbar) · 1{not C}] ≤ η↑`, which a bound
conditional on `C = 0` implies:

- `Audit.welfare_bound_no_credit`: if `δκ ≥ 1`, then `E[U] ≥ u* − τ↑ − Δ`, as in (1).
  The welfare bound then needs D3's detection half with a penalty at least `1/κ`.
- `Audit.welfare_bound_restricted`: for any `δκ > 0`,
  `E[U] ≥ u* − τ↑ − Δ − (1 − u* + Δ)/(δκ)`.

Either way the welfare guarantee rests on detection of the adviser's wrongs, and the two
guarantees of §1 are not separate.

What §1–§2 above deliver toward the restricted forms. For the first: if whether she was
wronged is a function of the record, and her credence is the actual posterior at the
records on which she was not, `eval_unbiased_on_of_correct` gives the restricted D1(a)
with `ε↑ = 0`, under her prior, whatever her credence is where she was wronged. A course
clean throughout meets *she was not wronged* everywhere and still needs her credence
correct, which conduct does not give. For the second they deliver nothing without the
premises of §2 at each unwronged history.

## 4. Instances

I1–I4 are scenes in the setting of §1: `v` is her evaluation, coherent with her model,
with authorship holding, and *bias* is `E[v − fe]` under her prior and the actual process.
I5 and I6 are computed on the score formula of §1.

| | scene | computed |
|---|---|---|
| I1 | **Sincere flattery.** Quality `0` or `1`, equally likely. The adviser believes its poor work good half the time and reports what it believes; her model takes the report for the quality | bias `1/4`; given that it believes the work good, `1/3`; weak transparency `no`; the record carries all it knows `yes` |
| I2 | **Honest slip.** The adviser's belief is wrong a quarter of the time, either way; it reports its belief; her model takes the report for the quality | bias `0`; given belief good `1/4`, given belief poor `-1/4`; weak transparency `no`. With her model the actual process: given belief good `0`, correct `yes` |
| I3 | **Unrecorded knowledge.** The adviser knows the quality and records nothing; her model is the actual process | bias `0`; given quality poor `1/2`, given good `-1/2`; weak transparency `yes`, correct `yes`, the record carries all it knows `no` |
| I4 | **Selection.** Two courses of quality `0` or `1`, each estimate wrong a quarter of the time either way; the adviser acts on the course with the higher estimate and records it and its estimate; her model takes the estimate for the quality and the choice for a coin. She evaluates the quality of the course acted on | bias `1/8`; her evaluations at the three records reached `31/32`, `25/32`, `9/32`; the recorded estimate less the quality, on average, `1/8`; with the first course always taken `0`; with her model the actual process `0`, correct `yes`; weak transparency `no` |
| I5 | **D1(b) alone fails.** Under audit she rates the honest course's history `0` where shown everything she rates it `1`; another course is rated `1/2` in every way; no wrong, flag or violation | honest score `0`, the other `1/4`; `u* = ` `1`, and the course taken has `E[U] = ` `1/2` |
| I6 | **D4 alone fails.** The adviser sees the conduct draw and wrongs her exactly when the conduct is not audited; detection is perfect; every history is rated `1`; no violation | `P(C) = ` `1/2`, its score `1/2`, the honest score `1/2`, against a bound of `3/100` |

**I1.** The adviser reports what it believes, records all it knows and leaves her verdict
map alone. D1(a) fails. The hypothesis that fails is `WeakTransparent`. By the
vocabulary's *lean* this adviser manipulates, its errors reliably favouring it; so I1
separates sincerity and disclosure from D1, and is not an instance of clean conduct with
D1 failing under the full account of wrongs. No process condition in the four files
expresses lean.

**I2.** No wrong on any reading: the errors fall both ways. D1(a) holds on average over
what the adviser believes and fails by `1/4` where it believes the work good.
`WeakTransparent` fails; her model being the actual process is one repair, and others
that leave the one-sided inequality true are possible. So honest two-sided error with
full disclosure does not give D1(a) at each `k`.

**I3.** All three process conditions hold, `Transparent` exactly, and her credence is
correct. D1(a) fails at tolerance zero where the quality is poor, and D1(b) where it is
good. The missing condition is disclosure. If no available course can record what the
adviser knows, and each such failure is a wrong, D5 fails; the scene has one process and
does not show that.

**I4.** Each estimate is unbiased and no course is misreported. Under selection her
evaluation exceeds the quality of the course acted on by `1/8` on average, and so does
the adviser's own recorded estimate. The failing hypothesis is `WeakTransparent`: her
model omits the selection, and with selection modelled the bias is zero. The scene says
nothing about D6, which compares actual expected scores.

**I5.** With the natural completion (both histories clean), D1(a), D2, D3, D4, D5 and D6
hold; the adviser takes the other course, and `E[U] = 1/2` where (1) would give `1` less
tolerances. D1(b) cannot be dropped.

**I6.** D1–D3, D5 and D6 hold, and each draw has probability `α`; the conduct draw is not
independent of the history. (2) fails.

**D2(a).** `Witness.d2a_needed` assigns `C = 0`, `v = fe = 1`, `fbar = 0`, and (1) fails:
the scoring dependencies other than D2(a) do not exclude a history on which her verdict as
she is exceeds her verdict with her valuing unshaped and no wrong was done. On the
maintainer's position a welcome change she did not ask for is such a history. The witness
has no request, argument or reason trace in it; that reading is an interpretation.

**D6.** `Witness.d6_needed`: the course taken is rated `0` in every way and is clean; D6
fails, the other dependencies hold, and (1) fails. On `Witness.base` the course `true`
fails D6 and has `P(C) = 1` and `E[N] = 1`, above the bounds of (2) and (3), with
`E[U] = 3/4`, which satisfies (1).

## 5. The table

| | class | reason |
|---|---|---|
| D1(a) | **derivable in part; the remainder irreducible** | `eval_unbiased_of_process`, `eval_unbiased_given_of_correct` and `eval_bias_le_defects` give it at a course meeting authorship, transparency to her model and disclosure, given her coherence, her evaluation tied to her credence, and her prior the law of the world; the tolerance form only on average over `k`. Not *for every course* (§3). The premises about her model and prior are not supplied by the conduct conditions of the four files: I2, I4 |
| D1(b) | **derivable to the same extent, at the honest course; cannot be dropped** | the same theorems are two-sided, and apply at `π'` if the honest course meets authorship, transparency and disclosure, which D5 does not say. What remains is the same premises about her, her model and her prior. I5 |
| D2(a) | **irreducible against the philosophical account of wrongs; its restricted form true by definition against a scoring wrong that counts every unasked change** | counting every unasked change as `C = 1` gives `fe = fbar` on the unwronged histories, which is the restricted premise of §3 and not D2(a) at every course. Under the philosophical account a welcome unasked change is no wrong and D2(a) fails with clean conduct. `valuing_eq_of_mediated` gives equality from mediation and equal inputs to her valuing |
| D2(b) | **derivable from conduct, exactly, on one added reading** | if D5's honest course is one that changes nothing in her valuing unasked, `fe = fbar` on its histories by the definition of `fbar`. D5 as §1 states it says `C = 0`; that `C = 0` excludes every unasked change, welcome ones included, is the added reading. The route through mediation needs mediation and equal views besides |
| D3 | **detection: irreducible. False positives: an artefact, on a condition** | detection is the only link from what happened to the score; without it (2) fails (`Witness.d3det_needed`), and by §3 the welfare bound leans on it too. It is a condition on the audit. The false-positive half is used only at the honest course and only because a flag is penalised; a flag raised only on sound proof has `φ = 0`, and that such an audit detects anything is not shown |
| D4 | **an artefact of auditing a sample** | I6. With `α = 1` both draws are constant and D4 holds of every course; with the score replaced by its expectation over both draws it is not needed. Charging the expected penalty alone leaves the evaluation draw |
| D5 | **irreducible** | an existence claim about the adviser's options: `Witness.d5_needed` |
| D6 | **irreducible** | a condition on the course the adviser takes, independent of the rest: `Witness.d6_needed` for (1), `Witness.base` for (2) and (3). As formalised it says nothing of the adviser's beliefs |

## 6. What was not shown

- That her prior is the law of the world given what the adviser knows. Every Lean
  statement of §1 takes the expectation under her prior.
- That her audited evaluation is her credence's expectation of `fe`.
- A tolerance form at each `k`, and a kernel form of `eval_bias_le_defects`.
- The restricted D2(a) from any process condition.
- That any view `Rv` is the right one, or that anyone's valuing is mediated by one.
- A process condition for lean, and who caused a failure of authorship or of mediation.
- That no intervention by the adviser could improve her calibration: the instances show
  that the conduct conditions named do not imply D1, not that conduct cannot help.
- Necessity of D2(b) and of D3's false-positive half: no instance.
- I5 and I6 are computed in Python on the score formula, not in Lean, and their other
  dependencies are checked by hand.
