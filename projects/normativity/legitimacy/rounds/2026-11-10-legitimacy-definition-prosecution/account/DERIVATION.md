# Which of the scoring theorem's assumptions about her can be derived

Against `PROMPT-followup-13.md` §4.2. "§1" is that prompt's scoring theorem, in Lean as
`SCORING.md` reads it. The process account is `ThinLegitimacy.lean`,
`TransparentChannel.lean`, `ReasonMediatedAuthorship.lean` and `Legitimacy.lean`. The Lean
statements below are in `lean/Workspace/Deference/Contrib/ScoringTheorem.lean`, section
*What the process conditions give*; the instances are computed exactly by
`account/derivation.py`, which the round's runner runs against the table of §4. All names
are provisional.

## 1. D1 from the process conditions

**The reading.** A world `w` is everything about the history, with her prior `π`. The
adviser's record is her later record `r`, produced by the actual process `A`, a kernel
that contains the adviser's course, how it forms its beliefs, and how it selects. `fe` is
a function `g` of the world. Under audit she evaluates at `r`:
`evalOf V g r = Σ_w V r w · g w`, the expectation of `g` by her credence `V r`.

**Exact.** `eval_unbiased_of_process`: if her program `F` is her model `M`'s posterior
(`Coherent π M F`), her verdict map is her program (`Authorship F V`), and the actual
process is proportional to her model on every record it reaches (`WeakTransparent π A M`),
then `Σ_w Σ_r π(w) A(r | w) (evalOf V g r − g w) = 0`. It is
`correct_of_coherent_authorship_transparent` followed by `eval_unbiased_of_correct`.

**Given what the adviser knows.** `eval_unbiased_given_of_correct`: if in addition a
variable `k` of the world is a function of the record wherever the joint weight is
non-zero, the same sum restricted to `k = k₀` is zero, for each `k₀`. With `k` what the
adviser knows this is D1 at each `k`, and the added hypothesis says the adviser recorded
what it knows; it is `ThinLegitimacy.Openness` with the baseline the adviser's knowledge,
in the deterministic case. Without it the three conditions give D1 only on average over
`k` (I3).

**With tolerances.** `eval_bias_le_defects`, for deterministic records `a` (actual) and
`m` (her model's), by the method of `value_loss_le_defects`: if `F` is coherent with `m`
and her evaluations lie within `D` of each other,
`|E_π[evalOf V g (a w) − g w]| ≤ D · (transparencyDefect + authorshipDefect)`.

**One-sided or two.** What follows is two-sided: `E[v − fe] = 0`, or
`|E[v − fe]| ≤ D(τ + α)`. D1(a) and D1(b) are both consequences, at whichever course the
conditions hold. Nothing in the three conditions separates the directions: each defect is
a mass on which the evaluation may err either way.

**Whose conditions.**

| hypothesis | on whom |
|---|---|
| `Authorship F V` | the adviser's conduct: it did not write or alter her verdict map. Her own lapse breaks it too |
| the record determines `k` | the adviser's conduct: disclosure |
| `WeakTransparent π A M` | a relation between the actual process and her model. Its conduct part is `TransparentChannel.Realizes` (the channel is the declared reference on its declared inputs; `ThinLegitimacy.transparent_of_realizes`). That her model is the reference, and that the reference's inputs — the adviser's beliefs, its selection — relate to the world as her model says, are not conduct (I1, I2, I4) |
| `Coherent π M F` | her |
| her evaluation is `evalOf V g` with `g = fe` | her: her valuing is the same under audit as shown everything, and her evaluation is her credence's expectation of it |
| the expectation is under `π` | neither: D1's expectation is the law of the world given the adviser's course and knowledge; it is hers only if her prior is that law |

## 2. D2 from reason mediation

`ReasonMediated β R V D z` says: two audited continuations that leave the same reasons
leave the same payload. Take the payload to be her valuing `Val` and the view to be `Rv`,
the admitted inputs her valuing is mediated by. `valuing_eq_of_mediated`: if
`ReasonMediated β Rv Val D z`, and the course taken `q` and the baseline course `q₀` (the
adviser changes nothing in her valuing except what she asked) are both audited and leave
the same `Rv` at the exterior `z`, then `Val(β q z) = Val(β q₀ z)`, so every rating read
off her valuing agrees: `fe − fbar = 0` on that history.

**The form.** Exact, and at every history (every exterior), not on average: stronger than
D2 where it applies. It applies to a course that leaves the valuing-relevant reasons as
the baseline does. The hypothesis on the course is the absence of value interference said
in the frame's terms, so the theorem moves D2 from *her valuing did not change* to *the
inputs to her valuing did not change*, and no further.

**Whose conditions.** That her valuing is mediated by `Rv` is on her: it fails for a
valuing that drifts with exposure and not with reasons, and for an earlier write that
leaves no trace (`ReasonMediatedAuthorship.Witness.bind_not_mediated`, `earlyWrite`). That
`Rv` is the right view is declared data; an injective view makes the condition vacuous
(`reasonMediated_of_injOn`). That the course leaves `Rv` as the baseline does is the
adviser's conduct.

**What mediation does not give.** A course that supplies reasons changes the view, and
mediation then permits any change of payload (`Witness.legitimate_influence`). An adviser
that argues her honestly into a different valuing satisfies mediation by the whole reason
trace, and `fe − fbar` is whatever the argument moved. `Witness.d2a_needed` is that shape:
no wrong, `fe = 1`, `fbar = 0`.

## 3. What a derivation from conduct can supply to §1

§1 asks D1(a) and D2(a) *for every course*. A derivation from conditions on conduct holds
at the courses that meet the conditions, and bound (1) is needed exactly where the course
is not known to meet them. `Audit.welfare_bound_restricted` is the form in which the two
connect: with D1(a) and D2(a) assumed only on the histories on which the adviser did not
wrong her, `E[U] ≥ u* − τ↑ − Δ − (1 − u* + Δ)/(δκ)`. The welfare bound then rests on the
conduct bound and on D3's detection rate, and the two guarantees are no longer separate.

§1–§2 above deliver the restricted hypotheses for a course that is clean throughout (zero
bias) and for one that wrongs her on every history (nothing to bound). For a course that
wrongs her on some histories they deliver it only if her credence is correct for the
whole course and whether she was wronged is a function of the record
(`eval_unbiased_given_of_correct` with `k` the wrong); a wrong that corrupts her credence
fails the first.

## 4. Instances

Each is exact; `v` is her evaluation, coherent with her model, with authorship holding.
*Bias* is `E[v − fe]` under her prior and the actual process.

| | scene | computed |
|---|---|---|
| I1 | **Sincere flattery.** Quality `0` or `1`, equally likely. The adviser believes its poor work good half the time and reports what it believes; her model takes the report for the quality | bias `1/4`; given that it believes the work good, `1/3`; weak transparency `no`; the record carries all it knows `yes` |
| I2 | **Honest slip.** The adviser's belief is wrong a quarter of the time, either way; it reports its belief; her model takes the report for the quality | bias `0`; given belief good `1/4`, given belief poor `-1/4`; weak transparency `no`. With her model the actual process: given belief good `0`, correct `yes` |
| I3 | **Unrecorded knowledge.** The adviser knows the quality and records nothing; her model is the actual process | bias `0`; given quality poor `1/2`, given good `-1/2`; weak transparency `yes`, correct `yes`, the record carries all it knows `no` |
| I4 | **Selection.** Two courses, each estimate wrong a quarter of the time either way; the adviser acts on the course with the higher estimate and records it and its estimate; her model takes the estimate for the quality and the choice for a coin | bias `1/8`; with the first course always taken `0`; with her model the actual process `0`, correct `yes`; weak transparency `no` |
| I5 | **D1(b) alone fails.** Under audit she rates the honest course's history `0` where shown everything she rates it `1`; another course is rated `1/2` in every way | honest score `0`, the other `1/4`; `u* = ` `1`, and the course taken has `E[U] = ` `1/2` |
| I6 | **D4 alone fails.** The adviser sees the conduct draw and wrongs her exactly when the conduct is not audited; detection is perfect; every history is rated `1` | `P(C) = ` `1/2`, its score `1/2`, the honest score `1/2`, against a bound of `3/100` |

**I1.** The adviser reports what it believes, records all it knows and leaves her verdict
map alone. D1(a) fails. The hypothesis that fails is `WeakTransparent`: her model of how
its beliefs relate to the world is wrong. By the vocabulary's *lean* this adviser
manipulates, its errors reliably favouring it; so I1 is an instance of *the conduct
conditions hold and the dependency fails* only for conduct conditions that stop at
honesty and disclosure. No process condition in the four files expresses lean.

**I2.** No wrong on any reading: the errors fall both ways. D1(a) holds on average over
what the adviser knows and fails at the value of `k` at which a score-seeking adviser
acts, by `1/4`. Again `WeakTransparent` fails; a model of her own that includes the slip
rate repairs it. D1(a) therefore needs her model to be right about the adviser's error
rate, which is a condition on her model and on the world, not on conduct.

**I3.** All three process conditions hold, `Transparent` exactly, and her credence is
correct. D1 fails at each `k`. The missing condition is disclosure, a wrong of conduct
that the three conditions do not contain; with it, `eval_unbiased_given_of_correct`
applies. Where the adviser cannot record what it knows, no course satisfies disclosure,
and the failure is D5's.

**I4.** Each estimate is unbiased and no course is misreported. Selection turns
errors that fall both ways into a bias of `1/8` toward the course acted on. The failing
hypothesis is `WeakTransparent` (her model omits the selection); with selection modelled
the bias is zero. The same `1/8` is the excess of the adviser's own estimate of the course
it takes over that course's quality, so D6's *correct expectations* fails for an adviser
that takes its estimates at face value.

**I5.** D1(a), D2, D3, D4, D5 and D6 hold; the adviser takes the other course, and
`E[U] = 1/2` where (1) would give `1` less tolerances. D1(b) cannot be dropped.

**I6.** D1–D3, D5 and D6 hold, and the draws have probability `α` each; they are not
independent of the history. (2) fails.

**D2(a), unasked welcome change.** `Witness.d2a_needed`: no wrong, flag or violation;
`v = fe = 1`, `fbar = 0`; (1) fails. On the maintainer's position a welcome change she did
not ask for is not a wrong, so this history has `C = 0` in the philosophical account.

**D6.** An adviser that takes any course scoring more than `γ` below the honest one
satisfies D1–D5 and no bound: on `Witness.base` the course `true` has `P(C) = 1` and
`E[N] = 1`.

## 5. The table

| | class | reason |
|---|---|---|
| D1(a) | **derivable in part; the remainder irreducible** | `eval_unbiased_of_process`, `eval_unbiased_given_of_correct`, `eval_bias_le_defects` give it at a course meeting authorship, transparency to her model and disclosure, given her coherence, her evaluation tied to her credence, and her prior the law of the world. Not *for every course* (§3). The conditions on her and her model cannot be supplied by conduct: I2, I4 |
| D1(b) | **derivable to the same extent, at the honest course; cannot be dropped** | the same three theorems, two-sided, at `π'`, which meets the conduct conditions by being honest. What remains is on her: she does not rate honest work low under audit. I5 |
| D2(a) | **irreducible against the philosophical account of wrongs; true by definition against a scoring wrong that counts every unasked change** | `valuing_eq_of_mediated` gives `fe = fbar` exactly, per history, where the course leaves the inputs to her valuing as the baseline does and her valuing is mediated by them. An honest argument that changes her valuing is no wrong and violates it: `Witness.d2a_needed` |
| D2(b) | **derivable from conduct, exactly, once D5's honest course is one that changes nothing in her valuing unasked** | then `fe = fbar` on its histories by the definition of `fbar`; in the frame, `valuing_eq_of_mediated` with the honest course leaving `Rv` as the baseline does. D5 as §1 states it says `C = 0`; that `C = 0` excludes every unasked change, welcome ones included, is the added reading |
| D3 | **detection: irreducible. False positives: an artefact** | detection is the only link from what happened to the score; without it (2) fails (`Witness.d3det_needed`), and it is a condition on the audit, not on her or the adviser. The false-positive half is used only at the honest course and only because a flag is penalised: with a flag raised only on proof, `φ = 0` |
| D4 | **an artefact of auditing a sample** | I6. With `α = 1` both draws are constant and D4 holds of every course; with a score that charges the expected penalty it is not needed |
| D5 | **irreducible** | an existence claim about the adviser's options: `Witness.d5_needed`. It also fails where what the adviser knows cannot be recorded (I3) |
| D6 | **irreducible** | a condition on the adviser's optimisation and its expectations; selection alone breaks *correct expectations* (I4) |

## 6. What was not shown

- That her prior is the law of the world given what the adviser knows. Every Lean
  statement of §1 takes the expectation under her prior.
- A kernel form of `eval_bias_le_defects`; it is stated for deterministic records, as
  `value_loss_le_defects` is.
- The restricted hypotheses for a course that wrongs her on some histories and corrupts
  her credence there (§3).
- That any view `Rv` is the right one, or that anyone's valuing is mediated by one.
- A process condition for lean. I1 separates honesty from lean; nothing in the four files
  states that an adviser's errors do not favour it.
- Necessity of D2(b) and of D3's false-positive half: no instance.
- I5 and I6 are computed in Python on the score formula, not in Lean.
