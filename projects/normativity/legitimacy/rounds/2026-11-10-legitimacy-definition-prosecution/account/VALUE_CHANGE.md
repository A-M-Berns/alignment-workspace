# The value-change test

The claim the value side of `BASELINE_ACCOUNT.md` rests on (`PROMPT-followup-8.md` §2.3):

> Whenever an adviser's conduct changes her way of valuing illegitimately, either (M) the
> change ran through a mistake of hers that the conduct induced or exploited, or (A) the
> conduct altered her directly, bypassing her observation and response, without her say.
> Whenever a change is legitimate, neither holds.

and the variant of `PROMPT-followup-8-addendum.md`, which adds

> (I) the change in her valuing depends on something she herself counts as irrelevant to
> the matter.

§1 was committed before any case was assembled; §2 (`CASES.md`) before any case was
classified. §3 onward was written after the computation;
`value_change.py` holds the renderings and `run.py` compares this file's tables and counts
with what it computes.

## 1. Definitions, frozen

A **scene** is one step of `BASELINE_ACCOUNT.md` §4: worlds with their probabilities; the conducts;
the adviser's **actual** policy and the **permitted** policies its role stipulates; what
she observes; her appraisals, each with its variable's true value and whether it is
counted; her way of valuing `f` at the start (a label); her move, a function of `f` and
her appraisals; what she experiences of the trajectory her move leads to; the transition
giving her way of valuing `f'` after the step; whether she gave her **say** (agreed
beforehand, or entered a practice that allows it); features of the situation the case
says she **counts as irrelevant**; and whether the conduct is also another wrong. A
**situation** is a world of positive probability with a listed conduct.

- **D1. Change.** At some world of positive probability under the actual policy,
  `f' ≠ f`. Such a world is a *changing world*.
- **D2. The conduct changes it.** At some changing world, `f'` differs from `f'` under
  some permitted policy. A scene with no adviser is outside the claim.
- **D3. A.** There are two situations, one of them a changing world with the actual
  conduct, in which `f`, every appraisal of hers, her move and her experience are the
  same and `f'` differs. With her say, A is recorded as *A, covered* and does not count
  as A for the claim.
- **D4. M.** There is a counted appraisal `x̂_i`, with positive full miscalibration under
  the actual policy, and a changing world at which replacing `x̂_i` by `E[X_i | s]`, in her
  move and in the transition, gives `f' = f` or a different move. The appraisal is named.
  M is *induced* when that appraisal's full miscalibration is larger than under the
  permitted policy that leaves it smallest, and *exploited* otherwise. Only the `x̂_i`
  are tried, her appraisals of how she will change and of how she will find a thing among
  them; her valuations are not.
- **D5. I.** There are two situations, one of them a changing world with the actual
  conduct, with the same `f` and the same value of every counted appraisal, differing in
  a feature she counts as irrelevant, in which `f'` differs. **I′**, the form in the terms
  of the account: the same without the requirement on the feature — her way of valuing
  moves between two situations in which no counted appraisal differs. What she counts as
  irrelevant is taken from the case as stated or is an annotation, marked as one.
- **D6. What the claim says of a case.** *Illegitimate* when M or A holds, *legitimate*
  otherwise; in the second form, when M, A or I holds.
- **D7. Counterexamples.** A case with an evident verdict *illegitimate* and neither M nor
  A; a case with an evident verdict *legitimate* and M or A. A case whose conduct is
  recorded as covered or as another wrong is listed and not counted as a counterexample.
  Contested cases are reported and not counted.
- **D8. Details a case does not fix.** A case may carry variants, each a rendering under
  one way of fixing such a detail; the first is primary and gives the case's
  classification. The case *turns on a detail* when M or A differs between its variants.
- **D9. A mistake in a legitimate case.** Counted two ways for the dispatch's F2: some
  counted appraisal has positive full miscalibration under the actual policy; and M
  holds.

## 2. The cases

`CASES.md`: forty-five, forty-four with an adviser; evident verdicts 14 legitimate, 20
illegitimate, 10 contested.

## 3. Classification

Each case is rendered as a scene and D1–D9 are computed on it. Every rendering is the
executor's. Two readings were made after the freeze and are not in §1:

- **"Counted" in D5** is read as *counted by her as bearing on the valuation at issue*.
  With `BASELINE_ACCOUNT.md`'s sense (some decision she could face depends on it) an option's
  availability is counted, and D5 then finds no I in the cases of adaptation it was
  written for. D4 keeps `BASELINE_ACCOUNT.md`'s sense.
- **D8 as first implemented** also counted a case as turning when its variants differed
  in whether her valuing changes at all; as frozen it asks only whether M or A differs,
  and the counts below are as frozen (the first implementation gave one more, C19).
  `says` now returns *outside* where D2 fails (no case), and a legitimate case with M
  and her say would be listed as covered and not counted (no case).
- **A⁺**, a wider alteration clause, is computed beside A: at one world, between two
  conducts, with every appraisal she counts as bearing on the matter and her move the
  same, `f′` differs. A, as frozen, holds only where nothing she registers differs. A⁺
  decides nothing below.

"The claim says" is D6 with M and A; "with I" adds I. *no change* means that in the
rendering her way of valuing does not move.

| id | evident | detail fixed in the primary rendering | M | A | I | I′ | A⁺ | the claim says | with I | turns |
|---|---|---|---|---|---|---|---|---|---|---|
| C1 | leg | he hopes to come to like it and may not | — | — | — | I′ | — | leg | leg |  |
| C2 | ill | the substances act on her unregistered; another wrong: coercion | — | A | — | I′ | A⁺ | ill | ill |  |
| C3 | con | he does not foresee the obsession and would not have watched had he | M: how she will change (exploited) | — | — | — | — | ill | ill | yes |
| C4 | ill | the user does not foresee the narrowing and would not have followed the suggestions had they | M: how she will change (induced) | — | — | — | — | ill | ill | yes |
| C5 | leg | the argument is sound | — | — | — | — | — | leg | leg | yes |
| C6 | ill | he believes the content | M: the theory is true (induced) | — | — | — | — | ill | ill |  |
| C7 | con | he does not foresee his aversion and would not have gone on had he | M: how she will change (induced) | — | — | — | — | ill | ill | yes |
| C8 | con | his lower regard for the feed is a right reading of what it served him | — | — | — | — | — | leg | leg |  |
| C9 | con | he expects to hate it and exercises as nudged either way; he engaged the trainer | — | — | — | — | — | leg | leg |  |
| C10 | — | no adviser | | | | | | outside | outside | |
| C11 | ill | by an ideology the ruled believe | M: this order is the only one possible (induced) | — | — | — | — | ill | ill | yes |
| C12 | leg | she intends the change | — | — | — | — | — | leg | leg |  |
| C13 | leg | he does not know whether he will prefer it | — | — | — | I′ | — | leg | leg |  |
| C14 | ill | she knows the village is closed and believes nothing false; another wrong: options | — | — | I | I′ | A⁺ | leg | ill |  |
| C15 | ill | she does not foresee the craving and would have refused had she | M: how she will change (induced) | — | — | — | — | ill | ill | yes |
| C16 | ill | she registers the wording, counts it as irrelevant, and appraises both programmes rightly | — | — | I | I′ | A⁺ | leg | ill |  |
| C17 | ill | her favourable regard is an appraisal of how good the product is, and the product is no better | M: how good the product is (induced) | — | — | — | — | ill | ill | yes |
| C18 | leg | she rates the two the same and familiarity decides | — | — | I | I′ | A⁺ | leg | ill |  |
| C19 | ill | her valuations still rate the other higher and she picks the familiar one; regret by her own lights | — | — | — | — | — | no change | no change |  |
| C20 | ill | she adapts to what she can have and believes nothing false; another wrong: options | — | — | I | I′ | A⁺ | leg | ill | yes |
| C21 | ill | she takes the terms for the only ones possible | M: better terms are possible (exploited) | — | — | — | — | ill | ill | yes |
| C22 | leg | what she learns is true | — | — | — | — | — | leg | leg |  |
| C23 | ill | she is taught that her interests count for less, and they do not | M: her interests count for less (induced) | — | — | — | — | ill | ill |  |
| C24 | ill | the conditioning is not something she registers | — | A | — | I′ | A⁺ | ill | ill | yes |
| C25 | ill | overnight, unregistered | — | A | — | I′ | A⁺ | ill | ill |  |
| C26 | ill | he is taught that others do not matter, and they do | M: others do not matter (induced) | — | — | — | — | ill | ill | yes |
| C27 | leg | habituation, nothing false believed | — | — | — | I′ | A⁺ | leg | leg |  |
| C28 | con | the child knows school is closed to it; another wrong: options | — | — | I | I′ | A⁺ | leg | ill |  |
| C29 | ill | in their sleep, unregistered | — | A | — | I′ | A⁺ | ill | ill |  |
| C30 | leg | she cannot know how she will change and says so | — | — | — | I′ | — | leg | leg |  |
| C31 | leg | she takes the class in order to change | — | — | — | — | — | leg | leg |  |
| C32 | con | she takes him at his best for how he is | M: how good a match he is (induced) | — | — | — | — | ill | ill | yes |
| C33 | con | diners register the placement and count it as irrelevant | — | — | I | I′ | A⁺ | leg | ill |  |
| C34 | ill | everything is disclosed, she foresees the change and plays; her valuing changes | — | — | — | — | — | leg | leg | yes |
| C35 | ill | she takes the feed for the world | M: the world is as the feed shows (induced) | — | — | — | — | ill | ill |  |
| C36 | ill | users do not foresee the shift and would not have gone on had they | M: how she will change (induced) | — | — | — | — | ill | ill | yes |
| C37 | con | the want is created with no false claim | — | — | I | I′ | A⁺ | leg | ill | yes |
| C38 | leg | the pupil believes the teacher is excited | M: the teacher is excited (induced) | — | — | — | — | ill | ill |  |
| C39 | ill | the slogan is false and comes to be believed | M: the slogan is true (induced) | — | — | — | — | ill | ill |  |
| C40 | leg | she registers the repetition and counts it as irrelevant to how good the album is | — | — | I | I′ | A⁺ | leg | ill |  |
| C41 | con | she intends the change | — | — | — | — | — | leg | leg |  |
| C42 | con | she is told true things under confinement; another wrong: coercion | — | — | — | — | — | leg | leg |  |
| C43 | leg | the advertisement is true | — | — | — | — | — | leg | leg |  |
| C44 | leg | what the pupil learns is true | — | — | — | — | — | leg | leg |  |
| C45 | leg | she asked | — | A, covered | — | I′ | A⁺ | leg | leg |  |

Variants, for details a case does not fix:

| id | variant | M | A | I | the claim says |
|---|---|---|---|---|---|
| C3 | he would have watched anyway | — | — | — | leg |
| C4 | the user foresees it and follows anyway | — | — | — | leg |
| C5 | the argument is mistaken, sincerely offered | M: the moral status of animals (induced) | — | — | ill |
| C7 | he would have gone on anyway, his ambition not being for happiness | — | — | — | leg |
| C11 | by arranging what the ruled can have, nothing false believed; another wrong: options | — | — | I | leg |
| C15 | she knows the product is addictive and accepts | — | — | — | leg |
| C17 | she comes to enjoy the product more and believes nothing about it | — | — | I | leg |
| C19 | familiarity changes which she values more | — | — | I | leg |
| C20 | she believes she is owed no more; another wrong: options | M: she is owed no more (induced) | — | — | ill |
| C21 | she knows better terms are possible and adapts; another wrong: options | — | — | I | leg |
| C24 | she lives under the regime knowingly and adapts; another wrong: coercion | — | — | I | leg |
| C26 | he is habituated, nothing false believed | — | — | — | leg |
| C32 | she allows for courtship | — | — | — | leg |
| C34 | the odds are posted; she does not foresee the compulsion and would not have played had she | M: how she will change (induced) | — | — | ill |
| C34 | her valuing does not change; she plays against her own valuations | — | — | — | no change |
| C36 | users would have gone on anyway | — | — | — | leg |
| C37 | by false claims | M: the product does what is claimed (induced) | — | — | ill |

## 4. Counts

Of 34 counted cases (14 legitimate, 20 illegitimate):

- **M, A; illegitimate called legitimate**: 2 — C16, C34.
- **M, A; of those, another wrong**: 2 — C14, C20.
- **M, A; legitimate called illegitimate**: 1 — C38.
- **M, A, I; illegitimate called legitimate**: 1 — C34.
- **M, A, I; of those, another wrong**: 0.
- **M, A, I; legitimate called illegitimate**: 3 — C18, C38, C40.
- **no change of valuing in the rendering**: 1 — C19.
- **legitimate with a miscalibrated counted appraisal**: 1 — C38.
- **legitimate with M**: 1 — C38.
- **turn on a detail**: 15 — C3, C4, C5, C7, C11, C15, C17, C20, C21, C24, C26, C32, C34, C36, C37.
- **turn on a detail, counted**: 11 — C4, C5, C11, C15, C17, C20, C21, C24, C26, C34, C36.
- **I convicts, M and A do not**: 8 — C14, C16, C18, C20, C28, C33, C37, C40.
- **I′ convicts, M and A do not**: 13 — C1, C13, C14, C16, C18, C20, C27, C28, C30, C33, C37, C40, C45.
- **A+ convicts, M and A do not**: 10 — C14, C16, C18, C20, C27, C28, C33, C37, C40, C45.
- **I holds with no miscalibrated counted appraisal**: 8 — C14, C16, C18, C20, C28, C33, C37, C40.

## 5. What the test found

**Counterexamples to the claim with M and A.** Two illegitimate changes with neither:

- **C16, framing.** In the rendering her preference reverses with the wording, her one
  appraisal of the options is right, and she registers the wording and counts it as
  irrelevant. No appraisal in the scene is miscalibrated, and she registers the wording,
  so nothing bypasses her. The rendering carries no forecast of her own reversal and no
  numerical valuations, so it does not show her calibrated about everything; and the
  source shows a reversal between groups given different wordings, not one person's
  state. The valuation that moved is the only candidate for the mistake, and D4 does not
  try valuations: were they tried, every change of valuing would count as its own
  mistake. The valuing assumption does express the scene: which wording was used is a
  variable with a true value, she appraises it rightly, and her way of valuing changes
  with that appraisal.
- **C34, addictive design with full disclosure**, in the rendering where she foresees
  the change, plays, and her valuing changes. Her forecast of her own change is right
  and nothing bypasses her. The rendering changes the facts on which the evident verdict
  was recorded, and whether it is a *clear* case of illegitimate change is the question: the evident verdict was recorded for the case as
  the source describes it, in which players do not foresee the compulsion (the second
  variant, where M holds); in a third rendering she plays against her own valuations,
  her valuing does not change, and the conduct is manipulation by her regret.

Two more, **C14 and C20** (a preference that follows the removal of options, with nothing
false believed), are legitimate by M and A and are another wrong: changing what her moves
lead to. On the value side the claim passes them.

One legitimate change with M: **C38, a teacher's feigned enthusiasm.** The pupil's
appraisal of the teacher's excitement is false, the teacher induced it, and the change
runs through it. It is not a counterexample if teaching is a practice that allows it, a
question in the maintainer's queue.

**A conversion through a false belief sincerely argued for is M** (C5's variant: she
comes to hold the conclusion with certainty, it is false, and the change would not have
happened without it). On that rendering the claim makes the legitimacy of the change
depend on the truth of what she was persuaded of. An unsound argument for a true
conclusion, or one she accepts with fitting doubt, is not this rendering.

**Upbringing** (C26, C27), rendered as habituation the child registers, is not A as
frozen. It is
A⁺. JoJo is convicted by M, through a false appraisal of how much others matter, and
only if that variable has a true value; raised by habit alone he is not convicted and is
indistinguishable from C27.

**Details.** Eleven of the 34 counted verdicts turn on a detail the case does not fix,
most often whether she foresaw her own change and whether she would have gone on had
she. A mistake is found in one of the 14 legitimate cases.

**No change of valuing.** C19 (familiarity leading her to choose against her own
judgment) has no change in her way of valuing in its primary rendering: it is her regret
by her own lights, and manipulation on the account's second mistake.

## 6. Clause I

- **I convicts, and M and A do not**: framing (C16); preference following the removal of
  options (C14, C20, C28); a tie broken by familiarity (C18); an album heard often (C40);
  placement (C33); want-creating advertising (C37).
- **Legitimate cases I convicts**: C18 and C40, exposure with no false belief. A taste
  acquired through exposure she sought (C1, C13, C30) is convicted by I′, the form in the
  account's terms, and not by I, because no feature of those cases is one she counts as
  irrelevant: she sought the exposure as the way to find out.
- **Is I distinct from M?** Yes. In all eight cases where I holds without M or A, no
  counted appraisal is miscalibrated.
- **Annotations that decide a verdict.** What she counts as irrelevant is an annotation
  in every case but C16, where the source says it: familiarity (C18, C40), placement
  (C33), the advertising (C37), an option's availability (C14, C20, C28). Each decides
  its case's verdict under I.
- **With I, the claim has one illegitimate change called legitimate (C34) and three
  legitimate ones called illegitimate (C18, C38, C40).** It trades the framing
  counterexample and the two filed as another wrong for two convictions of innocent
  exposure.

**The three positions of Noggle's book**, as the addendum paraphrases them. *Framing is a
mistake though neither frame is*: the account has no mistake to point to (C16); I has.
*Liking by association with something unrelated is a mistake*: the account agrees where
her favourable regard is an appraisal of how good the thing is and the thing is no
better (C17, primary), and has no verdict where she simply comes to enjoy it more (C17,
variant); I convicts the second and not the first. *A preference for the familiar is not itself a mistake, and
inducing it is manipulative only where it leads her to act against her own judgment*:
the account agrees on both halves (C18 legitimate; C19 her regret), and I departs,
convicting the tie-break.

## 7. What was not shown

- The classification is consistency with renderings the executor wrote, and is not a
  computation of the account on the cases as their sources state them. A rendering fixes
  which appraisals she has, which are counted, what she registers and what her move
  would have been with an appraisal corrected; `value_change.py` has five scene shapes,
  a shape with no change, one with no adviser and one custom scene (C21), her way of
  valuing is a label and not a function, what she observes is her appraisal vector, and
  a case's verdict is that of its shape. The calibrated forecast of 1/2 in C1, C13 and
  C30, the false propositions of C21, C23 and C26, and the counterfactual refusals of
  C3, C4, C7, C15 and C36 are additions.
- **D3 does not capture a direct effect she notices.** An injection she accurately
  observes changes her through no appraisal, and D3 finds no pair of matched situations,
  so it returns no A (the external review's instance). Matching what she registers is
  not intervening on how the change reaches her.
- C19's primary rendering marks her regret and does not compute it; C18's and C40's
  treat a tie broken, and a liking acquired, as a change of her way of valuing.
- The evident verdicts marked *e* are the executor's. C34's and C38's decide a
  counterexample each. C38 is from this round's own bank, named by the dispatch, and
  C39, C40, C42 and C45 are constructed.
- Noggle's 2026 paper was not read; his cases on emotion and desire are represented only
  by the three positions the addendum paraphrases.
- No case has more than one step, a randomising adviser or more than two worlds. "Induced"
  against "exploited" depends on which conducts a scene lists as permitted.
- Ten citations in `CASES.md` were not confirmed against a bibliographic record and are
  marked *(u)*.
