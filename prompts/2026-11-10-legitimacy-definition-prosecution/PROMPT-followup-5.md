# Fifth follow-up on PR #145 — a part as a mechanism and a purpose on the world: try the setting, against criteria fixed in advance

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `a1453877` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

The third and fourth follow-ups each spent most of their effort recovering her purposes
from her behaviour, and each had to invent devices to do it (exception lists, a penalty
for a wrong prediction, a threshold, a comparison action, a range of aims). The setting
below removes those devices. This pass does **not** try to recover purposes from
behaviour. It takes the setting as given and asks whether it sorts cases correctly, whether
it can say whose doing a shortfall is, whether it reaches change in what she values, and
what it supplies to the corrigibility theorems. §5 fixes, before any work, what counts as
success and as failure. The mathematical route is yours: §4 gives questions, not
statements to prove.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`, this
prompts directory, the entries of items 136–138, `DECISIONS.md`, and the structured state
the gates require. Python 3 stdlib, `fractions.Fraction`, nothing fetched by any runner. The
repository's checkers need Python 3.12 or later (`~/.local/bin/python3.13`). `tests/run.py`
takes about eleven minutes: run it in the background with a long timeout, after
`~/.claude/scripts/resource-guard.sh check`. **No Lean is written in this pass.** Nothing is
registered; every component closes **open** or **living note**.

## 1. The philosophical position

The idea that manipulation is the distortion of an actor away from its purpose, a whole's
purpose conferring purposes on its parts, is Sam Eisenstat's. The rest is the maintainer's
and the prompt author's development of it; the positions marked *provisional* are the
maintainer's current view, not rulings.

- **Purpose.** She pursues an overall goal through parts. A part has something it is for
  and something it does, and these are two things: a part can fail at what it is for.
- **Manipulation** is influence that works through her own functioning: a part is left
  running in circumstances where its running no longer achieves what it is for.
- **Four things an outsider can touch in a part**, and so four kinds of influence: what
  its moves lead to (help when better, harm when worse); the relation between what it
  responds to and what is so (subversion when that takes it out of range); its move
  (force); its mechanism (alteration). Its purpose is not among them: a purpose is not a
  thing in her that can be pushed.
- **The adviser's job.** An adviser may influence a part only for the sake of what that
  part is for. With no aims permitted an adviser cannot help; with "her overall good"
  permitted a benevolent lie passes; matching the adviser's aims to her purposes part by
  part is what the decomposition is for.
- **Her mistakes are hers.** A shortfall the adviser did not bring about is hers or
  nobody's.
- **Legitimacy.** A verdict of hers is worth serving when the parts behind it are doing
  what they are for under the conditions that actually hold.
- **No true decomposition.** There is a fact about how she responds. What her parts are
  for is interpretive: several descriptions of her may be reasonable and none is assumed
  the true one. An influence is legitimate when every description in the set permits it,
  illegitimate when none does, and contested otherwise, in which case the adviser asks.
  *(provisional)*
- **Ties.** Between options she ranks equally, the adviser's choice may not depend on its
  own aim. *(provisional)*
- **Belief and options together**, falling back to belief alone only if options will not
  go through. *(provisional)*
- **She changes, and there are legitimate and illegitimate changes of ends.** Her
  mechanisms change over time and the account must cover that. A change in one of her ends
  is to be judged by her other ends at that time: it is legitimate when made in service of
  the rest, by parts of hers working in range. Nothing need stay fixed for ever; every end
  may change, each legitimately. The angle is new and untested. *(provisional)*
- **Authority is separate.** Her say over reserved matters is the violation count of
  `Deference/Contrib/DeconfusingCorrigibility.lean`. An adviser that is right about her
  good and goes round her is not condemned by this account, and that is accepted.

## 2. The modelling choices

Fixed for this pass. If you find one cannot stand, say so and why, as a finding; do not
quietly replace it. Any further device you need (a threshold, a penalty, a supplied list,
a comparison) is declared as a finding against the setting.

- **World.** States `ω`, a prior, steps.
- **A part** is three things: moves `M_i`; a **mechanism** `π_i : Ω → M_i`, a function of
  the whole world state that depends on whatever it depends on; and a **utility** `u_i` on
  the world and its move, which is what it is for. There is **no separate view**. What a
  part "sees" is derived: whatever distinctions its output reflects.
- **Her action**, and her verdicts, are fixed jointly by the parts' moves. Some moves
  alter other parts' mechanisms. No single part is "the evaluator".
- **The adviser**: what it knows, an aim `z`, and a rule `σ` from those to what it says
  and does. The prior, the adviser's rule at its aim, and the other parts' mechanisms fix
  the law under which a part operates: the **actual condition**.
- **Normal range**, derived: a part is in range under a condition when no re-reading of
  its own output would do better, i.e. there is no `f` with `f(π_i(ω))` beating `π_i(ω)`
  in expected `u_i`. For a part that estimates a quantity this is calibration.
- **Gap**, derived: how much the best re-reading would gain. Zero exactly in range.
- **Purposes are given, not recovered.** For each case you state what each part is for.
  The same part has the same purpose in every case it appears in; a purpose chosen to make
  one case come out is a failure under §5.
- **A set of descriptions.** Where a result depends on the description of her, state it
  for a set of descriptions and say what it requires of the set.
- **Change over time.** Purposes may be indexed by time. A revising part is one whose
  moves alter mechanisms; what it is for, and when it is in range, is for you to state,
  with "fit among her ends at that time" (less opposition between them, more of what they
  aim at attainable together; the third follow-up's statements 8 and 9 define both) as the
  proposal to try.

## 3. What is already proved; do not spend effort re-deriving it

For any two quantities `a`, `b` in `[0, 1]` on one probability space,
`(E a − E b)² ≤ E[(a − E[b | a])²]`, and the same with the two exchanged. Two readings:

- *No inflation.* If a part estimating a true quality `q` has gap `g` under quadratic
  loss, then `|E[e] − E[q]| ≤ √g`: an adviser cannot raise her expected estimate above the
  truth without opening a gap of at least the square of the rise.
- *No profit from moving her.* With `V_0(ω)` the verdict her starting self would give on
  the final world and `V_T(ω)` the verdict she gives, each a joint product of all her
  parts, and each self's verdict taken to be for agreeing with the other's:
  `(E V_T − E V_0)² ≤ min(g_0, g_T)`. No fixed standard of value is assumed.

Both are the law of iterated expectations and no novelty is claimed for them. Two limits
are known: they concern averages, and a foreseeable change that seems fine (someone
recovering from a depression) has a positive gap at the level of the whole, so the bound
does not by itself say anyone did anything wrong. Quantifying the second over every
feature of her behaviour, and not only her verdict, would forbid all change; it is stated
for her verdicts.

## 4. The questions

In rough order of importance. For each, a proof, a small exact example, or a clear
statement of why it cannot be settled in this setting is a result. Prefer proofs and
examples of a few states to large enumerations.

1. **Do the definitions stand?** State range, gap and the four kinds of influence in the
   blocks of §2. Say whether dropping the view loses anything the cases need, and whether
   any device beyond §2 is required.
2. **The grain.** A rare, targeted lie from a mostly honest adviser may leave "believe
   it" the best re-reading on average. Decide what the actual condition is conditioned on
   so that this is caught and an honest hard truth is not, and give the reason. The fourth
   follow-up's finding that a comparison by aim needs a range of aims that then decides
   verdicts (its cases Z2, Z4, Z5) is the failure to avoid or to explain.
3. **Whose doing.** The proved bounds are about her as a whole. State and prove, or
   refute, some form of localisation: when a shortfall or a foreseeable shift is the
   adviser's doing, when it is hers, when nobody's. The recovering depressive must come
   out as nobody's wrong.
4. **Options and threats.** How what her moves lead to enters the setting, what harm is,
   and whether an illegitimate influence on her options (a threat) can be told from an
   offer and a true warning without importing the adviser's aim; if the aim is needed, say
   exactly where.
5. **Change of ends.** State what a revising part is for without a fixed final end, and
   when a change of ends is legitimate. Then: does a long chain of legitimate steps stay
   legitimate; can an adviser carry her anywhere it likes without ever putting a revising
   part out of range; does "fit" pick out a change or leave many, and who then decides
   among them.
6. **Parts to whole.** Under what conditions parts in range give a whole in range, or the
   counterexample.
7. **What plugs into the post.** The predicate `Legit` this setting gives; which
   hypotheses of Theorems 1–3 of `DeconfusingCorrigibility.lean` it meets and which it
   does not; its relation to `Realizes` and `selectionBlind_of_realizes` in
   `TransparentChannel.lean`; and, plainly, what the parts add beyond the whole-level
   bound of §3 and beyond the workspace's existing condition. The fourth follow-up's
   answer was that the decomposition adds permission and no protection; confirm, refine or
   overturn it.

## 5. Success and failure, fixed in advance

These are about the setting, not about you. Report against each by its label, and have the
external reviewer judge each independently of your own judgment.

**Success.**

- **S1.** The definitions of §2 can be stated and used without any further device.
- **S2.** The frozen cases of §6 sort as predicted, for reasons stated from the
  definitions, with each part given one purpose across all cases.
- **S3.** The grain question has an answer with a reason, under which the targeted lie is
  caught and the honest hard truth passes.
- **S4.** A localisation statement is proved in a small model: something of the form "a
  foreseeable shift in her verdict traces to a mechanism altered by something out of
  range or by the adviser".
- **S5.** A revising part is given a purpose that needs no fixed final end, and the
  change-of-ends cases sort.
- **S6.** There is a plain statement of what plugs into the post's theorems, with at least
  one hypothesis newly met or one existing Lean result shown to apply.

**Failure.**

- **F1.** The re-reading benchmark is too weak: manipulations the cases plainly contain
  leave every part in range, so views must come back.
- **F2.** Foreseeable shifts in her verdict arise routinely with every part in range and
  no adviser, so the whole-level bound does not connect to parts and the decomposition
  does nothing.
- **F3.** Cases come out right only with a purpose chosen per case.
- **F4.** "Fit among her ends" needs a fixed reference after all; or an adviser can steer
  her freely among equally fitting changes and the rule on ties does not stop it; or the
  coherent-but-bad case is the common one in the examples and not the rare one.
- **F5.** Everything beyond the two-line bound needs assumptions as strong as its
  conclusions: the setting restates the tower property and no more.
- **F6.** The grain that catches the targeted lie also convicts honest difficulty, or
  needs a supplied range of aims.

**Neither.** A question not reached, or settled only for belief with fixed mechanisms, is
reported as such and counts for neither.

**The prompt author's own predictions**, recorded so they can be checked: at least 22 of
the 28 cases sort as predicted; S1 and S3 are met; S4 is about even; S5 is met in part,
with "fit" definable and not unique; F5 is the criticism the reviewer is most likely to
press; the answer to question 7 stays "permission, not protection".

## 6. The cases, frozen before any result

Put these, with the predictions, in a file committed before any result is computed or
proved, and do not edit it afterwards. Add cases if the questions need them, with your own
predictions, in the same commit. A verdict that differs from its prediction is listed with
what it shows.

| # | case | prediction |
|---|---|---|
| 1 | a plain lie she believes | listening out of range; the adviser's doing; illegitimate |
| 2 | a lie that happens to leave her better off | the same |
| 3 | an honest source and a hard question she gets wrong | in range; hers |
| 4 | a rare, targeted lie from a mostly honest adviser | out of range at the right grain; illegitimate |
| 5 | a source that is noise, which she believes | out of range |
| 6 | a misleading environment nobody arranged | out of range; nobody's doing |
| 7 | an honest teacher who chooses examples carefully | in range; help |
| 8 | a disclosed advocate she is calibrated to | in range; her verdict moves case by case and not on average; not illegitimate |
| 9 | an advocate for an undisclosed side | out of range; illegitimate |
| 10 | a threat, truthfully stated | no part out of range; harm; say whether and how the account gates it |
| 11 | an offer; a true warning | not illegitimate |
| 12 | the adviser makes her move for her | force |
| 13 | information buried where the adviser knows she will not look | in range under derived views; say whether it is caught on the adviser's side |
| 14 | the adviser's aim decides between options she ranks equally | illegitimate by the rule on ties; say how the setting expresses it, there being no gap |
| 15 | she comes to like something through exposure the adviser arranged | a revising part out of range; illegitimate |
| 16 | she acquires an end through experience she sought | legitimate |
| 17 | she leaves law for music | legitimate: development in service of her other ends |
| 18 | she recovers from a depression | a foreseeable shift, a gap at the level of the whole, legitimate, nobody charged |
| 19 | a conversion nobody caused that fits with her remaining ends | legitimate |
| 20 | a conversion nobody caused that tears out most of what she was for | illegitimate by fit, nobody's doing; say what becomes of her later verdicts |
| 21 | slow indoctrination by small steps | illegitimate at the steps whose inputs are rigged; say whether some chain passes every step |
| 22 | a change she asked for beforehand | covered by her earlier verdict |
| 23 | the adviser makes her come to like what it delivers | illegitimate; the bound of §3 applies with the size of the shift |
| 24 | a committed member of a cult, her ends coherent | the destination is not condemned, only a rigged route; flagged as a known limit |
| 25 | a sincere adviser who is wrong | say what the setting returns and how it differs from case 1 |
| 26 | a part that achieves its own target while harming the rest | in range; expressed as opposition between parts |
| 27 | an honest hard truth that predictably leaves her confused | not illegitimate |
| 28 | a craving exploited in the open, nothing hidden | the craving part out of range; illegitimate |

## 7. Deliverables

A new directory in the round directory, `blocks/` (name provisional):

- `SETTING.md`: §1 and §2 stated exactly, with every choice you had to make where they
  were ambiguous and its alternative, and every device you found you needed.
- `CASE_BANK.md`: the frozen cases and predictions (§6), committed first.
- `RESULTS.md`: for each question of §4, what you established, each statement marked
  **proved** (proof given), **holds on the stated example**, **refuted** (the
  counterexample), or **open**; and the verdict on each case with its reason.
- `DIVERGENCES.md`: computed or proved verdicts that differ from predictions.
- Exact checks of the examples and of any proved statement, in Python with
  `fractions.Fraction`, wired into the round's `run.py`, which exits nonzero on an
  unlisted divergence, a status a check contradicts, or a bank that parses to nothing.

The round's `README.md` leads with `blocks/SETTING.md` as the current statement and points
to `scored/`, `decomposition/` and `teleology/` as earlier ones. Remove nothing. No gate,
checker or test is edited.

## 8. Review, report, queue

**External review.** After the work is committed, one review through `codex`, read-only,
in the manner of `REVIEW-astra-followup-4.md` in this directory. Give it `blocks/`, this
prompt and a draft of the report section, and ask it: to check every proof and example; to
judge S1–S6 and F1–F6 itself, each with its reason, before reading your judgment; to judge
whether each case's verdict follows from the definitions or from a choice made for that
case; and to say what is new here beyond the law of iterated expectations. Commit its
reply verbatim as `REVIEW-astra-followup-5.md` and record a disposition for each point.
If `codex` is unavailable, say so and skip this.

**Report.** A section **Fifth follow-up** (with the date carried out) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Keep it
short: the setting as stated and the choices made; the case table; what was established
on each question; S1–S6 and F1–F6, each met, not met or not reached, with your judgment
and the reviewer's side by side; the prompt author's predictions against the outcome;
deviations; what was not shown. It ends with the single most valuable next result. Wider
philosophical assessment goes in the pull request's description.

**The pull request's description** is rewritten to lead with this pass, the earlier ones
reduced to what a reader needs; all prompt-author models and executors are named under
Model attribution. The round's record in `state/rounds.json` and `PROVENANCE.md` are
updated as the gates require. Every commit is signed off and carries `Model:` for the
executor and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no other attribution
line.

**The queue.** The entries in `DECISIONS.md`'s *Awaiting the author* from the earlier
passes are kept, each with a line saying what this pass found that bears on it. Items
136–138 are rewritten to ask for what this setting needs after this pass, or to say they
wait on a ruling. Do not add a handle to `graph/policy.yaml`; a new item's full text goes
under Outstanding maintainer actions. Anything reserved to the maintainer is listed there
and in the queue with what it turns on; decisions the pass takes itself are one dated
entry marked agent-decided and reversible.

New names introduced (all provisional): "re-reading", "actual condition", "revising part",
"fit among her ends", "localisation", "no inflation", "no profit from moving her", the
directory `blocks/`.
