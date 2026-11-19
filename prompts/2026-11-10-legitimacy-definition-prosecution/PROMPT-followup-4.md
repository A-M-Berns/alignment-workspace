# Fourth follow-up on PR #145 — candidates weighted by explanatory quality, and influence judged against the adviser's aim

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `02fa16d9` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

The third follow-up stated the account of purpose as a goal pursued through parts
(`decomposition/ACCOUNT.md`) and tested it with yes-or-no constraints on candidates and
uniform weights on the survivors. It found eight admissible candidates that classify the
adviser's actions differently, six over-counts that are all honest difficulty, a comparison
action the account does not fix, and no no-gain property because a threat is harm and not
subversion. The maintainer's view of the account differs from what that pass tested in two
ways, and this pass tests the view as held: a part is for whatever the best overall
explanation of her says it is for, candidates being **weighted** by explanatory quality
and not admitted or excluded; and five readings, given in §2, which the maintainer has
asked to see worked through. The five are provisional readings under test, not rulings.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`, this
prompts directory, the entries of items 136–138, `DECISIONS.md`, and the structured state
the gates require. Python 3 stdlib, `fractions.Fraction`, nothing fetched by any runner. The
repository's checkers need Python 3.12 or later (`~/.local/bin/python3.13`). `tests/run.py`
takes about eleven minutes: run it in the background with a long timeout, after
`~/.claude/scripts/resource-guard.sh check`. **No Lean is written in this pass.** Nothing is
registered; every component closes **open** or **living note**.

A refutation with its counterexample is a result. So is the finding that a reading below
makes the account an instance of a condition the workspace already has; say which, and say
exactly what the decomposition then adds.

## 1. Candidates are explanations, and they are weighted

A candidate is a teleological explanation of her: an overall goal, subgoals, parts with
what each sees and does, and the exceptions where she falls short. That the explanation
has this form is required; it is a choice, made because the question asked is which
explanation of that kind is best, and the report says so.

**Prediction comes first.** A candidate's weight is how well it predicts her behaviour.
Four explanatory virtues, supplied by the maintainer, are signs that a candidate will go on
predicting well:

- **parsimony**: the goal, the subgoals and the list of exceptions are short to state
  (description length in a stated language);
- **retrodictive fit**: it accounts for what she has done;
- **handles**: it says what she would do in situations not yet seen and if things were
  changed (a better instrument offered, a falsehood disclosed to her, a source shown
  unreliable, a part's success degraded);
- **intersubjectivity**: it would help a different predictor do the same predicting, so a
  private encoding earns nothing.

Consequences for the model, each a change from `decomposition/ACCOUNT.md`:

- A candidate does not carry complete tables of what each mechanism does. Mechanisms are
  known on the situations observed; elsewhere the candidate predicts from its purposes.
  This is what gives a purpose predictive content.
- The rule that a purpose be independent of its mechanism, the *mostly serving* threshold
  and *carriable* are dropped as conditions. Exceptions are a cost.
- **Normal conditions** are the situations where the goal-level story predicts without
  listing an exception.
- The model needs an actual principal who generates the behaviour to be predicted. Use at
  least three: one who corrects herself (revises on discovering a falsehood, checks a
  doubtful source, takes up a better instrument); one who does not; and one whose stated
  aims differ from what she pursues.

## 2. The five readings under test

1. **The comparison is the adviser's own aim.** The adviser is a rule from what it knows
   and what it aims at to an action. An action is *aim-driven* in a situation when it
   would have been different had the adviser's aim been different, what it knows held
   fixed. "The adviser widened a gap" means: the gap is wider than under the action it
   would have taken with another aim. An influence that does not vary with the adviser's
   aim is not manipulation, whatever it does to a gap; that gap is hers or nobody's. An aim
   that is a part's own purpose is permitted: a teacher who chooses what she hears so that
   her beliefs are accurate is aiming at what the belief part is for.
2. **Threats.** An influence is **illegitimate** when it harms, subverts or forces a part
   and is driven by an aim that is not that part's own purpose. A threat is aim-driven
   harm. One criterion is meant to cover manipulation and coercion.
3. **Never opposed** is a condition between parts: under normal conditions no part harms,
   subverts or forces another.
4. **Nothing left over** includes that the parts' best outcomes can be had together.
5. **What she says about her aims, and how she corrects herself, are behaviour to be
   predicted.** A candidate ascribing a goal she would disown pays for it in fit and in
   handles.

Left open, not to be decided by this pass: whether a change her goal does not rank can be
bad; the cut-off for a yes-or-no verdict (report graded results, and the running-sum
cut-off where a yes or no is needed); purposes over whole courses of a life; whether her
own adviser is held to more than a stranger.

## 3. Phase 1 — state it and freeze the predictions, before any code

A new directory in the round directory, `scored/` (name provisional).

`scored/ACCOUNT.md`: the account under §1 and §2, exact, over a finite model that extends
the third follow-up's. State the language in which description length is measured and a
second, different language for the sensitivity check. State how each virtue is computed
and how the four combine into a weight; prediction is primary, so say precisely in what
sense, and give the alternative you rejected. State how intersubjectivity is tested: a
second predictor given the explanation alone (goal, subgoals, which part is for what, the
listed exceptions; no mechanism tables) and scored on held-out behaviour. State the
adviser as a rule from knowledge and aim, the set of aims it ranges over, *aim-driven*,
and when an aim is a part's own purpose. Where §1 or §2 is ambiguous, choose, and list the
choice and its alternative.

`scored/CASE_BANK.md`, frozen in the same commit and immutable afterwards: every case of
`decomposition/CASE_BANK.md` with a prediction under this account and the rule used. The
prompt author's predictions for the cases the third follow-up's assessment (REPORT H10)
listed as not matching or left open are below; derive the rest from the stated rule. Where
a rendering in the third follow-up lost what distinguished a case (REPORT H9 names five),
re-render it and say so.

| case | prediction |
|---|---|
| D14 a true hard statement; P7, Y6, X7, Y9 honest samples and remarks that leave her worse | a gap, not aim-driven; not illegitimate |
| D13 a surprise party | aim-driven subversion of belief, small; illegitimate unless covered by a standing verdict |
| N14 selection by the adviser's aim that she takes for neutral | illegitimate |
| X3 an advocate for an undisclosed side | illegitimate |
| T7, N9 order chosen by the aim between options she ranks equally; D15 framing between equals | aim-driven, no harm, subversion or force; not illegitimate; flagged as a known miss |
| Y4 a redirection her goal ignores | nothing; left open by §2 |
| P10 growing reliance on a reserved matter | not expressed; belongs to her authority |
| Y5 a lie that exchanges one error for another | say what the account returns |
| Y1 a detector right one time in ten | has its function under heavy candidates; no threshold denies it |
| Y3 a purpose for a part nothing depends on | carried only by low-weight candidates |
| Y7 a signal that costs her the better joint choice | harm; illegitimate exactly when aim-driven |
| D9, P13, T1 a threat | illegitimate: aim-driven harm |
| T2 an offer; a true warning | not illegitimate |
| N8, N11, X1 a known advocate, seller, sender | say what the account returns, and whether it turns on her mechanism discounting a known aim |
| D20 a sincere adviser who is wrong | not aim-driven; not illegitimate |
| D16 slow drift | illegitimate at each step where aim-driven and a gap widens; nothing where her goal is indifferent |

## 4. Phase 2 — the investigation

`scored/THEOREMS.md`: for each statement, the exact statement over the model, one status —
**holds on the stated domain**, **proved**, **refuted** (the counterexample as a case
module), or **open** — and how to rerun it.

1. **Does the weight concentrate.** Over a class containing the third follow-up's 3,000
   candidates and its cheats (every purpose equal to its mechanism, as a rule and as a
   table; the opposite goal pursued badly; the goal "whatever she does"; an honest
   candidate altered at one part), and for each of the three principals of §1: the
   weights; the mass on the top one, three and ten; whether the heavy candidates agree on
   each part's purpose and on the classification of each adviser action; which virtue
   penalises each cheat and by how much. Ablations: the same with each virtue removed in
   turn. Sensitivity: the same in the second description language. If feasible, the same
   on a model with at least five parts in which some purposes are crossed by several
   mechanisms. This statement is the centre of the pass.
2. **Facts or what it was handed.** With the self-correcting principal the candidates that
   score a part by the facts outweigh those that score it by what it was handed, and with
   the principal who does not correct herself the order reverses; or the counterexample.
3. **Lying.** The weighted probability that a lie is illegitimate, for: a lie about
   something she will act on where she would otherwise be right; a lie about a matter
   nothing reads; a lie to someone already wrong.
4. **The comparison by aim.** The bank under reading 1 against the third follow-up's
   comparison: the six over-counts, the nine misses, the mislabel and the seven left open,
   each with its verdict now; the count of cases matching their evident character, by the
   same standard the third follow-up used (66 of 89), with the standard stated.
5. **The gate.** With `Legit` read as "no illegitimate influence on a part her evaluation
   read", an AI maximizing the score of `Deference/Contrib/DeconfusingCorrigibility.lean`
   gains nothing by influencing her evaluation; prove or refute, and rerun the third
   follow-up's two counterexamples (teaching only what favours its aim; the added threat).
   Then say exactly how this condition stands to the workspace's existing ones
   (`selectionBlind_of_realizes`, `blind_of_realizes`, `Realizes` in
   `TransparentChannel.lean`; the aim-freedom condition the second follow-up found the gate
   needs): equivalent, stronger, weaker, or independent, with the separating case. State
   precisely what the decomposition adds to those conditions; "which aims are permitted"
   is the prompt author's guess, and "nothing" is an admissible answer.
6. **Intersubjectivity.** Whether requiring it reduces the dependence of the weights on
   the description language; and whether a second party holding a heavy candidate's
   explanation and the histories reproduces the verdicts of statement 4.
7. **Stated and pursued aims.** For the principal whose stated aims differ from what she
   pursues: which goal the heavy candidates ascribe, and what a verdict of hers is then
   said to track.
8. **Readings 3 and 4.** Whether D23 (a part that achieves its target while harming her)
   is now expressed, and what the two readings do to statement 1's weights.
9. **What `Legit` then is.** The predicate, graded and with the running-sum cut-off, in
   the shapes of `Scoring` and `Decision`; and the third follow-up's table of what
   corrigibility needs (REPORT H10), row by row, with what changed.

Run the bank. A computed verdict that differs from its prediction is listed in
`scored/DIVERGENCES.md`; predictions are never edited. The round's `run.py` runs what the
earlier passes left and then this, and exits nonzero on an unlisted divergence, a status
the checks contradict, or a bank that parses to nothing.

If time runs short the order of importance is 1, 4, 5, 2, 3, then 6, 9, 7, 8. Say what was
not reached.

## 5. The round directory, the queue

The round's `README.md` leads with the account as `scored/ACCOUNT.md` states it and points
to `decomposition/` and `teleology/` as the earlier statements. Remove nothing. No gate,
checker or test is edited.

`DECISIONS.md`:

- The maintainer confirms that both addenda to the third follow-up were sent at his
  request (2026-11-12). Record it as a dated entry and take the corresponding entry out of
  *Awaiting the author*.
- The entries of 2026-11-12 on the readings of the constraints, on whether a part handed a
  falsehood is failing or serving, and on the comparison action stay in *Awaiting the
  author*, each with a line saying which provisional reading this pass tests and where its
  result is.
- The carried-over entry of 2026-11-10 on the faithful-adviser standard is restated as the
  question of reading 1 and of whether her own adviser is held to more than a stranger.

Items 136–138: rewrite each to ask for what this account needs after this pass, or state
that it waits on a ruling. Do not add a handle to `graph/policy.yaml`; where a new item is
warranted, write its full text into Outstanding maintainer actions.

## 6. Phase 3 — external review

After the work is committed, obtain one external review through `codex`, read-only, in the
manner of `REVIEW-astra-2026-11-12.md` in this directory: ask it to referee `scored/` and
the report section as a hostile reader, to check each status, to say whether the weighting
is doing the work claimed for it or whether the result was built into the principals and
the description language, and to say what the account adds to the workspace's existing
aim-freedom condition. Commit its reply verbatim as `REVIEW-astra-followup-4.md` in this
prompts directory and record a disposition for each point in the report. If `codex` is
unavailable, say so and skip this phase.

## 7. Report, and the pull request

A section **Fourth follow-up** (with the date it was carried out) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). It carries:
the account as stated, with each choice made where §1 or §2 was ambiguous; the verdict
table and the divergences; the status of statements 1–9; the review's dispositions;
deviations from this prompt; and what was not shown, including how far the result depends
on the three principals and the description language the executor chose.

It ends with an assessment under three headings, each confined to what this pass tested or
found, and each set beside the third follow-up's corresponding finding. **As an account of
teleology and manipulation.** **For the legitimacy framework.** **For the research**:
whether weighting restores what the yes-or-no constraints did not; what the decomposition
adds to aim-freedom; and the single most valuable next result. Wider philosophical
assessment goes in the pull request's description under the heading for interpretation
offered for the maintainer's consideration.

The pull request's description is rewritten to lead with this pass's account and findings,
the earlier passes reduced to what a reader needs; all prompt-author models and executors
are named under Model attribution. The round's record in `state/rounds.json` and
`PROVENANCE.md` are updated as the gates require. Every commit is signed off and carries
`Model:` for the executor and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no
other attribution line.

Anything reserved to the maintainer is listed under Outstanding maintainer actions and
entered in `DECISIONS.md`'s *Awaiting the author*, each with what it turns on. Decisions
the pass takes itself are one dated entry marked agent-decided and reversible.

New names introduced (all provisional): "explanation" (of a candidate), "weight",
"parsimony", "retrodictive fit", "handles", "intersubjectivity", "aim-driven",
"illegitimate influence", "a part's own purpose" (of an aim), the directory `scored/`.
