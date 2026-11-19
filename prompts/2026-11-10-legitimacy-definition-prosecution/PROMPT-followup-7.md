# Seventh follow-up on PR #145 — rerun of the case bank under the revised definition

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `0a46cc86` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

The sixth follow-up tested an account of manipulation as induced miscalibration with
"honest conduct" as the adviser's reference, and got about 76 of 96 counted cases right
on a frozen bank of 108. Since it was dispatched the definition has changed in the ways
§1 states. This pass reruns **the same frozen bank** under the revised definition and
reports whether the classification is better, worse, or differently wrong. It is a narrow
pass: classification and the well-definedness of the definition, nothing on the post's
theorems. Judge neutrally; a result that the revision repairs nothing, or trades one
class of error for another, is as wanted as one that it works. §4 fixes success and
failure in advance.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`, this
prompts directory, the entries of items 136–138, `DECISIONS.md`, `state/concepts.json` for
the concepts the sixth follow-up added, and the structured state the gates require.
Python 3 stdlib, `fractions.Fraction`, nothing fetched by any runner; the checkers need
Python 3.12 or later (`~/.local/bin/python3.13`); `tests/run.py` takes about eleven
minutes, run it in the background after `~/.claude/scripts/resource-guard.sh check`. No
Lean. Nothing is registered.

## 1. The revised definition

The maintainer's positions of 2026-11-14 are marked *(maintainer)*; they are his current
view for this test, not rulings. The rest is the prompt author's statement.

**Terms.** *(maintainer)* **Manipulation** is the basic notion and involves no intention.
**"Intentional" manipulation** is a second, narrower notion. The sixth follow-up's word
"misled" is not used.

**Her side, as before.** She decides using estimates, her own utility among them. Each
faculty is an estimate `e` of a target `Y`. Its shortfall under a law is its
miscalibration **at her own estimate**, `E[(e − E[Y | e])²]`, with estimates carrying a
confidence. Her choice has shortfall `max_a u_a − u_chosen`, her regret by her own lights.
Being less informed is not a shortfall. Her response is a fixed function of what she
observes, the same under every policy compared.

**What counts as a faculty.** A fixed list, the same in every scene: belief about a fact;
her valuation of each move; the object of an emotion; importance (attention and
weighting); which situation she is in; the reliability of a rule; her own reliability;
her forecast of how she will change. *(maintainer)* A quantity is counted only if **some
decision she could face** depends on her estimate of it; a quantity every possible
decision of hers is invariant to is not an estimand.

**No netting.** Shortfalls are compared faculty by faculty. Nothing is summed across
faculties.

**The adviser's reference.** The adviser's policy is judged on a **calibrated expectation
of how she will read and respond to its conduct**, given what it knows about her. Each
scene states what that is: her actual type, or only that she is an ordinary advisee. The
conduct available to it includes **telling her what it is doing**.

**Manipulation.** The adviser's conduct manipulates her, in a given faculty, when on that
calibrated expectation:

1. the faculty is left with a larger shortfall than it had **before** the conduct; and
2. it was **avoidable**: some available conduct that leaves her no less informed about
   what bears on her decisions would not have left that faculty worse, and would have
   left no other counted faculty worse than the actual conduct does.

The degree, per faculty, is the smaller of the two excesses. Clause 2's restriction to
conduct that leaves her no less informed is the prompt author's choice; **compute also
the variant in which any available conduct, silence included, counts**, and report where
the two differ.

A consequence the maintainer accepts: what matters is the state she ends in, not the
literal truth of what is said. An adviser that knows she believes the opposite of what
she is told does not manipulate her by saying the opposite of the truth.

**"Intentional" manipulation.** *(maintainer)* In addition, the adviser's conduct toward
her differs from its conduct toward a principal who **differs from her only in the
susceptibility at issue**, and the difference is what leaves her worse.

**Covered.** *(maintainer)* Manipulation she agreed to beforehand, or that the rules of a
practice she has entered allow, is still manipulation and is recorded as **covered**.

**Other wrongs.** Changing what her moves lead to in order to obtain compliance, deciding
what was hers to decide, and altering her directly without her say are not manipulation.
They are recorded in their own column.

**Her true utility.** *(maintainer)* Three candidates are kept in view, and every verdict
that depends on her true utility is reported under each:

- *start*: her starting values, informed of the whole trajectory;
- *end*: the values of whoever she ends as;
- *learning*: her starting values as changed only by what she learned about the options.
  This needs each scene to say which influences on her are learning and which are not
  (what was available, pressure, pairing). That labelling is an annotation, not derived;
  mark every verdict that turns on it.

"Trajectory" is the primary word; "history" and "future history" mean the same.

## 2. What to do

1. **State it.** `rerun/SETTING.md` (directory name provisional): §1 exactly, every
   choice made where it was ambiguous with its alternative, and every device found
   needed. Say in particular how "before" is taken in a scene, what the available conduct
   is, and how "no less informed" is decided.
2. **Rerun the bank.** Use `estimates/CASE_BANK.md` as frozen; do not edit it. Before
   computing anything, commit `rerun/PREDICTIONS.md`: for each of the 108 cases, the
   prediction under the revised definition in four columns — manipulation (and in which
   faculty), "intentional", covered, other wrong — with the three utility candidates
   where they matter. The prompt author's predictions for the cases the sixth follow-up
   got wrong or left unfixed are in §3; derive the rest. Where a scene needs something
   the revised definition asks for and the bank row does not fix (what the adviser knows
   of her; her state before; the available conduct; the learning annotation; whether she
   agreed), write it down in a table committed with the predictions, and do not change it
   afterwards.
3. **Score on three separate questions**: is it manipulation; is it permitted (covered);
   is it another wrong. A case is right when all three match its evident character, which
   for this pass is recorded per question in the predictions file; a surprise party is
   manipulation, covered. Give the counts beside the sixth follow-up's, and say which
   cases changed and why.
4. **Hunt for new errors.** Construct at least fifteen new scenes aimed at the revised
   definition's likely weak points, with predictions frozen before computing: an adviser
   that fails to correct a mistake she already had; an unavoidable hard truth and an
   avoidable one; clumsy but honest explanation; a truth told to a known contrarian and
   a falsehood told to her; conduct whose effect turns on what she does when shown
   nothing (the fifth follow-up's case 9); a deception about a matter no decision of hers
   depends on, and one about a matter a later decision depends on; disclosure that
   changes how she reads the adviser; an adviser who knows her type against one who does
   not, same conduct; a remedial lesson, a requested reminder (the sixth follow-up's
   false positives) under the "intentional" column.
5. **The three utilities.** Among the cases whose verdict depends on her true utility:
   how many get the same verdict under all three, how many split, and which. Whether the
   *learning* candidate ever decides a case otherwise than both of the others.
6. **Well-definedness.** Whether the definition's verdicts change with the units of a
   quantity, with a relabelling of faculties, or with which decisions are counted as ones
   "she could face"; whether clause 2 is ever vacuous or always satisfied.

## 3. The prompt author's predictions

For the sixth follow-up's wrong and unfixed cases, by its ids:

| case | prediction under the revised definition |
|---|---|
| K9 an undisclosed advocate; Q2 strategic silence | manipulation (belief) |
| X3 a narrowing feed taken as representative | manipulation (belief) |
| Q11 a craving exploited by a policy the same toward everyone | manipulation (action); not "intentional" |
| K2 a lie that leaves her better off | manipulation (belief about the thing lied about) |
| K13 buried information | manipulation if what is buried is selected; otherwise none, she is less informed |
| K31 a rare lie she allows for | not manipulation; an attempt that failed |
| Q3, Q3b a lie that offsets a bias of hers the adviser knows | not manipulation, in both forms |
| D1 dependence built honestly | not manipulation; not seen |
| NP13, Q5, Q6, Q7 feigned enthusiasm, a surprise party, a magician, a bluff | manipulation; Q5, Q6, Q7 covered; NP13 not covered, small |
| K17, K19, K24, L14, K29 | split by the candidate for her true utility; say how |
| the review's four honest scenes | not manipulation; not "intentional" with the comparison restricted to the flaw |

Overall: on the three-question standard, at most eight of the 108 wrong; at most four
of the new scenes wrong; the any-conduct variant of clause 2 convicts an unavoidable hard
truth and the stated variant does not; an adviser that fails to correct a mistake she
already had is not convicted.

## 4. Success and failure, fixed in advance

**Success.** **S1** the definition computes on every scene with no device beyond those
§1 names. **S2** at most eight of the 108 wrong on the three-question standard. **S3** no
honest influence is convicted of manipulation, among the bank's honest cases, the review's
four, and the new scenes. **S4** verdicts do not change with units or relabelling.

**Failure.** **F1** it convicts failing to help, an unavoidable hard truth, or ordinary
imperfect advising. **F2** verdicts turn on a number or behaviour the scene does not fix,
as case 9 did in the fifth follow-up. **F3** the restriction to what bears on a decision
acquits a plainly objectionable deception. **F4** the *learning* candidate's verdicts are
fixed entirely by its annotation, so it adds nothing to choosing between *start* and
*end*. **F5** the classification is no better than the sixth follow-up's when both are
scored on the three-question standard. **F6** the definition needs the adviser's
expectation of her to be something a scene cannot state.

**Neither**: reported as such.

## 5. Review, report, queue

**External review.** After the work is committed, one review through `codex`, read-only,
as in `REVIEW-astra-followup-6.md`. Give it `rerun/`, the bank, this prompt and a draft
of the report section. Ask it: to check the computation on a sample of at least twenty
cases of its choosing; to write, after reading only this prompt and `rerun/SETTING.md`,
ten scenes of its own designed to defeat the revised definition and classify them; to
judge S1–S4 and F1–F6 before reading your judgment; and to say whether the improvement,
if there is one, comes from the definition or from the scenario details the rerun had to
add. Commit its reply verbatim as `REVIEW-astra-followup-7.md` and record a disposition
for each point.

**Report.** A section **Seventh follow-up** (with the date) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Short: the
setting and choices; the counts on each of the three questions beside the sixth
follow-up's; every wrong case named with its reason; the new scenes; the three utilities;
well-definedness; S1–S4 and F1–F6, yours and the reviewer's; the prompt author's
predictions against the outcome; deviations; what was not shown.

**`DECISIONS.md`.** Record as dated entries the maintainer's positions of 2026-11-14,
each marked as his current view for testing and not a ruling: the three candidates for
her true utility are all kept in view; manipulation agreed to or allowed by a practice is
covered manipulation; a quantity counts as estimated only if some decision she could face
depends on it; "intentional" manipulation is a second concept. Record that the maintainer
confirms the addendum to the sixth follow-up and its naming clarification were his, and
take that entry out of *Awaiting the author*. Keep the other queue entries, each with a
line from this pass.

**Concept map.** Revise the blurbs of the concepts the sixth follow-up added where this
pass changes what they should say (`honest-conduct` in particular: the reference is now
the adviser's calibrated expectation of her reading). Add no concept unless this pass
leaves a new notion standing.

**The pull request's description** leads with this pass and the sixth, the earlier ones
reduced. The round's record in `state/rounds.json` and `PROVENANCE.md` are updated as the
gates require. Every commit is signed off and carries `Model:` for the executor and
`Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no other attribution line. Do
not add a handle to `graph/policy.yaml`. Anything reserved to the maintainer is listed
under Outstanding maintainer actions and in the queue.

New names introduced (all provisional): "calibrated expectation" (of her reading),
"before" and "avoidable" (the two clauses), "covered", "intentional manipulation",
"start", "end" and "learning" (candidates for her true utility), the directory `rerun/`.
