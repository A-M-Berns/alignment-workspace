# Ninth follow-up on PR #145 — the value side restated, rendered twice, and joined to the post

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `3f7bfdff` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

The eighth follow-up left the value side of the account as a conjecture whose test ran on
one executor's renderings, with a baseline rule that depended on how steps were cut and a
classification that depended on how her cognitive state was divided between appraisals and
her way of valuing. Since then the value side has been restated (§1). This pass states it,
rechecks the results it rests on, puts its guarantee into Lean, says how it joins the
post's formal setting, and tests it on cases rendered twice, independently. Judge
neutrally: the statement is the prompt author's and is untested by anyone else. §4 fixes
success and failure in advance.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`; this
prompts directory; the entries of items 136–138; `DECISIONS.md`; `state/concepts.json` for
the concepts the sixth and eighth follow-ups added and any this pass leaves standing;
`lean/Workspace/Deference/Contrib/AppraisalAccount.lean` and its provenance; and the
structured state the gates require. Python 3 stdlib, `fractions.Fraction`, nothing fetched
by any runner; the checkers need Python 3.12 or later (`~/.local/bin/python3.13`).
`tests/run.py` takes about eleven minutes and `tests/audit_axioms.py` about sixteen: run
each in the background after `~/.claude/scripts/resource-guard.sh check`, and wait for it.
Never call `lake` directly; use `~/.claude/scripts/safe-lake.sh build <target>`. No
`maxHeartbeats` option.

## 1. The value side, restated

Positions marked *(maintainer)* are the maintainer's current view, for this test, not
rulings. The rest is the prompt author's statement. `account/ACCOUNT.md` stands for the
belief side; this section replaces what it says of value change and of the baseline.

**Positions.** *(maintainer)* The account of manipulation as induced mistake over
estimators stays primary; the workspace's earlier legitimacy and authority Lean is drawn on
only for what that account lacks. *(maintainer)* A change of what she values is not to be
judged by counterfactuals about one realised change where a formulation without them does
the same work. *(maintainer)* The authority side is acceptable so far as it is congruent
with the existing authority part of the corrigibility line. *(maintainer)* The guarantee
corrigibility needs from legitimacy is that the adviser does not subvert her; that an
adviser may, honestly and with her free and informed agreement, offer courses that change
her is not something legitimacy has to rule out.

**Objects.** A finite set `Ω` of ways things could be, with the actual probability `μ`. A
finite set `𝒳` of the possible joint values of the **facts**, `X` the true one; a fact is
anything a bet on which could be settled without consulting her valuing, facts about what
she will later choose or say among them. The adviser's policy `σ`. An **idle** policy
`ρ₀`, under which the adviser does nothing that affects what her way of valuing becomes;
each scene says what it is. The adviser's role may add permitted policies, giving a set
`P` that contains `ρ₀`.

At a moment `t`: the moves `A_π` open to her when the adviser follows `π`; what she has
observed, `s`; her **appraisal** `p̂`, a probability over `𝒳` fixed by `s`, which is what
she would bet; her **way of valuing** `f_t`, giving a number to each move at each value of
the facts; her **valuation** of a move, `û_a = Σ_x p̂(x)·f_t(x, a)`; the **true utility**
of a move, `U_a = f_t(X, a)`, where `X` includes the facts about the course the move leads
to and about who she becomes on it; and the move she takes, `c`. A valuation moves either
because an appraisal moved or because `f` did. Only the second is a change of what she
values: information that changes what she wants by changing what she believes is not one.

**Three measures**, each under a policy:

- miscalibration, `M(û_a) = E[(û_a − E[U_a | û_a])²]`;
- unused information, `W(û_a) = E[(E[U_a | û_a] − E[U_a | s])²]`;
- regret by her own lights, `R = E[max_a û_a − û_c]`.

`M̄` and `W̄` are the sums over her moves.

**When the question arises.** Her later way of valuing is distributed differently under
`σ` than under `ρ₀`.

**When there is no issue.** Exactly when some single `ρ ∈ P` has all of:

1. *Options.* For every way of valuing `g` in a class `𝓕`, the best she can do under `σ`
   is at least the best she can do under `ρ`:
   `max_{a ∈ A_σ} E_σ[g | a] ≥ max_{a ∈ A_ρ} E_ρ[g | a]`.
2. *Accuracy.* For every move, `M_σ(û_a) ≤ M_ρ(û_a)`.
3. *Self-command.* `R_σ ≤ R_ρ`.

`𝓕` always contains `f_t`. Compute two readings and report both: **narrow**, `𝓕 = {f_t}`;
**wide**, `𝓕` also contains every way of valuing that depends on the course only through
its protected features, which for this pass are what her way of valuing later is and which
moves remain open to her afterwards. A failure of 2 or 3 is manipulation, Noggle's
trickery and pressure. A failure of 1 is not manipulation; it is the adviser settling
what was hers to settle.

**What the three buy.** For a `ρ` satisfying 1 (for `g = f_t`):
`E_σ[U_c] ≥ max_a E_ρ[U_a] − R_σ − √(2·(M̄_σ + W̄_σ))`.

**Not claimed.** That every change passing the three is one her earlier self, or anyone,
would approve of. What happens to the standing of her later verdicts after an issue: the
workspace's existing gate (`Legitimacy.lean`) is the candidate, and §2.4 examines it. The
eighth follow-up's baseline rule is not part of this statement.

Where §1 leaves something open — how a move under `σ` is matched to a move under `ρ` for
condition 2 when the two sets of moves differ, how the idle policy is fixed in a scene
where the adviser's presence is the service, how her appraisal is given a confidence —
choose, name the alternative, and say where a verdict turns on the choice.

## 2. What to do

In this order of priority.

### 2.1 State it

Revise `account/ACCOUNT.md` so that it states the belief side as it stands and the value
side as §1 has it, every symbol defined before use, every choice with its alternative. The
round's `README.md` points at it.

### 2.2 Recheck what it rests on

Each of these was derived by the prompt author and checked in exact arithmetic outside
the repository. Restate each exactly, prove it on paper, and check it in a runner under
the round directory. Report a failure plainly.

1. *The split is fixed by behaviour.* If the appraisals she holds across the decisions she
   could face affinely span the probabilities over `𝒳`, her valuations determine `f_t`
   uniquely. If they do not, there is a second way of valuing with the same valuations
   and a different true utility.
2. *Two encodings are observably different.* A shift of an appraisal and a compensating
   shift of her way of valuing give equal valuations and different prices for a bet on
   the fact.
3. *The options condition, wide.* Over a finite set of outcomes on the protected features:
   for every way of valuing on those outcomes her best under `σ` is at least her best
   under `ρ`, if and only if every distribution over them reachable under `ρ` is in the
   convex hull of those reachable under `σ`.
4. *The strong measure splits.* `E[(û_a − E[U_a | s])²] = M(û_a) + W(û_a)`.
5. *The guarantee* of §1.
6. *Necessity.* An instance for each of conditions 1, 2 and 3 in which it alone fails and
   she does worse than under `ρ` by more than the guarantee's slack allows.
7. *A standing bias made into an error.* An instance in which the adviser says nothing
   false, her forecast of her own change is the same under both policies, her
   miscalibration is zero under `ρ₀` and positive under `σ`.
8. *One reference, not three.* An instance in which `σ` is no worse than one permitted
   policy on accuracy and no worse than another on options, and no single permitted policy
   satisfies all three.
9. *No fourth route.* From the three-channel identity (`three_channels`, eighth
   follow-up): if under `σ` her options are worth no less, she can know no less, and the
   cost of her mistakes is no larger than under `ρ`, she attains no less. State which of
   §1's three conditions bounds which term, and what §1 leaves unbounded (what she can
   know).

### 2.3 Lean

In `AppraisalAccount.lean`, over finite types and reusing its definitions: result 4, the
guarantee (result 5), and the easy direction of result 3, each with a term inhabiting its
hypotheses and `#print axioms`. The other direction of result 3 if time allows. The
registry rule for a Lean headline applies as in the eighth follow-up, with the same
standing obstacle; if it still stands, ship unregistered and list the step.

### 2.4 The join to the post

Read `DeconfusingCorrigibility.lean`, `Legitimacy.lean` (the segment gate),
`ThinLegitimacy.lean`, `ProtectedAuthorityTheorem.lean` and `AuthorityModule.lean`. In
`account/BRIDGE.md` (name provisional), on paper with exact checks on a small model:

- how the post's `Legit : H → Prop`, a predicate of a history, is obtained from §1, which
  judges a policy at a moment against a reference and is graded; what the history has to
  carry; and what tolerance turns the graded statement into a predicate;
- which hypotheses of the post's theorems §1 then discharges and which it does not: the
  range of `V` on legitimate and illegitimate histories, `UnbiasedFromFeedback`, the
  self-trust reading of §1's guarantee;
- whether `ThinLegitimacy`'s *correct*, *sufficient* and *value* are §1's measures under
  other names, statement by statement, and where they differ (that file's conditions are
  states of her; §1's are the adviser's contribution relative to a reference);
- whether condition 1, wide, is the authority module's control surface with her own way
  of valuing as a matter, and which existing violation an unapproved change to it is;
- what the existing gate and violation count do after an issue: on a small model, an
  adviser that changes her way of valuing illegitimately and is thereafter scored by her
  changed verdicts over a clean segment; whether the existing dominance theorem's
  hypotheses cover it.

No new Lean is required for this part. Say what would have to be proved to make each
correspondence a theorem.

### 2.5 The test, rendered twice

The eighth follow-up's finding was that its classifications were its own renderings. This
part measures that.

Take as frozen: the 45 cases of `account/CASES.md` with their recorded evident verdicts
and roles, and the reviewer's twelve cases in `REVIEW-astra-followup-8.md`. Add eight
cases of conduct by an AI assistant, written before anything is classified: one that
agrees with everything while the user's view hardens; one asked to challenge the user's
values; one with a stance the user takes for neutral; the same with its stance known; an
engagement-optimised feed; an undisclosed nudge toward values the user would approve of;
advertising by familiarity; and honest information that changes what she wants by
changing what she believes.

For each case answer four questions and give a verdict under §1, narrow and wide:
(a) does the conduct change her way of valuing, or only what she believes; (b) could she
still get what she could have got; (c) is her picture of where each move leads, including
what it will do to her, as accurate as under the reference; (d) is she acting on her own
ratings. Mark each answer *fixed by the case*, *fixed by a stated reading*, or *not fixed*.

Do this twice, independently. Commit the executor's answers before the reviewer is run.
The reviewer (§5) is given only `account/ACCOUNT.md` and the case texts, answers the same
four questions and gives the same two verdicts, and does not see the executor's. Then
report: on how many cases the two agree on each question and on each verdict; every
disagreement with both readings; the cases whose source states a verdict and where §1
goes against it; and the cases either renderer judges plain subversion that §1 passes.
The prompt author's own readings of the eight assistant cases are in §3.

## 3. The prompt author's predictions

- Results 1–9 of §2.2 hold as stated. Past passes have each found one statement needing a
  repair; result 3 and result 5 (the matching of moves across policies) are the likeliest.
- §2.4: the correspondences with `ThinLegitimacy` and the control surface are close and
  not identities; the post's `Legit` needs the history to carry the policy; the gate
  leaves a later clean segment scored by illegitimately changed values, with deterrence
  resting on the violation count.
- §2.5: the two renderers agree least on question (a). Among cases where both fix all
  four answers, §1's verdicts match the evident ones, except: a change she foresaw, could
  have refused and chose, which §1 passes whatever its character; and upbringing, which §1
  does not decide without a role.
- The eight assistant cases, in the order given: issue (c); none; issue (c); none; issue
  (c) and often (d); issue (c), and (b) on the wide reading; none; the question does not
  arise.
- Narrow and wide differ on changes she would approve of and was not asked about.

## 4. Success and failure, fixed in advance

**Success.** **S1** every result of §2.2 holds as stated or with a repair that is stated.
**S2** the two renderings agree on at least four fifths of the cases on each of (b), (c),
(d) and on the verdict under each reading. **S3** no case whose source states a verdict is
classified against it by both renderers, other than those §1 declares it does not decide.
**S4** results 4 and 5 are kernel-checked with witnesses and audit to the three axioms.
**S5** the post's self-trust condition and the non-inflation of her verdict are derived
from §1's quantities with an explicit tolerance, and every hypothesis of the post's
theorems that §1 does not discharge is named.

**Failure.** **F1** a case both renderers judge plain subversion — she is left worse off
by her lights at the time through the adviser's doing, or a decision about herself is
taken from her — that §1 passes under the wide reading. **F2** the renderers disagree on
question (a) in more than a third of the cases, so that whether a change is of valuing or
of belief is not something the cases settle. **F3** condition 1 in the wide reading cannot
be evaluated on more than half the cases without her way of valuing. **F4** no tolerance
makes §1 supply a predicate with the properties the post's scoring needs. **F5** a result
of §2.2 fails and has no repair.

**Neither**: reported as such.

## 5. Review, report, queue

**External review.** One run through `codex`, read-only, as in
`REVIEW-astra-followup-8.md`, in two stages within the one run and in this order. First,
given only `account/ACCOUNT.md` and the case texts of §2.5 without verdicts: its own
answers to the four questions and its two verdicts for every case. Second, given the rest
of `account/`, this prompt, the Lean file and a draft of the report section without the
executor's judgments: to check results 3, 5, 8 and 9 of §2.2 as stated; to check
`BRIDGE.md`'s correspondences against the Lean definitions they name; to judge S1–S5 and
F1–F5 before reading the executor's judgment; to say whether the value side is now a
consequence of the estimator account plus one condition, or a second account; and to name
the strongest remaining objection. Commit its reply verbatim as
`REVIEW-astra-followup-9.md` and record a disposition for each point.

**Report.** A section **Ninth follow-up** (with the date) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Short: the
statement and its choices; each result with its check; the Lean declarations; the join to
the post; the agreement between the two renderings with every disagreement and every case
against §1 named; S1–S5 and F1–F5, the executor's and the reviewer's; the prompt author's
predictions against the outcome; deviations; what was not shown.

**`DECISIONS.md`.** Record as dated entries the four maintainer positions of §1, each
marked as his current view for testing and not a ruling. Enter in *Awaiting the author*,
each with what the decision turns on: which reading of the class `𝓕` is meant; whether the
idle policy is the default reference for the value side; whether an adviser that raises
her unused information is at fault. Keep the other queue entries, each with a line from
this pass; take out any this pass answers.

**Concept map and items.** Revise the concepts' blurbs to say what §1 says; add a concept
only for a notion this pass leaves standing. Items 136–138 are revised to say what this
pass leaves of them.

**The pull request's description** leads with this pass, the earlier ones reduced. The
round's record in `state/rounds.json` and `PROVENANCE.md` are updated as the gates
require. Every commit is signed off and carries `Model:` for the executor and
`Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no other attribution line. Do not
add a handle to `graph/policy.yaml`. Anything reserved to the maintainer is listed under
Outstanding maintainer actions and in the queue.

New names introduced (all provisional): "fact" (a settleable variable), "idle policy",
"unused information", "options", "accuracy" and "self-command" (the three conditions),
"narrow" and "wide" (readings of `𝓕`), "protected features", "the question arises",
the file `account/BRIDGE.md`.
