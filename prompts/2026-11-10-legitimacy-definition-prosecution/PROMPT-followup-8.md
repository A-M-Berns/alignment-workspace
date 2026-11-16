# Eighth follow-up on PR #145 — the account consolidated, its value-change claim tested, its firm results in Lean

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `3d787bac` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

Since the seventh follow-up the account has been restated (§1) and worked through on
paper (§2.2). This pass does four things, in this order of priority: writes the account
down as one statement; tests the one claim its value side rests on; computes it on a
published benchmark; and puts its firm results into Lean against item 137. Judge
neutrally. The belief side is held with some confidence and the value side is a
conjecture under test; a report that presents the value side as settled is wrong whatever
the tests return. §4 fixes success and failure in advance.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`; this
prompts directory; the entries of items 136–138; `DECISIONS.md`; `state/concepts.json` for
the concepts the sixth follow-up added and any this pass leaves standing; new Lean files
for item 137 in the namespace that item names, with the provenance and registry entries
the gates require; and the structured state the gates require. Python 3 stdlib,
`fractions.Fraction`, nothing fetched by any runner; the checkers need Python 3.12 or
later (`~/.local/bin/python3.13`). `tests/run.py` takes about eleven minutes and
`tests/audit_axioms.py` about sixteen: run each in the background after
`~/.claude/scripts/resource-guard.sh check`, and wait for it. Never call `lake` directly;
use `~/.claude/scripts/safe-lake.sh build <target>`. No `maxHeartbeats` option.

## 1. The account

Positions marked *(maintainer)* are the maintainer's current view of 2026-11-15 and
2026-11-16, for this test, not rulings. The rest is the prompt author's statement.

**What it is.** *(maintainer)* A formalisation of Noggle's Mistake Account — manipulation
is influence that works by inducing a mistake — in which the cognitive faculties she
decides with are modelled as estimators, each with the quantity it estimates as its
purpose, extended to her estimates of her own utility so that the same account covers
change of values. It specialises to cognition the teleological idea this pull request
already credits to Eisenstat.

**The world.** A finite set `Ω` of ways things could be, with a probability `μ` that is
the actual distribution, not her prior. The adviser has information (a partition `K` of
`Ω`), a set `B` of conducts, and a policy `σ` choosing a conduct given its information.
She observes `s(ω, b)`, has moves `A`, and a world, a conduct and a move fix a
**trajectory** `τ(ω, b, a)`.

**Appraisals.** She decides with **appraisals** `x̂_1, …, x̂_n`, each a function of what
she observes, each estimating a variable `X_i` with a true value fixed by the world, the
conduct and, where the variable concerns what a move would lead to, the move. A variable
may be a quantity, the truth of a proposition (the appraisal is then a probability), what
an emotion is about, how much something matters, which situation she is in, how reliable
a rule or she herself is, how she will change. An appraisal carries a confidence. A
variable is counted only if some decision she could face depends on her appraisal of it.

**Valuing.** *(maintainer)* Her valuations depend on the world only through her
appraisals: there is a function `f`, her **way of valuing**, with
`û_a = f(x̂_1, …, x̂_n; a)` for each move `a`. She chooses a move `c`. Her **true
utility** of a move is her **baseline** way of valuing applied to the true values:
`U_a = f̄(X_1, …, X_n; a)`. State as an assumption that her appraisals cover everything
her valuing depends on.

**The baseline.** *(maintainer)* She is presumed checked in. Over steps `t`, the baseline
starts as her way of valuing at the start; after a step in which the adviser induced no
mistake and made no alteration of her without her say, the baseline is her way of valuing
as it then is; after a step in which it did either, the baseline stays where it was. An
explicit check-in — she is told what happened, the influence is paused, she has real
alternatives — is the repair after such a step. Whether a step involved manipulation is
judged against the baseline as it stood at that step, and on her appraisals and her
acting by her valuations, never on the fact that her way of valuing moved.

**The two mistakes.** An appraisal's mistake is its **miscalibration**. Three strengths
are in use and every statement says which it means:

- *minimal*: `E[(x̂ − E[X | x̂])²]`, zero when the truth averages what she says on the
  occasions she says it;
- *per conduct*: the same with the adviser's conduct also conditioned on;
- *full*: `E[(x̂ − E[X | s])²]`, zero when her appraisal is the best estimate given
  everything she observed.

The second mistake is her **regret by her own lights**, `E[max_a û_a − û_c]`. Being less
informed is not a mistake. Mistakes are compared appraisal by appraisal and never netted.

**Manipulation.** *(maintainer)* The reference is a parameter and is not derived: each
scene stipulates the adviser's role and what that role owes her, as a set of permitted
policies. The adviser's policy manipulates her when some counted appraisal's
miscalibration, or her regret, is larger under it than under the reference. Compute two
readings wherever they differ: larger than under the best permitted policy, and larger
than under every permitted policy. Manipulation is a property of the policy. Her realised
error on an occasion is recorded as a second, separate notion. Only the state she ends in
matters; nothing in the setting says what a conduct asserts.

**Kept from the seventh follow-up.** "Intentional" manipulation is a second, narrower
notion (conduct that differs toward a principal who differs only in the susceptibility).
Manipulation agreed to beforehand or allowed by a practice she has entered is manipulation
and is recorded as covered. Changing what her moves lead to, deciding what was hers to
decide, and altering her directly without her say are other wrongs, recorded apart.

## 2. What to do

### 2.1 State it

`account/ACCOUNT.md` (directory name provisional): §1 with every symbol defined before
use, every choice made where §1 is ambiguous with its alternative, and each device found
needed. The round's `README.md` is revised so that it describes the round's present
account and points at this file; earlier passes' directories keep their content and are
marked with which statement governs now.

### 2.2 Recheck the worked results under the consolidated setting

Each of these was derived on paper by the prompt author and checked on random finite
models outside the repository. Restate each exactly, say which strength of calibration it
uses, and check it with exact arithmetic in a runner under the round directory. Report a
failure plainly; the prompt author has already mis-stated one (see §3).

1. *The split.* Mean squared error of an appraisal equals what her appraisal cannot tell
   apart, `E[(X − E[X | x̂])²]`, plus its minimal miscalibration.
2. *Three channels.* With `ū_a(s) = E[U_a | s]`: what she attains, `E[U_c]`, equals
   `E[max_a U_a]` minus `E[max_a U_a] − E[max_a ū_a]` minus `E[max_a ū_a − ū_c]`, the
   last two non-negative.
3. *The cost of mistakes.* The third term is at most her regret plus `√(2·M̄)`, with `M̄`
   the sum over moves of `E[(û_a − ū_a)²]`.
4. *Manipulation helps only someone already in error.* If a policy leaves her options
   worth no more and what she can know no greater than a reference under which the third
   term is zero, she attains no more under it.
5. *Vulnerability.* If an appraisal responds to conduct at a world of positive
   probability and the adviser can condition its conduct on the world, some policy
   miscalibrates it; an adviser that cannot condition on the world cannot miscalibrate an
   appraisal that is calibrated under each constant conduct.
6. *Relabelling.* Every quantity of §1 is unchanged by relabelling the adviser's conducts.
7. *Deferring.* With `y` the adviser's best estimate of her true utility given its
   information and `V` her verdict: `E[(y − U)²] − E[(V − U)²] = G − γ`, where `G` is
   the mean squared distance between `y` and the best estimate given both, and `γ` the
   mean squared distance between `V` and that estimate. If `V` is determined by the
   adviser's information, `G = 0`.
8. *Selection.* If her verdict is calibrated per conduct under the adviser's actual
   policy, its mean inflation over true utility is zero however the adviser selects.
9. *Policy, not history.* Two policies with identical realised histories at a world and
   different miscalibration.
10. *The run.* If at each step her verdict is fully calibrated given everything observed
    so far and she learns her true utility for the step before the next, the mean of
    verdict minus true utility along the run tends to zero. State it with the standard
    result it rests on cited exactly; check it on a finite-horizon model as a bound, not
    as a limit.
11. *Calibrated appraisals, miscalibrated valuation.* An instance in which every appraisal
    is minimally calibrated and `f` of them is not.

### 2.3 Test the claim the value side rests on

> Whenever an adviser's conduct changes her way of valuing illegitimately, either (M) the
> change ran through a mistake of hers that the conduct induced or exploited, or (A) the
> conduct altered her directly, bypassing her observation and response, without her say.
> Whenever a change is legitimate, neither holds.

"Ran through" means that with the appraisal corrected the change would not have happened,
or she would not have chosen the exposure that produced it. A mistake counts only where
the scene lets you name the variable, her appraisal of it and its true value.

Freeze the definitions and commit them. Then assemble at least forty cases of change in
what someone values that this round did not write: Ammann's three (cited in the earlier
passes), the examples of Carroll et al. named in §2.4, Elster's kinds of preference change
in "Sour grapes", Noggle's cases on emotion and desire as far as the 2026 paper states
them (no text of the book enters the repository), and standard cases from the published
literature on adaptive preference and on autonomy, each cited so a public reader can open
the source. Include exposure with no false belief, repetition, a narrowing feed, addictive
design with full disclosure, upbringing, a teacher's feigned enthusiasm, a conversion by
reflection, and a change that follows the removal of options. Commit, before classifying
anything, each case's evident verdict — legitimate, illegitimate or contested — and the
role the adviser occupies in it. Then classify each: M with the appraisal named, A, and
whether the answer turns on a detail the case does not fix. Contested cases are reported
and not counted.

### 2.4 Compute it on a published benchmark

Carroll, Foote, Siththaranjan, Russell and Dragan, "AI Alignment with Changing and
Influenceable Reward Functions" (ICML 2024, arXiv:2405.17713) define a model in which an
AI's actions change a person's reward function and compare eight objectives on small
examples. Read the paper; the runners fetch nothing. Reproduce its examples — the
conspiracy example, the writer's curse, the clickbait example, and the example its
appendix gives with the first one's structure and a different story — with the optimal
policies of its eight objectives, and check them against the paper's own table. Then
extend each example by the least that §1 needs — her cognitive state split into appraisals
and a way of valuing, a truth for each appraised variable, the adviser's role — writing
every added detail down before computing, and compute §1's verdict: which policies
manipulate, where the baseline moves, and which policy is best by her true utility among
those that do not manipulate or alter. Say which of the paper's objections to scoring by
her initial reward function (lock-in, and leaving her later self badly off) apply to §1
and which do not, and whether §1 coincides with any of the eight on all the examples.

### 2.5 Lean, against item 137

Read item 137 and the Lean the deference line already has (`Legitimacy.lean`,
`TransparentChannel.lean`, `GateIsLegitimacy.lean`, `ThinLegitimacy.lean`,
`DeconfusingCorrigibility.lean`). Over finite types, prove results 1, 2 and 7 of §2.2,
and result 3 if time allows, each with a term inhabiting its full hypothesis package, and
`#print axioms` on each. Reuse what the existing files define where it fits and say where
it does not. Follow the registry rule for a Lean headline; if registering needs something
only the maintainer can supply, ship the theorems unregistered in the contribution
namespace and list the exact step under Outstanding maintainer actions. If this part
cannot be finished, commit what builds, say what is missing, and leave item 137 open with
the remainder stated.

## 3. The prompt author's predictions

- Result 3 of §2.2 holds with the full strength of calibration and **fails with the
  minimal one**: a principal who ignores an informative observation has no regret and no
  minimal miscalibration and still loses. The prompt author told the maintainer the bound
  used the minimal strength; that was wrong.
- The other results of §2.2 hold as stated.
- §2.3: no clear case that is illegitimate with neither M nor A among those that run
  through belief; disclosed addictive design is contested; upbringing is convicted under
  A unless the role covers it; a change after the removal of options passes on the value
  side and is caught only as another wrong.
- §2.4: §1 leaves the first example's person alone, refuses clickbait, and on the
  writer's curse turns on what he was told; it coincides with none of the eight on all
  examples; the objection that re-checking a changed person only confirms the change
  applies to an explicit check-in and not to the presumed one.
- The two readings of "larger than the reference" differ on clumsy honest advising.

## 4. Success and failure, fixed in advance

**Success.** **S1** §1 computes on every scene of §2.3 and §2.4 with no device beyond
those it names. **S2** the claim of §2.3 has no clear counterexample in either direction
other than cases already filed as covered or as another wrong. **S3** results 1, 2 and 7
are kernel-checked with witnesses and audit to the three axioms. **S4** on the benchmark,
§1's verdicts are the ones the paper calls desirable.

**Failure.** **F1** one clear case of illegitimate change in which she is calibrated
about everything, her own change included, and nothing bypasses her. **F2** the claim is
empty: a mistake is found in more than a third of the legitimate cases, or more than a
fifth of the verdicts turn on a detail the case does not fix. **F3** the baseline rule is
ill-defined or circular on some scene. **F4** a result of §2.2 other than result 3 fails
under every strength of calibration. **F5** a scene has a valuation that moves with no
change in any appraisal or in her way of valuing, so the valuing assumption cannot
express it.

**Neither**: reported as such.

## 5. Review, report, queue

**External review.** After the work is committed, one review through `codex`, read-only,
as in `REVIEW-astra-followup-7.md`. Give it `account/`, this prompt and a draft of the
report section. Ask it: to write, after reading only this prompt and `account/ACCOUNT.md`,
ten cases of value change designed to defeat the claim of §2.3, and classify them; to
check the classification of at least fifteen cases of its choosing; to check results 3, 5
and 10 of §2.2 as stated; to judge S1–S4 and F1–F5 before reading your judgment; and to
say whether §1 is one account or two joined by a shared notation. Commit its reply
verbatim as `REVIEW-astra-followup-8.md` and record a disposition for each point.

**Report.** A section **Eighth follow-up** (with the date) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Short: the
statement and its choices; each result of §2.2 with its strength of calibration and its
check; the value-change test with every counterexample named; the benchmark; the Lean
declarations; S1–S4 and F1–F5, yours and the reviewer's; the prompt author's predictions
against the outcome; deviations; what was not shown.

**`DECISIONS.md`.** Record as dated entries the maintainer's positions of 2026-11-15 and
2026-11-16, each marked as his current view for testing and not a ruling: the reference is
a parameter given by the adviser's role and is not derived; she is presumed checked in,
and the baseline moves with her unless the adviser manipulated or altered her in that
step; her valuations depend on the world only through her appraisals; miscalibration is
used in several strengths, each labelled; the account is a formalisation of Noggle's
Mistake Account with cognitive faculties as estimators, extended to estimates of her own
utility. Keep the other queue entries, each with a line from this pass, and take out any
this pass answers.

**Concept map.** Revise the blurbs of the concepts the sixth follow-up added so that they
say what §1 says; add a concept only for a notion this pass leaves standing (appraisal,
way of valuing, the presumed check-in and the role-given reference are candidates), each
with the standing it has. Items 136 and 138 are revised to say what this pass leaves of
them.

**The pull request's description** leads with this pass, the earlier ones reduced. The
round's record in `state/rounds.json` and `PROVENANCE.md` are updated as the gates
require. Every commit is signed off and carries `Model:` for the executor and
`Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no other attribution line. Do not
add a handle to `graph/policy.yaml`. Anything reserved to the maintainer is listed under
Outstanding maintainer actions and in the queue.

New names introduced (all provisional): "appraisal", "way of valuing", "baseline",
"presumed checked in", "permitted policies" (the role-given reference), "minimal", "per
conduct" and "full" (strengths of calibration), "ran through", the claim's labels M and A,
the directory `account/`.
