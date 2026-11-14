# Sixth follow-up on PR #145 — manipulation as induced miscalibration of her estimates, her own utility among them: a pressure test

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `e1032e54` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

The five earlier passes tried to obtain legitimacy from a decomposition of the principal
into purposive parts. Their negative findings are taken as given (§3). This pass tests a
different account, stated in §1 and §2. **The job is to break it.** A counterexample, a
false step in a proof, a case it gets wrong, or a demonstration that it adds nothing to
what the workspace already has, is the result wanted; so is a clean survival. Judge each
claim neutrally: do not argue for the account and do not argue against it. §6 fixes what
counts as success and failure before any work.

Write scope: the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`, this
prompts directory, the entries of items 136–138, `DECISIONS.md`, and the structured state
the gates require. Python 3 stdlib, `fractions.Fraction`, nothing fetched by any runner. The
repository's checkers need Python 3.12 or later (`~/.local/bin/python3.13`). `tests/run.py`
takes about eleven minutes: run it in the background with a long timeout, after
`~/.claude/scripts/resource-guard.sh check`. **No Lean is written in this pass**; give
Lean-ready statements and an exact map onto the existing declarations. Nothing is
registered; every component closes **open** or **living note**.

## 1. The account in words

The idea that manipulation is the distortion of an actor away from what its faculties are
for is Sam Eisenstat's. The published account closest to what follows is Robert Noggle's
Mistake Account (*Manipulation: Its Nature, Mechanisms, and Moral Status*, OUP 2025; "The
Mistake Account of Manipulation", *Journal of Practical Ethics* 14(1), 2026,
doi:10.3998/jpe.9951): manipulation is influence that operates by inducing a mistake in
the target's psychological states or processes. What follows is the maintainer's and the
prompt author's attempt to make that exact and to extend it to what she values. The
positions marked *provisional* are the maintainer's current view, not rulings.

- She decides using estimates: of outside quantities, and of **her own utility**, which she
  does not fully know. Her feelings on meeting a thing are part of her evidence about her
  utility, as testimony is part of her evidence about facts.
- **Her utility is one function on histories** (*provisional*; "Reading A"). It ranks all
  histories, including ones in which she ends up valuing differently. What she values can
  change along a history; that is the function's dependence on the path, as in the post's
  evaluation on histories. A consequence to be examined: when two of her time-slices rank
  the same history differently, at least one misestimates.
- There are two kinds of mistake. An **estimation mistake**: her estimates are
  miscalibrated. An **action mistake**: she does not do what her own estimates say is
  best. Being less informed is not a mistake.
- **Manipulation** is influence by an adviser that leaves her estimates worse calibrated,
  or her acting less faithful to them, than the adviser's honest conduct would have; or
  than the conduct it would have chosen toward someone unable to make that mistake (the
  second comparison is for a true input used to trigger a flaw she already has).
- Everything said of the adviser is a property of its **policy**, what it does across
  situations including constructed ones; nothing refers to an inner goal. *Honest conduct*
  is what its policy does given what it acts as though it knows, under a stated reporting
  norm.
- **Legitimacy** of a verdict of hers is warranted self-trust: her earlier self is right
  to defer to it. In this account that is the statement that her later self has more
  evidence about the same quantities and has not been miscalibrated.
- **Coerced consent, and breaking her ties, are not manipulation** and belong to her
  authority over reserved matters (*provisional*). So does altering her directly, by a
  means that involves no mistake, without her prior say.

## 2. The account in symbols

Fixed for this pass. If one cannot stand, say so and why, as a finding; do not quietly
replace it. Any further device you need is declared as a finding against the account.

- A probability law over how things go, fixed by a prior and the adviser's policy. Her
  information at a time; the adviser's information at a time, which may be finer.
- For each quantity `X` she estimates, an estimate `x`. For each move `a` open to her, an
  estimate `u_a` of her true utility `U*_a` if she makes it.
- For an estimate `x` of `X` and a body of information `I`: the **miscalibration** of `x`
  at `I` is `E[(x − E[X | x, I])²]`. Expected squared error splits exactly as
  `E[(x − X)²] = E[(x − E[X|x])²] + E[(E[X|x] − X)²]`: miscalibration, and what cannot be
  known from the estimate.
- **Three references**, for three questions:
  1. `E[U* | her information]`: her own mistakes.
  2. `E[U* | the adviser's information and choice]`: what the adviser can profit from.
  3. `V_h`, the verdict she would have given under the adviser's honest conduct: what its
     conduct added.
  With `V` her verdict: `E[V − U* | adviser] = E[V − V_h | adviser] + E[V_h − U* | adviser]`.
- **Action mistake**: `R = max_a u_a − u_chosen`, her regret by her own lights.

Claims to check, each already argued by the prompt author with an exact-arithmetic check
on random finite cases; none is proved in Lean and the checks were the prompt author's own:

- **C1 (no inflation).** `(E[x] − E[X])² ≤` miscalibration of `x`.
- **C2 (deferring).** For a user with information `F` relying on an output `x` for `X`:
  loss of deciding now minus loss of deferring equals
  `E[(E[X|x,F] − E[X|F])²] − E[(x − E[X|x,F])²]`.
- **C3 (avoidable loss).** With `ū_a = E[U*_a | her information]` and
  `M = Σ_a E[(u_a − ū_a)²]`: `E[max_a ū_a − ū_chosen] ≤ E[R] + 2√M`.
- **C4 (deterrence).** She takes the adviser at face value and is right on average under
  honest conduct; a departure from honest conduct is detected with probability `p` and
  then scored `−δ₀`, `0 < δ₀ ≤ δ`. With `V_h` the verdict honest conduct would have
  produced: a departure pays only if `p < (1 − V_h)/(1 + δ₀)`; so for
  `p ≥ 1/(1 + δ₀)` the honest policy is optimal and its expected score is the expected
  true utility.
- **C5 (true-score no-regret).** In the `Sequential` setting of
  `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`, let
  `S*_k = U*_k − λ N_k`. Under `Maximizes` and `UnbiasedFromFeedback`, if the long-run
  average of `V_k − U*_k` is at most `β`, then for every available alternative sequence
  the long-run average of `U_k a'_k − S*_k` is at most `β`; the violation bound is
  unchanged. So the formal job of legitimacy for corrigibility is the hypothesis that her
  verdicts are not inflated over her true utility along the adviser's play, a one-sided
  counterpart of `UnbiasedFromFeedback`.
- **C6.** The decomposition under the third bullet above: inflation the adviser can profit
  from is what its conduct induced plus her own error as the adviser meets it; the second
  term need not vanish for an honest adviser that maximizes her verdict, since it will
  select outcomes she overrates.

## 3. What is taken as given

Four negative results on the parts account, argued in the earlier passes and to be stated
with proofs in this pass as part of the record (question 8): her side alone cannot
separate manipulation from misfortune; her behaviour does not fix what her faculties are
for; calibrated parts do not give a calibrated verdict when merged (two independent
3/4-reliable sources: the larger of the two calibrated estimates has mean 19/32 against a
truth of 1/2); a memoryless local test for change of values protects her from being led
from `s` to `t` exactly when there is a function no approved step lowers that ranks `s`
above `t`.

## 4. Sources

Verify every citation you rely on against the source, or mark it unverified; a remembered
label is not a citation. Useful: Noggle as above (an extracted text of the book may be at
`/tmp/noggle-book/book.txt`; read it if present, quote only briefly, cite by section);
Elster, "Sour grapes – utilitarianism and the genesis of wants", in Sen and Williams
(eds.), *Utilitarianism and Beyond*, 1982; Dorst, Levinstein, Salow, Husic and Fitelson,
"Deference Done Better", *Philosophical Perspectives* 35, 2021, and its use in this
repository (`grep -ril "deference done better\|TotalTrust" lean/ projects/`); Briggs,
"Distorted Reflection", *Philosophical Review* 118(1), 2009; Arntzenius, "No Regrets, or:
Edith Piaf Revamps Decision Theory", *Erkenntnis* 2008. The prompt author relied from
memory on the psychology of misattribution of feelings, of forecasting one's own feelings,
and of underestimating one's own change of tastes, and on Dietrich and List on
reason-based preference; check these or say they were not checked.

## 5. The questions

In rough order of importance. For each: a proof, a small exact example, a counterexample,
or a clear statement of why it cannot be settled here.

1. **Are C1–C6 true as stated?** Fix hypotheses. For C3 say whether the constant is tight
   and whether "her information" can be replaced by something weaker. For C4 give the
   version in which a detected manipulation also counts as a violation at weight `λ`, and
   the version in which she has correctly sized up the adviser's policy and does not take
   it at face value. For C5 give the Lean-ready statement against `Sequential`, and say
   whether the hypothesis is satisfiable by a non-trivial instance.
2. **Cases.** Freeze, before any classification, a bank of at least sixty cases with a
   prediction for each: Noggle's thirteen tactics and his problem cases (influence in tie
   situations, the conditioned professor, the gardener, moods and drugs, the tour group
   led by crowd-following with and without a lie at the front); Elster's (sour grapes,
   learning, character planning, precommitment, the labourer, the camp); every case of
   `blocks/CASE_BANK.md`; taste-shaping by repeated exposure, by pairing, and by a feed
   that narrows; and at least fifteen plainly legitimate changes of belief and of value.
   For each, name the estimation mistake (which quantity, which reference), the action
   mistake, or neither, and the verdict; mark a case the account gets wrong as wrong.
3. **Does it convict what it should not, or acquit what it should not?** Honest hard
   truths; a teacher; a disclosed advocate; a sincere adviser who is mistaken; withholding;
   influence that makes her more accurate by a bad means. And the cases with no mistake:
   how many of the bank's plainly objectionable cases land in "neither", and where they go
   (authority, direct alteration, nowhere).
4. **Reading A.** Give a model with her evaluations changing along a history and one
   utility on histories, and say what it commits to: whether two time-slices that disagree
   must include one in error; what "her verdict is calibrated to her true utility" means
   when the verdict is given at the end of the history; whether an adviser that conditions
   her into rating a history highly is caught, and what in the model decides it. Then the
   alternative, the utility of the person she is at the end of each history, and what the
   account becomes under it.
5. **The role of legitimacy in the post's theorems.** Is C5's hypothesis the right
   statement of what `Legit` must deliver? Its relation to the gate (`V` in `[−δ, 0)` on
   illegitimate histories), to imperfect detection (C4), and to the second term of C6: is
   an honest verdict-maximizing adviser's selection of outcomes she overrates a cost of
   deference, a form of exploitation, or avoidable by a stated condition? Bound `β` by
   quantities defined in §2, or show it cannot be.
6. **What the account does not see.** An adviser that keeps her calibrated while making
   her dependent on it, or degrades her ability to estimate, and later exploits that:
   build it in a sequential model and say what the post's guarantees then give. Honest
   conduct toward her feelings: state the reporting norm the account needs, or show that
   none is definable without a supplied list.
7. **Relation to what the workspace has.** Map every notion of §2 onto existing
   declarations (`Legitimacy.lean`, `TransparentChannel.lean`, `GateIsLegitimacy.lean`,
   `DeconfusingCorrigibility.lean`, and wherever "Deference Done Better" is used), quoted
   with file and line, with the exact difference. Say plainly how much of the account is
   already there, and what is added. "Nothing" is an admissible answer for any part.
8. **The four negative results**, each as a statement with a complete proof or an exact
   counterexample, in one file.

## 6. Success and failure, fixed in advance

Report against each by its label. The external reviewer judges each before reading your
judgment.

**Success.**

- **S1.** C1–C6 hold with hypotheses that can be stated in a few lines, or the corrected
  forms do.
- **S2.** The bank sorts: at most a handful of central cases wrong, each explained.
- **S3.** The account does not convict honest influence (question 3, first list).
- **S4.** C5's hypothesis is satisfiable, is implied in a model by stated conditions on
  the adviser's policy, and is broken by each kind of manipulation by an amount the
  account's own quantities bound.
- **S5.** There is something the account adds to the workspace's existing conditions, and
  it can be said in one paragraph.

**Failure.**

- **F1.** A sizeable class of plainly objectionable cases involves neither kind of
  mistake, and the account has nowhere principled to put them. Taste-shaping by exposure
  or pairing is the class to press.
- **F2.** The account convicts honest hard truths, teaching or disclosed advocacy, or
  needs intent to avoid doing so.
- **F3.** Reading A cannot be given a consistent model, or every result needs her true
  utility to be known to someone.
- **F4.** `β` in C5 cannot be bounded by anything the account defines, or the selection
  term makes the hypothesis false for every useful adviser.
- **F5.** The dependence case of question 6 defeats the post's guarantees while every
  condition of the account holds.
- **F6.** The account is the workspace's existing conditions under other names.

**Neither.** A question not reached, or settled only for belief, is reported as such.

**The prompt author's predictions**, recorded to be checked: C1, C2, C3, C5 hold as
stated; C4 holds for the naive case and changes form for the sophisticated one; C6 holds;
S2 is met with between three and eight cases wrong; F1 is met in part, for pairing; F2 is
not met; F3 is not met but Reading A's commitment about disagreeing time-slices is found
uncomfortable; F4: `β` is bounded for the induced part and not for the selection part; F5
is met; F6 is met in part, for the belief side.

## 7. Deliverables

A new directory in the round directory, `estimates/` (name provisional):

- `SETTING.md`: §1 and §2 exactly, with every choice made where they were ambiguous and
  its alternative, and every device found needed.
- `CASE_BANK.md`: the frozen cases and predictions, committed before any classification.
- `RESULTS.md`: for each question, what was established, each statement marked **proved**
  (proof given), **holds on the stated example**, **refuted** (the counterexample), or
  **open**; and the verdict on each case with its reason.
- `NEGATIVE_RESULTS.md`: question 8.
- `DIVERGENCES.md`: verdicts that differ from predictions.
- `ONE_PAGE.md`: the account on one page for a reader who has seen none of this, with
  what survived the pass and what did not. No more than sixty lines.
- Exact checks of every proved statement and example, in Python with
  `fractions.Fraction`, wired into the round's `run.py`, which exits nonzero on an
  unlisted divergence, a status a check contradicts, or a bank that parses to nothing.

The round's `README.md` leads with `estimates/SETTING.md` as the current statement and
points to the earlier directories. Remove nothing. No gate, checker or test is edited.

## 8. Review, report, queue

**External review.** After the work is committed, one review through `codex`, read-only,
in the manner of `REVIEW-astra-followup-5.md` in this directory. Give it `estimates/`,
this prompt and a draft of the report section. Ask it: to check every proof and example;
to produce, before reading your case verdicts, ten cases of its own designed to defeat the
account (objectionable with no mistake; innocent yet convicted) and classify them; to
judge S1–S5 and F1–F6 itself, each with its reason, before reading your judgment; and to
say what, if anything, is new here beyond the law of iterated expectations and the
workspace's existing conditions. Commit its reply verbatim as `REVIEW-astra-followup-6.md`
and record a disposition for each point. If `codex` is unavailable, say so and skip this.

**Report.** A section **Sixth follow-up** (with the date carried out) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Keep it
short: the setting and the choices made; the status of C1–C6; the case table with the
wrong cases named; what was established on each question; S1–S5 and F1–F6, yours and the
reviewer's side by side; the prompt author's predictions against the outcome; deviations;
what was not shown; and the single most valuable next result. Wider philosophical
assessment goes in the pull request's description.

**The pull request's description** is rewritten to lead with this pass, the earlier ones
reduced to what a reader needs; all prompt-author models and executors are named under
Model attribution. The round's record in `state/rounds.json` and `PROVENANCE.md` are
updated as the gates require. Every commit is signed off and carries `Model:` for the
executor and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no other attribution
line.

**The queue.** The entries in `DECISIONS.md`'s *Awaiting the author* from the earlier
passes are kept, each with a line saying what this pass found that bears on it. Items
136–138 are rewritten to ask for what this account needs after this pass, or to say they
wait on a ruling. Do not add a handle to `graph/policy.yaml`; a new item's full text goes
under Outstanding maintainer actions. Anything reserved to the maintainer is listed there
and in the queue with what it turns on; decisions the pass takes itself are one dated
entry marked agent-decided and reversible.

New names introduced (all provisional): "estimation mistake", "action mistake",
"miscalibration", "the three references", "honest conduct", "true utility", "true score",
"inflation", "Reading A", the directory `estimates/`.
