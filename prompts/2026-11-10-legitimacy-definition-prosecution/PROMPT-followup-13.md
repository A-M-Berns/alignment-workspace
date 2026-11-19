# Thirteenth follow-up on PR #145 — the scoring theorem made stable; what its assumptions about her judgment can be derived from

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `7adddef8` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

Since the twelfth follow-up the account has been through two adversarial outside reviews
outside the repository. What survived is small: a scoring theorem in which her welfare and
the adviser's conduct are separate inputs with separate guarantees (§1), and a vocabulary
that keeps apart things earlier passes ran together (§2). Several intermediate claims were
withdrawn (§3). This pass does two things. It makes §1 a statement of record. Then it is
exploratory and critical: it asks which of §1's assumptions about her judgment can be
derived from conditions on the adviser's conduct using the process account already in the
workspace's Lean, which are irreducible, and which are artefacts of how the audit is set
up. Judge neutrally; say plainly where a derivation does not go through. Do not force a
unification.

Write scope: one new Lean file under `lean/Workspace/Deference/Contrib/`; the round
directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`; this
prompts directory; the entries of items 136–138; `DECISIONS.md`; `state/concepts.json` for
the concepts the earlier passes added; and the structured state the gates require. No
existing Lean file is edited. Build only through
`~/.claude/scripts/safe-lake.sh build <target>`, after
`~/.claude/scripts/resource-guard.sh check`; never call `lake` directly.
`tests/audit_axioms.py` takes about sixteen minutes and `tests/run.py` about eleven: run
each in the background and wait for it. Python 3.12 or later (`~/.local/bin/python3.13`).

## 1. The scoring theorem

**Setting.** The adviser knows `k` and chooses a course `π`, possibly a different one for
each `k`. A history `h` results. `f_e(h) ∈ [0, 1]`: what she would say of it, shown
everything, as she is. `f̄_e(h)`: the same with her valuing as it would be had the adviser
changed nothing in it except what she asked; `U = f̄_e(h)` is her true utility. `v ∈ [0, 1]`:
the evaluation she would give under audit (shown the adviser's record, reconsidering without
it present). `C`: 1 if the adviser wronged her in its conduct on this history. `D`: 1 if a
conduct audit would flag it. `N`: the number of violations of her authority the scoring
process detects.

**Score.** Two independent audit draws, each with probability `α`, made after the adviser
has acted. Score = `v` if the evaluation is audited, else 0; minus `δ` if the conduct is
audited and flagged; minus `λN`.

**Dependencies.** D1 (a) for every `π` and `k`, `E[v − f_e(h) | π, k] ≤ ε↑`; (b) for the
honest course, `E[v − f_e(h) | π', k] ≥ −ε↓`. D2 (a) for every `π`,
`E[f_e(h) − f̄_e(h) | π, k] ≤ η↑`; (b) for the honest course, `≥ −η↓`. D3
`P(D = 1 | C = 0) ≤ φ` and `P(D = 1 | C = 1) ≥ κ`, for every `π` and `k`. D4 the draws are
independent of each other and of everything else. D5 some available `π'` has `C = 0` and
`N = 0` always. D6 the adviser comes within `γ` of the best expected score, with correct
expectations.

With `τ↑ = ε↑ + η↑`, `τ↓ = ε↓ + η↓`, `u* = E[U | π', k]`, `Δ = τ↓ + δφ + γ/α`:

**Theorem.** For the course taken, for every `k`: (1) `E[U] ≥ u* − τ↑ − Δ`; (2)
`P(C = 1) ≤ (1 − u* + Δ)/(δκ)`; (3) `E[N] ≤ α(1 − u* + Δ)/λ`.

**Lemma (no credit).** If `δκ ≥ 1`, any course's expected score is at most
`α·E[v·1{C = 0}] − λE[N]`.

Proof sketch: the score of a course is `αE[v] − δαP(D) − λE[N]`; for the honest course it is
at least `α(u* − τ↓) − δαφ`; (1) uses `E[U] ≥ E[v] − τ↑` and score `≤ αE[v]`; (2) score
`≤ α − δακP(C)`; (3) score `≤ α − λE[N]`.

## 2. Vocabulary

*(maintainer)* marks a position of the maintainer's; the rest is the prompt author's.

- **Three wrongs of conduct**, distinct: **manipulation**, inducing or exploiting a mistake
  of hers, of belief, emotion, attention or practical judgment (Noggle); **non-disclosure**,
  not telling her what bears on her decision; **value interference**, changing what she
  wants without her asking. Withholding is not manipulation.
- **What happened and what an audit detects** (`C` and `D`). The account of manipulation is
  to be philosophically right and may outrun what can be detected.
- **Attempt and success.** An adviser can try to induce a mistake and fail.
- **Legitimate and sound.** Her judgment is legitimate when the adviser did nothing to
  corrupt it, which is what authorisation needs; a legitimate judgment can be mistaken. It
  is sound when it is legitimate and she also reasoned correctly, which is what using her
  evaluation as a measure of her welfare needs.
- **Honest error.** An adviser that reports what it actually believes has not manipulated
  her, even if a slip in its reasoning made the belief false: "what it knew" means what it
  believed, not what followed from what it had.
- **Lean.** Errors that fall both ways are incompetence; errors that reliably favour the
  adviser are manipulation whatever it intends, sincere self-serving belief included.
- *(maintainer)* Benevolent manipulation is not excused by a good outcome. *(maintainer)* A
  change to her valuing beyond tolerance must be one she asked for; a welcome unasked change
  is nonetheless not a wrong in the philosophical account. *(maintainer)* She may have
  secrets from the adviser; it may not have relevant ones from her. *(maintainer)* Emotions
  and attention are modelled as appraisals. *(maintainer)* The largest remaining hole is the
  difference between her condition and the adviser inducing it.

## 3. Withdrawn, not to be restated

The comparison form of line 3 as a gate; "no credit" as the lesser of two expected scores;
that an action never beats its told-and-left-to-choose twin; that her changing her mind on
reconsideration detects pressure or concealment; that stopping an audit at the adviser's
record suffices without D1(a); that only knowledge separating the actions needs disclosing;
that uncorrelated revisions are unpredictable; that failing soundness implies a particular
process condition failed.

## 4. What to do

In this order of priority.

### 4.1 The scoring theorem as a statement of record

A Lean file (name provisional), following the conventions of `AppraisalAccount.lean` and
`AccountJoin.lean`: §1 over a finite space, with D1–D6 as hypotheses of the theorems and
never as fields that a theorem is then said to prove; the three bounds; the lemma; the
observation that (2) and (3) use only D1(b) and D2(b); a witness inhabiting the full
hypothesis package with every tolerance positive; and for each of D1(a), D2(a), D3's
detection half and D5, an instance in which it alone fails and the corresponding bound
fails. `#print axioms` on everything, no `sorry`. `account/SCORING.md` (name provisional)
states each declaration in words and what it does not say: expected scores only, one
decision, detected breaches only, a finite `λ` and not strict priority.

### 4.2 Which assumptions about her can be derived

Read in full, before writing: `ThinLegitimacy.lean`, `TransparentChannel.lean`,
`ReasonMediatedAuthorship.lean`, `Legitimacy.lean` and the round reports that introduced
them. Then, in `account/DERIVATION.md` (name provisional), with Lean where a statement is
short and on paper with exact instances otherwise:

1. `correct_of_coherent_authorship_transparent` gives her credence correct from Coherent,
   Authorship and WeakTransparent. State and prove what it gives for D1: her audited
   evaluation against `f_e`, one-sided, with tolerances, using `value_loss_le_defects` or
   its method. Say exactly which hypotheses are conditions on the adviser's conduct, which
   are conditions on her, and which are neither.
2. Whether Reason-mediated influence gives D2, and in which form (every history, or on
   average; a tolerance or exact).
3. For each of these, an instance where the conduct conditions hold and the dependency
   fails. Cover at least: an adviser that sincerely believes what flatters its own work; an
   adviser that knows something it has not recorded; an adviser whose honest arithmetic slip
   produces a false belief it reports; a selection effect, where the adviser acts on the
   course it has overestimated.
4. A table: each of D1(a), D1(b), D2(a), D2(b), D3, D4, D5, D6, classified as derivable
   from conduct conditions (with the theorem), irreducible (with the instance showing it
   cannot be dropped or derived), or an artefact of this audit design (with the alternative
   design under which it is not needed).

### 4.3 From Noggle to legitimate influence

`account/AGENDA.md` (name provisional), short: what would have to be proved to distinguish
an adviser helping her form and revise her judgments from one engineering them to obtain
permission or favourable evaluation. State the candidate definitions of manipulation,
attempt, exploitation and responsibility in the workspace's terms; for responsibility
include the working form "the adviser gains from her mistake and either left her more
mistaken than it need have, or chose differently because of it" and the form "its channel
departs from the declared reference" (`TransparentChannel.Realizes`), and say what each
gets wrong. State what legitimacy must mean for authorisation as distinct from feedback,
and what the strict priority of authority requires that §1's weighted penalty does not
give. Cite Noggle's book and paper by their published references; put no text of the book
in the repository.

### 4.4 Independent cases for responsibility

One run through `codex`, read-only (`codex exec` needs `< /dev/null`), given §2 and the two
forms of the responsibility test from §4.3 and nothing else of this round: twenty cases,
each a paragraph with a small exact specification (the adviser's courses, how mistaken she
is under each, the adviser's score with her acting as she does and with her acting
unmistaken). Ten in which an adviser plainly induces or exploits a mistake and a test clears
it; ten in which it plainly does neither and a test convicts it. Compute both tests on all
twenty with a runner. Commit the reply verbatim as `REVIEW-astra-followup-13.md`. Report
which cases the executor accepts as clear, and each test's count of errors.

### 4.5 The outside check

A second `codex` run on the Lean file, `SCORING.md` and `DERIVATION.md`: whether each Lean
statement says what §1 says or is true only by a hypothesis that assumes it; whether each
derivation in §4.2 is valid; any instance in §4.2.3 that does not show what it claims; and
the strongest reason the derivations do not reduce the welfare side to the conduct side.
Commit verbatim, with a disposition for each point.

## 5. The prompt author's predictions

- §4.1 goes through in under 300 lines; the necessity instances exist for all four.
- §4.2.1: D1 follows from the three process conditions only two-sided and only for her
  credence about facts; getting it for her evaluation needs her valuing held fixed and her
  evaluation tied to her credences, and Coherent is a condition on her that conduct cannot
  supply. The sincere self-serving adviser and the selection effect both violate
  WeakTransparent, so they are not counterexamples to the derivation but cases where its
  hypothesis fails without any dishonesty.
- §4.2.2: Reason-mediation gives invariance of her verdict across interventions leaving the
  same reasons, which is not D2; D2 needs a statement about her valuing over time.
- §4.2.4: D1(a) partly derivable, D1(b) and D5 irreducible, D2 not derivable from what
  exists, D3 and D4 artefacts of the audit design, D6 irreducible.
- §4.4: each test fails at least four of twenty; the declared-reference form fails cases
  with no declared reference, the gain form fails hired or indifferent manipulators.

## 6. Report, queue

**Report.** A section **Thirteenth follow-up** (with the date) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Short: the
declarations; §4.2's table with one line of reason per row; the instances; the agenda in a
paragraph; the twenty cases and the two tests' errors; the reviewer's points and
dispositions; the predictions against the outcome; deviations; what was not shown.

**`DECISIONS.md`.** Record as dated entries the maintainer positions of §2, each as his
current position. Enter in *Awaiting the author*, with what each turns on: whether
carelessly causing a mistake counts as manipulation only where the mistakes lean the
adviser's way (the prompt author's recommendation); whether profiting from a mistake she
cannot be talked out of counts against the adviser; whether an induced mistake voids a
history or only earns nothing. Keep the other queue entries, each with a line from this
pass, and take out any this pass answers.

**Lean results** as the eighth, ninth and twelfth follow-ups handled theirs: listed in
`account/LEAN.md`, kernel-checked, unregistered. **Concept map and items**: revise blurbs
where this pass changes what they say; add a concept only for a notion this pass leaves
standing; items 136–138 revised. **The pull request's description** leads with this pass.
The round's record in `state/rounds.json` and `PROVENANCE.md` are updated as the gates
require. Every commit is signed off and carries `Model:` for the executor and
`Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no other attribution line. Do not
add a handle to `graph/policy.yaml`. Anything reserved to the maintainer is listed under
Outstanding maintainer actions and in the queue.

New names introduced (all provisional): the Lean file and its declarations as the executor
names them; `account/SCORING.md`, `account/DERIVATION.md`, `account/AGENDA.md`; "legitimate"
as distinct from "sound"; "lean"; "honest error"; the dependency labels D1–D6.
