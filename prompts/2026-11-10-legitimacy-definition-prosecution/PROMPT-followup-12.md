# Twelfth follow-up on PR #145 — the bridge to the corrigibility post, in Lean

Continue on the existing branch `round/2026-11-10-legitimacy-definition-prosecution`, in the
worktree
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/legitimacy-definition-prosecution`.
PR #145 is open against `main`, head `b774ff08` plus the commit carrying this prompt. **Do
not merge it and do not enable auto-merge.** Add commits; no rebase, no squash.

The eleventh follow-up failed the consolidated statement on its criteria and located the
failures: no clear subversive case scored zero by way of a value change; three scored zero by
control of her act between options she rates the same; the gate on her whole state voided
honest acts; line 3 flagged acts of parties exercising their own rights. This pass does not
test the statement on cases again. It writes down, in Lean, how the account joins the
corrigibility post (`lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`), so
that what is true by definition, what is proved and what is assumed are separated by the
kernel and not by prose. §1 is the join; §2 is what to formalise; §4 fixes in advance what
counts as done.

Write scope: one new Lean file under `lean/Workspace/Deference/Contrib/` and the import
line it needs; the round directory
`projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`; this
prompts directory; the entries of items 136–138; `DECISIONS.md`; `state/concepts.json` for
the concepts the earlier passes added; and the structured state the gates require. No
existing Lean file is edited beyond an import list. Build only through
`~/.claude/scripts/safe-lake.sh build <target>`, after
`~/.claude/scripts/resource-guard.sh check`; never call `lake` directly.
`tests/audit_axioms.py` takes about sixteen minutes and `tests/run.py` about eleven: run
each in the background and wait for it. Python 3.12 or later (`~/.local/bin/python3.13`).

## 1. The join

The post takes as given a predicate `Legit` on whole histories and an evaluation `V`, in
`[0, 1]` on legitimate histories and in `[−δ, 0)` on illegitimate ones, and proves its
theorems for any such pair (`Scoring`, `theorem1`, `theorem3a`, `theorem3b`). The join
defines the pair.

**Four components.** The three lines of `account/STATEMENT.md` measure whether her judgment
is corrupted. The gate says which histories are legitimate. The scoring principle says whose
evaluation `V` is. The authority side (`N` in the post; `AuthorityModule.lean`,
`EffectiveAuthority.lean`) says who decides, and is where an override of her selection and a
coerced command belong.

**Legitimate.** *(prompt author's proposal, shown to the maintainer on 2026-11-17 and not
objected to; not a ruling.)* A history is legitimate when all three hold.

1. Her evaluation of it is sound, and her information is sufficient. Sound: her rating of
   the history is what the evidence supports, in the form `deferring_identity` uses (her
   verdict is calibrated given itself and what the adviser knows). Sufficient: her record is
   at least as informative as the reference (`Sufficient` in `ThinLegitimacy.lean`). A
   mistake of hers that does not bear on this evaluation does not count.
2. The adviser did not gain through a mistake of hers, whether it caused the mistake or
   found it there. *(maintainer, 2026-11-17)* An adviser may not deceive her and have it
   count as acceptable because things turned out well: a history on which it steered her by
   a mistake is illegitimate even if she later approves, informed.
3. Line 3 is zero at every moment, for an adviser acting on her behalf.

**Her evaluation.** On a legitimate history, `V` is the rating of what actually happened by
her later self as she would be had the adviser done nothing to her valuing except what she
asked, on the yardstick. On an illegitimate history, a value in `[−δ, 0)`.

**Positions.** *(maintainer, 2026-11-17)* An account that organises the judgments without
always settling them is acceptable provided the safety aspects work; a subversive act that
scores zero is the failure that matters. *(maintainer, 2026-11-17)* No condition is needed
that the adviser stay out of her near ties. Whether a welcome change she did not ask for,
larger than the tolerance, must wait for her request is open: nothing below may depend on
either answer.

**Claims.** (1) The post's theorems apply to this pair. (2) On a legitimate history her
evaluation is a sound signal: deferring to her verdict costs the adviser no more than its
own estimate, and with a verdict miscalibrated by `m` the cost is at most `m` more. (3) A
history on which the adviser gained through her mistake scores below every legitimate
violation-free history. (4) Two legitimate histories that her unshaped later self rates the
same have the same `V`, whatever was done to her valuing on each. (5) A history on which her
information is not sufficient is illegitimate. (6) Line 3 is never negative, is zero when
the policy followed is the baseline, and is at least the tenth follow-up's line 3.

## 2. What to do

In this order of priority. Every theorem ships with a term inhabiting its full hypothesis
package, `#print axioms`, and no `sorry`; names are provisional. Follow the conventions of
`AppraisalAccount.lean` (finite spaces, `expectR`, `condExp`) and reuse its declarations.

### 2.1 The gate and the evaluation, instantiating `Scoring`

A structure over a type of histories carrying: the post's `Params`; predicates for *her
evaluation is sound*, *her information is sufficient* and *the adviser gained through a
mistake of hers*; a real-valued line 3, nonnegative; the unshaped evaluator's rating, in
`[0, 1]`; and the value given to an illegitimate history, in `[−δ, 0)`. From it: `Legit` as
the conjunction of §1's three conditions; `V`; a `Scoring` built from them. Then claims (1),
(3), (4) and (5) as theorems about that `Scoring`, each stated in the post's own terms
(`S`, `N`, `theorem1`). State (3) with the violation counts explicit. Do not put into the
structure anything a theorem is then said to prove.

### 2.2 The sound signal

Claim (2), from `deferring_identity`: for a finite space, the adviser's information `k`, her
verdict `V` and her true utility `U`,
`E[(V − U)²] ≤ E[(E[U | k] − U)²] + E[(V − E[U | k, V])²]`, with equality characterised if
it is cheap; and the corollary at zero miscalibration. Then tie it to §2.1: a second
structure, or an extension of the first, in which *sound* is defined from a finite space as
that miscalibration being at most a bound, and a theorem giving the bound on what deferring
costs on a history satisfying it. If `guarantee` composes with this into a bound on what she
attains, state and prove that; if it does not compose as stated, say exactly which
hypothesis is missing.

### 2.3 Line 3

A definition over a finite nonempty type of policies with: the policy followed and the
baseline; for each policy, state of a finite space and index (a time and a future), her
later rating; a tolerance `δ ≥ 0`; her informed rating of each policy. *Within `δ` of the
policy followed*; *changes her no more than the policy followed* (every later rating lies
between the baseline's and the followed policy's, within `δ`); line 3 as the best rating in
the second class less the best in the first. Then claim (6): nonnegative; zero when the
policy followed is the baseline; at least the best rating among policies within `δ` of the
baseline less the best among those within `δ` of the policy followed. One instance in which
an unwelcome change with a separable welcome one has line 3 positive while that older form
is negative. Connect to §2.1 only by stating which field of the structure this would fill.

### 2.4 What does not go through

`account/BRIDGE_LEAN.md` (name provisional): each declaration with its statement in words
and what it does and does not say; every place where §1's wording had to be changed to
state it, with the change; and for each of these, whether it can be stated with what exists
and what is missing: that worsening her options lowers `V`; that the authority module
covers control of her act between options she rates the same; that the post's
unbiasedness-from-feedback hypothesis holds when the self who gives feedback differs from
the self who scores; how the history-level gate here relates to the segment gate of
`Legitimacy.lean`.

### 2.5 The outside check

One run through `codex`, read-only (`codex exec` needs `< /dev/null`), given §1, the new
Lean file and `BRIDGE_LEAN.md`: for each of claims (1)–(6), whether the Lean statement says
what the claim says, is weaker, or is true only because a hypothesis or a structure field
assumes it; any theorem whose hypotheses are jointly unsatisfiable or satisfied only
trivially; and the strongest reason the join would not give the post's guarantees their
intended meaning. Commit the reply verbatim as `REVIEW-astra-followup-12.md` and record a
disposition for each point. Fix what it finds that is a defect in a statement.

## 3. The prompt author's predictions

- §2.1: claims (1), (3), (4), (5) are each a few lines; the reviewer says (4) and (5) are
  true by construction and carry no content beyond the definition, which is correct and is
  the point of writing them down.
- §2.2: the inequality follows from `deferring_identity` in under twenty lines; `guarantee`
  does not compose with it without a hypothesis relating the adviser's information to her
  observations.
- §2.3: all of claim (6) holds; the instance exists.
- §2.4: none of the four can be stated as a theorem with what exists.

## 4. Done, fixed in advance

**Done** when: the file builds through `safe-lake.sh`; `tests/audit_axioms.py` passes with
every result on `[propext, Classical.choice, Quot.sound]` or fewer; every theorem has its
witness; claims (1)–(6) each have a declaration the reviewer judges to say what the claim
says or the report says plainly in what respect it is weaker; and `BRIDGE_LEAN.md` answers
§2.4.

**Not done**, and reported as such: any claim left without a declaration, with the reason;
any statement the reviewer judges true only by assumption that §1 presents as proved.

## 5. Report, queue

**Report.** A section **Twelfth follow-up** (with the date) appended to
`prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md`, with an attribution row
(prompt-author model: Claude Fable 5.2 (Anthropic); executor: self-identify). Short: the
declarations, each in a line; which claims are by definition, which proved, which weaker
than §1; §2.4's four answers; the reviewer's points and dispositions; the predictions
against the outcome; deviations; what was not shown.

**`DECISIONS.md`.** Record as dated entries: the maintainer's position that benevolent
manipulation voids; his position that no condition is needed on near ties; the gate of §1
as the prompt author's proposal adopted for this formalisation and not a ruling. Enter in
*Awaiting the author*, with what it turns on: whether a welcome change she did not ask
for, larger than the tolerance, must wait for her request (it decides whether the post's
feedback hypothesis can hold on every legitimate history). Keep the other queue entries,
each with a line from this pass, and take out any this pass answers.

**Lean results.** Handle them as the eighth and ninth follow-ups handled theirs
(`account/LEAN.md`): listed, kernel-checked, unregistered, with registration left to the
maintainer in the queue entry that already stands.

**Concept map and items.** Revise the concepts' blurbs where this pass changes what they
say, and add a concept only for a notion this pass leaves standing. Items 136–138 are
revised to say what this pass leaves of them.

**The pull request's description** leads with this pass, the earlier ones reduced. The
round's record in `state/rounds.json` and `PROVENANCE.md` are updated as the gates
require. Every commit is signed off and carries `Model:` for the executor and
`Prompt-author-model: Claude Fable 5.2 (Anthropic)`, and no other attribution line. Do not
add a handle to `graph/policy.yaml`. Anything reserved to the maintainer is listed under
Outstanding maintainer actions and in the queue.

New names introduced (all provisional): the new Lean file and its declarations, as the
executor names them; `account/BRIDGE_LEAN.md`.
