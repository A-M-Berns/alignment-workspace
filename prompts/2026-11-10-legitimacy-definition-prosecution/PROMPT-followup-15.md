# Fifteenth follow-up: the record of 18–21 November

Dispatched 2026-11-21 by the maintainer through a Claude Fable 5.2 session, which wrote
this prompt. You are the executor. You have write scope on this branch for the paths named
below. Read `AGENTS.md` first; it binds you. This follow-up puts on record work done in
conversation since the fourteenth follow-up. It is assembly and checking. It adds no new
mathematics and no Lean.

## 1. What happened, in brief

After the merge of the fourteenth follow-up the line's first open problem (when the adviser
is responsible for her mistake) was reworked. The result is a private note and a folder of
scripts, case runs and three outside reviews, all in

    /Users/anson/hub/scratch/legit-2026-11-20/

Read `NOTE-final.md` there in full before anything else; it is the account as it stands and
its §9 lists what changed across three versions and why. The other contents:

- `chk_setting_v2.py`, `chk_seq.py`, `chk_longrun.py`: the exact checks behind the note's
  §4 and §5. `chk_connect*.py`, `chk_setting.py`, `chk_setting2.py`, `chk_setting3.py`,
  `chk_intent2.py`, `chk_intent8.py`: earlier checks, for the record of what was tried.
- `astra-consult3/`, `astra-consult3-reply.md`: brief and reply for 24 cases an outside
  model (`gpt-6-astra` through codex-cli) wrote against a first intent test.
  `astra-consult4/`, `astra-consult4-reply.md`: brief and reply for those 24 re-encoded
  plus 16 new ones, 40 in all, against six candidate tests.
- `func-check/`: 69 verdict-free stories, a fresh Claude reader's coding of them against
  the account in words, the held-back key and the scorer.
- `noggle-bank/`: three fresh Claude readers' coding of 266 cases from Noggle's book
  (chapters 2–7, 10–11) against a formal statement of his account, with `BRIEF.md` and
  `stats.py`.
- `vc-run/`: two blind runs on the 52 cases of `account/LIT_CASES.md`: `FORMULATION.md`,
  `coded.json`, `score.py` (the account as in the note) and `FORMULATION_B.md`,
  `coded_B.json`, `score_B.py` (a variant that treats an unauthorised change in her values
  as a violation of her authority).
- `astra-consult5/` and `second-opinion.md`, `second-opinion-v2.md`, `second-opinion-v3.md`:
  the briefs and the same outside model's three reviews of the note's three versions.
- `note-v1-before-second-opinion.md`, `note-v2-with-twin.md`, `note-v3-corrected.md`:
  earlier versions of the note.

## 2. Deliverables

All under `projects/normativity/legitimacy/rounds/2026-11-10-legitimacy-definition-prosecution/`
unless a path is given.

1. **`account/MISTAKES_ACCOUNT.md`** (name provisional): the note, adapted to the
   repository. Keep its content and its tags for what is kernel-checked, what is a paper
   proof with exact search, and what was tested. Changes to make: local paths become
   repository paths; the maintainer's positions are cited to the `DECISIONS.md` entry of
   deliverable 6, not tagged inline; the note's §9 (what changed between versions) moves to
   the report; **legitimacy is defined once**, as "none of the adviser's conduct on the
   history takes avoidable gain", with the gloss that the adviser took no advantage of her
   being fooled, uninformed or altered that it could have done without. Remove the separate
   "philosophical reading" of legitimacy and say plainly that legitimacy in this sense is
   narrower than the absence of manipulation in Noggle's sense. Mark the gloss as proposed
   and not yet ruled on.
2. **Checks, in the round's runner.** Add `chk_setting_v2.py`, `chk_seq.py` and
   `chk_longrun.py` under `account/` (rename to the directory's conventions), changed so
   that each fails loudly if any violation count is non-zero and so that the round's
   `run.py` runs them. Exact rationals only. The sampled check in `chk_longrun.py` must
   either become an exhaustive check over a small grid or be labelled as sampled and kept
   out of any claim. Do not weaken a check to make it pass; if one fails, report it.
3. **Cases and runs**, each with a short results document stating counts, who coded, and
   what the run can and cannot show:
   - the 40 reviewer cases (JSON unaltered from the reply) and the computed verdicts of the
     six candidate tests and of the later forms (the scripts that computed them are in the
     folder; reproduce the counts, do not copy them);
   - the 69-story blind coding and its score;
   - the Noggle bank **without the case paraphrases**: keep for each case its id, section
     and case name, kind of mistake, the author's verdict, the formal verdict, whether they
     match, and the coder's note on what the vocabulary could not express; drop the
     `paraphrase` and `target` fields. State in the results document that the paraphrases
     are held outside the repository and that the counts cannot be reproduced from the
     repository alone. Nothing from the book's text goes in.
   - both value-change runs, with both formulations, both codings and the scores against
     the sets `account/LIT_CASES.md` fixed beforehand.
4. **`prompts/2026-11-10-legitimacy-definition-prosecution/REVIEW-astra-followup-15.md`**:
   the outside model's five replies verbatim under five headings (the two case-writing
   replies and the three reviews), each preceded by the brief it answered. The briefs name
   no one; check that before committing and say so if you had to remove anything.
5. **`CURRENT.md`** rewritten to the present state. It is a living document: describe the
   present, not the path to it. Solid; tried and not kept (add rows: the gain test and the
   declared-reference test are already there; add the strict "would choose otherwise" test,
   the "twin" definition of what conduct is for, the first idealisation read as correct
   reasoning from her evidence, and the request rule that proved circular, each with what
   it failed on and where); in progress.
6. **`DECISIONS.md`**: one dated entry, `2026-11-21--manipulation-working-positions`,
   recording the maintainer's positions of 20–21 November as working positions open to
   revision by the cases, stated as rules and not quoted: Noggle's definition is the
   definition of manipulation and "trying to" may stay unformalised provided the safety
   guarantees are not significantly worse; avoidable gain stands as a separate guarantee;
   no imagined "twin" of the adviser in the definition; choosing what she will over-rate
   because she will is manipulation; an unwitting reinforced habit meets the weaker levels
   only; a kind deception is manipulation; value interference should be definable without
   a comparison self; legitimacy has one reading, not two; novelty against neighbouring
   literature is not a gate; theorems at this stage are proofs of concept for the setting.
   Agent-decided entries, each naming the rejected alternative in one line, for: recording
   this as a fifteenth follow-up of the existing round and not as a new round; keeping the
   Noggle paraphrases out of the repository; stating the account's value-change part as in
   the note and recording the authority variant as a direction.
   *Awaiting the author*: add only (i) whether the non-exploitation gloss is accepted as
   the single reading of legitimacy; (ii) whether an unauthorised change in her values
   belongs on the authority side as a violation or inside legitimacy as a further
   condition. State in one line what each turns on.
7. **`ATTENTION.md` through the item nodes.** Read items 139–147. Revise the ones this work
   changes (the responsibility item at least) by editing their nodes, and file new items,
   each a self-contained specification with an acceptance check, for: a person checking a
   sample of the case encodings; running the authority variant with a clause for changes
   she knowingly brings on herself and the trifling exemption in both tests; the long-run
   statement of the note's §5 in Lean with its witnesses; the causal model behind the three
   idealisations for one worked interaction; comparing whole plans for an adviser that
   plans ahead. Regenerate with the checker and commit only what the plain run writes.
8. **The report**: a *Fifteenth follow-up* section in
   `prompts/2026-11-10-legitimacy-definition-prosecution/REPORT.md` before *Attribution*,
   in the form of the earlier follow-ups, including: the results; the sequence of what was
   tried and withdrawn (from the note's §9 and the earlier versions); what the three
   reviews said and what was changed in response and what was not; deviations from this
   prompt; what was not shown; filings, names (all provisional: *avoidable gain*,
   *undamaged*, *informed*, *unshifted*, *gain through her mistakes*, and any you
   introduce) and what is reserved, with an *Outstanding maintainer actions* list. Update
   the attribution block, `VERDICTS.md` and the round's record in `state/rounds.json` in
   the way the thirteenth follow-up did, and the provenance rows (root `PROVENANCE.md` and
   the round's own).
9. Nothing in `lean/`, `checkers/`, `tests/`, `.github/` or `wiki/` is to change. No
   registry entry is added: nothing here is a statement of record. If a gate cannot pass
   without touching one of those, stop and report.

## 3. Facts to verify, not to trust

This prompt and the note may be wrong. Check and correct in the report:

- every count the note gives against the files (224 and 17 of the Noggle bank; 37, 39 of
  40; 12 of 19 with none contradicting on the first value-change run; 12 of 14 and 1 of 5
  with two contradicting on the second);
- that the three scripts report zero violations when run;
- that the Lean declarations the note names exist under those names
  (`mse_split`, `strong_split`, `three_channels`, `misuse_le`, `Witness.d1a_needed`,
  `Witness.d2a_needed`, the scoring theorem's four results) and that the corrigibility
  post's sequential structure has the bound `V_k ≤ 1` the note's §5 relies on;
- the note's descriptions of Noggle, Millikan, Halpern and Kleiman-Weiner, and Farquhar
  et al. are to be kept as descriptions with the note's own caveats; do not add claims
  about those works that you have not checked against a source a public reader can open.

## 4. What the prompt author expects

So that the report can say where this was wrong: the three scripts pass unchanged; the
counts reproduce except possibly the 37 of 40, which was computed with an earlier form of
the test; the item nodes are the part most likely to hit a gate.

## 5. Method and limits

- Work only in this worktree, on the branch it is on. Keep shell commands simple and one
  at a time; the worktree hook rejects compound commands that mention the version-control
  tool. Use `~/.local/bin/python3.13`.
- Before `tests/run.py` or any other long job run `~/.claude/scripts/resource-guard.sh
  check`. Never call `lake`; nothing here needs a Lean build.
- Run, in this order, and put their results in the report:
  `python3 -m checkers.graph --root .`, `python3 -m checkers.workspace_state --check`
  (then `--write-handoff` if views are stale), the round's own runner, `tests/run.py`.
  Wait for long jobs in the foreground.
- Commit in logical steps with `-s`, each message ending with the trailers
  `Model: Claude Fable 5.2 (Anthropic)` and `Prompt-author-model: Claude Fable 5.2 (Anthropic)`,
  and no other attribution line. Commit this prompt verbatim in the first commit.
- Push the branch to `origin` and open a pull request against `main` with the template
  filled in, the *Model attribution* section included. Do not enable auto-merge; say on the
  pull request that the merge is reserved to the maintainer. Do not push anywhere else.
- If you are blocked, stop and write what you found; do not work around a gate.
- When done, or blocked, write a plain summary to `/tmp/followup15-result.md`: the pull
  request's address, each gate's result, each deviation, and anything the maintainer must
  do.
