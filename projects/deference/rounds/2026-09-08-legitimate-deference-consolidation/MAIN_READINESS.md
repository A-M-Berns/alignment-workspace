# Main readiness

**Status:** `ci-only`.  The file-by-file record of what this landing changes, so a reader
of `main` can tell the corrected state from the two rounds' original claims.

## 1. Landing strategy

The stack `#92 → #93` sits directly on `main` (`5d2347e`; `main` did not move).  This
branch, `land/2026-09-08-legitimate-deference`, is the top of #93 plus the consolidation
commits.  The dispatched research commits are preserved (no squash on the branch); the
landing pull request targets `main` and carries the whole stack, so `main` never holds
the false completion interval or the `AnswerOK` placement.  #92 and #93 stay open for the
maintainer to close as superseded.  **Nothing is merged by this round.**

A repository-state note: the shared `.git/shallow` file marked five commits, including
the stack's base, as roots, which broke every local `merge-base` (three-dot diffs, the
`round_records` gate).  All objects were present; `git fetch --unshallow origin` cleared
the marks and fetched nothing.  Recorded here because the next session that sees a
"no merge base" error should know the cause.

## 2. Repairs to the open rounds, in place

| file | defect | repair |
|---|---|---|
| `2026-09-07-authority-activated-value/AUTHORITY_ACTIVATED_VALUE.md` §3 | `Bind(V)` placed inside `Protocol.AnswerOK`, which is evaluated at the strict prefix and takes no event | §3 rewritten to the derived predicate `EvalAnswered` over receipt + payload; status note at top |
| same, §1 | total `V` | partial object noted; completion invariance |
| same, §4 | the no-preview receipt as the scope condition | selection-induced channel blindness, no-preview one implementation; leakage named |
| same, §8 | end-to-end statement ends at completion regret | primary conclusion `R_auth ≤ ε/(1−η)` added; transfer two-sided |
| `INTERFACE_WITH_LEGITIMACY.md` §1 row "adequacy", §5 | same `AnswerOK` placement; "occurrence-local legitimacy" naming scope-local openness over global Integrity | corrected row; note that `LocalLegit` is the occurrence-local object |
| `LI_DEFERENCE_COMPOSITION.md` §3, §8 | "the scope condition is the no-preview receipt" | heading and note corrected |
| `README.md`, `state/rounds.json` (#92 verdict) | "no-preview receipt as its admissible-domain condition" | "selection-induced channel blindness as its admissible-domain condition" |
| `REPORT.md` (#92) | — | "Corrections applied by the consolidation round" section |
| `2026-09-07-reason-mediated-authorship/PARTIAL_VALUE_AND_REGRET.md` §3, §4 | `R_V̄ ∈ [R_U, R_U + D·η]` for every completion — **false** | two-sided theorem, lower sharpness, correction note; §5b adds the authoritative-regret theorem |
| `REPORT.md` (#93) verdict, C3, "survived" | same false interval | corrected in place; corrections section |
| `README.md`, `state/rounds.json` (#93 verdict) | "exact completion interval" | "two-sided completion bound … both constants sharp" |
| `COUNTERMODELS.md` (#93) I | "both ends attained" read as a general interval | qualified to the world-independent strategy |
| `AUTHORSHIP.md` §2.1, §4, §6 | session-local scope; selection blindness as a primitive | issuance-rooted frame and trace; instance of channel blindness |
| `tests/test_countermodels.py` (#93) `test_regret_interval` | asserted the false lower bound (true only for its constant strategy) | asserts the two-sided bound; comment |
| `DECISIONS.md` 2026-09-07 authorship entry | recorded the false interval | sentence corrected with a pointer to the 2026-09-08 entry |
| `lean/…/PartialActivatedValue.lean` | header claimed the interval; `availability_transfer_completion` docstring implied it | header rewritten; `regretV_sub_regretU_abs_le`, `SharpLower`, `voidMass`, `mass_eq`, `regretAuth_le_div`, `regretAuth_asymptotic`, `followed_excess_bounds`, `sup'_add_bounds` added |
| `lean/…/ReasonMediatedAuthorship.lean` | header session-local; `SelectionBlind` a primitive | header issuance-rooted; `selPairs`, `selectionBlind_iff_blind`, `selectionBlind_of_blind`; witnesses `earlyWrite`, `diachronic_learning`, `transient` |

Nothing in the two rounds' Lean was weakened; every prior declaration still builds with
its statement unchanged except the docstrings named above.

## 3. New in this round

- `lean/Workspace/Deference/Contrib/ReasonCoverage.lean` — barrier, bridge, coverage
  soundness, void-mass bound, RO route restatement, witnesses G–L.
- This round's documents and 16 exact fixtures.

## 4. Wiki

- `wiki/Deference.md` — the #92-only paragraph replaced by the mature stack; the
  status split into the paused older target (endpoint preservation, items 14/28/34,
  the two awaiting decisions, unchanged) and the active legitimate-deference consumer;
  links pinned to the landing commit.
- `wiki/Legitimacy.md` — one sentence: the consumer reads legitimacy through an
  occurrence-local projection, an application may still require the global segment as
  an evidentiary policy.  Legitimate Evolution's definition untouched.
- `wiki/Openness-Coverage-and-Non-Capture.md` — one paragraph: RO supplies route
  availability, not exercise or consideration; the bridge and barrier live at the
  consumer level.  RO's definition untouched.
- `wiki/Roadmap.md` — the deference heading distinguishes the paused older target from
  the active consumer; the resume items unchanged.
- `Glossary`, normativity pages: untouched.

## 5. Priorities, decisions, state

- `PRIORITIES.md` item 87 rewritten as the single seven-clause realization bill; no
  new items.
- `DECISIONS.md`: one 2026-09-08 agent-decided entry; the 2026-09-07 authorship entry's
  interval sentence corrected with a pointer.
- `state/rounds.json`: the two verdict strings amended to match the corrected READMEs;
  one record for this round; `state/views/**` regenerated.
- `PROVENANCE.md`: one row for this round naming every repaired file; round
  attribution row; Contrib table rows for the new and extended Lean files.

## 6. Claim registration

None.  No filed item is answered — item 87 is the open remainder and every Lean
declaration in the stack is either a definition, a finite identity, or a witness; none
is a realization.  The demand rule is not met, and nothing is registered.

## 7. Verification

- `python3 tests/run.py` at the root: all projects green, including the three deference
  rounds of the stack.
- `lake build` of the whole library: succeeds; every `#print axioms` line in the five
  Lean files of the stack reports at most `propext`, `Classical.choice`, `Quot.sound`.
- `python3 -m checkers.workspace_state --check`: valid after `--write-handoff`.
- `tests/name_lint.py`, `tests/dead_pointers.py`, `tests/untracked_pointers.py`,
  `tests/round_records.py` (against `origin/main`): clean.

## 8. Safe to merge?

**Yes, as one landing.**  The branch carries the two rounds with their known defects
repaired, the consolidation round, the wiki in the corrected state, item 87 as the
honest remainder, and no registered claim.  Merging #92 or #93 alone would put a known
false statement on `main`; merging this branch does not.  The maintainer decides the
merge.
