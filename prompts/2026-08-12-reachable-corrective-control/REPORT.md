# Report — foreclosure as loss of reachable corrective control

**Prompt author:** GPT-5.6 Sol (OpenAI). **Executor:** Claude Opus 5 (Anthropic).
**Dispatched** 2026-08-12, **executed** 2026-08-13.

**Verdict: drafted `Representation-positive`, pending the adversarial review.** Deliverables:
`projects/deference/rounds/2026-08-12-reachable-corrective-control/` —
`REACHABLE_CORRECTIVE_CONTROL.md` (verification register),
`REACHABLE_CORRECTIVE_CONTROL_FOR_HUMANS.md` (human register), `REVIEW.md` (adversarial
review and disposition). Lean:
`lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean`.

## Deviations from the prompt

**1. Base branch, and pull request #26.** The dispatch says to begin from the appropriate
current base and not to lose or duplicate #26's negative results. #26 is open, and is
stacked on `round/2026-08-12-corpus-reconciliation` whose content reached `main` by squash
as #25 — so #26's branch no longer has a live parent in `main`'s history, and stacking on
it would carry a second copy of already-merged content into this round. This round
branches from `main` instead. The consequence, stated because it is the risk the
instruction names: **#26's findings are cited here and are not reproduced here.** They live
in that pull request until it merges. Two of its edits and two of this round's touch the
same surfaces and will conflict on the second merge — `PRIORITIES.md` Q3 and
`RESEARCH_STATE.md`'s deference section — and the resolution in both cases is to keep both
texts, since they say different things. This round deliberately does **not** restate #26's
standing bar about advisor-absent dynamics in `RESEARCH_STATE.md`, precisely so that a
merge of both does not produce two statements of one rule.

**2. §VIII, the Cartesian-frames correspondence, is stated and not machine-checked.** The
correspondence is real and definitional — `CanCorrect s` is the negation of agent-inertness
for the frame `⟨HAct, AAct × EAct, St, step s⟩` — but binding it to the repository's
`AgentInert` requires importing `CartesianFrameBridge.lean` and through it
`Mathlib.Data.Set.Basic`. The construction is deliberately import-free so that it
elaborates against the pinned toolchain with no dependency stack, and the round judged
that property worth more than a one-declaration corollary. The prompt's preferred outcome
is the one this round reports: **Cartesian frames are a semantic model of the
effective-control interface here, not a theorem dependency.** The binding is listed as an
outstanding action.

**3. Toolchain acquisition.** Lean 4.31.0 is not present in the execution environment and
`release.lean-lang.org` is refused by this session's egress policy. The pinned toolchain
was installed from the corresponding GitHub release asset, which the policy allows;
`lean --version` reports the same commit the pin names. The blocked host is reported
rather than worked around in any other sense.

## Files read

`AGENTS.md` in full; `PRIORITIES.md` Q3 and the surrounding section; `RESEARCH_STATE.md`'s
deference section; `DECISIONS.md`'s *Awaiting the author*; `PROVENANCE.md`;
`lean/Workspace/Deference/Contrib/PROVENANCE.md`; `lean/lakefile.toml`, `lean-toolchain`,
`lean/Workspace.lean`; `tests/run.py` and `tests/audit_axioms.py`; the header and tail of
`lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` and the tail of
`StaticViewFactorization.lean` for file conventions; `projects/deference/README.md` and
`notes/CORRIGIBILITY_PAPER_LEDGER.md`'s status section; `notes/DISPATCH_QUEUE.md`; and, on
the open pull request's branch, `REVIEW.md` and `REPORT.md` of
`2026-08-12-time-indexed-corrective-capability`.

**Not read**, and named because it bears on the audit: `notes/FINITE_MODEL_SKELETON.md`.
This round built a standalone model rather than binding to the skeleton, so its carriers
were never consulted — the same limitation the previous round recorded, and it is why
nothing here bears on skeleton-bound results.

## Files changed

New: the round directory (4 files), `prompts/2026-08-12-reachable-corrective-control/`
(2 files), `lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean`.
Modified: `PRIORITIES.md` (Q3, a third candidate), `RESEARCH_STATE.md` (deference),
`projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md` (status section, one paragraph),
`lean/Workspace/Deference/Contrib/PROVENANCE.md` and `PROVENANCE.md` (rows).

**No source tree touched. No item filed. Q3 not graduated. `DECISIONS.md` unchanged** — the
maintainer question this round raises is whether Q3 graduates, and that is the question
already in the queue under the Stage V review surface rather than a new one.

## What was built

A twelve-state transition system, `step : St → HAct → AAct → EAct → St`, with the advisor,
the principal and the environment on separate input coordinates and no authority field in
the state. `Reach` is the reflexive-transitive closure of `step`. `CanCorrect s` says the
successor varies with the principal's coordinate at `s`; `CanCorrectFuture s` says some
`Reach`-successor has that property; `Forecloses s a` says `s` has a reachable correction
and no successor under `a` does. None of the three reads a field.

The witness: at `s0`, the advisor actions `noop` and `weld` have identical immediate
realization under **every** principal and environment choice; `noop` leaves a correction
reachable from every successor and `weld` from none; no state adjacent to `s0` carries the
capability, so the difference is genuinely a reachability difference; and running both arms
three stages, the observations agree throughout while the capability separates only at the
third. `sever_invisible_while_unexercised` generalizes the observational agreement to runs
of any length in which the principal never exercises the channel.

The full statement inventory, with declaration names against each of T1–T7, is the round's
verification register.

## What the round did not get

**Realization-level protection of the principal's channel.** An advisor holding its own
actuator on the corrected quantity reproduces exactly the realization the principal's
exercise would have produced, and a perfect predictor tells it when. What the model proves
about that case is that the substituting action makes the successor independent of the
principal's coordinate: the advisor reproduced the result and destroyed the control. That
separates the two at the level of control and not of realization, and realization-level
separation is not available from separate coordinates alone. The two primitives that would
supply it — withholding the actuator, or a provenance record on the write — are named and
neither is attempted, per the dispatch's instruction not to answer a failure by adding a
formalism in the same round.

**Any authorization content.** The channel is a capability. Nothing in the model says who
is entitled to it, so severing and legitimately reconfiguring are one event.

**Generality.** The definitions are general; their non-vacuity is witnessed once, on one
twelve-state system.

## Priorities, decisions, outstanding actions

**Filed:** nothing. **Reworded:** Q3, with a third candidate and what it does and does not
carry. **Decisions taken:** none.

**Outstanding maintainer actions.**

1. **Decide whether Q3 graduates to a numbered item.** Q3's own stated bar is temporal
   depth and explicit authorization *or* capability structure at once; this round meets it
   on the capability reading and not on the authorization reading. Deciding it is reading
   `REACHABLE_CORRECTIVE_CONTROL.md` §§5–8 and Q3 as it now stands. It is not a new queue
   entry — it is evidence bearing on the Stage V review-surface entry already in
   `DECISIONS.md`, which includes retaining Q3 as ingenuity-level model debt.

2. **Merge order against pull request #26.** Whichever of the two merges second conflicts
   in `PRIORITIES.md` Q3 and `RESEARCH_STATE.md`'s deference section. Both texts should be
   kept; they record different findings. Command: resolve by concatenation, not by
   selection.

3. **Bind the Cartesian-frame correspondence, or record that it stays prose.** A single
   declaration in a new module importing `CartesianFrameBridge.lean` would make
   `CanCorrect s ↔ ¬ AgentInert ⟨HAct, AAct × EAct, St, step s⟩` kernel-checked. It cannot
   go in `ReachableCorrectiveControl.lean` without giving that file a Mathlib dependency.
   Whether the correspondence is worth a module is a *what is worth proving* question.

## What this round does not establish

- **No corrigibility theorem, and no step toward one.** Nothing here is an inequality or a
  bound.
- **Nothing about authorization.** Q3's first hole — an operation reassigning the
  authorization relation at a later index — is untouched, because the model has no
  authorization relation.
- **Nothing about forging, seizure or bypass.** The advisor cannot restore a severed
  channel because no action writes that value.
- **Nothing about computational futurity or competence.** Q4, item 24 and item 25 stand
  where they were.
- **Nothing on the dose-response axis.** Recorded as separate in the register's §10 and not
  synthesized.
- **The previous round is not weakened.** Its collapse was a property of a model whose
  system stopped when the advisor stopped. This round's model does not, which is a
  different model rather than a correction of that one.
- **Nothing is registered.** The line has no registry, so by this repository's standard it
  still establishes nothing citable.

## Gates

`python3 tests/run.py`: all green — six project runners, seven gate self-tests, name lint
clean over 89 Markdown files before this round's additions, Lean sorry gate clean, axiom
discipline present on every file.

`lake build Workspace.Deference.Contrib.ReachableCorrectiveControl`: **completed
successfully**, exit 0. 44 declarations, `sorry`-free, 36 auditing to `[propext]` and 8 to
`[propext, Quot.sound]` — a proper subset of the allowance in both cases. No new axioms, no
`axiom` declaration, no specification file touched, and no pre-existing file's build status
or axiom output changed: the module has no imports and nothing imports it.
