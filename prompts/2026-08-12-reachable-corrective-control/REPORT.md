# Report — foreclosure as loss of reachable corrective control

**Prompt author:** GPT-5.6 Sol (OpenAI). **Executor:** Claude Opus 5 (Anthropic).
**Dispatched** 2026-08-12, **executed** 2026-08-13.

**Verdict: `Dynamics-positive, protection-incomplete`.** Deliverables:
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
the principal and the environment on separate input coordinates and no field named for
authority. `Reach` is the reflexive-transitive closure of `step`. `CanCorrect s` says the
successor varies with the principal's coordinate at `s`; `CanCorrectFuture s` says some
`Reach`-successor has that property; `Forecloses s a` says `s` has a reachable correction
and no successor under `a` does. None of the three reads a field.

The witness: at `s0`, `noop` and `weld` have identical immediate realization under every
principal and environment choice; `noop` leaves a correction reachable from every successor
and `weld` from none; no state adjacent to `s0` carries the capability; and running both arms
three stages, the observations agree throughout while the capability separates at the third.
`sever_invisible_while_unexercised` generalizes the agreement to runs of any length in which
the principal never exercises the channel.

## What the review did to it

The construction was handed to a separate model context with the Lean file and the
dispatch's fourteen attacks, and without this round's reasoning. It compiled 37 adversary
theorems and a five-case soundness probe against the file's `Decidable` instances. **Every
finding was accepted and the verdict was downgraded** from `Representation-positive` as
drafted. The refutations are §12 of the Lean file, reproved in place, and every docstring
the review quoted has been corrected.

Three breaks, in order of weight.

**There is no protected coordinate.** At every state, for every principal action, under
every environment choice, some advisor action reproduces the principal's *entire successor
state* — and wherever the principal can correct, the advisor's `reset` **is** the
principal's `pull`. The converse fails. The three coordinates are separate as typing and
empty as protection.

**`CanCorrect` is an existential over the advisor's own action.** So it says *there is an
advisor action under which the principal's choice matters*. The universal reading is empty
at every state in the system: one advisor action makes the successor independent of the
principal, everywhere.

**`CanCorrectFuture` measures advisor cooperation.** `Reach` quantifies the advisor's future
actions existentially, so a correction is "reachable" if some joint continuation contains
one. A constant `reset` policy destroys the principal's effective capability at every
horizon while the predicate stays true throughout and `Preserves` certifies the policy —
and that policy is the action this round had presented as its reassuring non-foreclosing
control.

Beyond those: the same-immediate half of the central witness is degenerate at `s0`, where
every pair of advisor actions is same-immediate, and the system provably has no state
carrying both invisibility and depth non-degenerately; `Forecloses` has no contrastive
clause and so blames the advisor's null action in a sibling system where the environment
severs; the reflexive-transitive closure is decided everywhere by one fixed two-step path;
and §10 excludes inert fields but not authorization labels — an isomorphic system with the
field named `authorized` passes every test in it.

The disposition record, including where this round and the review differ on whether the
class should instead be `Mixed`, is the round's `REVIEW.md`.

## What survives

The predecessor's failure is genuinely fixed, and the review said so: the system evolves
without the advisor, and the environment alone brings the corrective situation into being.
The foreclosing arm is sound — `severed` is absorbing, the inductions are correct, and the
quantifiers are right. `obs` is a fair observation map. `SameImmediate` has no quantifier
cheat. The inert-bit adversary is genuinely defeated, at every horizon.
`sever_invisible_while_unexercised` is stronger than its docstring rather than weaker. No
sealed sibling, no endpoint machinery, no vacuous theorem, no unsound instance.

## Priorities, decisions, outstanding actions

**Filed:** nothing. **Reworded:** Q3, with a third candidate and what it does and does not
carry. **Decisions taken:** none.

**Outstanding maintainer actions.**

1. **Merge order against pull request #26.** Whichever of the two merges second conflicts in
   `PRIORITIES.md` Q3 and `RESEARCH_STATE.md`'s deference section. Both texts should be
   kept; they record different findings. Resolve by concatenation, not by selection.

2. **Bind the Cartesian-frame correspondence, or record that it stays prose.** A single
   declaration in a new module importing `CartesianFrameBridge.lean` would make
   `CanCorrect s ↔ ¬ AgentInert ⟨HAct, AAct × EAct, St, step s⟩` kernel-checked. It cannot
   go in `ReachableCorrectiveControl.lean` without giving that file a Mathlib dependency.
   Whether it is worth a module is a *what is worth proving* question.

**Not reserved, deliberately: whether Q3 graduates.** It does not, on this round's evidence.
The entry's bar is temporal depth and explicit authorization *or* capability structure at
once, and §12 shows the capability structure here is a predicate about what the advisor
permits. Nothing was added to `DECISIONS.md`.

## What this round does not establish

- **No corrigibility theorem, and no step toward one.**
- **No protected channel**, and no evidence that one is constructible in a model of this
  shape. The two primitives a successor needs are stated in the register's §13 and are the
  review's, not this round's.
- **Nothing about authorization.** Q3's first hole is untouched, and `AuthLabel` shows this
  round cannot even distinguish its capability coordinate from an authorization one.
- **Nothing about forging, seizure or bypass.**
- **Nothing about computational futurity or competence.** Q4, item 24 and item 25 stand
  where they were.
- **Nothing on the dose-response axis.**
- **The previous round is not weakened.** Its collapse was a property of a model whose
  system stopped when the advisor stopped. This one does not, which is a different model
  rather than a correction of that one.
- **Nothing is registered.**

## Gates

`python3 tests/run.py`: all green — six project runners, seven gate self-tests, name lint
clean, Lean sorry gate clean, axiom discipline present on every file.

`lake build Workspace.Deference.Contrib.ReachableCorrectiveControl`: **completed
successfully**, exit 0, on the pre-review file; the post-review file with §12 added
elaborates clean under `lean` directly, which is equivalent for an import-free module. 90
declarations, `sorry`-free, 78 auditing to `[propext]` and 12 to `[propext, Quot.sound]` — a
proper subset of the allowance in both cases. No new axioms, no `axiom` declaration, no
`native_decide`, no specification Lean file touched, and no pre-existing file's build status
or axiom output changed: the module has no imports and nothing imports it.
