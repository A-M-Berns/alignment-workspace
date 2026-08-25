# Report — Reflective Integrity Core v1.0

Attribution: prompt author unrecorded (authored outside this repository, in a
prior session); executor Claude Opus 5 (Anthropic); dispatched and executed
2026-08-24.

## Verdict

```text
FREEZE-READY
```

The specification lands at
`projects/normativity/legitimacy/rounds/2026-08-24-reflective-integrity-core/REFLECTIVE_INTEGRITY_CORE.md`
with a reference model and 93 finite-history tests beside it. No repair required
a new persistent store, a new conservation law, abandonment of derived custody,
or restructuring of the answerability DAG.

## What was repaired

`AUDIT.md` in the round directory carries the full table with sources,
validation and the architecture column. In summary: the parametric demand
interface gained `D1` (monotonicity under multiset and cited-digest extension)
and `D2` (disposition gating); the seed gained `Z3'` and `Z6`; the allocator
gained `F1`–`F3`; `WF` became an ordered conjunction with `effect(a)` defined at
`G4`; `G3` became inference-step licensing over `steps : Derivation → Finset
StandingId`; Due-Witness and the trichotomy are stated over `Roots_t`; transfer
wording is admissibility rather than acceptance; `StandingChanges` is defined
exactly and the cohort package is demoted to one retained derived lemma.

`Creditor.Prin`, `Grounded` and the second conjunct of the old `G4` are deleted,
each with the reason recorded in `AUDIT.md`.

## Reconstruction, and its limits

The red-team context holding the verbatim text of repairs R1–R5 was lost before
this round began. Their necessary consequences survive in the audit recap and
rerun quoted in `PROMPT.md`, and that text is what the repairs here are derived
from. R6, R7, R8 and R5's repair text survive verbatim; R1 is identified by the
recap as `D1`–`D2` plus `Z6`; `Z3'` and the freshness repair are inferred from
the rerun's dependence on them. **This round does not claim to have reproduced
R1–R5.** Where the original repairs differed in form, only their consequences
are preserved.

## Independent adversarial pass

Run after the repairs, against the repaired signature, over the seven targets
the dispatch named. Three further local defects were found and fixed, each
recorded as a reconstructed local audit repair with the original R-number
unavailable:

1. `Supersede` and `Transfer` could target standing outside `dom(Std_{<τ})`,
   where the interpreter's clauses read `pred` and `payload`. `G6` now requires
   domain membership.
2. `cited(ρ)` ranged over `ids(N_t)`, which contains responses as well as
   events, where `Digest` is defined only on events. The step condition now
   ranges over `ids(NormEvents_t)`.
3. Episode Uniqueness was stated for all `x`, where `status_t(x)` is undefined
   off `dom(Std_t)`. It is now quantified over `dom(Std_t)`.

None is architectural. No fourth defect was found, which is not a completeness
claim.

## Cohort package: demoted

`I_s^{A_s}` and `New_t^{A_s}` are defined exactly, and **Source Closure**
(`New_t^{A_s} = ∅`) is retained as a derived lemma in §33, because §17's uniform
creditor rule cites it as its reason. Clause (8) — the partition
`I_s = D_t ⊔ R_t` — is dropped from the main theorem: with the symbols defined,
it is excluded middle over a set that `AC(i)` already keeps fixed, and it adds
nothing to successor-root continuity and Due-Witness. The dispatch's own
instruction was to prefer the smaller theorem.

## Repository integration

Nothing was superseded, because nothing was there: the grep the dispatch
specified — mutable `custodian`, `SetCustodian`, `AmendProto`, a separate
mutable stance store, a global `ContinuityOK` invariant, "acceptance via
authorization", `DemandCode` without `D1`/`D2`, undefined cohort notation —
returns no hits anywhere in the tree. No earlier version of this specification
has ever been committed here, so the canonical document has exactly one home and
no duplicate. No unrelated research prose was touched.

The round sits above `2026-08-23-transition-certificates`, whose frozen
reason-state interface §7 and §14 of the specification consume, and whose
`FRONTIER_HANDOFF.md` states the `O_t` consumer contract that §35 answers from
the record side.

## Tests

`python3 tests/run.py` in the round directory: **93 tests, all passing.**
Repo-level `python3 tests/run.py`: results in the pull request.

The batteries are enumerated in the round's `README.md`. Two of them are
necessity witnesses rather than confirmations: the ungated-demand seed executes
the recap's one-object counterexample and asserts that Episode Uniqueness fails
before asserting that the repaired interface refuses that seed; and the
freshness battery replaces the allocator with one that drops the time component
and shows the collision reaching `EP`.

## Final cleanup pass

A second dispatch asked for typing and mechanization hygiene before the freeze,
and `AUDIT.md`'s *Final cleanup* table records it: the interpreter now takes an
explicit `ApplyCtx`, `freshCount` is separated from `freshIds`, §34 states the
strong recursion the fate block actually needs instead of claiming a static
order it does not have, the successor-debtor prose is stated by case, `P_0` is
an explicit seed parameter, and the demand checker is renamed to say what it
does. Nothing in it changed a store, a constructor, a conservation law, a
theorem's meaning or a custody semantic.

## Deviations

1. **`PROMPT.md` display-math delimiters.** The prompt as sent used bare
   `[ ... ]` around display equations; the committed copy uses `\[ ... \]`.
   Nothing else was altered, and no word of the text was changed. Recorded here
   because `AGENTS.md` §12 asks for the prompt verbatim.
2. **The attachments are not committed.** The prompt referred to a candidate
   specification supplied as an attachment. It arrived with passages dropped
   mid-line by the paste that delivered it, so committing it would put a
   corrupted document in the record under a name suggesting it is the source.
   `PROVENANCE.md` in the round directory says this. The surviving hostile audit
   is quoted in full inside `PROMPT.md` and so is in the record.
3. **No `DECISIONS.md` entry.** The round reserves nothing: the freeze verdict is
   the round's to take under the dispatch, and a merge is never a queue entry.

## What this does not establish

- Nothing is Lean-checked and no claim is registered. The epistemic status is
  the same as the rounds it builds on: research artifacts, `ci-only`.
- `src/ri_core.py` is a reference model. It decides the finite histories it is
  given; it does not prove the general statements. `D1` and `D2` are decided
  over supplied finite samples, not over all response multisets, so a demand
  passing `sampled_episode_demand_violations` is not thereby proved monotone or gated.
- The paper proofs in §§10, 13, 19–24 and 28 are derivations, not machine-checked
  proofs, and §29's induction is assembled from them.
- The reconstruction of R2–R4 is inference from the rerun's dependencies. The
  claim is that the repaired specification has the properties the surviving
  report requires, not that these are the repairs the red team wrote.
- §35 establishes write separation and the shape of `O_t`. It does not establish
  that the `N → O → K` compilation exists.

## Outstanding maintainer actions

None. Nothing is reserved.

## Structural defects found

Worktrees had accumulated on the maintainer's machine — twenty at the start of
this round, six of them on branches whose pull requests had merged. On the
maintainer's instruction those six were removed; `git worktree remove` refuses a
worktree holding uncommitted or unmerged work, and none did. Two were left: the
`cleanup-and-compress` worktree, whose pull request has merged but which is
`locked`, and the shared checkout itself, which sits on the merged branch
`round/2026-08-17-counterfactual-legitimacy`. Neither is this round's to change —
a lock is a deliberate in-use signal, and moving the shared checkout's branch is
the hazard the worktree discipline exists to avoid.

## New names introduced

All provisional, per `AGENTS.md` §6, and absent from `state/vocabulary.json`:
`D1` / monotonicity and `D2` / disposition gating as names for the episode-demand
assumptions; `Z3'` and `Z6` as seed-clause labels; `F1`–`F3` as allocator
assumption labels; `EpisodeDemandSample` and `sampled_episode_demand_violations` in the
reference model; **Reflective Integrity Core v1.0** as the document's name.
