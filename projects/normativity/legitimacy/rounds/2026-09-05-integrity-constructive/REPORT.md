# Report

INTEGRITY-ENTAILS-CONSERVATION-ONLY-WITH-CONTENT-CLAUSE — structural record integrity gives a unique token fate, while the minimal local content-conservation clause plus closure certificates yields three-fate answerability and composes over segments.

## Finding

`DefeatTrace` is the minimal existing structural substrate needed here. It proves an identity-level token trichotomy and supplies fresh ancestry, grounds, settlement availability, participants, and resolution kinds. A universal event datatype would add representation without strengthening the theorem.

Identity-level trichotomy is weaker than Diachronic Answerability. The same defeat-disciplined trace admits a faithful slice ledger and a hollow ledger. The latter loses a disposed token's semantic load while retaining its fresh successor and every other tested local clause. Thus structural Integrity alone admits the fourth content fate, erasure.

The minimal separating repair is `carry_complete`: a disposed parent's load is below the join of its fresh children's post-state loads. For a general conservation theorem it sits with identity framing, no old-slice accretion, exact answer and closure-receipt accumulation, and locality. Their iteration is `SliceLedger.Integrity`. This segment predicate concatenates and yields exact preservation of answered, closure-discharged, or carried-live load.

Settlement availability and normative closure are separately typed. `T.Settled n s` is authenticated input; `Closes n s q` is an internal judgment. `LocalConservation.closure_certificate` requires both before a settlement-tagged resolution feeds the terminal receipt ledger. The generic theorem assumes, rather than constructs, the rules, grounds, and licence supporting `Closes`.

Later rejection of a closure rationale is prospective. The settlement item, resolution token, and closure event remain immutable. A new reconsideration obligation cites the defeated closure; any renewed old load enters explicitly on a fresh successor or slice.

## Evidence

`HistoryIntegrity.lean` proves resolution absorption and uniqueness, token fate and exclusivity, local and segment conservation, reflexivity, composition, restriction, and a nonvacuous faithful ledger. It proves the hollow model differs only at `carry_complete` among the stated one-step content clauses and changes the account. All declarations have `#print axioms` entries and build without `sorry`.

`src/fixtures.py` and `tests/run.py` give exact finite mirrors of hollow carry, closure/settlement separation, and append-only reconsideration. These are exact witnesses, not general proofs.

## Status labels

- Lean-proved: HI-1 through HI-8 in `THEOREMS.md`.
- Exact-witness: CM-1 through CM-3 as finite fixtures; CM-1 also has Lean proofs.
- Paper-derived: the comparison to anchored slices, authenticated transfer, and transition certificates.
- Proposed definition/interface: `SliceLedger`, `LocalConservation`, segment `Integrity`, separate `Closes`, prospective reconsideration.
- Ambient assumption: semantic authentication/order reflection; settlement-boundary integrity; substantive closure rules and licences; authenticated slice admission.
- Open: adequacy of an application's anchored order; a complete event realization; rules for reopening and reincurrence; necessity/minimality of every local field beyond the isolated `carry_complete` witness.

## Deviations

The worktree matched the prompt's expected base `5ff9539b44debc464128e6a1921ef1690f7b6487`.

The resumed state was described as staged but uncommitted. The prompt and Lean draft were untracked, not staged. They were audited before use. The inherited Lean draft also treated every settlement-tagged resolution as sufficient for the closure receipt; this conflicted with the dispatch's `Settled`/`Closes` distinction, so `closure_certificate` was added. `PROMPT.md` remains verbatim.

`python3 -m checkers.workspace_state --json` reported a baseline stale generated view, `state/views/NAMING_AUDIT.md`. This round had no write scope for `state/**` and did not alter it.

The final repository-wide `python3 tests/run.py` consequently failed in `checkers.wiki_state_bindings --self-test`, whose subprocess requires a successful workspace-state emission. The lane runner, Lean module, name lint, dead-pointer gate, and untracked-pointer gate passed.

## What this does not establish

It does not show that any concrete history implementation emits these projections or certificates. It does not prove semantic authentication, order reflection, settlement integrity, licence correctness, closure correctness, Non-Capture, Progress, service, practical adequacy, or a Normative Inductor theorem. The closure certificate is carried as a typed premise; its content is external to the lattice proof. The endpoint relation is proposed and no antisymmetry or witness uniqueness is shown. `token_fate` is about issue identity; it does not by itself rule out content erasure. The finite Python fixtures do not prove general statements.

## Proposed filings

1. A later integration round should file a priority for a concrete history-to-`DefeatTrace`/`SliceLedger` export theorem, consuming this interface and the Normative Inductor realization.
2. A later integration round should file the application-level obligation to define certificate-bearing `Closes`, including prospective reconsideration and explicit reincurrence semantics.
3. A later integration round should record the stale `state/views/NAMING_AUDIT.md` orientation result if it persists on its synthesis branch.

No maintainer decision is reserved by this round.

## Outstanding maintainer actions

None.

## Attribution

- Prompt author: orchestrator (Claude Fable 5.1, Anthropic), relaying a maintainer dispatch.
- Executor: GPT-5 (OpenAI).
- Execution date: 2026-09-05.
