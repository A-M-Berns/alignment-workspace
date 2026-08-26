# Provenance

| Files | Generator | Review status | Date | Originating round | Chat bundle |
|---|---|---|---|---|---|
| `README.md`, `LEGITIMATE_EVOLUTION.md`, `PROPER_EXERCISE.md`, `CROSS_PROCESS_INTERFACE.md`, `CONSUMER_TEST.md`, `TRADERIZATION_CONSUMER.md`, `COUNTERMODELS.md`, `THEOREM_MAP.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-26 | `prompts/2026-08-25-legitimate-evolution/` | — |
| `src/`, `tests/` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-26 | `prompts/2026-08-25-legitimate-evolution/` | — |

The prompt was authored outside this repository and is committed verbatim at
`prompts/2026-08-25-legitimate-evolution/PROMPT.md` — five dispatches: the round,
an addendum sent mid-round, a repair pass, a compression pass, a prosecution
pass, and a Proper Exercise discovery round.

## Sources

**In-repository, imported and run unmodified.** The Carroll legitimacy round at
`../2026-08-25-carroll-legitimacy-test/src/` — `enrichment.py` for the case
builder and the settlement-ancestry closure, `fixtures.py` for `C7b`, `C10`,
`C11`, `C14`, `C22`, `C23` and `C33`. Through it, the Reflective Integrity core
at `../2026-08-24-reflective-integrity-core/src/ri_core.py` and the vertical
slice's `standing.py` for `PValue`.

**In-repository, read and mapped rather than imported.**
`../2026-08-24-reflective-integrity-core/REFLECTIVE_INTEGRITY_CORE.md` §§12.3,
13, 15.2 and 17, for the extraction.
`../2026-08-25-end-to-end-vertical-slice/ANSWERABILITY_SCOUT.md` and
`VERTICAL_SLICE.md` §11, for the Level-I accounting result.

**In-repository, read as the consumers.** The traderized-enforcement round at
`../../rounds/2026-08-16-traderized-enforcement/src/` — `force_api.py`,
`outflow.py`, `deduction.py` — cited by declaration.
`lean/Workspace/Deference/Contrib/DelegationBridge.lean` and
`ReachableCorrectiveControl.lean`, cited by declaration and line;
`projects/deference/notes/FUTURE_AGENT_SPEC.md` and `FINITE_MODEL_SKELETON.md`
§8.5. No Lean file is modified and no registered claim is changed.

**Not used.** No Logical Induction object and no charged enforcement path is run;
no liability quantity is computed. `src/office.py` imports `replay.py` and the
standard library and nothing else, and `src/replay.py` names no architectural or
semantic identifier — `tests/test_replay.py` checks both by parsing.

## New names introduced

All provisional under `AGENTS.md` §6.

Kernel: *occurrence* (`Occ`), *edit*, *trace position*, *grounds*, *issues*,
*dispose*, *base* (`G`), *authority predicate*, *admitted*, *live*, *grounded*,
*grounding tree*.

Premises: *prior grounding* (S1), *no ex nihilo* (S2).

Theorem and corollaries: *Grounded Replay*, *no self-ratification*, *no
laundering*, *persistence*.

Semantics: *`Valid`*, *`Permit`*, *`ProvView`*, *`ProvComplete`*, *audit context*
(`alpha`), *threat class* (`Xi`).

Realization and computation: *extraction*, *extraction factorization*, *fold
determinism*, *agreement along the trace*, *simulation*, *soundness at the
checker's own state*.

Consumer-side: *the recognition axiom* (R), *W-index*, *bounded-lifetime
liability*.

Answerability: *claim occurrence* (`Ob`), *incurred*, *outstanding*, *claim key*,
*activation*, *newly due*, *resolution derivation*, *frontier*, *carry*,
*Answerability Resolution*, *no silent loss*, *controlled resolution* (A1), *due
realization* (D1), *conformance condition*, *asymmetric gating*, *potential*,
*dilution*, *total accounting*, *per-parent accounting*, *unheralded opening*,
*`Due`*, *`Resolve`*.

Withdrawn across rounds 7 and 8: *fresh obligations* (A2), as a premise and then
entirely; *`Disposes`* and *`Transfers`* as separate parameters, folded into
*`Resolve`*; the fresh-successor clause in the carry law; and `D1` as a
*structural premise*, relocated to the realization boundary.

Proper Exercise: *capability* (`Cap`), *reach*, *widening*, *proper exercise*, *authority over authority*, *plenary base*, *jurisdictional self-ratification*, *unauthorized privilege escalation*.
