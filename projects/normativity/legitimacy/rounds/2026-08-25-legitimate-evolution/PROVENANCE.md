# Provenance

| Files | Generator | Review status | Date | Originating round | Chat bundle |
|---|---|---|---|---|---|
| `README.md`, `LEGITIMATE_EVOLUTION.md`, `CROSS_PROCESS_INTERFACE.md`, `CONSUMER_TEST.md`, `TRADERIZATION_CONSUMER.md`, `COUNTERMODELS.md`, `THEOREM_MAP.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-25 | `prompts/2026-08-25-legitimate-evolution/` | — |
| `src/`, `tests/` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-25 | `prompts/2026-08-25-legitimate-evolution/` | — |

The prompt was authored outside this repository and is committed verbatim at
`prompts/2026-08-25-legitimate-evolution/PROMPT.md` — four dispatches: the round,
an addendum sent mid-round, a repair pass, and a compression pass.

## Sources

**In-repository, imported and run unmodified.** The Carroll legitimacy round at
`../2026-08-25-carroll-legitimacy-test/src/` — `enrichment.py` for the case
builder and the settlement-ancestry closure, `fixtures.py` for `C7b`, `C10`,
`C11`, `C14`, `C22`, `C23` and `C33`. Through it, the Reflective Integrity core
at `../2026-08-24-reflective-integrity-core/src/ri_core.py` and the vertical
slice's `standing.py` for `PValue`.

`legitimacy.py`'s `independent` and `survives_excision` are **not** imported: the
compressed judgment reads an edit's declared input rather than replaying the
record under a voided episode, and `LEGITIMATE_EVOLUTION.md` §7 is the account of
what that trades.

**In-repository, read and mapped rather than imported.**
`../2026-08-24-reflective-integrity-core/REFLECTIVE_INTEGRITY_CORE.md` §§12.3,
13, 15.2, 17 and 19, for the realization table.
`../2026-08-25-carroll-legitimacy-test/CRITERION.md` §§3-4 and 6, for the
challenge operator and the properties it does not have.
`../2026-08-25-end-to-end-vertical-slice/ANSWERABILITY_SCOUT.md` and
`VERTICAL_SLICE.md` §11, for the Level-I accounting result.
`../2026-08-17-counterfactual-legitimacy/LEGITIMACY_TO_TRUST_INTERFACE.md`, for
`H5` and `grade_reads_outside`.

**In-repository, read as the consumers.** The traderized-enforcement round at
`../../rounds/2026-08-16-traderized-enforcement/src/` — `force_api.py`,
`outflow.py`, `deduction.py` — cited by declaration for the charge, the deficit
certificate and the exhaustion policy.
`lean/Workspace/Deference/Contrib/DelegationBridge.lean` and
`ReachableCorrectiveControl.lean`, cited by declaration and line;
`projects/deference/CLAIMS.md`; `projects/deference/notes/FUTURE_AGENT_SPEC.md`
and `FINITE_MODEL_SKELETON.md` §8.5. No Lean file is modified and no registered
claim is changed.

**Not used.** No Logical Induction object and no charged enforcement path is run;
no liability quantity is computed here. `src/office.py` imports `replay.py` and
the standard library and nothing else, which `tests/test_replay.py` checks by
parsing its imports; `src/replay.py` names no architectural type, which the same
file checks by reading it.

## New names introduced

All provisional under `AGENTS.md` §6.

*Occurrence* (`Occ`), *edit*, *declared view*, *grounds*, *issue*, *dispose*,
*audit context* (`alpha`), *legitimate replay*, *legitimate state* (`L`),
*authority view* (`Auth`), *norm view* (`Norm`), *threat class* (`Xi`).

Parameters: *`Valid`*, *`Permit`*, *`ProvOK`*, *`InputOK`*, *`ExerciseOK`*.

Hypotheses: *mediated mutation* (H1), *fresh occurrence* (H2), *strict-prestate
grounding* (H3), *permit soundness* (H4), *declared factorization* (H5),
*threat-relative provenance adequacy* (H6).

Theorems: *finite grounding* (G1), *no self-ratification* (G2), *no laundering*
(G3), *hidden-state noninterference* (G4), *persistence* (G5), *unrestricted
permitted revision* (G6).

Consumer-side: *the recognition axiom* (R), *W-index*, *bounded-lifetime
liability*, *verifier soundness*, *verifier completeness*, *missed disposal*.
