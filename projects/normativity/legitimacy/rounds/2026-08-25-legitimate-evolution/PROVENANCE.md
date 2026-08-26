# Provenance

| Files | Generator | Review status | Date | Originating round | Chat bundle |
|---|---|---|---|---|---|
| `README.md`, `LEGITIMATE_EVOLUTION.md`, `CROSS_PROCESS_INTERFACE.md`, `CONSUMER_TEST.md`, `TRADERIZATION_CONSUMER.md`, `COUNTERMODELS.md`, `THEOREM_MAP.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-25 | `prompts/2026-08-25-legitimate-evolution/` | — |
| `src/`, `tests/` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-25 | `prompts/2026-08-25-legitimate-evolution/` | — |

The prompt was authored outside this repository and is committed verbatim at
`prompts/2026-08-25-legitimate-evolution/PROMPT.md`, including the addendum sent
while the first pass was running and the repair pass's dispatch.

## Sources

**In-repository, imported and run unmodified.** The Carroll legitimacy round at
`../2026-08-25-carroll-legitimacy-test/src/` — `enrichment.py` for `excise`,
`ancestry` and the case builder, `legitimacy.py` for `independent` and
`survives_excision`, `fixtures.py` for `C7b`, `C10`, `C11`, `C14`, `C22`, `C23`,
`C28` and `C33`. Through it, the Reflective Integrity core at
`../2026-08-24-reflective-integrity-core/src/ri_core.py` and the vertical slice's
`standing.py` for `PValue`.

**In-repository, read and mapped rather than imported.**
`../2026-08-24-reflective-integrity-core/REFLECTIVE_INTEGRITY_CORE.md` §§4, 12-13,
15, 17, 19-24, 26-27 and 32, for the realization table and the axiom-by-axiom
argument. `../2026-08-25-carroll-legitimacy-test/CRITERION.md` §§3-4 and 6 and
`THEOREM_MAP.md` entries 27-31c, for the challenge operator and what it does not
support. `../2026-08-25-end-to-end-vertical-slice/ANSWERABILITY_SCOUT.md` and
`VERTICAL_SLICE.md` §11, for the liability reading in
`CROSS_PROCESS_INTERFACE.md` §6. `../2026-08-17-counterfactual-legitimacy/`
`LEGITIMACY_INTERFACE.md` and `LEGITIMACY_TO_TRUST_INTERFACE.md`, for the
comparison in `CONSUMER_TEST.md` §3 and for `H5`.

**In-repository, read as the second consumer.** The traderized-enforcement round
at `../../rounds/2026-08-16-traderized-enforcement/src/` — `force_api.py`,
`outflow.py`, `deduction.py` — read for the charge, the deficit certificate and
the exhaustion policy, and cited by declaration. The vertical slice's
`ANSWERABILITY_SCOUT.md` and `VERTICAL_SLICE.md` §11 for the Level-I accounting
result. Nothing in either is modified and no liability quantity is computed here.

**In-repository, read as the first consumer.**
`lean/Workspace/Deference/Contrib/DelegationBridge.lean` and
`ReachableCorrectiveControl.lean`, cited by declaration and line;
`projects/deference/CLAIMS.md`; `projects/deference/notes/FUTURE_AGENT_SPEC.md`
and `FINITE_MODEL_SKELETON.md` §8.5. No Lean file is modified and no registered
claim is changed.

**Not used.** No Logical Induction object and no charged enforcement path is
run: the traderization modules above are read and cited, and nothing here
computes a liability quantity. `src/warrant.py` imports `frame.py` and the
standard library and nothing else, which `tests/test_frame.py` checks by parsing
its imports.

## New names introduced

All provisional under `AGENTS.md` §6.

*Succession frame*, *exercise*, *affected*, *parents*, *grounds*, *issued*,
*threat model*.

Axioms: *base stability* (L0), *precedence* (L1), *no ex nihilo authority* (L2),
*unique issuance* (L2'), *issuance stability* (L3), *origin necessity* (L3'),
*challenge bite* (L4), *challenge coverage* (C), *lifecycle entry* (L5),
*lifecycle exit* (L6), *account carriage* (L7), *account trichotomy* (L8).

Relations and objects: *certified succession*, *derivability* (`G |- y`),
*legitimately live frontier*, *AuthorityView*, *NormView*, *event identity*,
*effect identity*, *the recognition axiom* (R), *W-index*, *bounded-lifetime
liability*.

Theorems: *lineage existence* (T1), *canonicity* (T1'), *no self-ratifying
authority* (T2), *content independence* (T3), *persistence* (T4), *antitone in
challenges* (T4'), *visible discontinuity* (T5).
