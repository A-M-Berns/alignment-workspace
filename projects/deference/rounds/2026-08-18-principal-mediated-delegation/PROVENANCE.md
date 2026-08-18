# Provenance

| file or glob | generator | review status | date | round | chat bundle |
|---|---|---|---|---|---|
| `README.md`, `MODEL.md`, `REPO_MAP.md`, `PRINCIPAL_MEDIATION.md`, `REPAIR_LEMMA.md`, `RECOGNITION_AND_ANSWERABILITY.md`, `PRINCIPAL_TRANSPORT_INTERFACE.md`, `NATURALIZED_AGENCY_BRIDGE.md`, `LI_PREDICTION_INTERFACE.md`, `PROSECUTION.md`, `THEOREM_MAP.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-18 | `prompts/2026-08-18-principal-mediated-corrigibility/`; prompt author GPT-5.6 Sol (OpenAI) | — |
| `src/**`, `tests/**` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-08-18 | same | — |

Exact finite checks and displayed witnesses. No Lean, and `THEOREM_MAP.md` §5
says why none is proposed. Nothing is registered.

## Declared dependencies

`tests/run.py` puts two directories on the path and fails by name if either is
absent:

- `projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/src`
  — the protected normative response function, the non-capture and coverage
  clauses, the grade, and the 27 scenarios every composition statement is
  quantified over;
- `projects/normativity/legitimacy/rounds/2026-08-13-procedural-legitimacy/src`
  — required transitively by the above.

The selector is `judgment_of ∘ grade_of` from that round's `src/trust.py`, not a
second grade defined here. A fresh grade would have made the composition a claim
about this round's object.

`src/repair.py`'s `bridge_form` recomputes
`lean/Workspace/Deference/Contrib/DelegationBridge.lean`'s inequality in exact
rationals so the composition can be checked. It is a re-typing for prosecution,
not a port: the Lean file remains the statement of record.

## Branch dependency

The base commit is `4b0e17d`, which carries PR 39. PR 38
(`origin/traderized-enforcement` at `5fc434d`) had not landed on `main` when this
round ran; it was read and not merged, so nothing here depends on it and the
branch is independently mergeable. `REPO_MAP.md` records the reading and the
verdict of orthogonality.
