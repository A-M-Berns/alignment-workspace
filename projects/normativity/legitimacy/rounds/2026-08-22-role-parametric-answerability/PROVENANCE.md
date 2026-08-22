# Provenance

| Files | Generator | Review status | Date | Originating round | Chat bundle |
|---|---|---|---|---|---|
| `README.md`, `MEMO.md` | GPT-5.6 Sol (OpenAI) | `ci-only` | 2026-08-22 | `prompts/2026-08-22-role-parametric-answerability/` | — |
| `src/role_kernel.py`, `tests/` | GPT-5.6 Sol (OpenAI) | `ci-only` | 2026-08-22 | `prompts/2026-08-22-role-parametric-answerability/` | — |

The executor worked from live `origin/main` at
`76252ffbd6b384f78ccf2d2d27f76354af1f5a16`, which includes merged PR #45.
The Singh-informed continuation was performed on the existing PR #46 branch at
commit `75d21df` and updates these same artifacts in place.
The final consolidation was performed on the same branch after commit `bcbbeab`;
it reread the cited PDF passages for every attribution, decomposed the opaque
`Spec` into substantive content plus a pinned lifecycle/semantic receipt, added
typed disposition and operation-linked review witnesses, and compressed the memo
without changing the registered verdict.

## External source note

Full citation: Munindar P. Singh, “An Ontology for Commitments in Multiagent
Systems: Toward a Unification of Normative Concepts,” *Artificial Intelligence
and Law* 7 (1999), 97–113.

Local source inspected in full: `/Users/anson/Downloads/ai+law-final.pdf`.

Claims relied upon from the paper:

- Definition 1 gives the named four-place commitment `C(x,y,G,p)`: debtor,
  creditor, context group, and discharge condition.
- Sections 2.1 and 6 treat satisfaction/violation conditions as world-evaluable,
  not reducible to an agent's private mental state; assumptions A7–A8 distinguish
  semantics from pragmatics and reject subjectivist reduction.
- Section 2.2 names Create, Discharge, Cancel, Release, Delegate, and Assign and
  distinguishes their role effects and performers.
- Sections 3.2–3.3 use social policies, sometimes higher-order commitments, to
  govern operations.
- Sections 4.1–4.2 distinguish creditor from beneficiary, represent contextual
  ought with `creditor=G`, and analyze Hohfeldian claim/power/immunity through
  commitments and context action.
- The conclusion states that a model-theoretic semantics remains future work.

Round extrapolations, not claims attributed to Singh:

- immutable occurrence identity and account DAG lineage;
- per-input trace-semantic transport and anti-laundering;
- proof-relevant undertaken reason certificates;
- context-indexed basis-loss review;
- compilation of the six operations into generic resource rewrites;
- evidence-access and consequential-contest interfaces; and
- retained secondary liability or compositional delegation chains.
- pinned lifecycle/semantic receipts and the abstract `ValidDisposition`
  interface.
