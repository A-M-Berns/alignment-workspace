# Comparison with landed machinery

| Existing object | Relation to this round |
| --- | --- |
| `TraceData`, `IssueTrace`, `DefeatTrace` | Reused unchanged as the minimal structural substrate. The event ontology is represented by projections rather than duplicated as a sum type. |
| `Kind`, `DefeatTrace.dispose_successor` | Reused. `answer` and certified `settle` are terminal; `dispose` must carry to a fresh successor. |
| `DefeatTrace.Answerable` | Orthogonal record-side certificate for an individual disposal: grounded, non-self, routed, and separated. It does not constrain semantic load. |
| `DefeatTrace.Disciplined` | Orthogonal global resolution policy. `Witness.same_trace_disciplined` plus the hollow ledger proves that it does not entail content conservation. |
| `DefeatTrace.Grounded`, `grounded_replay` | Supplies historical availability and ancestry. It does not authenticate denotation or authorize `Closes`. |
| Answerability carriers' conservation law | Refined: terminal `Disposition` is removed; answer and settlement-closure receipts remain; disposal contributes through live successor load. |
| Anchored slices | Reused semantically. `SliceLedger` is one slice's load and receipts; its immutable denotation and admission witness remain parameters outside the structural trace. |
| Authenticated Transfer | Compressed to the order-facing fields `incoming_sound` and `carry_complete` for this theorem. Authentication, quotient adequacy, and bridge construction are not subsumed and remain premises justifying those inequalities. |
| Faithful semantic preservation | Not subsumed. Order reflection is needed to interpret equal stable-domain load as no relevant weakening/strengthening. The present Lean theorem only conserves the supplied `L` value. |
| Transition certificates | Their strict pre-state citation, constitutive immutability, and continuation principles govern how evidence for each local field is produced. `LocalConservation` is the semantic account those certificates must establish, not a replacement checker. |
| Settlement interface | Tightened: `Settled n s` authenticates availability; `Closes n s q` judges relevance; terminal receipt formation requires both. |
| `Met` | Separate prerequisite satisfaction derived from earlier answer/settlement kinds. This round does not identify `Met` with closure of an anchored slice. |

## Compression limit

One certificate envelope can carry basis, licence, lineage, settlement receipt, closure judgment, and semantic-transfer fields. The checks do not collapse into one predicate with one evidential source. In particular, provenance cannot prove semantic faithfulness, and settlement availability cannot prove closure relevance.

## Naming

Provisional names introduced: `HistoryIntegrity`, `SliceLedger`, `LocalConservation`, `Integrity`, `account`, and `closure_certificate`. `Closes` follows the dispatch's proposed interface and remains provisional until a canonical consolidation.
