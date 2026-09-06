# Theorem ledger

## Verdict

**Structural Integrity does not imply content-level Diachronic Answerability.** With the transition-local content clause in `DEFINITIONS.md`, plus authenticated anchored loads and the initial account equation, Integrity does imply Answerability Conservation. On the smallest separating disposal fixture, `carry_complete` is the only missing clause and permits a fourth fate: erased content.

| Result | Statement | Evidence |
| --- | --- | --- |
| HI-1 | Resolution is absorbing and its position is unique. | lean-proved: `not_out_after_res`, `res_unique` |
| HI-2 | After birth, each token is outstanding, discharged at a unique earlier resolution, or disposed at a unique earlier resolution with a fresh successor. | lean-proved: `token_fate`, `fate_exclusive` |
| HI-3 | Segment Integrity is reflexive and concatenates; restriction to a subsegment preserves it. | lean-proved: `SliceLedger.integrity_refl`, `integrity_compose`, `integrity_mono` |
| HI-4 | One local step preserves the slice account and locality. | lean-proved: `SliceLedger.account_succ`, `local_succ` |
| HI-5 | Segment Integrity plus initial locality preserves `sat join stl join live-load` at the endpoint. | lean-proved: `SliceLedger.conservation_segment`, `conservation` |
| HI-6 | The full hypotheses are jointly satisfiable on the landed disciplined trace. | lean-proved: `Witness.faithful_step`, `faithful_conserves`, reusing `witness_disciplined` |
| HI-7 | Defeat discipline alone admits erased content; the faithful and hollow ledgers share one trace. | lean-proved: `Witness.same_trace_disciplined`, `hollow_account_changes` |
| HI-8 | In the hollow fixture, every local clause except `carry_complete` holds. | lean-proved: `Witness.hollow_other_clauses`, `hollow_carry_fails`, `hollow_not_step` |
| HI-9 | A settlement-tagged resolution needs authenticated availability and a separate `Closes` judgment. | proposed definition/interface; the field `closure_certificate` is Lean-typed |
| HI-10 | Rejecting an earlier `Closes` produces a prospective reconsideration obligation while leaving the old token terminal. | proposed definition/interface |

Every printed declaration audits to a subset of `[propext, Classical.choice, Quot.sound]`. The full witness is nonvacuous. The Python runner supplies exact finite mirrors, not general proofs.

## Conservation statement

Let

```text
account_n(m) = sat_n join stl_n join join {lam_n(q) | q in Live_n(m)}.
```

Then:

```text
Local_n0(m) and n0 <= n and Integrity(Lambda,Closes,n0,n)
  imply account_n(m) = account_n0(m) and Local_n(m).
```

This is the three-fate law at the content level: answered, closure-discharged, or faithfully carried live. Disposal is absent from receipts because it transports rather than discharges.

## Dependency boundary

The proof uses structural exact evolution and fresh ancestry from `DefeatTrace`; load equality/inequality from `LocalConservation`; and initial locality. It does not use `Disciplined`, standing, licence content, attention, `Met`, or Progress. `Disciplined` supplies a compatible record-side resolution policy, not the semantic account equation.

The closure field is proof-irrelevant to the lattice equality once `stl_receipts` is assumed. It is nevertheless necessary for the receipt to mean closure rather than merely carry a settlement tag. This is interface typing, not a derived theorem.
