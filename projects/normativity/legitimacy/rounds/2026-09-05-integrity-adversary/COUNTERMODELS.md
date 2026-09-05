# Countermodel ledger

| ID | result | evidence | rerun / declaration |
|---|---|---|---|
| C0 | unchecked `answer` clears unit load | exact-witness | `python3 tests/run.py`, `test_a0_*` |
| C1 | genuine unrelated settlement item clears unit load | exact-witness | `test_a1_*` |
| C2 | rule revision flips `Closes` false to true | exact-witness | `test_a2_*` |
| C3 | reinterpretation flips `Closes` false to true | exact-witness | `test_a3_*` |
| C4 | honest ancestry/route reopening is structurally refused; fresh-root reopening is accepted but disconnected | exact-witness; lean-proved for the structural impossibility | `test_a4_*`; `parent_resolved_at_birth`, `root_not_resolved_before` |
| C5 | current-ontology applicability loses a transported obligation | exact-witness | `test_a5_*` |
| C6 | successor anchor change loses `P`'s standing | exact-witness | `test_a6_*` |
| C6b | later quotient accepts deletion of exact mass `1/2`; source quotient refuses it | exact-witness | `test_a6b_*` |
| C7 | `Met` is true while the root's successor carries the full load | exact-witness; lean-proved | `test_a7_*`; `Gate.gate_kind_decides_met` |
| C8a | an atomic unit is split into two independently answered halves | exact-witness | `test_a8a_*` |
| C8b | two units merge under one anchor and one answer label | exact-witness | `test_a8_*` |
| C9 | arbitrary finite `AnswerableFor P` chain ends in unchecked answer | exact-witness for tested depth 3; lean-proved for one edge | `test_a9_*`; `Evasive.evasive_answerable_for_P` |
| C10 | one resolver mints licence, issue, disposal and answer while `AnswerableFor P` holds | exact-witness; lean-proved | `test_a10_*`; `Evasive.evasive_minted_standing` |
| C11 | one history is disciplined under one `Li` and not another | exact-witness; lean-proved on the spine witness | `test_a11_*`; `Lemmas.witness_disciplined_is_relative` |
| C12 | dropping an unmet prerequisite makes an issue ready while its root stays live | exact-witness; lean-proved | `test_a12_*`; `Gate.gate_c_ready`, `gate_e_never_met`, `gate_u_live` |
| C13 | a late parentless root satisfies replay with itself as sole root | exact-witness; lean-proved | `test_a13_*`; `Evasive.evasive_late_root` |
| C14 | strict pre-state grounds form a diachronic semantic cycle | exact-witness | `test_a14_*` |
| N0 | six malformed controls are refused at their named I4–I9 clauses | exact-witness | `NegativeControls.test_refusals` |

All Lean declarations in
`Workspace.Normativity.Contrib.IntegrityAdversary` are `lean-proved`. Their explicit
`#print axioms` output contains only `propext`, `Classical.choice`, and `Quot.sound`.
The finite Python rows establish only their named instances.

## Proposed interfaces exposed by the countermodels

| interface | status | minimal obligation |
|---|---|---|
| `Closes(H_n,s,α)` | proposed definition/interface | store the prefix, internal rule derivation, interpretation version, and authority; external settlement authenticates `s`, not this judgment |
| `Reconsiders(q_new,q_old,c)` | proposed definition/interface | target a resolved obligation and its closure certificate without rewriting either; successful reconsideration creates live carried debt |
| `Carries(e,α_src,α_dst)` | proposed definition/interface | preserve anchored answer specification, standing, exact load, and compositional semantic transport across split/merge/rename |
| `AuthorizedRoot(r,n)` | proposed definition/interface | distinguish authenticated genesis/issuance from merely parentless birth |
| `LicenceAt(H_n,l,b,κ,τ,x)` | proposed definition/interface | make licence validity prefix-relative and replayable from the history |
| `AdequateAnswer(H_n,q,ρ)` | proposed definition/interface | authenticate responder authority and show receipt `ρ` meets the anchored answer specification |
| settlement integrity | ambient assumption | monotone, authentic, externally supplied settlement view |
| non-capture of entry/standing/rules | open | certify resistance relative to a declared intervention or coalition class |
| practical adequacy/value | open | certify joint response and counterfactual/value semantics externally |
