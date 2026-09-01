# Hostile finite examples

The executable versions are in `src/pe_models.py`; all numeric checks use exact
`Fraction` arithmetic.

| # | example | candidate accepted/rejected | discriminating fact |
| ---: | --- | --- | --- |
| 1 | authorized bogus terminal resolution | `Authorized`; rejected by `PE^resolve` | live post burden has neither discharge nor carrier |
| 2 | authorized self-revision destroys coverage | `Permit`; rejected by affected-complete PE | changed coverage burden was omitted/dropped |
| 3 | same-batch route deletion plus terminal resolution | prefix-only check accepts; transition PE rejects | pre-route exists, post-route and carrier do not |
| 4 | temporary coverage failure with open repair carrier | PE accepts | no route, but unresolved burden remains live |
| 5 | one burden splits into two | relational transport accepts | both successors are live and authenticated |
| 6 | two burdens merge into one | relational transport accepts | both sources authenticate the shared successor |
| 7 | ontology translation | PE accepts | old-to-new semantic pair is certified |
| 8 | fake translation drops a live claim | PE rejects | `actually_changed` is not covered by `Affected` |
| 9 | sensor deletion marked `Met` | `PE^met` rejects | deletion is not satisfaction evidence |
| 10 | valid obsolescence | `PE^met` accepts | authorized obsolescence witness backs rising edge |
| 11 | two liability rows | each PE-feasible alone; joint PE rejects | exact joint deficit \(1/4\) |
| 12 | same response policy, different receipts | response-structure locality accepts; `(BL)` rejects | identity rule maps 0/1 to different actions |
| 13 | same realized action, different latent rules | trace `(BL)` accepts at receipt 0; structure rejects | rules differ at receipt 1 |
| 14 | predictor reacts to query | exterior-fixed accepts | one fixed strategy table returns different outputs |
| 15 | self-modification changes response types | bare equality ill-typed; typed transport accepts | explicit old/new policy relation is required |

## Additional authorization examples

Deleting an authorized rule while leaving inherited matters and their interpretations
intact can pass standing PE.  The same authorized deletion fails when it destroys their
only interpretation.  An authorized evaluator replacement fails when it censors an
active criticism.  These differ in PE, not provenance.

## Failed locality implications

`(CFP)` plus a singleton residual admits whole-agent replacement, so exterior-fixed does
not imply response-structure-fixed.  Example 12 refutes response structure \(\Rightarrow\)
realized behavior.  Example 13 refutes realized behavior \(\Rightarrow\) response
structure.  A query bit which merely changes a display color satisfies all behavioral
invariants yet is not inquiry; semantic certification is independent.

## Conservation necessity

The one-burden Boolean fixture exhausts the combinations of affected, actually changed,
disposed, and post-live.  Every admitted `pe_sound` step leaves either a disposition
receipt or a live frontier.  Removing affected-completeness admits example 8; removing
nonempty/live successors admits examples 1–3; removing sound pair proofs admits an
arbitrary relabeling as “translation”; removing the Continuity-side persistence check
allows an unaffected carrier to vanish.
