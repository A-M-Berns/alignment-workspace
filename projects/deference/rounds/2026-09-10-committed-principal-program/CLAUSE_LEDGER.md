# The seven clauses of item 87, after this round

**Status:** `ci-only`.  Each verdict is either unchanged from the 2026-09-09 round
(`../2026-09-09-evaluation-ecosystem-realization/CLAUSE_LEDGER.md`, cited as *#97*) or
moved, with what moved it.

## 1. Authenticated principal-exclusive binding — DISCHARGED (repaired)

Unchanged verdict; the discharge had a hole.  The registry now binds `(party, key)` and
carries revocation (`PRESSURE.md` P1): a commit under the principal's key authored by
the advisor is not a receipt (`Instance.stolen_key_void`), a revoked delegation binds
nothing (`Instance.revoked_binds_nothing`).  Under re-execution a second key binds only
the mandated output (`Instance.delegated_binds_program_output`), and exclusivity then
fails as before.  **Rests on** log authenticity of the author field, now protecting who
bound and not what: the forger's own vector is void.

## 2. The issuance-rooted reason-trace factorization — CLOSED ON LOG AUTHENTICITY

Moved by the committed program.  `#97` discharged it for the reading principal and
named the residual "the receipts mean what they say" — a property of the counterfactual
class no log carries.  Now the mandate carries `π_P : ℛ → 𝒱` and the commit re-executes
it: `reasonMediated_of_reexecution` (**LEAN**, generic in the frame) gives
`ReasonMediated` over any audited class of activated continuations sharing the mandate,
with factor map `eval π_P`; `exclusiveBind_of_registry` gives `ExclusiveBind` from the
registry; `blind_payload_of_reexecution` transfers blindness from the trace.

**The residual, exactly.**  None of "the receipts mean what they say".  What remains is
(ii) issuance authenticity — the `ISSUE` event is the principal's (log authenticity) —
and (iii) that `ℛ` is correctly declared (EXT, unchanged).  The computational-integrity
statement (i) — *the principal computed `eval π_P` on that prefix rather than something
that coincided* — is **not** a hypothesis: the payload map is a function of the log,
a non-coinciding computation voids rather than certifies (`Instance.miscomputation_void`),
and the coinciding one produces the same log (`Instance.logs_equal`,
`Instance.payload_regardless`).  `PRINCIPAL_PROGRAM.md` §3.  The audited class is the
activated continuations, which is the partial-`Ṽ` instantiation of the consolidation.

## 3. Correctness of the declared abstraction — DISCHARGED, exclusion stated

Unchanged verdict (`#97`).  Added: the band for the program class (constant program,
`R = id`; `proofcheck` in the band, `Programs.proofcheck_in_band`) and the exclusion P3
names — content must be intrinsic to the admitted history; the program language has no
position term, the advisor-side half is a pair-class condition, EXT.

## 4. Representation faithfulness — DISCHARGED in Lean (repaired)

Unchanged verdict (`rep_faithful`, generic); the discharge admitted advisor-written
representation.  Representation is now the registrar's move (`routed` requires `S`;
`forged_route_not_represented`).  A scope no `ROUTE` can name makes the theorem vacuous:
scope-relative as `REASON_SUPPLY.md` §4 states, a declaration error outside it (P4).

## 5. Protected reason-supply liveness — RESIDUAL (the openness discharge reopened and repaired)

The liveness residual is unchanged (`#97`: the D4 criterion).  What moved is the
*activation event's* clause 5, which `#97` discharged with the class `J = {silent, honest}`:
for that `J` the counterfactual half of Robust Openness is empty, and pinned branch data
can hide a failing branch once a coverage-affecting intervention is declared (P2).  The
Lean semantics now defines branches as log transforms; with `jam ∈ J` and a robust
registrar the clause is nonvacuous and holds on `w1` (`Instance.openAll_robust`), with a
fragile registrar it fails (`Instance.not_openAll_fragile`), and the pinned form is kept
as the attack (`Instance.openAll_pinned_fragile`).  **Rests on** the transforms being the
causal truth of the interventions (EXT, one declaration per intervention).

## 6. Selection-induced target sealing — PARTIAL (unchanged), transfer refused

Unchanged (`#97`).  C5: a committed advisor program with no selection input makes
`Blind R P_sel` a typing fact in the finite model and does not seal the target — the view
leaks `σ` back whenever the ecosystem publishes it (`test_view_leak`).  Not built;
`PRINCIPAL_PROGRAM.md` §5.

## 7. Availability — RESIDUAL (unchanged), one void source added and removed

Unchanged criterion (`#97`).  Re-execution adds a void source relative to `#97`'s list
(nature / advisor): a commit whose vector is not the program's output.  Under honest
execution that source is empty; without it, it is a void and never a false
certification.  `η_n → 0` now needs: nature's voids vanish; the advisor's
selection-conditioned continuations stay admissible; and the principal executes its
program, or miscomputes with vanishing frequency.  The strict/tolerant choice moves
`η` by the frequency of attempted bypasses (P5: `7/22` versus `1/22` on the simulated
sequence).  No rate for the void frequency is claimed.

## Summary

| clause | #97 | now | moved by |
|---|---|---|---|
| 1 | DISCHARGED | DISCHARGED | key theft repaired; the program pins the vector |
| 2 | DISCHARGED / RESIDUAL (receipts) | **CLOSED ON LOG AUTHENTICITY** | the committed program and re-execution |
| 3 | DISCHARGED | DISCHARGED | exclusion stated |
| 4 | DISCHARGED | DISCHARGED | route forgery repaired |
| 5 | RESIDUAL | RESIDUAL; openness discharge reopened and repaired | transforms, `jam`, registrar robustness |
| 6 | PARTIAL | PARTIAL | transfer refused |
| 7 | RESIDUAL | RESIDUAL | one void source added, removed by honest execution |
