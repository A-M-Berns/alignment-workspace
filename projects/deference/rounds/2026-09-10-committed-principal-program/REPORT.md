# Report

## Verdict

**COMMITTED-PROGRAM-CLOSES-CLAUSE-TWO-ON-LOG-AUTHENTICITY.**  Clause 2 of item 87:
**CLOSED ON LOG AUTHENTICITY.**  Exact statement: with the principal's program `π_P : ℛ →
𝒱` committed in the mandate and re-executed by the verifier at commitment, for every
frame `β`, every audited class `D` of activated continuations sharing the mandate and
every policy `z`, `ReasonMediated β R V D z` holds with factor map `eval π_P`
(`reasonMediated_of_reexecution`, LEAN, generic; inhabited by `Instance.mediation_witness`),
`ExclusiveBind` follows from the party-bound registry (`exclusiveBind_of_registry`), and
blindness transfers (`blind_payload_of_reexecution`).  What remains is issuance
authenticity (log authenticity at the `ISSUE` event) and the correctness of the declared
trace `ℛ` — the two inputs the 2026-09-09 round already carried.  Computational integrity
(i) is not a hypothesis: a non-coinciding computation voids, a coinciding one produces
the same log and the same payload (`Instance.miscomputation_void`, `Instance.logs_equal`,
`Instance.payload_regardless`).  This is the headline the dispatch asked whether it was
true: it is.

## The pressure pass (§1)

`PRESSURE.md`.  Three breaks, all repaired locally: key theft (registry now binds
`(party, key)`, with revocation); advisor-written representation (the registrar's move
only); pinned counterfactual branches hiding a failing branch (Lean branches are now log
transforms; the pinned form is kept as the attack).  One finding: the 2026-09-09
intervention class had no counterfactual content, so its clause-5 openness discharge
was thin; `jam` and registrar robustness make it nonvacuous.  P3's exclusion stated
(content intrinsic to the admitted history).  P5 tabled under both readings, strict
kept as default.  P6: the typed rule needs two log-checkable clauses (`typed+`) and
still admits a chain through earlier activated evaluations.

## Re-scored expectations (P7)

All seven remain "right"; three (1, 4, 5) were right because the expectation asked for
less than the clause needed.  Table in `PRESSURE.md` P7.

## The push (§2)

`PRINCIPAL_PROGRAM.md`.  (C1) a total first-order language over the trace, typed by its
input; register programs a separate class; `evalTermR_ofTerm`.  (C2) `Kind.commit`
carries `(issue, prefix)`; `validAnswer` re-executes; `commitVector_of_validAnswer`;
`activated_iff` unchanged.  (C3) the theorem, the two pairs, (i) discharged.  (C4) the band
for the program class; `proofcheck` the canonical member; the reading principal is a
program (correspondence over every model trace).  (C5) not built: the view leaks the
selection back (`test_view_leak`); the horizon hides, does not remove, the obstacle.
(C6) no new `Protocol` field: the check lives in the builder's admission of the commit
event as a receipt, the implementation's authentication layer; `AnswerOK` unchanged.
(C7) Lean extended in place: 41 audited declarations, three axioms, `decide +kernel` for
the rational facts.  (C8) `src/` extended; the 48 fixtures of 2026-09-09 re-run, two
adapted and marked in their docstrings (the forged-author and second-key countermodels,
which under re-execution can bind only the program's output); 39 new fixtures.

## Availability under re-execution (§3)

`CLAUSE_LEDGER.md` clause 7: one void source added (miscomputation), removed by honest
execution; `η_n → 0` needs vanishing nature voids, admissible selection-conditioned
advisor continuations, and an executing principal.  No rate claimed.

## Settlement (§4)

`SETTLEMENT_CHANNEL.md`: "`P` committed `V`" decomposes into two of `P`'s moves and a
deductive fact re-executable by anyone; the typed rule survives with three kinds of
settlement; the queue entry's resolution is cleaner — independence is needed only for
external facts and exactly where the engine may be asked.  Recommendation only.

## Registration

`authorship.mediation-by-reexecution` registered in `projects/deference/CLAIMS.md`
(`lean-proved`, answers item 87, clause 2 only), statement of record
`reasonMediated_of_reexecution`, inhabited by `Instance.mediation_witness` (two
continuations, equal traces, different logs, both activated).  It meets the bar: a term
inhabits the full hypothesis package and the conclusion is nonvacuous on it.  Nothing
else registered; the availability corollary's package is still uninhabited.

## Deviations from the prompt

- The prompt's (C3)(i) is answered as "not a hypothesis" rather than "strictly weaker":
  the strictly-weaker comparison is made (the pairs) and then (i) is discharged by
  re-execution, which the prompt allowed as the headline.
- Frame mediation is stated over the activated subclass of `D` (the partial-`Ṽ`
  instantiation): a void sharing a trace with an activated continuation is not a
  mediation failure but an authority failure, and the `coincide` fixture shows why.
- The Lean `Kind.reason` gained a certificate field and `Kind.issue` a program, so the
  2026-09-09 instance `w1` is re-stated with those fields; every 2026-09-09 theorem name
  is kept.
- `Config.require_program = False` reproduces the 2026-09-09 protocol for the opaque
  baseline; under the new protocol a mandate without a program fails clause 6.
- The corrigibility round's files, items 84 and 86, and `wiki/Corrigibility.md` are
  untouched; `main` did not move; the branch stacks on PR #97.

## What this does not establish

- Log authenticity; the correctness of the declared trace, scope, pair class and
  intervention transforms.
- Anything about the advisor's sealing beyond the finite model's typing fact.
- The tower on activated LUVs; any rate for the void frequency.
- The gloss "genuinely P-authored", which the consolidation left EXT and which
  re-execution does not touch.

## Reserved to the maintainer

Nothing.  The strict/tolerant reading stays a configuration with both reported (the
prompt forbade a ruling); the settlement recommendation is input to the existing queue
entry; the language choice and the re-execution semantics are agent-decided entries.

## Consumers

The principal-side value the corrigibility line consumes is now a committed, re-executable
object: `W` is `eval π_P` on the trace at commitment where the log certifies, so the
activation-indexed grade of the 2026-09-08 ruling is a program the log carries rather
than a function read off a receipt.  Item 84's `(DV)` bridge does not get a sealed
advisor from this round: `test_view_leak` is the case it must still exclude.  Nothing is
integrated.

## Outstanding maintainer actions

1. Decide the merge of PR #97 and then of this pull request, which is stacked on it.
2. Nothing else.

## Attribution

- Prompt author: the maintainer, relayed verbatim (`prompts/2026-09-10-committed-principal-program/PROMPT.md`).
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-10.
