# normative-learner

This downstream project extends the standardized August 8 consolidation at
`../consolidation_aug8/`. The byte-exact pre-standardization input is archived in
both trees, and `FROZEN_INPUT_CHECKSUMS.json` pins the exact current consolidation
documents, sources, tests, and Lean files on which this project depends.

Lead result: a joint finite-interface theorem is proved.  The central new lemma
shows that a compiler-induced reference jump is a difference of two already
bounded prefix payoffs.  Consequently, finitely many consuming book changes give
a computable uniform movement cap once the inherited core, risk, error, and
ordinary-movement hypotheses hold.  Raw holdings need not be norm-bounded, and
movement is not converted into flow money.

The accountable-migration layer now proves a one-step conservative ontology
refinement theorem and implements its finite certificate interface.  Raw old and
shadow states plus a raw certificate are checked by `verify_migration`; the
report derives nine results, entitlement reachability, typed challenge
frontiers, payoff carrier/reference movement, eventual route coverage, authorization
binding, and atomic activation.  The migration layer then supplies one certified
reference jump transition to the existing `NL-J3` joint theorem; it does not
replace or mechanize that theorem.  A Lean-checked revision trilemma shows that a
live distinction cannot be collapsed, preserved exactly, and erased without
residual representation or explicit loss.

A composition layer now builds the first two-step accountable history,
`v_0 -> v_1 -> v_2`, reusing the certified harm refinement as its first span and
merging coercion with preference frustration in its second.  `verify_history`
derives thirteen further results — component verification, snapshot and
activation-chain continuity, the finite fiber-product arena, live-support
coverage, normalized end-to-end lineage, duplicate intermediate paths, composite
relation edges, composite challenge frontiers, authority conservation, inherited
residue, the exact movement ledger, and the retention and collection verdicts.

The lead composition result is negative and load-bearing: **two migrations that
each pass all nine one-step checks need not compose.**  A merge may join an
inherited suspended branch to a live one, and cell-level authority counting
conserves the total while permitting the suspended branch's liveness to be
laundered into the live output.  `CM-N1` states the liveness-monotonicity
condition that excludes this, and `CM-X1` exhibits the minimal one-cell
counterexample.  Four coherent repairs are constructed and compared; the
suspended-lineage repair gives the strongest preservation.  End-to-end reference
movement is `1/6 + 2/15 = 3/10`, derived from raw references and holdings, and
enters `NL-J2` as two jumps with no holdings-norm assumption.  Nothing makes
`v_1` a permanent ontology: after a witnessed terminal disposition its whole
frustration lineage becomes collectable, while the arenas stay retained because
a contract is still outstanding.

A composite-construction layer then asks the sharper question: does a certified
one-step `M_02 : V_0 -> V_2` exist?  It builds one — cells are the connected
components of the lineage graph, so a split that later merges consumes its
common ancestor once; the arena is the fiber product, so a distinction `V_2`
cannot express survives locally as two arena states.  The frozen verifier
accepts it, with composite movement `3/10`.  The result is nonetheless a
two-sided negative: **composite certification and composability are
incomparable.**  A certified composite exists for a history the composition
layer rejects — the composite cannot see an intermediate suspension, because
neither endpoint has one — and an admissible history whose split is terminally
disposed on one branch has no certified composite at all.  Composability is
therefore defined by invariants on all three certificates, never by "the
composite verifier accepts".  The retained distinction is collectable once its
challenge is answered, and then `V_1` leaves no residue in the live arena.

A liveness-transport layer then asks whether `CM-N1` is stronger than necessary.
It is — and it is also weaker than necessary, on a different axis.  Replacing the
single status order by four separately typed per-cell relations (semantic
support, liveness sponsorship, authority sponsorship, burden routing) plus
records scoped to one input or one output shows that the laundering of `CM-X1`
is a **burden-disappearance** failure rather than a liveness-lift failure.  On
the 5,184-cell realizable search space, the provenance-sensitive condition
accepts 902 safe merges `CM-N1` rejects, and rejects 291 cells `CM-N1` accepts —
including a one-input, one-output cell that silently drops an unresolved burden.
The two conditions are incomparable; `CM-N1` conjoined with burden conservation
and authority allocation implies the new one, not conversely.  A merge of
concepts is not a merger of reasons: semantic identification buys no
entitlement, shared ancestry buys no authority, and a response to one question
licenses no other claim.

A local-to-global layer then asks whether per-cell transport plans compose along
normalized ancestry.  **They do not, and the failure is confined to exactly one
of the three resources.**  Liveness sponsorship composes by transitivity of the
liveness order; authority licences compose because the local condition is an
*injection*, and injections compose; unresolved burdens do not, because the local
condition is an *existence* claim about a Boolean bit, and a bit cannot tell one
owed answer from two.  The minimal witness is two cells: merge two burdened
occurrences onto one carrier, then close that carrier with one scoped witness.
Both cells are accepted; two owed answers are discharged by one answer.  A
bounded search over 222,376 two-step burden histories finds 783 such cases and
over 8,400 authority histories finds none.  The repair — carrying the set of
borne burden lineages rather than a bit — rejects exactly those 783 and nothing
else, but the datum is historical rather than intrinsic to one migration, so it
is proposed and not adopted.  `CM-J5` is unchanged.

An answerability-docket layer then supplies the object the burden bit was
liveness in for.  Obligations get identities and live in a separate append-only
docket, not on occurrences; a response is filed as its own object and closes
nothing; discharge requires a certified coverage edge naming *that* obligation.
So one response may legitimately answer several questions — provided its adequacy
for each is separately represented — while two questions that merely share a
carrier stay two questions.  Over 92 scenarios, certified coverage accepts 68
against the rivalrous system's 36, accepts all 8 legitimate shared responses it
rejects, and accepts 0 unsafe closures against the bit system's 24.  Composition
is concatenation of logs, hence associative on the nose.  Concept merger is not
obligation merger, and identification never merges obligations at all.

A case-docket layer then makes the system answer practical questions.  A filed
query creates an identified decision obligation in the ledger; the active book
supplies an exact rational credal interval; a merits ruling requires a
threshold-clearing certificate that is *recomputed* from the interval, not read
off the certificate.  With an empty book (`[0,1]`) no merits verdict exists, and
exactly two accountable options remain — a scheduled default that closes the
obligation procedurally, or a decline that leaves it open and accruing refusal
liability.  A default creates no coverage edge and can never later be cited as
substantive support.  Procedure changes are prospective: a query is governed by
the schedule bound when it arrived, absent an authorized retrospective amendment.
Tariffs here are accounted liabilities, not incentives.

Every ruling is now carried by a typed **adjudication transaction** whose
verifier establishes each identity it asserts: the query it answers, the decision
obligation it addresses, the frozen schedule that governs it, the book version
and interval that support it, the ledger closure and boundary record that realize
it, and the liabilities it creates.  A scheduled default closes through a typed
`ProceduralClosure` — never a substantive withdrawal — and cannot enter the
merits channel, because a merits certificate is constructible only from a real
credal interval and its direction is recomputed rather than read.  Refusal
liability is derived from an explicit clock, so an unruled query cannot be
omitted from the accounting.

An objection-grammar layer replaces family labels with **judge footprints**: each
objection type declares the record tables its judge may read, standard-supplying
book content listed separately from evidence, and the verifier withholds the
verdict from any judge that reads outside its declaration.  Families become
computed equivalence classes, and the computed classification is strictly finer
than the legacy one — it splits three families that differ in what standard they
consult.

A leverage-interval layer then replaces the case docket's *supplied* credal
interval with one **computed from the active book by the statics**: the exact
rational range of the target's probability over the assignments consistent with
the simplex, the pinned settled record, and the book's endorsements, carrying a
primal witness and a dual certificate so recomputation recomputes the program.
A merits verdict is available exactly when the book's leverage on the target
clears the threshold; an empty book recovers the two-option accounting verbatim;
an infeasible book certifies nothing and yields typed sure-loss grounds; and a
default issued where merits was available is visible as record arithmetic.

A case-stream layer then prices demand.  Arrivals enter an intake queue whose
per-date capacity is derived from declared service work; the refusal clock runs
from admission; and accumulated liability draws down a finite account.  Every
date on which an admitted obligation is still open accrues at least one tariff
unit, so bounded liability bounds the dates in arrears — which gives the trilemma:
on any admitted substantive stream, either liability is unbounded, or the
insolvency trigger fires, or the ruling rate clears the stream.  Always-default
escapes the clock but drives the stakes-weighted default rate to its maximum and
becomes objectionable in aggregate; always-decline fails the third branch
outright.  Dropping the solvency coupling or the admission queue each breaks the
result, and both ablations are exhibited.  All of this is accounting: nothing
here claims a tariff changes what anyone does.

Files:

- `JOINT_THEORY.md`: definitions, theorem, proof, exact trace, and sharpness.
- `MIGRATION_THEORY.md`: accountable ontology migration and its collapse boundary.
- `COMPOSITION_THEORY.md`: versioned histories, composable local spans, the
  liveness invariant, and the retention criterion.
- `STANDING_TRANSPORT.md`: the per-cell transport plan, its seven conditions,
  the benchmark cases, and the exact comparison with `CM-N1`.
- `LOCAL_TO_GLOBAL.md`: the end-to-end transport object, the corrected
  accumulated authority bound, and the burden-composition counterexample.
- `ANSWERABILITY_LEDGER.md`: identified obligations, certified response
  coverage, and the ledger conservation and associativity theorems.
- `CASE_DOCKET.md`: queries, procedure schedules, credal merits certification,
  rulings, defaults, and decline.
- `LEDGER.md`: claim/status ledger (`NL-`, `AM-`, `CM-`, and `ST-` namespaces;
  the settlement-interface rows are `NL-SI-*`).
- `OPEN_PROBLEMS.md`: remaining mathematical frontiers.
- `ROUND_REPORT.md`: the current work report, its prediction scores, and
  what the work does not show.
- `FROZEN_INPUT_CHECKSUMS.json`, `DEVIATIONS.md`: upstream pins and downstream hygiene.
- `src/joint.py`, `tests/test_joint.py`: exact-rational instances.
- `src/migration.py`, `tests/test_migration.py`: finite verifier, raw exact trace,
  and typed failure reports.
- `src/composition.py`, `tests/test_composition.py`: version/history layer,
  `compose_migrations`, composite construction (`compose_certificates`,
  `legacy_discharge_report`, `authority_provenance`), the exact two-step trace,
  four repairs, and the naive/blind/repaired composite candidates.
- `src/standing.py`, `tests/test_standing.py`: transport plans,
  `check_transport_plan`, the seven benchmark cases, and the deterministic
  24,336-cell enumeration.
- `src/history.py`, `tests/test_local_to_global.py`: resource-identified global
  transport, associativity, and the bounded adversarial search.
- `src/answerability.py`, `tests/test_answerability.py`: the answerability
  ledger, its seven benchmark examples, and the three-system comparison.
- `src/case_docket.py`, `tests/test_case_docket.py`: the case docket, its
  adjudication protocol, the adjudication transaction, and the case-stream
  liability interface.
- `GRAMMAR.md`, `src/grammar.py`: record tables, judge footprints, computed
  classification, per-table ablation.
- `LEVERAGE_INTERVAL.md`, `src/leverage_interval.py`: the computed credal
  interval, its certificates, and the licensing guard.
- `CASE_STREAM.md`, `src/case_stream.py`: arrivals, admission, capacity, the
  liability trilemma, and the aggregate-default objection.
- `src/settlement_interface.py`, `tests/test_settlement_interface.py`: the
  settlement interface as one formal object — a predicate per clause, each
  checkable over a finite record prefix or carried as a hypothesis object, with
  the trivial reference engine that satisfies the checkable fragment.
- `src/coherence.py`, `tests/test_coherence.py`: the incoherence functional and
  its normalized certificate, the tolerance-robust interval and merits
  certificate, the working-tolerance check, and the certification layering.
- `src/core_geometry.py`, `tests/test_core_geometry.py`: the ambient and
  relative readings of the core condition, the transport lemma, the clipping
  adapter, and the finite-instance sweep over pin trajectories.
- `MOVING_INTERFACE_MAP.md`, `src/parametric_composition.py`,
  `tests/test_parametric_composition.py`: the mapping between the corpus's
  condition bundle and the interface clauses, the composite restated over any
  engine satisfying those clauses, and the instance corollary.
- `src/settlement_channel.py`, `tests/test_settlement_channel.py`: the funded
  empirical channel — request keys, observation procedures, the pin's three
  downstream effects, the clock discipline, the adequacy inequality, and the
  conduct witnesses.
- `src/two_engines.py`, `tests/test_two_engines.py`: the minimal multi-engine
  instance, with the disagreement, breach-isolation, and composed-purse
  witnesses.
- `lean/`: load-bearing movement and revision-trilemma mechanisms.

Verify with:

```sh
python3 tests/run.py
```

Python verification is always run.  Lean is optional and portable: set
`MATHLIB_DIR` to a local Mathlib/Lake project to compile the files
under `lean/`; otherwise the runner reports an explicit Lean skip without
turning a successful Python suite into a failure.

Upstream integrity is checked by the pinned digests in
`FROZEN_INPUT_CHECKSUMS.json`, which are verified on every run and are the
authoritative check.  The runner locates the authoritative consolidation in a
documented order — `CONSOLIDATION_DIR`, then the sibling checkout, then
`authoritative_consolidation.zip` delivered with this package — and verifies the
pinned digests in every case, so the package verifies with no sibling tree
present.  **`consolidation_aug8.zip` is the pre-standardization snapshot and is
not the pinned input**; verifying against it fails, correctly.  The upstream
rename inversion check additionally runs when its manifest's recorded absolute
roots resolve to the trees actually present, and otherwise reports an explicit
skip with the reason.

The strongest warranted interpretation is limited: within a supplied finite
normative interface, represented reasons can acquire capped operative force
while their continued authority remains publicly challengeable and revisable;
one certified conceptual refinement can preserve or explicitly dispose of the
associated deontic score, and two such refinements compose into one answerable
history provided every unanswered question survives the revision attached to
something and no branch acquires liveness it was not sponsored for.  Candidate
ontology generation still conveys no authority, and no intermediate ontology
acquires permanence: it is retained exactly as far as some unresolved position,
challenge, burden, provenance, or authorization record reaches.
