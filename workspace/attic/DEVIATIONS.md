# Deviations and dependency notes

1. The authoritative upstream is the standardized `../consolidation_aug8/`
   tree. Its byte-exact pre-standardization form remains recoverable from the
   archive and rename manifest; this project pins the current upstream bytes in
   `FROZEN_INPUT_CHECKSUMS.json`.
2. `NL-J3` and `AM-J3` remain complete hand derivations, not system-level Lean
   formalizations. Lean checks the jump-range recurrence algebra and the finite
   revision trilemma only.
3. Python verification establishes the displayed rational traces and the finite
   certificate verifier's behavior. It does not prove the general transition
   theorems.
4. The standardization pass changes names and symbols only. Stable claim IDs,
   hypotheses, witnesses, rational values, and proof steps are unchanged.
5. The historical Phase IX/X proposal files named by the author decisions were
   not present in either supplied tree. Their adopted content is recorded in the
   canonical decision ledger and the retained theory instead; no absent file was
   reconstructed.

## Verification behavior change (composition phase)

6. **The upstream rename inversion check is now conditional; the pinned digests are
   not.** `../consolidation_aug8/tools/rename_manifest.json` records the two
   tree roots as absolute machine-specific paths, so the inversion check fails or
   silently checks the wrong tree whenever either project is moved or copied.
   The consolidation is read-only upstream and was not edited to repair this.
   Instead the downstream runner now tests whether the manifest's recorded roots
   resolve to the trees actually present. If they do, the inversion check runs
   unchanged. If they do not, it is skipped with the reason printed, and the run
   is not failed on a path accident. `CONSOLIDATION_DIR` overrides the sibling
   default.
7. **What the skip does and does not cost.** The pinned digests in
   `FROZEN_INPUT_CHECKSUMS.json` are verified on every run, before the
   inversion check is attempted, and the runner now prints how many were checked. A
   missing upstream tree is a hard failure, not a skip. To keep the inversion check
   itself under integrity checking even when it is skipped,
   `tools/rename_manifest.json` was added to the pinned upstream inputs, so a
   changed manifest is detected by digest whether or not it runs.
   What is genuinely lost when it is skipped is the byte-exact invertibility
   claim for the pure-rename files — a claim about a completed historical pass,
   not about the current bytes, which remain pinned.
8. **Superseded post-rename digests are retained, not overwritten.** This phase
   edits five downstream files that the manifest pinned at their post-rename
   bytes (`README.md`, `LEDGER.md`, `OPEN_PROBLEMS.md`, `DEVIATIONS.md`,
   `tests/run.py`). Rather than overwrite the historical digests, each moves to
   a `post_rename_superseded` record carrying both the frozen `post_rename_sha256`
   and the new `current_sha256` together with a reason; the runner checks the
   current digest and requires both fields to be present. The upstream rename
   manifest independently classifies the three theory documents among these as
   contextual, so the inversion check is unaffected by the edits.
9. **New sources are outputs, not frozen inputs.** `COMPOSITION_THEORY.md`,
   `src/composition.py`, and `tests/test_composition.py` are this phase's
   products and are deliberately not pinned; the manifest exists to freeze
   inherited inputs. `src/migration.py`, `src/joint.py`, `tests/test_joint.py`,
   `tests/test_migration.py`, `MIGRATION_THEORY.md`, `JOINT_THEORY.md`, and both
   Lean files are unmodified, and the composition layer imports the one-step
   verifier rather than rewriting it.
10. **Composition claims are hand derivations.** `CM-J0` through `CM-J5`,
    `CM-N1`, and `CM-C1` are proved, conditional, or conjectured exactly as
    their ledger rows state. Python establishes the displayed finite two-step
    history, the four repairs, and the eight refutation witnesses. No `CM-`
    claim is Lean-checked, and `CM-J5` is not verified for histories longer than
    the displayed one.

## Liveness-transport phase

11. **`CM-N1` is reclassified, not weakened.** Its ledger row, status, and
    statement are unchanged, and `CM-J5` still uses it. `STANDING_TRANSPORT.md`
    adds the finding that it is a coarse sufficient condition: incomparable with
    the provenance-sensitive transport condition, implied by it only when
    conjoined with the burden and allocation properties `CM-N1` does not
    express. Nothing that previously passed now fails.
12. **The transport plan is an extension, not an interface change.**
    `src/migration.py` is untouched: no field was added to
    `MigrationCertificate`, `TerminalDisposition`, or `Occurrence`. The
    unresolved-burden bit that a single step lacks is recovered in
    `src/standing.py` by reading the *previous* certificate's suspension
    entries, which is available to a history and not to a step. `ST-C1` states
    the interface revision that would make the check local; it is proposed and
    explicitly not adopted, and its compatibility with existing `AM-` and `CM-`
    claims is unchecked.
13. **One shared symbol was made public.** `composition.STANDING_ORDER` was
    renamed from `_STANDING_ORDER` so the transport module uses the same status
    order rather than defining a second one. No behavior changed; this is a
    downstream file of this project, not frozen upstream material.
14. **Enumeration results are scoped facts, not theorems.** `ST-E1`, `ST-J2`,
    `ST-J5`, `ST-J6`, `ST-J7`, and `ST-N1` are machine-checked over the stated
    finite spaces — cells of at most two inputs and two outputs, three statuses,
    two Boolean bits, and the declared plan family. They are not evidence of
    adequacy for larger cells, other plan vocabularies, or arbitrary histories,
    and the ledger rows say so. `ST-J3` and `ST-J4` are hand derivations from
    the plan conditions and are stated for arbitrary finite cells, but only the
    small shapes are checked.
15. **The realizable sub-scope is reported separately.** The frozen verifier
    forbids terminal occurrences as cell endpoints, so comparisons between
    `CM-N1` and the transport condition are stated over the 5,184 cells without
    terminal endpoints. Over the full 24,336-cell space the predicate remains
    sound but is strictly stronger than the four safety properties on 1,156
    cells, all with terminal endpoints; that difference is disclosed rather than
    scoped away.

## Composite-construction phase

16. **The composite is built, not assumed.** `compose_certificates` constructs a
    real `MigrationCertificate` from `V_0` to `V_2` and submits it to the
    unmodified one-step verifier. No verdict is stored and no expected value is
    hard-coded; the tests recompute movement from the three compilers' raw
    references and holdings, and derive acceptance from the one-step verifier.
17. **Three composition policies, one constructor.** `naive` and `blind` are
    documented degradations of the same builder rather than separate code paths,
    so the comparison isolates one policy difference at a time. `naive` drops
    the relational, challenge, and disposition layers; `blind` composes cells
    pairwise instead of by component.
18. **`authorized-loss` has no certified composite, and that is a result.** The
    history is admissible and both its steps verify; the composite is rejected
    because a branch terminal disposition cannot be carried by a non-terminal
    composite cell. This is reported as a structured obstruction
    (`composite.branch_disposition_unexpressible`), not repaired by relaxing the
    one-step verifier.
19. **No new one-step primitives were added.** `src/migration.py` is still
    untouched. The composite construction reuses `ComparisonArena`,
    `DispositionCell`, `EdgeTransport`, and `constant_on_fibers` as they stand.
    The one interface item this phase would need — a per-branch terminal
    disposition — is already recorded as `ST-C1` item 2 and remains proposed.
20. **Scope of the composite claims.** `CM-J6`, `CM-J7`, `CM-J9`, and `CM-X10`
    are machine-checked on the displayed five-history family and the exact
    rational witnesses; `CM-J8` and `CM-J10` are hand derivations. Nothing is
    claimed for three or more steps, and `CM-J5` is unchanged.

## Local-to-global phase

21. **Package integrity: cause and repair.** The delivered package could not
    verify itself because `consolidation_aug8.zip` is a *pre-standardization*
    snapshot, not the tree `FROZEN_INPUT_CHECKSUMS.json` pins: 5 of the 42 pinned
    files are absent from it and 34 differ in content. Verification against it
    failed correctly. The repair adds `authoritative_consolidation.zip`, an
    archive of the exact pinned tree, pins its own digest, and teaches the runner
    to resolve the consolidation from `CONSOLIDATION_DIR`, then the sibling
    checkout, then that archive. No check was weakened or bypassed: the pinned
    digests are verified in every branch, a missing tree is a hard failure with a
    precise instruction, and the stale snapshot is still rejected. The historical
    zip is retained, unmodified, as provenance and is labelled as such in the
    manifest's `notes`.
22. **`CM-J8` was wrong and is corrected, not deleted.** The pooled-grant display
    asserted `a_1 <= a_0`, which a grant issued at the first step falsifies; the
    implementation also filtered grants against the endpoint occurrence set and
    so discarded every first-step grant. `authority_provenance` is now
    step-indexed and `LG-J0` states the accumulated bound. The grant-free
    corollary is preserved and tested. No previously passing test regressed.
23. **The central result of this phase is negative.** Local transport acceptance
    does not compose. `CM-J5` was **not** rewritten, no prefix
    challenge-frontier condition was shown redundant, and `CM-N1` remains in
    place in the composition theorem.
24. **A composer bug was caught before it became a finding.** An early run
    reported 14 authority obstructions; inspection showed the composer allocated
    licences greedily where the one-cell predicate uses a matching. Those were
    bugs, not obstructions, and the corrected composer reports zero. The episode
    is recorded because the same failure mode would silently manufacture
    counterexamples. The only edit to `src/standing.py` this phase is a public
    alias, `injective_assignment`, so the composer and the one-cell predicate
    share one allocation routine instead of defining two.
25. **`ST-C1` is partially adopted at most, and not yet.** Item 1 (the
    per-occurrence burden bit) is refuted in its bit form by `LG-X1`; its
    corrected set form is `LG-C1`, which is historical rather than intrinsic to a
    single migration and is therefore left in the history layer. Item 2 remains
    justified. Mixed-status many-to-many cells are not required by anything here.
    `src/migration.py` and `StandingTransportPlan` are unchanged.
26. **Enumeration is not proof.** `LG-E1`, `LG-E2`, `LG-J5`, and `LG-J6` are
    machine-checked over stated finite scopes — two-step histories of one cell
    per step, cells up to `(2,2)`, two statuses, one varying bit. `LG-J0` and
    `LG-J2` are hand derivations for arbitrary finite linear histories. No Lean
    mechanization was attempted this phase.

## Answerability-ledger phase

27. **Gate 0 repairs.** The `CM-J8` prose claiming one authority-bearing endpoint
    descendant regardless of grants is corrected to the licence form: one
    inherited licence sponsors at most one endpoint authority, and further
    endpoint authorities need distinct scoped grants. The proof language
    referring to "the two inequalities" now states the one-step bound and its
    telescoping. `OPEN_PROBLEMS.md` no longer says three-step composition is
    untested: associativity is verified on one constructed history and the
    general statement remains unproved. Outcome maps are keyed by
    `(origin version, origin occurrence)`, with a collision test using an
    occurrence name that legitimately repeats at a later version.
28. **Set versus multiset, settled.** The intended object is a finite set of
    *unique obligation identifiers*. As a collection of question contents it is a
    multiset, because distinct obligations may be extensionally identical and
    remain distinct; identity is carried by the identifier, never by the content.
    The text no longer alternates.
29. **The ledger is a separate object, deliberately.** `src/migration.py`,
    `StandingTransportPlan`, and every frozen test are untouched. `AD-C1` records
    the bridge as a proposal. `LG-J5` is **not** promoted: the ledger replaces the
    burden-bit transport rather than repairing it, so its `PROVED-CONDITIONAL`
    status stands.
30. **Fields were admitted only against a failure.** A satisfaction specification
    on the obligation and a terminal-disposition field were both rejected — the
    first because adequacy is parametric and belongs on the coverage edge, the
    second because closure is already an event. The status algebra is three
    statuses with the closure kind in the disposition record, rather than five
    statuses.
31. **Scope discipline.** `AD-J1`, `AD-J4`, and `AD-J5` are hand derivations for
    finite linear singleton-actor histories. `AD-E1` and `AD-E2` are
    machine-checked over stated finite scopes, and the 92-scenario count is not
    evidence for any unbounded claim. No Lean mechanization was attempted.

## Case-docket phase

32. **The rename was behavior-preserving.** `ANSWERABILITY_DOCKET.md`,
    `src/docket.py`, and `tests/test_docket.py` became
    `ANSWERABILITY_LEDGER.md`, `src/answerability.py`, and
    `tests/test_answerability.py`; the API and obstruction codes moved from
    `docket.*` to `ledger.*`. The full suite passed at 134 tests immediately
    after the rename, before any hardening. No compatibility shim was retained
    and no `docket.py` module remains: "docket" now names only the case layer.
    The `AD-` claim namespace was deliberately not churned.
33. **Hardening changed behavior, and the examples were updated to match.**
    Identifier uniqueness for events, responses, coverage edges, and
    obligations; origin bound to the filing event; nondecreasing versions; a
    load-bearing `identification_ref`; and an atomic top-level
    `BoundaryDisposition` replacing the "touched by any event" boundary test.
    A coverage edge and a filed response are explicitly not dispositions.
    Examples A-G were rewritten to satisfy the new rules and their verdicts are
    unchanged; the three-system comparison is unchanged at 92/68/36 with 0
    unsafe and 8 shared.
34. **Identification was made load-bearing rather than removed.** Gate 1.2
    preferred the smaller design, but removing identification would have removed
    the record that says *why* one adequacy argument answers two questions. It is
    now checked: a cited identification must exist and include the obligation,
    and two coverage edges from one response sharing one `adequacy_ref` now
    *require* one. This gives identification a job it did not previously have.
35. **Segment composition is not free-monoid concatenation.** `compose_segments`
    checks identifier freshness across the seam, version monotonicity, that the
    second segment does not act on obligations the first closed, and that no
    reference dangles. Concatenation remains associative; the compatibility
    conditions are the content.
36. **Scope discipline.** `CD-J1`-`CD-J4` are accounting and verifier-safety
    results. No result depends on optimization; tariffs are accounted liabilities
    and no behavioral claim is made. The credal interval is supplied input. The
    canonical liability-key rule `CD-C1` is a design proposal, and the
    schema-rate theorem it would support is not implemented.

## Adjudication-bridge hardening pass

37. **Withdrawal-as-default is withdrawn.** A scheduled default previously closed
    its obligation through `Dispose(kind="withdrawal")`. It now uses the typed
    `ProceduralClosure`, and `Dispose` carries only the substantive kinds
    `withdrawal` and `loss`. The ledger refuses a procedural closure on an
    obligation that already has merits coverage. Any earlier text implying a
    default is a withdrawal is superseded.
38. **Default non-evidence is now intrinsic.** The optional
    `default_is_not_evidence` string-matching helper is **removed**.
    `MeritsCertificate` is constructible only by `certify_merits` from a real
    credal interval, and `verify_transaction` recomputes the threshold direction
    from the interval the book supplied rather than reading the certificate.
39. **Boundary subrecords are now read.** `BoundaryDisposition.subrecords` was
    declared and never checked. Each named record must exist, concern the same
    obligation, occur at the declared version, have the claimed type, and justify
    the outcome; no record may dispose of two obligations. Examples and tests were
    updated where they previously named no subrecords.
40. **Silent map overwrites are closed.** Query, schedule-version, certificate,
    and ruling indices are built through `_unique`, which reports a duplicate
    rather than letting a later entry erase an earlier one.
41. **Refusal accounting is derived, not supplied.** `adjudicate` no longer takes
    a caller-provided `declined_steps` map. It takes `filed_step` and
    `horizon_step` and generates the charge for every unruled well-formed query,
    so an unruled query cannot be omitted. A snapshot (`horizon == filed`) costs
    nothing; a longitudinal horizon is costly in elapsed steps.
42. **The composition contract is exact.** `compose_segments` reports four
    separate clauses — first accepted, seam compatible, second accepted under the
    resulting state, composite accepted — and `accepted` is their conjunction.
    The third clause is the composite fold restricted to the second segment's
    events, and no more is claimed than that.
43. **Scope.** `CD-J5`-`CD-J9` are verifier-safety results and accounting
    identities. None is an incentive, convergence, or learning claim. The
    capacity/rate conjecture in Case Docket §11 is explicitly not proved, and the
    hypotheses it would need are listed there.

## Demand integration phase

44. **Grammar module built first, per D2.** Objection types declare judge
    footprints, never families. Every objection-shaped object in this repository
    is on the interface; upstream catalog types receive declared footprints via
    the mapping table in `GRAMMAR.md` §3, since the pinned consolidation stays
    byte-frozen. No behavioral change to any existing test.
45. **The credal interval is now computed.** `src/leverage_interval.py` computes
    `I_t(q)` from the simplex, the pinned settled record, and the book's
    endorsements by exact vertex enumeration, with a primal witness and an
    active-set dual certificate. Supplied-interval mode remains available as the
    degenerate oracle; every existing `CD-` test passes unchanged, so no
    predecessor was archived and no test behavior was replaced.
46. **A licensing guard was added, and it was not anticipated.** The A5
    adversarial suite showed that an unlicensed target has an all-zero indicator,
    hence probability 0, hence `upper < tau`: the bare arithmetic would certify a
    negative merits verdict for a question the language cannot express.
    `Language.licenses` now gates the computation and `threshold_direction`
    returns nothing for an unlicensed target.
47. **Four ground-rule conflicts are recorded rather than violated.** WP-C1
    requires editing the frozen `src/joint.py`; WP-C5 requires extending the
    read-only upstream rename manifest; D4's "no text may use liveness in the old
    sense" is unachievable because two frozen files contain ten such uses; and
    D1's citation of `REPORT.md` refers to the upstream file, which now collides
    in name with this phase's downstream deliverable. See `DECISIONS_PROPOSED.md`.
48. **WP-C1-C5 were not reached.** The phase specified roughly five to
    ten times a normal phase. Work proceeded in the mandated order and stopped
    where it was still solid. No stub, placeholder, or empty module was created
    for the unreached packages, and no claim row was written for a result that
    does not exist.

49. **One existing test was scoped, not replaced.** `test_case_docket_ledger_is_complete`
    matched every `CD-` identifier in `LEDGER.md`, so the new `CD-L` rows, whose
    anchors live in `LEVERAGE_INTERVAL.md`, made it fail. Its two regexes now
    exclude the `CD-L` namespace, which `tests/test_leverage_interval.py` checks
    two-way instead. No assertion was weakened: both namespaces remain checked in
    both directions, in the file that documents them.

50. **WP-B landed as pure accounting.** `src/case_stream.py` simulates the
    liability record and selects nothing: a `StreamPolicy` is a transcript of what
    the record shows, not a decision rule. Capacity is derived from declared
    service work by division rather than introduced as a new parameter, so no
    book-declared hygiene parameter was added. `CS-N1` and `CS-N2` are necessity
    witnesses per decision D1, and both were written before the positive results
    so the witnesses gate `CS-J1` rather than decorating it.

## Closing phase

51. **T1 lands beside the frozen joint module.** `src/joint_tightening.py`
    imports `movement_recursion` and never redefines it; `src/joint.py` is
    byte-identical. `NL-J2'` cites `NL-J2` and supersedes nothing, per P-4.
52. **T4 reclassification touches rows, not proofs.** 29 `NL-X*`/`AM-X*` rows
    moved from `REFUTED (witness displayed)` to `NECESSITY WITNESS` using
    `consolidation_aug8/REPORT.md` as the source. `AM-X10` is preserved as
    genuinely REFUTED. Frozen documents whose prose still says REFUTED are not
    edited; the mapping is recorded in `tools/rename_manifest_downstream.json`.
53. **T5 is prose-only and protected.** The flip skips code identifiers, file
    references, and inline code spans, so `standing_support`,
    `standing.termination_unscoped`, and `STANDING_TRANSPORT.md` survive as
    fossils alongside the frozen `ST-*` IDs. No test assertion changed.
54. **The downstream roundtrip runs after discovery.** Per P-3,
    `check_downstream_rename` is called only once unittest has reported, so a
    manifest problem can never mask a test result. Its paths are relative.
55. **T6 added one catalog type, which moved GR-J2's counts.** Registering
    `cross-subsidy` took the computed classification from 7 classes to 8 and the
    evidence projection from 6 to 7. `GRAMMAR.md`, the ledger row, and the test
    were updated together; the claim's content is unchanged.
56. **The previous downstream `REPORT.md` is archived, not deleted**, at
    `archive/REPORT_superseded.md` with a manifest entry, per P-1.
57. **T7 Lean was not attempted.** No `MATHLIB_DIR` is available here, and
    unverifiable Lean would violate the rule that external proofs are trusted
    only after compiling.
58. **The quantity `T1` governs is named "incoherence".** The natural word for
    the minimal distance from a price assignment to the coherent ones is on this
    tree's retired-vocabulary list, and the naming gate rejects it in prose. The
    referent stays single: `src/coherence.py::incoherence`, and the phrase
    "prices are epsilon-coherent" everywhere else. The same substitution applies
    to the interface's purse and enforcement clauses, whose two nouns are also
    retired: they are read here as the **downside limit** and the **core
    minimum**. The corpus's core coefficient is written `theta` throughout,
    matching the joint theory rather than the frozen operative-force statement.
59. **The engine's obligation and the book's are measured against different
    sets.** The incoherence functional runs against logic plus pins; the robust
    interval and merits certificate run against book plus pins with the
    tolerance inflation. Conflating them would charge a book breach to the
    engine and toll where it should charge. Both sets are named objects
    (`coherence_polytope`, `docket_polytope`) and the separation carries a
    guard witness, `NL-SI-1B`.
60. **A tolerance never relaxes a pin or the simplex.** Only compiled
    endorsements are relaxed, each after scaling to maximum coefficient
    magnitude one so the same declared tolerance means the same thing on every
    row. Relaxing a pin would let a declared tolerance buy back settled content.
61. **P1 is split into a checkable half and a declared half.** Containment of
    the core homothet is linear in the reference at fixed coefficient, so
    current satisfiability of a declared core minimum is a linear program with a
    declared branch on emptiness. The out-of-tree interface document is **not**
    treated as amended: its P1 text is quoted verbatim in the predicate, and the
    restatement is recorded as a proposed clause revision in `ROUND_REPORT.md`
    for its author to adopt or decline.
62. **The faithfulness axiom is typed, not proved.** The channel's executor
    takes the procedure, the date and the world, so no path from book or purse
    to a pin value can be written in this implementation. That is a disclosure
    about this construction; the axiom quantifies over every engine and is
    untouched. The same applies to the request key's missing outcome field: it
    makes directional funding unconstructible here, not impossible in general.
63. **Three evidence tables and two objection types were added to the grammar.**
    `settlement.requests`, `settlement.pins` and `positions` join the registry,
    and `probe-blackout` and `common-source` join the catalog with declared
    footprints. Upstream catalog types keep their frozen bytes. As with the T6
    addition, this moves the computed classification counts; the grammar claim's
    content is unchanged.
64. **The adequacy window inequality is release-aware.** An earlier form
    summed service work by deadline alone, which is not the feasibility
    condition: the correct window runs from the date a query's downstream
    service may first begin — admission plus upstream horizon — to its deadline.
    The corrected form is what `NL-SI-12` states and what the channel is checked
    against.
65. **The interface and audit documents are inputs, and live outside this tree.**
    Neither was copied in, and neither is modified. The audit's own note gives
    the reason: its central term for the logical residue is retired vocabulary
    here, so the document would fail this tree's naming gate. Clause texts are
    quoted verbatim inside `src/settlement_interface.py`, with the two retired
    nouns bracketed at the point of substitution so the edit is visible.
