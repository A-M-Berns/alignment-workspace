# Theory 9: practical demand — the docket, the stream, and the interval

This part covers what the learner must dispose of, what it costs to decline, and
how the credal interval that supports a disposition is computed. Every symbol
used here is defined here.

Five things stay separate throughout, and conflating any two is the standing
error this layer exists to prevent:

    case demand  !=  answer generation  !=  merits certification
                 !=  practical ruling   !=  operative force

A ruling is not a belief settlement. A default is not a normative belief.
Neither enters the settled record. Nothing here models parties or optimizes
anything: tariffs are accounted liabilities, never incentives.

## 1. The computed interval

Let a finite language, a settled record, and a book be as in Theory 11 §2. The
**feasible set** is the docket polytope; the **credal interval** `I(q)` of a
target `q` is the exact rational minimum and maximum of `q`'s probability over
it.

**The interval is computed, not supplied.** {#CD-L1} **Status: PROVED (single
derivation).** For a finite language at a date, the interval is attained at
vertices of the feasible set and is an exact rational pair, with a primal
witness for each endpoint and multipliers on the active rows reproducing the
objective.

**Proof.** The feasible set is an intersection of finitely many rational
half-spaces with the simplex, hence a bounded polytope, hence the convex hull of
its finitely many vertices. A linear objective on a bounded polytope attains its
extremes at vertices. Each vertex is the unique solution of a square subsystem
of the rows, so enumerating subsystems, solving exactly, and discarding
infeasible solutions produces every vertex; the extremes over that finite set
are the endpoints. The attaining vertex is the primal witness. For the
multipliers, the rows active at an optimal vertex span the objective when the
optimum is attained there, and nonnegative weights on the inequality rows
reproducing the objective certify optimality. `square`

**Merits requires the interval, and separation is strict.** {#CD-J2}
**Status: PROVED (single derivation).** A merits direction exists exactly when
the interval separates the threshold: positive when the lower endpoint is at
least the threshold, negative when the upper endpoint is below it, and otherwise
no merits verdict is available.

**Proof.** If the lower endpoint is at least the threshold then every feasible
state assigns the target at least the threshold, so the positive verdict holds
under every feasible reading of the book. If the upper endpoint is below the
threshold the negative verdict holds likewise. If the threshold lies strictly
inside the interval, both a feasible state above and one below exist, so neither
verdict holds under every feasible reading, and no direction is available.
`square`

**Licensing must be checked, not inferred.** {#CD-L3} **Status: NECESSITY
WITNESS.** A target outside the language fragment has an all-zero indicator, so
its computed probability is exactly zero and the threshold comparison would
certify a *negative* merits verdict on a sentence the book never addressed.

**Witness.** Any language and book, with target `Z` absent from the truth
assignment. The indicator is the zero vector, the interval is `[0,0]`, and for
any threshold in `(0,1)` the direction rule returns negative. The interval
computer therefore reports the target as unlicensed rather than pricing it, and
the direction rule refuses an unlicensed interval. `square`

**Empty-book recovery.** {#CD-L2} **Status: PROVED (single derivation).** With
no endorsements and no settled premise bearing on the target, the interval is
the whole unit interval and no merits direction is available for a threshold
strictly inside it.

**Proof.** The feasible set is the whole simplex, over which the target's
probability ranges from zero — put all mass off the target's worlds, possible
since the target is not identically true — to one, similarly. So the interval is
`[0,1]` and the direction rule returns nothing for a threshold in `(0,1)`.
`square`

This degeneration is the reference point for the tolerance discussion of
Theory 11: a maximal declared tolerance reproduces it at every date.

**Infeasibility is a typed objection against the book.** {#CD-L4}
**Status: PROVED (single derivation).** When the feasible set is empty, the
combination of the settled and endorsed rows witnessing emptiness is grounds for
a sure-loss objection whose respondent is the book.

**Proof.** Emptiness means no credal state satisfies the simplex, the settled
record and the endorsements jointly. The settled record is incorrigible and the
simplex is definitional, so the only revisable content in the conflict is the
endorsements; the objection therefore addresses the book. The witnessing
combination is finite and rational, so it is checkable. `square`

## 2. The docket

A **query** names a claim type and the schedule version bound at its arrival. A
**procedure schedule** carries a threshold, verdict labels, a fallback, and two
tariffs; it is revisable but prospective, and its application to a filed query
is frozen unless an authorized amendment says otherwise. A **ruling** carries a
verdict, a basis tag — merits or default — and the certificates supporting it.

**Default non-evidence is a property of the type.** {#CD-J1} **Status: PROVED
(single derivation).** A merits certificate cannot be manufactured from a ruling
identifier.

**Proof.** A merits certificate is constructible only from an actual interval
together with the query and schedule it answers, and the verifier recomputes the
direction from the interval the active book supplied. A default ruling carries
no interval, so there is no field it could populate to produce one. The property
is therefore structural and not a naming convention. `square`

**Refusal liability is derived from an explicit clock.** {#CD-J8}
**Status: PROVED (single derivation).** With a declared evaluation horizon and a
frozen tariff, the refusal charge is elapsed time times tariff; an
instantaneous snapshot, in which the horizon equals the filing date, carries no
charge.

**Proof.** Elapsed time is the nonnegative part of horizon minus filing. The
charge is that quantity times the frozen tariff, so it is determined by the
record and is not supplied by the party charged. When horizon equals filing the
elapsed time is zero and so is the charge. `square`

**Tolling is subtraction on an existing quantity.** {#CD-J9} **Status: PROVED
(single derivation).** Pausing a clock removes dates from the elapsed term and
therefore reduces the derived charge, without any new primitive.

**Proof.** Immediate from `CD-J8`: the charge depends on the record only through
elapsed dates, so excluding tolled dates from that count is well defined and
lowers the charge by the tariff times the number excluded. `square`

## 3. The stream

Arrivals are admitted through an **intake queue** with a per-date capacity
derived from declared service work; the refusal clock runs from **admission**,
not from filing; fairness is **finite overtaking**.

**No free silence.** {#CS-J1} **Status: PROVED (single derivation).** With a
positive substantive arrival rate, a capacity from declared service work, a
positive refusal tariff and a solvency coupling, persistent substantive silence
is not cost-free: dates in arrears are limited by accumulated liability over the
tariff.

**Proof.** On every date at which something admitted is still open, at least one
tariff unit accrues, by `CD-J8` applied to that date. Hence the number of such
dates is at most the accumulated liability divided by the tariff. If liability
stays limited, arrears are limited, so a stream that never resolves and never
accumulates liability does not exist. `square`

**Necessity of admission.** {#CS-N2} **Status: NECESSITY WITNESS.** Dropping
admission control makes live state unbounded under an adversarial arrival
stream.

**Witness.** Fifty substantive arrivals at date zero with admission bypassed:
every arrival is open from its arrival date, so the open set has fifty members
at date zero, and no per-date capacity limits it. With admission, at most the
declared capacity is admitted per date and the open set is limited at every
date. `square`

**Fairness.** {#CS-J3} **Status: PROVED (single derivation).** Finite-overtaking
admission defers nothing forever.

**Proof.** An arrival is admitted once every earlier-queued arrival ahead of it
has been admitted. With a positive per-date capacity, the number ahead strictly
decreases each date, so admission occurs after finitely many dates. `square`

**The liability trilemma.** {#CS-J2} **Status: PROVED (single derivation).** On
every admitted substantive stream at least one holds: liability exceeds any
declared limit; the solvency coupling triggers; or everything admitted is
resolved and nothing is never-admitted.

**Proof.** Suppose the third fails: something is open at the end or something
was never admitted. If something is open, `CS-J1` accrues tariff on every date
it remains open, so liability grows without limit unless the horizon is finite,
in which case liability is at least the accrued amount; if that exceeds the
declared limit the first holds, and if the coupling's account is drawn below
zero the second holds. If something was never admitted the queue is
non-empty at the horizon, which by `CS-J3` means capacity was exhausted every
date, so the open set was full every date and the same accrual applies.
`square`

**Fenced accounts and cross-subsidy.** {#CS-J5} **Status: PROVED (single
derivation).** A transfer crosses a declared fence exactly when one endpoint is
inside it and the other is not; a pooled system declares no fence and nothing
crosses.

**Proof.** The definition is the exclusive-or of the two endpoint memberships,
which is decidable from the declaration. When no fence is declared the predicate
is false by definition, so the objection is vacuous rather than universal.
`square`


## Transcribed rows: the source ledger's remaining claims

The rows below complete the consolidation's discard test for this layer. They
are **transcriptions**, carried folder-locally from the source tree's own claim
ledger during the completing pass: no new mathematics, no reinterpretation, and
no status change to any claim already stated above. Each carries its hypotheses,
its conclusion, and — for a drop-contract or necessity row — the witness the
source displayed, so the instance is readable here rather than only named.

Two conventions apply throughout this section. Where the source recorded a
status of a compound form, the status here is the plain mandated one and the
qualifier is carried in the ledger's verification column as provenance: the
mandated vocabulary of this package has no compound forms, and the qualifier
describes how the source established the claim rather than what its status is.
And where the source's verification pointer names a file of the source tree,
that pointer is recorded as historical provenance only — it is **not** evidence
a reader of this package can follow, and the folder-local evidence for a
transcribed row is the displayed witness itself.

**default non-laundering.** {#CD-J3} **Status: PROVED (single derivation).** it creates no coverage edge, alters no interval, enters no settled record, and cannot later be cited as merits support

*Hypotheses.* a default ruling in history

*Necessity / sharpness.* a two-query history attempting the citation is rejected with a structured obstruction

**prospective procedure.** {#CD-J4} **Status: PROVED (single derivation).** later changes to threshold, fallback, or tariffs do not govern it absent an authorized retrospective amendment naming query, versions, and consequence

*Hypotheses.* a query bound to a schedule version at arrival

*Necessity / sharpness.* rejected even when the new schedule would make a desired merits ruling available

**adversarial suite.** {#CD-E1} **Status: MACHINE-CHECKED (stated finite scope).** the displayed verdicts, computed from raw inputs

*Hypotheses.* the fifteen finite scenarios of Case Docket §4

*Witness.* finite instances only; no general claim

**transaction completeness.** {#CD-J5} **Status: PROVED (single derivation).** it exhibits one live query, the unique decision obligation for it, and a ruling for that query under the bound schedule version, with every named ledger record checked

*Hypotheses.* an accepted adjudication transaction

*Necessity / sharpness.* a verifier-safety result, not a representation theorem over all adjudications

**basis coherence.** {#CD-J6} **Status: PROVED (single derivation).** ruling basis, certificate or fallback, ledger closure kind, boundary outcome, and liability treatment agree; every cross-basis pairing is rejected

*Hypotheses.* an accepted transaction

*Necessity / sharpness.* eleven single-field mutations rejected, each isolating one invariant

**boundary faithfulness.** {#CD-J7} **Status: PROVED (single derivation).** each exists, concerns the same obligation, occurs at the declared version, has the claimed type, and justifies the outcome; no record disposes of two obligations

*Hypotheses.* a boundary disposition naming subrecords

*Necessity / sharpness.* previously `subrecords` was declared and never read

**merits evasion is record-visible.** {#CD-L5} **Status: PROVED (single derivation).** the fact is arithmetic and yields typed grounds; priced, never forbidden

*Hypotheses.* a ruling with basis `default` whose bound interval cleared tau

*Necessity / sharpness.* the degenerate coinciding-direction case is stated: the objection asserts wrong basis, not wrong verdict

**aggregate default.** {#CS-J4} **Status: PROVED (single derivation).** every obligation terminates and no refusal accrues, yet the stakes-weighted default rate reaches its maximum and yields filable grounds

*Hypotheses.* always-default on a substantive stream; a book-declared rate bound

*Necessity / sharpness.* single defaults stay procedurally defended; the aggregate pattern is what is objectionable; the window is book content, not canonical

**necessity of the solvency coupling.** {#CS-N1} **Status: NECESSITY WITNESS.** liability accrues and nothing follows: the trigger never fires and no trilemma branch closes

*Hypotheses.* drop the coupling; hold arrivals, capacity, and tariffs

*Witness.* shows the link to the bounded-force machinery is a real hypothesis

## 4. What this part does not establish

Nothing here is an incentive claim. The tariffs price silence; they do not
predict that anyone speaks. `CS-J2` is a disjunction over the record, not a
statement about anyone's policy. Schema-level demand rates — how demand scales
with the schema set rather than with arrivals — are not treated and are carried
in `OPEN_PROBLEMS.md`.
