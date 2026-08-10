# Theory 7: the objection grammar

This part fixes what an objection type is, what its judge may read, and what the
verifier enforces. It replaces a family-labelled scheme with a footprint-typed
one. Every symbol used here is defined here.

## 1. Definitions

A **record table** is a named, finite store. The **registry** is a fixed finite
set of table specifications, each typed **standard** — it supplies the standard
a judge applies — or **evidence**. The registry of this package has thirteen
tables: three standard (`book.endorsements`, `book.declared_rates`,
`schedule.procedure`) and ten evidence (`settled.record`, `rulings`,
`ledger.obligations`, `ledger.coverage`, `liabilities`, `region`, `arrivals`,
`settlement.requests`, `settlement.record`, `positions`).

A **judge footprint** is a pair of finite table-name lists, the standard-
supplying and the evidence reads a judge is permitted. **Grounds** are what is
filed: an identifier, a finite payload, a finite list of disposition references,
and a depth. An **objection type** is an identifier, a footprint, a judge — a
function of a reader and grounds returning a truth value — and a flag saying
whether it may reference dispositions.

An objection type **declares no family**. Families, where useful for reporting,
are the computed equivalence classes of footprints and are never stored.

An **access log** records every table name a judge asks for, including
membership probes: knowing a table is absent is a read.

## 2. Enforcement

**Enforcement soundness.** {#GR-J1} **Status: PROVED (single derivation).**
Every table read is recorded before its value is returned; after the judge
returns, any recorded name outside the declaration withholds the verdict; and a
judge that raises is recorded as failing rather than passing.

**Proof.** The reader appends to the log on every call, including the membership
probe, before returning, so the log is a superset of the names the judge used.
The check is set difference of the log against a finite declaration, so it is
decidable and total. A judge that raises is caught, its exception recorded as an
obstruction, and the verdict left absent; since a verdict is reported only when
no obstruction was raised, a raising judge cannot be recorded as upholding.
`square`

**Static well-formedness.** {#GR-J3} **Status: PROVED (single derivation).** A
footprint naming an unregistered table, declaring a table under the wrong kind,
or listing one table as both, is rejected before any judge runs; and the
disposition depth cap attaches to grounds that reference dispositions rather
than to a family.

**Proof.** Each condition is a finite membership or equality test against the
fixed registry, evaluated before the judge is invoked. For the cap: a type
declaring disposition references is rejected when the grounds' depth exceeds the
cap, and a type not declaring them is rejected when its grounds carry references
at all. Both tests read only the grounds and the declaration, so neither depends
on a family label. `square`

## 3. The computed classification

**The computed classification does not reproduce the declared legacy families.**
{#GR-J2} **Status: MACHINE-CHECKED (stated finite scope).** Over the twelve
types of this package's catalog, the computed footprint classification has ten
classes, the declared legacy assignment has four, and the evidence-table
projection has nine. The computed classification splits **all four** legacy
families.

**Scope and provenance.** The four-family legacy assignment is a reconstruction
declared in this monograph, not an upstream artifact: the previous consolidation
enumerates no machine-readable family catalog. This claim is stated against that
declared assignment and its scope says so.

**What splits, and why.** `{cross-subsidy, exposure, sure-loss}` splits because
its members differ in their standard-supplying reads while agreeing on evidence;
`{address, coverage}` likewise; `{aggregate-default, merits-evasion,
persistence, probe-blackout}` likewise. The fourth family,
`{calibration, common-source, frequency}`, splits because the settlement type
reads the settlement record and supplies no standard, where the other two both
read the endorsement table as standard. The two settlement types are what took
that family from intact to split.

## 4. Registry adequacy

**Per-table ablation.** {#GR-N1} **Status: MACHINE-CHECKED (stated finite
scope).** For a registered table, removing it from the tables offered leaves
every type not declaring it still accepted, and makes every type declaring it
lose its judgement.

**Scope, stated as a limitation.** Ablation gives witnesses for the tables the
displayed grounds exercise, not for all thirteen. Registry **completeness** —
that no judge needs a table the registry lacks — is not established here and is
carried in `OPEN_PROBLEMS.md` as the highest-priority open item of this layer:
an incomplete registry is the one gap that would make a footprint declaration
unsound rather than merely coarse.

## 5. What this part does not establish

The verifier enforces declarations; it does not certify that a declaration is
the right one. Whether the registry is complete is open. The legacy assignment
is a declared comparison baseline, and `GR-J2` is a statement about that
baseline rather than about any upstream catalog.
