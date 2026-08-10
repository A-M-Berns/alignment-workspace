# The objection grammar: tables and judge footprints

## 0. What decision D2 changes

An objection type declares no family.  It declares a **judge footprint**: the
record tables its judge may read, with standard-supplying book content and
evidence tables listed separately.  The verifier enforces the declaration; a
judge that reads an undeclared table fails the check.  Families are computed
equivalence classes of footprints and are never stored.

## 1. Finiteness discipline

The table registry is a fixed finite set.  Every objection type declares a finite
footprint over it.  Grounds carry a finite disposition-reference depth bounded by
an explicit cap (`DEFAULT_DEPTH_CAP = 2`).  Every judge is a total function of
the finitely many tables it declares, and a judge that raises is recorded as
failing rather than passing.  Ablation and judgement allocate nothing that grows
with date, so no unbounded live state is introduced.  All arithmetic is exact.

## 2. The registry

Thirteen named tables, each typed `standard` (supplies the standard a judge
applies) or `evidence`: `book.endorsements`, `book.declared_rates`,
`schedule.procedure` (standard); `settled.record`, `rulings`,
`ledger.obligations`, `ledger.coverage`, `liabilities`, `region`, `arrivals`,
`settlement.requests`, `settlement.pins`, `positions` (evidence).

The last three are the settlement surface: funded requests with their blackout
windows, the pins with the funding profile recorded per pin, and the positions
actors took by date.  They are evidence and never standard-supplying — no judge
applies a standard *drawn from* the settled record, which is the reports-only
jurisdiction showing up in the registry's typing.

A footprint that names an unregistered table, declares a table under the wrong
kind, or lists one table as both, is rejected statically by `check_footprint`.

## 3. Upstream footprint mapping table

The pinned consolidation stays byte-frozen, so upstream catalog types receive
their footprints here.  This is a **declared mapping under checksum discipline**,
not a proposal hedge: the declarations below are the authoritative footprints for
those types in this repository.

| type | origin | standard tables | evidence tables | declared legacy family | source |
|---|---|---|---|---|---|
| `frequency` | upstream | `book.endorsements` | `settled.record` | calibration | Theory 5 §C-ADDRESS |
| `calibration` | upstream | `book.endorsements` | `settled.record` | calibration | Theory 5 |
| `exposure` | upstream | — | `region` | coherence | Theory 5 |
| `address` | upstream | `book.endorsements` | — | repair | Theory 5 §C-ADDRESS |
| `coverage` | upstream | — | `ledger.coverage`, `ledger.obligations` | repair | Theory 5 route coverage |
| `persistence` | upstream | — | `ledger.obligations` | answerability | Glossary "persistence of an unaddressed objection" |
| `sure-loss` | this phase | `book.endorsements` | — | coherence | CD-L3 |
| `merits-evasion` | this phase | `schedule.procedure` | `rulings` | answerability | CD-L5 |
| `aggregate-default` | this phase | `book.declared_rates` | `rulings` | answerability | CS-J4 |
| `cross-subsidy` | this phase | — | `liabilities` | coherence | T6 patron fence |
| `probe-blackout` | settlement interface | — | `settlement.requests`, `positions` | answerability | interface F3 |
| `common-source` | settlement interface | — | `settlement.pins` | calibration | interface F4 |

**A correction to the phase's premise.** The prompt refers to a "legacy
six-family scheme".  The pinned consolidation does **not** enumerate one in
machine-readable form: `GLOSSARY.md` records only the rename row
the pre-standardization grammar/family term to `objection grammar/family`, and `THEORY_5`'s table is a
*claim*-family table about stock versus flow semantics, not an objection
catalog.  The legacy column above is therefore a reconstruction declared here,
with four families, not an upstream artifact.  `GR-J2` is stated against that
declared assignment and its scope says so.

## 4. Claims

**Enforcement soundness.** {#GR-J1}
**Status: PROVED (single derivation).** Every table read is recorded before the
value is returned, including membership probes; after the judge returns, any
recorded name outside the declaration produces
`grammar.undeclared_table_read` and the verdict is withheld (`upheld` is `None`).
A judge that raises produces `grammar.judge_failed` rather than a pass.

**Proof.** `RecordAccess.read` and `.available` append to the access log on every
call, so the log is a superset of the names the judge used; the check is set
difference against a finite declaration. `square`

Machine-checked by the mutation suite: one leaky judge per registered table, of
which exactly the declared one is accepted.

**The recovered classification.** {#GR-J2}
**Status: MACHINE-CHECKED (stated finite scope).** Over the twelve types, the
computed footprint classification has **10** classes; the declared legacy
assignment has **4**; the evidence-table projection has **9**.  The computed
classification does **not** reproduce the legacy families: it now splits **all
four** of them — `{cross-subsidy, exposure, sure-loss}`, `{address, coverage}`,
`{aggregate-default, merits-evasion, persistence, probe-blackout}` and
`{calibration, common-source, frequency}` — in each case because the members
differ in their standard-supplying reads while agreeing or nearly agreeing on
evidence.  The two settlement types are what took the calibration family from
intact to split: they read the settlement surface and supply no standard, where
`frequency` and `calibration` both read `book.endorsements` as standard.

Scope: the twelve types of §3 under the declared legacy assignment.  Per decision
P-5 that four-family assignment is **the declared comparison baseline going
forward**: no machine-readable upstream catalog exists, so the reconstruction is
the authoritative referent of this claim.

**Depth-cap re-attachment.** {#GR-J3}
**Status: PROVED (single derivation).** The cap attaches to grounds that
reference dispositions, not to a family.  A type declaring
`references_dispositions` is rejected when `grounds.depth` exceeds the cap; a
type not declaring it is rejected when its grounds carry disposition references
at all.

**Per-table ablation necessity.** {#GR-N1}
**Status: MACHINE-CHECKED (stated finite scope).** Dropping `rulings` makes
exactly its declared readers — `merits-evasion` and `aggregate-default` —
unable to judge, and changes `merits-evasion`'s verdict from upheld to not
upheld; `persistence`, which never declared it, is unaffected.  Dropping
`book.endorsements` blinds `sure-loss` in the same way.  Ablation is therefore
**per table**, which supersedes the per-family formulation.

## 5. The adequacy conjecture, per table

**Restated, and not proved.** The pre-D2 formulation asked whether the family
catalog is adequate.  The per-table formulation is: *for each registered table,
is there an entitlement failure that becomes invisible when it is dropped?*
`GR-N1` answers this affirmatively for `rulings` and `book.endorsements`.  The
remaining eight tables have no ablation witness in this phase, and the general
conjecture — that every registered table is necessary, and that the registry is
complete — is **open**.  A registry that is unnecessary in part is harmless; one
that is incomplete is not, and nothing here bounds that.
