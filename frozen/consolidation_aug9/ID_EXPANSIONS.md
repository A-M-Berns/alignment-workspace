# Claim-ID expansions

Every claim-ID family used in this monograph, what its letters stand for, where
its claims live, and where the family came from. Identifiers are retained across
the consolidation rather than renumbered, so that the reclassification history
stays traceable; nothing in a claim's content depends on its letters.

| family | expansion | part | provenance |
|---|---|---|---|
| `GR-` | **g**rammar **r**esult | Theory 7 | the objection-grammar layer of the source tree |
| `AM-` | **a**ccountable **m**igration | Theory 8 | the migration layer |
| `CM-` | **c**omposition of **m**igrations | Theory 8 | the composition layer |
| `ST-` | **s**tanding **t**ransport | Theory 8 | the transport layer; its lowercase prose term was flipped to *liveness* in the source tree and the identifiers were frozen as fossils |
| `AL-` | **a**nswerability **l**edger | Theory 8 | this package's family for the ledger layer, used by the claims stated before the completing pass |
| `AD-` | **a**nswerability **d**ocket-ledger | Theory 8 | the source tree's own family for the same layer, retained on the rows transcribed in the completing pass |
| `LG-` | **l**ocal-to-**g**lobal | Theory 8 | the local-to-global transport layer |
| `CD-` | **c**ase **d**ocket | Theory 9 | the docket and adjudication layer |
| `CS-` | **c**ase **s**tream | Theory 9 | the arrivals, admission and demand layer |
| `NL-` | **n**ormative **l**earner | Theory 10 | the joint-composition layer |
| `NL-SI-` | normative learner, **s**ettlement **i**nterface | Theory 11, Theory 12 | the settlement-interface era |
| `C-` | corpus claim | *not used here* | the previous consolidation's own families, authoritative in its vendored parts and never restated under this package's identifiers |

### A two-family overlap, recorded rather than repaired

The ledger layer carries **two** families. `AL-` is this package's own, used by
the four claims stated in the first consolidation pass; `AD-` is the source
tree's, retained on the rows transcribed in the completing pass. Two source rows
were already restated under the first family and are not duplicated: the source's
ledger-conservation row is this package's `AL-J1`, and its ledger-associativity
row is `AL-J3`. Every other `AD-` row is transcribed under its own identifier.

Renaming one family into the other would have meant either renumbering claims
already stated — which the completing pass forbids — or silently rewriting
source identifiers. The overlap is therefore recorded here and in the
reconciliation table of `COMPLETING_PASS_REPORT.md`.

## Suffix conventions

| suffix | reading |
|---|---|
| `-J<n>` | a positive result of the family, numbered in the order it entered |
| `-L<n>` | a lemma-level positive result, usually a computation |
| `-N<n>` | a **necessity witness**: an instance showing a named condition cannot be dropped |
| `-X<n>` | a drop-contract result: what fails when a hypothesis is removed |
| `-P<n>` | a property of a defined object, as distinct from a theorem about a process |
| `-A<n>` | a result about the core condition's geometry |
| `-C<n>` | a result about the incoherence functional |
| `-T<n>` | a result about the tolerance clauses |
| `-K<n>` | a result about the constructed channel |
| `-E<n>` | a result about the multi-engine instance |
| `-M<n>` | a result about the correspondence with the previous consolidation's bundle |
| `-AD<n>` | a result about the adequacy inequality |
| `-X<n>` (in `NL-SI-`) | a result about the parametric composite |
| `<id>-B`, `<id>-C`, `<id>-CAP`, `<id>-T` | a companion to the named claim, stated separately because its status or scope differs |

Two suffix letters are reused across families with different readings — `X` is
a drop-contract marker in `NL-` and a composite marker in `NL-SI-`, and `T`
marks tolerance in `NL-SI-` and the tightening in `NL-J3-T`. The families are
disjoint, so no identifier is ambiguous; the reuse is recorded here rather than
repaired, because renumbering would break traceability for no mathematical gain.

## Reclassification history, carried

The source tree reclassified twenty-nine `NL-X*` and `AM-X*` rows from
`REFUTED (witness displayed)` to `NECESSITY WITNESS`, on the ground that a
displayed instance showing a condition cannot be dropped is a *necessity
witness* for that condition, not a refutation of the surrounding theory. One row
was preserved as genuinely refuted: `AM-X10`, which refutes the proposal that a
migration may create authorization for content it introduces, and whose repair
is enforced in composition.

This package adopts the reclassified vocabulary as canonical. `NECESSITY
WITNESS` is a first-class status here, carried by twelve rows. The history is
recorded, not re-litigated: no row's *content* changed in the reclassification,
only the word naming what its witness shows.
