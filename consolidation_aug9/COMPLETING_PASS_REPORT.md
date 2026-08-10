# Completing pass report

Two phases, strictly ordered. Phase 1 closed the consolidation's discard-test
gap with the source tree treated as read-only evidence. Phase 2 reset the tree
as a disposable forward workspace. This report covers both.

## Phase 1 — the reconciliation

The source tree's ledger carries **134** four-layer rows, not the 133 the
previous report stated. The earlier figure was wrong: it came from a regular
expression that missed the local-to-global and answerability-ledger namespaces
while counting some section prose as rows. The exact figure is parsed from the
ledger's tables and is reproduced row by row below.

Every row is dispositioned exactly once, and the arithmetic closes:

| disposition | count |
|---|---|
| already-restated at first freeze | 38 |
| restated in this pass | 93 |
| deviation, quarantined verbatim in `DEVIATIONS_ANNEX.md` | 3 |
| **total** | **134** |

### Status mapping

The source uses two compound status forms the mandated vocabulary does not
have. They are mapped, and the qualifier is preserved rather than dropped:

| source status | mapped to | where the qualifier went |
|---|---|---|
| `PROVED+MACHINE-CHECKED` | `PROVED (single derivation)` | the ledger's verification column, as provenance |
| `PROVED+INDEPENDENTLY-REDERIVED` | `PROVED (single derivation)` | the ledger's verification column, as provenance |
| `CONJECTURE (not proved)` | *not mapped* | the row is a deviation: promoting a conjecture to a claim is forbidden |

`PROPOSED (interface revision)` was already in the mandated vocabulary but no
claim had used it; the runner's status pattern was extended to accept it. Every
other source status maps to itself.

### The 134 rows

| # | source row | claim | layer | disposition | folder-local id |
|---|---|---|---|---|---|
| 1 | `NL-E1` | exact two-date joint trace | Theory 10 | restated-this-pass | NL-E1 |
| 2 | `NL-J0` | joint-certificate decidability | Theory 10 | restated-this-pass | NL-J0 |
| 3 | `NL-J1` | reference jump payoff-range lemma | Theory 10 | already-restated | NL-J1 |
| 4 | `NL-J2` | finite reference jump cap | Theory 10 | already-restated | NL-J2 |
| 5 | `NL-J2'` | tightened movement cap | Theory 10 | already-restated | NL-J2P |
| 6 | `NL-J2'-B` | attained-optimum companion | Theory 10 | already-restated | NL-J2P-B |
| 7 | `NL-J3` | joint finite reason-governed process theorem | Theory 10 | already-restated | NL-J3 |
| 8 | `NL-J4` | typed liability decomposition | Theory 10 | restated-this-pass | NL-J4 |
| 9 | `NL-N-J2a` | core condition is load-bearing | Theory 10 | already-restated | NL-N-J2A |
| 10 | `NL-X1` | proposal-bypass witness | Theory 10 | restated-this-pass | NL-X1 |
| 11 | `NL-X10` | duplicate-channel witness | Theory 10 | restated-this-pass | NL-X10 |
| 12 | `NL-X11` | market-priority interference witness | Theory 10 | restated-this-pass | NL-X11 |
| 13 | `NL-X12` | reusable-crossing witness | Theory 10 | restated-this-pass | NL-X12 |
| 14 | `NL-X13` | finite-change-only movement cap | Theory 10 | restated-this-pass | NL-X13 |
| 15 | `NL-X14` | quote-before-activation witness | Theory 10 | restated-this-pass | NL-X14 |
| 16 | `NL-X15` | late-account-assignment witness | Theory 10 | restated-this-pass | NL-X15 |
| 17 | `NL-X16` | suspension-jump boundary | Theory 10 | restated-this-pass | NL-X16 |
| 18 | `NL-X17` | service-inadequacy witness | Theory 10 | restated-this-pass | NL-X17 |
| 19 | `NL-X18` | uncertified-compiler activation witness | Theory 10 | restated-this-pass | NL-X18 |
| 20 | `NL-X2` | unrecorded-movement witness | Theory 10 | restated-this-pass | NL-X2 |
| 21 | `NL-X3` | shared-reward-scalar obstruction | Theory 10 | restated-this-pass | NL-X3 |
| 22 | `NL-X4` | funding-to-authorization obstruction | Theory 10 | restated-this-pass | NL-X4 |
| 23 | `NL-X5` | compiled-suspension witness | Theory 10 | restated-this-pass | NL-X5 |
| 24 | `NL-X6` | expansion-stable suspension | Theory 10 | already-restated | NL-X6 |
| 25 | `NL-X7` | pooled protected-trace witness | Theory 10 | restated-this-pass | NL-X7 |
| 26 | `NL-X8` | geometry-only repair obstruction | Theory 10 | restated-this-pass | NL-X8 |
| 27 | `NL-X9` | no-disposition obstruction | Theory 10 | restated-this-pass | NL-X9 |
| 28 | `GR-J1` | enforcement soundness | Theory 7 | already-restated | GR-J1 |
| 29 | `GR-J2` | recovered classification | Theory 7 | already-restated | GR-J2 |
| 30 | `GR-J3` | depth-cap re-attachment | Theory 7 | already-restated | GR-J3 |
| 31 | `GR-N1` | per-table ablation necessity | Theory 7 | already-restated | GR-N1 |
| 32 | `AD-C1` | ledger bridge to the migration certificate | Theory 8 | restated-this-pass | AD-C1 |
| 33 | `AD-E1` | benchmark examples | Theory 8 | restated-this-pass | AD-E1 |
| 34 | `AD-E2` | three-system comparison | Theory 8 | restated-this-pass | AD-E2 |
| 35 | `AD-J1` | ledger conservation | Theory 8 | already-restated | AL-J1 |
| 36 | `AD-J4` | ledger associativity | Theory 8 | already-restated | AL-J3 |
| 37 | `AD-J5` | identification need not merge obligations | Theory 8 | restated-this-pass | AD-J5 |
| 38 | `AD-X2` | one witness answers one obligation | Theory 8 | restated-this-pass | AD-X2 |
| 39 | `AD-X3` | ledger conservation implies frontier coverage | Theory 8 | restated-this-pass | AD-X3 |
| 40 | `AM-E1` | exact harm-refinement trace | Theory 8 | restated-this-pass | AM-E1 |
| 41 | `AM-J0` | occurrence-cell conservation | Theory 8 | restated-this-pass | AM-J0 |
| 42 | `AM-J1` | finite migration verifier | Theory 8 | already-restated | AM-J1 |
| 43 | `AM-J2` | migration reference-jump theorem | Theory 8 | restated-this-pass | AM-J2 |
| 44 | `AM-J3` | one-step accountable migration theorem | Theory 8 | already-restated | AM-J3 |
| 45 | `AM-J4` | local discrepancy composition | Theory 8 | already-restated | AM-J4 |
| 46 | `AM-N1` | finite revision trilemma | Theory 8 | restated-this-pass | AM-N1 |
| 47 | `AM-X1` | preserved claim/lost ancestry | Theory 8 | restated-this-pass | AM-X1 |
| 48 | `AM-X10` | universal-arena underdetermination | Theory 8 | already-restated | AM-X10 |
| 49 | `AM-X11` | duplicate disposition cells | Theory 8 | restated-this-pass | AM-X11 |
| 50 | `AM-X12` | partial activation | Theory 8 | restated-this-pass | AM-X12 |
| 51 | `AM-X13` | late burden reassignment | Theory 8 | restated-this-pass | AM-X13 |
| 52 | `AM-X14` | incomplete rollback | Theory 8 | restated-this-pass | AM-X14 |
| 53 | `AM-X15` | disclosure-as-loss-authorization | Theory 8 | restated-this-pass | AM-X15 |
| 54 | `AM-X16` | split authority duplication | Theory 8 | restated-this-pass | AM-X16 |
| 55 | `AM-X17` | asserted eventual route coverage | Theory 8 | restated-this-pass | AM-X17 |
| 56 | `AM-X2` | split challenge orphan | Theory 8 | restated-this-pass | AM-X2 |
| 57 | `AM-X3` | merged incompatibility loss | Theory 8 | restated-this-pass | AM-X3 |
| 58 | `AM-X4` | changed outstanding payoff | Theory 8 | restated-this-pass | AM-X4 |
| 59 | `AM-X5` | preactivation force | Theory 8 | restated-this-pass | AM-X5 |
| 60 | `AM-X6` | inexpressibility-as-discharge | Theory 8 | restated-this-pass | AM-X6 |
| 61 | `AM-X7` | duplicate loss entry | Theory 8 | restated-this-pass | AM-X7 |
| 62 | `AM-X8` | coupling-as-authorization | Theory 8 | restated-this-pass | AM-X8 |
| 63 | `AM-X9` | lossless collapse | Theory 8 | restated-this-pass | AM-X9 |
| 64 | `CM-C1` | retention and collection criterion | Theory 8 | deviation | annex |
| 65 | `CM-E1` | exact two-step harm history | Theory 8 | restated-this-pass | CM-E1 |
| 66 | `CM-J0` | administrative continuity | Theory 8 | already-restated | CM-J0 |
| 67 | `CM-J1` | finite composition verifier | Theory 8 | already-restated | CM-J1 |
| 68 | `CM-J10` | composite movement subadditivity | Theory 8 | restated-this-pass | CM-J10 |
| 69 | `CM-J2` | fiber-product live-support criterion | Theory 8 | already-restated | CM-J2 |
| 70 | `CM-J3` | lineage normalization | Theory 8 | restated-this-pass | CM-J3 |
| 71 | `CM-J4` | composite movement additivity | Theory 8 | restated-this-pass | CM-J4 |
| 72 | `CM-J5` | local-span composition theorem | Theory 8 | already-restated | CM-J5 |
| 73 | `CM-J6` | component composite migration | Theory 8 | restated-this-pass | CM-J6 |
| 74 | `CM-J7` | composite certification is incomparable with composability | Theory 8 | restated-this-pass | CM-J7 |
| 75 | `CM-J8` | no double authority | Theory 8 | restated-this-pass | CM-J8 |
| 76 | `CM-J9` | legacy discharge | Theory 8 | restated-this-pass | CM-J9 |
| 77 | `CM-N1` | liveness monotonicity | Theory 8 | restated-this-pass | CM-N1 |
| 78 | `CM-X1` | component validity is not composite validity | Theory 8 | restated-this-pass | CM-X1 |
| 79 | `CM-X10` | a composite accounts for its history | Theory 8 | restated-this-pass | CM-X10 |
| 80 | `CM-X2` | naive lossless collapse | Theory 8 | restated-this-pass | CM-X2 |
| 81 | `CM-X3` | locally adequate arena | Theory 8 | restated-this-pass | CM-X3 |
| 82 | `CM-X4` | self-consistent activation records chain | Theory 8 | restated-this-pass | CM-X4 |
| 83 | `CM-X5` | one token authorizes two migrations | Theory 8 | restated-this-pass | CM-X5 |
| 84 | `CM-X6` | stored expected output launders a certificate | Theory 8 | restated-this-pass | CM-X6 |
| 85 | `CM-X7` | challenge follows one descendant | Theory 8 | restated-this-pass | CM-X7 |
| 86 | `CM-X8` | states may be edited between migrations | Theory 8 | restated-this-pass | CM-X8 |
| 87 | `CM-X9` | blind composition preserves ancestry | Theory 8 | restated-this-pass | CM-X9 |
| 88 | `LG-C1` | revised burden interface | Theory 8 | restated-this-pass | LG-C1 |
| 89 | `LG-E1` | bounded local-to-global search | Theory 8 | restated-this-pass | LG-E1 |
| 90 | `LG-E2` | authority composes in scope | Theory 8 | restated-this-pass | LG-E2 |
| 91 | `LG-J0` | accumulated authority bound | Theory 8 | restated-this-pass | LG-J0 |
| 92 | `LG-J2` | authority injections compose | Theory 8 | restated-this-pass | LG-J2 |
| 93 | `LG-J5` | ledger-relative burden condition | Theory 8 | restated-this-pass | LG-J5 |
| 94 | `LG-J6` | associativity up to outcome equality | Theory 8 | restated-this-pass | LG-J6 |
| 95 | `LG-X1` | local burden acceptance composes | Theory 8 | restated-this-pass | LG-X1 |
| 96 | `ST-C1` | proposed one-step interface revision | Theory 8 | deviation | annex |
| 97 | `ST-E1` | exhaustive finite classification | Theory 8 | restated-this-pass | ST-E1 |
| 98 | `ST-J1` | finite transport-plan decidability | Theory 8 | already-restated | ST-J1 |
| 99 | `ST-J2` | no liveness laundering | Theory 8 | already-restated | ST-J2 |
| 100 | `ST-J3` | no authority duplication | Theory 8 | already-restated | ST-J3 |
| 101 | `ST-J4` | burden conservation | Theory 8 | restated-this-pass | ST-J4 |
| 102 | `ST-J5` | comparison with CM-N1 | Theory 8 | restated-this-pass | ST-J5 |
| 103 | `ST-J6` | two-step compositionality | Theory 8 | restated-this-pass | ST-J6 |
| 104 | `ST-J7` | canonical maximality | Theory 8 | restated-this-pass | ST-J7 |
| 105 | `ST-N1` | semantic support never decides | Theory 8 | already-restated | ST-N1 |
| 106 | `ST-X1` | CM-N1 conserves burdens | Theory 8 | restated-this-pass | ST-X1 |
| 107 | `ST-X2` | CM-N1 blocks authority duplication | Theory 8 | restated-this-pass | ST-X2 |
| 108 | `ST-X3` | a terminal disposition is a grant | Theory 8 | restated-this-pass | ST-X3 |
| 109 | `ST-X4` | semantic support sponsors liveness | Theory 8 | restated-this-pass | ST-X4 |
| 110 | `ST-X5` | a cell-scoped termination discharges every input | Theory 8 | restated-this-pass | ST-X5 |
| 111 | `ST-X6` | case B is expressible as one frozen cell | Theory 8 | restated-this-pass | ST-X6 |
| 112 | `CD-C1` | canonical liability-key rule | Theory 9 | deviation | annex |
| 113 | `CD-E1` | adversarial suite | Theory 9 | restated-this-pass | CD-E1 |
| 114 | `CD-J1` | empty-substantive-book accounting | Theory 9 | already-restated | CD-J1 |
| 115 | `CD-J2` | unsupported-merits rejection | Theory 9 | already-restated | CD-J2 |
| 116 | `CD-J3` | default non-laundering | Theory 9 | restated-this-pass | CD-J3 |
| 117 | `CD-J4` | prospective procedure | Theory 9 | restated-this-pass | CD-J4 |
| 118 | `CD-J5` | transaction completeness | Theory 9 | restated-this-pass | CD-J5 |
| 119 | `CD-J6` | basis coherence | Theory 9 | restated-this-pass | CD-J6 |
| 120 | `CD-J7` | boundary faithfulness | Theory 9 | restated-this-pass | CD-J7 |
| 121 | `CD-J8` | automatic refusal accounting | Theory 9 | already-restated | CD-J8 |
| 122 | `CD-J9` | intrinsic default non-laundering | Theory 9 | already-restated | CD-J9 |
| 123 | `CD-L1` | merits iff leverage | Theory 9 | already-restated | CD-L1 |
| 124 | `CD-L2` | empty book recovery | Theory 9 | already-restated | CD-L2 |
| 125 | `CD-L3` | sure loss grounds nothing | Theory 9 | already-restated | CD-L3 |
| 126 | `CD-L4` | docket-mediated exposure | Theory 9 | already-restated | CD-L4 |
| 127 | `CD-L5` | merits evasion is record-visible | Theory 9 | restated-this-pass | CD-L5 |
| 128 | `CS-J1` | no free silence | Theory 9 | already-restated | CS-J1 |
| 129 | `CS-J2` | the trilemma | Theory 9 | already-restated | CS-J2 |
| 130 | `CS-J3` | fairness guarantee | Theory 9 | already-restated | CS-J3 |
| 131 | `CS-J4` | aggregate default | Theory 9 | restated-this-pass | CS-J4 |
| 132 | `CS-J5` | no double counting | Theory 9 | already-restated | CS-J5 |
| 133 | `CS-N1` | necessity of the solvency coupling | Theory 9 | restated-this-pass | CS-N1 |
| 134 | `CS-N2` | necessity of admission | Theory 9 | already-restated | CS-N2 |
## Phase 1 — the discard audit

One sweep beyond the ledger, checking rather than assuming. Every document of
the source tree was classified.

| document | verdict |
|---|---|
| `LEDGER.md` | the 134 rows, all dispositioned above; **vendored** as the authority for every transcription |
| `JOINT_THEORY.md`, `MIGRATION_THEORY.md`, `COMPOSITION_THEORY.md`, `STANDING_TRANSPORT.md`, `LOCAL_TO_GLOBAL.md`, `ANSWERABILITY_LEDGER.md`, `CASE_DOCKET.md`, `CASE_STREAM.md`, `GRAMMAR.md`, `LEVERAGE_INTERVAL.md` | the layers' derivations and fuller witness displays; content restated in Theories 7–10, and the documents **vendored** so the source's own exhibits travel with the package |
| `OPEN_PROBLEMS.md` | every item either appears in this package's ranked open list or is an adopted decision recorded in the decision ledger; **vendored** so no open question is lost in the move |
| `MOVING_INTERFACE_MAP.md` | the nine-row correspondence, restated in full as Theory 12 §2. The only change is the row labels, `MI-n` upstream and `M-n` here; the content, relations and findings are identical. **Vendored** as well |
| `DEVIATIONS.md` | source disclosures; **vendored** |
| `FIX_REPORT.md` | process narration of one repair. Its mathematical content — the retention repair, its counterexample and its constants — is `NL-N-J2A`, `NL-J2P`, `NL-J2P-B` and the Tier B constants. Excluded as narration, **vendored** anyway |
| `ROUND_REPORT.md` | process narration and prediction scores. Excluded by the standing exclusions, **vendored** anyway |
| `DECISIONS_PROPOSED.md` | proposals about the tree's own file organization; the one with mathematical consequence is the decision recorded as `P-4` in the decision ledger. Excluded, **vendored** anyway |
| `README.md` | navigation. No mathematical content. **Vendored** anyway |
| `src/`, `tests/` | original implementations, excluded by the standing exclusions. Tier A reimplements the load-bearing computations folder-locally and Tier B carries the numbers |
| `lean/` | already vendored at first freeze |
| `archive/`, zips | superseded snapshots, excluded as chronology |

**Result: nothing of retained mathematical value was found beyond the 134 rows.**
The prediction that this sweep would come up empty is scored below. Eighteen
documents were vendored regardless of that verdict, because vendoring is cheap
and leaves no room for argument about what was excluded.

## Phase 1 — deviations

Three rows, each quoted verbatim in `DEVIATIONS_ANNEX.md` with its obstacle and
with what a resolution would require.

| row | obstacle | resolution would require |
|---|---|---|
| `CD-C1` canonical liability-key rule | recorded as a conjecture; the schema-rate result it would support is, in the source's own words, not implemented and not claimed | proving that result — new mathematics. The question is carried in the ranked open list as schema-level demand rates |
| `CM-C1` retention and collection criterion | recorded as a conjecture whose necessity direction the source itself records as blocked by the authorization-manufacture refutation | settling necessity; restating only sufficiency would promote a conjecture |
| `ST-C1` proposed one-step interface revision | a proposal about a future interface, with compatibility against the migration and composition claims recorded upstream as unchecked | adopting the revision and checking that compatibility |

None is a transport-layer witness stated against an implementation, which is
what the risk prediction anticipated; the scoring below says so.

## Phase 2 — workspace reset inventory

The tree's dual role ended: it is a workspace only.

**Removed outright — none of it survives.** The checksum manifest
(`FROZEN_INPUT_CHECKSUMS.json`); the downstream rename manifest and its
roundtrip gate, together with the `tools/` directory holding it; the
consolidation-locating logic and every path or digest pinned to
pre-consolidation history; both vendored consolidation archives; the `archive/`
directory of superseded snapshots; and five ledger-completeness tests that
checked the tree's own ledger against the tree's own theory documents — that
bookkeeping now belongs to the consolidation, and each stripped method leaves a
one-line note saying so.

**Kept, because forward work needs it.** `src/grammar.py` — the footprint
verifier — with its dependents `src/answerability.py`, `src/case_docket.py` and
`src/case_stream.py`; `src/leverage_interval.py` as the exact-rational core,
together with `src/migration.py`, which is retained **only** because the
interval computer imports its exact square solver; and the six matching test
modules. Plus `lean/`, a simplified runner, and the three documents below.

**Attic.** A single `attic/` directory holds material that is consolidated and
therefore redundant here, but recent or substantial enough that deleting it
outright seemed gratuitous: the eighteen theory and report documents, the six
settlement-era source modules, the joint, composition, transport and history
modules, and their tests. `attic/` is not gated, not tested, and not referenced
by anything live. It can be deleted at any time; it is kept only so that a
reader who wants the source's working code does not have to unzip the
consolidation to see it.

**Written.** `CONSOLIDATION_REF.md`, pinning the consolidation by digest as the
sole authoritative reference, with the citation rule: cite frozen results by
claim identifier, never by reproducing them. `WORKSPACE.md`, three sentences of
policy. `CONVENTIONS.md`, carrying the vocabulary canon, the status vocabulary
including the necessity-witness status, and the footprint discipline.

**The runner** is test discovery, the vocabulary gate over live documents, and
the optional Lean skip. Nothing else.

## Prediction scores

**CP1 — CONFIRMED.** All 93 transcribed rows carried over without a
**definitional** extension to any theory part: none required a symbol the part
did not already define. Three parts gained a container section holding the
transcriptions, which is structural rather than definitional. Against the
threshold of ninety percent, the figure is a hundred.

**CP2 — NOT CONFIRMED.** No row revealed a definition gap requiring a marked
extension. The prediction expected at least one, and the reason it missed is
worth recording: the source's ledger rows are self-describing at row level —
each carries its own hypotheses and conclusion in its own vocabulary — so
transcription never had to reach into a definition the target part lacked. Had
the pass attempted to *re-prove* the transcribed rows rather than transcribe
them, the prediction would very likely have held.

**CP3 — CONFIRMED, checked rather than asserted.** The 87 rows of the first
freeze retain exactly their original status distribution: 50 proved, 17
machine-checked, 12 necessity witnesses, 7 conditional, 1 refuted. No status of
any prior claim changed.

**CP4 — PARTIALLY CONFIRMED; right count, wrong mechanism.** A handful of rows
did land as deviations — three — and one is indeed transport-layer. But none
landed for the predicted reason. No row was blocked by an upstream witness
stated against an implementation rather than a definition; all three were
blocked by status, being one conjecture and two unadopted interface proposals.
The annex absorbed them as predicted.

**CP5 — CONFIRMED.** The discard audit found nothing of retained mathematical
value beyond the 134 rows. The one document that came closest to an exception —
the correspondence table — is restated in full in Theory 12, differing only in
row labels.

**CP6 — CONFIRMED.** The reset workspace is green at 94 tests and
self-contained. A sweep for references to pre-consolidation history — the old
archives, the checksum manifest, the rename manifest, the consolidation-locating
variable — returns hits only inside `attic/`, which is retired by construction.
The live tree's only reference to anything prior is the pinned consolidation.

## Exact counts

| quantity | before this pass | after |
|---|---|---|
| consolidation ledger claims | 87 | **180** |
| — transcribed this pass | — | 93 |
| consolidation documents (non-vendored) | 19 | 21 |
| consolidation vendored-and-frozen files | 8 | **26** |
| consolidation tests | 107 | 107 |
| source rows unaccounted for | ~100 | **0** |
| workspace documents | 18 | 3 |
| workspace source modules | 17 | 6 |
| workspace tests | 227 | 94 |
| workspace freeze machinery | 4 mechanisms | **0** |

The consolidation's test count is unchanged, and deliberately so: transcription
adds claims whose evidence is the displayed source text, not new computations.
Adding tests would have implied a verification this pass did not perform.

## What this does NOT show

**No status of any prior claim changed.** Checked, not asserted: the original 87
rows retain their exact status distribution.

**No vendored or checksummed file was changed.** The August 8 archive, the three
interface documents and the four Lean sources carry the same digests as at first
freeze; the eighteen source-tree documents were added to the frozen set, not
substituted for anything. `CLEANUP_PASS.md` was not touched.

**Transcription is not re-proof.** The 93 added rows carry the source's own
hypotheses, conclusions and sharpness notes. Their folder-local evidence is that
displayed text, and the ledger's verification column says so on every one of
them. Where the source's fuller witness display lives in a source document, that
document is vendored — preserved, not restated. A reader wanting a re-derivation
of a transcribed drop-contract witness will not find one here.

**The final standing is exactly what `REPORT.md` §3 now states.** The source
tree is disposable because, and only because, that section says so truthfully:
every item of retained value is either restated in this package or preserved
verbatim and flagged in it. If that section is wrong, the tree is not
disposable, and nothing else in this report repairs that.

**The workspace is not evidence.** It is green, but its greenness certifies only
that the six retained modules behave as their tests say. Nothing in it is
frozen, and nothing in it survives unless it is consolidated.
