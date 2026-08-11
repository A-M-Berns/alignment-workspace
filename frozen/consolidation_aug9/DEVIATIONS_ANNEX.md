# Deviations annex

Quarantined **non-restated source material**. Nothing here is a claim of this
package: nothing in this file is proved, endorsed, or counted in the ledger, and
no theory part cites it. It exists so that the completing pass leaves nothing of
retained value stranded in the source tree.

Two kinds of material are preserved.

## 1. Deviation rows

Three of the source tree's 134 four-layer ledger rows were **not** transcribed
into the ledger. Each is quoted verbatim below with the obstacle and with what a
resolution would require. Silent omission was the one unacceptable outcome; this
section is the alternative.


### CM-C1 — retention and collection criterion

**Obstacle.** the row records a CONJECTURE, and a conjecture is an open question rather than a claim; promoting it to a ledger row would violate the standing rule that open questions are not promoted.

**Source row, verbatim:**

```
ID / claim: CM-C1 retention and collection criterion
Full hypotheses: live descendant ancestry, live typed target chains, outstanding payoff indexing, and retained disclosure indexing
Conclusion: an intermediate structural record must remain public iff one of the four clauses holds
Status: CONJECTURE (not proved)
Proof location: Composition Theory §8
Necessity / sharpness: sufficiency computed and two instances exhibited; necessity quantifies over future migrations and is blocked by AM-X10
Verification: R-B collects nothing; R-A collects exactly the four frustration-lineage occurrences; both retain the arenas
Dependencies: AM-X10, C-FIXED-KERNEL
```

**A resolution would require** settling the necessity direction, which the row itself records as blocked: necessity quantifies over future migrations and is obstructed by the authorization-manufacture refutation. Sufficiency is computed upstream and its two instances are exhibited there. Restating only the sufficiency half would promote a conjecture, which the standing rule forbids.

### ST-C1 — proposed one-step interface revision

**Obstacle.** the row records a PROPOSED interface revision — a proposal about a future interface, not a claim about this one; its compatibility with the migration and composition claims is recorded upstream as unchecked.

**Source row, verbatim:**

```
ID / claim: ST-C1 proposed one-step interface revision
Full hypotheses: a certificate that would decide transport locally
Conclusion: needs a per-occurrence unresolved-burden bit, input-scoped terminal dispositions, three typed support relations, scoped grants, and a mixed-status many-to-many cell
Status: PROPOSED (interface revision)
Proof location: Standing Transport §6
Necessity / sharpness: items 1 and 2 are load-bearing; the rest make the check local rather than historical
Verification: not adopted; compatibility with existing AM- and CM- claims unchecked
Dependencies: AM-J0, CM-N1, ST-X6
```

**A resolution would require** adopting the proposed interface revision and checking its compatibility with the migration and composition claims, which the row records as unchecked. Until adopted it is a proposal about a future interface, not a claim about this one.

### CD-C1 — canonical liability-key rule

**Obstacle.** the row records a PROPOSED interface revision, not a proved claim; and the schema-rate result it is designed to support is, in the source's own words, not implemented and not claimed.

**Source row, verbatim:**

```
ID / claim: CD-C1 canonical liability-key rule
Full hypotheses: a liability key includes exactly the coordinates along which an admissible challenge or disposition can vary independently
Conclusion: schema-keyed endorsement objections; `(rho, query id, grounds binding)` for application obligations; fresh applicability per case
Status: PROPOSED (interface revision)
Proof location: Case Docket §6
Necessity / sharpness: the schema-rate theorem this would support is not implemented and not claimed
Verification: none
Dependencies: AD-C1
```

**A resolution would require** implementing the schema-rate result the row says is *not implemented and not claimed*, and then restating the key rule as a theorem about it. That is new mathematics, so the row stays here and the underlying question is carried in `OPEN_PROBLEMS.md` as schema-level demand rates.

## 2. Source material the transcribed rows point at

The 93 transcribed rows carry their source hypotheses, conclusions and
sharpness notes into the ledger and into their theory parts. For a subset of the
drop-contract and necessity rows, the source's *fuller* witness display — the
exhibited instance with its numbers — lives in the source tree's own theory
documents rather than in the ledger row that names it. Those documents are
therefore vendored **byte-for-byte** under `vendor/source_theory/` and frozen by
digest, so the witness material is inside this package and the source tree is
not needed to read it.

**This is preservation, not restatement, and the distinction is deliberate.** A
transcribed row's folder-local evidence is the text displayed in its theory
part; where a reader wants the source's fuller exhibit, the vendored document is
the place, and it is quarantined source material with the same standing as any
other vendored evidence — frozen, unedited, and not a claim of this package.

| vendored document | what it carries |
|---|---|
| `LEDGER.md` | the source tree's complete claim ledger, all 151 rows, as the authority for every transcription |
| `JOINT_THEORY.md` | the joint-composition layer's derivations and drop-contract witnesses |
| `MIGRATION_THEORY.md` | the accountable-migration layer's witnesses |
| `COMPOSITION_THEORY.md` | the migration-composition layer's witnesses and repairs |
| `STANDING_TRANSPORT.md` | the transport layer's enumeration and its witnesses |
| `LOCAL_TO_GLOBAL.md` | the local-to-global search and its bounded witnesses |
| `ANSWERABILITY_LEDGER.md` | the ledger layer's scenario scope and benchmark examples |
| `CASE_DOCKET.md`, `CASE_STREAM.md`, `LEVERAGE_INTERVAL.md`, `GRAMMAR.md` | the practical-demand and grammar layers' displays |
| `OPEN_PROBLEMS.md`, `DEVIATIONS.md` | the source tree's own open list and disclosures, retained so no open question is lost in the move |

Because these are vendored, the retired-name gate does not apply to them, and
their wording is the source's own.
