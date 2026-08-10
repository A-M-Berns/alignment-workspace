# Consolidation, August 9

This folder is a self-contained statement and verification package for the
retained mathematics produced since the August 8 consolidation. It covers two
bodies of work: the layers of the normative-learner development — the objection
grammar, diachronic identity, practical demand, and joint composition — and the
settlement-interface era, which defines the interface a world-channel must meet
before the mechanism grants its writings operative force, and states what is
known about whether any engine meets it.

The previous consolidation is **vendored here byte-for-byte**. Its six theory
parts remain authoritative for their own content, and nothing from them is
restated except where a result here modifies or repairs it — each such place
says so. So a reader holding only this folder holds the previous consolidation
too — and, since the completing pass, the source tree's retained content as
well. **This folder is the sole authoritative record; the discard-test audit
below argues that in full.**

Theory numbering continues the previous consolidation's, so the two read as one
monograph.

## Folder map

- `THEORY_7_OBJECTION_GRAMMAR.md` through
  `THEORY_12_PARAMETRIC_COMPOSITE_AND_CONSTRUCTIONS.md`: definitions,
  statements, proofs, counterexamples and boundaries, in dependency order. Every
  part defines every symbol it uses.
- `LEDGER.md`: one row for every claim, with full hypotheses, conclusion,
  status, necessity or sharpness, verification pointer, and dependencies.
- `ID_EXPANSIONS.md`: every claim-ID family, its expansion, and the
  reclassification history it carries.
- `GLOSSARY.md`: canonical vocabulary and notation, the retired-term table, and
  the mapping that makes the vendored interface documents readable against this
  package.
- `VERIFICATION.md`: the trust audit — machine-checked versus hand-derived
  versus **reading audit** versus assumed — executable coverage, and Lean scope.
- `DECISION_LEDGER.md`: every author decision of this era and every
  discretionary consolidation choice.
- `OPEN_PROBLEMS.md`: the mathematical frontiers, ranked.
- `INTERPRETATION.md`: non-authoritative readings and design commentary, as a
  three-zone map. Nothing here is cited by a theory part.
- `FOR_HUMANS.md`: a standalone plain-language account.
- `AUDIT_CORRIGENDUM.md`: two corrections and one reconciliation against the
  vendored reading audit, which is frozen and unedited.
- `DEVIATIONS.md`, `AMBIGUITIES.md`: source problems and per-line judgment calls.
- `REPORT.md`: what was consolidated, what was archived, exact counts, and the
  standing what-this-does-not-show section.
- `src/`, `tests/`: exact-rational Tier A and Tier B. Run
  `python3 tests/run.py` from this folder.
- `lean/`: vendored Lean sources, checked for `sorry` unconditionally.
- `vendor/`: the previous consolidation as an archive, and the four interface
  documents, all frozen by digest.
- `FROZEN_INPUT_CHECKSUMS.json`: SHA-256 over everything vendored.

## Evidence discipline

Passing finite code is evidence for the displayed finite instances only. General
theorems are supported by the complete rederivations in the theory parts, and
**no proof cites a tree file, a test, or a program as a proof step**. The ledger
uses only the mandated status vocabulary. Conditional statements list their
conditions; refutations display their witnesses; open questions are not
promoted.

Citation integrity is enforced as policy: **content is stated inline, and no
identifier is cited that has not been verified against the source it names.**
Where a source identifier turned out not to exist, the corrigendum says so and
the content is stated directly instead.

One claim class is weaker than the rest and is labelled everywhere it appears: a
**reading audit** is a clause-by-clause reading of a candidate's published
source, not a theorem of this package.

## One-command verification

From this directory:

```sh
python3 tests/run.py
```

The runner executes both Python tiers, the retired-name gate over every
non-vendored document, the ledger-coverage and status-agreement cross-check, the
identifier-expansion check, and the frozen-input digests, then compiles the
vendored Lean. It needs no sibling tree. Lean is skipped with an explicit
message unless `MATHLIB_DIR` names a Mathlib-enabled Lake project; the Python
tiers and every document audit run regardless.

## Discard-test audit

The claim is that everything outside this folder can be thrown away and nothing
of retained mathematical value is lost. **As of the completing pass that claim
holds for the whole package**, and the argument is below. It did not hold at
first freeze; what changed is recorded in `COMPLETING_PASS_REPORT.md`.

**Theorems and witnesses.** All 180 ledger claims are stated here with their
hypotheses, conclusions, statuses and dependencies, and the runner refuses to
pass if a status disagrees between a theory part and the ledger. The 87 claims
of the first freeze are proved here from definitions given here; the 93 added by
the completing pass are faithful transcriptions of the source tree's own rows,
each carrying its witness or sharpness text into its theory part, and each
marked as transcribed in its verification column.

**Exact numbers.** The load-bearing ones are recomputed by Tier A and the long
tail by Tier B, both folder-local, and each is also derived by hand in the part
that states it — so a number survives even if the code is never run.

**Everything else on the test's list.** Status boundaries: in the ledger, gate-
enforced. Canonical definitions: every part defines every symbol it uses, and
the glossary carries the vocabulary with its retirement history. Adopted
decisions: the decision ledger carries the era, dated, and no adopted decision
appears in the open problems. Open questions: ranked, none promoted. The
previous consolidation: vendored whole, by digest. The reading-audit evidence
base: vendored whole.

**The three rows that were not transcribed** — one conjecture and two unadopted
interface proposals — are quoted verbatim in `DEVIATIONS_ANNEX.md` with their
obstacles. **The source material the transcribed rows point at** is vendored
byte-for-byte under `vendor/source_theory/`, 18 documents including the source's
complete ledger, and frozen by digest. So every item of retained value is either
restated here or preserved verbatim and flagged here.

**What is genuinely lost, and does not count.** Chronology. Process narration.
Superseded designs — each surviving where it matters as the necessity witness
that killed it: the ambient reading is displayed failing at every positive
coefficient in `NL-SI-A1`, and the bare-admission predicate is displayed
certifying a zero charge where two-fifteenths is owed in `NL-N-J2A`. Original
implementations — Tier A is a fresh implementation and Tier B keeps the numbers
rather than the programs that first produced them.

**So the source tree may now be changed or deleted wholesale.** It is no longer
evidence for anything. `REPORT.md` §3 states the standing precisely, including
what transcription is and is not.
