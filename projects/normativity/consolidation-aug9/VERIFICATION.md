# Verification

What is checked by machine, what is derived by hand, what rests on a reading,
and what is assumed. The distinction between the third and the first two is the
one this document exists to keep visible.

## 1. Trust audit

Every claim of this monograph falls in exactly one of five classes.

**Machine-checked over a displayed finite instance — 17 claims.** A folder-local
exact-rational program recomputes the displayed numbers. Passing is evidence for
those instances and for nothing else: no generalization is implied, and where a
claim's general form is proved, the proof and not the program is the evidence.

**Hand-derived from folder-local definitions — 69 claims** (fifty proved, twelve
necessity witnesses, and the seven conditional rows, whose conditions are listed
in their rows and which belong to this class — a placement the first freeze left
implicit). The proof in the
theory part is the whole evidence. Every one of these is a finite argument from
definitions stated in the same part; **no proof cites a tree file, a test, or a
program as a proof step.** Where a program exists for the same object, it
exercises instances of the theorem and is listed as verification, never as
proof.

**Reading audit — 1 claim, and one corollary depending on it.** `NL-SI-SIM`
records a clause-by-clause reading of one candidate engine's published source
against this interface. It is not machine-checked, it is not derived from these
definitions, and it is not a theorem of this package. It is retained because it
is the only evidence about a non-trivial engine that exists, and it is labelled
in its ledger row, in Theory 11 §7, and here. `NL-SI-X4` depends on it and
inherits its standing.

**Transcribed from the vendored source ledger — 93 claims.** The rows of
Theories 7 through 10 carried over by the completing pass. Each carries the
source's own hypotheses, conclusion, status and sharpness; its folder-local
evidence is that displayed text together with the vendored source document its
verification pointer names, frozen by digest under `vendor/source_theory/`.
These rows are preserved and stated, not re-derived: transcription is not
re-proof, and the ledger's verification column says so on every one of them.
The classes sum: 17 + 69 + 1 + 93 = 180.

**Assumed, and named — the two residues.** Procedural faithfulness on the
empirical channel and checker soundness on the logical channel are axioms. They
are stated in Theory 11 §4 and are not discharged anywhere in this package. Two
typed obstructions in Theory 12 (`NL-SI-K2`, `NL-SI-K1`) make certain
dependences unwritable *in the constructions displayed here*; those are
disclosures about those constructions and are labelled as such, not proofs of
the axioms.

### The reading-audit class, in the audit's own words

The vendored audit's closing section says of itself that inhabitation is not the
witness theorem, that producing its result-class is not proving the witness
theorem, and that no verdict in it rests on the behaviour of any
implementation. This package takes that at face value and gives the class its
own label rather than folding it in with the derived results.

## 2. Executable coverage

| tier | what it covers | count |
|---|---|---|
| Tier A | fresh folder-local implementations of the load-bearing computations: exact linear algebra and programming, the interval computer, the incoherence functional and the robust forms, the core-geometry program and closed form, the interface predicates, the parametric-composite evaluator with its hypothesis objects and drop-one checks, the channel and conduct and two-engine witnesses, and the grammar verifier | 91 tests |
| Tier B | the long tail of exact numbers carried forward from the source tree, recomputed against Tier A | 16 tests |

Tier B retains **numerical assertions**, not every historical implementation.
That is an intentional distinction inherited from the previous consolidation: a
number that mattered is kept and rechecked; a particular way of having computed
it once is not. It alters no mathematical content, and it is the one place where
the discard test loses something — original implementations — that is not of
retained mathematical value.

**Nothing in `src/` imports from any repository.** The package is green from a
clean checkout of this folder alone.

## 3. What the runner enforces

`python3 tests/run.py` runs, in order:

1. the **retired-name gate** over every non-vendored document, including this
   one and the report;
2. a **`sorry` scan** over every vendored Lean source;
3. **ledger coverage**: every claim identifier in a theory part has a ledger row,
   every ledger row has a claim, and the statuses agree — a mismatch fails;
4. **identifier expansion**: every claim-ID family in use is expanded in
   `ID_EXPANSIONS.md`;
5. **frozen-input digests** over the vendored archive, the four interface
   documents, and every Lean file;
6. **both Python tiers**;
7. **Lean**, with an explicit skip when `MATHLIB_DIR` is unset or `lake` is
   unavailable.

The ledger cross-check is the load-bearing one. It is what makes it impossible
for a status to be softened in one document and not the other.

## 4. Lean scope

Four files are vendored: two from the previous consolidation and two from the
source tree. They are checked for `sorry` unconditionally and compiled when a
Mathlib-enabled project is configured. **They do not cover the new
mathematics.** Nothing in Theory 11 or Theory 12 is formalized; the Lean here is
inherited evidence for inherited results, and this package adds none.

## 5. Known limits of the verification

- Machine checking is over displayed instances. The core-geometry sweep covers
  four endorsed rows against nine candidate settlements on three worlds; the
  trajectory reports are over searched finite trajectories. No asymptotic claim
  anywhere rests on them.
- The exact-rational programs are correct by construction rather than by
  independent implementation: vertex enumeration is the only algorithm, and it
  is used identically everywhere. A systematic error in `src/exact.py` would be
  invisible to the tiers. The mitigation is that every number it produces is
  also derived by hand in the theory part, and the two agree — including the
  four-fifteenths instance, the one-tenth boundary, and the closed-form
  coefficients.
- The certificate extraction is searched, not solved, and whatever it returns is
  **verified by an independent program** before it is reported. A failure of the
  search is a missing certificate, never a false one.
- The reading audit was performed against a published source this package does
  not vendor. It vendors the audit, the corrigendum, the interface draft and its
  changelog, which is the evidence base for the reading, not the source read.
