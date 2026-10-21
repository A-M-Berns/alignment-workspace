---
id: enabling-machine-checked-corpus
kind: and
children: [cleanroom-flags-resolved, notes-corrected-after-lean, cleanroom-results-in-public-ci, enabling-machine-checked-corpus.complete]
author: "@smithy-verity-opus55"
size: L
size_reason: "the clean-room README, digest and origin note"
version: 1
---
## Statement
The research corpus's claims are formalized in Lean 4 over FAF and
adversarially audited in a run independent of the first, the run's flagged
packages are repaired or ruled on, the notes stop asserting what the Lean
refutes, and selected results build in this repository's CI.

## Source
projects/deference/faf-cleanroom-2026-10-02/README.md: "Lean 4 formalizations
of a research corpus on logical induction, deference, corrigibility, decision
theory and Bayesian logical induction (BLI), stated over Formalized Agent
Foundations (FAF) and adversarially audited, 2026-09-29 to 2026-10-02";
"Moving selected results into lean/ needs a FAF pin bump there and is future
work". projects/deference/faf-cleanroom-2026-10-02/DIGEST.md and ORIGIN.md.

## Notes
An enabling goal filed by the activity sweep: results of every line of the
agenda enter the map through this library. The clean-room run has 106 work
packages in 13 areas; 83 passed their last fresh audits and 23 are flagged,
none of them a false proved Lean statement (DIGEST.md, item 1 and the flags
section).

The first clause is done; the other three are open. The port of the
deference results is filed by the li-deference trust line; this goal holds the
parts every line's results share, and the decomposition is the filing
session's reading.
