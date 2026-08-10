# Deviations

Source problems and consolidation limitations. Each is a fact about the inputs
or about this package's construction, not a mathematical claim.

1. **The interface documents use vocabulary this package's gate rejects.** The
   draft, its changelog and the reading audit are therefore **vendored rather
   than incorporated**: their content enters the theory parts under the
   substitutions ratified in `GLOSSARY.md`, and the documents themselves are
   frozen and unedited. This is the same reason the audit gives for having been
   housed outside the source tree in the first place.

2. **Two citations in the interface draft did not survive verification, and one
   audit citation did not either.** The draft's adequacy clause cited three
   identifiers, of which two occur nowhere; and it described the probe-blackout
   clause as extending existing conduct machinery that does not exist. The audit
   cited a source label for the budget-limiting construction that does not
   exist, though its content is correct. All three are recorded in
   `AUDIT_CORRIGENDUM.md` and in the vendored changelog, and this package cites
   content instead.

3. **The audit's own citation-integrity flag was too broad**, claiming a witness
   label occurs in neither tree when it occurs three times in the previous
   consolidation. Corrected in `AUDIT_CORRIGENDUM.md` rather than silently.

4. **A delimited gate exemption exists, for one document.** The glossary's
   mapping tables must name the retired words to be useful, which the gate
   otherwise forbids. The exemption is marked by comment delimiters, is
   available to `GLOSSARY.md` only, and the runner fails if another document
   opens it or if a region is left open. Decision C-11.

5. **Tier B keeps numbers, not implementations.** The long tail of exact numbers
   from the source tree is recomputed against this package's fresh
   implementations; the original programs are not vendored. This is the one
   place the discard test loses something, and what it loses is not of retained
   mathematical value. Recorded in `VERIFICATION.md`.

6. **The vendored Lean does not cover the new mathematics.** Four files are
   carried and checked; none formalizes anything in Theory 11 or Theory 12.
   Nothing here claims Lean coverage it does not have.

7. **The reading audit was performed against a source this package does not
   vendor.** What is vendored is the evidence base for the reading — the audit,
   the corrigendum, the draft and its changelog — not the source read. A reader
   wanting to re-perform the reading needs that source.

8. **The previous consolidation's parts are not restated.** They are vendored
   whole and remain authoritative for their own content. Where a result here
   modifies or repairs one of them, the modification says so; where a result
   here merely uses one, the content is stated inline so no proof depends on
   opening the archive.

9. **One claim class is not a theorem.** `NL-SI-SIM` is a reading audit. It is
   labelled in the ledger, in its theory part, and in the trust audit; anything
   depending on it inherits the label. It is retained because it is the only
   evidence about a non-trivial engine that exists.
