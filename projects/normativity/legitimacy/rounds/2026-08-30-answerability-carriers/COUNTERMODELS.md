# Countermodels

`src/transfer_models.py` contains exact finite-set realizations. `tests/run.py` executes
the twenty requested hostile cases plus exhaustive two-atom splits.

| # | case | issue-only | matter-only | carrier-frontier | result |
| ---: | --- | --- | --- | --- | --- |
| 1 | one faithful successor | accepts | accepts | accepts | valid |
| 2 | structurally valid bogus successor | needs extra comparison | accepts live matter | rejects soundness | invalid |
| 3 | two children jointly carry halves | cannot demand each carry all | says matter remains | accepts collective join | valid |
| 4 | both children duplicate same half | local child checks accept | says matter remains | rejects completeness | invalid |
| 5 | two parents merge completely | awkward without matter indexing | accepts identity only | accepts parent-set union | valid |
| 6 | merge drops one parent | may miss cross-parent loss | accepts live matter | rejects completeness | invalid |
| 7 | partial satisfaction plus carry | needs mixed account | cannot locate remainder | accepts SDT decomposition | valid |
| 8 | genuine satisfaction | accepts receipt | accepts closure | accepts | valid |
| 9 | authorized disposition | accepts receipt | accepts closure | accepts | valid |
| 10 | ontology deletion called satisfaction | may accept empty state | may accept closure | rejects absent receipt | invalid |
| 11 | issue stays live while load erased | accepts structural occurrence | accepts live matter | rejects realization | invalid |
| 12 | live set has carrier plus helpers | treats all issues alike | has no realization locus | selects nonzero-load subset | valid only after selection |
| 13 | Coverage translation retains all criticisms | possible | cannot audit allocation | accepts complete join | valid |
| 14 | Coverage drops one criticism | may miss omission | matter remains | rejects completeness | invalid |
| 15 | Reason Carry translation | accepts with denotation map | too coarse | accepts | valid |
| 16 | two-step faithful translation | pairwise links compose | identity persists | composed relation is sound | valid |
| 17 | complete-looking links change meaning | genealogy accepts | identity assertion is unsupported | rejects semantic map | invalid |
| 18 | empty succession without exit | issue gone | matter closes structurally | rejects terminal account | invalid |
| 19 | fixed residual rule, different actions | not a carrier question | not a carrier question | accepts policy locality premise | valid locality |
| 20 | apparent finite burden graph | would duplicate issues | would omit allocations | embeds as issue loads | no separate lifecycle needed |

## Necessity summary

Dropping Transfer Soundness admits invented child content. Dropping Completeness admits
the duplicate-half split and lossy merge. Replacing the carrier frontier by raw `Live`
classifies empty helper branches as semantic carriers. Dropping terminal receipts admits
empty closure. Dropping Continuity permits a semantically named successor that is never
outstanding or ancestrally attached. Dropping authenticated intermediate denotation makes
sequential composition lose meaning.

No hostile finite example requires an independent burden occurrence. Example 20 embeds
the proposed burden graph into existing fresh issues and their matter-indexed load
allocation. This is evidence for interface sufficiency, not an impossibility proof for
all future inter-agent or cross-matter transfer theories.
