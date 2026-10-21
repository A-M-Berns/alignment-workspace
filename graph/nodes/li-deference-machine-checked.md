---
id: li-deference-machine-checked
kind: frame
children: [lean-deference-audit-closed, cleanroom-deference-followups, public-port-of-deference-results, lean-deference-audit-findings, cleanroom-deference-headlines, registry-policy-for-ported-results, crux-cleanroom-citable]
question: "Which machine-checked statements over a formalized logical induction criterion establish the li-deference results as the prose states them?"
owner: "@maintainer"
roots:
  - {id: lean-deference-audit-closed, role: plan, preset: worst-case, success_class: utopia}
  - {id: cleanroom-deference-followups, role: plan, preset: worst-case, success_class: utopia}
  - {id: public-port-of-deference-results, role: plan, preset: worst-case, success_class: utopia}
  - {id: lean-deference-audit-findings, role: shared-claim, preset: worst-case}
  - {id: cleanroom-deference-headlines, role: shared-claim, preset: worst-case}
  - {id: registry-policy-for-ported-results, role: shared-claim, preset: worst-case}
  - {id: crux-cleanroom-citable, role: shared-claim, preset: worst-case}
author: "@smithy-verity-opus55"
size: L
size_reason: "three Lean generations and the public line's items"
version: 1
---
## Statement
The logical-induction deference results are machine-checked over a
formalization of the logical induction criterion with the market and traders
present, and the checked statements are the ones the prose claims.

## Source
projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md §1: "The Lean
proves the *implications* of the deference theory. It does not prove the
*antecedents*."

projects/deference/faf-cleanroom-2026-10-02/STANDARDS.md (state over FAF's
objects, no trust holes, no squeezes, non-degenerate witnesses).

## Notes
The formalization work as a programme: three generations (lean-deference to
July, faf-lab in September, the clean room to 2026-10-02) and the public
line's Workspace.Deference. The id faf-pin-bump-and-public-port is filed under
this frame.
