---
id: deference-finite-results
kind: frame
children: [local-delegation-bridge, local-delegation-bridge.improvable]
question: "Which finite results about delegation, certificates, exposure, substitution, magnitude and corrective control does the deference line hold as kernel-checked theorems?"
owner: "@abram"
narrative: wiki/What-Deference-Requires.md
roots:
  - {id: local-delegation-bridge, role: shared-claim, preset: worst-case}
  - {id: local-delegation-bridge.improvable, role: shared-claim, preset: worst-case}
holds: [delegation.bridge-unconditional, delegation.gradetrust-refinement, certificate.margin-forces-agreement, certificate.selection-eq-of-margin, certificate.override-bound, certificate.defect-bound, certificate.advantage-estimate, certificate.grade-register-strict, exposure.greedy-duality, exposure.harvest-bound, exposure.harvest-attained, substitution.extensional-admits-both, substitution.sim-depends-on-induced-choice, substitution.separation-requires-disagreement, substitution.unpredictability-separates, magnitude.unit-trader-networth, magnitude.signed-bounded, magnitude.signed-bounded-actual, magnitude.mixture-networth-zero, magnitude.not-trader-payoff, magnitude.sq-error-split, magnitude.sharp-trader-networth, jurisdiction.value-eq-of-price-realization, jurisdiction.static-view-eq, corrective.can-correct-iff, corrective.can-correct-future-iff, corrective.forecloses-iff, corrective.no-exclusive-effect, corrective.advisor-veto, corrective.capability-measures-cooperation]
author: "@smithy-verity"
size: M
size_reason: "thirty-one registered results of the deference registry"
version: 1
---
## Statement
The delegation bridge, the certificate, exposure and substitution lemmas, the signed-versus-magnitude separation, the jurisdiction results and the corrective-control model hold as registered theorems, and the strongest among them are impossibilities.

## Source
projects/deference/CLAIMS.md (delegation.*, certificate.*, exposure.*, substitution.*, magnitude.*, jurisdiction.*, corrective.*); wiki/Deference.md, Current status (Established lean-proved).

## Notes
Filed by prompts/2026-10-22-map-as-canonical to hold the deference registry's finite results as formal results under the line that produced them. Since ruling G2 (2026-10-23) they are held (`holds`), not roots: the frame has no goal until a maintainer names one.
