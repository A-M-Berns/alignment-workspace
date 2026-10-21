---
id: paper-tiling-formalized
kind: and
children: [paper-tiling-formalized.record, paper-tiling-formalized.bridge, policy-fairness-hypothesis, paper-tiling-formalized.complete]
author: "@smithy-verity"
size: M
size_reason: "one package report and the paper's theorem section"
version: 1
---
## Statement
Under a causal structure in which available actions modify only strictly later
observations, one pass of elimination along any rank-sorted enumeration reaches
the effective policy, and UDT 1.1 tiles under Policy Fairness (Theorem 1 of
Understanding Trust in the form its proof supports); without the causal order
the limit of repeated elimination is not unique.

## Source
projects/deference/faf-cleanroom-2026-10-02/packages/udt-paper-tiling/udt-paper-tiling-report.md:
effCausal, elimSeq_eq_effCausal, thm1_udt11_tiling, thm2_udt10_tiling with the
forced tie, Chain.limit_not_unique. Source:
projects/deference/faf-cleanroom-2026-10-02/sources/references/bli/understanding-trust/overleaf-final-source/main.tex,
sections Tiling & Trust and the theorems.

## Notes
The first route: the paper's results formalized with the causal order the paper
avoided. The package is flagged on text only: its CausalStructure docstring
states the opposite of what is proved (flag B1), which the text-repair task
given to the bridge fixes. Theorem 2's package forces a tie at every
observation, which is a finding about the paper's hypotheses rather than a
refutation.
