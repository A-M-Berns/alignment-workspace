---
id: ps-trained-systems-seek-power.improvable
kind: or
children: [ps-route-partial-observability, ps-route-suboptimal-policies, ps-route-empirical-trained-policies, ps-route-residual]
improves: ps-trained-systems-seek-power
reality: the policies produced by the training procedures actually used
author: "@smithy-verity"
size: M
size_reason: "one paper's closing sentence, two published steps and one dispute"
version: 1
---
## Statement
The power-seeking theorem chain, from optimal policies in symmetric fully
observable Markov decision processes through retargetable decision functions
and training-compatible goal sets, can be improved until it reflects the
policies produced by the training procedures actually used well.

## Source
The protocol's rule that every toy a plan builds on carries its improvement
claim; the authors' stated plan, Turner et al. 2021: "We look
forward to future work which addresses partially observable environments,
suboptimal policies, or 'almost similar' RSD sets"; the two published steps
(Turner and Tadepalli 2022; Krakovna and Kramar 2023) and the first author's
dispute (Turner 2024).

## Notes
Improvement claim on the theorem route of the instrumental-convergence risk
story (improves: ps-trained-systems-seek-power; reality: the policies produced
by the training procedures actually used). Filed as a shared-claim root of the
corrigibility-landscape frame rather than of the top frame, because the top
frame's roots are fixed by the round's content contract. Two of three relaxation
steps are published; the third has no proof and is disputed by the toy's first
author.
