---
id: ps-trained-systems-seek-power
kind: and
children: [thm-power-seeking-optimal, bridge-ps-s1-retargetable, bridge-ps-s2-training-compatible, bridge-ps-s3-trained-policies, ps-trained-systems-seek-power.complete]
author: "@smithy-verity"
size: M
size_reason: three papers and one disputed step
version: 1
---
## Statement
Policies produced by the training procedures actually used tend to seek power
in the sense of the power-seeking theorems: they keep options available and,
when optimizing average reward, navigate toward larger sets of potential
terminal states.

## Source
Turner, Smith, Shah, Critch and Tadepalli 2021, Optimal policies tend to seek
power (NeurIPS), abstract: "we prove that certain environmental symmetries are
sufficient for optimal policies to tend to seek power over the environment";
the endpoint of the plan the paper states: "We look forward to future work
which addresses partially observable environments, suboptimal policies, or
'almost similar' RSD sets."

## Notes
The theorem route: the toy theorem and three bridges, from optimal policies to
retargetable decision functions, from a symmetric reward distribution to the
training-compatible goal set, and from that set to the policies the procedures
produce. The last bridge has no proof and its toy's first author disputes it.
