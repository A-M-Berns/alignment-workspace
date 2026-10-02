---
id: thm-ps-symmetric-mdp-setting
kind: leaf
leaf_kind: hypothesis
discharge: definitional
author: "@smithy-verity"
size: S
size_reason: the theorem's hypothesis list
version: 1
---
## Statement
The agent is an optimal policy for a reward function drawn from a distribution
invariant under the environmental symmetry, in a finite fully observable
Markov decision process.

## Source
Turner et al. 2021, section 6, the hypotheses of Theorem 6.13 as stated.

## Notes
Definitional within the toy: the theorem is about these agents. The relaxation
to trained systems is the three bridges' task, which is why the trained-policy
story about the shared assumption lands on them and not here.
