---
id: pic-T-kk-training-compatible-goal
kind: leaf
leaf_kind: picture
refines: pic-T-not-reward-maximizers
author: "@smithy-verity"
size: S
size_reason: one abstract
version: 1
---
## Statement
The system is a trained policy that is not a reward maximizer but has learned
some goal in the training-compatible goal set, the set of goals consistent
with the training rewards, and acts for that goal in new situations.

## Source
Krakovna and Kramar 2023, Power-seeking can be probable and predictive for
trained agents (arXiv 2304.06528), abstract: "We formally define the
training-compatible goal set (the set of goals consistent with the training
rewards) and assume that the trained agent learns a goal from this set. In a
setting where the trained agent faces a choice to shut down or avoid shutdown
in a new situation, we prove that the agent is likely to avoid shutdown."

## Notes
The published reply, filed by a contributor as a refinement of the
trained-policy picture: in this part of it the claim holds for a learned goal,
and the power-seeking conclusion follows by the paper's theorem. The paper
predates the post it is filed against; the post was written with it in view.
