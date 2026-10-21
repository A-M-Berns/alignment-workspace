---
id: cole-stability-reading
kind: leaf
leaf_kind: question
action: "Write the martingale step behind the post's for-all-time clause (stability for all time with high probability) in the finite shadow, or show where it needs more than the trust bound."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/packages/uea-sink-swim/uea-sink-swim-report.md]
author: "@smithy-verity-opus55"
size: M
size_reason: "one post and one omitted argument"
version: 1
---
## Statement
Cole Wyeth's revised theorem is a stability result: an agent that chooses
actions one at a time by evidential expected utility, is confident but not
certain that this is its own decision procedure, and acts relative to an
oracle fixed point that cooperates with itself stays near-optimal in
environments that treat it dualistically, for all time with high probability.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/01-primary/lesswrong-post--live-2026-08-22.md:
"In particular, $\pi_S$ remains $\varepsilon$-(Bayes)optimal for all time with
high probability."

## Notes
The post's framing; the for-all-time part is not formalized in the public
sources. The sink-or-swim
package's target 5 formalizes a 1 − w_t martingale in the finite model, the
nearest existing piece.
