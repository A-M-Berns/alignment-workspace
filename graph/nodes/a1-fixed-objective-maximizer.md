---
id: a1-fixed-objective-maximizer
kind: cases
children: [a1-fixed-objective-maximizer.partition, pic-T-kk-training-compatible-goal, pic-T-rest-no-single-objective, pic-N-a1-residual]
rows:
  - {picture: pic-T-kk-training-compatible-goal, class: null, observable: never}
  - {picture: pic-T-rest-no-single-objective, class: null, observable: never}
  - {picture: pic-N-a1-residual, class: undescribed-failure, observable: never, residual: true}
attribution: reconstructed
author: "@smithy-verity"
size: M
size_reason: "two sources, two reconstructions identified, and two trained-policy pictures"
version: 1
---
## Statement
The system selects actions by their predicted consequences for a single
objective that is fixed across the episode.

## Source
Reconstructed from Omohundro 2008, section 2: "Because they are goal directed,
they will try to change themselves to better meet their goals in the future",
and section 3: "these systems will try to be rational by representing their
preferences using utility functions whose expectations they try to maximize";
and from Bostrom 2012, section 2, which takes instrumental reasoning toward a
final goal as the meaning of intelligence.

Identified with the assumption of Soares, Fallenstein, Yudkowsky and Armstrong
2015, Corrigibility, footnote 1: "Von Neumann-Morgenstern rational agents (von
Neumann and Morgenstern 1944), that is, agents which attempt to maximize
expected utility according to some utility function." Neither source states
the assumption in this form.

## Notes
Shared by the informal route and the anti-naturality root. The table holds the
trained-policy story and its published reply as two pictures refining the
original filing, plus a residual.

Whether the fixed-objective reconstruction and the complete-fixed-preferences
reconstruction are one assumption is a question for the maintainer; the
identification is the filing session's.
