---
id: natural-latents-approx-coefficient
kind: leaf
leaf_kind: question
given: wentworth-constant-located
action: "Decide the open statement: find a sharper chain-rule route to coefficient 1, or a non-xor refutation, as one clean-room-style Lean file."
who: agent
files: [projects/deference/faf-cleanroom-2026-10-02/]
work:
  - {kind: open, ref: Cleanroom.Info.InfoVoiLatents.Open.natural_latents_approx}
author: "@smithy-verity-opus55"
size: L
size_reason: "one open Lean statement"
version: 1
---
## Statement
Wentworth's approximate natural-latent theorem holds with coefficient 1 on the
third error term.

## Source
projects/deference/faf-cleanroom-2026-10-02/DIGEST.md, §6 item 20: "Wentworth's
approximate theorem with coefficient `1` on `ε₃` (the `2ε₃` bound is proved;
the constant is tight at the xor instance), so either a sharper chain-rule
route or a non-xor refutation settles the quantitative form."
projects/deference/faf-cleanroom-2026-10-02/packages/info-voi-latents/info-voi-latents-audit-r3-fidelity.md,
line 53: the xor instance shows the conjectured constant is tight if true.

## Notes
An open statement of the clean room. On the reading of 'tight': the xor
instance shows the coefficient cannot be lowered
below 1, not that 1 fails.
