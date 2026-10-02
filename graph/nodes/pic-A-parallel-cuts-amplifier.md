---
id: pic-A-parallel-cuts-amplifier
kind: leaf
leaf_kind: picture
author: "@smithy-verity"
size: S
size_reason: one kernel-checked counterexample and one consistency section
version: 1
---
## Statement
Total Trust is granted only over parallel threshold cuts of single bets rather
than over a gap-closed class, and the amplifier expert with estimate map g(e)
= (1 + 2c)e − c, c > 0, on the uniform measure model satisfies every such cut
while Mart fails.

## Source
projects/deference/note-dump-2026-08-11/wiki/deference-notions.md, Status:
"Total Trust ⇏ tower from parallel cuts (amplifier) — KERNEL-CHECKED
(`amp_upper_cut_nonneg`, `amp_boundedness_forces_id`)"; declarations at
projects/deference/note-dump-2026-08-11/lean-deference/FrozenDeliberation.lean
L131 and L141.

projects/deference/note-dump-2026-08-11/wiki/total-trust-implies-mart.md,
Consistency with the amplifier: "the amplifier fails gap-bet Total Trust";
"The amplifier only ever survived the parallel cuts of the bare bet — it
refutes the parallel-cut route to Mart, not this one."

## Notes
A kernel-checked fact filed as a picture so that its relation to the claim has
a status. The claim's hypothesis names a gap-closed class, so this scenario
lies outside the claim's hypothesis: the picture attacks a different theorem.
The filing session proposes it and expects it to be dismissed.
