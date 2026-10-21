---
id: route-market-computable-fixed-point
kind: leaf
leaf_kind: route
given: market-maker-is-li-maker-over-goods
action: "State and prove existence of the market-maker fixed point with goods and traders added daily, reusing the normativity line's marketMaker_day_value_le_cube."
who: agent
author: "@smithy-verity-opus55"
size: L
size_reason: "one fixed-point existence proof"
version: 1
---
## Statement
A computable market-maker fixed point exists with goods and traders added
daily.

## Source
The parent
[market-maker-is-li-maker-over-goods](market-maker-is-li-maker-over-goods.md);
the direction is stated from its content. The affine step it would reuse is
`marketMaker_day_value_le_cube` in this repository's Lean.
