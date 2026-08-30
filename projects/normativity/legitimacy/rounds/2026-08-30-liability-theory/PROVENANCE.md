# Provenance

This round starts from merged PR69 at `d0132630533e0d27f633d0e493e30ec75f363990`.
It reads the liability hard pass in
`2026-08-30-progress-liability-hard-pass` and audits PR50 without modification at
`fa22b8a21cbd2bde81efe4cb0cd13d5551bbd51d`.

The market interfaces used are the exact theorem seams recorded by the hard pass:
`ProjectionBudget.cumValue_nonneg_of_forall_mem`, the projection force/value lemmas,
the MarketMaker cumulative upper bound, the TradingFirm live-world floor, and
`EnforcementPreservation.no_efficient_trader_exploits`. PR50's one-coordinate and
set-gap claims remain model-supported and unregistered. New claims in this round are
finite convex algebra, the potential-switching identity, and exact-rational fixtures;
no PR50 file, registry, or settled theorem is changed.

