# CF Coverage Continuity interface

Research round testing whether a thin Cartesian-frame-style patch can realize Coverage
contracts against the settled Normative Continuity theorem spine.

The result is negative for a bare map `Q × Z → Ω` and positive for a minimally certified
factorization through an authenticated ambient frame. `SELF_SEALING.md` gives the precise
boundary: Continuity alone cannot prove No Clean Self-Sealing, while unchanged Continuity
plus Coverage-specific resolution soundness proves a genuine safety form. Failure
materialization is needed only for a dedicated failure issue consumed by Progress.

Artifacts: `INTERACTION_INTERFACE.md`, `COVERAGE_CONTRACTS.md`,
`CONTINUITY_BRIDGE.md`, `PROPER_EXERCISE.md`, `SELF_SEALING.md`,
`COUNTERMODELS.md`, and `REPORT.md`. Exact finite fixtures and tests live under `src/`
and `tests/`.
