import Cleanroom.Corrigibility.CorrPositionFinds.Basic
import Cleanroom.Corrigibility.CorrPositionFinds.Silence
import Cleanroom.Corrigibility.CorrPositionFinds.Fud
import Cleanroom.Corrigibility.CorrPositionFinds.Assumptions
import Cleanroom.Corrigibility.CorrPositionFinds.PrivateInfo
import Cleanroom.Corrigibility.CorrPositionFinds.Chains
import Cleanroom.Corrigibility.CorrPositionFinds.Cells

/-!
# `corr-position-finds`: findings against the corrigibility position statement

Root module. Every finding about `workflow-2026-09-13/position-statement.md` that the three
later surveys located is shipped here as a Lean witness over `corr-three-step`'s objects — a
refutation instance, or the nearest well-posed pair (the reading that fails and the reading
that survives) — or as a "no statement" verdict in the findings file.

Files: `Basic` (shared infrastructure: the singleton-`Sh` form of D1, the silence posterior),
`Silence` (T1 the manufactured silence, T2 the deceiver's Blackwell side, T8 earned trust),
`Fud` (T3 fully updated deference as arithmetic, T4 Good's theorem up to `εβh`),
`Assumptions` (T5 the dictionary row is A0, T6 minimal viability needs `P(L)`, T9 the
negative-"VOI" anomaly), `PrivateInfo` (T7 private information and the static form of Claim
2.4c), `Chains` (T11 chains across frames, T12 a structural guarantee claim), `Cells` (T10 one
inequality, T13 policies as value learners, T14 the four cells, T15 one accounting).

Deliverables: `run/wp/corr-position-finds/` — report, findings (the primary output), ledger,
open list.
-/
