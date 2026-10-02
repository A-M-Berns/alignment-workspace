import Cleanroom.Trust.LegitLiRegister.Defs
import Cleanroom.Trust.LegitLiRegister.Idle
import Cleanroom.Trust.LegitLiRegister.Diagonal
import Cleanroom.Trust.LegitLiRegister.PiOne
import Cleanroom.Trust.LegitLiRegister.Predication
import Cleanroom.Trust.LegitLiRegister.Schedule
import Cleanroom.Trust.LegitLiRegister.Tiling
import Cleanroom.Trust.LegitLiRegister.Gate
import Cleanroom.Trust.LegitLiRegister.Corrigible
import Cleanroom.Trust.LegitLiRegister.Modification
import Cleanroom.Trust.LegitLiRegister.Layers
import Cleanroom.Trust.LegitLiRegister.Certificate
import Cleanroom.Trust.LegitLiRegister.Filtered
import Cleanroom.Trust.LegitLiRegister.Open
import Cleanroom.Trust.LegitLiRegister.Witness

/-!
# `legit-li-register` — root module

Legitimacy as endpoint preservation over FAF histories ([[legit-li-register-mandate]]), namespace
`Cleanroom.Trust.LegitLiRegister`, files under `Cleanroom/Trust/LegitLiRegister/`.

The influence defect `d_n = |Y_n − Hplus (F n) (P^{(n)})|` is `def-frozen-sibling`'s `defect`
(imported, never redefined). What this package establishes about it:

* `Defs` — the legitimacy predicates (`EpsLegitimate`, `LegitimateAlong`), `defect ∈ [0,1]`, the
  `Dist` lemmas, the shared-data congruences, and the relaxed carrier `FrozenSystemL` with T1
  re-proved over it (`trackingL`).
* `Idle` — Target 2: at grade (a) the horizon price agrees with the reader's own anticipation of
  the settled value (`horizon_price_agree_anticipation`); reaching the *truth* on the timely
  fragment costs an `H`-side polarity certificate (`defect_agreeAlong_zero_onG_ofPattern`, the
  headline), discharged where the pattern is e.c. (constant contract; `onGSystem`); the mandate's
  grade-(a) statement is OPEN and believed false (findings F1).
* `Diagonal` — Target 4, Claim 1: `d_n ≥ ½ − δ` eventually on the diagonal contract, from T1 (`hz`),
  the `H`-side read certificate for the diagonal literal, and the arithmetic core
  (`defect_ge_half_diagonal`).
* `PiOne` — Target 5: bounded legitimacy learned (`lic_provind_true`, also deferred-day), global
  legitimacy pinned in `(0,1)` (`lic_nonDogmatism` both duals).
* `Predication` — Target 8: predication is FAF's growing-prefix conditioning, no e.c. book, and the
  dichotomy satisfiable-and-alive / unsatisfiable-and-dead (the scout's trilemma dissolves under
  the asymptotic reading; under its finite book it is exhibited at a logical inductor over the
  dead process and untested at FAF's LIA — findings F6).
* `Schedule` — Target 9: the schedule surface of `thm:wub` named; the truth-correlated schedule
  built; every item resolves truthfully whatever the delay; FAF's bridge is schedule- and
  market-blind at the alternating stream (`truthProcess_bridge_alternating`), inhabited by FAF's
  LIA over the scheduled process itself (`truthProcess_bridge_alternating_lia`); the leak theorem
  at an arbitrary stream OPEN.
* `Tiling` — Target 7: the two-stage finite gate-tiling instability witness and its transparency
  near-miss, exact rationals.
* `Gate` — Target 6: the finite "sound but not safe" frame; the gated update at a non-generable
  gate OPEN; the `ccee` rows imported (ledger).
* `Corrigible`, `Modification`, `Layers`, `Certificate`, `Filtered`, `Open` — Targets 11, 10, 12,
  13, 16, 14/15: definitions of record with their L corollaries and OPEN statements.
* `Witness` — the N+/N− instances at `onGSystem` and FAF's LIA over `paperDP 𝗜𝚺₁`.

Deliverables: `run/wp/legit-li-register/legit-li-register-{report,findings,ledger}.md`,
`legit-li-register-open.txt`.
-/
