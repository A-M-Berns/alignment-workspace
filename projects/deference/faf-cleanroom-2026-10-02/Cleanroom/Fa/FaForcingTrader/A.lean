import Cleanroom.Fa.FaForcingTrader.A.Bridge
import Cleanroom.Fa.FaForcingTrader.A.Mesh
import Cleanroom.Fa.FaForcingTrader.A.TheoremSS
import Cleanroom.Fa.FaForcingTrader.A.Violation
import Cleanroom.Fa.FaForcingTrader.A.Analysis
import Cleanroom.Fa.FaForcingTrader.A.NonDerivability
import Cleanroom.Fa.FaForcingTrader.A.Gating
import Cleanroom.Fa.FaForcingTrader.A.Witnesses
import Cleanroom.Fa.FaForcingTrader.A.Open

/-!
# `fa-forcing-trader` · angle A: the trader route

Root of `Cleanroom.Fa.FaForcingTrader.A` ([[fa-forcing-trader-mandate]], "Attempt angles", A).
Report: `run/wp/fa-forcing-trader/fa-forcing-trader-report-A.md`; ledger `-ledger-A.md`; findings
`-findings-A.md`; open list `fa-forcing-trader-A-open.txt`. Shared definitions: `Defs.lean`,
`Schedule.lean` (package root `Cleanroom/Fa/FaForcingTrader.lean`).

* `Bridge` — T4, the `H`-side Kelly round trip at grade (a): FAF's
  `lic_not_frequently_positive_feedback_return` on `bundle X` along `interleave f d`.
* `Mesh` — T5, the closing-grid mesh term vanishes (`mesh_independence`) and is washed out.
* `TheoremSS` — T6 (general gate; upper/lower quote gates; Tower corollary under readability),
  T7 (`SchedThresholdAbove/Below`, unnormalized form, from the limit point, eventually from a
  full limit, per-day ⟹ averaged), T12 (a).
* `Violation` — T3, v3 Theorem 1 under joint legibility (two-way, partial over the OPEN pair),
  summable corollary, fixed-`X` form.
* `Analysis` — T9 (signed ≠ absolute; the approximant mismatch is not `o(W_n)`), T10 (finite on
  every window-disjoint schedule ⟹ `w_n → 0`; the converse refuted; `ChasingSchedule`; the FAF
  corollaries up to v3's Corollary 2).
* `NonDerivability` — T8 (Prop 7.1, its scheduled restriction, Prop 5.4, the one big lie).
* `Gating` — T12 (b), (c).
* `Witnesses` — the N+ instances: T4 on `li-pseudorandom`'s decided-atom inductor; the
  same-market instances of T3/T6/T7 over `paperDP 𝗜𝚺₁`.
* `Open` — T11, the two-market non-vacuity of (L), OPEN.
-/
