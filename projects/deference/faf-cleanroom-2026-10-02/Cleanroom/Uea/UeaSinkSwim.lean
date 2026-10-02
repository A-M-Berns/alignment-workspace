import Cleanroom.Uea.UeaSinkSwim.TheoremA
import Cleanroom.Uea.UeaSinkSwim.ResidualArgmax
import Cleanroom.Uea.UeaSinkSwim.TrapChain
import Cleanroom.Uea.UeaSinkSwim.NewcombOpaque
import Cleanroom.Uea.UeaSinkSwim.NewcombTransparent
import Cleanroom.Uea.UeaSinkSwim.BestOnPath
import Cleanroom.Uea.UeaSinkSwim.BestOnPathPolicy
import Cleanroom.Uea.UeaSinkSwim.Updateless
import Cleanroom.Uea.UeaSinkSwim.PolicyFloor
import Cleanroom.Uea.UeaSinkSwim.FiveTen
import Cleanroom.Uea.UeaSinkSwim.Mixtures
import Cleanroom.Uea.UeaSinkSwim.Corner
import Cleanroom.Uea.UeaSinkSwim.Twin
import Cleanroom.Uea.UeaSinkSwim.Martingale
import Cleanroom.Uea.UeaSinkSwim.Dogmatic
import Cleanroom.Uea.UeaSinkSwim.ChainCorollaries

/-!
# `Cleanroom.Uea.UeaSinkSwim`: sink-or-swim, D0–D2, Newcomb in the sequential model

Root module of the `uea-sink-swim` work package (faf-cleanroom run, 2026-09-30). Depends on
`Cleanroom.Uea.UeaColeShadow` (imported narrowly, never edited).

* `TheoremA`: the sink-or-swim characterization as two-sided iffs for every `Params` (A0–A5), the N+ witness,
  and the printed 2025 Theorem 1 refuted in the finite-shadow reading.
* `ResidualArgmax`: D0 — `π^R` is a pure plain fixed point of every model; discharges `uea-cole-shadow`'s
  `pure_exists_open`; `π^R` is the trap on sink-or-swim when `b(1-s) < c`.
* `TrapChain`: D2 — the trap chain for every `K, δ, δ'`: unique fixed point among all policies, strict, root loss
  exactly `1 - (1-δ')^K`; target 9(−): no horizon-free `δ` at `γ = 1`.
* `NewcombOpaque`: `T = 1` lemmas; opaque Newcomb three-way at `1001/2000`; 2-003's `ξ`-null fallback.
* `NewcombTransparent`: transparent Newcomb — 2box the unique fixed point, `gap = 0`, `TB`, the true values.
* `BestOnPath`, `BestOnPathPolicy`: D1 — the best-on-path recursion `B` with `V^* - B ≤ 1-(1-δ)^(T-1-n)`, the policy
  `π^B` (pure plain fixed point of every model with that loss at every node with `w ≥ 1-δ`); target 9(+)
  (`∀ε ∀T ∃δ`).
* `Updateless`: `V_upd` facts (threshold `1000/1999`), `VupdSelf`, the prefix-conditioned yardstick, and the
  generic `Upd`-floored fixed point: inert on transparent Newcomb (2box unique for every `U ≤ 1`).
* `PolicyFloor`: the policy-level floor — UDT iff the exact inequality, the self-trap threshold `f*(q, δ)`.
* `FiveTen`: the trap is 5&10; a trust-bound plain fixed point is floored; Instance B's floored-not-plain point.
* `Mixtures`: Observation 1 as abstract mutual dominance (model-free).
* `Corner`: the `δ = 0` corner — a plain fixed point is optimal on residual-null subtrees, no `TB`.
* `Twin`: the three-parameter twin — the trap `ρ`-free, the twin kills the good point, the floor inert.
* `Martingale`: the one-step `1 - w` martingale identity; monotone `w` along a pure path; the mixed witness.
* `Dogmatic`: mupi's Prop 4.29 in finite form (the dogmatic residual, subjective equilibrium, true loss `1/2`) and
  the two-node tree on which `stay` is a fixed point of no residual class (refuting the unqualified transcription).
* `ChainCorollaries` (repair round 1): D1 at the root with no hypothesis; D1 exercised on the trap chain (the D1
  witness); `π^R`, `π^B` on the chain are `stay`; the 2025 refutation under the existential reading too.
-/
