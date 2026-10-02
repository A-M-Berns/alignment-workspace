import Cleanroom.Decision.DpDutchBook.Defs
import Cleanroom.Decision.DpDutchBook.MsrValues
import Cleanroom.Decision.DpDutchBook.MsrExists
import Cleanroom.Decision.DpDutchBook.EpsFixed
import Cleanroom.Decision.DpDutchBook.NashMap
import Cleanroom.Decision.DpDutchBook.Newcomb
import Cleanroom.Decision.DpDutchBook.BetExt
import Cleanroom.Decision.DpDutchBook.WhoBuys
import Cleanroom.Decision.DpDutchBook.MuggingHybrid
import Cleanroom.Decision.DpDutchBook.Cast
import Cleanroom.Decision.DpDutchBook.NewcombSeed
import Cleanroom.Decision.DpDutchBook.Damascus
import Cleanroom.Decision.DpDutchBook.Demons
import Cleanroom.Decision.DpDutchBook.DamascusHyp
import Cleanroom.Decision.DpDutchBook.Xor
import Cleanroom.Decision.DpDutchBook.Yankees
import Cleanroom.Decision.DpDutchBook.XorTheorem1
import Cleanroom.Decision.DpDutchBook.Bundle
import Cleanroom.Decision.DpDutchBook.Majority
import Cleanroom.Decision.DpDutchBook.MiniatureR

/-!
# `dp-dutch-book`: the book against CDT, mixed-strategy ratifiability and deliberation dynamics

Root module of the package `Cleanroom.Decision.DpDutchBook` (faf-cleanroom run, 2026-09-30);
dependents import this one name. Depends on `Cleanroom.Decision.DpCalibration` and
`Cleanroom.Found.FixKakutani`. See `run/wp/dp-dutch-book/`.

* `Defs` — `SupposedVal` (the cf slot reduced to act values), `r3Val` (D4's tremble-pinned
  value at a deviation), `brSet` (Definition 18's best-response face), `MsrAtD4` (MSR at one
  point, D4 form) and its bridge to `dp-calibration`'s `AdviceEdt` clause.
* `MsrValues` (T7(a)–(b)) — F3′ as a structural fact, the recording lemma
  `ν(a ∧ O_d) = C(d)(a)·ν(O_d)` for every procedure, the payoff factorisation, the
  `ε`-polynomial factorisations, and `r3Val = Q_a(m)/R(m)` at every label.
* `MsrExists` (T7(b)–(d)) — continuity on the simplex, the best-response correspondence with a
  proved closed graph, MSR existence without trembles by `kakutani_findim`.
* `EpsFixed` (T8) — per-`ε` existence of D2At procedures by `kakutani_pi_stdSimplex` over the
  queried points (`ι` arbitrary), and the discharge of `dp-calibration`'s OPEN row
  `testSeq_exists_open` (`testSeq_exists`; `testSeq_exists_open_discharged` has the row's exact
  signature — repair round 1).
* `MiniatureR` (T8(d)) — the `ℝ` witnesses of `d2At_exists` and `testSeq_exists` on the cast
  miniature: `procStarR ε` is `D2At` at every `ε ∈ (0, ½]` (`miniR_d2At_qStar`), and `procR (2/3)`
  is test-sequence tremble-EDT-consistent along `ε_n = 1/(n+2)` (`miniR_testSeq`).
* `NashMap` (T9) — Skyrms's `k`-family Nash map on the miniature: fixed points exactly `2/3`
  (DE = MSR there), the exact one-sided slope factors and the `4/15` threshold, a 2-cycle at
  `k = 1/5`.
* `Newcomb` (T3, T4(a)) — opaque Newcomb's closed forms with `(p, L, S, q)` free: `e`, R1-state,
  R3, the book gaps `Δ_{R1} = qL(1−q)(2p−1)`, `Δ_{R3} = 0`, the argmax lemmas, the reviewer's
  biconditional refuted and its surviving neighbour qualified.
* `BetExt` (T1) — P12's bet extension `attachBet` / `attachBetRegardless` as one constructor,
  label honesty, the master leaf-sum identity, the leaf-wise book identity.
* `WhoBuys` (T2) — the sophisticated bettor declines; with the reverse bet offered regardless,
  `V(buy) − V(decline) = Δ − 2δ`; the myopic bettor's `E[r] − 2δ + Δ`; `Δ` identified with
  P12's `P_{s_d}(a)|c − e|` at the strictly calibrated state.
* `MuggingHybrid` (T4(b), T2's N+) — P12-7's mugging hybrid on `B₁` at the tails node: the
  point is Definition-7-recorded for every procedure, the strictly calibrated tails conditionals
  `(−x, 0)`, the hybrid cf `(V_{B₁}(δ_pay), V_{B₁}(δ_refuse))`, the deterministic payer approved
  yet bookable at its taken act (`Δ = 2`) — the "⇒" of the reviewer's biconditional refuted —
  and the three bettors instantiated: myopic buys for `δ < 1`, sophisticated declines, buys with
  the reverse bet iff `2δ < 2`; the book loses `δ` per tails leaf and `δ/2` in value.
* `Cast` (§3.1, T7(e)) — base change `ℚ → ℝ` (`castDistr`/`castTree`/`castProc`, the leaf
  bijection, transport of `leafLaw`/`nu`/`paySum`/`value`/`condExp`), and the `ℝ`-cast miniature
  as the N+ witness of `msrAtD4_exists`: F3′ structural, `ν(O_d) = 1`, `r3Val m = (2m(b), m(a))`
  at every `ℝ`-label (the casts of `limitVal_mini`), the face flips at `2/3`, `MsrAtD4` iff
  `m(a) = 2/3`, so Kakutani's fixed point is `2/3`.
* `NewcombSeed` (T3, the 6′ side) — opaque Newcomb under the shared seed: the run law
  `C(d)(s)·coin(i)·[s = l]`, conditioning `= (Lp, L(1−p)+S)` = the deviation values (R1-state
  spared, `Δ' = 0`), the do-CDT construal of the forcing value (SE-1(d)) equal to Definition 6's
  conditioning and bitten at `qL(1−q)(2p−1)` — the roles reverse (`opaque_inversion`); the
  deterministic labels have `Δ' = 0` at the taken act under both cfs.
* `Damascus` (T6) — draw-keyed Death in Damascus `didRouted p L c` with `(p, L, c)` free:
  `e(stay) − e(flee) = L(1−p)(1−2q) + c`, Death's marginal `= q` for every skill, the unique
  interior tie `½ + c/(2L(1−p))` iff `p < 1 − c/L`, stay dominates beyond, the prior value's
  completed square with `q_opt = ½ + c/(4L(1−p))` interior iff `p ≤ 1 − c/(2L)`, the gap
  `c²/(8L(1−p))` (the source's `1/8000` is the `p = 0` instance, not `p = ½`), the band rider
  proved, and the marginal-holding cf's tie `½ + c/(2L)` as `c`-data.
* `Demons` (T10) — Skyrms's Nice and Mean Demons as the miniature with diagonal payoffs
  `(u, v)`: under Definition 6 `e = (uq, v(1−q))`, `V_B = uq² + v(1−q)²`, the sampler's tie at
  `v/(u+v)` (`2/3` for both); `δ₁` is `EventTrembleEdtConsistent` iff `u > 0` — on the Nice
  Demon both pure labels are tremble-consistent while `V(δ₁) = 1 < 2` (the plan's N+), on the
  Mean Demon neither is; under 6′ the values are `(u, v)` at every label, Skyrms's `.9/.1` prior
  is the 6′ law and the miniature pays `0` on every 6′ run.
* `DamascusHyp` (T5(a)) — the hypothetical-node encoding `didHyp`: Death's accuracy about the
  live act is `p(q² + (1−q)²) + (1−p)·2q(1−q)`; the abstract problem "conditional accuracy `> ½`
  for both acts" is `MakesInconsistent` for every properly mixed label (the two accuracies sum
  to `1` under strict calibration) and `Consistent` on `didRouted` for `p > ½` — the encoding
  axis.
* `Xor` (T13(a)–(d)) — XOR blackmail with `(δ, c, X, q)` free: under Definition 6 the disaster
  conditional is act-independent so conditioning refuses by `c`, R3 = conditioning at every
  label (F3′ structural with `O_d ≠ ⊤`), R1-state pays by `X − c`, the letter's lie rates; the
  policy values under both semantics; under 6′ evidential choice pays by `X − c`, the value is
  affine in `q`, do-CDT refuses by `c`, the forecast table; implementability under 6′ fails on
  XOR against `D = 1` while the Definition-6 identities hold; the ⇐ direction OPEN in its
  almost-fair form.
* `Yankees` (T7(f)) — Arntzenius's Yankees–Red Sox tree: F3′ structural at both points, the
  standing hypothesis holds at `d_win` and fails at `d_lose`, the tremble-pinned values and D4 in
  closed form at each point, the tie curves derived and shown never to meet (the margins sum to
  `−7/10`), the `(BY, BR)` tremble limit, and `yankees_no_msrAtD4`: no procedure, pure or mixed,
  is D4-approved at both points.
* `XorTheorem1` (T13(a), the fifth evaluator) — Theorem 1's fiber sum on XOR through an
  opaque-leaf shape lemma: refuses by `c(δ(1−2q) + 2q(1−δ))`, positive for `δ < ½`; no label
  with `q > 0` is D3⁰-consistent.
* `Bundle` (T1(c), T5(b)–(d)) — P09's bundled book on Death in Damascus (hypothetical-node
  prediction, the live act with its bundled side bet, the post-act sell point): Definition 6's
  strict values equal the marginal-holding cf's (`bundleVal`), under 6′ nobody survives
  (`bundleVal'`); the booked label `(0, ½, 0, ½)` approved at the strict grade and declined at
  every full-support self-model, the classical values `(4, 9/2, 4, 9/2)`, the leaf-wise `k' − k`;
  booking one act moves the tie to `21/40` (values `(19/4, 167/40, 19/4)`), approved, strict
  `T_EDT` refuses it under 6′, `V' = −19/80`; the Definition-6 keep tie `11/23` and
  `bundle_no_pair_def6`; F10's discrepancy identity.
* `Majority` (T12) — mako yass's majority game, three copies of one point: under Definition 6
  the live draw is independent of "both others drew `a`" (a product identity) and the
  conditional value of `a` is `1 − (1−q)²`; under 6′ all copies draw alike, the product identity
  fails at every properly mixed label and the conditional says "majority = me".
-/
