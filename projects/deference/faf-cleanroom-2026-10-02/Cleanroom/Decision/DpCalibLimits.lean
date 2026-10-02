import Cleanroom.Decision.DpCalibLimits.Defs
import Cleanroom.Decision.DpCalibLimits.Popper
import Cleanroom.Decision.DpCalibLimits.Rays
import Cleanroom.Decision.DpCalibLimits.TwoRoute
import Cleanroom.Decision.DpCalibLimits.Nonstandard
import Cleanroom.Decision.DpCalibLimits.MiniatureTS
import Cleanroom.Decision.DpCalibLimits.Seq
import Cleanroom.Decision.DpCalibLimits.Family
import Cleanroom.Decision.DpCalibLimits.TsMsr
import Cleanroom.Decision.DpCalibLimits.AppendixB
import Cleanroom.Decision.DpCalibLimits.Zo1
import Cleanroom.Decision.DpCalibLimits.Cancellation
import Cleanroom.Decision.DpCalibLimits.Sampler
import Cleanroom.Decision.DpCalibLimits.Chicken
import Cleanroom.Decision.DpCalibLimits.Skyrms
import Cleanroom.Decision.DpCalibLimits.Theses
import Cleanroom.Decision.DpCalibLimits.SscMasked
import Cleanroom.Decision.DpCalibLimits.Traps
import Cleanroom.Decision.DpCalibLimits.ChanceTwin
import Cleanroom.Decision.DpCalibLimits.PopperClass
import Cleanroom.Decision.DpCalibLimits.SinglePoint
import Cleanroom.Decision.DpCalibLimits.WitnessesR1
import Cleanroom.Decision.DpCalibLimits.WitnessesR2
import Cleanroom.Decision.DpCalibLimits.Curve
import Cleanroom.Decision.DpCalibLimits.MugPerRun
/-!
# `dp-calib-limits`: calibration at the limit — Popper functions, ray dependence, the device
family, Appendix B's variants, ZO-1 and the manifold

Root module of the package `Cleanroom.Decision.DpCalibLimits` (the plan's split of
`dp-calibration`; see `run/wp/dp-calib-limits/`). Depends on `Cleanroom.Decision.DpCalibration`.

* `Defs` — §3 definitions of record: `IsPopper`/`popperLimit` (the `≡ 1` convention), `Ray`
  and the ray polynomials, `NonnegNear0`, `MSRAt`/`MSR`, the abbrevs `FF`/`TS`/`MSR17At`/`DE`,
  `EpsFP`, the chicken rule, the Weak Thesis, per-run SSC with a self-model, the grid's
  uniform substitution, the manifold.
* `Popper` (T1) — Definition 10's limit conditional is a Popper function; with the junk `0`
  exactly (P1) fails; the LPS reading (`limitCond_eq_lps`, level `0` = `ν_C`).
* `Rays` (T2(a),(b),(e)) — ray-independence at realized observations; Lemma 2 along every ray.
* `TwoRoute` (T2(c),(d)) — SE-18′(b)'s `(5,15)/(10,0)/(0,30)`; the single-point claim refuted
  at three actions.
* `Nonstandard` (T3(a),(b)) — the bridge lemma; D2 ⟺ `NonnegNear0` of the cross polynomials.
* `MiniatureTS` (T3(c)) — `q*(ε)` trembles to exactly `2/3`; FF ⊊ TS on the miniature.
* `Seq` — elementary convergence and continuity of the run law in the weights.
* `Family` (T4) — MSR vs D4, FF ⊆ TS, TS ⊆ MSR under realized acts, MSR ⊆ MSR¹⁷ under
  recording, εFP ⟺ D2 and `lim εFP ⊆ TS`.
* `TsMsr` (T4(c)) — **TS ⊄ MSR**: a test-sequence limit whose uniform-ray values reverse.
* `AppendixB` (T5) — the 4×2 cell table on `t1`/`fantasy241`/`fantasy541`.
* `Zo1` (T6(a),(c)) — ZO-1's letter-proof separation; the uniform substitution.
* `Cancellation` (T6(b), T7(a)–(c)) — the factorisation, the cancellation lemma, the manifold,
  self-transparency on it, which zeros survive.
* `Sampler` (T8) — the sampler's act-accuracy from the run law; stipulated accuracies are
  inconsistent under Definition 6 and met by the 6′-statistics.
* `Chicken` (T9) — the anti-zero-respecting rule refused at recorded deterministic points;
  fixed-point-free under a unique maximiser.
* `Skyrms` (T10) — the Ratifiability Lemma.
* `Theses` (T11) — the Weak Thesis as a grade on the miniature; Levi's vacuity.
* `SscMasked` (T12) — per-run SSC with a full-support self-model on `TB(θ)`.
* `Traps` (T13) — trap rays: Lemma 2 survives, the device is silent on the trap.
* `ChanceTwin` (T15) — not every Popper function is a ray limit (refutation).
* `PopperClass` (T16) — Definition 10 = its Popper reading; the chance-conditional invariance.
* `SinglePoint` (T2(d)) — the two-action single-point ray-independence, proved (repair round 1;
  stated OPEN in the first round): along any full-support ray of a pure label the limit is the
  ray-free level-mass ratio.
* `WitnessesR1` (repair round 1) — the hypothesis-package witnesses the audits asked for:
  `TB(θ)`'s per-run state, the cancellation and recording packages on `coinQuery`, T4(c),(d)
  on `coinQuery`, MSR¹⁷ ⊋ MSR on the recorded `t1`, the twin-leaf invariance on `chanceTwin`,
  the εFP form of the `TS ⊄ MSR` family, `Σ_{½}` consistent.
* `WitnessesR2` (repair round 2) — the non-degenerate witnesses: `condExp_deviate_eq` on a tree
  with coin-dependent payoffs (`cqPay`, common value `½`), both sides of `tb_masked_flip`,
  `twoAct_single_point_ray_independent` on two genuinely different rays of `δ_b`, and
  `msr17At_of_msrAt_recorded`'s package with a strict maximum (`t1` with `δ_b`).
* `Curve` (T7(e), stretch; repair round 2) — the miniature's run law is the product of the label
  with itself, the calibration manifold there is the open curve `(m², m(1−m), m(1−m), (1−m)²)`,
  CA-10′'s off-curve product state confirmed, and the convex hull strictly exceeds the manifold
  (the midpoint of `m = ¼` and `m = ¾`); the mandate's witness pairing corrected (F19).
* `MugPerRun` (T12(c), stretch; repair round 2) — on `mug1` (`occ(d)` = all runs) the per-run
  clauses are the strict clauses at `O_d = ⊤`, and per-run SSC with a self-model is Definition 9
  (LF) at `O_d = ⊤` under either null-case reading: the combined state is prior calibration of
  `C[d ↦ m]`.
-/
