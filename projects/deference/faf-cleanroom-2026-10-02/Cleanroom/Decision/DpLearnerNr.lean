import Cleanroom.Decision.DpLearnerNr.Defs
import Cleanroom.Decision.DpLearnerNr.Leak
import Cleanroom.Decision.DpLearnerNr.Modal
import Cleanroom.Decision.DpLearnerNr.LeakLI
import Cleanroom.Decision.DpLearnerNr.TbThetaDoc
import Cleanroom.Decision.DpLearnerNr.KPartStay
import Cleanroom.Decision.DpLearnerNr.Tremble
import Cleanroom.Decision.DpLearnerNr.Explore
import Cleanroom.Decision.DpLearnerNr.Policy
import Cleanroom.Decision.DpLearnerNr.PolicyValues
import Cleanroom.Decision.DpLearnerNr.MisPartition
import Cleanroom.Decision.DpLearnerNr.E1
import Cleanroom.Decision.DpLearnerNr.Enforcer
import Cleanroom.Decision.DpLearnerNr.Diagonal
import Cleanroom.Decision.DpLearnerNr.Refuser
import Cleanroom.Decision.DpLearnerNr.RefuserChain
import Cleanroom.Decision.DpLearnerNr.RefuserTrap
import Cleanroom.Decision.DpLearnerNr.Estimator
import Cleanroom.Decision.DpLearnerNr.EstimatorWitness

/-!
# `dp-learner-nr`: non-responsiveness, the marginal-formula learner and the refuser trap

Root module of the package `Cleanroom.Decision.DpLearnerNr` (mandate
`run/wp/dp-learner-nr/dp-learner-nr-mandate.md`). Depends on `dp-troll-bridge`,
`dp-causal-consist`, `dp-referents-cdt` (cited, not re-shipped) and, through them, `dp-core-tree`,
`dp-calibration`, `dp-local-opt`, `dp-calib-limits`.

* `Defs`: D2 — the act-level marginal formula `cfMarginal`, the pushforward and Bernoulli
  marginals, the troll's response table `trollE` and `cf(cross) = 10 − 20·P(incon)`.
* `Leak`: target 1(a)(b) — the leak `P(Incon) ≥ P(Cross ∧ Incon) ≥ P(Cross) − ε` and the
  unshielded threshold `P(Cross) < ½ + ε`, with N+ witnesses.
* `Modal`: D1 — the (β′) schema `BetaPrime` over GL; target 1(d) NR1 is (β′), not ¬(β)
  (`betaPrime_crosser_not_afflicted`, the constant crosser `⊤` is a (β′) agent); target 1(e) the
  self-misprediction troll; target 8(b) Conjecture F(v) per round.
* `LeakLI`: target 1(c) — price monotonicity on the diagonal (`li_mono`, affine provability
  induction) composed with `dp-troll-bridge`'s `li_lesion_conj` into the LI-level leak
  (`li_leak`); target 8(c) the decided crosser's one-world refutation of the lesion.
* `TbThetaDoc`: D3 — the doc-faithful tree; target 3(a) `V(q) = 10q(1−2θ)`, the deviation gap
  `10(1−2θ)` positive iff `θ < ½` (Proposition 10's rule); 3(b) `bot` non-responsive on both trees;
  3(c) the five evaluations coincide at `10 − 20θ` (`tbThetaDoc_five`); target 4(a) the marginal
  formula is the K-partition value on the bypass tree (`cfMarginal_eq_kPart_tb`).
* `KPartStay`: target 4(a)'s caveat made precise — at the stay label the identity *fails*
  (`−10θ ≠ −10`, `cfMarginal_ne_kPart_stay`), so the general lemma's `hpos` is load-bearing.
* `Tremble`: target 2 — swamping in closed form at the stay and cross labels, the explicit
  `ε → 0` limit, `tremble_neg` re-founded, the P11 regression numerals, and the doc-faithful
  contrast (`swamping_contrast`: nothing is swamped there).
* `Explore`: target 3(d) — the exploring-agent troll `tbThetaExplore`: gap `10(1−ε)(1−2θ)`,
  LICDT `= −10`, N+ `81/10`.
* `Policy`: D4 — `PolicyLearner` (static), `cfPol`, `evPol`, `ExogenousCoord`; target 5(a) the FDT
  property by construction, 5(b) the non-responsiveness clause as a `congr` lemma; target 7(b)
  a policy-fair `Env` determines the learner at the truth; target 4(b) 𝔅 as the one-point learner.
* `PolicyValues`: target 5(c)–(f) — Newcomb (label probe, threshold reader on the grid vs the
  corner comparison, policy-invariant box), TB(θ) at the policy level, XOR (refuse, the jump),
  the mugging (pay iff `y > x`).
* `MisPartition`: targets 6, 7(a) — the flag-reading Omega, the stricter troll and the EMA Omega
  have no round law `F(π, w)` (two-point refutations of policy-fairness).
* `E1`: target 8(a) — E1-static (`e1_static`, with Conjecture F(i) and `limsup p < ½` as (b)
  hypotheses, N+ witness); target 8(d) the regret row.
* `Enforcer`: target 9 — the enforcer's payoff identity `q − c` on `A = a`, `0` otherwise; VOI
  (`voi_nonneg`, `voi_zero_of_certain`).
* `Diagonal`: target 10 — Soto's exploration sentence is FAF's `ParadoxResistanceQuote`
  (`lic_paradox_resistance` instantiated, the price is eventually in `(0,1)`); prices converge
  (`lic_price_convergesTo`).
* `Refuser`: target 11(a) — the inert mugging, likelihood ratio 1, Bayes' rule is the identity,
  the refuser's credence is constant, the myopic rule.
* `RefuserChain`: D5, targets 11(b)–(d) — the GR-16 product chain derived from the mechanics,
  rows sum to one, the absorbing states, the first-step system's unique solution `2/η`, `4/η`,
  the sealed hazard, the two one-way-reset chains' unique stationary distributions.
* `RefuserTrap`: target 11(e) — DY-15: the refuser's state is masked-calibrated on both muggings,
  mixture-calibrated on its own data (the `O_T`-conditional state of every two-point mixture of
  `h₁`, `h₀`, `refuser_mixture_calibrated`), masked-EDT-consistent (the extra the mandate named),
  and uncalibrated only in the deviation statistic.
* `Estimator`: target 14 (stretch) — Conjecture F(i)'s estimator half proved over Mathlib's
  strong law on the `Nat.nth` subsequence of `π₀`-rounds (`cell_mean_converges`; stated OPEN in
  the first session, proved at repair round 1, so `dp-learner-nr-open.txt` is empty).
* `EstimatorWitness`: the N+ witness for target 14 — i.i.d. fair coins under Mathlib's
  `Measure.infinitePi` and the even-round policy (`cell_mean_witness`).
-/
