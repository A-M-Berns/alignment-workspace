import Cleanroom.Li.TtLadder.Defs
import Cleanroom.Li.TtLadder.Arrows
import Cleanroom.Li.TtLadder.Closure
import Cleanroom.Li.TtLadder.Averaged
import Cleanroom.Li.TtLadder.Witnesses
import Cleanroom.Li.TtLadder.WitnessesConst
import Cleanroom.Li.TtLadder.WitnessesLog
import Cleanroom.Li.TtLadder.Repair
import Cleanroom.Li.TtLadder.Schedules
import Cleanroom.Li.TtLadder.Rates
import Cleanroom.Li.TtLadder.Bounds

/-!
# `tt-ladder`: the strength ladder of Total-Trust readings

Root module of the package `Cleanroom.Li.TtLadder`; dependents import this one name.
Mandate: `run/wp/tt-ladder/tt-ladder-mandate.md`; report, findings and ledger beside it.

Everything here is **pure real analysis over two sequences** `a` (a quote) and `e` (a
credence), stated over FAF's ramp `ctsInd`, FAF's asymptotic order `AsympGE`, FAF's
`prefixSum`/`weightedAverage`, and `li-asymp-calc`'s violation weight `viol` and `Dominates`.
No inductor appears; nothing is called Total Trust.

* `Defs`: the readings as predicates — `gateSeq`, `TSeq`, `TAllEpsSeq`, `TFullSeq`, `BVSeq`,
  `LProdSeq`, `LCondSeq`, `AvgSeq`, `GatedMeanSeq`, `SupportNondegenerate`, `WindowDisjoint`.
* `Arrows`: the sound arrows at fixed `t, δ` — `BV ⇒ T_∀ε ⇒ T(t,ε)`, `L_cond ⇒ T_∀ε`,
  `L_cond ⇒ L_prod`, Prop A `T_∀ε ⇒ L_prod` (for `e ≥ 0`), `BV ⇒ L_prod`; the bridges
  `L_prod ⟺ G·(t−e)⁺ → 0` and, for `L_cond`, the finite-gate convention, the restricted-filter
  form and the `liminf` form along `atTop ⊓ 𝓟 {n ∣ t < a n}`.
* `Closure`: Prop B at fixed width — `T_full(δ) ⟺ Dominates ⟺ ∀t·L_cond`; δ-independence;
  bridges to `li-asymp-calc`'s all-`δ` form and to `0 ≤ liminf (e − a)`; at the closure
  "summable" is "eventually zero"; the schedule form.
* `Averaged`: the averaged lemma over an abstract gate (the notes' Corollary), `T ⇒ Avg`.
* `Witnesses`, `WitnessesConst`, `WitnessesLog`: W1–W7, creep, park/park′, gap, alt, the
  trust lab's `witness_gate`/`middle_rung_false`/`witness_not_averaged`, Prop A's lower-bound
  counterexample, the averaged lemma's full-package witnesses (solid and harmonic gate), Cor 5's
  one-sided ceiling, its silent-quote floor and the rate-free limit; every non-arrow of the
  Hasse diagram as an explicit `∃ a e`.
* `Repair`: support-nondegeneracy repairs the middle rung and collapses `L_prod`, `L_cond`,
  `T_∀ε` into one (no bounds on `e`); `witness_gate_no_gap`; a non-constant witness.
* `Schedules`: the greedy lemma and its corollary, the tower, root-fa-015's separating profile,
  the staircase refuting root-fa-2-003 (ii)'s converse, the growth lemma.
* `Rates` (extension): the `L²` rung and its sharpness at a straddled threshold, the `L¹` rung
  under the solid gate with both sides at the package's width, the parked rung (`∑ G < ∞`
  versus `G → 0`).
* `Bounds` (repair round 2): where the standing bounds are load-bearing — `0 ≤ e` for
  `T ⇒ Avg` and for `BV ⇒ L_prod`, `a ∈ [0,1]` for both closure `⟹` directions — each with a
  counterexample; the threshold range (`T_full` over all rational `t` equals `T_full` over
  `t ∈ [0,1]` under the bounds); and uniformity across thresholds at the closure: under
  dominance the weight vanishes from one day on uniformly in `t` at each margin, while
  uniformity in `(t, ε)` is "eventually no violation" and fails for W7.
-/
