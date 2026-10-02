import Cleanroom.Found.LiAsympCalc.Compactness
import Cleanroom.Found.LiAsympCalc.WeightedAverage

/-!
# `tt-ladder`: definitions of record

The definitions module of the package `Cleanroom.Li.TtLadder` ([[tt-ladder-mandate]]). Only
definitions and their unfolding lemmas live here.

**Scope (every declaration below).** Everything is stated over two *real sequences*
`a : ℕ → ℝ` (a quote) and `e : ℕ → ℝ` (a credence), joined by FAF's ramp `ctsInd` and FAF's
asymptotic order `AsympGE`; no inductor, market or trader appears. These are the *readings* of
Total Trust that `faithful-acceleration.md` §5 and `li-deference.md` lines 233–246 range over,
made into predicates so that a later package can name the rung it lands on. **Not a theorem
about inductors**, and nothing here is called Total Trust.

**Conventions pinned here** (dependents rely on them):

* `ctsInd δ x y` (FAF, `Properties/SelfTrust.lean`) ramps in its *first* argument exceeding the
  second: `0` at `x ≤ y`, `1` at `x ≥ y + δ`. So the gate is `ctsInd δ (a n) t` = `Ind_δ(a_n > t)`
  and the violation ramp is `ctsInd δ (t - ε) (e n)` = `Ind_δ(e_n < t − ε)`.
* `viol e a t ε δ n` is `li-asymp-calc`'s violation weight (`Compactness.lean`), definitionally
  `gateSeq t δ a n * ctsInd δ (t - ε) (e n)` (`viol_eq_gateSeq_mul`); it is reused, never
  re-defined. Parameters `t ε δ : ℚ` as there: the closure theorems quantify over rationals.
* `AsympGE f g` (FAF, `Framework/Asymptotics.lean`) is `∀ ε > 0, ∀ᶠ n in atTop, g n ≤ f n + ε`
  — the `≳ₙ` of the notes; `Filter.liminf` enters only through bridges under `[0,1]` bounds.
* `weightedAverage w x n` (FAF) is `0` while `prefixSum w n = 0`; the averaged predicates put the
  divergence of the gate mass *inside* the predicate as an antecedent, as every source does, so
  that branch is eventually never taken under the antecedent.
* `LCondSeq` is δ-free and stated in `∀ c, ∀ᶠ` form so that it is *true* when the gate is
  touched only finitely often (the sources' convention), without a `liminf` along a restricted
  filter.
* A negative or zero width `δ` is never meaningful: at width `0` the gate is identically `0`
  (Lean's `x / 0 = 0`) and every fixed-`t` predicate is trivially true; at a negative width FAF's
  ramp fires in the reverse direction. Every lemma whose meaning depends on the width carries
  `0 < δ`; the width-free exceptions (`lProdSeq_iff_tendsto`, `tSeq_of_tAllEpsSeq`,
  `avgSeq_of_nonpos`, `lProdSeq_parked_iff`, the `[0,1]` bounds on `gateSeq`) are true at every
  width because `min 1 (max 0 _)` is, and say so in their docstrings.
* A quote that never exceeds `t` (a *silent* quote) satisfies every fixed-`t` predicate below,
  and `SupportNondegenerate`, for every credence: the fixed-`t` diagram says nothing on it
  (`silent_quote_floor`, `WitnessesConst.lean`) — the floor mirror of Cor 5's `e ≡ 1` ceiling.
-/

namespace Cleanroom.Li.TtLadder

open LogicalInduction Filter Topology
open Cleanroom.Found.LiAsympCalc

/-! ## The gate and the single-instance predicates -/

/-- The soft gate `G_n = Ind_δ(a_n > t)` as FAF's ramp `ctsInd δ (a n) t` (trust-lab's `gate`,
`li-deference`'s `g_n`). Over real sequences; not a theorem about inductors.
Source: lean-deference-2-001; root-fa-007; trust-lab-059 (`gate`); [[li-deference]] l.234
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
noncomputable def gateSeq (t δ : ℚ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ctsInd δ (a n) (t : ℝ)

/-- `T(t,ε,δ)`: the violation weight `w_n = G_n · Ind_δ(e_n < t − ε)` is summable — the
single instance of "bounded ε-violation" (the notes' "the Theorem"). The weight is
`li-asymp-calc`'s `viol e a t ε δ`. Over real sequences; not a theorem about inductors.
Source: lean-deference-2-001; root-fa-007; trust-lab-059 (`BoundedEpsViolation`); [[li-deference]] l.235
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
def TSeq (a e : ℕ → ℝ) (t ε δ : ℚ) : Prop :=
  Summable (viol e a t ε δ)

/-- `T_∀ε(t)`: `T(t,ε,δ)` for every rational margin `ε > 0`, at fixed `t, δ`. Over real
sequences; not a theorem about inductors.
Source: lean-deference-2-001 (`T_∀ε`); lean-deference-046 Prop A
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
def TAllEpsSeq (a e : ℕ → ℝ) (t δ : ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → TSeq a e t ε δ

/-- `T_full` at fixed width `δ`: `T(t,ε,δ)` for every rational threshold `t` and margin
`ε > 0`. Independence of `δ` is a *theorem* (`Closure.lean`, `tFullSeq_iff_tFullSeq`), not part
of the definition; the all-`δ` form `∀ δ > 0, TFullSeq a e δ` is the left side of
`li-asymp-calc`'s `summable_viol_iff_dominates`. The family runs over *every* rational `t`,
where the sources' runs over `t ∈ [0,1]`; under the sources' standing bounds (`a ≤ 1`, `0 ≤ e`)
the two coincide (`tFullSeq_iff_Icc`, `Bounds.lean`: for `t ≥ 1` the gate is `0`, for `t < 0`
the violation ramp is `0`), and the extra thresholds carry content only off those bounds — which
is why the closure theorems, which assume only `a ∈ [0,1]`, take the all-`t` form. Over real
sequences; not a theorem about inductors.
Source: lean-deference-2-001 (`T_full`); lean-deference-2-004
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
def TFullSeq (a e : ℕ → ℝ) (δ : ℚ) : Prop :=
  ∀ t ε : ℚ, 0 < ε → TSeq a e t ε δ

/-- `BV(t,δ)`, bounded violation without margin: `Σ_n G_n · Ind_δ(e_n < t) < ∞`
(`li-deference`'s `Σ v_n`, the top rung of `faithful-acceleration` §5). It is the `ε = 0`
instance of `TSeq` (`bvSeq_iff_summable_viol_zero`). Over real sequences; not a theorem about
inductors.
Source: lean-deference-2-001 (`BV`); root-fa-007; trust-lab-059 (`BoundedViolation`); [[li-deference]] l.238
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
def BVSeq (a e : ℕ → ℝ) (t δ : ℚ) : Prop :=
  Summable (fun n => gateSeq t δ a n * ctsInd δ (t : ℝ) (e n))

/-- `L_prod(t)`: `G_n · (e_n − t) ≳ₙ 0` over FAF's `AsympGE` — the notes' "limit" rung under the
product reading, `li-deference`'s `q_n ≳ₙ 0`, trust-lab's `LimitRung`. Equivalent to
`G_n · max 0 (t − e_n) → 0` (`lProdSeq_iff_tendsto`, `Arrows.lean`). Over real sequences; not a
theorem about inductors.
Source: lean-deference-2-001 (`L_prod`); root-fa-007; trust-lab-059 (`LimitRung`); [[li-deference]] l.236
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
def LProdSeq (a e : ℕ → ℝ) (t δ : ℚ) : Prop :=
  AsympGE (fun n => gateSeq t δ a n * (e n - t)) (fun _ => 0)

/-- `L_cond(t)`: the credence is eventually not undercut by any margin on gate-touched days —
`∀ c > 0, ∀ᶠ n, t < a n → t − c < e n`, i.e. `liminf_{n : a_n > t} e_n ≥ t` when the gate is
touched infinitely often, and *true* when it is touched only finitely often (the sources'
convention, `lCondSeq_of_finite_gate`; the restricted-filter form is
`lCondSeq_iff_eventually_inf_principal` and the `liminf` bridge for an infinite gate set, under
`e ∈ [0,1]`, is `lCondSeq_iff_liminf` — all in `Arrows.lean`). δ-free: it refers to the hard
event `t < a n`, not to the ramp. The FA chat reads
the note's `E^H_n(X ∣ a_n > t) ≳ₙ t` this way ("the alternative per-day ratio reading makes no
sense per-day") — that is a claim about the note's intent: ATTRIBUTION-UNVETTED. Over real
sequences; not a theorem about inductors.
Source: lean-deference-2-001 (`L_cond`); [[faithful-acceleration]] l.171
Kind: D
Fidelity: variant: sequence-level (the `∀ c ∀ᶠ` form of a conditional `liminf`)
Hyps: n/a -/
def LCondSeq (a e : ℕ → ℝ) (t : ℚ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, (t : ℝ) < a n → (t : ℝ) - c < e n

/-- `Avg(t,ε,δ)`, the averaged rung ("the Corollary"): *if* the gate mass diverges then the
gate-weighted average of `e` is `≳ₙ t − ε − δ`, over FAF's `weightedAverage` (which is `0` at
zero mass — harmless, the antecedent makes that branch eventually never taken). The divergence
antecedent is inside the predicate, as in every source ("let `g` be any gate with `Σ g = ∞`"):
the predicate is *conditional on divergent gate mass and vacuous otherwise* — on a summable gate
it holds against every credence (`avgSeq_gatedMeanSeq_vacuous_sqQuote`, `Witnesses.lean`); in
every `Avg ∧ ¬T` witness the divergence is forced by `¬T`, since the weight is `≤` the gate.
Over real sequences; not a theorem about inductors.
Source: lean-deference-2-001 (`Avg`); root-fa-006; trust-lab-059 (`AveragedRung`); [[faithful-acceleration]] l.159
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
def AvgSeq (a e : ℕ → ℝ) (t ε δ : ℚ) : Prop :=
  Tendsto (prefixSum (gateSeq t δ a)) atTop atTop →
    AsympGE (weightedAverage (gateSeq t δ a) e) (fun _ => (t : ℝ) - ε - δ)

/-- The margin-free gated mean: *if* the gate mass diverges then the gate-weighted average of
`e` is `≳ₙ t` — `li-deference`'s "gated Total Trust" (l.216–226) and the bare mean of
root-fa-007's incomparability sentence. Distinct from `AvgSeq` (no `ε + δ` slack). Like
`AvgSeq`, conditional on divergent gate mass and vacuous otherwise
(`avgSeq_gatedMeanSeq_vacuous_sqQuote`). Over real sequences; not a theorem about inductors.
Source: [[li-deference]] l.216–226 (root-deference-051/052); [[faithful-acceleration]] l.140
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
def GatedMeanSeq (a e : ℕ → ℝ) (t δ : ℚ) : Prop :=
  Tendsto (prefixSum (gateSeq t δ a)) atTop atTop →
    AsympGE (weightedAverage (gateSeq t δ a) e) (fun _ => (t : ℝ))

/-- The gate is bounded away from `0` where positive ("effectively hard": `G_n ∈ {0} ∪ [c,1]`).
The proviso under which the notes' "limit ⇒ bounded-ε-violation" arrow is repaired
(`Repair.lean`). It holds vacuously for a silent quote (gate identically `0`,
`silent_quote_floor`), where the repaired diagram says nothing; its non-trivial inhabitant is
`repair_witness`. Over real sequences; not a theorem about inductors.
Source: trust-lab-061 (c); root-deference-2-006 (`g_n ∈ {0} ∪ [γ,1]`)
Kind: D
Fidelity: variant: sequence-level
Hyps: n/a -/
def SupportNondegenerate (t δ : ℚ) (a : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n, 0 < gateSeq t δ a n → c ≤ gateSeq t δ a n

/-- A window-disjoint schedule: strictly increasing with `2 ^ d k ≤ d (k+1)` — v3 §3's shape,
*without* any computability clause (v3's "e.c. in the index" reading empties the class; see
[[tt-ladder-findings]] and `Schedules.lean`). Over `ℕ → ℕ`; not FAF's `DeferralFunction`.
Source: [[fa-positive-results-corrected-v3]] §3 l.52; root-fa-2-003
Kind: D
Fidelity: variant: sequence-level (computability clause dropped, deliberately)
Hyps: n/a -/
def WindowDisjoint (d : ℕ → ℕ) : Prop :=
  StrictMono d ∧ ∀ k, 2 ^ d k ≤ d (k + 1)

/-! ## Unfolding lemmas -/

/-- The violation weight is the gate times the violation ramp, definitionally.
Source: none: infrastructure (`li-asymp-calc` `viol`, `dsWeight`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem viol_eq_gateSeq_mul (a e : ℕ → ℝ) (t ε δ : ℚ) (n : ℕ) :
    viol e a t ε δ n = gateSeq t δ a n * ctsInd δ ((t : ℝ) - ε) (e n) := rfl

/-- `BV(t,δ)` is the `ε = 0` instance of the violation-weight family: `Summable (viol e a t 0 δ)`.
This makes monotonicity in `ε` the whole content of `BV ⇒ T_∀ε`.
Source: lean-deference-2-001; [[tt-ladder-mandate]] target 1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bvSeq_iff_summable_viol_zero (a e : ℕ → ℝ) (t δ : ℚ) :
    BVSeq a e t δ ↔ Summable (viol e a t 0 δ) := by
  have h : viol e a t 0 δ = fun n => gateSeq t δ a n * ctsInd δ (t : ℝ) (e n) := by
    funext n
    rw [viol_eq_gateSeq_mul]
    simp
  rw [BVSeq, h]

/-- The gate lies in `[0,1]`.
Source: none: infrastructure (FAF `ctsInd_mem_Icc`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_mem_Icc (t δ : ℚ) (a : ℕ → ℝ) (n : ℕ) : gateSeq t δ a n ∈ Set.Icc (0 : ℝ) 1 :=
  ctsInd_mem_Icc δ (a n) t

/-- `0 ≤ gateSeq t δ a n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_nonneg (t δ : ℚ) (a : ℕ → ℝ) (n : ℕ) : 0 ≤ gateSeq t δ a n :=
  (gateSeq_mem_Icc t δ a n).1

/-- `gateSeq t δ a n ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_le_one (t δ : ℚ) (a : ℕ → ℝ) (n : ℕ) : gateSeq t δ a n ≤ 1 :=
  (gateSeq_mem_Icc t δ a n).2

/-- For a positive width the gate is positive exactly on the hard event `t < a n`.
Source: none: infrastructure (`li-asymp-calc` `ctsInd_pos_iff`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_pos_iff {t δ : ℚ} (hδ : 0 < δ) (a : ℕ → ℝ) (n : ℕ) :
    0 < gateSeq t δ a n ↔ (t : ℝ) < a n :=
  ctsInd_pos_iff hδ (a n) t

/-- For a positive width the gate vanishes exactly off the hard event: `a n ≤ t`.
Source: none: infrastructure (`li-asymp-calc` `ctsInd_eq_zero_iff`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem gateSeq_eq_zero_iff {t δ : ℚ} (hδ : 0 < δ) (a : ℕ → ℝ) (n : ℕ) :
    gateSeq t δ a n = 0 ↔ a n ≤ t :=
  ctsInd_eq_zero_iff hδ (a n) t

/-- The violation weight is nonnegative.
Source: none: infrastructure (`li-asymp-calc` `dsWeight_nonneg`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem viol_nonneg (a e : ℕ → ℝ) (t ε δ : ℚ) (n : ℕ) : 0 ≤ viol e a t ε δ n :=
  dsWeight_nonneg _ _ _ _ _

/-- The violation weight is at most `1`.
Source: none: infrastructure (`li-asymp-calc` `dsWeight_le_one`)
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem viol_le_one (a e : ℕ → ℝ) (t ε δ : ℚ) (n : ℕ) : viol e a t ε δ n ≤ 1 :=
  dsWeight_le_one _ _ _ _ _

end Cleanroom.Li.TtLadder
