import Cleanroom.Fa.FaDelayBsi.Split

/-!
# `fa-delay-bsi` · Witnesses (W1, W5): sequence-level refutations

* **W1** (T3): BSI Theorem C's second display, `∑_k w^{frozen}_{d_k} < ∞` "in any block-stale
  pair", does not follow from the per-day arithmetic: with quote `1`, frozen credence `0` and
  live credence `1`, the frozen weight is `1` every day (not summable) while the violation weight
  is `0` every day. So the per-day inequality's frozen term cannot be dropped by arithmetic. What
  this does **not** show is that some pair of logical inductors realizes these values: that is
  `frozen_divergent_pair_open` (`Open.lean`), and the findings (F3) give reasons the sources'
  scenario is not realizable as described.
* **W5** (E1): no lower bound on violations from the update mass — `|c − F| = 1` every day with
  `violWeight = 0` every day (the forecaster never advertised).

Both are **N−** by construction (constant sequences, [[STANDARDS]] §3's named degenerate pattern;
audit r1 fidelity B3, adversarial B1), adequate for the sequence-level sentences they refute —
a single point suffices against a universal — and nothing more. The inductor-level objects are
out of this package's reach (findings F3, F16).
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- A constant nonzero real sequence is not summable.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem not_summable_const_one : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro hs
  have h := hs.tendsto_atTop_zero
  exact one_ne_zero (tendsto_const_nhds_iff.1 h)

/-- **W1 (T3 (ii), the sequence-level half). The per-day arithmetic does not force the frozen part
to be finite.** For any rationals `t`, `ε > 0`, `δ > 0` with `t + δ ≤ 1` and `0 ≤ t − ε/2 − δ`:
the constant sequences `a ≡ 1` (quote), `F ≡ 0` (frozen credence), `c ≡ 1` (live credence) have
`frozenWeight = 1` on every day — so `∑ frozenWeight` is not summable — while `violWeight = 0` on
every day. This refutes the *sequence-level* universal "for all real `a, c, F`, the frozen sum is
finite" and nothing stronger: BSI §5's display is about pairs of logical inductors, no inductor
is exhibited here, and whether any pair realizes these values is `frozen_divergent_pair_open`
(`Open.lean`; the findings F3 argue the sources' own scenario does not). The mandate's "`Y ≡ 1`,
forecasts perfect" conjunct was `1 − 1 = 0`, connected to nothing, and is dropped (audit r1
adversarial B1 (iv)).
Scope: sequence-level (FAF's `ctsInd`); constant sequences.
Source: BSI §5 line 96 (the second display, "in any block-stale pair"; lean-deference-054); [[delay-program]] §6 T6 line 254 (root-fa-029 (Refutation): "frozen credence `≈ 0`, credence jumps to `≈ 1` mid-block, quote `≈ 1` — the frozen-gated weight is `1` every day with the forecaster's forecasts *perfect*"); [[delay-and-visibility]] §5 (vq-wiki-039 (a))
Kind: N−
Fidelity: variant: sequence-level (the display is about inductor pairs; the inductor-level question is OPEN, `frozen_divergent_pair_open`)
Hyps: (a) none -/
theorem frozen_not_finite_witness {t ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) (ht1 : t + δ ≤ 1)
    (ht0 : 0 ≤ t - ε / 2 - δ) :
    let a : ℕ → ℝ := fun _ => 1
    let F : ℕ → ℝ := fun _ => 0
    let c : ℕ → ℝ := fun _ => 1
    (∀ n, frozenWeight t ε δ (a n) (F n) = 1) ∧
      ¬ Summable (fun n => frozenWeight t ε δ (a n) (F n)) ∧
      ∀ n, violWeight t ε δ (a n) (c n) = 0 := by
  intro a F c
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have ht1R : (t : ℝ) + δ ≤ 1 := by exact_mod_cast ht1
  have ht0R : (0 : ℝ) ≤ t - ε / 2 - δ := by exact_mod_cast ht0
  have hfr : ∀ n, frozenWeight t ε δ (a n) (F n) = 1 := fun n =>
    (frozenWeight_eq_one_iff hδ t ε 1 0).2 ⟨ht1R, by linarith⟩
  refine ⟨hfr, ?_, fun n => ?_⟩
  · have : (fun n => frozenWeight t ε δ (a n) (F n)) = fun _ => (1 : ℝ) := funext hfr
    rw [this]
    exact not_summable_const_one
  · show violWeight t ε δ 1 1 = 0
    unfold violWeight
    rw [(ctsInd_eq_zero_iff hδ ((t : ℝ) - ε) 1).2 (by linarith), mul_zero]

/-- **W5 (E1, closed negatively at the sequence level). No lower bound on violations from the
update mass — as a sequence-level universal.** For any `t`, `ε`, `δ > 0`: the constant sequences
`a ≡ t` (the quote never advertises above `t`), `c ≡ 1`, `F ≡ 0` have `violWeight = 0` on every
day while `|c − F| = 1` on every day. So no inequality of the form `∑ w ≥ κ·∑ |c − F| − O(1)`
with `κ > 0` holds *for arbitrary real sequences*. Degenerate twice over: constant sequences, and
the forecaster says nothing, so no violation is possible for the uninteresting reason — the
regime in which a lower bound would be conjectured (a forecaster that tracks, Theorem A holding)
is not engaged. The inductor-level question (a tracking forecaster, a fresh-question family `H`
settles true) is open and has no named package here (findings F16).
Scope: sequence-level (FAF's `ctsInd`); constant sequences.
Source: [[fa-delay-bsi-mandate]] E1 (the plan's extension: "the deficit bound made two-sided — or the witness that none holds")
Kind: N−
Fidelity: variant: sequence-level (the inductor-level question is open, F16)
Hyps: (a) none -/
theorem no_lower_bound (t ε δ : ℚ) :
    let a : ℕ → ℝ := fun _ => (t : ℝ)
    let c : ℕ → ℝ := fun _ => 1
    let F : ℕ → ℝ := fun _ => 0
    (∀ n, violWeight t ε δ (a n) (c n) = 0) ∧ (∀ n, |c n - F n| = 1) ∧
      ¬ Summable (fun n => |c n - F n|) := by
  intro a c F
  refine ⟨fun n => ?_, fun n => by simp [c, F], ?_⟩
  · show violWeight t ε δ (t : ℝ) 1 = 0
    unfold violWeight
    rw [ctsInd_self, zero_mul]
  · have : (fun n => |c n - F n|) = fun _ => (1 : ℝ) := funext fun n => by simp [c, F]
    rw [this]
    exact not_summable_const_one

end Cleanroom.Fa.FaDelayBsi
