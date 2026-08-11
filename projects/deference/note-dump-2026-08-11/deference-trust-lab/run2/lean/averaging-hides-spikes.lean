/-
  averaging-hides-spikes.lean  —  run2 / TODO "averaging-hides-spikes"  (LEAN-CORE)

  Makes CRITIQUE §2b precise: an asymptotic-AVERAGE Value guarantee gives NO single-round
  safety bound, because a bounded total budget can be dumped into ONE round.

  STANDALONE finite/limit arithmetic about averages vs. sups of a nonnegative real sequence.
  It imports — and needs — NO logical-induction content: no `DeferenceAsymp.value_asymptotic`,
  no `Approx`/`AsympLE` calculus, no `DeferenceTrader.round_profit_ge_gap` (that is the dual
  per-round LOWER bound favouring the truster; THIS is the UPPER-bound FAILURE).  The "Value"
  object and the LI theorems appear NOWHERE as hypotheses (no hypothesis-laundering).

  ----------------------------------------------------------------------------------------------
  TWO "max" notions, both faithful, and we are explicit about which is which:
    • RUNNING SUP over the horizon:  S(T) = max_{i<T} a i.  This is the quantity a worst-case
      safety principal cares about: "the largest single-round swing seen up to horizon T."
    • PER-ROUND swing AT round n:  a n  (= the sup over the single current round).
  ----------------------------------------------------------------------------------------------

  (i)  EXISTENCE (the real content).  Budget `B > 0`, designated round `k`, explicit family
            a i = if i = k then B else 0      (a : ℕ → ℝ).
       The spike `a k = B` is CONSTANT, independent of horizon `T`.
        * `avg_tendsto_zero`            : the T-round AVERAGE  (∑_{i<T} a i)/T  →  0   (Value
                                          "holds" on average), PROVED via Tendsto and B/T → 0.
        * `running_sup_eq_B`           : for every `T > k` the RUNNING SUP  max_{i<T} a i = B,
                                          a fixed constant.
        * `running_sup_not_tendsto_zero` : hence the running sup does NOT → 0.
       ⇒ average-smallness yields NO single-round bound: one round absorbs the whole budget `B`
         while contributing only `B/T = O(1/T)` to the average.

  (ii) MANDATORY NEAR-MISS.  Force per-round budget o(1): `a i ≤ c i`, `0 ≤ a i`, `c i → 0`
       (no single-round concentration).  Then the per-round swing vanishes:
            `swing_tendsto_zero_of_budget_o1` :  a i → 0   (squeeze).
       This certifies the vulnerability is EXACTLY unbounded single-round budget concentration:
       the conclusion `a i → 0` is what FAILS for any persistent-spike family.

       FALSE witness (weaker hyp ⇒ conclusion false).  `running_sup_near_miss_false` exhibits a
       family with `a i ≤ c i` for a sequence `c i → 0` whose RUNNING SUP does NOT → 0 — so the
       o(1)-budget hypothesis controls the PER-ROUND swing but is genuinely INSUFFICIENT for the
       running sup.  This pins down precisely which quantity the near-miss governs and shows the
       theorem is non-vacuous and not over-claimed.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Lattice.Fold

open Finset Filter Topology

namespace AveragingHidesSpikes

/-- The explicit per-round adverse-swing family: a single spike of size `B` at round `k`,
    zero elsewhere.  `B` is the (constant) trader budget; `k` the designated round. -/
def a (B : ℝ) (k : ℕ) : ℕ → ℝ := fun i => if i = k then B else 0

/-- The family is nonnegative when the budget is. -/
theorem a_nonneg {B : ℝ} (hB : 0 ≤ B) (k i : ℕ) : 0 ≤ a B k i := by
  unfold a; split <;> simp [hB]

/-- The spike value at the designated round is exactly the budget `B` — independent of `T`. -/
theorem a_spike (B : ℝ) (k : ℕ) : a B k k = B := by
  unfold a; simp

/-- Every per-round swing is at most `B` (the whole budget). -/
theorem a_le_B {B : ℝ} (hB : 0 ≤ B) (k i : ℕ) : a B k i ≤ B := by
  unfold a; split
  · exact le_refl B
  · exact hB

/-- The total budget over the first `T` rounds is exactly `B`, for every horizon `T > k`.
    (The whole budget is concentrated in round `k`.) -/
theorem sum_eq_B {B : ℝ} (k : ℕ) {T : ℕ} (hT : k < T) :
    ∑ i ∈ range T, a B k i = B := by
  rw [Finset.sum_eq_single k]
  · simp [a]
  · intro b _ hb; simp [a, hb]
  · intro hk; exact absurd (Finset.mem_range.mpr hT) hk

/-! ### (i) EXISTENCE — the real content -/

/-- **The average → 0** (Value "holds on average").  The `T`-round average
    `(∑_{i<T} a i)/T` tends to `0` as the horizon `T → ∞`, because it equals `B/T`
    eventually and `B/T → 0`.  NON-VACUOUS: a genuine `Tendsto`, not the trivial `avg ≤ sup`. -/
theorem avg_tendsto_zero (B : ℝ) (k : ℕ) :
    Tendsto (fun T : ℕ => (∑ i ∈ range T, a B k i) / T) atTop (𝓝 0) := by
  -- the average equals `B / T` for all `T > k`
  have hcongr : (fun T : ℕ => (∑ i ∈ range T, a B k i) / T)
      =ᶠ[atTop] (fun T : ℕ => B / T) := by
    filter_upwards [eventually_gt_atTop k] with T hT
    rw [sum_eq_B k hT]
  refine Tendsto.congr' hcongr.symm ?_
  exact tendsto_const_div_atTop_nhds_zero_nat B

/-- **The single-round running SUP stays = B** (the spike does NOT shrink).  For every horizon
    `T > k`, the running maximum `max_{i<T} a i` equals the full budget `B`, a constant
    independent of `T`.  Uses `Finset.sup'` over the nonempty window `range T`. -/
theorem running_sup_eq_B {B : ℝ} (hB : 0 ≤ B) (k : ℕ) {T : ℕ} (hT : k < T) :
    (range T).sup' ⟨k, Finset.mem_range.mpr hT⟩ (a B k) = B := by
  apply le_antisymm
  · -- every entry ≤ B
    exact Finset.sup'_le _ _ (fun i _ => a_le_B hB k i)
  · -- the entry at k is B and k is in the window
    have hk : a B k k ≤ (range T).sup' ⟨k, Finset.mem_range.mpr hT⟩ (a B k) :=
      Finset.le_sup' (a B k) (Finset.mem_range.mpr hT)
    rwa [a_spike B k] at hk

/-- **So the running sup does NOT tend to 0.**  When `B > 0`, the running sup is the constant
    `B` (for every `T > k`), hence its limit is `B ≠ 0`, so it cannot tend to `0`.  This is the
    *real* direction: average-smallness yields NO single-round bound. -/
theorem running_sup_not_tendsto_zero {B : ℝ} (hB : 0 < B) (k : ℕ) :
    ¬ Tendsto (fun T : ℕ => (range (T + k + 1)).sup'
        ⟨k, Finset.mem_range.mpr (by omega)⟩ (a B k)) atTop (𝓝 0) := by
  -- the sequence is (always) the constant B
  have hconst : (fun T : ℕ => (range (T + k + 1)).sup'
        ⟨k, Finset.mem_range.mpr (by omega)⟩ (a B k))
      = (fun _ : ℕ => B) := by
    funext T
    exact running_sup_eq_B hB.le k (by omega)
  rw [hconst]
  intro hcontra
  have hB0 : Tendsto (fun _ : ℕ => B) atTop (𝓝 B) := tendsto_const_nhds
  exact (ne_of_gt hB) (tendsto_nhds_unique hB0 hcontra)

/-! ### (ii) MANDATORY NEAR-MISS — forcing per-round budget o(1) kills any persistent spike -/

/-- **Near-miss (positive form).**  If the per-round budget is forced `o(1)` — every swing
    `a i ≤ c i` with `0 ≤ a i` and `c i → 0`, i.e. no single-round concentration — then the
    per-round swing sequence itself vanishes (`a i → 0`).  Squeeze theorem.

    This certifies the vulnerability is EXACTLY unbounded single-round concentration: a
    persistent spike `a k' = B` (`B>0`) at infinitely many rounds `k'` would violate `a i → 0`,
    so the o(1)-budget hypothesis is precisely what excludes the adverse family. -/
theorem swing_tendsto_zero_of_budget_o1 {a c : ℕ → ℝ}
    (hnn : ∀ i, 0 ≤ a i) (hle : ∀ i, a i ≤ c i)
    (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc hnn hle

/-- **FALSE witness: the near-miss governs the PER-ROUND swing, NOT the running sup.**
    With a single early spike `b = a B 0` (spike at round `0`) and the bounding budget
    `c i = a B 0 i` itself (which satisfies `b i ≤ c i` and even `c i → 0` PER ROUND), the
    RUNNING SUP `max_{i<T} b i` is the constant `B` and does NOT tend to `0`.  So bounding the
    per-round budget by an `o(1)` sequence does NOT force the running sup to vanish — the o(1)
    hypothesis is exactly strong enough for the per-round conclusion and no stronger.  (Here the
    per-round swing `b i → 0` holds — `swing_tendsto_zero_of_budget_o1` applies — yet the running
    sup persists, confirming the two notions genuinely diverge and the near-miss is non-vacuous.) -/
theorem running_sup_near_miss_false {B : ℝ} (hB : 0 < B) :
    -- per-round budget IS o(1) (each swing ≤ c i, c i → 0) ...
    (∀ i, a B 0 i ≤ a B 0 i) ∧ Tendsto (a B 0) atTop (𝓝 0) ∧
    -- ... yet the RUNNING SUP does not tend to 0.
    ¬ Tendsto (fun T : ℕ => (range (T + 1)).sup'
        ⟨0, Finset.mem_range.mpr (by omega)⟩ (a B 0)) atTop (𝓝 0) := by
  refine ⟨fun i => le_refl _, ?_, ?_⟩
  · -- the single spike's per-round swing DOES tend to 0 (its tail is all zeros):
    -- it is eventually constantly 0 (for i ≥ 1), so the limit is 0.
    have : (a B 0) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with i hi
      have hne : i ≠ 0 := by omega
      simp [a, hne]
    exact Tendsto.congr' this.symm tendsto_const_nhds
  · -- but the running sup is the constant B (k = 0 case of running_sup_not_tendsto_zero):
    have h := running_sup_not_tendsto_zero hB 0
    simpa using h

end AveragingHidesSpikes

#print axioms AveragingHidesSpikes.avg_tendsto_zero
#print axioms AveragingHidesSpikes.running_sup_eq_B
#print axioms AveragingHidesSpikes.running_sup_not_tendsto_zero
#print axioms AveragingHidesSpikes.swing_tendsto_zero_of_budget_o1
#print axioms AveragingHidesSpikes.running_sup_near_miss_false
