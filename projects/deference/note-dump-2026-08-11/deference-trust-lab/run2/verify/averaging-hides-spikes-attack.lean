/-
  averaging-hides-spikes-attack.lean  —  FAITHFULNESS GATE (independent skeptic)

  Adversarial re-derivation of the original file's claims, plus:
    (A) HYPOTHESIS-INERTNESS attacks: drop hypotheses; if it still compiles ⇒ inert ⇒ shadow.
        We EXPECT these to FAIL (be commented out / shown false), confirming the hyps are
        load-bearing. The ones that are genuinely inert we leave UNCOMMENTED and they compile.
    (B) FAITHFULNESS PROBE (the real attack): show the EXISTENCE family ITSELF satisfies the
        near-miss hypotheses and even the near-miss conclusion (per-round swing → 0). Hence the
        near-miss (ii) does NOT exclude the vulnerable family (i) — so "(ii) certifies the cause
        of (i)" is the over-claim. This COMPILES (it is a true fact), and is the smoking gun.

  All theorems get `#print axioms`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Lattice.Fold

open Finset Filter Topology

namespace AttackAHS

/-- The original family. -/
def a (B : ℝ) (k : ℕ) : ℕ → ℝ := fun i => if i = k then B else 0

theorem a_spike (B : ℝ) (k : ℕ) : a B k k = B := by unfold a; simp

theorem a_le_B {B : ℝ} (hB : 0 ≤ B) (k i : ℕ) : a B k i ≤ B := by
  unfold a; split
  · exact le_refl B
  · exact hB

theorem sum_eq_B {B : ℝ} (k : ℕ) {T : ℕ} (hT : k < T) :
    ∑ i ∈ range T, a B k i = B := by
  rw [Finset.sum_eq_single k]
  · simp [a]
  · intro b _ hb; simp [a, hb]
  · intro hk; exact absurd (Finset.mem_range.mpr hT) hk

/-! ====================================================================================
    (A) HYPOTHESIS-INERTNESS ATTACKS on `running_sup_eq_B`
    The original needs `hB : 0 ≤ B`. We test: is `hB` inert? If the no-hB version
    compiled, hB would be inert (shadow). We instead PROVE the no-hB version is FALSE
    for B<0 (sup over the window is 0, not B), confirming hB is load-bearing.
    ==================================================================================== -/

/-- For `B < 0`, the running sup is `0`, NOT `B`.  Concretely at `k=0, T=2`:
    window values are `{B, 0}`, sup = 0 ≠ B.  So dropping `hB` makes `running_sup_eq_B`
    FALSE — `hB` is load-bearing (NOT inert). -/
theorem running_sup_eq_B_FALSE_without_hB :
    ∃ (B : ℝ), B < 0 ∧
      (range 2).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (a B 0) ≠ B := by
  refine ⟨-1, by norm_num, ?_⟩
  -- the sup over the window {0,1} of a (-1) 0 = (-1, 0) is 0, not -1.
  -- Show 0 is an upper bound and is attained at index 1, so sup ≤ 0 and sup ≥ a 1 = 0; hence = 0.
  have hub : (range 2).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (a (-1 : ℝ) 0) ≤ 0 := by
    apply Finset.sup'_le
    intro i _; unfold a; split <;> norm_num
  have hlb : (0 : ℝ) ≤ (range 2).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (a (-1 : ℝ) 0) := by
    have h1 : a (-1 : ℝ) 0 1 ≤ (range 2).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (a (-1 : ℝ) 0) :=
      Finset.le_sup' (a (-1 : ℝ) 0) (Finset.mem_range.mpr (by omega))
    have : a (-1 : ℝ) 0 1 = 0 := by unfold a; norm_num
    rwa [this] at h1
  have hval : (range 2).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (a (-1 : ℝ) 0) = 0 :=
    le_antisymm hub hlb
  rw [hval]; norm_num

/-! ====================================================================================
    (A') HYPOTHESIS-INERTNESS ATTACKS on the near-miss `swing_tendsto_zero_of_budget_o1`.
    Original hyps: hnn (0 ≤ a), hle (a ≤ c), hc (c → 0). We test each.
    ==================================================================================== -/

/-- Drop `hc` (c → 0).  Without it the conclusion fails: take a = c = const 1, then
    0 ≤ a, a ≤ c, but a ↛ 0.  So `hc` is load-bearing. (FALSE-witness for the no-hc version.) -/
theorem nearmiss_FALSE_without_hc :
    ∃ (a c : ℕ → ℝ), (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≤ c i) ∧
      ¬ Tendsto a atTop (𝓝 0) := by
  refine ⟨fun _ => 1, fun _ => 1, fun _ => by norm_num, fun _ => le_refl _, ?_⟩
  intro h
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  exact (by norm_num : (1:ℝ) ≠ 0) (tendsto_nhds_unique h1 h)

/-- Drop `hle` (a ≤ c).  Without it the conclusion fails: a = const 1, c = const 0 (c→0),
    0 ≤ a, but a ↛ 0. So `hle` is load-bearing. -/
theorem nearmiss_FALSE_without_hle :
    ∃ (a c : ℕ → ℝ), (∀ i, 0 ≤ a i) ∧ Tendsto c atTop (𝓝 0) ∧
      ¬ Tendsto a atTop (𝓝 0) := by
  refine ⟨fun _ => 1, fun _ => 0, fun _ => by norm_num, tendsto_const_nhds, ?_⟩
  intro h
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  exact (by norm_num : (1:ℝ) ≠ 0) (tendsto_nhds_unique h1 h)

/-- Drop `hnn` (0 ≤ a). Without it the conclusion can fail: a = const (-1), c = const 0 (c→0),
    a ≤ c, but a ↛ 0. So `hnn` is load-bearing (one-sided squeeze needs the lower bound). -/
theorem nearmiss_FALSE_without_hnn :
    ∃ (a c : ℕ → ℝ), (∀ i, a i ≤ c i) ∧ Tendsto c atTop (𝓝 0) ∧
      ¬ Tendsto a atTop (𝓝 0) := by
  refine ⟨fun _ => -1, fun _ => 0, fun _ => by norm_num, tendsto_const_nhds, ?_⟩
  intro h
  have h1 : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)) := tendsto_const_nhds
  exact (by norm_num : (-1:ℝ) ≠ 0) (tendsto_nhds_unique h1 h)

/-! ====================================================================================
    (B) THE FAITHFULNESS PROBE — the real attack.

    Claim under test (spec's near-miss intent): "forcing per-round budget o(1) (a_i ≤ c_i,
    c_i → 0) certifies the EXISTENCE vulnerability is removed — the cause is single-round
    concentration." We show this is OVER-CLAIMED: the EXISTENCE family `a B k` (the vulnerable
    one, running sup = B) ITSELF satisfies the near-miss hypotheses AND the near-miss conclusion.
    So the near-miss does NOT exclude the vulnerable family; it governs a different quantity.
    ==================================================================================== -/

/-- The vulnerable existence family satisfies the near-miss HYPOTHESES with c = a:
    `0 ≤ a B k i`, `a B k i ≤ c i`, and `c → 0` (take c = a B k, whose tail is zeros).
    AND it satisfies the near-miss CONCLUSION `a B k → 0`.
    Yet (existence direction) its running sup = B ↛ 0.  Hence the near-miss is SATISFIED
    BY THE VULNERABLE FAMILY — it does not certify removal of the running-sup vulnerability. -/
theorem existence_family_SATISFIES_nearmiss {B : ℝ} (hB : 0 ≤ B) (k : ℕ) :
    -- near-miss hypotheses, with c := a B k:
    (∀ i, 0 ≤ a B k i) ∧ (∀ i, a B k i ≤ a B k i) ∧ Tendsto (a B k) atTop (𝓝 0)
    -- ... and the near-miss conclusion (per-round swing → 0) holds for this very family:
    ∧ Tendsto (a B k) atTop (𝓝 0) := by
  have htail : (a B k) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
    filter_upwards [eventually_gt_atTop k] with i hi
    have hne : i ≠ k := by omega
    simp [a, hne]
  have hto0 : Tendsto (a B k) atTop (𝓝 0) := Tendsto.congr' htail.symm tendsto_const_nhds
  refine ⟨fun i => ?_, fun i => le_refl _, hto0, hto0⟩
  unfold a; split <;> simp [hB]

/-- Pinpoint the GAP: the vulnerable family satisfies the near-miss conclusion (per-round → 0)
    while its running sup ↛ 0.  Concretely for k=0: per-round swing → 0 BUT running sup = B ↛ 0.
    (This re-derives the executor's own `running_sup_near_miss_false`, independently, to confirm
    the near-miss conclusion and the running-sup vulnerability COEXIST — so (ii) ⇏ (i)-is-cured.) -/
theorem gap_perround_to_0_but_runningsup_not {B : ℝ} (hB : 0 < B) :
    Tendsto (a B 0) atTop (𝓝 0) ∧
    ¬ Tendsto (fun T : ℕ => (range (T + 1)).sup'
        ⟨0, Finset.mem_range.mpr (by omega)⟩ (a B 0)) atTop (𝓝 0) := by
  constructor
  · have htail : (a B 0) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with i hi
      have hne : i ≠ 0 := by omega
      simp [a, hne]
    exact Tendsto.congr' htail.symm tendsto_const_nhds
  · -- running sup is constant B (every window T+1 contains round 0)
    have hconst : (fun T : ℕ => (range (T + 1)).sup'
          ⟨0, Finset.mem_range.mpr (by omega)⟩ (a B 0)) = (fun _ : ℕ => B) := by
      funext T
      apply le_antisymm
      · exact Finset.sup'_le _ _ (fun i _ => a_le_B hB.le 0 i)
      · have hk : a B 0 0 ≤ (range (T+1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (a B 0) :=
          Finset.le_sup' (a B 0) (Finset.mem_range.mpr (by omega))
        rwa [a_spike B 0] at hk
    rw [hconst]
    intro hcontra
    exact (ne_of_gt hB) (tendsto_nhds_unique tendsto_const_nhds hcontra)

end AttackAHS

#print axioms AttackAHS.running_sup_eq_B_FALSE_without_hB
#print axioms AttackAHS.nearmiss_FALSE_without_hc
#print axioms AttackAHS.nearmiss_FALSE_without_hle
#print axioms AttackAHS.nearmiss_FALSE_without_hnn
#print axioms AttackAHS.existence_family_SATISFIES_nearmiss
#print axioms AttackAHS.gap_perround_to_0_but_runningsup_not
