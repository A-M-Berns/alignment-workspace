import Cleanroom.Fa.FaAdaptiveJoint.Witnesses

/-!
# `fa-adaptive-joint` · audit r2 (adversarial) · probe: T4's witness inhabits the *full* package

Evidence for `fa-adaptive-joint-audit-r2-adversarial.md`. **Not imported by the library.**

The OPEN `adaptiveBridge` quantifies (inside `AdaptiveBridgeHolds H f X`) over weightings `G`
with `PGenerableWeighting G`, `OnePosition f (G·denote H)` **and** `DivergentWeighting G H`. The
package's witness `onePosition_positive_everywhere` (`w ≡ ¾`, `θ = 1`, `f n = 2n + 2`) states
one-position, positivity on every day and "supported on no schedule" — but not divergence, and a
one-position weighting positive everywhere can be summable (`u n = 2^{−n−1}`), in which case it is
outside the scope of *both* `AdaptiveBridgeHolds` and `hSideBridge` and shows nothing about one
generalizing the other. This probe closes the gap: the same sequence is **not summable** (if it
were, its open mass would tend to `0` by the tail bound of T2's proof and the firing value to `½`),
so `adaptFire (const ¾) (linearSchedule 0) 1` is a `PGenerableWeighting` that is one-position,
divergent on **every** market, and supported on no schedule — a full-package inhabitant of the
OPEN statement that `hSideBridge` does not cover.
-/

namespace Cleanroom.Fa.FaAdaptiveJoint.AuditR2

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Found.LiQuoteLane Filter Topology

/-- The witness lookahead `f n = 2n + 2`. -/
def f34 : ℕ → ℕ := fun n => 2 * n + 2

/-- The witness sequence of `onePosition_positive_everywhere`. -/
noncomputable def u34 : ℕ → ℝ := fireSeq f34 1 (fun _ => (3 / 4 : ℝ))

theorem u34_rec : FireRec f34 1 (fun _ => (3 / 4 : ℝ)) u34 := fireSeq_fireRec _ _ _

theorem ramp34 : ctsInd (1 / 2) (3 / 4 : ℝ) (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 := by
  unfold ctsInd
  norm_num

theorem u34_val (n : ℕ) : u34 n = (1 - openMass f34 u34 n) / 2 := by
  rw [u34_rec n]
  simp only [ramp34]
  ring

theorem u34_nonneg (n : ℕ) : 0 ≤ u34 n := (u34_rec.nonneg_openMass_le_one n).1

/-- Beyond day `2N`, every piece open was opened on a day `≥ N`, so the open mass is bounded by the
tail sum from `N` (the bound inside T2's proof, specialised to `f34`). -/
theorem openMass_le_tail (hs : Summable u34) (N n : ℕ) (hn : 2 * N ≤ n) :
    openMass f34 u34 n ≤ ∑' k, u34 (k + N) := by
  have hNn : N ≤ n := by omega
  have hle : openMass f34 u34 n ≤ ∑ m ∈ Finset.Ico N n, u34 m := by
    rw [openMass]
    calc ∑ m ∈ Finset.range n, (if n < f34 m then u34 m else 0)
        = ∑ m ∈ Finset.Ico N n, (if n < f34 m then u34 m else 0) := by
          rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNn]
          have h0 : ∑ m ∈ Finset.Ico 0 N, (if n < f34 m then u34 m else 0) = 0 := by
            refine Finset.sum_eq_zero (fun m hm => ?_)
            have hm' : m < N := (Finset.mem_Ico.1 hm).2
            rw [if_neg (by unfold f34; omega)]
          rw [h0, zero_add]
      _ ≤ ∑ m ∈ Finset.Ico N n, u34 m := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          by_cases hc : n < f34 m
          · rw [if_pos hc]
          · rw [if_neg hc]; exact u34_nonneg m
  have hle2 : ∑ m ∈ Finset.Ico N n, u34 m ≤ ∑' k, u34 (k + N) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hc : ∑ k ∈ Finset.range (n - N), u34 (N + k) = ∑ k ∈ Finset.range (n - N), u34 (k + N) :=
      Finset.sum_congr rfl (fun k _ => by rw [add_comm])
    rw [hc]
    exact ((summable_nat_add_iff N).2 hs).sum_le_tsum _ (fun k _ => u34_nonneg _)
  exact hle.trans hle2

/-- **The witness is not summable.** -/
theorem u34_not_summable : ¬ Summable u34 := by
  intro hs
  have htail : Tendsto (fun N => ∑' k, u34 (k + N)) atTop (𝓝 0) := tendsto_sum_nat_add u34
  obtain ⟨N, hN⟩ : ∃ N, ∑' k, u34 (k + N) < 1 / 2 :=
    (htail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  have hu0 : ∀ᶠ n in atTop, u34 n < 1 / 4 :=
    hs.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨n, hn1, hn2⟩ := (hu0.and (eventually_ge_atTop (2 * N))).exists
  have h1 := openMass_le_tail hs N n hn2
  have h2 := u34_val n
  linarith

/-- Hence its prefix sums diverge. -/
theorem u34_prefixSum_tendsto : Tendsto (prefixSum u34) atTop atTop := by
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg u34_nonneg).1 u34_not_summable
  exact h.comp (tendsto_add_atTop_nat 1)

theorem denote_const34 (V : History) : (EF.const (3 / 4 : ℚ)).denote V = (3 / 4 : ℝ) := by
  rw [EF.denote, EF.denoteWith_const]
  norm_num

/-- The feature `adaptFire (const ¾) (linearSchedule 0) 1` denotes `u34` on every market. -/
theorem adaptFire34_denote (V : History) :
    (fun n => (adaptFire (fun _ => EF.const (3 / 4)) (linearSchedule 0) 1 n).denote V) = u34 := by
  funext n
  rw [adaptFire_denote_fireSeq (pgenerableWeighting_const _) _ one_pos]
  have hfun : (linearSchedule 0).f = f34 := funext linearSchedule_zero_apply
  rw [hfun]
  unfold u34
  congr 1
  funext m
  exact denote_const34 V

/-- **A full-package inhabitant of the OPEN `AdaptiveBridgeHolds`'s quantifier, on every market,
supported on no schedule**: generable (T1), one-position, divergent. -/
theorem adaptFire34_full_package (V : History) :
    PGenerableWeighting (adaptFire (fun _ => EF.const (3 / 4)) (linearSchedule 0) 1) ∧
      OnePosition (linearSchedule 0)
        (fun n => (adaptFire (fun _ => EF.const (3 / 4)) (linearSchedule 0) 1 n).denote V) ∧
      DivergentWeighting (adaptFire (fun _ => EF.const (3 / 4)) (linearSchedule 0) 1) V ∧
      ∀ d : DeferralFunction,
        ¬ (∀ n, (adaptFire (fun _ => EF.const (3 / 4)) (linearSchedule 0) 1 n).denote V ≠ 0 →
          ∃ k, d.f k = n) := by
  have hden := adaptFire34_denote V
  have hfun : (linearSchedule 0).f = f34 := funext linearSchedule_zero_apply
  have hpos : ∀ n, 0 < u34 n := by
    intro n
    rw [u34_val n]
    have hopen : openMass f34 u34 n < 1 := by
      induction n with
      | zero => simp [openMass]
      | succ n ih =>
          have h1 := openMass_succ f34 u34 n (by unfold f34; omega)
          have h2 : 0 ≤ ∑ m ∈ Finset.range (n + 1), (if f34 m = n + 1 then u34 m else 0) :=
            Finset.sum_nonneg (fun m _ => by split_ifs <;> [exact u34_nonneg m; exact le_rfl])
          have h3 := u34_val n
          linarith
    linarith
  refine ⟨adaptFire_pgenerable (pgenerableWeighting_const _) _ _, ?_, ?_, fun d hd => ?_⟩
  · rw [hden]
    show ∀ n, 0 ≤ u34 n ∧ openMass (linearSchedule 0).f u34 n ≤ 1
    rw [hfun]
    exact u34_rec.nonneg_openMass_le_one
  · refine ⟨fun n => ?_, ?_⟩
    · rw [congrFun hden n]
      exact (u34_rec.mem_Icc n)
    · rw [hden]
      exact u34_prefixSum_tendsto
  · obtain ⟨k, hk⟩ := hd 0 (by rw [congrFun hden 0]; exact (hpos 0).ne')
    have := d.lt k
    omega

end Cleanroom.Fa.FaAdaptiveJoint.AuditR2
