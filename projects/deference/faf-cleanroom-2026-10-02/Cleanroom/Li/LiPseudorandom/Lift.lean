import Cleanroom.Li.LiPseudorandom.Fixed
import Cleanroom.Li.LiPseudorandom.Deferral

/-!
# `li-pseudorandom` — lifted rules and the disjoint union of rule families (T9's machinery)

The mandate's T9 asks for `diag` over the **disjoint union of the rule families**: several
families of members share the days, and each family must be pseudorandom relative to the LIA over
the process deciding all of them — against weightings that may read the *other* families' decided
atoms. This module supplies the two ingredients, both plain instances of T1 (`diag_pseudorandom`
quantifies over arbitrary strictly causal rules and never sees a feature progression):

* **A schedule** (`Schedule`): a strictly increasing placement `ι` of a subfamily's members among
  the days, with an explicit left inverse `π` (no `Classical.choose`). Instances: `evenSched`
  (`2m`), `oddSched` (`2m + 1`), `pairSched r` (`Nat.pair r m`, countably many families at once).
* **The lifted rule** (`lift S B W : CausalRule`): on a day `j = ι m` of the schedule, the clamped
  denotation of `W m` on the market built from the truth prefix of days `< j`; `0` on other days.
  Strictly causal by construction, exactly as `builderRule`. Under `CausalBuilder`, its realized
  weight on day `ι m` is `clamp ((W m).denote (B x))` (`lift_w_ι_eq`).
* **The subfamily theorem** (`subfamily_of_lift`, `subfamily_pseudorandom_of_lift`): for any
  diagonal `diag R q` whose rule family contains `lift S B W` and whose target is `p` on the
  schedule's days, the `W`-weighted truth frequency of the subfamily `m ↦ truthR (diag R q) (ι m)`
  on `B (diag R q)` tends to `p`. T1 at the lift's index, the prefix sums reindexed along the
  schedule (`sum_lift`), and the limit read along the subsequence `ι n`.
* **The disjoint union** (`unionRules fam`): countably many rule families `fam i` interleaved by
  `Nat.pair`, with `unionRules_pair`.
* `variedPseudorandom_of_builderRule_mem`: the combined-stream statement
  (`variedPseudorandom_of_causal`) for any rule family that *contains* the builder rules of a
  covering enumeration — so enlarging the family by lifts loses nothing.

Round-2 fidelity audit, B1: the package had left the two-family cross-reading form OPEN with a
diagnosis that blamed a missing FAF closure property; the auditor's probe (`EvenLift.lean`) showed
the obstacle was the package's own rule family. This module is that probe generalized from the even
lift to an arbitrary schedule; `Joint.lean` builds the two-family and countable-family streams on
it.
-/

namespace Cleanroom.Li.LiPseudorandom

open LogicalInduction Filter Topology
open scoped BigOperators

/-! ## Prefix sums of nonnegative sequences are monotone (moved here from `Witnesses.lean`) -/

/-- Prefix sums of a nonnegative sequence are monotone in the day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prefixSum_mono_of_nonneg {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) {n m : ℕ} (h : n ≤ m) :
    prefixSum w n ≤ prefixSum w m := by
  unfold prefixSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ h))
  intro j _ _
  exact hw j

/-! ## Schedules -/

/-- **A schedule**: a strictly increasing placement `ι` of a subfamily's members among the days,
with an explicit left inverse `π` (`π (ι m) = m`). Day `j` carries a member iff `ι (π j) = j`.
Source: mandate T9 ("diag over the disjoint union of the rule families")
Kind: D
Fidelity: exact -/
structure Schedule where
  /-- The day of member `m`. -/
  ι : ℕ → ℕ
  /-- The member on day `j` (junk off the schedule; `ι (π j) = j` tests membership). -/
  π : ℕ → ℕ
  /-- `π` inverts `ι`. -/
  π_ι : ∀ m, π (ι m) = m
  /-- Members occupy later and later days. -/
  strictMono : StrictMono ι

/-- Day `j` is on the schedule iff it is `ι m` for some `m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Schedule.onDay_iff (S : Schedule) (j : ℕ) : S.ι (S.π j) = j ↔ ∃ m, S.ι m = j := by
  constructor
  · intro h
    exact ⟨S.π j, h⟩
  · rintro ⟨m, rfl⟩
    rw [S.π_ι]

/-- Every member's day is at least its index (`ι` is strictly increasing on `ℕ`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Schedule.le_ι (S : Schedule) (m : ℕ) : m ≤ S.ι m :=
  S.strictMono.id_le m

/-- The even days: member `m` on day `2m`.
Source: mandate T9 (two-family case)
Kind: D
Fidelity: exact -/
def evenSched : Schedule where
  ι m := 2 * m
  π j := j / 2
  π_ι m := by omega
  strictMono := fun a b h => by show 2 * a < 2 * b; omega

/-- The odd days: member `m` on day `2m + 1`.
Source: mandate T9 (two-family case)
Kind: D
Fidelity: exact -/
def oddSched : Schedule where
  ι m := 2 * m + 1
  π j := j / 2
  π_ι m := by omega
  strictMono := fun a b h => by show 2 * a + 1 < 2 * b + 1; omega

/-- Family `r` of countably many: member `m` on day `Nat.pair r m`.
Source: mandate T9 ("countably many families at once")
Kind: D
Fidelity: exact -/
def pairSched (r : ℕ) : Schedule where
  ι m := Nat.pair r m
  π j := (Nat.unpair j).2
  π_ι m := by simp [Nat.unpair_pair]
  strictMono := fun _ _ h => Nat.pair_lt_pair_right r h

/-! ## The lifted rule -/

/-- **The lifted rule.** On a day `j = ι m` of the schedule `S`, the clamped denotation of `W m`
on the market the builder makes from the truth prefix of days `< j`; `0` on other days. Strictly
causal by construction (it reads `restrict x j`), exactly like `builderRule`; no hypothesis on `B`
is needed to define it.
Source: mandate T9; round-2 fidelity audit B1 (`EvenLift.lean`, generalized)
Kind: D
Fidelity: variant: the feature is evaluated on `B (restrict x j)`; the realized weights agree
with `clamp ((W m).denote (B x))` under `CausalBuilder B g` with `j < g j` (`lift_w_ι_eq`) -/
noncomputable def lift (S : Schedule) (B : (ℕ → Bool) → History) (W : ℕ → EF) : CausalRule where
  w x j := if S.ι (S.π j) = j then clamp ((W (S.π j)).denote (B (restrict x j))) else 0
  nonneg _ _ := by
    split_ifs
    · exact clamp_nonneg _
    · exact le_rfl
  le_one _ _ := by
    split_ifs
    · exact clamp_le_one _
    · exact zero_le_one
  causal x y n h := by
    have : restrict x n = restrict y n := by
      funext j
      unfold restrict
      split_ifs with hj
      · exact h j hj
      · rfl
    simp only [this]

/-- Off the schedule the lifted rule puts weight `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lift_w_off (S : Schedule) (B : (ℕ → Bool) → History) (W : ℕ → EF) (x : ℕ → Bool)
    {j : ℕ} (hj : ¬ S.ι (S.π j) = j) : (lift S B W).w x j = 0 := by
  show (if S.ι (S.π j) = j then clamp ((W (S.π j)).denote (B (restrict x j))) else 0) = 0
  rw [if_neg hj]

/-- On the day of member `m` the lifted rule reads `W m` on the prefix-built market.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma lift_w_ι (S : Schedule) (B : (ℕ → Bool) → History) (W : ℕ → EF) (x : ℕ → Bool)
    (m : ℕ) : (lift S B W).w x (S.ι m) = clamp ((W m).denote (B (restrict x (S.ι m)))) := by
  show (if S.ι (S.π (S.ι m)) = S.ι m then
    clamp ((W (S.π (S.ι m))).denote (B (restrict x (S.ι m)))) else 0) = _
  rw [S.π_ι, if_pos rfl]

/-- Under causality, the realized weight of the lifted rule on day `ι m` is the clamped
denotation of `W m` on `B x` itself (rank `≤ m ≤ ι m`, and `B (restrict x (ι m))` agrees with
`B x` at days `≤ ι m`) — the same argument as `builderRule_w_eq`.
Source: mandate T9 (proof)
Kind: L
Fidelity: exact
Hyps: (a) -/
lemma lift_w_ι_eq {B : (ℕ → Bool) → History} {g : ℕ → ℕ} (hB : CausalBuilder B g)
    (hg : ∀ j, j < g j) {W : ℕ → EF} (hW : PGenerableWeighting W) (S : Schedule) (x : ℕ → Bool)
    (m : ℕ) : (lift S B W).w x (S.ι m) = clamp ((W m).denote (B x)) := by
  rw [lift_w_ι]
  congr 1
  apply PGenerableWeighting.denote_congr hW m
  intro m' hm' φ
  apply hB (restrict x (S.ι m)) x (S.ι m) _ m' (hm'.trans (S.le_ι m)) φ
  intro j hj
  unfold restrict
  rw [if_pos (by have := hg j; omega)]

/-- The realized weights of the lifted rule on `x`, as a function of the day, when the
denotations on `B x` lie in `[0,1]`.
Source: mandate T9 (proof)
Kind: L
Fidelity: exact
Hyps: (a) -/
lemma lift_w_eq_fun {B : (ℕ → Bool) → History} {g : ℕ → ℕ} (hB : CausalBuilder B g)
    (hg : ∀ j, j < g j) {W : ℕ → EF} (hW : PGenerableWeighting W) (S : Schedule) (x : ℕ → Bool)
    (hrange : ∀ n, 0 ≤ (W n).denote (B x) ∧ (W n).denote (B x) ≤ 1) :
    (lift S B W).w x = fun j => if S.ι (S.π j) = j then (W (S.π j)).denote (B x) else 0 := by
  funext j
  by_cases hj : S.ι (S.π j) = j
  · obtain ⟨m, rfl⟩ := (S.onDay_iff j).1 hj
    rw [S.π_ι, if_pos rfl, lift_w_ι_eq hB hg hW, clamp_of_mem_Icc (hrange m)]
  · rw [lift_w_off S B W x hj, if_neg hj]

/-- **Reindexing along a schedule**: the sum over days `≤ ι n` of a term supported on the
schedule is the sum over members `≤ n`.
Source: mandate T9 (proof)
Kind: L
Fidelity: n/a -/
lemma sum_lift (S : Schedule) (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (S.ι n + 1), (if S.ι (S.π j) = j then f (S.π j) else 0) =
      ∑ m ∈ Finset.range (n + 1), f m := by
  rw [← Finset.sum_filter]
  have himg : (Finset.range (S.ι n + 1)).filter (fun j => S.ι (S.π j) = j) =
      (Finset.range (n + 1)).image S.ι := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hjn, hj⟩
      refine ⟨S.π j, ?_, hj⟩
      rw [← S.strictMono.le_iff_le, hj]
      exact hjn
    · rintro ⟨m, hm, rfl⟩
      exact ⟨S.strictMono.monotone hm, by rw [S.π_ι]⟩
  rw [himg, Finset.sum_image (fun _ _ _ _ h => S.strictMono.injective h)]
  apply Finset.sum_congr rfl
  intro m _
  rw [S.π_ι]

/-! ## The subfamily theorem -/

/-- **A subfamily is defeated by any diagonal whose rule family contains its lift (paper form).**
For a causal builder `B` (delay `g`, `∀ j, j < g j`), a schedule `S`, a target `q ∈ [0,1]` equal
to `p` on the schedule's days, and a rule family `R` with `R k = lift S B W` for a P-generable `W`
divergent on `B (diag R q)`: the `W`-weighted truth frequency of the subfamily
`m ↦ truthR (diag R q) (ι m)` tends to `p`. T1 at index `k`, the prefix sums reindexed along the
schedule, and the limit read along the subsequence `ι n`. `W` is evaluated on the market over the
*whole* stream, so it may read every other subfamily's decided atoms.
Source: mandate T9 (cross-reading clause); round-2 fidelity audit B1
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem subfamily_of_lift {B : (ℕ → Bool) → History} {g : ℕ → ℕ} (hB : CausalBuilder B g)
    (hg : ∀ j, j < g j) (S : Schedule) (R : ℕ → CausalRule) (q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1) (p : ℝ) (hqS : ∀ m, q (S.ι m) = p)
    {W : ℕ → EF} (hW : PGenerableWeighting W) {k : ℕ} (hk : R k = lift S B W)
    (hWdiv : DivergentWeighting W (B (diag R q))) :
    weightedAverage (fun m => (W m).denote (B (diag R q)))
      (fun m => truthR (diag R q) (S.ι m)) ≈ₙ (fun _ => p) := by
  have hw : (R k).w (diag R q) =
      fun j => if S.ι (S.π j) = j then (W (S.π j)).denote (B (diag R q)) else 0 := by
    rw [hk]
    exact lift_w_eq_fun hB hg hW S _ hWdiv.1
  have hS : ∀ n, prefixSum ((R k).w (diag R q)) (S.ι n) =
      prefixSum (fun m => (W m).denote (B (diag R q))) n := by
    intro n
    rw [hw]
    unfold prefixSum
    exact sum_lift S (fun m => (W m).denote (B (diag R q))) n
  have hD : ∀ n, prefixSum (fun j => (R k).w (diag R q) j * (truthR (diag R q) j - q j))
      (S.ι n) =
      prefixSum (fun m => (W m).denote (B (diag R q)) * (truthR (diag R q) (S.ι m) - p)) n := by
    intro n
    rw [hw]
    unfold prefixSum
    rw [← sum_lift S
      (fun m => (W m).denote (B (diag R q)) * (truthR (diag R q) (S.ι m) - p)) n]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    by_cases hj : S.ι (S.π j) = j
    · rw [if_pos hj, if_pos hj]
      have hqj : q j = p := by
        rw [← hj]
        exact hqS (S.π j)
      rw [hqj, hj]
    · rw [if_neg hj, if_neg hj, zero_mul]
  have hdiv : Tendsto (prefixSum ((R k).w (diag R q))) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    obtain ⟨n₀, hn₀⟩ := tendsto_atTop_atTop.1 hWdiv.2 M
    refine ⟨S.ι n₀, fun N hN => ?_⟩
    calc M ≤ prefixSum (fun m => (W m).denote (B (diag R q))) n₀ := hn₀ n₀ le_rfl
      _ = prefixSum ((R k).w (diag R q)) (S.ι n₀) := (hS n₀).symm
      _ ≤ prefixSum ((R k).w (diag R q)) N :=
          prefixSum_mono_of_nonneg ((R k).nonneg (diag R q)) hN
  have hT1 := diag_pseudorandom R q hq k hdiv
  have h0 : Tendsto (fun N => weightedAverage ((R k).w (diag R q))
      (fun j => truthR (diag R q) j - q j) N) atTop (𝓝 0) := by
    unfold AsympEq at hT1
    simpa only [sub_zero] using hT1
  have hsub : Tendsto (fun n => weightedAverage ((R k).w (diag R q))
      (fun j => truthR (diag R q) j - q j) (S.ι n)) atTop (𝓝 0) :=
    h0.comp S.strictMono.tendsto_atTop
  have hSpos : ∀ᶠ n in atTop, 0 < prefixSum (fun m => (W m).denote (B (diag R q))) n :=
    hWdiv.2.eventually (eventually_gt_atTop 0)
  unfold AsympEq
  refine hsub.congr' ?_
  filter_upwards [hSpos] with n hn
  have hpos' : prefixSum ((R k).w (diag R q)) (S.ι n) ≠ 0 := by
    rw [hS n]
    exact hn.ne'
  rw [weightedAverage_eq_div hpos', hD n, hS n,
    ← weightedAverage_sub_const _ _ _ hn.ne', weightedAverage_eq_div hn.ne']

/-- **The subfamily inhabits FAF's `PseudorandomFrequency`, for every `f`**, relative to
`B (diag R q)`, whenever the rule family contains the lift of every P-generable weighting.
Source: mandate T9 (cross-reading clause); FAF `PseudorandomFrequency`
Kind: C
Fidelity: stronger: all `f`
Hyps: (a) -/
theorem subfamily_pseudorandom_of_lift {B : (ℕ → Bool) → History} {g : ℕ → ℕ}
    (hB : CausalBuilder B g) (hg : ∀ j, j < g j) (S : Schedule) (R : ℕ → CausalRule)
    (hR : ∀ W, PGenerableWeighting W → ∃ k, R k = lift S B W) (q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1) (p : ℝ) (hqS : ∀ m, q (S.ι m) = p) :
    ∀ f : DeferralFunction,
      PseudorandomFrequency (fun m => truthR (diag R q) (S.ι m)) p f (B (diag R q)) := by
  intro _ W hW hWdiv _
  obtain ⟨k, hk⟩ := hR W hW
  exact subfamily_of_lift hB hg S R q hq p hqS hW hk hWdiv

/-! ## The disjoint union of rule families -/

/-- **The disjoint union of countably many rule families**, interleaved by `Nat.pair`: rule
`Nat.pair i j` is the `j`-th rule of family `i`.
Source: mandate T9 ("diag over the disjoint union of the rule families")
Kind: D
Fidelity: exact -/
def unionRules (fam : ℕ → ℕ → CausalRule) : ℕ → CausalRule :=
  fun k => fam (Nat.unpair k).1 (Nat.unpair k).2

/-- The `j`-th rule of family `i` sits at index `Nat.pair i j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma unionRules_pair (fam : ℕ → ℕ → CausalRule) (i j : ℕ) :
    unionRules fam (Nat.pair i j) = fam i j := by
  simp [unionRules, Nat.unpair_pair]

/-- **The combined stream over any rule family containing the builder rules is varied
pseudorandom** relative to `B (diag R q)`, every `f`: `variedPseudorandom_of_causal` with the
enumeration's rule family replaced by any family that contains the builder rule of every
P-generable weighting — enlarging the family by lifts loses nothing.
Source: mandate T9 (varied form); FAF `VariedPseudorandom`
Kind: C
Fidelity: stronger: all `f`; no generability of `q` needed
Hyps: (a) -/
theorem variedPseudorandom_of_builderRule_mem (B : (ℕ → Bool) → History) (g : ℕ → ℕ)
    (hB : CausalBuilder B g) (hg : ∀ j, j < g j) (R : ℕ → CausalRule)
    (hR : ∀ W, PGenerableWeighting W → ∃ k, R k = builderRule B W) (q : ℕ → ℚ)
    (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1) :
    ∀ f : DeferralFunction, VariedPseudorandom (truthR (diag R (fun n => (q n : ℝ))))
      q f (B (diag R (fun n => (q n : ℝ)))) := by
  intro f
  have hp : ∀ n, 0 ≤ (q n : ℝ) ∧ (q n : ℝ) ≤ 1 := fun n => by
    exact_mod_cast hq n
  have key : ∀ W : ℕ → EF, PGenerableWeighting W →
      DivergentWeighting W (B (diag R (fun n => (q n : ℝ)))) →
      weightedAverage (fun i => (W i).denote (B (diag R (fun n => (q n : ℝ)))))
        (fun n => truthR (diag R (fun n => (q n : ℝ))) n - (q n : ℝ)) ≈ₙ
        (fun _ => 0) := by
    intro W hWgen hWdiv
    obtain ⟨k, hk⟩ := hR W hWgen
    have hw : (R k).w (diag R (fun n => (q n : ℝ))) =
        fun n => (W n).denote (B (diag R (fun n => (q n : ℝ)))) := by
      rw [hk]
      exact builderRule_w_eq_denote hB hg hWgen _ hWdiv.1
    have h := diag_pseudorandom R (fun n => (q n : ℝ)) hp k (by rw [hw]; exact hWdiv.2)
    rw [hw] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro W hWgen hWdiv _
    exact (asympEq_iff_asympLE_asympGE.1 (key W hWgen hWdiv)).2
  · intro W hWgen hWdiv _
    exact (asympEq_iff_asympLE_asympGE.1 (key W hWgen hWdiv)).1

/-- **The combined stream over any rule family containing the builder rules is pseudorandom at
a constant target (paper form)**: `diagBuilder_pseudorandom_of_causal` for an enlarged family.
Source: mandate T9; `def:pseudorandom`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem pseudorandom_all_of_builderRule_mem (B : (ℕ → Bool) → History) (g : ℕ → ℕ)
    (hB : CausalBuilder B g) (hg : ∀ j, j < g j) (R : ℕ → CausalRule)
    (hR : ∀ W, PGenerableWeighting W → ∃ k, R k = builderRule B W) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) :
    ∀ W : ℕ → EF, PGenerableWeighting W → DivergentWeighting W (B (diag R (fun _ => p))) →
      weightedAverage (fun i => (W i).denote (B (diag R (fun _ => p))))
        (truthR (diag R (fun _ => p))) ≈ₙ (fun _ => p) := by
  intro W hWgen hWdiv
  obtain ⟨k, hk⟩ := hR W hWgen
  have hw : (R k).w (diag R (fun _ => p)) =
      fun n => (W n).denote (B (diag R (fun _ => p))) := by
    rw [hk]
    exact builderRule_w_eq_denote hB hg hWgen _ hWdiv.1
  have h := diag_pseudorandom_const R p hp k (by rw [hw]; exact hWdiv.2)
  rw [hw] at h
  exact h

end Cleanroom.Li.LiPseudorandom
