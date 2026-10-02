import Cleanroom.Fa.FaAdaptiveJoint.Expressibility
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# `fa-adaptive-joint` · Counting: the real-sequence facts of the softened machine (T2)

[[fa-adaptive-joint-mandate]] T2, over real sequences satisfying the recursion law `FireRec`
(`Defs.lean`): the one-position structure (`FireRec.onePosition`: the open mass never exceeds `1`
— the content of the additive softening, and what the product softening lacks, F2), the firing
value on a flat day with `w_n ≥ θ` (`FireRec.eq_one_of_flat`), the support clause
(`FireRec.pos_imp`: firing days are near-violation days, `w_n > θ/2`), the additive update
(`openMass_succ`), and **the counting argument** `FireRec.eventually_lt_of_summable`:
`Summable fire → ∀ᶠ n, w n < θ` — v3's "finitely many windows plus finitely many firing days",
proved as `open n → 0` (the open mass is bounded by the tail sum beyond `min {m : n < f m}`), so
eventually `open n < ½` and a day with `w_n ≥ θ` would fire `> ½`, contradicting `fire n → 0`.
Its corollary `tendsto_zero_of_summable_fireSeq` (`(∀ θ > 0, Summable (fire θ)) → w → 0`) is what
`v3Theorem2` ends with. The `∀ᶠ` form is the one `tendsto_viol_iff_dominates` consumes
(mandate trap: no `Set.Finite` of an undecidable set without it).
-/

namespace Cleanroom.Fa.FaAdaptiveJoint

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Filter Topology

/-! ## A. The one-position invariant -/

/-- **The additive softening keeps the open position in `[0, 1]`**: every solution of the recursion
law is nonnegative with open mass `≤ 1` on every day (strong induction:
`open (n+1) ≤ open n + fire n = open n + (1 − open n) · r n ≤ 1`).
Source: [[fa-adaptive-joint-mandate]] § T1 ("the *additive* soft update keeps the total open position in `[0,1]`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem FireRec.nonneg_openMass_le_one {f : ℕ → ℕ} {θ : ℚ} {w u : ℕ → ℝ} (h : FireRec f θ w u) :
    ∀ n, 0 ≤ u n ∧ openMass f u n ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hopen : openMass f u n ≤ 1 := by
      rcases n with _ | n
      · simp [openMass]
      · have hun := ih n (Nat.lt_succ_self n)
        have hterm : (if n + 1 < f n then u n else 0) ≤ u n := by
          by_cases hc : n + 1 < f n
          · rw [if_pos hc]
          · rw [if_neg hc]; exact hun.1
        have hsum : ∑ m ∈ Finset.range n, (if n + 1 < f m then u m else 0) ≤
            ∑ m ∈ Finset.range n, (if n < f m then u m else 0) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          have hum := (ih m (lt_trans (Finset.mem_range.1 hm) (Nat.lt_succ_self n))).1
          by_cases h1 : n + 1 < f m
          · rw [if_pos h1, if_pos (by omega)]
          · rw [if_neg h1]
            by_cases h2 : n < f m
            · rw [if_pos h2]; exact hum
            · rw [if_neg h2]
        have hr := ctsInd_mem_Icc (θ / 2) (w n) ((θ / 2 : ℚ) : ℝ)
        have h0 : 0 ≤ 1 - openMass f u n := by linarith [hun.2]
        have hun1 : u n ≤ 1 - openMass f u n := by
          rw [h n]
          calc (1 - openMass f u n) * ctsInd (θ / 2) (w n) ((θ / 2 : ℚ) : ℝ)
              ≤ (1 - openMass f u n) * 1 := mul_le_mul_of_nonneg_left hr.2 h0
            _ = 1 - openMass f u n := mul_one _
        calc openMass f u (n + 1)
            = ∑ m ∈ Finset.range n, (if n + 1 < f m then u m else 0)
                + (if n + 1 < f n then u n else 0) := by rw [openMass, Finset.sum_range_succ]
          _ ≤ ∑ m ∈ Finset.range n, (if n < f m then u m else 0) + u n := add_le_add hsum hterm
          _ = openMass f u n + u n := by rw [openMass]
          _ ≤ 1 := by linarith
    refine ⟨?_, hopen⟩
    rw [h n]
    exact mul_nonneg (by linarith) (ctsInd_mem_Icc _ _ _).1

/-- A solution of the recursion law is a one-position weighting (mandate `adaptOpen_le_one`).
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem FireRec.onePosition {f : DeferralFunction} {θ : ℚ} {w u : ℕ → ℝ} (h : FireRec f.f θ w u) :
    OnePosition f u :=
  h.nonneg_openMass_le_one

/-- The open mass of a nonnegative weighting is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem openMass_nonneg (f : ℕ → ℕ) {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) (n : ℕ) :
    0 ≤ openMass f u n := by
  unfold openMass
  refine Finset.sum_nonneg (fun m _ => ?_)
  split_ifs
  · exact hu m
  · exact le_rfl

/-- A solution of the recursion law is `[0, 1]`-valued (mandate `adaptFire_mem_Icc`).
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem FireRec.mem_Icc {f : ℕ → ℕ} {w u : ℕ → ℝ} {θ : ℚ} (h : FireRec f θ w u) (n : ℕ) :
    u n ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := h.nonneg_openMass_le_one n
  refine ⟨h0, ?_⟩
  rw [h n]
  have hr := ctsInd_mem_Icc (θ / 2) (w n) ((θ / 2 : ℚ) : ℝ)
  have hom := openMass_nonneg f (fun m => (h.nonneg_openMass_le_one m).1) n
  have hsub : 0 ≤ 1 - openMass f u n := by linarith
  calc (1 - openMass f u n) * ctsInd (θ / 2) (w n) ((θ / 2 : ℚ) : ℝ)
      ≤ 1 * 1 := mul_le_mul (by linarith) hr.2 hr.1 zero_le_one
    _ = 1 := one_mul _

/-- **The additive update** (the mandate's `flat_{n+1} = flat_n − fire_n + (pieces closing at `n+1`)`,
in `open` form): `open (n+1) = open n + fire n − ∑_{m ≤ n, f m = n+1} fire m`, for any real
sequence and any lookahead with `n < f n`. The positive half of findings F2: this is the update
v3's "composing one bounded-size soft update per day" names, and it is the sum form.
Source: [[fa-adaptive-joint-mandate]] § T1 trap (α) ("the *additive* update … *is* the sum form")
Kind: L
Fidelity: exact
Hyps: (a) `hf` -/
theorem openMass_succ (f : ℕ → ℕ) (u : ℕ → ℝ) (n : ℕ) (hf : n < f n) :
    openMass f u (n + 1) =
      openMass f u n + u n - ∑ m ∈ Finset.range (n + 1), (if f m = n + 1 then u m else 0) := by
  have h1 : openMass f u n + u n = ∑ m ∈ Finset.range (n + 1), (if n < f m then u m else 0) := by
    rw [openMass, Finset.sum_range_succ, if_pos hf]
  rw [h1, openMass, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases h2 : n + 1 < f m
  · rw [if_pos h2, if_pos (by omega), if_neg (by omega), sub_zero]
  · rw [if_neg h2]
    by_cases h3 : f m = n + 1
    · rw [if_pos (by omega), if_pos h3, sub_self]
    · rw [if_neg (by omega), if_neg h3, sub_zero]

/-! ## B. Firing values -/

/-- **On a flat day with `w_n ≥ θ` the machine fires fully** (mandate `adaptFire_eq_one_of_flat`).
Source: [[fa-adaptive-joint-mandate]] § T1; [[fa-positive-results-corrected-v3]] §4 ("when flat on a day with `w_n ≥ θ`")
Kind: L
Fidelity: exact
Hyps: (a) `hθ` -/
theorem FireRec.eq_one_of_flat {f : ℕ → ℕ} {θ : ℚ} (hθ : 0 < θ) {w u : ℕ → ℝ}
    (h : FireRec f θ w u) {n : ℕ} (hflat : openMass f u n = 0) (hw : (θ : ℝ) ≤ w n) : u n = 1 := by
  rw [h n, hflat, sub_zero, one_mul]
  exact ctsInd_eq_one_of_le_sub _ _ _ (half_pos hθ) (by push_cast; linarith)

/-- The continuous threshold gate is positive only above its threshold.
Source: none: infrastructure (FAF `ctsInd_eq_zero_of_le`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ctsInd_pos_imp {δ : ℚ} (hδ : 0 < δ) {x y : ℝ} (h : 0 < ctsInd δ x y) : y < x := by
  by_contra hxy
  rw [ctsInd_eq_zero_of_le δ x y hδ (not_lt.1 hxy)] at h
  exact lt_irrefl _ h

/-- **Firing days are near-violation days**: `fire n > 0 → w n > θ/2` (T3's `A`-side support
clause).
Source: [[fa-adaptive-joint-mandate]] § T2 ("`fire n > 0 → w n > θ/2`")
Kind: L
Fidelity: exact
Hyps: (a) `hθ` -/
theorem FireRec.pos_imp {f : ℕ → ℕ} {θ : ℚ} (hθ : 0 < θ) {w u : ℕ → ℝ} (h : FireRec f θ w u)
    {n : ℕ} (hpos : 0 < u n) : ((θ / 2 : ℚ) : ℝ) < w n := by
  rw [h n] at hpos
  rcases (ctsInd_mem_Icc (θ / 2) (w n) ((θ / 2 : ℚ) : ℝ)).1.lt_or_eq with hr | hr
  · exact ctsInd_pos_imp (half_pos hθ) hr
  · rw [← hr, mul_zero] at hpos
    exact absurd hpos (lt_irrefl _)

/-! ## C. T2: the counting argument -/

/-- **T2 (headline, load-bearing). Summable firing forces `w_n < θ` eventually.** For any real
`w`, any lookahead `f : ℕ → ℕ`, rational `θ > 0`, and `u` the firing sequence
(`u n = (1 − ∑_{m<n, n<f m} u m) · ctsInd (θ/2) (w n) (θ/2)`): if `∑ u < ∞` then `∀ᶠ n, w n < θ`.
Proof: for `N` with tail `∑_{k ≥ N} u k < ½` and `n ≥ max_{m<N} f m`, every piece open on day
`n` was opened on a day `≥ N`, so `open n < ½`; eventually also `u n < ½`; on such a day `w n ≥ θ`
would give `u n = 1 − open n > ½`. v3's "finitely many windows plus finitely many firing days".
Scope: real sequences (no market). Lookahead: any `ℕ → ℕ` (`n < f n` not needed). Threshold:
per rational `θ`.
Source: [[fa-positive-results-corrected-v3]] §4 Theorem 2, last paragraph; root-fa-020 ("S for the counting argument"); [[fa-adaptive-joint-mandate]] § T2
Kind: P
Fidelity: exact (`∀ᶠ` form; the note's "finitely many days" is this)
Hyps: (a) `hθ`, `h` (the recursion law, discharged by `adaptFireR_fireRec`/`fireSeq_fireRec`), `hs`; no (b), no (c). -/
theorem FireRec.eventually_lt_of_summable {f : ℕ → ℕ} {θ : ℚ} (hθ : 0 < θ) {w u : ℕ → ℝ}
    (h : FireRec f θ w u) (hs : Summable u) : ∀ᶠ n in atTop, w n < θ := by
  have hnn : ∀ n, 0 ≤ u n := fun n => (h.nonneg_openMass_le_one n).1
  have htail : Tendsto (fun N => ∑' k, u (k + N)) atTop (𝓝 0) := tendsto_sum_nat_add u
  obtain ⟨N, hN⟩ : ∃ N, ∑' k, u (k + N) < 1 / 2 :=
    (htail.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  set M := (Finset.range N).sup f with hM
  have hopen : ∀ n, N ≤ n → M ≤ n → openMass f u n < 1 / 2 := by
    intro n hNn hMn
    have hle : openMass f u n ≤ ∑ m ∈ Finset.Ico N n, u m := by
      rw [openMass]
      calc ∑ m ∈ Finset.range n, (if n < f m then u m else 0)
          = ∑ m ∈ Finset.Ico N n, (if n < f m then u m else 0) := by
            rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNn]
            have h0 : ∑ m ∈ Finset.Ico 0 N, (if n < f m then u m else 0) = 0 := by
              refine Finset.sum_eq_zero (fun m hm => ?_)
              have hm' : m < N := (Finset.mem_Ico.1 hm).2
              have hfm : f m ≤ M := Finset.le_sup (f := f) (Finset.mem_range.2 hm')
              rw [if_neg (by omega)]
            rw [h0, zero_add]
        _ ≤ ∑ m ∈ Finset.Ico N n, u m := by
            refine Finset.sum_le_sum (fun m _ => ?_)
            by_cases hc : n < f m
            · rw [if_pos hc]
            · rw [if_neg hc]; exact hnn m
    have hle2 : ∑ m ∈ Finset.Ico N n, u m ≤ ∑' k, u (k + N) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hc : ∑ k ∈ Finset.range (n - N), u (N + k) = ∑ k ∈ Finset.range (n - N), u (k + N) :=
        Finset.sum_congr rfl (fun k _ => by rw [add_comm])
      rw [hc]
      exact ((summable_nat_add_iff N).2 hs).sum_le_tsum _ (fun k _ => hnn _)
    linarith
  have hu0 : ∀ᶠ n in atTop, u n < 1 / 2 :=
    hs.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hu0, eventually_ge_atTop N, eventually_ge_atTop M] with n hun hNn hMn
  by_contra hwn
  have hwn' : (θ : ℝ) ≤ w n := not_lt.1 hwn
  have h1 : ctsInd (θ / 2) (w n) ((θ / 2 : ℚ) : ℝ) = 1 :=
    ctsInd_eq_one_of_le_sub _ _ _ (half_pos hθ) (by push_cast; linarith)
  have hrec := h n
  rw [h1, mul_one] at hrec
  have := hopen n hNn hMn
  linarith

/-- **T2, the other direction (contrapositive)**: if `w_n ≥ θ` infinitely often, the firing
sequence is not summable — the soft trader never goes quiet while violations keep coming.
Source: [[fa-adaptive-joint-mandate]] § T2 ("`(∃ᶠ n, θ ≤ w n) → ¬ Summable fire`")
Kind: L
Fidelity: exact
Hyps: (a) `hθ`, `h`. -/
theorem FireRec.not_summable_of_frequently {f : ℕ → ℕ} {θ : ℚ} (hθ : 0 < θ) {w u : ℕ → ℝ}
    (h : FireRec f θ w u) (hfreq : ∃ᶠ n in atTop, (θ : ℝ) ≤ w n) : ¬ Summable u := by
  intro hs
  have hev := h.eventually_lt_of_summable hθ hs
  obtain ⟨n, h1, h2⟩ := (hfreq.and_eventually hev).exists
  linarith

/-- A nonnegative real sequence eventually below every positive rational tends to `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem tendsto_zero_of_eventually_lt_rat {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (h : ∀ θ : ℚ, 0 < θ → ∀ᶠ n in atTop, w n < θ) : Tendsto w atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨θ, hθ0, hθε⟩ := exists_rat_btwn hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h θ (by exact_mod_cast hθ0))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hw0 n)]
  exact lt_trans (hN n hn) hθε

/-- **T2, corollary**: if the firing sequence is summable for every rational threshold `θ > 0`,
then `w_n → 0` (`w ≥ 0`). The step `v3Theorem2` ends with.
Source: [[fa-adaptive-joint-mandate]] § T2 ("Corollary: `(∀ θ > 0, Summable (fire θ)) → Tendsto w atTop (𝓝 0)`")
Kind: C
Fidelity: exact
Hyps: (a) `hw0`, `hs`. -/
theorem tendsto_zero_of_summable_fireSeq {f : ℕ → ℕ} {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (hs : ∀ θ : ℚ, 0 < θ → Summable (fireSeq f θ w)) : Tendsto w atTop (𝓝 0) :=
  tendsto_zero_of_eventually_lt_rat hw0
    (fun θ hθ => (fireSeq_fireRec f θ w).eventually_lt_of_summable hθ (hs θ hθ))

/-! ## D. Instances for `fireSeq` and `adaptFire` -/

/-- `fireSeq` is a one-position weighting.
Source: [[fa-adaptive-joint-mandate]] § T1 (`adaptOpen_le_one`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem fireSeq_onePosition (f : DeferralFunction) (θ : ℚ) (w : ℕ → ℝ) :
    OnePosition f (fireSeq f.f θ w) :=
  (fireSeq_fireRec f.f θ w).onePosition

/-- `fireSeq` is `[0, 1]`-valued.
Source: [[fa-adaptive-joint-mandate]] § T1 (`adaptFire_mem_Icc`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem fireSeq_mem_Icc (f : ℕ → ℕ) (θ : ℚ) (w : ℕ → ℝ) (n : ℕ) :
    fireSeq f θ w n ∈ Set.Icc (0 : ℝ) 1 :=
  (fireSeq_fireRec f θ w).mem_Icc n

/-- **`adaptFire` denotes a one-position weighting on every market** (mandate `adaptOpen_le_one`).
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: exact
Hyps: (a) `hw`, `hθ` -/
theorem adaptFire_onePosition {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    {θ : ℚ} (hθ : 0 < θ) (V : History) :
    OnePosition f (fun n => (adaptFire w f θ n).denote V) := by
  have := (adaptFireR_fireRec hw f hθ V).onePosition
  simpa only [adaptFire_denote hw] using this

/-- **`adaptFire` denotes values in `[0, 1]`** (mandate `adaptFire_mem_Icc`).
Source: [[fa-adaptive-joint-mandate]] § T1
Kind: L
Fidelity: exact
Hyps: (a) `hw`, `hθ` -/
theorem adaptFire_mem_Icc {w : ℕ → EF} (hw : PGenerableWeighting w) (f : DeferralFunction)
    {θ : ℚ} (hθ : 0 < θ) (V : History) (n : ℕ) :
    (adaptFire w f θ n).denote V ∈ Set.Icc (0 : ℝ) 1 := by
  rw [adaptFire_denote hw]
  exact (adaptFireR_fireRec hw f hθ V).mem_Icc n

/-! ## E. F2: the product softening over-fires -/

/-- The *product* softening's recursion law (FAF's `armChain` shape): `p n = (∏_{m<n, n<f m} (1 − p m)) · r n`.
Source: [[fa-adaptive-joint-mandate]] § T1 trap (α)
Kind: D
Fidelity: exact (the trap's object)
Hyps: n/a -/
def ProdRec (f : ℕ → ℕ) (r p : ℕ → ℝ) : Prop :=
  ∀ n, p n = (∏ m ∈ Finset.range n, if n < f m then 1 - p m else 1) * r n

/-- **F2: the product softening over-fires.** With all pieces open for ten days (`f n = n + 10`),
ramp values `r 0 = ½`, `r 1 = r 2 = 1`, the product law gives `p = ½, ½, ¼, …` and the open
position on day `3` is `5/4 > 1` — whereas every solution of the additive law keeps it `≤ 1`
(`FireRec.nonneg_openMass_le_one`). v3's "composing one bounded-size soft update per day" admits
both readings; only the additive one is a one-position machine.
Source: [[fa-adaptive-joint-mandate]] § T1 trap (α); findings F2
Kind: N+
Fidelity: n/a (refutation of the product reading)
Hyps: (a) none -/
theorem product_softening_overfires :
    ∃ (f : ℕ → ℕ) (r : ℕ → ℝ), (∀ n, n < f n) ∧ (∀ n, r n ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p, ProdRec f r p → 1 < openMass f p 3 := by
  refine ⟨fun n => n + 10, fun n => if n = 0 then 1 / 2 else 1,
    fun n => by show n < n + 10; omega,
    fun n => by
      show (if n = 0 then (1 : ℝ) / 2 else 1) ∈ Set.Icc 0 1
      split_ifs <;> norm_num,
    fun p hp => ?_⟩
  have h0 : p 0 = 1 / 2 := by
    rw [hp 0]; simp
  have h1 : p 1 = 1 / 2 := by
    rw [hp 1]; simp [h0]; norm_num
  have h2 : p 2 = 1 / 4 := by
    rw [hp 2]; simp [Finset.prod_range_succ, h0, h1]; norm_num
  simp [openMass, Finset.sum_range_succ, h0, h1, h2]
  norm_num

end Cleanroom.Fa.FaAdaptiveJoint
