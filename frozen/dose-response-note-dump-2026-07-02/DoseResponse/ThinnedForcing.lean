/-
  Kernel-checked core of THINNED FORCING — Theorem T1 of `dose-response.md` §5,
  in the per-sparse-schedule form (the unrestricted form needs Sparsification —
  the note's §8, problem 1, open).

  Discipline (identical to the corpus): the arithmetic/asymptotic core is the
  vendored `FaithfulAccel` chain (`round_profit_ge` → … → `soft_total_trust`),
  re-run with the THINNED weight  S·c·dsWeight  — schedule indicator × coin ×
  the doubly-soft gate.  The support lemmas T1 needs ("w > 0 ⇒ exposed day,
  scheduled day, quote high, price low") are PROVED about the construction.
  The LI inputs stay named hypotheses:
    hbias — [LI 4.8.16] (EUFF) instantiated for the market A over Γ_A as in §5
            of the note (the (II^S) display), i.e. the weighted forecast bias is
            o(Σw) along the schedule;
    hbdd  — the LIC for H applied to the round-trip trader of §5.  The
            f-SPARSITY of the schedule lives here and only here: disjoint
            positions of size ≤ 1 are what make the trader's plausible value
            bounded, so sparsity is part of this hypothesis' provenance, not of
            the arithmetic.  Formally `S` is just an indicator sequence.
  No `sorry`; axiom audit at the end.

  Map to the note (§5):
    thinnedWeight            the weight  w_n = S_n · c_n · Ind_δ(a−t)·Ind_δ(t−ε−p)
    thinnedWeight_pos_imp_*  its support facts (coin fired, scheduled, a > t, p < t−ε)
    thinnedWeight_continuous per-day continuity in the price pair (trader legality)
    thinned_forcing          T1's headline:  Σ_{n∈S} w_n < ∞  (as `Summable`)
    design_non_interference  Corollary T1.1: at S ≡ 1, c ≡ 1 the weight IS dsWeight —
                             the production guarantee is untouched by the audit
    gated_average_forced     T1's second display: where the thinned gate carries
                             infinite weight, the gated average of H's next-day
                             price is ≥ t − ε − o(1) (full strength, no δ loss)
-/
import DoseResponse.FaithfulAccelCore

open Filter Topology FaithfulAccel

namespace ThinnedForcing

/-- A `{0,1}`-valued sequence: coins (D1) and schedule indicators alike.  Model (D)
    only — coins are fixed sequences, exactly as §6.2 prescribes. -/
def IsIndicator (c : ℕ → ℝ) : Prop := ∀ n, c n = 0 ∨ c n = 1

theorem IsIndicator.nonneg {c : ℕ → ℝ} (hc : IsIndicator c) (n : ℕ) : 0 ≤ c n := by
  rcases hc n with h | h <;> simp [h]

theorem IsIndicator.eq_one_of_pos {c : ℕ → ℝ} (hc : IsIndicator c) {n : ℕ}
    (h : 0 < c n) : c n = 1 := by
  rcases hc n with h0 | h1
  · exact absurd h (by simp [h0])
  · exact h1

theorem IsIndicator.le_one {c : ℕ → ℝ} (hc : IsIndicator c) (n : ℕ) : c n ≤ 1 := by
  rcases hc n with h | h <;> simp [h]

/-- The soft indicator never exceeds its saturation value. -/
theorem softInd_le_one (δ x : ℝ) : softInd δ x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The doubly-soft gate is a genuine `[0,1]` weight. -/
theorem dsWeight_le_one (t ε δ a p : ℝ) : dsWeight t ε δ a p ≤ 1 :=
  calc softInd δ (a - t) * softInd δ (t - ε - p)
      ≤ 1 * 1 := mul_le_mul (softInd_le_one _ _) (softInd_le_one _ _)
        (softInd_nonneg _ _) zero_le_one
    _ = 1 := mul_one 1

/-- The **thinned doubly-soft violation weight** of §5, restricted to the schedule:
    `S_n · c_n · Ind_δ(a_n − t) · Ind_δ(t − ε − p_n)`.  Computed from the recorded
    pair `(c_n, c_n·a_n)` — the quote factor is moot when the coin is 0. -/
noncomputable def thinnedWeight (S c : ℕ → ℝ) (t ε δ : ℝ) (a p : ℕ → ℝ) (n : ℕ) : ℝ :=
  S n * (c n * dsWeight t ε δ (a n) (p n))

section Support

variable {S c : ℕ → ℝ} {t ε δ : ℝ} {a p : ℕ → ℝ}

private theorem pos_factors {x y : ℝ} (hx : 0 ≤ x) (_hy : 0 ≤ y) (h : 0 < x * y) :
    0 < x ∧ 0 < y := by
  rcases mul_pos_iff.1 h with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact ⟨h1, h2⟩
  · exact absurd h1 (not_lt.2 hx)

theorem thinnedWeight_nonneg (hS : IsIndicator S) (hc : IsIndicator c) (n : ℕ) :
    0 ≤ thinnedWeight S c t ε δ a p n :=
  mul_nonneg (hS.nonneg n) (mul_nonneg (hc.nonneg n) (dsWeight_nonneg _ _ _ _ _))

/-- Support: a firing weight certifies a *scheduled* day. -/
theorem thinnedWeight_pos_imp_scheduled (hS : IsIndicator S) (hc : IsIndicator c)
    {n : ℕ} (h : 0 < thinnedWeight S c t ε δ a p n) : S n = 1 :=
  hS.eq_one_of_pos (pos_factors (hS.nonneg n)
    (mul_nonneg (hc.nonneg n) (dsWeight_nonneg _ _ _ _ _)) h).1

/-- Support: a firing weight certifies an *exposed* day (the coin fired) — the
    thinning is real. -/
theorem thinnedWeight_pos_imp_exposed (hS : IsIndicator S) (hc : IsIndicator c)
    {n : ℕ} (h : 0 < thinnedWeight S c t ε δ a p n) : c n = 1 := by
  have h2 := (pos_factors (hS.nonneg n)
    (mul_nonneg (hc.nonneg n) (dsWeight_nonneg _ _ _ _ _)) h).2
  exact hc.eq_one_of_pos (pos_factors (hc.nonneg n) (dsWeight_nonneg _ _ _ _ _) h2).1

private theorem thinnedWeight_pos_imp_ds (hS : IsIndicator S) (hc : IsIndicator c)
    {n : ℕ} (h : 0 < thinnedWeight S c t ε δ a p n) :
    0 < dsWeight t ε δ (a n) (p n) := by
  have h2 := (pos_factors (hS.nonneg n)
    (mul_nonneg (hc.nonneg n) (dsWeight_nonneg _ _ _ _ _)) h).2
  exact (pos_factors (hc.nonneg n) (dsWeight_nonneg _ _ _ _ _) h2).2

/-- Support: a firing weight certifies the quote is high (`t < a_n`) — inherited
    from the vendored `dsWeight` support lemma. -/
theorem thinnedWeight_pos_imp_quote_high (hS : IsIndicator S) (hc : IsIndicator c)
    (hδ : 0 < δ) {n : ℕ} (h : 0 < thinnedWeight S c t ε δ a p n) : t < a n :=
  dsWeight_pos_imp_fst t ε δ (a n) (p n) hδ (thinnedWeight_pos_imp_ds hS hc h)

/-- Support: a firing weight certifies the arm sits low (`p_n < t − ε`). -/
theorem thinnedWeight_pos_imp_price_low (hS : IsIndicator S) (hc : IsIndicator c)
    (hδ : 0 < δ) {n : ℕ} (h : 0 < thinnedWeight S c t ε δ a p n) : p n < t - ε :=
  dsWeight_pos_imp_snd t ε δ (a n) (p n) hδ (thinnedWeight_pos_imp_ds hS hc h)

/-- Trader legality (the `dsWeight` discipline, thinned): on each day the weight is
    a *constant* (the recorded schedule bit and coin bit) times the continuous
    doubly-soft gate — jointly continuous in the price pair. -/
theorem thinnedWeight_continuous (S c : ℕ → ℝ) (t ε δ : ℝ) (n : ℕ) :
    Continuous (fun ap : ℝ × ℝ => S n * (c n * dsWeight t ε δ ap.1 ap.2)) :=
  (continuous_const.mul (continuous_const.mul (dsWeight_continuous t ε δ)))

end Support

/-- Monotone upgrade: a nonnegative series whose partial sums do not diverge has
    bounded partial sums.  (This is what turns the chain's `¬(W → ∞)` into the
    note's `Σ_{n∈S} w_n < ∞`.) -/
theorem bounded_of_not_tendsto (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h : ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    ∃ M, ∀ n, ∑ i ∈ Finset.range n, w i ≤ M := by
  by_contra hM
  push_neg at hM
  apply h
  apply tendsto_atTop_atTop_of_monotone
  · intro m n hmn
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset.2 fun x hx => Finset.mem_range.2 (lt_of_lt_of_le hx hmn))
      (fun i _ _ => hw i)
  · intro b
    obtain ⟨n, hn⟩ := hM b
    exact ⟨n, hn.le⟩

/-- **Theorem T1 (thinned forcing, per-sparse-schedule form).**  Instantiate the
    vendored kernel-checked chain at the thinned weight: with A's calibration along
    the schedule (`hbias`, = [LI 4.8.16] as instantiated in §5) and the LIC bound on
    the sparse round-trip trader (`hbdd` — f-sparsity enters here, as provenance),
    the thinned violation weight is SUMMABLE:  Σ_{n∈S} w_n < ∞.

    All support hypotheses of `soft_total_trust` are discharged by the
    `thinnedWeight_pos_imp_*` lemmas — theorems about the construction, not
    assumptions. -/
theorem thinned_forcing (S c : ℕ → ℝ) (hS : IsIndicator S) (hc : IsIndicator c)
    (v p a : ℕ → ℝ) (t ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hbias : Tendsto (fun n =>
        (∑ i ∈ Finset.range n, thinnedWeight S c t ε δ a p i * (v i - a i))
          / (∑ i ∈ Finset.range n, thinnedWeight S c t ε δ a p i)) atTop (𝓝 0))
    (hbdd : ∃ M, ∀ n,
        (∑ i ∈ Finset.range n, thinnedWeight S c t ε δ a p i * (v i - p i)) ≤ M) :
    Summable (thinnedWeight S c t ε δ a p) := by
  have hw : ∀ i, 0 ≤ thinnedWeight S c t ε δ a p i := thinnedWeight_nonneg hS hc
  have hnot : ¬ Tendsto
      (fun n => ∑ i ∈ Finset.range n, thinnedWeight S c t ε δ a p i) atTop atTop :=
    soft_total_trust (thinnedWeight S c t ε δ a p) v p a t ε hε hw
      (fun i h => thinnedWeight_pos_imp_quote_high hS hc hδ h)
      (fun i h => thinnedWeight_pos_imp_price_low hS hc hδ h)
      hbias hbdd
  obtain ⟨M, hM⟩ := bounded_of_not_tendsto _ hw hnot
  exact summable_of_sum_range_le hw hM

/-- **Corollary T1.1 (design non-interference).**  At `S ≡ 1`, `c ≡ 1` (undosed,
    unscheduled) the thinned weight is *definitionally* the corpus's `dsWeight`:
    T1 specializes to `faithful-acceleration.md` §5 verbatim.  Reference arms,
    coins, and audits appear nowhere in the production guarantee. -/
theorem design_non_interference (t ε δ : ℝ) (a p : ℕ → ℝ) (n : ℕ) :
    thinnedWeight (fun _ => 1) (fun _ => 1) t ε δ a p n
      = dsWeight t ε δ (a n) (p n) := by
  simp [thinnedWeight]

/- ====================================================================================
   T1's second display: the gated classwise form.  Where the thinned GATE
   g_n = S_n·c_n·Ind_δ(a_n−t) carries infinite weight, the gate-weighted average of
   H's next-day price is forced up to t − ε − o(1) — the note's display at full
   strength.  The key is the ramp identity: below saturation the second soft
   indicator gives g·(t−ε−p) = δ·w EXACTLY, so the deficit g·(t−ε−p)⁺ is paid for
   by max δ 1 · w on every day, and Σw < ∞ caps the total deficit.  The bridge is
   one pointwise inequality (`gate_pointwise`), then pure averaging arithmetic.
   ==================================================================================== -/

/-- The thinned gate `g_n = S_n · c_n · Ind_δ(a_n − t)` (T1's display). -/
noncomputable def thinnedGate (S c : ℕ → ℝ) (t δ : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  S n * (c n * softInd δ (a n - t))

theorem thinnedGate_nonneg {S c : ℕ → ℝ} (hS : IsIndicator S) (hc : IsIndicator c)
    (t δ : ℝ) (a : ℕ → ℝ) (n : ℕ) : 0 ≤ thinnedGate S c t δ a n :=
  mul_nonneg (hS.nonneg n) (mul_nonneg (hc.nonneg n) (softInd_nonneg _ _))

/-- The soft indicator saturates past its ramp. -/
theorem softInd_eq_one (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) : softInd δ x = 1 := by
  unfold softInd
  have h1 : (1 : ℝ) ≤ x / δ := (one_le_div hδ).2 hx
  rw [min_eq_left h1, max_eq_right zero_le_one]

/-- **The pointwise bridge, full strength.**  For prices `≥ 0` and `t ≤ 1`: on every
    day, `g_n·(t − ε) − max δ 1 · w_n ≤ g_n·p_n`.  Three-way split on the deficit
    `t − ε − p_n`: nonpositive (price already clears the threshold); on the ramp
    `(0, δ]`, where the identity `g·(t − ε − p) = δ·w` is EXACT; past saturation,
    where `w = g` and the deficit is `< 1`.  This is the ramp identity of the
    note's §5 gated-form proof. -/
theorem gate_pointwise {S c : ℕ → ℝ} (hS : IsIndicator S) (hc : IsIndicator c)
    {t ε δ : ℝ} (hδ : 0 < δ) (ht : t ≤ 1) {a p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n)
    (hε : 0 < ε) (n : ℕ) :
    thinnedGate S c t δ a n * (t - ε) - max δ 1 * thinnedWeight S c t ε δ a p n
      ≤ thinnedGate S c t δ a n * p n := by
  set g := thinnedGate S c t δ a n with hg
  have hg0 : 0 ≤ g := thinnedGate_nonneg hS hc t δ a n
  have hw : thinnedWeight S c t ε δ a p n = g * softInd δ (t - ε - p n) := by
    simp only [hg, thinnedWeight, thinnedGate, dsWeight]
    ring
  have hkey : g * (t - ε - p n) ≤ max δ 1 * thinnedWeight S c t ε δ a p n := by
    rw [hw]
    rcases le_or_gt (t - ε - p n) 0 with hle | hpos
    · have h1 : g * (t - ε - p n) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg0 hle
      have h2 : 0 ≤ max δ 1 * (g * softInd δ (t - ε - p n)) :=
        mul_nonneg (le_max_of_le_right zero_le_one)
          (mul_nonneg hg0 (softInd_nonneg _ _))
      linarith
    · rcases le_or_gt (t - ε - p n) δ with hramp | hsat
      · -- on the ramp: softInd = (t−ε−p)/δ, so g·(t−ε−p) = δ·w exactly
        have hsi : softInd δ (t - ε - p n) = (t - ε - p n) / δ := by
          unfold softInd
          rw [min_eq_right ((div_le_one hδ).2 hramp),
            max_eq_right (div_nonneg hpos.le hδ.le)]
        rw [hsi]
        have hfact : δ * (g * ((t - ε - p n) / δ)) = g * (t - ε - p n) := by
          field_simp
        calc g * (t - ε - p n) = δ * (g * ((t - ε - p n) / δ)) := hfact.symm
          _ ≤ max δ 1 * (g * ((t - ε - p n) / δ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (mul_nonneg hg0 (div_nonneg hpos.le hδ.le))
      · -- past saturation: w = g and the deficit t − ε − p < 1
        have hsi : softInd δ (t - ε - p n) = 1 := softInd_eq_one δ _ hδ hsat.le
        rw [hsi, mul_one]
        have h1 : t - ε - p n ≤ 1 := by linarith [hp n]
        have h2 : (1:ℝ) ≤ max δ 1 := le_max_right _ _
        nlinarith
  have hexp : g * (t - ε) - g * p n = g * (t - ε - p n) := by ring
  linarith

/-- **T1, gated classwise form — the note's display at full strength.**  If the
    thinned violation weight is summable (T1's conclusion, `hΣw`) while the thinned
    gate carries infinite weight (`hG`), then for every `η > 0` the gate-weighted
    running average of H's next-day price eventually clears `t − ε − η` — i.e. the
    note's `≥ t − ε − o(1)`, with no `δ`-loss.  Pure averaging arithmetic from
    `gate_pointwise`, with total deficit capped by `max δ 1 · M`; prices in `[0,1]`,
    `t ≤ 1`. -/
theorem gated_average_forced {S c : ℕ → ℝ} (hS : IsIndicator S) (hc : IsIndicator c)
    {t ε δ : ℝ} (hδ : 0 < δ) (ht : t ≤ 1) (hε : 0 < ε)
    {a p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n)
    (hSw : ∃ M, ∀ n, ∑ i ∈ Finset.range n, thinnedWeight S c t ε δ a p i ≤ M)
    (hG : Tendsto (fun n => ∑ i ∈ Finset.range n, thinnedGate S c t δ a i)
      atTop atTop)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N in atTop,
      t - ε - η ≤
        (∑ i ∈ Finset.range N, thinnedGate S c t δ a i * p i)
          / (∑ i ∈ Finset.range N, thinnedGate S c t δ a i) := by
  obtain ⟨M, hM⟩ := hSw
  set M' : ℝ := max δ 1 * M with hM'def
  filter_upwards [hG.eventually_ge_atTop (max (M' / η) 1)] with N hN
  set G : ℝ := ∑ i ∈ Finset.range N, thinnedGate S c t δ a i with hGdef
  have hG1 : (1 : ℝ) ≤ G := le_trans (le_max_right _ _) hN
  have hGpos : (0 : ℝ) < G := lt_of_lt_of_le one_pos hG1
  -- sum the pointwise bridge; the total deficit is ≤ max δ 1 · M =: M'
  have hsum : G * (t - ε) - M' ≤ ∑ i ∈ Finset.range N, thinnedGate S c t δ a i * p i := by
    have h1 : ∑ i ∈ Finset.range N,
        (thinnedGate S c t δ a i * (t - ε) - max δ 1 * thinnedWeight S c t ε δ a p i)
          ≤ ∑ i ∈ Finset.range N, thinnedGate S c t δ a i * p i :=
      Finset.sum_le_sum fun i _ => gate_pointwise hS hc hδ ht hp hε i
    have h2 : ∑ i ∈ Finset.range N,
        (thinnedGate S c t δ a i * (t - ε) - max δ 1 * thinnedWeight S c t ε δ a p i)
          = G * (t - ε)
            - max δ 1 * ∑ i ∈ Finset.range N, thinnedWeight S c t ε δ a p i := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← hGdef]
    have h3 : max δ 1 * (∑ i ∈ Finset.range N, thinnedWeight S c t ε δ a p i) ≤ M' :=
      mul_le_mul_of_nonneg_left (hM N) (le_max_of_le_right zero_le_one)
    linarith
  -- divide by the (positive, large) gate mass
  have hMη : M' / G ≤ η := by
    have hMG : M' / η ≤ G := le_trans (le_max_left _ _) hN
    rw [div_le_iff₀ hη] at hMG
    rw [div_le_iff₀ hGpos]
    linarith [mul_comm G η]
  have hdiv : (G * (t - ε) - M') / G
      ≤ (∑ i ∈ Finset.range N, thinnedGate S c t δ a i * p i) / G := by
    gcongr
  have hsplit : (G * (t - ε) - M') / G = (t - ε) - M' / G := by
    field_simp
  calc t - ε - η ≤ t - ε - M' / G := by linarith
    _ = (G * (t - ε) - M') / G := hsplit.symm
    _ ≤ _ := hdiv

end ThinnedForcing

-- Axiom audit: each must rest on ONLY [propext, Classical.choice, Quot.sound] (no `sorryAx`).
#print axioms ThinnedForcing.softInd_le_one
#print axioms ThinnedForcing.dsWeight_le_one
#print axioms ThinnedForcing.thinnedWeight_nonneg
#print axioms ThinnedForcing.thinnedWeight_pos_imp_scheduled
#print axioms ThinnedForcing.thinnedWeight_pos_imp_exposed
#print axioms ThinnedForcing.thinnedWeight_pos_imp_quote_high
#print axioms ThinnedForcing.thinnedWeight_pos_imp_price_low
#print axioms ThinnedForcing.thinnedWeight_continuous
#print axioms ThinnedForcing.bounded_of_not_tendsto
#print axioms ThinnedForcing.thinned_forcing
#print axioms ThinnedForcing.design_non_interference
#print axioms ThinnedForcing.softInd_eq_one
#print axioms ThinnedForcing.gate_pointwise
#print axioms ThinnedForcing.gated_average_forced
