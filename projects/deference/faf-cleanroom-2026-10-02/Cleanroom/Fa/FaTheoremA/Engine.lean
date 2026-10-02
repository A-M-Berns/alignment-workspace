import Cleanroom.Fa.FaTheoremA.Half1

/-!
# `fa-theorem-a` · Engine: the gate argument on a generable day-set

The one argument that Theorem A ([[faithful-acceleration-result]] §4.2) and Lemma P
([[route-negative-introspective]] §7) share, written once: on a generable `{0,1}`-valued day-set
`E` of `A`'s market, if the realized `Y_n` is eventually `≤ u` on `E`, the quote `a_n` cannot be
`≥ u + η` infinitely often on `E` (and dually). Proof: pick a rational threshold
`q ∈ (u + η/4, u + η/2)` and a rational width `δ ∈ (0, η/8)`; the gated ramp
`E_n · Ind_δ(a_n > q)` is generable (T2 + `PGenerableWeighting.mul`), **divergent** because it is
`1` on each of the infinitely many days with `E_n = 1` and `a_n ≥ u + η ≥ q + δ`
(`tendsto_prefixSum_atTop_of_frequently_one`), and **one-signed on its support** because a
positive weight forces `E_n = 1` and `q < a_n` while `Y_n ≤ u < q − η/4` there; T4
(`engine_no_persistent_bias`) then contradicts. Theorem A is this at `E ≡ 1`; Lemma P is this
at a general `E`. Only FAF's `recurringunbiasednessexp` is used — the note's route through
Expectation Preemptive Learning (4.8.13) and Limit Coherence is not needed (finding F5 of
[[fa-theorem-a-findings]]).

Scope: one-way — `A` is any inductor over `DPA`; `H` any inductor; neither reads the other's
prices. The only modelling step is `pkg.reflected` (see `Half1.lean`).
-/

namespace Cleanroom.Fa.FaTheoremA

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- **The gate argument, upper side.** On a generable `{0,1}`-valued day-set feature `E` of
`A`'s market: if eventually on `E` the realized `Y_n ≤ u`, then it is not the case that
`a_n ≥ u + η` on infinitely many days of `E`, for any `η > 0`. The gate is
`gatedAbove Y E q δ` with rational `q ∈ (u + η/4, u + η/2)`, `δ ∈ (0, η/8)`.
Scope: one-way; the (c) is `pkg.reflected` (`Half1.lean`).
Source: [[faithful-acceleration-result]] §4.2 (the proof of Theorem A, localized to `E`); [[route-negative-introspective]] §7 (Lemma P)
Kind: C
Fidelity: exact (the note's argument with the day-set made explicit)
Hyps: (a) `hworldA`, `hE`, `hE01`, `hY`; (c) `pkg.reflected`. -/
theorem not_frequently_quote_ge {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {E : ℕ → EF} (hE : PGenerableWeighting E)
    (hE01 : ∀ n, (E n).denote A = 0 ∨ (E n).denote A = 1)
    {u η : ℝ} (hη : 0 < η)
    (hY : ∀ᶠ n in atTop, (E n).denote A = 1 → realized H f X n ≤ u) :
    ¬ ∃ᶠ n in atTop, (E n).denote A = 1 ∧ u + η ≤ quoteSeq Y A n := by
  intro hfreq
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u + η / 4 < u + η / 2 by linarith)
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (show (0 : ℝ) < η / 8 by positivity)
  have hδ0' : (0 : ℚ) < δ := by exact_mod_cast hδ0
  have hW : PGenerableWeighting (gatedAbove Y E q δ) :=
    gatedAbove_pgenerable Y pkg.quote_codes hE q δ
  have hden : ∀ n, (gatedAbove Y E q δ n).denote A =
      (E n).denote A * ctsInd δ ((Y n).expect A n) (q : ℝ) :=
    fun n => gatedAbove_denote Y E hδ0' A n
  have hbd : ∀ n, 0 ≤ (gatedAbove Y E q δ n).denote A ∧ (gatedAbove Y E q δ n).denote A ≤ 1 := by
    intro n
    rw [hden]
    rcases hE01 n with h | h <;> rw [h]
    · simp
    · simpa using ctsInd_mem_Icc δ _ _
  have hone : ∃ᶠ n in atTop, 1 ≤ (gatedAbove Y E q δ n).denote A := by
    refine hfreq.mono ?_
    rintro n ⟨hEn, hn⟩
    rw [hden, hEn, one_mul]
    exact ((ctsInd_eq_one_iff hδ0' _ _).2 (by linarith)).ge
  have hdiv : DivergentWeighting (gatedAbove Y E q δ) A :=
    ⟨hbd, tendsto_prefixSum_atTop_of_frequently_one (fun i => (hbd i).1) hone⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hY
  refine engine_no_persistent_bias pkg hworldA hW ⟨hdiv, η / 4, by positivity, N, ?_⟩
  intro n hn hpos
  rw [hden] at hpos
  have hEn : (E n).denote A = 1 := by
    rcases hE01 n with h | h
    · rw [h, zero_mul] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h
  rw [hEn, one_mul, ctsInd_pos_iff hδ0'] at hpos
  have hYn := hN n hn hEn
  show η / 4 ≤ (Y n).expect A n - (X n).expect H (f.f n)
  linarith

/-- **The gate argument, lower side.** On a generable `{0,1}`-valued day-set feature `E`: if
eventually on `E` the realized `Y_n ≥ u`, then `a_n ≤ u − η` on infinitely many days of `E` is
impossible, for any `η > 0`. The gate is `gatedBelow Y E q δ` with rational
`q ∈ (u − η/2, u − η/4)`, `δ ∈ (0, η/8)`.
Scope: one-way; the (c) is `pkg.reflected`.
Source: [[faithful-acceleration-result]] §4.2; [[route-negative-introspective]] §7; [[route-recurring-ccee]] §4 (the dual gate)
Kind: C
Fidelity: exact
Hyps: (a) `hworldA`, `hE`, `hE01`, `hY`; (c) `pkg.reflected`. -/
theorem not_frequently_quote_le {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {E : ℕ → EF} (hE : PGenerableWeighting E)
    (hE01 : ∀ n, (E n).denote A = 0 ∨ (E n).denote A = 1)
    {u η : ℝ} (hη : 0 < η)
    (hY : ∀ᶠ n in atTop, (E n).denote A = 1 → u ≤ realized H f X n) :
    ¬ ∃ᶠ n in atTop, (E n).denote A = 1 ∧ quoteSeq Y A n ≤ u - η := by
  intro hfreq
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u - η / 2 < u - η / 4 by linarith)
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (show (0 : ℝ) < η / 8 by positivity)
  have hδ0' : (0 : ℚ) < δ := by exact_mod_cast hδ0
  have hW : PGenerableWeighting (gatedBelow Y E q δ) :=
    gatedBelow_pgenerable Y pkg.quote_codes hE q δ
  have hden : ∀ n, (gatedBelow Y E q δ n).denote A =
      (E n).denote A * ctsInd δ (q : ℝ) ((Y n).expect A n) :=
    fun n => gatedBelow_denote Y E hδ0' A n
  have hbd : ∀ n, 0 ≤ (gatedBelow Y E q δ n).denote A ∧ (gatedBelow Y E q δ n).denote A ≤ 1 := by
    intro n
    rw [hden]
    rcases hE01 n with h | h <;> rw [h]
    · simp
    · simpa using ctsInd_mem_Icc δ _ _
  have hone : ∃ᶠ n in atTop, 1 ≤ (gatedBelow Y E q δ n).denote A := by
    refine hfreq.mono ?_
    rintro n ⟨hEn, hn⟩
    rw [hden, hEn, one_mul]
    exact ((ctsInd_eq_one_iff hδ0' _ _).2 (by linarith)).ge
  have hdiv : DivergentWeighting (gatedBelow Y E q δ) A :=
    ⟨hbd, tendsto_prefixSum_atTop_of_frequently_one (fun i => (hbd i).1) hone⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hY
  refine engine_no_persistent_bias_neg pkg hworldA hW ⟨hdiv, η / 4, by positivity, N, ?_⟩
  intro n hn hpos
  rw [hden] at hpos
  have hEn : (E n).denote A = 1 := by
    rcases hE01 n with h | h
    · rw [h, zero_mul] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h
  rw [hEn, one_mul, ctsInd_pos_iff hδ0'] at hpos
  have hYn := hN n hn hEn
  show (Y n).expect A n - (X n).expect H (f.f n) ≤ -(η / 4)
  linarith

end Cleanroom.Fa.FaTheoremA
