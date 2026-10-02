import Cleanroom.Fa.FaForcingTrader.A.TheoremSS
import Cleanroom.Fa.FaTheoremA.Decided

/-!
# `fa-forcing-trader` · angle A · Violation: v3 Theorem 1 under joint legibility (T3)

v3's Theorem 1: on every window-disjoint schedule the violation weight
`w_n = Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t) · Ind_δ(𝔼^H_n(X_n) < t − ε) · 1[n ∈ im d]` has finite
total mass. Its weight reads `H`'s *same-day* price at `A`'s day `n`, so it is legal for `A` only
under v3's joint clearing (A1). Over FAF the only form (A1) can take is joint legibility of the
real sequence: `LegibleOn A violW ∧ LegibleOn H violW` — a `(c)` with no two-market inhabitant in
the run (K3: even `li-coupled-pair`'s `TwoWayPair` publishes `H`'s *day-`f n`* expectation, not
its day-`n` price). The statement is therefore **two-way** and its ledger Status is
`partial: over the OPEN pair`; the same-market instance (`A = H`) inhabits the hypothesis package
(Witnesses).

Proof shape (the mandate's second route): under joint legibility the general Theorem SS
(`theoremSS_limitPoint_general` at `G :=` the `A`-legible copy of `violW`) gives a limit point `0`
of the `violW`-average of `a_n − h_n`; on the support `a_n > t` and `h_n < t − ε`, so that average
is `≥ ε` wherever the mass is positive — contradiction once the mass diverges. The `H`-side
content is T4 (the criterion on FAF's own trader), the `A`-side is `quote_unbiased`.
-/

namespace Cleanroom.Fa.FaForcingTrader.A

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader
  Filter Topology

/-- **T3 (headline). v3 Theorem 1, violation-weight form, under joint legibility.** For inductors
`A`, `H`, a quote package, a window-disjoint schedule `d` for `f`, rationals `t`, `ε > 0`,
`δ > 0`, and the violation weight
`violW_n = 1[n ∈ im d] · Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t) · Ind_δ(𝔼^H_n(X_n) < t − ε)` legible on
*both* markets (`hjoint`, v3's (A1) in the only form FAF can state): the mass
`∑_{i≤n} violW_i` does **not** diverge.
Scope: **two-way** (partial: over the OPEN pair — li-coupled-pair's `twoWayPair_exists` — and K3:
even that pair does not supply `hjoint`, which reads `𝔼^H_n(X_n)` at `A`'s day `n`). e.d. family
`X`. Schedule: window-disjoint `DeferralFunction`. Grade: limit point on the `A` side, full limit
on the `H` side; the conclusion is finiteness.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
`hjoint` is about the *real sequence* `violW`, never about the `A`-denotation of a feature pricing
`H`'s sentences on `A`'s market (trap (i)); the ramps' orientations are `dsWeight_pos_imp` (K7);
`δ = 0` makes both ramps `≡ 0` and the statement vacuous, so the headline takes `0 < δ`.
Source: root-fa-019 (the complete proof); lean-deference-042; root-deference-050 (the v6 original); root-fa-2-004; [[fa-positive-results-corrected-v3]] §3
Kind: C
Fidelity: variant: joint legibility of the real violation sequence on each market's own `PGenerableWeighting` class (`hjoint`) in place of v3's joint clearing (K2, K3) — no ledger object appears in the package; schedules are `DeferralFunction`s (K1)
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hwd`, `hδ`, `hε`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H` — li-quote-lane); (c) `hjoint` (joint legibility, v3's (A1); no two-market inhabitant, K3; same-market instance in Witnesses). -/
theorem v3Theorem1_of_jointLegible {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hε : 0 < ε)
    (hjoint : LegibleOn A (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) ∧
      LegibleOn H (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ)) :
    ¬ Tendsto (prefixSum (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ))
      atTop atTop := by
  intro hdivR
  obtain ⟨GA, hGA, hGAv⟩ := hjoint.1
  have hfun : (fun n => (GA n).denote A) =
      violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ := funext hGAv
  have hdivA : DivergentWeighting GA A := by
    refine ⟨fun n => by rw [hGAv]; exact violW_mem_Icc _ _ _ _ _ _ n, ?_⟩
    rw [hfun]
    exact hdivR
  have hsuppA : ∀ n, (GA n).denote A ≠ 0 → ∃ k, d.f k = n :=
    fun n hn => violW_ne_zero_imp _ _ _ _ _ _ (by rwa [hGAv] at hn)
  have hL : LegibleOn H (fun n => (GA n).denote A) := by
    rw [hfun]
    exact hjoint.2
  have hlp := theoremSS_limitPoint_general pkg hcode hworldA hworldH hval hwd hGA hsuppA hL hdivA
  rw [hfun, hasLimitPoint_zero_iff] at hlp
  have hev : ∀ᶠ n in atTop,
      0 < prefixSum (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) n :=
    hdivR.eventually (eventually_gt_atTop 0)
  obtain ⟨n, h1, h2⟩ := ((hlp ε (by exact_mod_cast hε)).and_eventually hev).exists
  have hge : (ε : ℝ) ≤ weightedAverage (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ)
      (fun i => quoteSeq Y A i - (X i).expect H i) n := by
    refine le_weightedAverage_of_support (fun i => (violW_mem_Icc _ _ _ _ _ _ i).1)
      (fun i hi => ?_) h2
    obtain ⟨-, hta, hht⟩ := violW_pos_imp d _ _ t ε hδ hi
    linarith
  have hbias : weightedBias (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ)
      (quoteSeq Y A) (fun n => (X n).expect H n) n =
      weightedAverage (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ)
        (fun i => quoteSeq Y A i - (X i).expect H i) n := rfl
  rw [hbias, abs_lt] at h1
  linarith [h1.2]

/-- **T3, corollary: the violation weight is summable** (nonnegative with bounded partial sums).
Scope: two-way (partial: over the OPEN pair).
Source: [[fa-positive-results-corrected-v3]] §3 ("`∑_k w_{d_k} < ∞`"); root-fa-019
Kind: C
Fidelity: as `v3Theorem1_of_jointLegible`
Hyps: as `v3Theorem1_of_jointLegible`: (c) `pkg.reflected`; (c) `hjoint`. -/
theorem v3Theorem1_summable {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hε : 0 < ε)
    (hjoint : LegibleOn A (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) ∧
      LegibleOn H (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ)) :
    Summable (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) := by
  have hnot := v3Theorem1_of_jointLegible pkg hcode hworldA hworldH hval hwd t ε hδ hε hjoint
  have hnn : ∀ n, 0 ≤ violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ n :=
    fun n => (violW_mem_Icc _ _ _ _ _ _ n).1
  have hbdd : ∃ M, ∀ n,
      prefixSum (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) n ≤ M := by
    by_contra hcon
    push_neg at hcon
    exact hnot (tendsto_atTop_atTop_of_monotone (prefixSum_mono hnn)
      (fun M => let ⟨n, hn⟩ := hcon M; ⟨n, hn.le⟩))
  obtain ⟨M, hM⟩ := hbdd
  refine summable_of_sum_range_le (c := M) hnn (fun n => ?_)
  rcases n with _ | n
  · have h0 := hM 0
    rw [prefixSum_zero] at h0
    simp only [Finset.range_zero, Finset.sum_empty]
    linarith [hnn 0]
  · exact hM n

/-- **T3 at a fixed LUV `X`** (the mandate's statement shape: `pkg : CrossQuotePackage H DPA f (fun _ => X) Y`,
`hcode : X.MachineThresholdCodes`).
Scope: two-way (partial: over the OPEN pair). Fixed `X`.
Source: root-fa-019; root-fa-013 (the grid-wise statement is this at a fixed `d`)
Kind: C
Fidelity: as `v3Theorem1_of_jointLegible`
Hyps: (c) `pkg.reflected`; (c) `hjoint`. -/
theorem v3Theorem1_fixed {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} (X : LUV)
    {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => X) Y)
    (hcode : X.MachineThresholdCodes)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt X x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hε : 0 < ε)
    (hjoint : LegibleOn A (violW d (quoteSeq Y A) (fun n => X.expect H n) t ε δ) ∧
      LegibleOn H (violW d (quoteSeq Y A) (fun n => X.expect H n) t ε δ)) :
    ¬ Tendsto (prefixSum (violW d (quoteSeq Y A) (fun n => X.expect H n) t ε δ)) atTop atTop :=
  v3Theorem1_of_jointLegible pkg (machineThresholdCodeSeq_const hcode) hworldA hworldH
    (fun _ v hv => hval v hv) hwd t ε hδ hε hjoint

end Cleanroom.Fa.FaForcingTrader.A
