import Cleanroom.Fa.FaAdaptiveJoint.Bridge
import Cleanroom.Fa.FaForcingTrader.A.TheoremSS

/-!
# `fa-adaptive-joint` · Theorem2: v3 Theorem 2 and Corollaries 1–3, 5 (T3)

[[fa-adaptive-joint-mandate]] T3. v3's Theorem 2 — the schedule-free violation weight
`viol_n = Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t) · Ind_δ(𝔼^H_n(X_n) < t − ε)` tends to `0` on **all** days
— from FAF's criterion on both sides and the adaptive weighting of T1: fix `θ`; the firing
sequence `u = fireSeq f θ viol` is `A`-generable and `H`-generable (T1 on each market's legible
copy, `hjoint`); if its mass diverged, `quote_unbiased` (schedule-free, the `A` side) would give a
limit point `0` of the `u`-average of `a_n − Y_n`, the `H`-side bridge (T4, on the `H`-copy,
one-position by T2) with the mesh term (dependency T5) the limit `0` of the `u`-average of
`Y_n − h_n`, while on `u`'s support `a_n − h_n > ε` (firing days are near-violation days,
`FireRec.pos_imp`); so `u` is summable and T2 gives `∀ᶠ n, viol_n < θ`; every rational `θ` gives
`viol → 0`. This discharges `fa-forcing-trader`'s chasing (c) `hch`
(`v3Theorem1_tendsto_zero_of_chasing`): the schedule that chases violations is now the trader,
and its legality is proved (T1) rather than assumed.

Two statements: `v3Theorem2_of_bridge` takes T4's conclusion as the named hypothesis
`hbridge : AdaptiveBridgeHolds H f X` and is sorry-free; `v3Theorem2_of_jointLegible` (the
statement of record) discharges it by the OPEN `adaptiveBridge` and is listed in
`fa-adaptive-joint-open.txt`. Corollaries 2 and 3 likewise (`_of_bridge` sorry-free, the record
names resting on the OPEN row). Corollary 1 is Theorem 2 itself at every rational `(t, ε, δ)`
(per parameter — each `θ` its own trader, no uniformity, v3 Cor 5 (ii)); Corollary 4 (averaged
form) is the dependency's T7 and root-fa-006; Corollary 5's three limits are scope clauses.
-/

namespace Cleanroom.Fa.FaAdaptiveJoint

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Filter Topology
open Cleanroom.Fa.FaForcingTrader.A (hasLimitPoint_zero_of_add_tendsto weightedAverage_three)

/-- The firing sequence of a legible real sequence is denoted by `adaptFire` on the legible copy.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) `hθ`; (c) `hx` -/
theorem adaptFire_denote_of_legible {P : History} {x : ℕ → ℝ} {G : ℕ → EF}
    (hG : PGenerableWeighting G) (hGx : ∀ n, (G n).denote P = x n) (f : DeferralFunction)
    {θ : ℚ} (hθ : 0 < θ) :
    (fun n => (adaptFire G f θ n).denote P) = fireSeq f.f θ x := by
  funext n
  rw [adaptFire_denote_fireSeq hG f hθ]
  congr 1
  funext m
  exact hGx m

/-- **The gate-general form of v3 Theorem 2 (two-way, bridge as a hypothesis).** For *any* real
gate `g ∈ [0,1]` legible on both markets whose support carries a uniform gap `c ≤ a_n − h_n`
(`hsupp`), `g_n → 0`. This is the whole of T3's argument with the violation weight abstracted
away: `v3Theorem2_of_bridge` is the instance `g = viol`, `c = ε` (support by `dsWeight_pos_imp`),
and T7 (iii)'s positive transfer is the instance `g = staleViol` under "no one-day jumps on the
gate" (`Staleness.lean`). Proof: fix `θ`; the firing weighting `u_θ = fireSeq f θ g` is legal on
`A` and on `H` (T1 on each legible copy); if `∑ u_θ = ∞`, `quote_unbiased` (schedule-free) gives
a limit point `0` of the `u_θ`-average of `a − Y`, the bridge on the `H`-copy (one-position by
T2) with the mesh term the limit `0` of the `u_θ`-average of `Y − h`, while on `u_θ`'s support
`g > θ/2 > 0` so `a − h ≥ c`: contradiction; so `∑ u_θ < ∞` and T2 gives `∀ᶠ n, g n < θ`.
Scope: two-way (partial: over the OPEN pair). Grade: limit point on the `A` side, full limit on
the `H` side. (A4): expressibility T1; exploitation `hbridge` (T4, OPEN).
Source: [[fa-positive-results-corrected-v3]] §4 Theorem 2 (the proof, with the gate abstracted); [[fa-adaptive-joint-mandate]] § T3, § T7 (iii)
Kind: C
Fidelity: stronger: any legible gate with a support gap, not only the violation weight
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hg`, `hc`, `hsupp`; (c) `pkg.reflected`; (c) `hjoint`; `hbridge` (T4's conclusion, OPEN-dependent). -/
theorem v3Theorem2_gate_of_bridge {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {g : ℕ → ℝ} (hg : ∀ n, g n ∈ Set.Icc (0 : ℝ) 1) {c : ℝ} (hc : 0 < c)
    (hsupp : ∀ n, 0 < g n → c ≤ quoteSeq Y A n - (X n).expect H n)
    (hjoint : LegibleOn A g ∧ LegibleOn H g) (hbridge : AdaptiveBridgeHolds H f X) :
    Tendsto g atTop (𝓝 0) := by
  have hg0 : ∀ n, 0 ≤ g n := fun n => (hg n).1
  refine tendsto_zero_of_summable_fireSeq (f := f.f) hg0 (fun θ hθ => ?_)
  set u := fireSeq f.f θ g with hu
  have hrec : FireRec f.f θ g u := fireSeq_fireRec _ _ _
  by_contra hns
  have hnn : ∀ n, 0 ≤ u n := fun n => (hrec.mem_Icc n).1
  have hdivR : Tendsto (prefixSum u) atTop atTop := by
    have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).1 hns
    exact h.comp (tendsto_add_atTop_nat 1)
  -- the `A` side: the firing weighting is `A`-generable and divergent, so the quote is unbiased on it
  obtain ⟨GA, hGA, hGAv⟩ := hjoint.1
  have hfunA : (fun n => (adaptFire GA f θ n).denote A) = u :=
    adaptFire_denote_of_legible hGA hGAv f hθ
  have hdivA : DivergentWeighting (adaptFire GA f θ) A := by
    refine ⟨fun n => ?_, ?_⟩
    · rw [congrFun hfunA n]
      exact ⟨hnn n, (hrec.mem_Icc n).2⟩
    · rw [hfunA]
      exact hdivR
  have hlp := quote_unbiased pkg hworldA (adaptFire_pgenerable hGA f θ) hdivA
  rw [hfunA] at hlp
  -- the `H` side: the same real weighting is `H`-generable, one-position and divergent
  obtain ⟨GH, hGH, hGHv⟩ := hjoint.2
  have hfunH : (fun n => (adaptFire GH f θ n).denote H) = u :=
    adaptFire_denote_of_legible hGH hGHv f hθ
  have hdivH : DivergentWeighting (adaptFire GH f θ) H := by
    refine ⟨fun n => ?_, ?_⟩
    · rw [congrFun hfunH n]
      exact ⟨hnn n, (hrec.mem_Icc n).2⟩
    · rw [hfunH]
      exact hdivR
  have honeH : OnePosition f (fun n => (adaptFire GH f θ n).denote H) := by
    rw [hfunH]
    exact hrec.onePosition
  have hbr := hbridge _ (adaptFire_pgenerable hGH f θ) honeH hdivH
  rw [hfunH] at hbr
  have hmesh : WeightedApprox u (fun n => (bundle X n).price H (f.f n)) (realized H f X) :=
    weightedApprox_bundle_realized hcode hworldH hval f hnn hdivR
  unfold WeightedApprox at hbr hmesh
  have hv := hbr.sub hmesh
  rw [sub_zero] at hv
  have hlp2 : HasLimitPoint (weightedAverage u (fun i => quoteSeq Y A i - (X i).expect H i)) 0 :=
    hasLimitPoint_zero_of_add_tendsto hlp hv (fun n => by
      rw [weightedBias]
      exact weightedAverage_three u (quoteSeq Y A) (realized H f X)
        (fun i => (bundle X i).price H (f.f i)) (fun n => (X n).expect H n) n)
  -- the squeeze: on the support `a_n − h_n ≥ c`
  rw [hasLimitPoint_zero_iff] at hlp2
  have hev : ∀ᶠ n in atTop, 0 < prefixSum u n := hdivR.eventually (eventually_gt_atTop 0)
  obtain ⟨n, h1, h2⟩ := ((hlp2 c hc).and_eventually hev).exists
  have hge : c ≤ weightedAverage u (fun i => quoteSeq Y A i - (X i).expect H i) n := by
    refine le_weightedAverage_of_support hnn (fun i hi => ?_) h2
    have hθ2 : (0 : ℝ) < ((θ / 2 : ℚ) : ℝ) := by exact_mod_cast half_pos hθ
    exact hsupp i (lt_trans hθ2 (hrec.pos_imp hθ hi))
  rw [abs_lt] at h1
  linarith [h1.2]

/-- **T3 (headline, load-bearing; two-way). v3 Theorem 2 with the `H`-side bridge as a named
hypothesis.** In the hypothesis frame of `v3Theorem1_of_jointLegible` (`pkg`, `hcode`, `hworldA`,
`hworldH`, `hval`, rationals `t`, `ε > 0`, `δ > 0`), with the **schedule-free** violation weight
`viol_n = Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t) · Ind_δ(𝔼^H_n(X_n) < t − ε)` legible on both markets
(`hjoint`, v3's (A1)/(A4) carrier) and T4's conclusion for `H` (`hbridge`):
`viol_n → 0` on all days. Where each input enters (v3 §3's bookkeeping): T1 makes the firing
weighting `u_θ` of `viol` legal on `A` and on `H`; `quote_unbiased` (schedule-free) is the `A`
side; `hbridge` on the `H`-copy, one-position by T2 (`FireRec.onePosition`), plus the mesh term
`weightedApprox_bundle_realized` is the `H` side; `FireRec.pos_imp` orients the support
(`viol_n > θ/2 > 0`, so `a_n > t`, `h_n < t − ε` by `dsWeight_pos_imp`, K4/K7); the squeeze
`ε ≤ u-average of (a − h)` against the limit point `0` forces `∑ u_θ < ∞`; T2
(`FireRec.eventually_lt_of_summable`) gives `∀ᶠ n, viol_n < θ`, and
`tendsto_zero_of_eventually_lt_rat` finishes. **Discharges `fa-forcing-trader`'s `hch`**
(`ChasingSchedule`, the e.c.-level gap (A4) named): no chasing hypothesis appears.
Scope: **two-way** (partial: over the OPEN pair — `li-coupled-pair`'s `twoWayPair_exists`, and
K3: no two-market inhabitant of `hjoint` is known, `fa-forcing-trader` T11). Family: e.c. family
`X` (`MachineThresholdCodeSeq`). Lookahead: any `DeferralFunction f` (v3: `2^n`). Threshold: per
rational `(t, ε, δ)`; content region `0 < ε < t < 1` (for `t − ε ≤ 0` the lower ramp is empty on
`h ∈ [0,1]`, `viol ≡ 0`, and the conclusion is trivial). Grade: limit point on the `A` side
(`quote_unbiased`) / full limit on the `H` side; the conclusion is a full limit of the weight.
(A4): expressibility proved in T1; exploitation via T4 (OPEN, listed; here the hypothesis
`hbridge`). No `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Source: [[fa-positive-results-corrected-v3]] §4 Theorem 2 (imported-chats copy, K7); root-fa-020, root-fa-021; lean-deference-043/044; root-fa-2-003 ("(A4) is the whole distance between Theorem 1 and the box"); [[fa-adaptive-joint-mandate]] § T3
Kind: C
Fidelity: variant: joint legibility of the real sequence `viol` on each market's own `PGenerableWeighting` class (`hjoint`) in place of v3's joint clearing (K1); the `H`-side bridge taken as the named hypothesis `hbridge` (T4 OPEN); lookahead a general `DeferralFunction` (K3)
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hδ`, `hε`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H`, li-quote-lane); (c) `hjoint` (joint legibility, v3's (A1); no two-market inhabitant, K3); OPEN-dependent `hbridge` (T4's conclusion; its grade-(a) proof is the OPEN `adaptiveBridge`, its schedule instance is proved; not (b): no published theorem states it — v3's own proof does not supply it, F1). -/
theorem v3Theorem2_of_bridge {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε)
    (hjoint : LegibleOn A (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) ∧
      LegibleOn H (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ))
    (hbridge : AdaptiveBridgeHolds H f X) :
    Tendsto (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) atTop (𝓝 0) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  refine v3Theorem2_gate_of_bridge pkg hcode hworldA hworldH hval
    (g := viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)
    (fun n => ⟨dsWeight_nonneg _ _ _ _ _, dsWeight_le_one _ _ _ _ _⟩)
    (c := (ε : ℝ)) hεR (fun n hn => ?_) hjoint hbridge
  have hvi_pos : 0 < dsWeight (t : ℝ) (ε : ℝ) δ (quoteSeq Y A n) ((X n).expect H n) := hn
  obtain ⟨hta, hht⟩ := dsWeight_pos_imp hδ hvi_pos
  linarith

/-- **T3, the statement of record (two-way; rests on the OPEN T4). v3 Theorem 2: the violation
weight tends to `0` on all days**, from FAF's criterion on both sides, joint legibility of the
violation weight, and the adaptive trader of (A4): `v3Theorem2_of_bridge` with `hbridge`
discharged by `adaptiveBridge` (OPEN). Listed in `fa-adaptive-joint-open.txt` as resting on it.
Scope, family, lookahead, threshold, grade, (A4): as `v3Theorem2_of_bridge`.
Source: [[fa-positive-results-corrected-v3]] §4 Theorem 2; root-fa-005 (the box, recovered under (c) joint legibility and (A4) proved / T4); [[fa-adaptive-joint-mandate]] § T3
Kind: C
Fidelity: as `v3Theorem2_of_bridge`
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hδ`, `hε`; (c) `pkg.reflected`; (c) `hjoint`; rests on OPEN `adaptiveBridge`. -/
theorem v3Theorem2_of_jointLegible {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε)
    (hjoint : LegibleOn A (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) ∧
      LegibleOn H (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)) :
    Tendsto (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) atTop (𝓝 0) :=
  v3Theorem2_of_bridge pkg hcode hworldA hworldH hval t ε hδ hε hjoint
    (adaptiveBridge hcode hworldH f)

/-- `A`'s quote is `[0,1]`-valued (FAF's `LUV.expect_mem_Icc` on `A`'s prices).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem quoteSeq_mem_Icc {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (Y : ℕ → LUV) (n : ℕ) : quoteSeq Y A n ∈ Set.Icc (0 : ℝ) 1 :=
  LUV.expect_mem_Icc A n (Y n) (fun s => IsLogicalInductor.price_mem_Icc (DP := DPA) n s)

/-- **v3 Corollary 2 (two-way), with the bridge as a hypothesis: `H`'s credence dominates `A`'s
quote** — `∀ c > 0, ∀ᶠ n, a_n − c < h_n` — from Theorem 2 at every rational triple
(`tendsto_viol_iff_dominates`, li-asymp-calc's compactness; `a ∈ [0,1]` by `quoteSeq_mem_Icc`).
Joint legibility is needed at every rational `(t, ε, δ)` with `ε, δ > 0` (`hjointAll`).
Scope: two-way (partial: over the OPEN pair). Threshold: all rational triples at once.
Source: [[fa-positive-results-corrected-v3]] §5 Corollary 2; root-fa-021; lean-deference-044; root-fa-014 (compactness)
Kind: C
Fidelity: exact (given Theorem 2)
Hyps: (a) as T3; (c) `pkg.reflected`; (c) `hjointAll`; `hbridge` as T3. -/
theorem v3Corollary2_dominates_of_bridge {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (hjointAll : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
      LegibleOn A (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) ∧
        LegibleOn H (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ))
    (hbridge : AdaptiveBridgeHolds H f X) :
    Dominates (fun n => (X n).expect H n) (quoteSeq Y A) :=
  (tendsto_viol_iff_dominates (fun n => quoteSeq_mem_Icc (DPA := DPA) Y n)).1
    (fun t ε δ hε hδ =>
      v3Theorem2_of_bridge pkg hcode hworldA hworldH hval t ε hδ hε (hjointAll t ε δ hε hδ) hbridge)

/-- **v3 Corollary 2, statement of record (two-way; rests on the OPEN T4).**
Source: [[fa-positive-results-corrected-v3]] §5 Corollary 2
Kind: C
Fidelity: as `v3Corollary2_dominates_of_bridge`
Hyps: (c) `pkg.reflected`; (c) `hjointAll`; rests on OPEN `adaptiveBridge`. -/
theorem v3Corollary2_dominates {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (hjointAll : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
      LegibleOn A (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) ∧
        LegibleOn H (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)) :
    Dominates (fun n => (X n).expect H n) (quoteSeq Y A) :=
  v3Corollary2_dominates_of_bridge pkg hcode hworldA hworldH hval hjointAll
    (adaptiveBridge hcode hworldH f)

/-- **v3 Corollary 3 (two-way), with the bridge as a hypothesis — stronger than v3 states: every
rational-parameter violation weight is eventually `0`** (hence summable, `v3Corollary3_summable_of_bridge`).
Corollary 2 at `c = ε` gives `a_n − ε < h_n` eventually, which empties the lower ramp — finite
*support*, not merely a finite sum (findings F4: v3's Cor 3 understates its own Cor 2).
Scope: two-way (partial: over the OPEN pair). Threshold: per rational triple, under `hjointAll`.
Source: [[fa-positive-results-corrected-v3]] §5 Corollary 3; [[fa-adaptive-joint-mandate]] § T3 (F4)
Kind: C
Fidelity: stronger: eventually zero, where v3 claims `∑ w_n < ∞`
Hyps: (a) `hε`, `hδ`, and T3's; (c) `pkg.reflected`; (c) `hjointAll`; `hbridge` as T3. -/
theorem v3Corollary3_eventually_zero_of_bridge {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (hjointAll : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
      LegibleOn A (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) ∧
        LegibleOn H (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ))
    (hbridge : AdaptiveBridgeHolds H f X) (t : ℚ) {ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ n = 0 :=
  (v3Corollary2_dominates_of_bridge pkg hcode hworldA hworldH hval hjointAll
    hbridge).viol_eventually_zero t hε hδ

/-- **v3 Corollary 3 as stated (summability), with the bridge as a hypothesis.**
Source: [[fa-positive-results-corrected-v3]] §5 Corollary 3 ("`∑_n w_n < ∞`")
Kind: C
Fidelity: exact
Hyps: as `v3Corollary3_eventually_zero_of_bridge`. -/
theorem v3Corollary3_summable_of_bridge {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (hjointAll : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
      LegibleOn A (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) ∧
        LegibleOn H (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ))
    (hbridge : AdaptiveBridgeHolds H f X) (t : ℚ) {ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    Summable (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) :=
  (v3Corollary2_dominates_of_bridge pkg hcode hworldA hworldH hval hjointAll
    hbridge).summable_viol t hε hδ

/-- **v3 Corollary 3, statement of record (eventually-zero form; rests on the OPEN T4).**
Source: [[fa-positive-results-corrected-v3]] §5 Corollary 3; findings F4
Kind: C
Fidelity: stronger: eventually zero
Hyps: (c) `pkg.reflected`; (c) `hjointAll`; rests on OPEN `adaptiveBridge`. -/
theorem v3Corollary3_eventually_zero {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (hjointAll : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
      LegibleOn A (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) ∧
        LegibleOn H (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ))
    (t : ℚ) {ε δ : ℚ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ n = 0 :=
  v3Corollary3_eventually_zero_of_bridge pkg hcode hworldA hworldH hval hjointAll
    (adaptiveBridge hcode hworldH f) t hε hδ

end Cleanroom.Fa.FaAdaptiveJoint
