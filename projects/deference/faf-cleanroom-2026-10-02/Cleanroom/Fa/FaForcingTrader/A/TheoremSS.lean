import Cleanroom.Fa.FaForcingTrader.A.Bridge
import Cleanroom.Fa.FaForcingTrader.A.Mesh
import Cleanroom.Fa.FaTheoremA.Half1

/-!
# `fa-forcing-trader` · angle A · TheoremSS: Theorem SS at limit-point grade (T6) and scheduled soft Total Trust (T7)

**T6.** On the scheduled quote gate `w_n = 1[n ∈ im d] · Ind_δ(a_n > t)`, the gate-weighted
average of `a_n − 𝔼^H_n(X_n)` has limit point `0`: fa-theorem-a's `quote_unbiased` (FAF's
`recurringunbiasednessexp` on the `A`-native gate — a limit point) plus T4 (the `H`-side bridge
on the *same numbers*, legible on `H` by (L) — a full limit) plus T5 (the mesh term — a full
limit); a limit point plus two full limits is a limit point. Stated first for an arbitrary
`A`-generable gate `G` supported on the schedule and legible on `H`
(`theoremSS_limitPoint_general`), then at the upper and lower quote gates.

**T7.** `SchedThresholdAbove w h t` — "for every `ρ > 0`, frequently the `w`-average of `h` is
`≥ t − ρ`" — and its mirror; the unnormalized form; the theorem that T6 yields it as a
*conclusion* on the gate's support (no false positives); the per-day ⟹ averaged bridge (the
converse fails: T8). Names carry `Sched`; nothing here is called Total Trust (plan §0.4 rule 10).

**Grades.** T4/T5 (a); the (c)s of every two-market headline are `pkg.reflected` (Σ₁-completeness
of `Γ_A` about `H`, li-quote-lane) and `hL : LegibleOn H (quoteSeq Y A)` (the corpus's (L), no
two-market inhabitant known, T11). Fidelity `weaker: limit point` against the note's two-sided
full limit (angle B's T6′). The Tower form (L4) is a corollary *under* a readability hypothesis
(`theoremSS_tower_of_readable`), as the note states it: [[theorem-ss-streamlined]] §5 gives L4
"under (L)" and consumes it; the phrase "L4 is free" is the mandate's (T6 trap (iii)), not the
note's (li-quote-lane F2; corrected in repair round 1, audit r1 fidelity B1).
-/

namespace Cleanroom.Fa.FaForcingTrader.A

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader
  Filter Topology

/-! ## A. Limit-point arithmetic -/

/-- A limit point `0` plus a full limit `0` is a limit point `0`.
Source: none: infrastructure (mandate T6: "a limit point plus two full limits is a limit point")
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem hasLimitPoint_zero_of_add_tendsto {u v s : ℕ → ℝ} (hu : HasLimitPoint u 0)
    (hv : Tendsto v atTop (𝓝 0)) (hs : ∀ n, s n = u n + v n) : HasLimitPoint s 0 := by
  rw [hasLimitPoint_zero_iff] at hu ⊢
  intro ε hε
  have hv' := (Metric.tendsto_nhds.1 hv) (ε / 2) (half_pos hε)
  refine ((hu (ε / 2) (half_pos hε)).and_eventually hv').mono (fun n hn => ?_)
  obtain ⟨h1, h2⟩ := hn
  rw [Real.dist_eq, sub_zero] at h2
  rw [hs n]
  calc |u n + v n| ≤ |u n| + |v n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

/-- Three-term split of a weighted bias: `a − h = (a − Y) + ((p − h) − (p − Y))`, averaged.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem weightedAverage_three (w a Y p h : ℕ → ℝ) (n : ℕ) :
    weightedAverage w (fun i => a i - h i) n =
      weightedAverage w (fun i => a i - Y i) n +
        (weightedAverage w (fun i => p i - h i) n - weightedAverage w (fun i => p i - Y i) n) := by
  unfold weightedAverage
  split_ifs with h0
  · ring
  · rw [← sub_div, ← add_div]
    congr 1
    simp only [prefixSum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Two-term split: `x − z = (x − y) + (y − z)`, averaged.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem weightedAverage_split (w x y z : ℕ → ℝ) (n : ℕ) :
    weightedAverage w (fun i => x i - z i) n =
      weightedAverage w (fun i => x i - y i) n + weightedAverage w (fun i => y i - z i) n := by
  unfold weightedAverage
  split_ifs with h0
  · ring
  · rw [← add_div]
    congr 1
    simp only [prefixSum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)

/-! ## B. T6: Theorem SS, limit-point grade -/

/-- **T6, general gate. Theorem SS at limit-point grade for any `A`-generable gate supported on
the schedule and legible on `H`.** For inductors `A` over `DPA` and `H` over `DPH`, a quote
package `pkg` tying `⌜Y_n⌝` to `𝔼^H_{f n}(X_n)`, a window-disjoint schedule `d` for `f`, and a
`PGenerableWeighting G` of `A`'s market with `(G n).denote A ≠ 0 → n ∈ im d`, whose real values
`(G n).denote A` are also a legal feature progression of `H`'s market (`hL`) and which is divergent
in `A`'s prices: `0` is a limit point of the `G`-weighted average of
`𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) − 𝔼^H_n(X_n)`.
Scope: one-way (`H` reads `A`'s quote only through `hL`; `A` never reads `H`'s prices). e.d.
family `X`. Schedule: window-disjoint `DeferralFunction`. Grade: limit point.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Proof: `quote_unbiased` (limit point of `a_n − Y_n` on `G`), T4 on the `H`-legible copy of the
same numbers (full limit of `price_{f n}(bundle_n) − 𝔼^H_n(X_n)`), T5 (full limit of
`price_{f n}(bundle_n) − Y_n`), and `weightedAverage_three`.
Source: vq-wiki-050 (Theorem SS, agreement form); lean-deference-038; [[theorem-ss-streamlined]] §0, §6
Kind: C
Fidelity: weaker: limit point, not the note's two-sided full limit (angle B's T6′)
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hwd`, `hG`, `hsupp`, `hdiv`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H` — li-quote-lane); (c) `hL` (the corpus's (L) for this gate; no two-market inhabitant known, T11). -/
theorem theoremSS_limitPoint_general {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d)
    {G : ℕ → EF} (hG : PGenerableWeighting G)
    (hsupp : ∀ n, (G n).denote A ≠ 0 → ∃ k, d.f k = n)
    (hL : LegibleOn H (fun n => (G n).denote A))
    (hdiv : DivergentWeighting G A) :
    HasLimitPoint (weightedBias (fun n => (G n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n)) 0 := by
  have h1 : HasLimitPoint (weightedBias (fun n => (G n).denote A) (quoteSeq Y A)
      (realized H f X)) 0 := quote_unbiased pkg hworldA hG hdiv
  obtain ⟨GH, hGH, hGHw⟩ := hL
  have hfun : (fun n => (GH n).denote H) = (fun n => (G n).denote A) := funext hGHw
  have hdivH : DivergentWeighting GH H := by
    refine ⟨fun n => by rw [hGHw]; exact hdiv.1 n, ?_⟩
    rw [hfun]
    exact hdiv.2
  have hsuppH : ∀ n, (GH n).denote H ≠ 0 → ∃ k, d.f k = n :=
    fun n hn => hsupp n (by rwa [hGHw] at hn)
  have h2 : Tendsto (weightedAverage (fun n => (G n).denote A)
      (fun i => (bundle X i).price H (f.f i) - (X i).expect H i)) atTop (𝓝 0) := by
    have := hSideBridge hcode hworldH hwd hGH hsuppH hdivH
    rw [hfun] at this
    exact this
  have h3 : Tendsto (weightedAverage (fun n => (G n).denote A)
      (fun i => (bundle X i).price H (f.f i) - realized H f X i)) atTop (𝓝 0) :=
    weightedApprox_bundle_realized hcode hworldH hval f (fun i => (hdiv.1 i).1) hdiv.2
  have hv := h2.sub h3
  rw [sub_zero] at hv
  exact hasLimitPoint_zero_of_add_tendsto h1 hv (fun n =>
    weightedAverage_three (fun n => (G n).denote A) (quoteSeq Y A) (realized H f X)
      (fun i => (bundle X i).price H (f.f i)) (fun n => (X n).expect H n) n)

/-- The scheduled upper gate's real values are legible on `H` under (L).
Source: [[theorem-ss-streamlined]] §0 ("ledger-lookup for `H` under (L)")
Kind: L
Fidelity: exact
Hyps: (c) `hL` (the corpus's (L)) -/
theorem legibleOn_schedGate {H A : History} {Y : ℕ → LUV} (hL : LegibleOn H (quoteSeq Y A))
    (d : DeferralFunction) (t : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    LegibleOn H (fun n => (schedGate Y d t δ n).denote A) :=
  ((LegibleOn.schedInd d H).mul (hL.rampAbove t hδ)).congr
    (fun n => (schedGate_denote Y d t hδ A n).symm)

/-- The scheduled lower gate's real values are legible on `H` under (L).
Source: [[theorem-ss-streamlined]] §8
Kind: L
Fidelity: exact
Hyps: (c) `hL` -/
theorem legibleOn_schedGateBelow {H A : History} {Y : ℕ → LUV} (hL : LegibleOn H (quoteSeq Y A))
    (d : DeferralFunction) (t : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    LegibleOn H (fun n => (schedGateBelow Y d t δ n).denote A) :=
  ((LegibleOn.schedInd d H).mul (hL.rampBelow t hδ)).congr
    (fun n => (schedGateBelow_denote Y d t hδ A n).symm)

/-- **T6 (headline). Theorem SS, one-way, limit-point grade, on the scheduled quote gate.** For
inductors `A`, `H`, a quote package, a window-disjoint schedule `d`, rationals `t`, `δ > 0`, the
corpus's (L) for the quote (`hL`), and the gate `w_n = 1[n ∈ im d] · Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t)`
divergent in `A`'s prices: `0` is a limit point of
`(∑_{i≤n} w_i (𝔼^A_i(⌜𝔼^H_{f i}(X_i)⌝) − 𝔼^H_i(X_i))) / ∑_{i≤n} w_i`.
Scope: one-way (`H` reads `A`'s quote through the ledger under (L); `A` never reads `H`'s prices).
e.d. family `X` (the note's actual statement). Schedule: window-disjoint `DeferralFunction`.
Grade: limit point.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
Junk width: at `δ = 0` the gate is identically `0` (Lean's `1/0 = 0` inside `ctsInd`), `hdiv` is
unsatisfiable and the statement vacuous (fa-theorem-a's `not_divergent_zero_width`); the headline
takes `0 < δ`. `hdiv` is a hypothesis about `A`'s realized prices; under `hL` the same real
sequence is divergent on `H` (`theoremSS_limitPoint_general` proves the transfer, it is not assumed
twice).
Source: vq-wiki-050 (Theorem SS, agreement form); lean-deference-038; [[theorem-ss-streamlined]] §0, §6; [[route-sparse-schedule]] §8
Kind: C
Fidelity: weaker: limit point, not the note's two-sided full limit
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hwd`, `hδ`, `hdiv`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H` — li-quote-lane); (c) `hL : LegibleOn H (quoteSeq Y A)` (the corpus's (L); no two-market inhabitant known, T11). -/
theorem theoremSS_limitPoint {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGate Y d t δ) A) :
    HasLimitPoint (weightedBias (fun n => (schedGate Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n)) 0 :=
  theoremSS_limitPoint_general pkg hcode hworldA hworldH hval hwd
    (schedGate_pgenerable Y pkg.quote_codes d t δ) (schedGate_supported Y d t δ A)
    (legibleOn_schedGate hL d t hδ) hdiv

/-- **T6, mirror.** Theorem SS on the scheduled lower gate `1[n ∈ im d] · Ind_δ(a_n < t)` — a
genuinely separate application (averaged statements are relative to their weighting).
Scope: one-way. e.d. family. Grade: limit point.
Source: [[theorem-ss-streamlined]] §8 ("the mirror ramp — a genuinely separate application")
Kind: C
Fidelity: weaker: limit point
Hyps: as `theoremSS_limitPoint`: (c) `pkg.reflected`; (c) `hL`. -/
theorem theoremSS_limitPoint_below {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A) :
    HasLimitPoint (weightedBias (fun n => (schedGateBelow Y d t δ n).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n)) 0 :=
  theoremSS_limitPoint_general pkg hcode hworldA hworldH hval hwd
    (schedGateBelow_pgenerable Y pkg.quote_codes d t δ) (schedGateBelow_supported Y d t δ A)
    (legibleOn_schedGateBelow hL d t hδ) hdiv

/-- **T6b, the Tower form as a corollary of a readability input.** If some `H`-LUV family `Q`
(the ledger atom naming `A`'s quote) has `𝔼^H_n(Q_n) ≈ₙ a_n` — li-quote-lane's `readability`
supplies exactly this when the quote is published as a `PGenerableRat` table — then the Tower
form `𝔼^H_i(⌜a_i⌝) − 𝔼^H_i(X_i)` averaged on `w` also has limit point `0`, by the donor rule.
Readability costs (L) (li-quote-lane F2) — as [[theorem-ss-streamlined]] §5 itself states
("under (L)"); the mandate's "the corpus's 'L4 is free'" misread the note (repair round 1) —
which is why this is stated as a corollary with the readability input named, not derived.
Scope: one-way. Grade: limit point.
Source: [[theorem-ss-streamlined]] §5 (L4), §6; vq-wiki-051 (owned by li-quote-lane); lean-deference-038 (Tower form)
Kind: L
Fidelity: exact relative to the note's L4 step (the Tower form from the agreement form)
Hyps: (a) `hw`, `hdiv`, `hlp`; (c)/(b) `hread` (readability of the published quote on `H`: li-quote-lane's `readability` under its `hL : PGenerableRat`). -/
theorem theoremSS_tower_of_readable {w a h q : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hlp : HasLimitPoint (weightedBias w a h) 0)
    (hread : q ≈ₙ a) : HasLimitPoint (weightedBias w q h) 0 := by
  have hv : Tendsto (weightedAverage w (fun i => q i - a i)) atTop (𝓝 0) :=
    weightedAverage_tendsto_zero hw hdiv hread
  refine hasLimitPoint_zero_of_add_tendsto hlp hv (fun n => ?_)
  show weightedAverage w (fun i => q i - h i) n =
    weightedAverage w (fun i => a i - h i) n + weightedAverage w (fun i => q i - a i) n
  rw [weightedAverage_split w q a h n]
  ring

/-! ## C. T7: scheduled soft Total Trust as a conclusion -/

/-- **The scheduled, averaged above-threshold inequality**: for every `ρ > 0`, frequently the
`w`-weighted average of `h` through day `n` is at least `t − ρ`. This is `def-lattice`'s
`ThresholdIneqAbove` with three changes, each named here and in the ledger: the weight is a real
gate on the quote (not a `WeightQuote` LUV pair), the inequality is *averaged along `w`* (not
per-day `≳ₙ`), and it holds *frequently* (limit-point grade; angle B's full limit upgrades to
eventually, `schedThresholdAbove_eventually_of_fullLimit`). "Total Trust" is deliberately absent
from the name.
Source: [[theorem-ss-streamlined]] §8 ("Soft Total Trust, both one-sided inequalities, scheduled and averaged"); lean-deference-039; root-deference-050 ("liminf ≥ t − ε − δ")
Kind: D
Fidelity: variant: averaged along the gate, scheduled, frequently — not def-lattice's per-day `ThresholdIneqAbove`
Hyps: n/a -/
def SchedThresholdAbove (w h : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ᶠ n in atTop, t - ρ ≤ weightedAverage w h n

/-- **The scheduled, averaged below-threshold inequality.**
Source: [[theorem-ss-streamlined]] §8
Kind: D
Fidelity: variant: averaged, scheduled, frequently
Hyps: n/a -/
def SchedThresholdBelow (w h : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ᶠ n in atTop, weightedAverage w h n ≤ t + ρ

/-- The unnormalized form `(t − ρ) · ∑_{i≤n} w_i ≤ ∑_{i≤n} w_i h_i` (no division).
Source: mandate T7 ("the unnormalized form is better: no division")
Kind: D
Fidelity: variant: unnormalized
Hyps: n/a -/
def SchedThresholdAboveUnnorm (w h : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∃ᶠ n in atTop, (t - ρ) * prefixSum w n ≤ prefixSum (fun i => w i * h i) n

/-- On a divergent weighting the normalized and unnormalized forms coincide.
Source: mandate T7
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedThresholdAbove_iff_unnorm {w h : ℕ → ℝ} {t : ℝ}
    (hdiv : Tendsto (prefixSum w) atTop atTop) :
    SchedThresholdAbove w h t ↔ SchedThresholdAboveUnnorm w h t := by
  have hev : ∀ᶠ n in atTop, 0 < prefixSum w n := hdiv.eventually (eventually_gt_atTop 0)
  constructor
  · intro H ρ hρ
    refine ((H ρ hρ).and_eventually hev).mono (fun n hn => ?_)
    obtain ⟨h1, h2⟩ := hn
    rwa [weightedAverage_eq_div h2.ne', le_div_iff₀ h2] at h1
  · intro H ρ hρ
    refine ((H ρ hρ).and_eventually hev).mono (fun n hn => ?_)
    obtain ⟨h1, h2⟩ := hn
    rwa [weightedAverage_eq_div h2.ne', le_div_iff₀ h2]

/-- **From a limit point of the bias to the above-threshold inequality**: if `0` is a limit point
of the `w`-weighted average of `a − h` and `a ≥ t` wherever `w > 0`, then
`SchedThresholdAbove w h t`.
Source: [[theorem-ss-streamlined]] §8 ("On `w̄`'s support the ramp has no false positives … the `w`-weighted average of `𝔼^H_i(X_i)` is `≥ t − o(1)`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedThresholdAbove_of_limitPoint {w a h : ℕ → ℝ} {t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hsupp : ∀ i, 0 < w i → t ≤ a i)
    (hlp : HasLimitPoint (weightedBias w a h) 0) : SchedThresholdAbove w h t := by
  intro ρ hρ
  have hev : ∀ᶠ n in atTop, 0 < prefixSum w n := hdiv.eventually (eventually_gt_atTop 0)
  rw [hasLimitPoint_zero_iff] at hlp
  refine ((hlp ρ hρ).and_eventually hev).mono (fun n hn => ?_)
  obtain ⟨h1, h2⟩ := hn
  have hge : t ≤ weightedAverage w a n := le_weightedAverage_of_support hw hsupp h2
  have hsub : weightedBias w a h n = weightedAverage w a n - weightedAverage w h n :=
    weightedAverage_sub w a h h2.ne'
  rw [hsub, abs_lt] at h1
  linarith [h1.2]

/-- **The mirror**: `a ≤ t` on the support gives `SchedThresholdBelow w h t`.
Source: [[theorem-ss-streamlined]] §8
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedThresholdBelow_of_limitPoint {w a h : ℕ → ℝ} {t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hsupp : ∀ i, 0 < w i → a i ≤ t)
    (hlp : HasLimitPoint (weightedBias w a h) 0) : SchedThresholdBelow w h t := by
  intro ρ hρ
  have hev : ∀ᶠ n in atTop, 0 < prefixSum w n := hdiv.eventually (eventually_gt_atTop 0)
  rw [hasLimitPoint_zero_iff] at hlp
  refine ((hlp ρ hρ).and_eventually hev).mono (fun n hn => ?_)
  obtain ⟨h1, h2⟩ := hn
  have hle : weightedAverage w a n ≤ t := weightedAverage_le_of_support hw hsupp h2
  have hsub : weightedBias w a h n = weightedAverage w a n - weightedAverage w h n :=
    weightedAverage_sub w a h h2.ne'
  rw [hsub, abs_lt] at h1
  linarith [h1.1]

/-- **T7 (headline). Scheduled soft Total Trust, above-threshold inequality, as a conclusion.**
Under T6's hypotheses: for every `ρ > 0`, frequently
`(∑_{i≤n} w_i 𝔼^H_i(X_i)) / ∑_{i≤n} w_i ≥ t − ρ` on the gate
`w_i = 1[i ∈ im d] · Ind_δ(𝔼^A_i(⌜𝔼^H_{f i}(X_i)⌝) > t)` — the human's present credence, averaged
over the scheduled days on which the forecaster quotes above `t`, is at least `t` up to `o(1)`.
The forcing is in the conclusion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`, no per-day hypothesis.
Scope: one-way. e.d. family. Schedule: window-disjoint `DeferralFunction`. Grade: limit point
(frequently); angle B's full limit upgrades to eventually.
Source: [[theorem-ss-streamlined]] §8; lean-deference-039 (`total_trust_above_ramp`, with its `hbias`/`hbdd` discharged); [[route-sparse-schedule]] §8; root-deference-050's "liminf ≥ t − ε − δ"
Kind: C
Fidelity: variant: averaged along the gate, scheduled, frequently (not def-lattice's per-day `ThresholdIneqAbove`; T8 shows the per-day form is not implied)
Hyps: as `theoremSS_limitPoint`: (c) `pkg.reflected`; (c) `hL`. -/
theorem schedThresholdAbove_of_theoremSS {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGate Y d t δ) A) :
    SchedThresholdAbove (fun n => (schedGate Y d t δ n).denote A) (fun n => (X n).expect H n) t :=
  schedThresholdAbove_of_limitPoint (fun i => (schedGate_mem_Icc Y d t hδ A i).1) hdiv.2
    (fun i hi => ((schedGate_pos_iff Y d t hδ A i).1 hi).2.le)
    (theoremSS_limitPoint pkg hcode hworldA hworldH hval hwd t hδ hL hdiv)

/-- **T7, mirror. Scheduled soft Total Trust, below-threshold inequality**, on the lower gate.
Scope: one-way. Grade: limit point.
Source: [[theorem-ss-streamlined]] §8 ("The below-threshold inequality re-runs everything with the mirror ramp")
Kind: C
Fidelity: variant: averaged, scheduled, frequently
Hyps: (c) `pkg.reflected`; (c) `hL`. -/
theorem schedThresholdBelow_of_theoremSS {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hL : LegibleOn H (quoteSeq Y A)) (hdiv : DivergentWeighting (schedGateBelow Y d t δ) A) :
    SchedThresholdBelow (fun n => (schedGateBelow Y d t δ n).denote A)
      (fun n => (X n).expect H n) t :=
  schedThresholdBelow_of_limitPoint (fun i => (schedGateBelow_mem_Icc Y d t hδ A i).1) hdiv.2
    (fun i hi => ((schedGateBelow_pos_iff Y d t hδ A i).1 hi).2.le)
    (theoremSS_limitPoint_below pkg hcode hworldA hworldH hval hwd t hδ hL hdiv)

/-- **A full limit turns "frequently" into "eventually"** (angle B's T7′ from its T6′;
lean-deference-039's `total_trust_above_ramp` shape).
Source: lean-deference-039; mandate T7 (`schedThreshold_eventually_of_fullLimit`)
Kind: L
Fidelity: exact
Hyps: (a) none (`hfull` is the full-limit input, angle B's) -/
theorem schedThresholdAbove_eventually_of_fullLimit {w a h : ℕ → ℝ} {t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (hsupp : ∀ i, 0 < w i → t ≤ a i)
    (hfull : WeightedApprox w a h) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ n in atTop, t - ρ ≤ weightedAverage w h n := by
  intro ρ hρ
  have hev : ∀ᶠ n in atTop, 0 < prefixSum w n := hdiv.eventually (eventually_gt_atTop 0)
  have hfull' : Tendsto (weightedAverage w (fun i => a i - h i)) atTop (𝓝 0) := hfull
  have hsm := (Metric.tendsto_nhds.1 hfull') ρ hρ
  filter_upwards [hev, hsm] with n h2 h1
  have hge : t ≤ weightedAverage w a n := le_weightedAverage_of_support hw hsupp h2
  rw [Real.dist_eq, sub_zero, weightedAverage_sub w a h h2.ne', abs_lt] at h1
  linarith [h1.2]

/-- **The per-day ⟹ averaged bridge**: if eventually, on the support of `w`, `h ≥ t − ρ`
*per day* (the shape of def-lattice's per-day `ThresholdIneqAbove` at the gate, in real-sequence
form), then `SchedThresholdAbove w h t`. The converse fails (T8: `averaged_not_perDay`). This is
the precise relation between the scheduled averaged statement and the per-day lattice notion:
strictly weaker, in this direction only.
Source: mandate T7 (`schedThreshold_vs_thresholdIneqAbove`); [[theorem-ss-streamlined]] §8
Kind: L
Fidelity: variant: real-sequence form of the per-day notion on the gate's support
Hyps: (a) none -/
theorem schedThresholdAbove_of_perDay {w h : ℕ → ℝ} {t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop)
    (hpd : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop, 0 < w i → t - ρ ≤ h i) :
    SchedThresholdAbove w h t := by
  intro ρ hρ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hpd (ρ / 2) (half_pos hρ))
  let r : ℕ → ℝ := fun i => if 0 < w i then max 0 ((t - ρ / 2) - h i) else 0
  have hr0 : ∀ i, N ≤ i → r i = 0 := fun i hi => by
    simp only [r]
    split_ifs with hwi
    · have := hN i hi hwi
      exact max_eq_left (by linarith)
    · rfl
  have hrt := weightedAverage_tendsto_zero_of_eventually_zero hw hdiv hr0
  have hev : ∀ᶠ n in atTop, 0 < prefixSum w n := hdiv.eventually (eventually_gt_atTop 0)
  have hsmall := (Metric.tendsto_nhds.1 hrt) (ρ / 2) (half_pos hρ)
  refine Eventually.frequently ((hev.and hsmall).mono (fun n hn => ?_))
  obtain ⟨hpos, hlt⟩ := hn
  rw [Real.dist_eq, sub_zero] at hlt
  have hpt : ∀ i, w i * (t - ρ / 2) - w i * r i ≤ w i * h i := fun i => by
    simp only [r]
    split_ifs with hwi
    · have := mul_le_mul_of_nonneg_left (le_max_right 0 ((t - ρ / 2) - h i)) (hw i)
      linarith
    · have hw0 : w i = 0 := le_antisymm (not_lt.1 hwi) (hw i)
      simp [hw0]
  have hsum : (t - ρ / 2) * prefixSum w n - prefixSum (fun i => w i * r i) n ≤
      prefixSum (fun i => w i * h i) n := by
    simp only [prefixSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ => by have := hpt i; linarith)
  rw [weightedAverage_eq_div hpos.ne', le_div_iff₀ hpos]
  rw [weightedAverage_eq_div hpos.ne', abs_lt, div_lt_iff₀ hpos] at hlt
  linarith [hlt.2, hsum]

/-! ## D. T12 (a): gating closure over FAF is `PGenerableWeighting.mul` -/

/-- **T12 (a). Gated Theorem SS**: for any further `A`-generable gate `c` whose values are also
legible on `H`, Theorem SS holds on the product gate `G · c` — over FAF the "class closed under
gates" of trust-lab-045/047 is just `PGenerableWeighting.mul` and `LegibleOn.mul`, so this is one
instantiation of `theoremSS_limitPoint_general`, nothing more.
Scope: one-way. Grade: limit point.
Source: trust-lab-045, trust-lab-047 (the closure theorem); mandate T12 (a)
Kind: L
Fidelity: exact (one instantiation)
Hyps: (c) `pkg.reflected`; (c) `hL`, `hLc` (legibility of both factors on `H`). -/
theorem gated_theoremSS {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d)
    {G c : ℕ → EF} (hG : PGenerableWeighting G) (hc : PGenerableWeighting c)
    (hsupp : ∀ n, (G n).denote A ≠ 0 → ∃ k, d.f k = n)
    (hL : LegibleOn H (fun n => (G n).denote A)) (hLc : LegibleOn H (fun n => (c n).denote A))
    (hdiv : DivergentWeighting (fun n => EF.mul (G n) (c n)) A) :
    HasLimitPoint (weightedBias (fun n => (EF.mul (G n) (c n)).denote A) (quoteSeq Y A)
      (fun n => (X n).expect H n)) 0 :=
  theoremSS_limitPoint_general pkg hcode hworldA hworldH hval hwd (hG.mul hc)
    (fun n hn => hsupp n (by
      rw [EF.denote_mul, Pi.mul_apply] at hn
      exact left_ne_zero_of_mul hn))
    ((hL.mul hLc).congr (fun n => by rw [EF.denote_mul, Pi.mul_apply])) hdiv

end Cleanroom.Fa.FaForcingTrader.A
