import Cleanroom.Fa.FaDelayBsi.DeckTT
import Cleanroom.Li.LiDiagonal.Forcing

/-!
# `fa-delay-bsi` · Anticipated (T8, T10's Lean item, E2): trusting the future AI

* **T8, positive** (`anticipated_deference`): for a fixed `X`, `H`'s current expectation of
  `A`'s *future* quote `⌜𝔼^A_{g(n)}(⌜𝔼^H_{g'(g n)}(X)⌝)⌝` is asymptotically `H`'s current credence
  `𝔼^H_n(X)` — two-sided and pointwise, stronger than the source's "on average and one-sidedly".
  Route: Theorem A's common limit (`theoremA_common_limit`: `𝔼^H_n(X) → L` and the quote
  `→ L`), so the future quote, read at `g n → ∞`, tends to `L`, and expectation provability
  induction on the determined family `Q` (`expect_tendsto_of_determinedVia_tendsto`) gives
  `𝔼^H_n(Q_n) → L`. **No `cee`, no three averages on common weightings**: the source's bookkeeping
  is avoided because, for a fixed `X`, everything converges to one number.
* **T8, negative** (`future_quote_pinned`, `forcingA_future`): the time-agnostic diagonal —
  `li-diagonal`'s `defDiag_future_price` restated with the delay reading, and `forcingA`
  reindexed along any deferral (the cross-process form, `partial: over the OPEN pair`).
* **T10's Lean item** (`realized_violation_frequently_pair`): over the diagonal pair, what the
  built pieces kill is the **horizon-side** (realized-credence, v3-format) violation weight at
  `(t, ε, δ) = (3/8, 1/16, 1/16)`: it equals `1` infinitely often. This is *not* a kill of deck-TT
  (whose left side is `H`'s *day-`n`* credence); see the findings.
* **E2** (`gate_closes_of_realized_tendsto_zero`): on a generable day-set where the realized
  credence `→ 0`, the quote `→ 0` (`lemmaP`) and the upper gate is eventually `0` — the
  composition vq-wiki-060 (c) describes.
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaTheoremA
open Cleanroom.Li.LiDiagonal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Propositional
open Filter Topology

/-! ## A. T8, positive: anticipated deference -/

/-- **T8 (headline). Anticipated deference, two-sided and pointwise.** Fix `X`. With Theorem A's
package (`H` over `DPH`, `A` over `DPA`, `pkg : CrossQuotePackage H DPA g (fun _ => X) Y` — `A`
reads `H`) and an anticipated-quote package (`Q n` determined in `H`'s theory at `A`'s day-`g n`
quote — `H` reads `A`'s *future* quote): `𝔼^H_n(Q_n) ≈ₙ 𝔼^H_n(X)`. The human's expectation of
the future quote is its own current credence, up to `o(1)`, pointwise. Proof: Theorem A's
common limit `L` (`theoremA_common_limit`); the future quote `quoteSeq Y A (g n) → L` along the
deferral; expectation provability induction at the convergent determined value gives
`𝔼^H_n(Q_n) → L`; `𝔼^H_n(X) → L`.
Scope: **two-way** (`partial: over the OPEN pair`): `pkg.reflected` is "A reads H" (c);
`hQ.reflected` is "H reads A's future quote" (c); fixed `X`. The same-market instance (`A = H`,
`Q` the `cee` quote of `H`'s own future expectation) is FAF's `thm:cee` itself — N−, not dressed up.
Source: FA-critique msg 43 line 3040 (lean-deference-056: "the human's expectation of any future quote is, on average and one-sidedly, at most its current credence plus `o(1)`"); [[fa-delay-bsi-mandate]] T8
Kind: C
Fidelity: stronger at fixed `X`: two-sided, pointwise (source: one-sided, on average); the source's averaged chain ("three averages on common weightings", Corollary 2, `cee`) is the route that generalizes to a *fresh* family `X_n`, which is not formalized here (F8; audit r1 fidelity non-blocking 4)
Hyps: (a) `hcode`, `hworldH`, `hworldA` (FAF's boundaries); (c) per FAF `hval` (`thm:ec`); (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H`; `li-coupled-pair`); (c) `hQ.reflected` (H's theory determines A's future quote) -/
theorem anticipated_deference {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPH.D n))
    (hval : ∀ w : PCWorld, w.ConsistentWithTheory DPH → ∃ x : ℝ, w.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPA.D n))
    {g : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA g (fun _ => X) Y)
    {Q : ℕ → LUV} (hQ : AnticipatedQuote H DPH Y A g Q) :
    (fun n => (Q n).expect H n) ≈ₙ fun n => X.expect H n := by
  obtain ⟨L, hL, ha⟩ := theoremA_common_limit (A := A) X hcode hworldH hval hworldA pkg
  have hfut : Tendsto (fun n => quoteSeq Y A (g.f n)) atTop (𝓝 L) := ha.comp g.tendsto_atTop
  have hQlim := expect_tendsto_of_determinedVia_tendsto H DPH Q hQ.quote_codes _ hQ.reflected L
    hfut hworldH
  exact asympEq_of_tendsto hQlim hL

/-- **T8, the source's one-sided form** as a corollary: `𝔼^H_n(Q_n) ≲ₙ 𝔼^H_n(X)` (the human's
expectation of the future quote is at most its current credence plus `o(1)`).
Scope: as `anticipated_deference`.
Source: FA-critique msg 43 line 3040 (lean-deference-056)
Kind: L
Fidelity: exact to the source's inequality, pointwise instead of on average
Hyps: as `anticipated_deference` -/
theorem anticipated_deference_le {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (X : LUV) (hcode : X.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPH.D n))
    (hval : ∀ w : PCWorld, w.ConsistentWithTheory DPH → ∃ x : ℝ, w.ValuesAt X x)
    {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    (hworldA : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPA.D n))
    {g : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA g (fun _ => X) Y)
    {Q : ℕ → LUV} (hQ : AnticipatedQuote H DPH Y A g Q) :
    (fun n => (Q n).expect H n) ≲ₙ fun n => X.expect H n :=
  (anticipated_deference X hcode hworldH hval hworldA pkg hQ).asympLE

/-! ## B. T8, negative: the time-agnostic diagonal -/

section Deferred

variable {DP : DeductiveProcess} {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]
  (Q : QuotationTheoryPresentation DP T) (P : History) [IsLogicalInductor P DP]
  (market : MarketComputation P) (p : ℚ) (f : DeferralFunction)

include Q

/-- **T8, negative (single market): the future quote about a self-referential target is pinned.**
A sentence arranged true iff the market's *future* (day-`f n`) price of it is below `p` has that
future price `→ p`: `li-diagonal`'s `defDiag_future_price`, restated with the delay reading.
Trust in the future self is average, one-sided and content-free on such targets — the
reflective ceiling transfers across time. (The source says "at most `½`"; FAF's Kleene diagonal
is parameterized by `p`, and `½` is the instance.)
Scope: single market; threshold `p`, deferral `f`; `defDiag` of FAF's Kleene diagonal.
Source: FA-critique msg 43 line 3042 (lean-deference-057: "a sentence arranged to be true iff the future AI's quote about it is at most `½` pins that future quote at `½`"); `Cleanroom.Li.LiDiagonal.defDiag_future_price`
Kind: L
Fidelity: exact (restatement; `½` is the instance `p = ½`)
Hyps: (a) none -/
theorem future_quote_pinned (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P (f n) (defDiag (kleeneDiag T market p) f n)) ≈ₙ fun _ => (p : ℝ) :=
  defDiag_future_price Q P market p f hp0 hp1 hworld

end Deferred

/-- **T8, negative (cross-process), `partial: over the OPEN pair`:** over `li-diagonal`'s diagonal
pair, `A`'s published quote read along any deferral `g` is pinned at `½`: `forcingA` composed
with `g` (`a_{g n} → ½` because `a_n → ½`). **What the family is:** `li-diagonal`'s diagonal
`gDiag` is *present*-referencing — true iff `A`'s day-`n` quote is `≤ ½` (`DiagonalPair.quoted_eq`);
the source's "a sentence arranged to be true iff the *future* AI's quote about it is at most `½`"
(msg 43) is a cross-process diagonal referencing the quote at a future day, which is **not built
here** (the single-market future-referencing diagonal is `future_quote_pinned`, exact). So this
is the reindexing the mandate asked for, not the source's object (audit r1 fidelity non-blocking 1).
Scope: **two-way** (`partial: over the OPEN pair`); threshold `½`, deferral `f`; `gDiag` over the ledger, present-referencing.
Source: FA-critique msg 43 line 3042 (lean-deference-057); `Cleanroom.Li.LiDiagonal.forcingA`
Kind: L
Fidelity: variant: as `forcingA` (price of the median threshold), reindexed along `g`; the family references the present quote, not the future one
Hyps: (c) `D.cross.reflected`; (c) `htrack` via `li-diagonal`'s `lemmaB_expect_quarter` under its certificates `hR`/`hR'`/`hG` (no inhabitant of `hR`/`hR'` exhibited there) -/
theorem forcingA_future {f : DeferralFunction} (D : DiagonalPair f)
    (htrack : ∀ᶠ n in atTop, |D.eH n - side (D.pair.a 0) n| < 1 / 4) (g : DeferralFunction) :
    (fun n => D.pair.A (g.f n) (D.pair.quoted 0 (g.f n))) ≈ₙ fun _ => (1 / 2 : ℝ) := by
  have h := forcingA D htrack
  unfold AsympEq at h ⊢
  exact h.comp g.tendsto_atTop

/-! ## C. T10's Lean item: what the diagonal pair kills -/

/-- Over the diagonal pair, the settled side is `0` infinitely often: otherwise the constant
weighting's average of `s_n − ½` would tend to `½`, against `theoremC_i`'s limit point at `0`.
Scope: **two-way** (`partial: over the OPEN pair`).
Source: `Cleanroom.Li.LiDiagonal.theoremC_i` at the constant weighting
Kind: L
Fidelity: n/a
Hyps: (c) `D.cross.reflected`; (c) `htrack` via `li-diagonal`'s `lemmaB_expect_quarter` certificates `hR`/`hR'`/`hG` (no inhabitant exhibited) -/
theorem side_zero_frequently {f : DeferralFunction} (D : DiagonalPair f)
    (htrack : ∀ᶠ n in atTop, |D.eH n - side (D.pair.a 0) n| < 1 / 4) :
    ∃ᶠ n in atTop, side (D.pair.a 0) n = 0 := by
  haveI := D.pair.A_inductor
  have hone : ∀ i : ℕ, (EF.const (1 : ℚ)).denote D.pair.A = 1 := fun _ => by simp
  have hpre : Tendsto (prefixSum fun _ : ℕ => (EF.const (1 : ℚ)).denote D.pair.A) atTop atTop :=
    tendsto_prefixSum_atTop_of_frequently_one (fun i => by rw [hone i]; exact zero_le_one)
      (Filter.Eventually.of_forall fun i => by rw [hone i]).frequently
  have hdiv : DivergentWeighting (fun _ => EF.const 1) D.pair.A :=
    ⟨fun n => by rw [hone n]; exact ⟨zero_le_one, le_rfl⟩, hpre⟩
  have hlp := theoremC_i D htrack (fun _ => EF.const 1) (pgenerableWeighting_const 1) hdiv
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hside : ∀ᶠ n in atTop, side (D.pair.a 0) n - 1 / 2 = 1 / 2 := by
    filter_upwards [hcon] with n hn
    rcases side_eq_zero_or_one (D.pair.a 0) n with h | h
    · exact absurd h hn
    · rw [h]; norm_num
  have htend : Tendsto (weightedAverage (fun _ : ℕ => (EF.const (1 : ℚ)).denote D.pair.A)
      (fun n => side (D.pair.a 0) n - 1 / 2)) atTop (𝓝 (1 / 2)) :=
    weightedAverage_tendsto (fun i => by rw [hone i]; exact zero_le_one) hpre
      (tendsto_const_nhds.congr' (hside.mono fun n hn => hn.symm))
  have hfreq := (hasLimitPoint_zero_iff.1 hlp) (1 / 4) (by norm_num)
  have hev := (Metric.tendsto_nhds.1 htend) (1 / 4) (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev).exists
  rw [Real.dist_eq, abs_lt] at hn2
  rw [abs_lt] at hn1
  linarith [hn1.2, hn2.1]

/-- **T10 (Lean item). What the diagonal pair kills is the horizon-side violation weight.** Over
`li-diagonal`'s diagonal pair, with `htrack`, the FA-format weight with the *realized* (day-`f n`)
credence, `Ind_δ(a_n > t) · Ind_δ(𝔼^H_{f(n)}(𝟙 g_n) < t − ε)` at `(t, ε, δ) = (3/8, 1/16, 1/16)`,
equals `1` infinitely often: the published quote `a_n → ½ > 7/16` saturates the quote ramp, and on
the infinitely many days with `s_n = 0` the realized credence is below `¼`. So the v3-format
(horizon) Total Trust family fails on the diagonal — `li-diagonal`'s two faces in violation-weight
form. **This is not a kill of deck-TT**: deck-TT's left side is `H`'s *day-`n`* credence in
`g_n`, which the built pieces do not pin (findings, T10).
Scope: **two-way** (`partial: over the OPEN pair`); threshold `½`, deferral `f`; `gDiag` over the ledger.
Source: [[delay-program]] §5 line 199 (root-fa-035: the "already dead" claim, examined); `Cleanroom.Li.LiDiagonal.two_faces_pair`, `forcingA_table`, `theoremC_i`
Kind: C
Fidelity: variant: the horizon-side (realized) weight, not the deck's day-`n` object; price of the median threshold as `forcingA`
Hyps: (c) `D.cross.reflected`; (c) `htrack` via `li-diagonal`'s `lemmaB_expect_quarter` certificates `hR`/`hR'`/`hG` (no inhabitant exhibited) (as `forcingA`) -/
theorem realized_violation_frequently_pair {f : DeferralFunction} (D : DiagonalPair f)
    (htrack : ∀ᶠ n in atTop, |D.eH n - side (D.pair.a 0) n| < 1 / 4) :
    ∃ᶠ n in atTop, violWeight (3 / 8) (1 / 16) (1 / 16) (D.pair.a 0 n) (D.eH n) = 1 := by
  have ha := forcingA_table D htrack
  unfold AsympEq at ha
  have hev : ∀ᶠ n in atTop, (7 / 16 : ℝ) ≤ (D.pair.a 0 n : ℝ) := by
    filter_upwards [(Metric.tendsto_nhds.1 ha) (1 / 16) (by norm_num)] with n hn
    rw [Real.dist_eq, _root_.sub_zero, abs_lt] at hn
    linarith [hn.1]
  refine ((side_zero_frequently D htrack).and_eventually (hev.and htrack)).mono ?_
  rintro n ⟨hs, ha', ht⟩
  rw [hs, _root_.sub_zero, abs_lt] at ht
  refine (violWeight_eq_one_iff (by norm_num) _ _ _ _).2 ⟨?_, ?_⟩
  · push_cast; linarith
  · push_cast; linarith [ht.2]

/-- The horizon-side violation weight over the diagonal pair does not tend to `0` (hence is not
summable and the realized side is not dominated by the quote).
Scope: **two-way** (`partial: over the OPEN pair`).
Source: as `realized_violation_frequently_pair`
Kind: L
Fidelity: as `realized_violation_frequently_pair`
Hyps: as `realized_violation_frequently_pair` -/
theorem not_tendsto_realized_viol_pair {f : DeferralFunction} (D : DiagonalPair f)
    (htrack : ∀ᶠ n in atTop, |D.eH n - side (D.pair.a 0) n| < 1 / 4) :
    ¬ Tendsto (viol D.eH (fun n => (D.pair.a 0 n : ℝ)) (3 / 8) (1 / 16) (1 / 16)) atTop
      (𝓝 0) := by
  intro h
  have hfreq := realized_violation_frequently_pair D htrack
  have hev := (Metric.tendsto_nhds.1 h) (1 / 2) (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev).exists
  rw [← violWeight_eq_viol, hn1, Real.dist_eq] at hn2
  norm_num at hn2

/-! ## D. E2: Theorem N's refutation composed from built pieces -/

/-- **E2. On a generable day-set where the realized credence vanishes, the quote vanishes and the
upper gate closes.** For a generable `{0,1}` day-set `E` of `A`'s market along which
`Y_n = 𝔼^H_{f n}(X_n) → 0` (what `li-diagonal`'s Lemma F supplies on each `E_k` with `k` false),
`fa-theorem-a`'s Lemma P gives `a_n → 0` along `E`, so for every threshold `t > 0` the gate
`Ind_δ(a_n > t)` is eventually `0` on `E` — vq-wiki-060 (c)'s sentence "on each `E_k` … `Y_n → 0`
by Lemma F, hence `a_n → 0` by Lemma P, and the gate closes".
Scope: one-way (`pkg.reflected`; `A` reads `H`); the along-`E` hypothesis is Lemma F's output, taken as the antecedent. **Half the composition:** `li-diagonal`'s `gated_forcing` concludes a weighted *price*-level statement on `H`'s market at day `n`, not `realized H f X → 0` along a `{0,1}` day-set of `A`'s market; the bridge (`thm:ei`, the reindexing, the filter conversion) is not built, so this is the `lemmaP` half with Lemma F's output assumed in a shape `gated_forcing` does not yet deliver (audit r1 adversarial non-blocking 2).
Source: [[vq-wiki-inventory]] 060 (c); [[route-negative-introspective]] §7 Corollary; `li-diagonal` T6d ("owned elsewhere")
Kind: L
Fidelity: variant: the `lemmaP` half of vq-wiki-060 (c)'s sentence; the `Y_n → 0 along E` antecedent is Lemma F's conclusion in a shape not yet delivered by `gated_forcing`
Hyps: (a) `hworldA`, `hE`, `hE01`, `ht`, `hδ`; (c) `pkg.reflected`; `hY` assumed (Lemma F's output, bridge not built) -/
theorem gate_closes_of_realized_tendsto_zero {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {E : ℕ → EF} (hE : PGenerableWeighting E)
    (hE01 : ∀ n, (E n).denote A = 0 ∨ (E n).denote A = 1)
    (hY : Tendsto (realized H f X) (atTop ⊓ 𝓟 {n | (E n).denote A = 1}) (𝓝 0))
    {t δ : ℚ} (ht : 0 < t) (hδ : 0 < δ) :
    ∀ᶠ n in atTop ⊓ 𝓟 {n | (E n).denote A = 1}, (quoteRampAbove Y t δ n).denote A = 0 := by
  have h := lemmaP pkg hworldA hE hE01 hY
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  filter_upwards [h.eventually (Iio_mem_nhds htR)] with n hn
  rw [quoteRampAbove_denote Y hδ]
  exact (ctsInd_eq_zero_iff hδ _ _).2 (le_of_lt hn)

end Cleanroom.Fa.FaDelayBsi
