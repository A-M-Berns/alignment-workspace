import Cleanroom.Fa.FaDelayBsi.Defs
import Cleanroom.Fa.FaTheoremA.TheoremA
import Cleanroom.Fa.FaTheoremA.Decided
import Cleanroom.Li.LiDiagonal.Grade

/-!
# `fa-delay-bsi` · DeckTT (T5, T7): robustness of deck-TT, the factoring step, the constant-`V`
accelerator instance

* **T5** `deckTT_robust`: two reflecting pairs for the same `(expert, V, v, δ)` have asymptotically
  equal expectations (`li-diagonal`'s `expect_asympEq_of_eventually_values_close` at slack `0`), so
  `DeckTT`'s quantification over all reflecting pairs is well-posed; `asympGE_transfer` moves the
  inequality between pairs.
* **T7** the factoring step: when the gate's day-`n` value `g n` is a world-independent number
  that *converges* (which is what the fixed-`V` case supplies through Theorem A), the product LUV
  `A n` (valued at `x · g n` where `V` is valued at `x`) has `𝔼_n(A n) ≈ₙ g n · 𝔼_n(V)`
  (`factoring_of_convergent_gate`), by FAF's expectation provability induction on the
  constant-coefficient combination `A n − q·V` for rationals `q` near the limit. The
  non-convergent determined-gate form needs a varying-coefficient syntax certificate and is
  stated OPEN (`Open.lean`).
* **T7** `deckTT_const_accelerator`: for a fixed `V`, deck-TT at constant thresholds with the
  accelerator as expert, from Theorem A (`claim2`'s common limit) and the factoring. Two-way:
  `pkg.reflected` (`A` reads `H`) and the `DeckTrustQuote` fields (`H` reads the quote).
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaTheoremA
open Cleanroom.Li.LiDiagonal Cleanroom.Deference.DefSelfTrust
open Filter Topology

/-! ## A. Asymptotic plumbing -/

/-- `AsympGE` transfers along `AsympEq` on both sides.
Source: none: infrastructure (FAF `AsympLE.trans_asympEq`, `AsympEq.trans_asympLE`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem asympGE_transfer {a b a' b' : ℕ → ℝ} (h : AsympGE a b) (ha : a ≈ₙ a') (hb : b ≈ₙ b') :
    AsympGE a' b' :=
  (hb.symm.trans_asympLE h).trans_asympEq ha

/-- Two convergent sequences with ordered limits are asymptotically ordered.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem asympGE_of_tendsto_le {a b : ℕ → ℝ} {la lb : ℝ} (ha : Tendsto a atTop (𝓝 la))
    (hb : Tendsto b atTop (𝓝 lb)) (hle : lb ≤ la) : AsympGE a b := by
  intro ε hε
  have ha' := (Metric.tendsto_nhds.1 ha) (ε / 2) (by positivity)
  have hb' := (Metric.tendsto_nhds.1 hb) (ε / 2) (by positivity)
  filter_upwards [ha', hb'] with n hna hnb
  rw [Real.dist_eq, abs_sub_lt_iff] at hna hnb
  linarith [hna.1, hna.2, hnb.1, hnb.2]

/-! ## B. T5: robustness across reflecting pairs -/

/-- **T5 (headline). Deck-TT's objects do not depend on the reflecting pair.** Two pairs `(A, B)`,
`(A', B')` both satisfying `DeckTrustQuote` for the same `expert`, `V`, `v`, `δ` have
`𝔼_n(A n) ≈ₙ 𝔼_n(A' n)` and `𝔼_n(B n) ≈ₙ 𝔼_n(B' n)`: in every completed world both members are
valued at the same number (`x · gate`, resp. `gate`), so `li-diagonal`'s
`expect_asympEq_of_eventually_values_close` applies at slack `0`. This is what justifies
`DeckTT`'s quantification over all pairs.
Scope: one market (`H`'s); any expert sequence.
Source: [[fa-delay-bsi-mandate]] T5 (`deckTT_robust`); [[delay-program]] §5 (root-fa-034)
Kind: C
Fidelity: exact
Hyps: (a) `hworld` (FAF's non-vacuity boundary); the two packages' `source_valued` are (c) per FAF (`thm:ec`) -/
theorem deckTT_robust {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    {expert : ℕ → ℝ} {V : ℕ → LUV} {v δ : ℕ → ℚ} {A B A' B' : ℕ → LUV}
    (h : DeckTrustQuote H DPH expert V v δ A B) (h' : DeckTrustQuote H DPH expert V v δ A' B')
    (hworld : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPH.D n)) :
    ((fun n => (A n).expect H n) ≈ₙ fun n => (A' n).expect H n) ∧
      ((fun n => (B n).expect H n) ≈ₙ fun n => (B' n).expect H n) := by
  classical
  constructor
  · -- the product side: both valued at `x · gate`, `x` the world's value of `V n`
    let α : ℕ → PCWorld → ℝ := fun n w =>
      if hw : w.ConsistentWithTheory DPH then
        Classical.choose (h.source_valued n w hw) * ctsInd (δ n) (expert n) (v n)
      else 0
    refine expect_asympEq_of_eventually_values_close H DPH A A' h.product_codes
      h'.product_codes α α ?_ ?_ ?_ hworld
    · intro n w hw
      simp only [α, dif_pos hw]
      exact h.product_reflected n w hw _ (Classical.choose_spec (h.source_valued n w hw))
    · intro n w hw
      simp only [α, dif_pos hw]
      exact h'.product_reflected n w hw _ (Classical.choose_spec (h.source_valued n w hw))
    · intro ε hε
      exact Filter.Eventually.of_forall fun n w _ => by rw [sub_self, abs_zero]; exact hε.le
  · -- the gate side: both valued at the gate
    refine expect_asympEq_of_eventually_values_close H DPH B B' h.confidence_codes
      h'.confidence_codes (fun n _ => ctsInd (δ n) (expert n) (v n))
      (fun n _ => ctsInd (δ n) (expert n) (v n)) ?_ ?_ ?_ hworld
    · intro n w hw; exact h.confidence_reflected n w hw
    · intro n w hw; exact h'.confidence_reflected n w hw
    · intro ε hε
      exact Filter.Eventually.of_forall fun n w _ => by rw [sub_self, abs_zero]; exact hε.le

/-- **T5, corollary.** If the deck inequality holds for *one* reflecting pair at `(v, δ)`, it holds
for every reflecting pair at `(v, δ)`.
Source: [[fa-delay-bsi-mandate]] T5
Kind: L
Fidelity: exact
Hyps: (a) `hworld` -/
theorem deckTT_of_pair {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    {expert : ℕ → ℝ} {V : ℕ → LUV} {v δ : ℕ → ℚ} {A B A' B' : ℕ → LUV}
    (h : DeckTrustQuote H DPH expert V v δ A B) (h' : DeckTrustQuote H DPH expert V v δ A' B')
    (hworld : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPH.D n))
    (hge : AsympGE (fun n => (A n).expect H n) (fun n => (v n : ℝ) * (B n).expect H n)) :
    AsympGE (fun n => (A' n).expect H n) (fun n => (v n : ℝ) * (B' n).expect H n) := by
  obtain ⟨hA, hB⟩ := deckTT_robust h h' hworld
  refine asympGE_transfer hge hA ?_
  unfold AsympEq at hB ⊢
  rw [Metric.tendsto_nhds] at hB ⊢
  intro ε hε
  filter_upwards [hB ε hε] with n hn
  rw [Real.dist_eq, sub_zero] at hn ⊢
  have hv1 : |(v n : ℝ)| ≤ 1 := by
    have hm := h.threshold_mem n
    have h0 : (0 : ℝ) ≤ v n := by exact_mod_cast hm.1
    have h1 : (v n : ℝ) ≤ 1 := by exact_mod_cast hm.2
    rw [abs_le]; constructor <;> linarith
  calc |(v n : ℝ) * (B n).expect H n - (v n : ℝ) * (B' n).expect H n|
      = |(v n : ℝ)| * |(B n).expect H n - (B' n).expect H n| := by rw [← mul_sub, abs_mul]
    _ ≤ 1 * |(B n).expect H n - (B' n).expect H n| :=
        mul_le_mul_of_nonneg_right hv1 (abs_nonneg _)
    _ < ε := by rw [one_mul]; exact hn

/-! ## C. Expectation provability induction at a convergent determined value (real limit) -/

/-- **Expectation provability induction at a convergent determined value, real limit.** An e.c.
LUV family `Y`, each `Y n` determined in `DP`'s completed theory at `y n`, with `y n → L` (a real),
has `𝔼_n(Y_n) → L`. `li-diagonal`'s `expect_asympEq_of_determinedVia_tendsto` is the rational-limit
case; here the limit is approximated by rationals and the two one-sided eventual
`thm:expprovind` faces of `def-self-trust` (`expect_asympLE_of_eventually`,
`expect_asympGE_of_eventually`) are applied to `Y n − q`.
Scope: single market.
Source: none: infrastructure (LI paper `thm:expprovind`; `li-diagonal` `expect_asympEq_of_determinedVia_tendsto`)
Kind: C
Fidelity: n/a
Hyps: (a) none -/
theorem expect_tendsto_of_determinedVia_tendsto (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (y : ℕ → ℝ)
    (hdet : ∀ n, LUV.DeterminedVia (Y n) DP (y n)) (L : ℝ) (hy : Tendsto y atTop (𝓝 L))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => (Y n).expect P n) atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_rat_near L (show (0 : ℝ) < ε / 4 by positivity)
  have hev : ∀ᶠ n in atTop, |y n - q| ≤ ε / 2 := by
    filter_upwards [(Metric.tendsto_nhds.1 hy) (ε / 4) (by positivity)] with n hn
    rw [Real.dist_eq] at hn
    calc |y n - q| = |(y n - L) + (L - q)| := by ring_nf
      _ ≤ |y n - L| + |L - q| := abs_add_le _ _
      _ ≤ ε / 2 := by linarith
  have hwv := worldValued_affineImage 1 (-q) (X := Y) (DP := DP)
    (fun n v hv => ⟨y n, hdet n v hv⟩)
  have hbdd : ∀ n, (LUVCombination.affineImage 1 (-q) (Y n)).l1Norm P ≤
      |((-q : ℚ) : ℝ)| + |((1 : ℚ) : ℝ)| := fun n => (l1Norm_affineImage 1 (-q) (Y n) P).le
  have hvalue : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν, (LUVCombination.affineImage 1 (-q) (Y n)).ValuesAt v ν →
        (LUVCombination.affineImage 1 (-q) (Y n)).value P ν = y n - q := by
    filter_upwards with n v hv ν hν
    rw [affineImage_value]
    have hval : ν (Y n) = y n :=
      ((valuesAt_affineImage_iff 1 (-q) v (Y n) ν).1 hν).eq (hdet n v hv)
    rw [hval]; push_cast; ring
  have hle := expect_asympLE_of_eventually (P := P) (DP := DP) (affineImageSyntax 1 (-q) Y hY)
    hbdd hwv (c := ε / 2) (by positivity)
    (by
      filter_upwards [hev, hvalue] with n hn hv v hv' ν hν
      rw [hv v hv' ν hν]; exact (abs_le.1 hn).2) hworld
  have hge := expect_asympGE_of_eventually (P := P) (DP := DP) (affineImageSyntax 1 (-q) Y hY)
    hbdd hwv (c := -(ε / 2)) (by linarith)
    (by
      filter_upwards [hev, hvalue] with n hn hv v hv' ν hν
      rw [hv v hv' ν hν]; exact (abs_le.1 hn).1) hworld
  filter_upwards [hle (ε / 8) (by positivity), hge (ε / 8) (by positivity)] with n h1 h2
  rw [affineImage_expect] at h1 h2
  rw [Real.dist_eq]
  push_cast at h1 h2 hq
  rw [abs_lt] at hq ⊢
  constructor <;> linarith [hq.1, hq.2]

/-! ## D. T7: the factoring step at a convergent gate -/

/-- **T7 (headline). The factoring step at a convergent world-independent gate.** Let `V` be a
fixed e.c. LUV valued in every completed world, `g n ∈ [0,1]` a gate sequence with `g n → L`, and
`A n` an e.c. family valued at `x · g n` in every world valuing `V` at `x`. Then
`𝔼_n(A n) ≈ₙ g n · 𝔼_n(V)`: for rationals `q` near `L` the constant-coefficient combination
`A n − q · V` is valued at `x (g n − q)`, eventually within `ε` of `0`, so its expectation is
eventually within `ε` of `0` (`def-self-trust`'s eventual `thm:expprovind` faces), and
`|q − g n| · 𝔼_n(V)` is small. This is [[delay-program]] T7's factoring
`𝔼^H_n(V·Ind) ≳ₙ 𝔼^H_n(V)·𝔼^H_n(Ind) − o(1)` in the only form Theorem A needs: the gate is a
determined quantity of `H`'s theory (the ledger) *and* converges (fixed `V`). The non-convergent
determined-gate form is `factoring_of_determined_gate_open` (`Open.lean`).
Scope: one-way: `H`'s market, the gate's determinacy assumed through `hArefl` (the "H reads the gate" direction).
Source: [[delay-program]] §6 T7 line 264 (root-fa-033: "concluding TT needs a factoring step … which is not free"); [[fa-delay-bsi-mandate]] T7 route
Kind: C
Fidelity: weaker: the gate converges (the fixed-`V` case); the note's step is for any determined gate
Hyps: (a) `hcode`, `hworld`, `hg01`, `hg`, `hA`; (c) per FAF `hval` (`thm:ec`); `hArefl` is the reflecting-pair field (the "H reads A" direction, two-way with the quote package where it is used) -/
theorem factoring_of_convergent_gate {H : History} {DPH : DeductiveProcess}
    [IsLogicalInductor H DPH] (V : LUV) (hcode : V.MachineThresholdCodes)
    (hval : ∀ w : PCWorld, w.ConsistentWithTheory DPH → ∃ x : ℝ, w.ValuesAt V x)
    (hworld : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPH.D n))
    (g : ℕ → ℝ) {L : ℝ} (hg : Tendsto g atTop (𝓝 L))
    (A : ℕ → LUV) (hA : LUV.MachineThresholdCodeSeq A)
    (hArefl : ∀ n (w : PCWorld), w.ConsistentWithTheory DPH →
      ∀ x, w.ValuesAt V x → w.ValuesAt (A n) (x * g n)) :
    (fun n => (A n).expect H n) ≈ₙ fun n => g n * V.expect H n := by
  classical
  have hP : ∀ n s, 0 ≤ H n s ∧ H n s ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := H) (DP := DPH)
  unfold AsympEq
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_rat_near L (show (0 : ℝ) < ε / 8 by positivity)
  have hev : ∀ᶠ n in atTop, |g n - q| ≤ ε / 4 := by
    filter_upwards [(Metric.tendsto_nhds.1 hg) (ε / 8) (by positivity)] with n hn
    rw [Real.dist_eq] at hn
    calc |g n - q| = |(g n - L) + (L - q)| := by ring_nf
      _ ≤ |g n - L| + |L - q| := abs_add_le _ _
      _ ≤ ε / 4 := by linarith
  -- the combination `A n − q · V`
  set terms : List (ℚ × (ℕ → LUV)) := [((1 : ℚ), A), ((-q : ℚ), fun _ => V)] with hterms
  have hmem : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hA
    · exact machineThresholdCodeSeq_const hcode
  have hbdd : ∀ n, (constComb 0 terms n).l1Norm H ≤ 1 + |(q : ℝ)| := by
    intro n
    rw [constComb_l1Norm]
    simp [hterms]
  have hwv : LUVCombination.WorldValued (constComb 0 terms) DPH := by
    intro n w hw
    obtain ⟨x, hx⟩ := hval w hw
    refine ⟨fun X => if X = A n then x * g n else x, ?_⟩
    intro p hp
    simp only [constComb, hterms, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simp only [if_true]
      exact hArefl n w hw x hx
    · by_cases hVA : V = A n
      · simp only [hVA, if_true]
        rw [← hVA]
        have := hArefl n w hw x hx
        rw [← hVA] at this
        exact this
      · simp only [hVA, if_false]
        exact hx
  have hvalue : ∀ᶠ n in atTop, ∀ w : PCWorld, w.ConsistentWithTheory DPH →
      ∀ ν, (constComb 0 terms n).ValuesAt w ν → |(constComb 0 terms n).value H ν| ≤ ε / 4 := by
    filter_upwards [hev] with n hn w hw ν hν
    obtain ⟨x, hx⟩ := hval w hw
    have hνA : ν (A n) = x * g n := by
      have h := hν (EF.const 1, A n) (by simp [constComb, hterms])
      exact h.eq (hArefl n w hw x hx)
    have hνV : ν V = x := by
      have h := hν (EF.const (-q), V) (by simp [constComb, hterms])
      exact h.eq hx
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hνA, hνV]
    push_cast
    have hx01 : 0 ≤ x ∧ x ≤ 1 := ⟨hx.1, hx.2.1⟩
    calc |(0 : ℝ) + (1 * (x * g n) + (-(q : ℝ) * x + 0))| = |x| * |g n - q| := by
          rw [← abs_mul]; congr 1; ring
      _ ≤ 1 * |g n - q| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [abs_le]; constructor <;> linarith [hx01.1, hx01.2]
      _ ≤ ε / 4 := by rw [one_mul]; exact hn
  have hle := expect_asympLE_of_eventually (P := H) (DP := DPH) (constCombSyntax 0 terms hmem)
    hbdd hwv (c := ε / 4) (by positivity)
    (by filter_upwards [hvalue] with n hn w hw ν hν; exact (abs_le.1 (hn w hw ν hν)).2) hworld
  have hge := expect_asympGE_of_eventually (P := H) (DP := DPH) (constCombSyntax 0 terms hmem)
    hbdd hwv (c := -(ε / 4)) (by linarith)
    (by filter_upwards [hvalue] with n hn w hw ν hν; exact (abs_le.1 (hn w hw ν hν)).1) hworld
  have hEV : ∀ n, 0 ≤ V.expect H n ∧ V.expect H n ≤ 1 := fun n => LUV.expect_mem_Icc H n V (hP n)
  filter_upwards [hle (ε / 4) (by positivity), hge (ε / 4) (by positivity), hev] with n h1 h2 h3
  rw [constComb_expect] at h1 h2
  simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1 h2
  push_cast at h1 h2
  rw [Real.dist_eq, sub_zero]
  have hE := hEV n
  have hgq : |(g n - q) * V.expect H n| ≤ ε / 4 := by
    rw [abs_mul]
    calc |g n - q| * |V.expect H n| ≤ (ε / 4) * 1 := by
          apply mul_le_mul h3 _ (abs_nonneg _) (by positivity)
          rw [abs_le]; constructor <;> linarith [hE.1, hE.2]
      _ = ε / 4 := by ring
  have hsplit : (A n).expect H n - g n * V.expect H n =
      ((A n).expect H n - (q : ℝ) * V.expect H n) - (g n - q) * V.expect H n := by ring
  rw [hsplit]
  calc |((A n).expect H n - (q : ℝ) * V.expect H n) - (g n - q) * V.expect H n|
      ≤ |(A n).expect H n - (q : ℝ) * V.expect H n| + |(g n - q) * V.expect H n| :=
        abs_sub _ _
    _ < ε := by
        have hA1 : (A n).expect H n - (q : ℝ) * V.expect H n ≤ ε / 2 := by linarith
        have hA2 : -(ε / 2) ≤ (A n).expect H n - (q : ℝ) * V.expect H n := by linarith
        have : |(A n).expect H n - (q : ℝ) * V.expect H n| ≤ ε / 2 := abs_le.2 ⟨hA2, hA1⟩
        linarith

/-- The gate `ctsInd δ (a n) v` of a convergent quote converges (to the ramp of the limit).
Source: none: infrastructure (`li-asymp-calc` `continuous_ctsInd`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem tendsto_ctsInd_of_tendsto (δ : ℚ) {a : ℕ → ℝ} {L : ℝ} (ha : Tendsto a atTop (𝓝 L))
    (v : ℝ) : Tendsto (fun n => ctsInd δ (a n) v) atTop (𝓝 (ctsInd δ L v)) :=
  ((continuous_ctsInd δ).tendsto (L, v)).comp (ha.prodMk_nhds tendsto_const_nhds)

/-- **T7 (headline). Deck-TT for a constant family with the accelerator as expert.** Fix `V`.
With Theorem A's package (`H` over `DPH`, `A'` over `DPA`, `pkg : CrossQuotePackage H DPA f (fun _ => V) Y`,
FAF's boundaries), the accelerator `a_n := 𝔼^{A'}_n(⌜𝔼^H_{f n}(V)⌝)` satisfies deck-TT at every
constant threshold `v` and width `δ`: for every reflecting pair `(A, B)`,
`𝔼^H_n(V · Ind_δ(a_n > v)) ≳ₙ v · 𝔼^H_n(Ind_δ(a_n > v))`. Proof: `claim2` (via
`theoremA_common_limit`) gives `a_n → L` with `𝔼^H_n(V) → L`; the gate `w_n := Ind_δ(a_n > v)`
converges to `w := Ind_δ(L > v)`; the factoring gives `𝔼_n(A n) → w·L` and the determined gate
gives `𝔼_n(B n) → w`; and `v·w ≤ w·L` because `w > 0` forces `v < L`.
Scope: **two-way** (`partial: over the OPEN pair`): `pkg.reflected` is "A reads H"; the reflecting
pair's fields (`confidence_reflected`, `product_reflected`: the gate of the published quote is a
determined quantity of `H`'s theory) are "H reads A" — root-fa-033's "difficulty is 016 again",
discharged by the one-way ledger at the same-market instance (`SelfInstance.lean`).
Source: [[delay-program]] §6 T7 line 264 (root-fa-033); [[delay-program]] §5 (root-fa-034, the bridge)
Kind: C
Fidelity: exact for constant thresholds (`DeckTTConst`); the full generable family is not reached (the factoring needs a convergent gate)
Hyps: (a) `hcode`, `hworldH`, `hworldA` (FAF's boundaries); (c) per FAF `hval` (`thm:ec`); (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H`; `li-coupled-pair`); (c) the reflecting pair's determinacy of the gate (ledger) -/
theorem deckTT_const_accelerator {H : History} {DPH : DeductiveProcess} [IsLogicalInductor H DPH]
    (V : LUV) (hcode : V.MachineThresholdCodes)
    (hworldH : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPH.D n))
    (hval : ∀ w : PCWorld, w.ConsistentWithTheory DPH → ∃ x : ℝ, w.ValuesAt V x)
    {A' : History} {DPA : DeductiveProcess} [IsLogicalInductor A' DPA]
    (hworldA : ∀ n, ∃ w : PCWorld, w.ConsistentWith (DPA.D n))
    {f : DeferralFunction} {Y : ℕ → LUV} (pkg : CrossQuotePackage H DPA f (fun _ => V) Y) :
    DeckTTConst H DPH (accelerator Y A') (fun _ => V) := by
  intro v δ A B hq
  obtain ⟨L, hL, ha⟩ := theoremA_common_limit (A := A') V hcode hworldH hval hworldA pkg
  -- the gate converges
  have hgate : Tendsto (fun n => ctsInd δ (accelerator Y A' n) (v : ℝ)) atTop
      (𝓝 (ctsInd δ L (v : ℝ))) := tendsto_ctsInd_of_tendsto δ ha (v : ℝ)
  set w : ℝ := ctsInd δ L (v : ℝ) with hw
  -- the product side
  have hA : (fun n => (A n).expect H n) ≈ₙ
      fun n => ctsInd δ (accelerator Y A' n) (v : ℝ) * V.expect H n :=
    factoring_of_convergent_gate V hcode hval hworldH _ hgate A hq.product_codes
      (fun n w' hw' x hx => hq.product_reflected n w' hw' x hx)
  have hAlim : Tendsto (fun n => (A n).expect H n) atTop (𝓝 (w * L)) := by
    have h1 : Tendsto (fun n => ctsInd δ (accelerator Y A' n) (v : ℝ) * V.expect H n) atTop
        (𝓝 (w * L)) := hgate.mul hL
    unfold AsympEq at hA
    have := hA.add h1
    simpa using this
  -- the gate side
  have hBlim : Tendsto (fun n => (B n).expect H n) atTop (𝓝 w) :=
    expect_tendsto_of_determinedVia_tendsto H DPH B hq.confidence_codes _
      (fun n w' hw' => hq.confidence_reflected n w' hw') w hgate hworldH
  have hvBlim : Tendsto (fun n => (v : ℝ) * (B n).expect H n) atTop (𝓝 ((v : ℝ) * w)) :=
    hBlim.const_mul _
  -- ordered limits
  have hle : (v : ℝ) * w ≤ w * L := by
    rcases (ctsInd_nonneg δ L (v : ℝ)).lt_or_eq with hpos | hzero
    · have hvL : (v : ℝ) < L := (ctsInd_pos_iff (hq.delta_pos 0) _ _).1 hpos
      have := mul_lt_mul_of_pos_right hvL hpos
      linarith
    · rw [hw, ← hzero]; simp
  exact asympGE_of_tendsto_le hAlim hvBlim hle

end Cleanroom.Fa.FaDelayBsi
