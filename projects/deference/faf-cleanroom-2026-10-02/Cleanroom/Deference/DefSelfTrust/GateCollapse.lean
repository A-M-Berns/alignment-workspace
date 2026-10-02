import Cleanroom.Deference.DefSelfTrust.FeatComb
import Cleanroom.Deference.DefSelfTrust.Est

/-!
# `def-self-trust` — target 5: Lemma B (gate-knowledge collapse), Prop 3.1, the T1 identity

vq-wiki-062 ([[route-transitivity]] §3): when the truster can *read* the gate — the gate is a
P-generable rational `c_n` of `H`'s own day-`n` prices — soft conditioning buys nothing:

* **Lemma B** (`gateKnowledge_weight`, `gateKnowledge_product`): `E_n(⌜c_n⌝) ≈ₙ c_n` and
  `E_n(⌜X_n c_n⌝) ≈ₙ c_n · E_n(X_n)` — `thm:expprovind` on the bets `⌜c_n⌝ − c_n` and
  `c_n · X_n − ⌜X_n c_n⌝` with the *feature* `c_n` as a coefficient (`FeatComb.lean`), the
  product within its vanishing slack (tail trick);
* **Prop 3.1** (`softTT_readable_iff_dominance`): soft Total Trust at the readable gate
  `û_n := Ind_δ(c_n > t)` is **equivalent** to the per-day dominance
  `Ind_δ(c_n > t) · (E_n(X_n) − t) ≳ₙ 0` — Lemma B on both sides. `st`'s gate is a *future*
  price, unknown at day `n`, which is why `est` (target 2) has content and this does not;
* **T1** (vq-wiki-053; `gatedTower_loe_route`, `gatedTower_ccee_route`, `gatedTower_routes_agree`):
  the gated tower identity at a day-`n` generable gate `u_n`,
  `E_n(⌜X_n u_n⌝) ≈ₙ u_n E_n(X_n) ≈ₙ u_n E_n(⌜E_{f(n)}(X_n)⌝) ≈ₙ E_n(⌜Y_n u_n⌝)` — Lemma B twice
  around `cee`; and the same identity through `ccee` at the pulled-back weight
  (`pullbackWeight f u`, `w (f n) = u n`); the two routes reach the same quote value, so their
  right-hand sides agree.

The gate must be a **rational** generable feature (`PGenerableRat`): `loe`-style bets need
rational coefficient values, and ramps of rational width on rational prices are rational
(`ratCtsInd`). A gate that is a fixed rational *sequence* (not a market feature) makes 5b
content-free for the self-case; the theorems are stated for `PGenerableRat P c`.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## Asymptotic plumbing -/

/-- `f ≈ₙ g` transports `≳ₙ 0` both ways.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympGE_zero_congr {f g : ℕ → ℝ} (h : f ≈ₙ g) :
    f ≳ₙ (fun _ => (0 : ℝ)) ↔ g ≳ₙ (fun _ => (0 : ℝ)) :=
  ⟨fun hf => AsympLE.trans_asympEq hf h, fun hg => AsympLE.trans_asympEq hg h.symm⟩

/-- Multiplying an `≈ₙ` pair by a `[−1, 1]`-bounded sequence preserves `≈ₙ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem asympEq_mul_left_of_bounded {u a b : ℕ → ℝ} (hu : ∀ n, |u n| ≤ 1) (h : a ≈ₙ b) :
    (fun n => u n * a n) ≈ₙ (fun n => u n * b n) := by
  have h' : Tendsto (fun n => a n - b n) atTop (𝓝 0) := h
  have habs : Tendsto (fun n => |a n - b n|) atTop (𝓝 0) := by
    have := h'.abs
    simpa using this
  show Tendsto (fun n => u n * a n - u n * b n) atTop (𝓝 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) habs
  rw [Real.norm_eq_abs, ← _root_.mul_sub, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hu n)

variable {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]

/-! ## Lemma B — gate-knowledge collapse -/

/-- **Lemma B (a):** an e.c. quote `W` valued at a P-generable `[0,1]` rational `c_n` in every
completed-theory world has `E_n(W_n) ≈ₙ c_n` — `thm:expprovind` on the exact bet `⌜c_n⌝ − c_n`
(constant `−c_n` as a feature).
Source: vq-wiki-062 (Lemma B: "`E^H_n(⌜c_n⌝) ≈_n c_n`"); FAF `lic_expect_combination_provind_eq`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem gateKnowledge_weight {c : ℕ → ℚ} (hc : PGenerableRat P c)
    (hmem : ∀ n, 0 ≤ c n ∧ c n ≤ 1) {W : ℕ → LUV} (hW : LUV.MachineThresholdCodeSeq W)
    (hWr : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → v.ValuesAt (W n) ((c n : ℚ) : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (W n).expect P n) ≈ₙ (fun n => ((c n : ℚ) : ℝ)) := by
  obtain ⟨C, hC⟩ := hc
  set c₀ : ℕ → EF := fun n => EF.mul (EF.const (-1)) (C n) with hc₀
  have hc₀gen : PGenerableWeighting c₀ := (constWeighting (-1)).mul hC.toWeighting
  set terms : List ((ℕ → EF) × (ℕ → LUV)) := [(fun _ => EF.const 1, W)] with hterms
  have S : LUVCombinationSyntax (featComb c₀ terms) :=
    featCombSyntax c₀ hc₀gen terms
      (fun p hp => by
        simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp; exact constWeighting 1)
      (fun p hp => by
        simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp; exact hW)
  have hc₀den : ∀ n, (c₀ n).denote P = -((c n : ℚ) : ℝ) := fun n => by
    simp [hc₀, EF.denote_mul, hC.denote n]
  have hbdd : ∀ n, (featComb c₀ terms n).l1Norm P ≤ 2 := fun n => by
    rw [featComb_l1Norm]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hc₀den,
      EF.denote_const]
    have := hmem n
    have h0 : (0 : ℝ) ≤ (c n : ℝ) := by exact_mod_cast this.1
    have h1 : (c n : ℝ) ≤ 1 := by exact_mod_cast this.2
    rw [abs_neg, abs_of_nonneg h0]
    norm_num
    linarith
  have hwv : LUVCombination.WorldValued (featComb c₀ terms) DP := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_featComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact valuesAt_worldValue (hWr n v hv)
  have hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∀ ν, (featComb c₀ terms n).ValuesAt v ν → (featComb c₀ terms n).value P ν = 0 := by
    intro n v hv ν hν
    have e := (hν (EF.const 1, W n) (by simp [featComb, hterms])).eq (hWr n v hv)
    rw [featComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e, hc₀den,
      EF.denote_const]
    push_cast
    ring
  have h := lic_expect_combination_provind_eq ⟨S.polySequence, ⟨2, hbdd⟩⟩ hwv 0 hval hworld
  have hE : (fun n => (featComb c₀ terms n).expect P n) =
      (fun n => (W n).expect P n - ((c n : ℚ) : ℝ)) := by
    funext n
    rw [featComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hc₀den,
      EF.denote_const]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- **Lemma B (b):** an e.c. product quote `XW` valued within a vanishing slack of `x · c_n`
(whenever `X_n` is valued at `x`) has `E_n(XW_n) ≈ₙ c_n · E_n(X_n)` — `thm:expprovind` on the
bet `c_n · X_n − ⌜X_n c_n⌝` with the feature `c_n` as coefficient, the slack handled by the
tail trick.
Source: vq-wiki-062 (Lemma B: "`E^H_n(⌜X_n c_n⌝) ≈_n c_n E^H_n(X_n)`, `loe` with coefficient
`c_n`"); FAF `lic_expect_combination_provind_{le,ge}` (the determinacy form of `thm:loe` is
blocked by the mesh slack, so the one-sided forms are used instead)
Kind: C
Fidelity: exact (conclusion); the product quote within its slack
Hyps: (a) -/
theorem gateKnowledge_product {c : ℕ → ℚ} (hc : PGenerableRat P c)
    (hmem : ∀ n, 0 ≤ c n ∧ c n ≤ 1) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (hval : Valued DP X) {XW : ℕ → LUV} (hXW : LUV.MachineThresholdCodeSeq XW) {slack : ℕ → ℝ}
    (hs : Tendsto slack atTop (𝓝 0))
    (hr : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x, v.ValuesAt (X n) x →
      ∃ z, v.ValuesAt (XW n) z ∧ |z - x * ((c n : ℚ) : ℝ)| ≤ slack n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n) ≈ₙ (fun n => ((c n : ℚ) : ℝ) * (X n).expect P n) := by
  obtain ⟨C, hC⟩ := hc
  set terms : List ((ℕ → EF) × (ℕ → LUV)) := [(C, X), (fun _ => EF.const (-1), XW)] with hterms
  have S : LUVCombinationSyntax (featComb (fun _ => EF.const 0) terms) :=
    featCombSyntax _ (constWeighting 0) terms
      (fun p hp => by
        simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hC.toWeighting
        · exact constWeighting (-1))
      (fun p hp => by
        simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hX
        · exact hXW)
  have hbdd : ∀ n, (featComb (fun _ => EF.const 0) terms n).l1Norm P ≤ 2 := fun n => by
    rw [featComb_l1Norm]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hC.denote n,
      EF.denote_const]
    have := hmem n
    have h0 : (0 : ℝ) ≤ (c n : ℝ) := by exact_mod_cast this.1
    have h1 : (c n : ℝ) ≤ 1 := by exact_mod_cast this.2
    rw [abs_of_nonneg h0]
    norm_num
    linarith
  have hwv : LUVCombination.WorldValued (featComb (fun _ => EF.const 0) terms) DP :=
    fun n v hv => by
    obtain ⟨x, hx⟩ := hval n v hv
    obtain ⟨z, hz, -⟩ := hr n v hv x hx
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_featComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact valuesAt_worldValue hx
    · exact valuesAt_worldValue hz
  have hvalb : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      ∀ ν, (featComb (fun _ => EF.const 0) terms n).ValuesAt v ν →
        |(featComb (fun _ => EF.const 0) terms n).value P ν| ≤ ε := by
    intro ε hε
    filter_upwards [hs.eventually (gt_mem_nhds hε)] with n hn v hv ν hν
    obtain ⟨x, hx⟩ := hval n v hv
    obtain ⟨z, hz, hb⟩ := hr n v hv x hx
    have e₁ := (hν (C n, X n) (by simp [featComb, hterms])).eq hx
    have e₂ := (hν (EF.const (-1), XW n) (by simp [featComb, hterms])).eq hz
    rw [featComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂,
      hC.denote n, EF.denote_const]
    push_cast
    rw [show (0 : ℝ) + ((c n : ℝ) * x + (-1 * z + 0)) = -(z - x * (c n : ℝ)) by ring, abs_neg]
    exact hb.trans hn.le
  have h := expect_asympEq_zero_of_eventually_abs_le S hbdd hwv hvalb hworld
  have hE : (fun n => (featComb (fun _ => EF.const 0) terms n).expect P n) =
      (fun n => ((c n : ℚ) : ℝ) * (X n).expect P n - (XW n).expect P n) := by
    funext n
    rw [featComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hC.denote n,
      EF.denote_const]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  have := h.neg
  simpa [neg_sub] using this

/-! ## Prop 3.1 — soft Total Trust at a readable gate is per-day dominance -/

/-- **Prop 3.1:** at the readable gate `û_n := Ind_δ(c_n > t)` (`c` P-generable in `[0,1]`),
for e.c. quotes `W` valued at `û_n` and `XW` within slack of `x · û_n`:
`E_n(XW_n) − t·E_n(W_n) ≳ₙ 0 ⟺ Ind_δ(c_n > t) · (E_n(X_n) − t) ≳ₙ 0`. Lemma B on both sides:
the left is `≈ₙ û_n (E_n(X_n) − t)`. "Soft conditioning buys nothing when the truster can read
the gate; `st`'s gate is a future price, unknown at day `n`, which is why `est` has content."
Source: vq-wiki-062 (Prop 3.1); [[route-transitivity]] §3
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem softTT_readable_iff_dominance {c : ℕ → ℚ} (hc : PGenerableRat P c)
    {δ : ℚ} (hδ : 0 < δ) (t : ℚ) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued DP X) {W XW : ℕ → LUV}
    (hW : LUV.MachineThresholdCodeSeq W) (hXW : LUV.MachineThresholdCodeSeq XW)
    (hWr : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      v.ValuesAt (W n) ((ratCtsInd δ (c n) t : ℚ) : ℝ))
    {slack : ℕ → ℝ} (hs : Tendsto slack atTop (𝓝 0))
    (hr : ∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∀ x, v.ValuesAt (X n) x →
      ∃ z, v.ValuesAt (XW n) z ∧ |z - x * ((ratCtsInd δ (c n) t : ℚ) : ℝ)| ≤ slack n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n - (t : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ)) ↔
      (fun n => ctsInd δ ((c n : ℚ) : ℝ) (t : ℝ) * ((X n).expect P n - (t : ℝ))) ≳ₙ
        (fun _ => (0 : ℝ)) := by
  have hu := pgenerableRat_ratCtsInd_left hc hδ t
  have humem : ∀ n, 0 ≤ ratCtsInd δ (c n) t ∧ ratCtsInd δ (c n) t ≤ 1 :=
    fun n => ratCtsInd_mem_Icc _ _ _
  have hA := gateKnowledge_product hu humem hX hval hXW hs hr hworld
  have hB := gateKnowledge_weight hu humem hW hWr hworld
  have hAB := hA.sub (hB.const_mul (t : ℝ))
  have hfun : (fun n => ((ratCtsInd δ (c n) t : ℚ) : ℝ) * (X n).expect P n -
      (t : ℝ) * ((ratCtsInd δ (c n) t : ℚ) : ℝ)) =
      (fun n => ctsInd δ ((c n : ℚ) : ℝ) (t : ℝ) * ((X n).expect P n - (t : ℝ))) := by
    funext n
    rw [← ratCtsInd_cast]
    ring
  rw [← hfun]
  exact asympGE_zero_congr hAB

/-! ## T1 — the gated tower identity at a day-`n` gate, two routes -/

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **T1, the `loe` route** (vq-wiki-053 §3.2): for a day-`n` P-generable `[0,1]` gate `u`, an
e.c. valued source `X`, a product quote `XU` within slack of `x · u_n` and a product quote `YU`
within slack of `E_{f(n)}(X_n) · u_n`:
`E_n(XU_n) ≈ₙ u_n E_n(X_n)`, `u_n E_n(X_n) ≈ₙ u_n E_n(⌜E_{f(n)}(X_n)⌝)`, and
`u_n E_n(⌜E_{f(n)}(X_n)⌝) ≈ₙ E_n(YU_n)` — Lemma B, `cee` (times the bounded gate), Lemma B.
Source: vq-wiki-053 ([[route-recurring-ccee]] §3.2: "via 4.8.10 (the gate is a decided rational,
factor it out), `cee`, 4.8.10 again")
Kind: C
Fidelity: exact (conclusions); products within their slacks
Hyps: (a) -/
theorem gatedTower_loe_route (f : DeferralFunction) {u : ℕ → ℚ}
    (hu : PGenerableRat (liaHistory (paperDP T)) u) (humem : ∀ n, 0 ≤ u n ∧ u n ≤ 1)
    {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X)
    {XU : ℕ → LUV} (hXU : LUV.MachineThresholdCodeSeq XU) {s₁ : ℕ → ℝ}
    (hs₁ : Tendsto s₁ atTop (𝓝 0))
    (hr₁ : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) → ∀ x, v.ValuesAt (X n) x →
      ∃ z, v.ValuesAt (XU n) z ∧ |z - x * ((u n : ℚ) : ℝ)| ≤ s₁ n)
    {YU : ℕ → LUV} (hYU : LUV.MachineThresholdCodeSeq YU) {s₂ : ℕ → ℝ}
    (hs₂ : Tendsto s₂ atTop (𝓝 0))
    (hr₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∃ z, v.ValuesAt (YU n) z ∧
        |z - (X n).expect (liaHistory (paperDP T)) (f n) * ((u n : ℚ) : ℝ)| ≤ s₂ n) :
    ((fun n => (XU n).expect (liaHistory (paperDP T)) n) ≈ₙ
        (fun n => ((u n : ℚ) : ℝ) * (X n).expect (liaHistory (paperDP T)) n)) ∧
      ((fun n => ((u n : ℚ) : ℝ) * (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
        (fun n => ((u n : ℚ) : ℝ) *
          ((paperDeferredExpectationQuoteCode T f X hX).luv n).expect (liaHistory (paperDP T)) n)) ∧
      ((fun n => ((u n : ℚ) : ℝ) *
          ((paperDeferredExpectationQuoteCode T f X hX).luv n).expect (liaHistory (paperDP T)) n) ≈ₙ
        (fun n => (YU n).expect (liaHistory (paperDP T)) n)) := by
  refine ⟨gateKnowledge_product hu humem hX hval hXU hs₁ hr₁ (paperDP_hworld T), ?_, ?_⟩
  · refine asympEq_mul_left_of_bounded (fun n => ?_)
      (lic_expected_future_expectations_closed T f X hX hval)
    have := humem n
    rw [abs_of_nonneg (by exact_mod_cast this.1)]
    exact_mod_cast this.2
  · have hQval : Valued (paperDP T) (paperDeferredExpectationQuoteCode T f X hX).luv :=
      fun n v hv => ⟨_, deferredExpectationQuote_reflected T f X hX n v hv⟩
    refine (gateKnowledge_product hu humem (paperDeferredExpectationQuoteCode T f X hX).poly
      hQval hYU hs₂ (fun n v hv x hx => ?_) (paperDP_hworld T)).symm
    obtain ⟨z, hz, hb⟩ := hr₂ n v hv
    refine ⟨z, hz, ?_⟩
    rwa [hx.eq (deferredExpectationQuote_reflected T f X hX n v hv)]

/-- **T1, the `ccee` route** (vq-wiki-053 §3.1): with the gate pulled back along an injective
`f` (`pullbackWeight f u`, so that `w (f n) = u n`), FAF's `thm:ccee` gives
`E_n(⌜X_n u_n⌝) ≈ₙ E_n(⌜E_{f(n)}(X_n) u_n⌝)` directly, at FAF's quotes — one FAF application
at the pulled-back weight (Kind L; the certificate `pullbackWeight_pgenerable` is the content).
Source: vq-wiki-053 ("supply `w_m := u_{f^{-1}(m)}` on `im f` … `ccee` gives the same identity");
mandate design decision 3
Kind: L
Fidelity: variant: product within FAF's slack; `f` injective (the "(F-INV)" legality remark
needs injectivity, finding F2)
Hyps: (a); `hinj` -/
theorem gatedTower_ccee_route (f : DeferralFunction) (hinj : Function.Injective f.f)
    {u : ℕ → ℚ} (hu : PGenerableRat (liaHistory (paperDP T)) u)
    (humem : ∀ n, 0 ≤ u n ∧ u n ≤ 1) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (hval : Valued (paperDP T) X) :
    (fun n => (meshProductLUV (paperDeferredWeightQuoteCode T f (pullbackWeight f u)
        (pullbackWeight_pgenerable f hinj hu) (pullbackWeight_mem f humem)) X n).expect
          (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => ((paperConditionalExpectationQuoteCode T f X hX (pullbackWeight f u)
        (pullbackWeight_pgenerable f hinj hu) (pullbackWeight_mem f humem)).luv n).expect
          (liaHistory (paperDP T)) n) :=
  lic_no_expected_net_update_conditional_closed T f X hX hval (pullbackWeight f u)
    (pullbackWeight_mem f humem) (pullbackWeight_pgenerable f hinj hu)

/-- **The two routes agree**: the `ccee` route's right-hand quote is valued at
`E_{f(n)}(X_n) · u_n` (since `pullbackWeight f u (f n) = u n`), so it is `≈ₙ` any `YU` of the
`loe` route, and both routes end at the same number.
Source: vq-wiki-053 (the check that "`ccee` gives the same identity")
Kind: C
Fidelity: exact
Hyps: (a); `hinj` -/
theorem gatedTower_routes_agree (f : DeferralFunction) (hinj : Function.Injective f.f)
    {u : ℕ → ℚ} (hu : PGenerableRat (liaHistory (paperDP T)) u)
    (humem : ∀ n, 0 ≤ u n ∧ u n ≤ 1) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    {YU : ℕ → LUV} (hYU : LUV.MachineThresholdCodeSeq YU) {s₂ : ℕ → ℝ}
    (hs₂ : Tendsto s₂ atTop (𝓝 0))
    (hr₂ : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∃ z, v.ValuesAt (YU n) z ∧
        |z - (X n).expect (liaHistory (paperDP T)) (f n) * ((u n : ℚ) : ℝ)| ≤ s₂ n) :
    (fun n => ((paperConditionalExpectationQuoteCode T f X hX (pullbackWeight f u)
        (pullbackWeight_pgenerable f hinj hu) (pullbackWeight_mem f humem)).luv n).expect
          (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (YU n).expect (liaHistory (paperDP T)) n) :=
  expect_asympEq_of_reflected_within
    (paperConditionalExpectationQuoteCode T f X hX _ _ _).poly hYU
    (fun n _ => (X n).expect (liaHistory (paperDP T)) (f n) * ((u n : ℚ) : ℝ))
    (s₁ := fun _ => 0) tendsto_const_nhds hs₂
    (fun n v hv => ⟨_, by
      have h := conditionalExpectationQuote_reflected T f X hX (pullbackWeight f u)
        (pullbackWeight_pgenerable f hinj hu) (pullbackWeight_mem f humem) n v hv
      rwa [pullbackWeight_at f hinj] at h, by simp⟩)
    hr₂ (paperDP_hworld T)

/-! ## Lemma B over the paper market, at FAF's own quote of a generable rational -/

/-- FAF's quote code of a P-generable `[0,1]` rational sequence over the paper market
(`RationalQuoteCode.ofComputable` at `PGenerableRat.computable`).
Source: FAF `RationalQuoteCode.ofComputable`, `PGenerableRat.computable`
Kind: D
Fidelity: exact -/
def generableQuote {c : ℕ → ℚ} (hc : PGenerableRat (liaHistory (paperDP T)) c)
    (hmem : ∀ n, 0 ≤ c n ∧ c n ≤ 1) : RationalQuoteCode T c :=
  RationalQuoteCode.ofComputable T (hc.computable (paperMarketComputation T)) hmem

/-- **Lemma B over the paper market, at FAF's quotes:** `E_n(⌜c_n⌝) ≈ₙ c_n` and
`E_n(⌜X_n c_n⌝) ≈ₙ c_n E_n(X_n)` for FAF's quote of `c` and its mesh product with `X`.
Source: vq-wiki-062 (Lemma B); FAF `RationalQuoteCode.reflected`, `meshProductLUV_valuesAt`
Kind: C
Fidelity: exact (conclusions); mesh product within FAF's slack
Hyps: (a) -/
theorem gateKnowledge_paper {c : ℕ → ℚ} (hc : PGenerableRat (liaHistory (paperDP T)) c)
    (hmem : ∀ n, 0 ≤ c n ∧ c n ≤ 1) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (hval : Valued (paperDP T) X) :
    ((fun n => ((generableQuote T hc hmem).luv n).expect (liaHistory (paperDP T)) n) ≈ₙ
        (fun n => ((c n : ℚ) : ℝ))) ∧
      ((fun n => (meshProductLUV (generableQuote T hc hmem) X n).expect
          (liaHistory (paperDP T)) n) ≈ₙ
        (fun n => ((c n : ℚ) : ℝ) * (X n).expect (liaHistory (paperDP T)) n)) :=
  ⟨gateKnowledge_weight hc hmem (generableQuote T hc hmem).poly
    (fun n v hv => RationalQuoteCode.reflected (paperQuotationPresentation T) _ n v hv)
    (paperDP_hworld T),
   gateKnowledge_product hc hmem hX hval (meshProductLUV_machineThresholdCodeSeq _ hX)
    tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n v hv _ hx => meshProductLUV_valuesAt (paperQuotationPresentation T)
      (generableQuote T hc hmem) X n v hv hx)
    (paperDP_hworld T)⟩

end

end Cleanroom.Deference.DefSelfTrust
