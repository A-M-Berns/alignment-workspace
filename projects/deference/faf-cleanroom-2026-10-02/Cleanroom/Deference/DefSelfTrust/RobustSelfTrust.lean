import Cleanroom.Deference.DefSelfTrust.Est
import Cleanroom.Deference.DefSelfTrust.GateCollapse

/-!
# `def-self-trust` — target 6: Lemma C, Theorem B, Corollary B.1, Prop 6.3

[[route-transitivity]] §4 (vq-wiki-063), §6.1–6.2 (vq-wiki-2-008, 2-009, 2-010). Fix an e.c.
world-valued source `X`, a threshold `t ∈ [0, ∞)`, a width `δ > 0`, and an arbitrary
**computable** rational forecast `c` of `Y_n := E_{f(n)}(X_n)` — in the corpus `A`'s
ledger quote `a_n`; here any sequence the market can name (single market; the cross-market
instance is `def-squeeze-diamond`'s over `li-quote-lane`). The source restricts the forecast to
`[0,1]`; no statement below needs that (the ramp and the truncated error carry their own
`[0,1]` certificates, and `lemmaC_core` bounds only the *source's* value), so every result
holds for every computable rational `c` (repair round 2, after the round-2 fidelity audit N2).
`Computable c` is also *weaker* than the source's hypothesis — its `ā_n = E^H_n(⌜a_n⌝)` is a
market expectation, hence P-generable, and FAF's `PGenerableRat.computable` gives generable ⇒
computable, not the converse — so the Lean's Lemma C / Theorem B are more general than the
source's on that axis; the source's *per-day* form of Theorem B (`theoremB_perDay`) is the one
statement that needs `c` P-generable, because it goes through Lemma B. Quoted LUVs over
`paperDP T`:
`Û_n = ⌜Ind_δ(c_n > t)⌝`, `B_n = ⌜Ind_δ(Y_n > t)⌝` (= `est`'s `W_F`), the truncated error
`E_n = ⌜min(1, |c_n − Y_n|/δ)⌝`, and the mesh products `XÛ`, `XB`.

* **Lemma C** (`lemmaC`): `E_n(XÛ) − t·E_n(Û) ≳ₙ E_n(XB) − t·E_n(B) − (1+t)·E_n(E)` — the
  five-term bet `D_n := XÛ − t·Û − XB + t·B + (1+t)·E` is nonnegative up to the two mesh slacks
  in every completed-theory world, by the `1/δ`-Lipschitz bound `|û − β| ≤ e` (`Ramp.lean`)
  and `|x − t| ≤ 1 + t`;
* **Theorem B** (`theoremB`): with `est` at `s := t`,
  `E_n(XÛ) ≳ₙ t·E_n(Û) − (1+t)·E_n(⌜min(1, |c_n − Y_n|/δ)⌝)` — full limit, all days, no
  visibility hypothesis; the whole cross-agent deficit is the one number `E_n(⌜e_n⌝)`;
* **Corollary B.1** (`corollaryB1`): under uniform accuracy `(UA)` the residual vanishes and
  per-day soft Total Trust at `û` holds. `(UA)` is a scope condition on `c`; target 7 shows it
  excludes exactly the targets deference is about. `(UA)` is trivially satisfiable: the
  market's own deferred expectation `c_n := Y_n`, a computable forecast, satisfies it with error
  `0` (`deferredForecast_UA`), and at that forecast Corollary B.1 is `est_productForm`
  restated — the mandate's `c = Y` trap, now named as the canonical inhabitant of `(UA)`;
* **Theorem B, per-day form** (`theoremB_perDay`, repair round 2): the source's second display
  `liminf_n [û_n(E^H_n(X_n) − t) + (1+t)·E^H_n(⌜e_n⌝)] ≥ 0`, Theorem B transported by Lemma B
  (`GateCollapse.lean`); it needs `c` P-generable, which Theorem B itself does not;
* **Prop 6.3** (`prop63_witness`): Theorem B's residual is not necessary — real-sequence data
  where the bound is vacuous while the target holds.

**Inhabitants of Theorem B's package** (`Witness.lean`): at Prop 6.3's data on the parity source
(`theoremB_parity_instance`) the bound is *vacuous* (the residual is `1` eventually, the
right-hand side tends to `−1`; graded N− since repair round 2, after both round-2 audits); at
the parity-tracking forecast `c_n := 1` on even days, `0` on odd days
(`theoremB_parityForecast_instance`) the residual vanishes and the bound is positive
infinitely often (`theoremB_parityForecast_bound_bites`), but the source is decided, so
Theorem B is `provind`-implied there (N− for the content). On any decided source Theorem B
is `provind`-implied for every forecast, so no content-exercising inhabitant exists over
`paperDP T` without `li-pseudorandom` T7 — the same structural limit as for `est`.

**The dual face** (repair round 1; the source's "The dual cut holds with `Ind_δ(ā_n < t)`,
`≲`, and the same residual"): `lemmaC_below`, `theoremB_below`, `corollaryB1_below` at the
down-ramps `Ud_n = ⌜Ind_δ(c_n < t)⌝` (`forecastGateBelow`) and `B'_n = ⌜Ind_δ(Y_n < t)⌝`
(`est`'s `estWBelow`), with the same residual `E_n`: the mirror bet is
`−XUd + t·Ud + XB' − t·B' + (1+t)·E`, nonnegative up to the two mesh slacks by
`|β' − ud| ≤ e` (the ramp's `1/δ`-Lipschitz bound in its *threshold* argument,
`ctsInd_lipschitz_right_min`) and `|x − t| ≤ 1 + t`.

**`t ≥ 0`.** The source states Lemma C and Theorem B "for every rational `t`", but its own
world-value bound `W(D_n) ≥ −(1+t)|û − β| + (1+t)e` uses `|x − t| ≤ 1 + t`, which fails for
`t < 0` (there `|x − t| ≤ 1 − t` and the constant is `1 + |t|`). Both faces here carry
`ht : 0 ≤ t`; the negative-threshold case is uninteresting on `[0,1]` sources (the up-gate is
`1` for `c_n ≥ t + δ`, i.e. always for `t < −δ`). Finding F16.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-! ## The quoted objects -/

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- The market's deferred expectation of the day-`n` source member, as a computable rational
sequence (`Y_n`).
Source: FAF `MarketComputation.expectQuoteAt_computable`
Kind: L
Fidelity: n/a -/
theorem deferredExpect_computable (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) :
    Computable fun n => (paperMarketComputation T).expectQuoteAt X n (f.f n) :=
  (((paperMarketComputation T).expectQuoteAt_computable hX).comp
    (Computable.id.pair f.computable) : _)

/-- The forecast gate `Û_n = ⌜Ind_δ(c_n > t)⌝` for a computable rational forecast `c` (any
computable rational sequence; the source's `[0,1]` restriction is not needed — the ramp's
membership certificate is its own, `ratCtsInd_mem_Icc`).
Source: vq-wiki-063 (`û_n := Ind_δ(ā_n > t)`, the forecast read as a computable sequence)
Kind: D
Fidelity: variant: the corpus's `ā_n := E^H_n(⌜a_n⌝)` is `≈ₙ a_n` by Lemma B for a
market-nameable forecast; stated at `c` (finding F11); `Computable c` is weaker than the
source's P-generable `ā` -/
def forecastGate {c : ℕ → ℚ} (hc : Computable c) (δ t : ℚ) : RationalQuoteCode T
    (fun n => ratCtsInd δ (c n) t) :=
  RationalQuoteCode.ofComputable T
    ((ratCtsInd_computable.comp ((Computable.const δ).pair (hc.pair (Computable.const t)))) : _)
    (fun _ => ratCtsInd_mem_Icc _ _ _)

/-- The truncated error `E_n = ⌜min(1, |c_n − Y_n|/δ)⌝`, a single quoted LUV.
Source: vq-wiki-063 (`e_n := min(1, |ā_n − Y_n|/δ)`)
Kind: D
Fidelity: exact -/
def truncError (f : DeferralFunction) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    {c : ℕ → ℚ} (hc : Computable c) {δ : ℚ} (hδ : 0 < δ) : RationalQuoteCode T
    (fun n => min 1 (|c n - (paperMarketComputation T).expectQuoteAt X n (f.f n)| / δ)) :=
  RationalQuoteCode.ofComputable T
    ((ratMin_prim.to_comp.comp (Computable.const 1)
      (ratDiv_prim.to_comp.comp
        (ratAbs_prim.to_comp.comp (ratSub_prim.to_comp.comp hc (deferredExpect_computable T f hX)))
        (Computable.const δ))) : _)
    (fun _ => ⟨le_min zero_le_one (div_nonneg (abs_nonneg _) hδ.le), min_le_left _ _⟩)

omit [Entailment.Consistent T] in
/-- `Û_n` is valued at `Ind_δ(c_n > t)` in every completed-theory world.
Source: FAF `RationalQuoteCode.reflected`, `ratCtsInd_cast`
Kind: L
Fidelity: n/a -/
theorem forecastGate_reflected {c : ℕ → ℚ} (hc : Computable c) (δ t : ℚ) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((forecastGate T hc δ t).luv n) (ctsInd δ ((c n : ℚ) : ℝ) (t : ℝ)) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) (forecastGate T hc δ t)
    n v hv
  rwa [← ratCtsInd_cast] at h

omit [Entailment.Consistent T] in
/-- `E_n` is valued at `min 1 (|c_n − Y_n|/δ)` in every completed-theory world.
Source: FAF `RationalQuoteCode.reflected`, `expectQuoteAt_cast`
Kind: L
Fidelity: n/a -/
theorem truncError_reflected (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {c : ℕ → ℚ} (hc : Computable c) {δ : ℚ} (hδ : 0 < δ)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((truncError T f hX hc hδ).luv n)
      (min 1 (|((c n : ℚ) : ℝ) - (X n).expect (liaHistory (paperDP T)) (f n)| / (δ : ℝ))) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T) (truncError T f hX hc hδ)
    n v hv
  rwa [Rat.cast_min, Rat.cast_one, Rat.cast_div, Rat.cast_abs, Rat.cast_sub,
    ← (paperMarketComputation T).expectQuoteAt_cast X n (f.f n)] at h

omit [Entailment.Consistent T] in
/-- The mesh product `XÛ_n` is valued within `1/(n+1)` of `x · Ind_δ(c_n > t)`.
Source: FAF `meshProductLUV_valuesAt`
Kind: L
Fidelity: n/a -/
theorem forecastProduct_reflected {c : ℕ → ℚ} (hc : Computable c) (δ t : ℚ) (X : ℕ → LUV)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) {x : ℝ}
    (hx : v.ValuesAt (X n) x) :
    ∃ z, v.ValuesAt (meshProductLUV (forecastGate T hc δ t) X n) z ∧
      |z - x * ctsInd δ ((c n : ℚ) : ℝ) (t : ℝ)| ≤ 1 / ((n : ℝ) + 1) := by
  have h := meshProductLUV_valuesAt (paperQuotationPresentation T) (forecastGate T hc δ t) X n v
    hv hx
  rwa [← ratCtsInd_cast] at h

/-! ## Lemma C -/

/-- The real-arithmetic core of Lemma C: for `x ∈ [0,1]`, `t ≥ 0`,
`(x − t)(û − β) + (1 + t) e ≥ 0` whenever `|û − β| ≤ e`.
Source: vq-wiki-063 ("package as one bet `D_n ≥ 0` in every world")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem lemmaC_core {x t û β e : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (ht : 0 ≤ t) (hub : |û - β| ≤ e) :
    0 ≤ (x - t) * (û - β) + (1 + t) * e := by
  have hxt : |x - t| ≤ 1 + t := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hprod : |(x - t) * (û - β)| ≤ (1 + t) * e := by
    rw [abs_mul]
    exact mul_le_mul hxt hub (abs_nonneg _) (by linarith)
  linarith [(abs_le.1 hprod).1]

/-- **Lemma C** (the residual bound): for any computable rational forecast `c` (the source's
`[0,1]` restriction is not needed: `lemmaC_core` bounds only the source's value `x ∈ [0,1]`),
`t ≥ 0`, `δ > 0`, an injective deferral `f`, and an e.c. world-valued source `X`,
`E_n(XÛ_n) − t·E_n(Û_n) ≳ₙ E_n(XB_n) − t·E_n(B_n) − (1 + t)·E_n(E_n)`
where `B, XB` are `est`'s quotes at `s := t` and `E` the truncated error. The five-term bet
`XÛ − t·Û − XB + t·B + (1+t)·E` has world value `≥ (x − t)(û − β) + (1+t)e − 2/(n+1) ≥ −2/(n+1)`
(`lemmaC_core` with `|û − β| ≤ e` from `ctsInd_lipschitz`); the mesh slacks add a vanishing
error handled by the eventual form of `thm:expprovind`.
Source: vq-wiki-063 (Lemma C); [[route-transitivity]] §4
Kind: P
Fidelity: variant: products within FAF's mesh slack; forecast stated at `c` (finding F11)
Hyps: (a); `hinj` -/
theorem lemmaC (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {c : ℕ → ℚ}
    (hc : Computable c) {δ : ℚ} (hδ : 0 < δ) {t : ℚ} (ht : 0 ≤ t) :
    (fun n => (meshProductLUV (forecastGate T hc δ t) X n).expect (liaHistory (paperDP T)) n -
        (t : ℝ) * ((forecastGate T hc δ t).luv n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => (estXW T f hX hδ t n).expect (liaHistory (paperDP T)) n -
        (t : ℝ) * (estW T f hX hδ t n).expect (liaHistory (paperDP T)) n -
        (1 + (t : ℝ)) * ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) := by
  set Û := (forecastGate T hc δ t).luv with hÛ
  set XÛ := meshProductLUV (forecastGate T hc δ t) X with hXÛ
  set B := estW T f hX hδ t with hB
  set XB := estXW T f hX hδ t with hXB
  set E := (truncError T f hX hc hδ).luv with hE
  set terms : List (ℚ × (ℕ → LUV)) := [(1, XÛ), (-t, Û), (-1, XB), (t, B), (1 + t, E)]
    with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact meshProductLUV_machineThresholdCodeSeq _ hX
    · exact (forecastGate T hc δ t).poly
    · exact meshProductLUV_machineThresholdCodeSeq _ hX
    · exact (paperDeferredWeightQuoteCode T f _ _ _).poly
    · exact (truncError T f hX hc hδ).poly
  have hbdd : ∀ n, (constComb 0 terms n).l1Norm (liaHistory (paperDP T)) ≤ 3 + 3 * t :=
    fun n => by
    rw [constComb_l1Norm]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
    rw [abs_neg, abs_of_nonneg ht', abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)]
    norm_num
    linarith
  have hwv : LUVCombination.WorldValued (constComb 0 terms) (paperDP T) := fun n v hv => by
    obtain ⟨x, hx⟩ := hval n v hv
    obtain ⟨z₁, hz₁, -⟩ := forecastProduct_reflected T hc δ t X n v hv hx
    obtain ⟨z₂, hz₂, -⟩ := estXW_reflected T f hinj hX hδ t n v hv hx
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact valuesAt_worldValue hz₁
    · exact valuesAt_worldValue (forecastGate_reflected T hc δ t n v hv)
    · exact valuesAt_worldValue hz₂
    · exact valuesAt_worldValue (estW_reflected T f hinj hX hδ t n v hv)
    · exact valuesAt_worldValue (truncError_reflected T f hX hc hδ n v hv)
  have hvalb : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        -ε ≤ (constComb 0 terms n).value (liaHistory (paperDP T)) ν := by
    intro ε hε
    have hslack : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := this.const_mul 2
      simp only [mul_zero] at h2
      refine h2.congr (fun n => ?_)
      ring
    filter_upwards [hslack.eventually (gt_mem_nhds hε)] with n hn v hv ν hν
    obtain ⟨x, hx⟩ := hval n v hv
    obtain ⟨z₁, hz₁, hb₁⟩ := forecastProduct_reflected T hc δ t X n v hv hx
    obtain ⟨z₂, hz₂, hb₂⟩ := estXW_reflected T f hinj hX hδ t n v hv hx
    have e₁ := (hν (EF.const 1, XÛ n) (by simp [constComb, hterms])).eq hz₁
    have e₂ := (hν (EF.const (-t), Û n) (by simp [constComb, hterms])).eq
      (forecastGate_reflected T hc δ t n v hv)
    have e₃ := (hν (EF.const (-1), XB n) (by simp [constComb, hterms])).eq hz₂
    have e₄ := (hν (EF.const t, B n) (by simp [constComb, hterms])).eq
      (estW_reflected T f hinj hX hδ t n v hv)
    have e₅ := (hν (EF.const (1 + t), E n) (by simp [constComb, hterms])).eq
      (truncError_reflected T f hX hc hδ n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂, e₃, e₄,
      e₅]
    push_cast
    set y := (X n).expect (liaHistory (paperDP T)) (f n) with hy
    set û := ctsInd δ ((c n : ℚ) : ℝ) (t : ℝ) with hû
    set β := ctsInd δ y (t : ℝ) with hβ
    set e := min 1 (|((c n : ℚ) : ℝ) - y| / (δ : ℝ)) with he
    have hcore := lemmaC_core (t := (t : ℝ)) (û := û) (β := β) (e := e) ⟨hx.1, hx.2.1⟩
      (by exact_mod_cast ht) (ctsInd_lipschitz hδ _ _ _)
    have hb₁' := (abs_le.1 hb₁).1
    have hb₂' := (abs_le.1 hb₂).2
    have hn' : 2 / ((n : ℝ) + 1) < ε := hn
    have hsplit : 2 / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
    nlinarith [hcore, hb₁', hb₂', hn', hsplit]
  have hS := constCombSyntax 0 terms hcodes
  have hE : (fun n => (constComb 0 terms n).expect (liaHistory (paperDP T)) n) =
      (fun n => ((XÛ n).expect (liaHistory (paperDP T)) n -
        (t : ℝ) * (Û n).expect (liaHistory (paperDP T)) n) -
        ((XB n).expect (liaHistory (paperDP T)) n -
          (t : ℝ) * (B n).expect (liaHistory (paperDP T)) n -
          (1 + (t : ℝ)) * (E n).expect (liaHistory (paperDP T)) n)) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  intro ε hε
  have hge := expect_asympGE_of_eventually hS hbdd hwv (c := -(ε / 2)) (by linarith)
    (hvalb (ε / 2) (by positivity)) (paperDP_hworld T) (ε / 2) (by positivity)
  rw [hE] at hge
  filter_upwards [hge] with n hn
  linarith

/-! ## Theorem B and Corollary B.1 -/

/-- **Theorem B** (robust self-trust with an explicit error budget): for any computable
rational forecast `c` of `Y_n = E_{f(n)}(X_n)` (the source's `[0,1]` restriction is not
needed), `t ≥ 0`, `δ > 0`, an injective `f` and an e.c. world-valued `X`,
`E_n(⌜X_n Ind_δ(c_n > t)⌝) ≳ₙ t·E_n(⌜Ind_δ(c_n > t)⌝) − (1 + t)·E_n(⌜min(1, |c_n − Y_n|/δ)⌝)`
— full limit, all days, no visibility hypothesis, single market: Lemma C composed with `est`
at `s := t`. The whole cross-agent deficit is the one number `E_n(⌜e_n⌝)`. The source's
equivalent per-day display (`liminf_n [û_n(E_n(X_n) − t) + (1+t)E_n(⌜e_n⌝)] ≥ 0`) is
`theoremB_perDay`; it needs `c` P-generable (Lemma B), which this statement does not.
**Witnesses** (`Witness.lean`): the package is inhabited at Prop 6.3's data
(`theoremB_parity_instance`), where the bound is vacuous, and at the parity-tracking forecast
(`theoremB_parityForecast_instance`), where the bound is positive infinitely often; both are
N− for the content, because on a decided source (payout `∈ {0,1}` in every world) Theorem B
is `provind`-implied for every forecast, and a content-exercising inhabitant needs an
undecided source with a provable gate crossing — out of reach over `paperDP T` without
`li-pseudorandom` T7, exactly as for `est` (repair round 2, after the round-2 adversarial
audit B1/N4).
Source: vq-wiki-063 (Theorem B); [[route-transitivity]] §4, §10(b)
Kind: C
Fidelity: variant: products within FAF's mesh slack; forecast stated at `c` (finding F11);
stronger on the forecast axis: any computable rational `c`, where the source has a `[0,1]`
market expectation (P-generable)
Hyps: (a); `hinj` -/
theorem theoremB (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {c : ℕ → ℚ}
    (hc : Computable c) {δ : ℚ} (hδ : 0 < δ) {t : ℚ} (ht : 0 ≤ t) :
    (fun n => (meshProductLUV (forecastGate T hc δ t) X n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => (t : ℝ) * ((forecastGate T hc δ t).luv n).expect (liaHistory (paperDP T)) n -
        (1 + (t : ℝ)) * ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) := by
  have hC := lemmaC T f hinj hX hval hc hδ ht
  have hest := est_productForm T f hinj hX hval hδ t
  intro ε hε
  filter_upwards [hC (ε / 2) (by positivity), hest (ε / 2) (by positivity)] with n h1 h2
  linarith

/-- The residual vanishes under uniform accuracy: if for every `ε > 0` eventually
`|c_n − Y_n| < ε` (`(UA)`, against the deferred expectation `Y_n`), then
`E_n(⌜min(1, |c_n − Y_n|/δ)⌝) ≈ₙ 0` (the LUV's value is `< ε/δ` eventually; the expectation
is nonnegative).
Source: vq-wiki-063 (Corollary B.1: "the residual vanishes (4.2.1 on the accuracy)")
Kind: C
Fidelity: exact
Hyps: (a); `(UA)` -/
theorem truncError_expect_tendsto_zero_of_UA (f : DeferralFunction) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) {c : ℕ → ℚ} (hc : Computable c) {δ : ℚ} (hδ : 0 < δ)
    (hUA : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      |((c n : ℚ) : ℝ) - (X n).expect (liaHistory (paperDP T)) (f n)| < ε) :
    (fun n => ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun _ => (0 : ℝ)) := by
  set E := (truncError T f hX hc hδ).luv with hE
  set terms : List (ℚ × (ℕ → LUV)) := [(1, E)] with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact (truncError T f hX hc hδ).poly
  have hbdd : ∀ n, (constComb 0 terms n).l1Norm (liaHistory (paperDP T)) ≤ 1 := fun n => by
    rw [constComb_l1Norm]
    simp [hterms]
  have hwv : LUVCombination.WorldValued (constComb 0 terms) (paperDP T) := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact valuesAt_worldValue (truncError_reflected T f hX hc hδ n v hv)
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hvalb : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        |(constComb 0 terms n).value (liaHistory (paperDP T)) ν| ≤ ε := by
    intro ε hε
    filter_upwards [hUA (ε * δ) (by positivity)] with n hn v hv ν hν
    have e := (hν (EF.const 1, E n) (by simp [constComb, hterms])).eq
      (truncError_reflected T f hX hc hδ n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e]
    push_cast
    rw [zero_add, one_mul, add_zero]
    rw [abs_of_nonneg (le_min zero_le_one (div_nonneg (abs_nonneg _) hδR.le))]
    calc min 1 (|((c n : ℚ) : ℝ) - (X n).expect (liaHistory (paperDP T)) (f n)| / (δ : ℝ))
        ≤ |((c n : ℚ) : ℝ) - (X n).expect (liaHistory (paperDP T)) (f n)| / (δ : ℝ) :=
          min_le_right _ _
      _ ≤ ε * δ / δ := div_le_div_of_nonneg_right hn.le hδR.le
      _ = ε := by field_simp
  have h := expect_asympEq_zero_of_eventually_abs_le (constCombSyntax 0 terms hcodes) hbdd hwv
    hvalb (paperDP_hworld T)
  have hEq : (fun n => (constComb 0 terms n).expect (liaHistory (paperDP T)) n) =
      (fun n => (E n).expect (liaHistory (paperDP T)) n) := by
    funext n
    rw [constComb_expect]
    simp [hterms]
  rwa [hEq] at h

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- **`(UA)` is trivially satisfiable — the `c = Y` trap, named.** The market's own deferred
expectation `c_n := Y_n` (FAF's `expectQuoteAt`, a computable rational forecast by
`deferredExpect_computable`) satisfies uniform accuracy with error `0` on every day. At this
forecast the forecast gate is `est`'s own gate `B_n`, the residual is `⌜0⌝`, and Corollary B.1
is `est_productForm` restated — so `(UA)`'s hypothesis package is inhabited for every source,
but by an instance on which the corollary has no content beyond `est`. The non-trivial
inhabitants of record are in `Witness.lean` (the parity-tracking forecast on the parity source,
`parityForecast_UA`), and no content-exercising one exists over `paperDP T` (module header).
Source: mandate target 6d (the `c = Y` trap); round-2 adversarial audit N1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem deferredForecast_UA (f : DeferralFunction) (X : ℕ → LUV) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      |(((paperMarketComputation T).expectQuoteAt X n (f.f n) : ℚ) : ℝ) -
        (X n).expect (liaHistory (paperDP T)) (f n)| < ε := by
  intro ε hε
  refine Filter.Eventually.of_forall (fun n => ?_)
  rw [(paperMarketComputation T).expectQuoteAt_cast X n (f.f n), _root_.sub_self, abs_zero]
  exact hε

/-- **Corollary B.1**: under uniform accuracy `(UA)` — `∀ ε > 0, ∀ᶠ n, |c_n − Y_n| < ε` against
the deferred expectation `Y_n = E_{f(n)}(X_n)` — per-day soft Total Trust at the forecast gate
holds: `E_n(⌜X_n Ind_δ(c_n > t)⌝) − t·E_n(⌜Ind_δ(c_n > t)⌝) ≳ₙ 0`. `(UA)` is a scope condition
on the forecast, not a squeeze (Theorem B is the content); target 7 shows it fails on exactly
the pseudorandom targets deference is about (and, against the *settled* value rather than
`Y_n`, fails by `min p (1−p)` — finding F12). `(UA)` is trivially satisfiable by the market's
own deferred expectation (`deferredForecast_UA`, on which this corollary is `est_productForm`
restated); its non-trivial inhabitant of record is the parity-tracking forecast on the parity
source (`parityForecast_corollaryB1`, `Witness.lean`), N− for the content because the source
is decided. Any computable rational `c`: the `[0,1]` restriction is not needed.
Source: vq-wiki-063 (Corollary B.1)
Kind: C
Fidelity: variant: products within FAF's mesh slack
Hyps: (a); `hinj`; `(UA)` (named scope condition) -/
theorem corollaryB1 (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {c : ℕ → ℚ}
    (hc : Computable c) {δ : ℚ} (hδ : 0 < δ) {t : ℚ} (ht : 0 ≤ t)
    (hUA : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      |((c n : ℚ) : ℝ) - (X n).expect (liaHistory (paperDP T)) (f n)| < ε) :
    (fun n => (meshProductLUV (forecastGate T hc δ t) X n).expect (liaHistory (paperDP T)) n -
        (t : ℝ) * ((forecastGate T hc δ t).luv n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => (0 : ℝ)) := by
  have hB := theoremB T f hinj hX hval hc hδ ht
  have hres := truncError_expect_tendsto_zero_of_UA T f hX hc hδ hUA
  have hres' : Tendsto (fun n =>
      (1 + (t : ℝ)) * ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun n =>
        ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) atTop (𝓝 0) := by
      have := hres
      unfold AsympEq at this
      simpa using this
    simpa using h0.const_mul (1 + (t : ℝ))
  intro ε hε
  filter_upwards [hB (ε / 2) (by positivity),
    hres'.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))] with n h1 h2
  linarith

/-! ## The dual face: down-ramps -/

/-- The ramp is `1/δ`-Lipschitz in its *threshold* argument, truncated at `1` (both ramps lie in
`[0,1]`): `|ctsInd δ x t − ctsInd δ x t'| ≤ min 1 (|t − t'|/δ)` — the form Lemma C's dual face
needs for the down-ramps `Ind_δ(c_n < t) = ctsInd δ t c_n` and `Ind_δ(Y_n < t) = ctsInd δ t Y_n`.
Source: vq-wiki-063 (Lemma C, "the dual cut … the same residual"); `Ramp.lean`
`ctsInd_lipschitz_right`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ctsInd_lipschitz_right_min {δ : ℚ} (hδ : 0 < δ) (x t t' : ℝ) :
    |ctsInd δ x t - ctsInd δ x t'| ≤ min 1 (|t - t'| / (δ : ℝ)) := by
  refine le_min ?_ (ctsInd_lipschitz_right hδ x t t')
  rw [abs_le]
  constructor <;> linarith [ctsInd_nonneg δ x t, ctsInd_le_one δ x t, ctsInd_nonneg δ x t',
    ctsInd_le_one δ x t']

/-- The forecast down-gate `Ud_n = ⌜Ind_δ(c_n < t)⌝ = ⌜ctsInd δ t c_n⌝` for a computable rational
forecast `c` (no `[0,1]` restriction needed).
Source: vq-wiki-063 ("The dual cut holds with `Ind_δ(ā_n < t)`")
Kind: D
Fidelity: variant: stated at `c` (finding F11) -/
def forecastGateBelow {c : ℕ → ℚ} (hc : Computable c) (δ t : ℚ) : RationalQuoteCode T
    (fun n => ratCtsInd δ t (c n)) :=
  RationalQuoteCode.ofComputable T
    ((ratCtsInd_computable.comp ((Computable.const δ).pair ((Computable.const t).pair hc))) : _)
    (fun _ => ratCtsInd_mem_Icc _ _ _)

omit [Entailment.Consistent T] in
/-- `Ud_n` is valued at `Ind_δ(c_n < t)` in every completed-theory world.
Source: FAF `RationalQuoteCode.reflected`, `ratCtsInd_cast`
Kind: L
Fidelity: n/a -/
theorem forecastGateBelow_reflected {c : ℕ → ℚ} (hc : Computable c) (δ t : ℚ) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.ValuesAt ((forecastGateBelow T hc δ t).luv n) (ctsInd δ (t : ℝ) ((c n : ℚ) : ℝ)) := by
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
    (forecastGateBelow T hc δ t) n v hv
  rwa [← ratCtsInd_cast] at h

omit [Entailment.Consistent T] in
/-- The mesh product `XUd_n` is valued within `1/(n+1)` of `x · Ind_δ(c_n < t)`.
Source: FAF `meshProductLUV_valuesAt`
Kind: L
Fidelity: n/a -/
theorem forecastProductBelow_reflected {c : ℕ → ℚ} (hc : Computable c) (δ t : ℚ)
    (X : ℕ → LUV) (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) {x : ℝ}
    (hx : v.ValuesAt (X n) x) :
    ∃ z, v.ValuesAt (meshProductLUV (forecastGateBelow T hc δ t) X n) z ∧
      |z - x * ctsInd δ (t : ℝ) ((c n : ℚ) : ℝ)| ≤ 1 / ((n : ℝ) + 1) := by
  have h := meshProductLUV_valuesAt (paperQuotationPresentation T)
    (forecastGateBelow T hc δ t) X n v hv hx
  rwa [← ratCtsInd_cast] at h

/-- **Lemma C, dual face** (the residual bound at the down-ramps): for any computable rational
forecast `c` (no `[0,1]` restriction needed), `t ≥ 0`, `δ > 0`, an injective deferral `f`, and
an e.c. world-valued source `X`,
`E_n(XUd_n) − t·E_n(Ud_n) ≲ₙ E_n(XB'_n) − t·E_n(B'_n) + (1 + t)·E_n(E_n)`
where `B', XB'` are `est`'s below-face quotes at `s := t` and `E` the same truncated error.
The five-term bet `−XUd + t·Ud + XB' − t·B' + (1+t)·E` has world value
`≥ (x − t)(β' − ud) + (1+t)e − 2/(n+1) ≥ −2/(n+1)` (`lemmaC_core` with `|β' − ud| ≤ e` from
`ctsInd_lipschitz_right_min`).
Source: vq-wiki-063 (Lemma C; "The dual cut holds with `Ind_δ(ā_n < t)`, `≲`, and the same
residual"); [[route-transitivity]] §4
Kind: P
Fidelity: variant: products within FAF's mesh slack; forecast stated at `c` (finding F11);
`t ≥ 0` (finding F16)
Hyps: (a); `hinj` -/
theorem lemmaC_below (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {c : ℕ → ℚ}
    (hc : Computable c) {δ : ℚ} (hδ : 0 < δ) {t : ℚ} (ht : 0 ≤ t) :
    (fun n => (meshProductLUV (forecastGateBelow T hc δ t) X n).expect
        (liaHistory (paperDP T)) n -
        (t : ℝ) * ((forecastGateBelow T hc δ t).luv n).expect (liaHistory (paperDP T)) n) ≲ₙ
      (fun n => (estXWBelow T f hX hδ t n).expect (liaHistory (paperDP T)) n -
        (t : ℝ) * (estWBelow T f hX hδ t n).expect (liaHistory (paperDP T)) n +
        (1 + (t : ℝ)) * ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) := by
  set Ud := (forecastGateBelow T hc δ t).luv with hUd
  set XUd := meshProductLUV (forecastGateBelow T hc δ t) X with hXUd
  set B := estWBelow T f hX hδ t with hB
  set XB := estXWBelow T f hX hδ t with hXB
  set E := (truncError T f hX hc hδ).luv with hE
  set terms : List (ℚ × (ℕ → LUV)) := [(-1, XUd), (t, Ud), (1, XB), (-t, B), (1 + t, E)]
    with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact meshProductLUV_machineThresholdCodeSeq _ hX
    · exact (forecastGateBelow T hc δ t).poly
    · exact meshProductLUV_machineThresholdCodeSeq _ hX
    · exact (paperDeferredWeightQuoteCode T f _ _ _).poly
    · exact (truncError T f hX hc hδ).poly
  have hbdd : ∀ n, (constComb 0 terms n).l1Norm (liaHistory (paperDP T)) ≤ 3 + 3 * t :=
    fun n => by
    rw [constComb_l1Norm]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [abs_zero, abs_neg, abs_one, abs_of_nonneg ht',
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)]
    linarith
  have hwv : LUVCombination.WorldValued (constComb 0 terms) (paperDP T) := fun n v hv => by
    obtain ⟨x, hx⟩ := hval n v hv
    obtain ⟨z₁, hz₁, -⟩ := forecastProductBelow_reflected T hc δ t X n v hv hx
    obtain ⟨z₂, hz₂, -⟩ := estXWBelow_reflected T f hinj hX hδ t n v hv hx
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact valuesAt_worldValue hz₁
    · exact valuesAt_worldValue (forecastGateBelow_reflected T hc δ t n v hv)
    · exact valuesAt_worldValue hz₂
    · exact valuesAt_worldValue (estWBelow_reflected T f hinj hX hδ t n v hv)
    · exact valuesAt_worldValue (truncError_reflected T f hX hc hδ n v hv)
  have hvalb : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
      ∀ ν, (constComb 0 terms n).ValuesAt v ν →
        -ε ≤ (constComb 0 terms n).value (liaHistory (paperDP T)) ν := by
    intro ε hε
    have hslack : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := this.const_mul 2
      simp only [mul_zero] at h2
      refine h2.congr (fun n => ?_)
      ring
    filter_upwards [hslack.eventually (gt_mem_nhds hε)] with n hn v hv ν hν
    obtain ⟨x, hx⟩ := hval n v hv
    obtain ⟨z₁, hz₁, hb₁⟩ := forecastProductBelow_reflected T hc δ t X n v hv hx
    obtain ⟨z₂, hz₂, hb₂⟩ := estXWBelow_reflected T f hinj hX hδ t n v hv hx
    have e₁ := (hν (EF.const (-1), XUd n) (by simp [constComb, hterms])).eq hz₁
    have e₂ := (hν (EF.const t, Ud n) (by simp [constComb, hterms])).eq
      (forecastGateBelow_reflected T hc δ t n v hv)
    have e₃ := (hν (EF.const 1, XB n) (by simp [constComb, hterms])).eq hz₂
    have e₄ := (hν (EF.const (-t), B n) (by simp [constComb, hterms])).eq
      (estWBelow_reflected T f hinj hX hδ t n v hv)
    have e₅ := (hν (EF.const (1 + t), E n) (by simp [constComb, hterms])).eq
      (truncError_reflected T f hX hc hδ n v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e₁, e₂, e₃, e₄,
      e₅]
    push_cast
    set y := (X n).expect (liaHistory (paperDP T)) (f n) with hy
    set ud := ctsInd δ (t : ℝ) ((c n : ℚ) : ℝ) with hud
    set β := ctsInd δ (t : ℝ) y with hβ
    set e := min 1 (|((c n : ℚ) : ℝ) - y| / (δ : ℝ)) with he
    have hub : |β - ud| ≤ e :=
      (abs_sub_comm β ud).trans_le (ctsInd_lipschitz_right_min hδ (t : ℝ) _ _)
    have hcore := lemmaC_core (t := (t : ℝ)) (û := β) (β := ud) (e := e) ⟨hx.1, hx.2.1⟩
      (by exact_mod_cast ht) hub
    have hb₁' := (abs_le.1 hb₁).2
    have hb₂' := (abs_le.1 hb₂).1
    have hn' : 2 / ((n : ℝ) + 1) < ε := hn
    have hsplit : 2 / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
    nlinarith [hcore, hb₁', hb₂', hn', hsplit]
  have hS := constCombSyntax 0 terms hcodes
  have hE : (fun n => (constComb 0 terms n).expect (liaHistory (paperDP T)) n) =
      (fun n => ((XB n).expect (liaHistory (paperDP T)) n -
          (t : ℝ) * (B n).expect (liaHistory (paperDP T)) n +
          (1 + (t : ℝ)) * (E n).expect (liaHistory (paperDP T)) n) -
        ((XUd n).expect (liaHistory (paperDP T)) n -
          (t : ℝ) * (Ud n).expect (liaHistory (paperDP T)) n)) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  intro ε hε
  have hge := expect_asympGE_of_eventually hS hbdd hwv (c := -(ε / 2)) (by linarith)
    (hvalb (ε / 2) (by positivity)) (paperDP_hworld T) (ε / 2) (by positivity)
  rw [hE] at hge
  filter_upwards [hge] with n hn
  linarith

/-- **Theorem B, dual face**: for any computable rational forecast `c` of `Y_n = E_{f(n)}(X_n)`
(no `[0,1]` restriction needed), `t ≥ 0`, `δ > 0`, an injective `f` and an e.c. world-valued
`X`,
`E_n(⌜X_n Ind_δ(c_n < t)⌝) ≲ₙ t·E_n(⌜Ind_δ(c_n < t)⌝) + (1 + t)·E_n(⌜min(1, |c_n − Y_n|/δ)⌝)`
— Lemma C's dual face composed with `est`'s below face at `s := t`; the same residual.
Source: vq-wiki-063 (Theorem B, "The dual cut holds with `Ind_δ(ā_n < t)`, `≲`, and the same
residual"); [[route-transitivity]] §4
Kind: C
Fidelity: variant: products within FAF's mesh slack; forecast stated at `c` (finding F11);
`t ≥ 0` (finding F16)
Hyps: (a); `hinj` -/
theorem theoremB_below (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {c : ℕ → ℚ}
    (hc : Computable c) {δ : ℚ} (hδ : 0 < δ) {t : ℚ} (ht : 0 ≤ t) :
    (fun n => (meshProductLUV (forecastGateBelow T hc δ t) X n).expect
        (liaHistory (paperDP T)) n) ≲ₙ
      (fun n => (t : ℝ) * ((forecastGateBelow T hc δ t).luv n).expect (liaHistory (paperDP T)) n +
        (1 + (t : ℝ)) * ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) := by
  have hC := lemmaC_below T f hinj hX hval hc hδ ht
  have hest := est_productForm_below T f hinj hX hval hδ t
  intro ε hε
  filter_upwards [hC (ε / 2) (by positivity), hest (ε / 2) (by positivity)] with n h1 h2
  linarith

/-- **Corollary B.1, dual face**: under `(UA)` the lower cut of per-day soft Total Trust at the
forecast down-gate holds: `E_n(⌜X_n Ind_δ(c_n < t)⌝) − t·E_n(⌜Ind_δ(c_n < t)⌝) ≲ₙ 0`.
Source: vq-wiki-063 (Corollary B.1, "both cuts")
Kind: C
Fidelity: variant: products within FAF's mesh slack; `t ≥ 0`
Hyps: (a); `hinj`; `(UA)` (named scope condition) -/
theorem corollaryB1_below (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {c : ℕ → ℚ}
    (hc : Computable c) {δ : ℚ} (hδ : 0 < δ) {t : ℚ} (ht : 0 ≤ t)
    (hUA : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop,
      |((c n : ℚ) : ℝ) - (X n).expect (liaHistory (paperDP T)) (f n)| < ε) :
    (fun n => (meshProductLUV (forecastGateBelow T hc δ t) X n).expect
        (liaHistory (paperDP T)) n -
        (t : ℝ) * ((forecastGateBelow T hc δ t).luv n).expect (liaHistory (paperDP T)) n) ≲ₙ
      (fun _ => (0 : ℝ)) := by
  have hB := theoremB_below T f hinj hX hval hc hδ ht
  have hres := truncError_expect_tendsto_zero_of_UA T f hX hc hδ hUA
  have hres' : Tendsto (fun n =>
      (1 + (t : ℝ)) * ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun n =>
        ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) atTop (𝓝 0) := by
      have := hres
      unfold AsympEq at this
      simpa using this
    simpa using h0.const_mul (1 + (t : ℝ))
  intro ε hε
  filter_upwards [hB (ε / 2) (by positivity),
    hres'.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))] with n h1 h2
  linarith

/-! ## Theorem B, the source's per-day form -/

/-- **Theorem B, per-day form** — the source's second display: "and by Lemma B equivalently
`liminf_n [û_n(E^H_n(X_n) − t) + (1 + t)·E^H_n(⌜e_n⌝)] ≥ 0`", in `∀ ε, ∀ᶠ` form:
`Ind_δ(c_n > t)·(E_n(X_n) − t) + (1 + t)·E_n(⌜min(1, |c_n − Y_n|/δ)⌝) ≳ₙ 0`. Theorem B at the
computable forecast `c`, with its two gate expectations transported by Lemma B
(`gateKnowledge_product`: `E_n(⌜X_n û_n⌝) ≈ₙ û_n·E_n(X_n)`; `gateKnowledge_weight`:
`E_n(⌜û_n⌝) ≈ₙ û_n`). This is the one Theorem-B statement that needs `c` **P-generable** (Lemma
B's gate `û_n = Ind_δ(c_n > t)` must be a generable feature, `pgenerableRat_ratCtsInd_left`),
which is the source's own hypothesis (`ā_n` a market expectation); `theoremB` needs only
`Computable c`, and the computability used here is `PGenerableRat.computable`.
Source: vq-wiki-063 (Theorem B, "by Lemma B equivalently …"); [[route-transitivity]] §4
Kind: C
Fidelity: exact (conclusion on real sequences; the product quote inside Theorem B within FAF's
mesh slack); `t ≥ 0` (finding F16)
Hyps: (a); `hinj` -/
theorem theoremB_perDay (f : DeferralFunction) (hinj : Function.Injective f.f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {c : ℕ → ℚ}
    (hcg : PGenerableRat (liaHistory (paperDP T)) c) {δ : ℚ} (hδ : 0 < δ) {t : ℚ} (ht : 0 ≤ t) :
    (fun n => ctsInd δ ((c n : ℚ) : ℝ) (t : ℝ) *
          ((X n).expect (liaHistory (paperDP T)) n - (t : ℝ)) +
        (1 + (t : ℝ)) *
          ((truncError T f hX (hcg.computable (paperMarketComputation T)) hδ).luv n).expect
            (liaHistory (paperDP T)) n) ≳ₙ (fun _ => (0 : ℝ)) := by
  have hc : Computable c := hcg.computable (paperMarketComputation T)
  have hB := theoremB T f hinj hX hval hc hδ ht
  have hu := pgenerableRat_ratCtsInd_left hcg hδ t
  have humem : ∀ n, 0 ≤ ratCtsInd δ (c n) t ∧ ratCtsInd δ (c n) t ≤ 1 :=
    fun n => ratCtsInd_mem_Icc _ _ _
  have hA := gateKnowledge_product hu humem hX hval
    (meshProductLUV_machineThresholdCodeSeq (forecastGate T hc δ t) hX)
    tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n v hv x hx => by
      obtain ⟨z, hz, hzx⟩ := forecastProduct_reflected T hc δ t X n v hv hx
      exact ⟨z, hz, by rwa [ratCtsInd_cast] at hzx⟩)
    (paperDP_hworld T)
  have hW := gateKnowledge_weight hu humem (forecastGate T hc δ t).poly
    (fun n v hv => by
      have h := forecastGate_reflected T hc δ t n v hv
      rwa [ratCtsInd_cast] at h)
    (paperDP_hworld T)
  have hD : (fun n =>
      (meshProductLUV (forecastGate T hc δ t) X n).expect (liaHistory (paperDP T)) n -
        (t : ℝ) * ((forecastGate T hc δ t).luv n).expect (liaHistory (paperDP T)) n +
        (1 + (t : ℝ)) * ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun _ => (0 : ℝ)) := by
    intro ε hε
    filter_upwards [hB ε hε] with n hn
    linarith
  have hEq : (fun n =>
      (meshProductLUV (forecastGate T hc δ t) X n).expect (liaHistory (paperDP T)) n -
        (t : ℝ) * ((forecastGate T hc δ t).luv n).expect (liaHistory (paperDP T)) n +
        (1 + (t : ℝ)) * ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => ctsInd δ ((c n : ℚ) : ℝ) (t : ℝ) *
          ((X n).expect (liaHistory (paperDP T)) n - (t : ℝ)) +
        (1 + (t : ℝ)) *
          ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n) := by
    have h := (hA.sub (hW.const_mul (t : ℝ))).add
      (AsympEq.refl (fun n => (1 + (t : ℝ)) *
        ((truncError T f hX hc hδ).luv n).expect (liaHistory (paperDP T)) n))
    unfold AsympEq at h ⊢
    refine h.congr (fun n => ?_)
    simp only [ratCtsInd_cast]
    ring
  exact (asympGE_zero_congr hEq).1 hD

/-! ## Prop 6.3 — the residual is not necessary -/

/-- **Prop 6.3's numerical example** (real sequences): `c ≡ 1/2`, `Y ∈ {0,1}` (the honest quote
on a pseudorandom target), `t = 2/5`, `δ = 1/20`. The gate `û = Ind_δ(1/2 > 2/5) = 1` fires,
the residual `e = min(1, |1/2 − Y|/δ) = 1` is maximal, Theorem B's lower bound
`t·1 − (1+t)·1 < 0` is vacuous — yet the per-day target `û · (h − t) ≥ 0` holds at
`h = 1/2 ≥ t`. So Theorem B's residual is not necessary: the gate transfer demands
absolute-error control where the `cee` route demands only signed-average control. This is the
source's example as four real-number facts — a numerical identity at fixed values, Kind L
(repair round 2, after the round-2 adversarial audit N3; it was labelled N+, but four
real-number facts inhabit nothing); it does **not** inhabit `theoremB`'s hypothesis package
(the inhabitants are `theoremB_parity_instance`, which realises exactly this vacuous regime
over the paper inductor, and `theoremB_parityForecast_instance`, on which the bound bites —
`Witness.lean`), and the inductor-level Prop 6.3 (a target on which the novice itself sits
near `1/2`) needs the pseudorandom family over T7 — not written.
Source: vq-wiki-2-010 ([[route-transitivity]] §6.2, Proposition 6.3)
Kind: L
Fidelity: exact (the source's abstract-sequence example; the inductor-level form rests on
target 7's family)
Hyps: (a) none -/
theorem prop63_witness (Y : ℝ) (hY : Y = 0 ∨ Y = 1) :
    ctsInd (1 / 20 : ℚ) (1 / 2 : ℝ) ((2 / 5 : ℚ) : ℝ) = 1 ∧
      min 1 (|(1 / 2 : ℝ) - Y| / ((1 / 20 : ℚ) : ℝ)) = 1 ∧
      (2 / 5 : ℝ) * 1 - (1 + 2 / 5) * 1 < 0 ∧
      0 ≤ ctsInd (1 / 20 : ℚ) (1 / 2 : ℝ) ((2 / 5 : ℚ) : ℝ) * ((1 / 2 : ℝ) - 2 / 5) := by
  have h1 : ctsInd (1 / 20 : ℚ) (1 / 2 : ℝ) ((2 / 5 : ℚ) : ℝ) = 1 := by
    rw [ctsInd_eq_one_iff (by norm_num)]
    norm_num
  refine ⟨h1, ?_, by norm_num, by rw [h1]; norm_num⟩
  rcases hY with rfl | rfl <;> norm_num

end

end Cleanroom.Deference.DefSelfTrust
