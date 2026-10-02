import Cleanroom.Udt.UdtHarmonyBargain.Support
import Cleanroom.Found.FixKakutani.Transport

/-!
# `udt-harmony-bargain` — existence of trembling-hand equilibria (T6)

For every finite `StrategicGame N ℝ`: every uniformly `ε`-perturbed game with `ε > 0` and
`card (strategy i) · ε < 1` has a Nash equilibrium (`exists_perturbedNash`), and a trembling-hand
equilibrium exists (`exists_thpe`). Route: the `ε`-floor simplex is the affine image
`q ↦ ε·𝟙 + (1 − Kᵢε) q` of the standard simplex; the constrained best-response correspondence on
`Set.univ.pi (stdSimplex ℝ (strategy i))` has nonempty convex values and a closed graph
(`hasClosedGraphOn_iff_seq_of_isClosed` + continuity of the expected payoff), so `fix-kakutani`'s
`kakutani_pi_stdSimplex` gives a fixed point; then `ε k := 1/(K + k + 2)`, and a convergent
subsequence of the perturbed equilibria (`IsCompact.tendsto_subseq`) is a trembling-hand
equilibrium by definition. Kakutani is `fix-kakutani`'s theorem, not a hypothesis (plan rule 11
discharged). The limit may be mixed: no pure trembling-hand equilibrium is claimed.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset StrategicGame Filter Topology Cleanroom.Found.FixKakutani

variable {N : Type} [Fintype N] [DecidableEq N]
variable {G : StrategicGame N ℝ} [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
  [∀ i, Nonempty (G.strategy i)]

/-- The domain: a product of standard simplices, one per player.
Source: none: infrastructure
Kind: D -/
def simplexPi (G : StrategicGame N ℝ) [∀ i, Fintype (G.strategy i)] :
    Set (∀ i, G.strategy i → ℝ) :=
  Set.univ.pi fun i => stdSimplex ℝ (G.strategy i)

/-- The reparametrisation of the `ε`-floor simplex by the standard simplex, coordinatewise:
`q ↦ ε + (1 − Kᵢ ε) q`.
Source: mandate T6 ("reparametrise the ε-floor simplex as the affine image")
Kind: D -/
def aff (G : StrategicGame N ℝ) [∀ i, Fintype (G.strategy i)] (ε : ℝ)
    (x : ∀ i, G.strategy i → ℝ) : ∀ i, G.strategy i → ℝ :=
  fun i s => ε + (1 - Fintype.card (G.strategy i) * ε) * x i s

theorem continuous_aff (ε : ℝ) : Continuous (aff G ε) := by
  refine continuous_pi fun i => continuous_pi fun s => ?_
  exact continuous_const.add (continuous_const.mul ((continuous_apply s).comp (continuous_apply i)))

theorem aff_update_of_ne (ε : ℝ) (x : ∀ i, G.strategy i → ℝ) {i j : N} (hj : j ≠ i)
    (q : G.strategy i → ℝ) : aff G ε (Function.update x i q) j = aff G ε x j := by
  funext s
  unfold aff
  rw [Function.update_of_ne hj]

theorem aff_update (ε : ℝ) (x : ∀ i, G.strategy i → ℝ) (i : N) (q : G.strategy i → ℝ) :
    aff G ε (Function.update x i q) = Function.update (aff G ε x) i (aff G ε (Function.update x i q) i) := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · rw [Function.update_of_ne hj, aff_update_of_ne ε x hj]

theorem aff_mem_stdSimplex {ε : ℝ} (hε : 0 ≤ ε) (hK : ∀ i, (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1)
    {x : ∀ i, G.strategy i → ℝ} (hx : x ∈ simplexPi G) (i : N) :
    aff G ε x i ∈ stdSimplex ℝ (G.strategy i) := by
  have hxi : x i ∈ stdSimplex ℝ (G.strategy i) := hx i (Set.mem_univ _)
  refine ⟨fun s => ?_, ?_⟩
  · unfold aff
    have := hxi.1 s
    have := hK i
    nlinarith
  · unfold aff
    rw [sum_add_distrib, ← mul_sum, hxi.2, sum_const, card_univ, nsmul_eq_mul]
    ring

theorem aff_floor {ε : ℝ} (hε : 0 ≤ ε) (hK : ∀ i, (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1)
    {x : ∀ i, G.strategy i → ℝ} (hx : x ∈ simplexPi G) (i : N) (s : G.strategy i) :
    ε ≤ aff G ε x i s := by
  unfold aff
  have := (hx i (Set.mem_univ _)).1 s
  have := hK i
  nlinarith

/-- Player `i`'s payoff when the profile is `aff x` with `i`'s coordinate replaced by `aff` of `q`.
Source: none: infrastructure
Kind: D -/
def gPay (G : StrategicGame N ℝ) [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
    (ε : ℝ) (x : ∀ i, G.strategy i → ℝ) (i : N) (q : G.strategy i → ℝ) : ℝ :=
  euFun G (aff G ε (Function.update x i q)) i

theorem continuous_gPay (ε : ℝ) (i : N) :
    Continuous (fun p : (∀ j, G.strategy j → ℝ) × (G.strategy i → ℝ) => gPay G ε p.1 i p.2) := by
  unfold gPay
  refine (continuous_euFun G i).comp ((continuous_aff ε).comp ?_)
  exact continuous_fst.update i continuous_snd

/-- The expected payoff is affine in one player's raw weight vector.
Source: none: infrastructure (raw form of `expectedPayoff_update_eq_sum`)
Kind: P -/
theorem euFun_update_affine (z : ∀ i, G.strategy i → ℝ) (i : N) (r r' : G.strategy i → ℝ)
    (t : ℝ) :
    euFun G (Function.update z i (fun s => t * r s + (1 - t) * r' s)) i =
      t * euFun G (Function.update z i r) i + (1 - t) * euFun G (Function.update z i r') i := by
  unfold euFun
  simp only [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun σ _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ i), ← mul_prod_erase univ _ (mem_univ i),
    ← mul_prod_erase univ _ (mem_univ i)]
  simp only [Function.update_self]
  have h : ∀ (w : G.strategy i → ℝ), ∏ j ∈ univ.erase i, (Function.update z i w j) (σ j) =
      ∏ j ∈ univ.erase i, z j (σ j) :=
    fun w => prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [h, h, h]
  ring

/-- `gPay` is affine in `q`.
Source: none: infrastructure
Kind: L -/
theorem gPay_affine (ε : ℝ) (x : ∀ i, G.strategy i → ℝ) (i : N) (q q' : G.strategy i → ℝ)
    (t : ℝ) :
    gPay G ε x i (fun s => t * q s + (1 - t) * q' s) =
      t * gPay G ε x i q + (1 - t) * gPay G ε x i q' := by
  unfold gPay
  rw [aff_update, aff_update ε x i q, aff_update ε x i q']
  have hw : aff G ε (Function.update x i (fun s => t * q s + (1 - t) * q' s)) i =
      fun s => t * aff G ε (Function.update x i q) i s + (1 - t) * aff G ε (Function.update x i q') i s := by
    funext s
    simp only [aff, Function.update_self]
    ring
  rw [hw, euFun_update_affine]

/-- The constrained best-response correspondence on the product of simplices.
Source: mandate T6
Kind: D -/
def brCorr (G : StrategicGame N ℝ) [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]
    (ε : ℝ) (x : ∀ i, G.strategy i → ℝ) : Set (∀ i, G.strategy i → ℝ) :=
  {y | y ∈ simplexPi G ∧ ∀ i, ∀ q ∈ stdSimplex ℝ (G.strategy i), gPay G ε x i q ≤ gPay G ε x i (y i)}

theorem isClosed_simplexPi : IsClosed (simplexPi G) :=
  isClosed_set_pi fun i _ => isClosed_stdSimplex ℝ (G.strategy i)

theorem isCompact_simplexPi : IsCompact (simplexPi G) :=
  isCompact_univ_pi fun i => isCompact_stdSimplex ℝ (G.strategy i)

theorem brCorr_nonempty (ε : ℝ) (x : ∀ i, G.strategy i → ℝ) : (brCorr G ε x).Nonempty := by
  have h : ∀ i, ∃ q ∈ stdSimplex ℝ (G.strategy i), ∀ q' ∈ stdSimplex ℝ (G.strategy i),
      gPay G ε x i q' ≤ gPay G ε x i q := by
    intro i
    obtain ⟨q, hq, hmax⟩ := (isCompact_stdSimplex ℝ (G.strategy i)).exists_isMaxOn
      ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary (G.strategy i))⟩
      (((continuous_gPay ε i).comp (Continuous.prodMk continuous_const continuous_id)).continuousOn)
    exact ⟨q, hq, fun q' hq' => hmax hq'⟩
  choose q hq hmax using h
  exact ⟨q, fun i _ => hq i, fun i q' hq' => hmax i q' hq'⟩

theorem brCorr_convex (ε : ℝ) (x : ∀ i, G.strategy i → ℝ) : Convex ℝ (brCorr G ε x) := by
  intro y hy y' hy' a b ha hb hab
  refine ⟨?_, ?_⟩
  · exact (convex_pi fun i _ => convex_stdSimplex ℝ (G.strategy i)) hy.1 hy'.1 ha hb hab
  · intro i q hq
    have hb' : b = 1 - a := by linarith
    have e : (a • y + b • y') i = fun s => a * y i s + (1 - a) * y' i s := by
      funext s; simp [hb']
    rw [e, gPay_affine]
    have h1 := mul_le_mul_of_nonneg_left (hy.2 i q hq) ha
    have h2 := mul_le_mul_of_nonneg_left (hy'.2 i q hq) (by linarith : (0 : ℝ) ≤ 1 - a)
    linarith

theorem tendsto_gPay (ε : ℝ) (i : N) {xs : ℕ → ∀ j, G.strategy j → ℝ}
    {qs : ℕ → G.strategy i → ℝ} {x : ∀ j, G.strategy j → ℝ} {q : G.strategy i → ℝ}
    (hxs : Tendsto xs atTop (𝓝 x)) (hqs : Tendsto qs atTop (𝓝 q)) :
    Tendsto (fun n => gPay G ε (xs n) i (qs n)) atTop (𝓝 (gPay G ε x i q)) := by
  have h1 : Tendsto (fun n => (xs n, qs n)) atTop (𝓝 (x, q)) := hxs.prodMk_nhds hqs
  have h2 := ((continuous_gPay ε i).tendsto (x, q)).comp h1
  exact h2

theorem brCorr_closedGraph (ε : ℝ) : HasClosedGraphOn (brCorr G ε) (simplexPi G) := by
  refine (hasClosedGraphOn_iff_seq_of_isClosed isClosed_simplexPi).mpr ?_
  intro xs ys x y hmem hxs hys
  have hyD : y ∈ simplexPi G :=
    isClosed_simplexPi.mem_of_tendsto hys (Eventually.of_forall fun n => (hmem n).2.1)
  refine ⟨hyD, ?_⟩
  intro i q hq
  have hl := tendsto_gPay ε i (qs := fun _ => q) hxs tendsto_const_nhds
  have hr := tendsto_gPay ε i (qs := fun n => ys n i) hxs (tendsto_pi_nhds.mp hys i)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n => (hmem n).2.2 i q hq)

theorem brCorr_maps (ε : ℝ) (x : ∀ i, G.strategy i → ℝ) : brCorr G ε x ⊆ simplexPi G :=
  fun _ hy => hy.1

/-- **Existence of perturbed equilibria**: for `0 < ε` with `card (strategy i) · ε < 1` for every
player, the uniformly `ε`-perturbed game has a Nash equilibrium (in the constrained-deviation sense
of `IsPerturbedNash`).
Source: mandate T6 (`exists_perturbedNash`); Selten 1975 via Kakutani (`fix-kakutani`)
Kind: P
Fidelity: exact
Hyps: (a) all (Kakutani is `kakutani_pi_stdSimplex`, plan rule 11 discharged) -/
theorem exists_perturbedNash {ε : ℝ} (hε : 0 < ε)
    (hK : ∀ i, (Fintype.card (G.strategy i) : ℝ) * ε < 1) :
    ∃ p : MixedProfile G, IsPerturbedNash ε p := by
  obtain ⟨x, hx, hfix⟩ := kakutani_pi_stdSimplex (brCorr G ε) (fun x _ => brCorr_maps ε x)
    (fun x _ => brCorr_nonempty ε x) (fun x _ => brCorr_convex ε x) (brCorr_closedGraph ε)
  have hK' : ∀ i, (Fintype.card (G.strategy i) : ℝ) * ε ≤ 1 := fun i => (hK i).le
  refine ⟨fun i => ⟨aff G ε x i, aff_mem_stdSimplex hε.le hK' hx i⟩, ?_, ?_⟩
  · intro i s
    exact aff_floor hε.le hK' hx i s
  · intro i q hq
    -- pull `q` back to the standard simplex
    set c : ℝ := 1 - Fintype.card (G.strategy i) * ε with hc
    have hcpos : 0 < c := by rw [hc]; linarith [hK i]
    let q' : G.strategy i → ℝ := fun s => (q.val s - ε) / c
    have hc0 : c ≠ 0 := hcpos.ne'
    have hq' : q' ∈ stdSimplex ℝ (G.strategy i) := by
      refine ⟨fun s => div_nonneg (by linarith [hq s]) hcpos.le, ?_⟩
      show ∑ s, (q.val s - ε) / c = 1
      simp_rw [div_eq_mul_inv]
      rw [← sum_mul, sum_sub_distrib, q.2.2, sum_const, card_univ, nsmul_eq_mul, ← hc]
      exact mul_inv_cancel₀ hc0
    have hqq : q.val = aff G ε (Function.update x i q') i := by
      funext s
      unfold aff
      rw [Function.update_self]
      show q.val s = ε + (1 - Fintype.card (G.strategy i) * ε) * ((q.val s - ε) / c)
      rw [← hc, mul_div_cancel₀ _ hc0]
      ring
    have h1 := hfix.2 i q' hq'
    have hpv : profileVal (Function.update (fun j => (⟨aff G ε x j, aff_mem_stdSimplex hε.le hK' hx j⟩ :
        MixedStrategy G j)) i q) = aff G ε (Function.update x i q') := by
      funext j
      rcases eq_or_ne j i with rfl | hj
      · show (Function.update (fun j => (⟨aff G ε x j, aff_mem_stdSimplex hε.le hK' hx j⟩ :
            MixedStrategy G j)) j q j).val = _
        rw [Function.update_self]
        exact hqq
      · show (Function.update (fun j => (⟨aff G ε x j, aff_mem_stdSimplex hε.le hK' hx j⟩ :
            MixedStrategy G j)) i q j).val = _
        rw [Function.update_of_ne hj, aff_update_of_ne ε x hj]
    have hpv' : profileVal (fun j => (⟨aff G ε x j, aff_mem_stdSimplex hε.le hK' hx j⟩ :
        MixedStrategy G j)) = aff G ε x := rfl
    rw [expectedPayoff_eq_euFun, expectedPayoff_eq_euFun, hpv, hpv']
    unfold gPay at h1
    have hxx : Function.update x i (x i) = x := Function.update_eq_self i x
    rw [hxx] at h1
    exact h1

/-- **Existence of trembling-hand equilibria** for every finite game (SC Def. 10.4): perturbed
equilibria along `ε k = 1/(K + k + 2)` and a convergent subsequence. The limit may be mixed.
Source: mandate T6 (`exists_thpe`); Selten 1975
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem exists_thpe : ∃ pStar : MixedProfile G, THPE pStar := by
  let Kmax : ℕ := univ.sup fun i => Fintype.card (G.strategy i)
  have hKmax : ∀ i, Fintype.card (G.strategy i) ≤ Kmax := fun i =>
    Finset.le_sup (f := fun i => Fintype.card (G.strategy i)) (mem_univ i)
  let ε : ℕ → ℝ := fun k => 1 / (Kmax + k + 2)
  have hpos : ∀ k, 0 < ε k := fun k => by positivity
  have hK : ∀ k i, (Fintype.card (G.strategy i) : ℝ) * ε k < 1 := by
    intro k i
    have h1 : (Fintype.card (G.strategy i) : ℝ) ≤ Kmax := by exact_mod_cast hKmax i
    show (Fintype.card (G.strategy i) : ℝ) * (1 / (Kmax + k + 2)) < 1
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  choose p hp using fun k => exists_perturbedNash (G := G) (hpos k) (hK k)
  have hmem : ∀ k, profileVal (p k) ∈ simplexPi G := fun k i _ => (p k i).2
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_simplexPi.tendsto_subseq hmem
  refine ⟨fun i => ⟨a i, ha i (Set.mem_univ _)⟩, ε ∘ φ, p ∘ φ, fun k => hpos (φ k), ?_,
    fun k => hp (φ k), ?_⟩
  · have hε : Tendsto ε atTop (𝓝 0) := by
      have : Tendsto (fun k : ℕ => (1 : ℝ) / ((k + (Kmax + 2) : ℕ) : ℝ)) atTop (𝓝 0) :=
        (tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat (Kmax + 2))
      refine this.congr fun k => ?_
      simp only [ε]
      push_cast
      ring_nf
    exact hε.comp hφ.tendsto_atTop
  · exact hlim

end Cleanroom.Udt.UdtHarmonyBargain
