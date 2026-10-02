import Cleanroom.Info.InfoVoiLatents.Mediation

/-!
# info-voi-latents — the S5 assembly under H1–H4 (Target 6(iii); repair round 2)

Repair round 1 and audit r2 (fidelity item 5(b)) left the *assembly* of S5's two bounds undone
("every piece proved, the two-measure carrier not set up"). This file sets the carrier up and
assembles.

**The two-measure carrier.** The truth is a probability measure `μ` on `Ω` with the latent
`Λ : Ω → Λ'`, the data `Y : Ω → Y'` and the next chunk (carrier (ii)); its posteriors `P^H(λ | y)`
are the ratio `pm2 μ Λ Y λ y / pm1 μ Y y` (`truePost`, junk `0` at a null `y`) and its data
marginal is `pm1 μ Y`. The *agent's* posterior `Pt : Y' → Λ' → ℝ` is a second family of
distributions on the same finite carrier (carrier (i)); nothing ties it to `μ` except the
hypotheses. So the "two measures" are one measure and one kernel, and every expectation is under
the truth.

* **`predictive_tv_assembly`** (S5(i), P5(i); carrier (i)): with a shared kernel `K` (H3: the
  agent's predictive is `∑_λ K(λ) · Pt(λ | y)`), the true predictive `∑_λ KH y λ · PH(λ | y)`
  (`KH y λ = P^H[X_k | λ, y]`), the mediation gap `∑_y ∑_λ P(y) PH(λ | y) · klFin (KH y λ) (K λ)
  ≤ ε_med` and the posterior gap `∑_y P(y) · klFin (PH y) (Pt y) ≤ ε₄` (H4), the expected total
  variation between the agent's and the true predictive is at most `√(ε_med/2) + √(ε₄/2)`. Route:
  `tv` triangle inequality, `Mediation.tv_mix_le` (a common kernel contracts) for the first gap,
  mixture convexity (`tv_mix_mix_le`) for the second, Pinsker and Jensen for `√` on each
  (`sum_mul_tv_le_sqrt`).
* **`expected_miss_assembly`** (S5(ii), P5(ii); carriers (i) + (ii)): the expected posterior miss
  of the truth under the *agent's* posterior, `∑_{λ,y} P(λ, y)(1 − Pt(λ | y))`, is at most the
  true one plus the expected `tv` (`P^H(λ | y) − Pt(λ | y) ≤ tv`, `sub_le_tv`), hence
  `≤ H[Λ | Y] + √(ε₄/2)` (`expMiss_le_condEntropy`).
* **`expected_err_assembly`**: with `Λ_C = f ∘ Λ`, `EIG ≤ ε_red` and a profile of range `M`,
  `E[err] ≤ M · (ε_red + ν + √(ε₄/2))` with `ν = H[Λ_C | ⟨X_k, X_{≤t}⟩]` — the mandate's
  `E[err_t(C_k)] ≤ M(ε_red + ν_k + √(ε₄/2))` (`err_le_mul_one_sub` pointwise,
  `condEntropy_le_eig_add_noise`).

Hyps: every hypothesis is the claim's own antecedent — H3 enters as the *shape* of the agent's
predictive (a mixture through `K`), H4 and the mediation gap as stated KL bounds, `EIG ≤ ε_red` as
a bound; the note's own remark that H3 "is the generalization problem assumed" is about the world,
not about the theorem. Absolute continuity of the true posterior with respect to the agent's
(`AbsCont (P^H(· | y)) (Pt y)` at every positive-mass `y`, and of `KH y λ` w.r.t. `K λ`) is required
for Pinsker and is stated explicitly (findings F10). Mandate: Target 6(iii).
-/

namespace Cleanroom.Info.InfoVoiLatents.Mediation

open MeasureTheory ProbabilityTheory Finset Real
open Cleanroom.Info.InfoVoiLatents.Eig Cleanroom.Info.InfoVoiLatents.Coverage
open Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Total variation: triangle inequality, mixture convexity, single coordinates -/

/-- The triangle inequality for `tv`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tv_triangle {W : Type} [Fintype W] (p q r : W → ℝ) : tv p r ≤ tv p q + tv q r := by
  unfold tv
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) (by norm_num)
  calc |p w - r w| = |(p w - q w) + (q w - r w)| := by ring_nf
    _ ≤ |p w - q w| + |q w - r w| := abs_add_le _ _

/-- **Mixture convexity of `tv`**: `tv (K₁ ⋆ P) (K₂ ⋆ P) ≤ ∑ λ, P λ · tv (K₁ λ) (K₂ λ)` for a
nonnegative weight vector `P` (two kernels, one weight).
Source: [[generalization-final]] P5(i) l. 125 (the second gap, `E tv(P^H[X_k | λ, y], P^H[X_k | λ])`)
Kind: P
Fidelity: exact -/
theorem tv_mix_mix_le {Λ' X : Type} [Fintype Λ'] [Fintype X] (K₁ K₂ : Λ' → X → ℝ) {P : Λ' → ℝ}
    (hP : ∀ l, 0 ≤ P l) : tv (mix K₁ P) (mix K₂ P) ≤ ∑ l, P l * tv (K₁ l) (K₂ l) := by
  unfold tv mix
  calc (1 / 2) * ∑ x, |∑ l, P l * K₁ l x - ∑ l, P l * K₂ l x|
      = (1 / 2) * ∑ x, |∑ l, P l * (K₁ l x - K₂ l x)| := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ (1 / 2) * ∑ x, ∑ l, P l * |K₁ l x - K₂ l x| := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by norm_num)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [abs_mul, abs_of_nonneg (hP l)]
    _ = ∑ l, P l * ((1 / 2) * ∑ x, |K₁ l x - K₂ l x|) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun x _ => ?_
        ring

/-- **A single coordinate moves by at most `tv`**: `p w − q w ≤ tv p q` for simplex vectors.
Source: [[generalization-final]] P5(ii) l. 125 (the transfer `1 − P_t(true | y) ≤ 1 − P^H(true | y)
+ tv`)
Kind: P
Fidelity: exact -/
theorem sub_le_tv {W : Type} [Fintype W] {p q : W → ℝ} (hp : p ∈ stdSimplex ℝ W)
    (hq : q ∈ stdSimplex ℝ W) (w : W) : p w - q w ≤ tv p q := by
  classical
  rw [tv_eq_sum_filter hp hq]
  by_cases h : q w < p w
  · exact Finset.single_le_sum (f := fun w => p w - q w)
      (fun w' hw' => by
        have := (Finset.mem_filter.1 hw').2
        linarith)
      (Finset.mem_filter.2 ⟨Finset.mem_univ w, h⟩)
  · push Not at h
    refine le_trans (by linarith) (Finset.sum_nonneg fun w' hw' => ?_)
    have := (Finset.mem_filter.1 hw').2
    linarith

/-! ### Pinsker + Jensen in expectation -/

/-- **Expected `tv` from expected KL** (Pinsker then Jensen for `√`): for a weight vector `P` in
the simplex and families `p q` that are simplex vectors with `p s ≪ q s` wherever `P s ≠ 0`,
`∑ s, P s · tv (p s) (q s) ≤ √(∑ s, P s · klFin (p s) (q s) / 2)` (null weights see nothing).
Source: [[generalization-final]] S2 l. 61, P5(i) l. 125 ("Pinsker + Jensen")
Kind: C
Fidelity: exact -/
theorem sum_mul_tv_le_sqrt {S W : Type} [Fintype S] [Fintype W] {P : S → ℝ}
    (hP : P ∈ stdSimplex ℝ S) {p q : S → W → ℝ} (hp : ∀ s, P s ≠ 0 → p s ∈ stdSimplex ℝ W)
    (hq : ∀ s, P s ≠ 0 → q s ∈ stdSimplex ℝ W) (hac : ∀ s, P s ≠ 0 → AbsCont (p s) (q s)) :
    ∑ s, P s * tv (p s) (q s) ≤ Real.sqrt ((∑ s, P s * klFin (p s) (q s)) / 2) := by
  classical
  set x : S → ℝ := fun s => if P s = 0 then 0 else klFin (p s) (q s) / 2 with hxdef
  have hx : ∀ s, 0 ≤ x s := fun s => by
    simp only [hxdef]
    split_ifs with hs
    · exact le_rfl
    · have := klFin_nonneg (hp s hs) (hq s hs) (hac s hs)
      positivity
  have e : ∑ s, P s * x s = (∑ s, P s * klFin (p s) (q s)) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hxdef]
    split_ifs with hs
    · rw [hs]
      ring
    · ring
  calc ∑ s, P s * tv (p s) (q s) ≤ ∑ s, P s * Real.sqrt (x s) := by
        refine Finset.sum_le_sum fun s _ => ?_
        by_cases hs : P s = 0
        · rw [hs, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ (hP.1 s)
          simp only [hxdef, if_neg hs]
          exact pinsker (hp s hs) (hq s hs) (hac s hs)
    _ ≤ Real.sqrt (∑ s, P s * x s) := sum_mul_sqrt_le hP hx
    _ = Real.sqrt ((∑ s, P s * klFin (p s) (q s)) / 2) := by rw [e]

/-- The joint weight `(y, λ) ↦ P(y) · Q(λ | y)` of a simplex vector and a simplex-valued kernel is
in the simplex on `Y × Λ'`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem jointWeight_mem {Y' Λ' : Type} [Fintype Y'] [Fintype Λ'] {P : Y' → ℝ}
    (hP : P ∈ stdSimplex ℝ Y') {Q : Y' → Λ' → ℝ} (hQ : ∀ y, Q y ∈ stdSimplex ℝ Λ') :
    (fun p : Y' × Λ' => P p.1 * Q p.1 p.2) ∈ stdSimplex ℝ (Y' × Λ') := by
  refine ⟨fun p => mul_nonneg (hP.1 p.1) ((hQ p.1).1 p.2), ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  calc ∑ y, P y * ∑ l, Q y l = ∑ y, P y := Finset.sum_congr rfl fun y _ => by rw [(hQ y).2, mul_one]
    _ = 1 := hP.2

/-! ### S5(i): the predictive TV chain, assembled -/

/-- **The S5(i) assembly** (P5(i) l. 125): with the agent's predictive `∑_λ K(λ) · Pt(λ | y)` (H3,
a shared kernel) and the true predictive `∑_λ KH y λ · PH(λ | y)`, the expected total variation
between them is at most `√(ε_med/2) + √(ε₄/2)`, where the mediation gap is
`∑_y ∑_λ P(y)·PH(λ | y)·klFin (KH y λ) (K λ) ≤ ε_med` (Target 1's twin identity renders this
as `I[X_k : X_{≤t} | Λ]` on carrier (ii); here it is a stated bound) and the posterior gap is H4,
`∑_y P(y)·klFin (PH y) (Pt y) ≤ ε₄`. Pointwise: `tv(agent, true) ≤ tv(K ⋆ Pt, K ⋆ PH)
+ tv(K ⋆ PH, KH ⋆ PH) ≤ tv(Pt, PH) + ∑_λ PH(λ | y)·tv(K λ, KH y λ)`; then Pinsker and Jensen on
each term.
Source: [[generalization-final]] S5(i) l. 73, P5(i) l. 125 ("the first gap is `≤ TV(P_t(λ | X_{≤t}),
P^H(λ | X_{≤t}))`", "the second gap … `≤ √(medErr/2)`"); mandate Target 6(iii)
Kind: C
Fidelity: exact (the assembly the mandate asks for, on carrier (i); the mediation gap enters as
its KL form, which Target 1 identifies with `I[X_k : X_{≤t} | Λ]`)
Hyps: (a) all — H3 is the shape of the agent's predictive (the claim's antecedent), H4 and the
mediation gap are the stated KL bounds, plus simplex membership and absolute continuity for
Pinsker -/
theorem predictive_tv_assembly {Y' Λ' X' : Type} [Fintype Y'] [Fintype Λ'] [Fintype X']
    {P : Y' → ℝ} (hP : P ∈ stdSimplex ℝ Y')
    {PH Pt : Y' → Λ' → ℝ} (hPH : ∀ y, PH y ∈ stdSimplex ℝ Λ') (hPt : ∀ y, Pt y ∈ stdSimplex ℝ Λ')
    (hacP : ∀ y, AbsCont (PH y) (Pt y))
    {K : Λ' → X' → ℝ} (hK : ∀ l, K l ∈ stdSimplex ℝ X')
    {KH : Y' → Λ' → X' → ℝ} (hKH : ∀ y l, KH y l ∈ stdSimplex ℝ X')
    (hacK : ∀ y l, AbsCont (KH y l) (K l))
    {ε₄ εmed : ℝ} (h₄ : ∑ y, P y * klFin (PH y) (Pt y) ≤ ε₄)
    (hmed : ∑ y, ∑ l, P y * PH y l * klFin (KH y l) (K l) ≤ εmed) :
    ∑ y, P y * tv (mix K (Pt y)) (mix (KH y) (PH y))
      ≤ Real.sqrt (εmed / 2) + Real.sqrt (ε₄ / 2) := by
  -- pointwise chain
  have hpt : ∀ y, tv (mix K (Pt y)) (mix (KH y) (PH y))
      ≤ tv (PH y) (Pt y) + ∑ l, PH y l * tv (KH y l) (K l) := by
    intro y
    calc tv (mix K (Pt y)) (mix (KH y) (PH y))
        ≤ tv (mix K (Pt y)) (mix K (PH y)) + tv (mix K (PH y)) (mix (KH y) (PH y)) :=
          tv_triangle _ _ _
      _ ≤ tv (Pt y) (PH y) + ∑ l, PH y l * tv (K l) (KH y l) :=
          add_le_add (tv_mix_le hK _ _) (tv_mix_mix_le K (KH y) (hPH y).1)
      _ = tv (PH y) (Pt y) + ∑ l, PH y l * tv (KH y l) (K l) := by
          rw [tv_comm]
          congr 1
          exact Finset.sum_congr rfl fun l _ => by rw [tv_comm]
  -- the posterior gap
  have h1 : ∑ y, P y * tv (PH y) (Pt y) ≤ Real.sqrt (ε₄ / 2) := by
    refine le_trans (sum_mul_tv_le_sqrt hP (fun y _ => hPH y) (fun y _ => hPt y)
      (fun y _ => hacP y)) (Real.sqrt_le_sqrt ?_)
    linarith
  -- the mediation gap, as a single expectation over `Y' × Λ'`
  have h2 : ∑ y, P y * ∑ l, PH y l * tv (KH y l) (K l) ≤ Real.sqrt (εmed / 2) := by
    have hjoint := sum_mul_tv_le_sqrt (jointWeight_mem hP hPH)
      (p := fun p : Y' × Λ' => KH p.1 p.2) (q := fun p : Y' × Λ' => K p.2)
      (fun p _ => hKH p.1 p.2) (fun p _ => hK p.2) (fun p _ => hacK p.1 p.2)
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hjoint
    simp only at hjoint
    have e1 : ∑ y, P y * ∑ l, PH y l * tv (KH y l) (K l)
        = ∑ y, ∑ l, P y * PH y l * tv (KH y l) (K l) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1]
    refine le_trans hjoint (Real.sqrt_le_sqrt ?_)
    have : ∑ y, ∑ l, P y * PH y l * klFin (KH y l) (K l) ≤ εmed := hmed
    linarith
  calc ∑ y, P y * tv (mix K (Pt y)) (mix (KH y) (PH y))
      ≤ ∑ y, P y * (tv (PH y) (Pt y) + ∑ l, PH y l * tv (KH y l) (K l)) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpt y) (hP.1 y)
    _ = ∑ y, P y * tv (PH y) (Pt y) + ∑ y, P y * ∑ l, PH y l * tv (KH y l) (K l) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ Real.sqrt (ε₄ / 2) + Real.sqrt (εmed / 2) := add_le_add h1 h2
    _ = Real.sqrt (εmed / 2) + Real.sqrt (ε₄ / 2) := add_comm _ _

/-! ### S5(ii): the expected miss under the agent's posterior, assembled -/

variable {Ω : Type*} {Λ' Y' : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype Λ'] [Fintype Y'] [MeasurableSpace Λ'] [MeasurableSpace Y']
  [MeasurableSingletonClass Λ'] [MeasurableSingletonClass Y']

/-- **The true posterior** `P^H(λ | y) = P(λ, y) / P(y)` of the joint law of `(Λ, Y)` as a
carrier-(i) family (junk `0` at a null `y`, where nothing below reads it).
Source: [[generalization-final]] P5(i) l. 125 (`P^H(λ | X_{≤t})`)
Kind: D
Fidelity: exact under `pm1 μ Y y ≠ 0` -/
def truePost (μ : Measure Ω) (Λ : Ω → Λ') (Y : Ω → Y') (y : Y') (l : Λ') : ℝ :=
  pm2 μ Λ Y l y / pm1 μ Y y

/-- `P(λ, y) ≤ P(y)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm2_le_pm1 (Λ : Ω → Λ') (Y : Ω → Y') (l : Λ') (y : Y') :
    pm2 μ Λ Y l y ≤ pm1 μ Y y :=
  measureReal_mono Set.inter_subset_right

/-- At a null `y` every cell `P(λ, y)` vanishes.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pm2_eq_zero_of_pm1_eq_zero {Λ : Ω → Λ'} {Y : Ω → Y'} {y : Y'} (hy : pm1 μ Y y = 0)
    (l : Λ') : pm2 μ Λ Y l y = 0 :=
  le_antisymm (hy ▸ pm2_le_pm1 Λ Y l y) (pm2_nonneg (μ := μ) Λ Y l y)

/-- The true posterior at a positive-mass `y` is a distribution on `Λ'`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truePost_mem {Λ : Ω → Λ'} {Y : Ω → Y'} (hΛ : Measurable Λ) {y : Y'}
    (hy : pm1 μ Y y ≠ 0) : truePost μ Λ Y y ∈ stdSimplex ℝ Λ' := by
  refine ⟨fun l => div_nonneg (pm2_nonneg (μ := μ) Λ Y l y) (pm1_nonneg (μ := μ) Y y), ?_⟩
  unfold truePost
  rw [← Finset.sum_div, sum_pm2_x hΛ y, div_self hy]

/-- **The agent's expected miss is the true one plus at most the expected `tv`**:
`∑_{λ,y} P(λ, y)(1 − Pt(λ | y)) ≤ expMiss + ∑_y P(y) · tv (P^H(· | y)) (Pt y)` — the transfer
`1 − P_t(true | y) ≤ 1 − P^H(true | y) + tv` in expectation (`sub_le_tv` cell by cell).
Source: [[generalization-final]] P5(ii) l. 125 ("the transfer `1 − P_t(true|y) ≤ 1 − P^H(true|y)
+ tv`")
Kind: P
Fidelity: exact (in expectation over the joint) -/
theorem agentMiss_le_expMiss_add_tv {Λ : Ω → Λ'} {Y : Ω → Y'} (hΛ : Measurable Λ)
    {Pt : Y' → Λ' → ℝ} (hPt : ∀ y, pm1 μ Y y ≠ 0 → Pt y ∈ stdSimplex ℝ Λ') :
    ∑ l, ∑ y, pm2 μ Λ Y l y * (1 - Pt y l)
      ≤ expMiss μ Λ Y + ∑ y, pm1 μ Y y * tv (truePost μ Λ Y y) (Pt y) := by
  unfold expMiss
  have key : ∀ y, ∑ l, pm2 μ Λ Y l y * (1 - Pt y l)
      ≤ ∑ l, pm2 μ Λ Y l y * (1 - pm2 μ Λ Y l y / pm1 μ Y y)
        + pm1 μ Y y * tv (truePost μ Λ Y y) (Pt y) := by
    intro y
    by_cases hy : pm1 μ Y y = 0
    · simp [pm2_eq_zero_of_pm1_eq_zero hy, hy]
    · have hT := truePost_mem hΛ hy
      have hterm : ∀ l, pm2 μ Λ Y l y * (1 - Pt y l)
          = pm2 μ Λ Y l y * (1 - pm2 μ Λ Y l y / pm1 μ Y y)
            + pm1 μ Y y * (truePost μ Λ Y y l * (truePost μ Λ Y y l - Pt y l)) := by
        intro l
        unfold truePost
        field_simp
        ring
      rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_add_distrib, ← Finset.mul_sum]
      refine add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ?_ (pm1_nonneg (μ := μ) Y y))
      calc ∑ l, truePost μ Λ Y y l * (truePost μ Λ Y y l - Pt y l)
          ≤ ∑ l, truePost μ Λ Y y l * tv (truePost μ Λ Y y) (Pt y) :=
            Finset.sum_le_sum fun l _ =>
              mul_le_mul_of_nonneg_left (sub_le_tv hT (hPt y hy) l) (hT.1 l)
        _ = tv (truePost μ Λ Y y) (Pt y) := by rw [← Finset.sum_mul, hT.2, one_mul]
  have hA : ∑ l, ∑ y, pm2 μ Λ Y l y * (1 - Pt y l) = ∑ y, ∑ l, pm2 μ Λ Y l y * (1 - Pt y l) :=
    Finset.sum_comm
  have hB : ∑ l, ∑ y, pm2 μ Λ Y l y * (1 - pm2 μ Λ Y l y / pm1 μ Y y)
      = ∑ y, ∑ l, pm2 μ Λ Y l y * (1 - pm2 μ Λ Y l y / pm1 μ Y y) := Finset.sum_comm
  rw [hA, hB, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun y _ => key y

/-- **The S5(ii) assembly, miss form** (P5(ii) l. 125): under H4 in the form
`∑_y P(y) · klFin (P^H(· | y)) (Pt y) ≤ ε₄` (with `P^H(· | y) ≪ Pt y` at every positive-mass `y`),
the expected posterior miss of the truth under the agent's posterior is at most
`H[Λ | Y ; μ] + √(ε₄/2)`: the transfer to the true posterior, the min-entropy step
(`expMiss_le_condEntropy`), and Pinsker + Jensen on the expected `tv`.
Source: [[generalization-final]] S5(ii) l. 73, P5(ii) l. 125; mandate Target 6(iii)
Kind: C
Fidelity: exact (the assembly, with the true posterior defined from the measure)
Hyps: (a) all — H4 is the claim's antecedent; simplex membership and absolute continuity of the
agent's posterior are the conditions Pinsker needs -/
theorem expected_miss_assembly {Λ : Ω → Λ'} {Y : Ω → Y'} (hΛ : Measurable Λ) (hY : Measurable Y)
    {Pt : Y' → Λ' → ℝ} (hPt : ∀ y, pm1 μ Y y ≠ 0 → Pt y ∈ stdSimplex ℝ Λ')
    (hac : ∀ y, pm1 μ Y y ≠ 0 → AbsCont (truePost μ Λ Y y) (Pt y))
    {ε₄ : ℝ} (h₄ : ∑ y, pm1 μ Y y * klFin (truePost μ Λ Y y) (Pt y) ≤ ε₄) :
    ∑ l, ∑ y, pm2 μ Λ Y l y * (1 - Pt y l) ≤ H[Λ | Y ; μ] + Real.sqrt (ε₄ / 2) := by
  have hP : pm1 μ Y ∈ stdSimplex ℝ Y' := ⟨fun y => pm1_nonneg (μ := μ) Y y, sum_pm1 hY⟩
  have htv : ∑ y, pm1 μ Y y * tv (truePost μ Λ Y y) (Pt y) ≤ Real.sqrt (ε₄ / 2) := by
    refine le_trans (sum_mul_tv_le_sqrt hP (fun y hy => truePost_mem hΛ hy) hPt hac)
      (Real.sqrt_le_sqrt ?_)
    linarith
  linarith [agentMiss_le_expMiss_add_tv hΛ hPt, expMiss_le_condEntropy (μ := μ) hΛ hY]

/-- **The S5(ii) assembly, error form** — the mandate's `E[err_t(C_k)] ≤ M(ε_red + ν_k + √(ε₄/2))`:
for the concept class `Λ_C = f ∘ Λ`, data `X_{≤t}`, the agent's posterior `Pt` on the class, a
profile of within-action range `M ≥ 0` and a nonempty menu, the expected sup-norm error of the
agent's posterior against the truth (expectation over the joint of `(Λ_C, X_{≤t})`) is at most
`M · (ε_red + H[Λ_C | ⟨X_k, X_{≤t}⟩] + √(ε₄/2))` when `EIG(Λ) ≤ ε_red` and H4 holds. Route:
`err ≤ M · (1 − Pt(true | y))` pointwise (`err_le_mul_one_sub`), the miss assembly, and
`H[Λ_C | X_{≤t}] ≤ EIG + ν` (`condEntropy_le_eig_add_noise`).
Source: [[generalization-final]] S5 l. 73 ("mediation buys calibration, redundancy buys
coverage"), P5(ii) l. 125; mandate Target 6(iii) ("Assemble … `E[err_t(C_k)] ≤ M(ε_red + ν_k
+ √(ε₄/2))`")
Kind: C
Fidelity: exact (the assembly; `ε_red` enters as a stated bound on `EIG`)
Hyps: (a) all — `EIG ≤ ε_red` and H4 are the claim's antecedents; `0 ≤ M` and the range bound are
the profile's; simplex membership and absolute continuity are Pinsker's conditions -/
theorem expected_err_assembly {S T C α : Type} [Fintype S] [Fintype T] [Fintype C]
    [DecidableEq C] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace C]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass C]
    {Λ : Ω → S} {Xk : Ω → T} {Xle : Ω → Y'} (hΛ : Measurable Λ) (hXk : Measurable Xk)
    (hXle : Measurable Xle) (f : S → C)
    {Pt : Y' → C → ℝ} (hPt : ∀ y, pm1 μ Xle y ≠ 0 → Pt y ∈ stdSimplex ℝ C)
    (hac : ∀ y, pm1 μ Xle y ≠ 0 → AbsCont (truePost μ (f ∘ Λ) Xle y) (Pt y))
    {ε₄ εred M : ℝ} (h₄ : ∑ y, pm1 μ Xle y * klFin (truePost μ (f ∘ Λ) Xle y) (Pt y) ≤ ε₄)
    (hred : EIG Λ Xk Xle μ ≤ εred) {Vbar : α → C → ℝ} (hM : ∀ a c c', Vbar a c - Vbar a c' ≤ M)
    (hM0 : 0 ≤ M) (A : Finset α) (hA : A.Nonempty) :
    ∑ c, ∑ y, pm2 μ (f ∘ Λ) Xle c y * err (Pt y) Vbar c A hA
      ≤ M * (εred + H[f ∘ Λ | (⟨Xk, Xle⟩ : Ω → T × Y') ; μ] + Real.sqrt (ε₄ / 2)) := by
  have hfΛ : Measurable (f ∘ Λ) := (measurable_of_countable f).comp hΛ
  have hmiss := expected_miss_assembly (μ := μ) hfΛ hXle hPt hac h₄
  have hH := condEntropy_le_eig_add_noise (μ := μ) hΛ hXk hXle f
  have hpt : ∀ c y, pm2 μ (f ∘ Λ) Xle c y * err (Pt y) Vbar c A hA
      ≤ pm2 μ (f ∘ Λ) Xle c y * (M * (1 - Pt y c)) := by
    intro c y
    by_cases hy : pm1 μ Xle y = 0
    · rw [pm2_eq_zero_of_pm1_eq_zero hy, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (pm2_nonneg (μ := μ) (f ∘ Λ) Xle c y)
      unfold err
      rw [Finset.sup'_le_iff]
      intro a _
      exact err_le_mul_one_sub (hPt y hy) hM a
  calc ∑ c, ∑ y, pm2 μ (f ∘ Λ) Xle c y * err (Pt y) Vbar c A hA
      ≤ ∑ c, ∑ y, pm2 μ (f ∘ Λ) Xle c y * (M * (1 - Pt y c)) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun y _ => hpt c y
    _ = M * ∑ c, ∑ y, pm2 μ (f ∘ Λ) Xle c y * (1 - Pt y c) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ M * (H[f ∘ Λ | Xle ; μ] + Real.sqrt (ε₄ / 2)) := mul_le_mul_of_nonneg_left hmiss hM0
    _ ≤ M * (εred + H[f ∘ Λ | (⟨Xk, Xle⟩ : Ω → T × Y') ; μ] + Real.sqrt (ε₄ / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        unfold EIG at hred
        unfold EIG at hH
        linarith

end

end Cleanroom.Info.InfoVoiLatents.Mediation
