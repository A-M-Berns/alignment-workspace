import Cleanroom.Decision.DpTwoLesions.InteriorReal

/-!
# T5 — The Corollary: the limit of the fixed points is not the fixed point of the limit

The grip family `δ ↦ P.withGrip δ` made explicit (`kδ`, `kcCδ`, the quadratic's coefficients
`qAδ`, `qBδ`, `qEδ`, the roots `rootLo`, `rootHi`), the pointwise limit `Δ₀(p) = lim_{δ→0⁺} Δ_δ(p)`
**derived** (reading one: `Δ₀ = 0` on `(0, 1)`, `β(1−ρ)(γ₁−γ₀)` at `0`, `βρ(γ₁−γ₀)` at `1`),
`Δ₀`'s unique fixed point `0` under (H), and reading two: for all small `δ` the fixed points are
`{0, p̌(δ), p̂(δ)}` with `p̌(δ) → 0` and `p̂(δ) → 1` — because the root formulas are continuous at
`δ = 0` with `discrim → α² > 0` and vertex `→ ½`. The two readings' limit sets, `{0}` and
`{0, 1}`, differ.
Serves [[dp-two-lesions-mandate]] T5 (dp-core-076).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Set Filter Topology

namespace DlParams

variable (P : DlParams ℝ)

/-! ## The grip family, explicit -/

/-- `κ` at grip `δ`: `1 − (ρ + ρA)δ`. Source: doc §3 (`κ`). Kind: D -/
def kδ (δ : ℝ) : ℝ := 1 - (P.ρ + P.ρA) * δ

/-- `κc_C` at grip `δ`. Source: [[double-lesion]]. Kind: D -/
def kcCδ (δ : ℝ) : ℝ := P.ρ * (1 - δ) * P.γ₁ + (P.ρA * (1 - δ) + 1 - P.ρ - P.ρA) * P.γ₀

/-- `qA` at grip `δ`. Source: mandate §3.6. Kind: D -/
def qAδ (δ : ℝ) : ℝ := P.α * (P.kδ δ) ^ 2

/-- `qB` at grip `δ`. Source: mandate §3.6. Kind: D -/
def qBδ (δ : ℝ) : ℝ :=
  P.β * (-(P.ρ * δ) * P.γ₁ * P.kδ δ + P.kcCδ δ * (P.ρA * δ) - (P.ρA * δ) * P.γ₀ * P.kδ δ +
    P.kcCδ δ * (P.ρ * δ)) +
  P.α * P.kδ δ * (P.ρ * δ - P.ρA * δ - P.kδ δ)

/-- `qE` at grip `δ`. Source: mandate §3.6. Kind: D -/
def qEδ (δ : ℝ) : ℝ :=
  P.β * (P.ρ * δ) * (P.γ₁ * (P.ρA * δ + P.kδ δ) - P.ρA * δ * P.γ₀ - P.kcCδ δ) -
  P.α * (P.ρ * δ) * (P.ρA * δ + P.kδ δ)

/-- The discriminant at grip `δ`. Source: mandate §3.6. Kind: D -/
def discδ (δ : ℝ) : ℝ := discrim (P.qAδ δ) (P.qBδ δ) (P.qEδ δ)

/-- **`p̌(δ)`**, the smaller root of the quadratic at grip `δ` (a fixed point in the regime).
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) (`p̌(δ)`)
Kind: D -/
noncomputable def rootLo (δ : ℝ) : ℝ := (-P.qBδ δ - Real.sqrt (P.discδ δ)) / (2 * P.qAδ δ)

/-- **`p̂(δ)`**, the larger root. Source: doc §4 Proposition 3(iii) (`p̂(δ)`). Kind: D -/
noncomputable def rootHi (δ : ℝ) : ℝ := (-P.qBδ δ + Real.sqrt (P.discδ δ)) / (2 * P.qAδ δ)

/-- The fields of `P.withGrip δ` for `δ ∈ (0, 1]`. Source: none: infrastructure. Kind: L -/
theorem withGrip_fields {δ : ℝ} (hδ : 0 < δ ∧ δ ≤ 1) :
    (P.withGrip δ).ρ = P.ρ ∧ (P.withGrip δ).ρA = P.ρA ∧ (P.withGrip δ).δL = δ ∧
    (P.withGrip δ).δA = δ ∧ (P.withGrip δ).γ₁ = P.γ₁ ∧ (P.withGrip δ).γ₀ = P.γ₀ ∧
    (P.withGrip δ).α = P.α ∧ (P.withGrip δ).β = P.β := by
  unfold withGrip; rw [dif_pos hδ]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `κ` of `P.withGrip δ`. Source: none: infrastructure. Kind: L -/
theorem withGrip_kappa {δ : ℝ} (hδ : 0 < δ ∧ δ ≤ 1) : (P.withGrip δ).kappa = P.kδ δ := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := P.withGrip_fields hδ
  unfold kappa kδ; rw [h1, h2, h3, h4]; ring

/-- `κc_C` of `P.withGrip δ`. Source: none: infrastructure. Kind: L -/
theorem withGrip_kcC {δ : ℝ} (hδ : 0 < δ ∧ δ ≤ 1) : (P.withGrip δ).kcC = P.kcCδ δ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := P.withGrip_fields hδ
  unfold kcC kcCδ; rw [h1, h2, h3, h4, h5, h6]

/-- The quadratic's coefficients of `P.withGrip δ`. Source: none: infrastructure. Kind: L -/
theorem withGrip_q {δ : ℝ} (hδ : 0 < δ ∧ δ ≤ 1) :
    (P.withGrip δ).qA = P.qAδ δ ∧ (P.withGrip δ).qB = P.qBδ δ ∧ (P.withGrip δ).qE = P.qEδ δ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := P.withGrip_fields hδ
  have hk := P.withGrip_kappa hδ
  have hc := P.withGrip_kcC hδ
  refine ⟨?_, ?_, ?_⟩
  · unfold qA qAδ; rw [h7, hk]
  · unfold qB qBδ; rw [h1, h2, h3, h4, h5, h6, h7, h8, hk, hc]
  · unfold qE qEδ; rw [h1, h2, h3, h4, h5, h6, h7, h8, hk, hc]

/-- (H) does not depend on the grip. Source: none: infrastructure. Kind: L -/
theorem withGrip_hypH {δ : ℝ} (hδ : 0 < δ ∧ δ ≤ 1) : (P.withGrip δ).HypH ↔ P.HypH := by
  obtain ⟨h1, -, -, -, h5, h6, h7, h8⟩ := P.withGrip_fields hδ
  unfold HypH; rw [h1, h5, h6, h7, h8]

/-- The discriminant of `P.withGrip δ`. Source: none: infrastructure. Kind: L -/
theorem withGrip_discrim {δ : ℝ} (hδ : 0 < δ ∧ δ ≤ 1) :
    discrim (P.withGrip δ).qA (P.withGrip δ).qB (P.withGrip δ).qE = P.discδ δ := by
  obtain ⟨hA, hB, hE⟩ := P.withGrip_q hδ
  unfold discδ; rw [hA, hB, hE]

/-! ## Values and continuity at `δ = 0` -/

/-- `kδ 0 = 1`. Source: none: infrastructure. Kind: L -/
@[simp] theorem kδ_zero : P.kδ 0 = 1 := by simp [kδ]

/-- `qAδ 0 = α`. Source: none: infrastructure. Kind: L -/
@[simp] theorem qAδ_zero : P.qAδ 0 = P.α := by simp [qAδ]

/-- `qBδ 0 = −α`. Source: none: infrastructure. Kind: L -/
@[simp] theorem qBδ_zero : P.qBδ 0 = -P.α := by simp [qBδ]

/-- `qEδ 0 = 0`. Source: none: infrastructure. Kind: L -/
@[simp] theorem qEδ_zero : P.qEδ 0 = 0 := by simp [qEδ]

/-- `discδ 0 = α²`. Source: none: infrastructure. Kind: L -/
@[simp] theorem discδ_zero : P.discδ 0 = P.α ^ 2 := by
  simp [discδ, discrim]

/-- `p̌(0) = 0` (the root formula at grip `0`). Source: none: infrastructure. Kind: L -/
theorem rootLo_zero : P.rootLo 0 = 0 := by
  unfold rootLo
  rw [qBδ_zero, discδ_zero, qAδ_zero, Real.sqrt_sq P.α_pos.le]
  simp

/-- `p̂(0) = 1`. Source: none: infrastructure. Kind: L -/
theorem rootHi_zero : P.rootHi 0 = 1 := by
  unfold rootHi
  rw [qBδ_zero, discδ_zero, qAδ_zero, Real.sqrt_sq P.α_pos.le]
  have : P.α ≠ 0 := P.α_pos.ne'
  field_simp
  norm_num

/-- The coefficient functions are continuous. Source: none: infrastructure. Kind: L -/
theorem continuous_q : Continuous P.qAδ ∧ Continuous P.qBδ ∧ Continuous P.qEδ ∧
    Continuous P.discδ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold qAδ kδ; fun_prop
  · unfold qBδ kδ kcCδ; fun_prop
  · unfold qEδ kδ kcCδ; fun_prop
  · unfold discδ discrim qAδ qBδ qEδ kδ kcCδ; fun_prop

/-- The root formulas are continuous at `δ = 0` (where `2qAδ = 2α ≠ 0`).
Source: none: infrastructure
Kind: L -/
theorem continuousAt_roots : ContinuousAt P.rootLo 0 ∧ ContinuousAt P.rootHi 0 := by
  obtain ⟨hA, hB, hE, hD⟩ := P.continuous_q
  have hden : ContinuousAt (fun δ => 2 * P.qAδ δ) 0 := (continuous_const.mul hA).continuousAt
  have hden0 : (fun δ => 2 * P.qAδ δ) 0 ≠ 0 := by simp [P.α_pos.ne']
  have hs : ContinuousAt (fun δ => Real.sqrt (P.discδ δ)) 0 :=
    (Real.continuous_sqrt.comp hD).continuousAt
  constructor
  · exact ((hB.neg.continuousAt).sub hs).div hden hden0
  · exact ((hB.neg.continuousAt).add hs).div hden hden0

/-- Eventually within `𝓝[>] 0`, `0 < δ ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem eventually_grip : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ ≤ 1 := by
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioi (0 : ℝ) := eventually_mem_nhdsWithin
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 :=
    (gt_mem_nhds (zero_lt_one' ℝ)).filter_mono nhdsWithin_le_nhds
  exact (h1.and h2).mono fun δ ⟨a, b⟩ => ⟨a, b.le⟩

/-! ## Reading two: the limit of the fixed points -/

/-- **`p̌(δ) → 0` and `p̂(δ) → 1` as `δ → 0⁺`**: the root formulas are continuous at `0` with
`p̌(0) = 0`, `p̂(0) = 1`.
Source: [[two-lesions-doc-2026-09-18]] §4 Corollary ("`p̌(δ) → 0` and `p̂(δ) → 1`")
Kind: P
Fidelity: exact (the limits of the explicit root formulas; that they are the fixed points for
small `δ` is `corollary_fixedPts_eventually`)
Hyps: none -/
theorem corollary_limits :
    Tendsto P.rootLo (𝓝[>] 0) (𝓝 0) ∧ Tendsto P.rootHi (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨hlo, hhi⟩ := P.continuousAt_roots
  constructor
  · have := hlo.tendsto; rw [P.rootLo_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · have := hhi.tendsto; rw [P.rootHi_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this

/-- **The three-fixed-point regime holds for every sufficiently small grip** (under (H)):
`discrim → α² > 0` and the vertex `→ ½`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(iii) ("the three-fixed-point regime
obtains for `δ` below `δ*`"); Corollary
Kind: P
Fidelity: exact (eventually in `𝓝[>] 0`; the explicit threshold `δ*` is `DeltaStar.lean`)
Hyps: (a) (H) -/
theorem corollary_regime_eventually (hH : P.HypH) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (0 < δ ∧ δ ≤ 1) ∧ (P.withGrip δ).HypH ∧
      0 < discrim (P.withGrip δ).qA (P.withGrip δ).qB (P.withGrip δ).qE ∧
      0 < -(P.withGrip δ).qB / (2 * (P.withGrip δ).qA) ∧
      -(P.withGrip δ).qB / (2 * (P.withGrip δ).qA) < 1 := by
  obtain ⟨hA, hB, hE, hD⟩ := P.continuous_q
  have hα := P.α_pos
  -- discriminant → α² > 0
  have hd : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < P.discδ δ := by
    have h0 : ContinuousAt P.discδ 0 := hD.continuousAt
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) h0.tendsto
    rw [P.discδ_zero] at this
    exact this.eventually (lt_mem_nhds (pow_pos hα 2))
  -- vertex → ½
  have hv : Tendsto (fun δ => -P.qBδ δ / (2 * P.qAδ δ)) (𝓝[>] 0) (𝓝 (1/2)) := by
    have hc : ContinuousAt (fun δ => -P.qBδ δ / (2 * P.qAδ δ)) 0 :=
      (hB.neg.continuousAt).div (continuous_const.mul hA).continuousAt (by simp [hα.ne'])
    have := hc.tendsto
    have h0 : -P.qBδ 0 / (2 * P.qAδ 0) = 1/2 := by
      rw [qBδ_zero, qAδ_zero]; field_simp
    rw [h0] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hv0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < -P.qBδ δ / (2 * P.qAδ δ) :=
    hv.eventually (lt_mem_nhds (by norm_num))
  have hv1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), -P.qBδ δ / (2 * P.qAδ δ) < 1 :=
    hv.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [eventually_grip, hd, hv0, hv1] with δ hδ hd hv0 hv1
  obtain ⟨hA', hB', hE'⟩ := P.withGrip_q hδ
  refine ⟨hδ, (P.withGrip_hypH hδ).mpr hH, ?_, ?_, ?_⟩
  · rw [P.withGrip_discrim hδ]; exact hd
  · rw [hA', hB']; exact hv0
  · rw [hA', hB']; exact hv1

/-- **For every sufficiently small grip the fixed points are exactly `{0, p̌(δ), p̂(δ)}`** with
`0 < p̌(δ) < p̂(δ) < 1` (under (H)) — reading two of the amendment, with the roots the
explicit `rootLo`/`rootHi` whose limits are `0` and `1`.
Source: [[two-lesions-doc-2026-09-18]] §4 Corollary ("the fixed points of the `δ`-problems
converge, as `δ → 0`, to the set `{0, 1}`")
Kind: P
Fidelity: exact
Hyps: (a) (H) -/
theorem corollary_fixedPts_eventually (hH : P.HypH) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (P.withGrip δ).fixedPts = {0, P.rootLo δ, P.rootHi δ} ∧
      0 < P.rootLo δ ∧ P.rootLo δ < P.rootHi δ ∧ P.rootHi δ < 1 := by
  filter_upwards [P.corollary_regime_eventually hH] with δ ⟨hδ, hH', hd, hv0, hv1⟩
  obtain ⟨hA', hB', hE'⟩ := P.withGrip_q hδ
  have hs0 : 0 < Real.sqrt (P.discδ δ) := by
    rw [← P.withGrip_discrim hδ]; exact Real.sqrt_pos.mpr hd
  have hs : discrim (P.withGrip δ).qA (P.withGrip δ).qB (P.withGrip δ).qE =
      Real.sqrt (P.discδ δ) * Real.sqrt (P.discδ δ) := by
    rw [P.withGrip_discrim hδ]
    exact (Real.mul_self_sqrt (by rw [← P.withGrip_discrim hδ]; exact hd.le)).symm
  obtain ⟨hr0, hr12, hr1, hset⟩ := (P.withGrip δ).fixedPts_eq_of_sqrt hH' hs0 hs hv0 hv1
  unfold rootLo rootHi
  rw [← hA', ← hB']
  exact ⟨hset, hr0, hr12, hr1⟩

/-! ## Reading one: the pointwise limit `Δ₀` -/

/-- **`Δ₀`, the pointwise limit of `Δ_δ` as `δ → 0⁺`**: `β(1−ρ)(γ₁−γ₀)` at `0`, `βρ(γ₁−γ₀)` at
`1`, `0` in between. Defined by its values and **derived** as the limit in
`corollary_delta0_limit`.
Source: [[two-lesions-doc-2026-09-18]] §4 Corollary ("`Δ₀` vanishes on `(0, 1)` and equals
`C(1 − ε_L)` at `0` and `Cε_L` at `1`")
Kind: D -/
noncomputable def Delta0 (p : ℝ) : ℝ :=
  if p = 0 then P.β * (1 - P.ρ) * (P.γ₁ - P.γ₀)
  else if p = 1 then P.β * P.ρ * (P.γ₁ - P.γ₀) else 0

/-- **`Δ_δ(p) → Δ₀(p)` as `δ → 0⁺`, for every `p ∈ [0, 1]`** (reading one: the policy is
fixed, the grip vanishes). Three cases: at the endpoints through `Delta_zero`/`Delta_one`,
in the interior through the closed form, whose denominators tend to `p` and `1 − p`.
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3(ii) ("`Δ(p) → 0` for each `p ∈ (0, 1)`,
while `Δ(0) → C(1 − ε_L)` and `Δ(1) → Cε_L`"); Corollary (`Δ₀`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem corollary_delta0_limit (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun δ => (P.withGrip δ).Delta p) (𝓝[>] 0) (𝓝 (P.Delta0 p)) := by
  rcases hp.1.lt_or_eq with hp0 | hp0
  · rcases hp.2.lt_or_eq with hp1 | hp1
    · -- interior
      have hne0 : p ≠ 0 := hp0.ne'
      have hne1 : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.ne'
      have hval : P.Delta0 p = 0 := by simp [Delta0, hne0, hp1.ne]
      rw [hval]
      -- the explicit function
      let g : ℝ → ℝ := fun δ => P.β * ((P.ρ * δ * P.γ₁ + P.kcCδ δ * p) / (P.ρ * δ + P.kδ δ * p) -
        (P.ρA * δ * P.γ₀ + P.kcCδ δ * (1 - p)) / (P.ρA * δ + P.kδ δ * (1 - p)))
      have hg : ContinuousAt g 0 := by
        have h1 : ContinuousAt (fun δ => P.ρ * δ * P.γ₁ + P.kcCδ δ * p) 0 := by
          unfold kcCδ; fun_prop
        have h2 : ContinuousAt (fun δ => P.ρ * δ + P.kδ δ * p) 0 := by unfold kδ; fun_prop
        have h2' : (fun δ => P.ρ * δ + P.kδ δ * p) 0 ≠ 0 := by simp [kδ, hne0]
        have h3 : ContinuousAt (fun δ => P.ρA * δ * P.γ₀ + P.kcCδ δ * (1 - p)) 0 := by
          unfold kcCδ; fun_prop
        have h4 : ContinuousAt (fun δ => P.ρA * δ + P.kδ δ * (1 - p)) 0 := by unfold kδ; fun_prop
        have h4' : (fun δ => P.ρA * δ + P.kδ δ * (1 - p)) 0 ≠ 0 := by simp [kδ, hne1]
        exact continuousAt_const.mul ((h1.div h2 h2').sub (h3.div h4 h4'))
      have hg0 : g 0 = 0 := by
        simp only [g, mul_zero, zero_mul, zero_add, kδ_zero, one_mul]
        rw [mul_div_cancel_right₀ _ hne0, mul_div_cancel_right₀ _ hne1]
        ring
      have hlim : Tendsto g (𝓝[>] 0) (𝓝 0) := by
        have := hg.tendsto; rw [hg0] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      refine hlim.congr' ?_
      filter_upwards [eventually_grip] with δ hδ
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := P.withGrip_fields hδ
      rw [Delta_eq _ p hp.1 hp.2]
      unfold condSmoke condAbstain
      rw [h1, h2, h3, h4, h5, h6, h8, P.withGrip_kappa hδ, P.withGrip_kcC hδ]
    · -- p = 1
      subst hp1
      have hval : P.Delta0 1 = P.β * P.ρ * (P.γ₁ - P.γ₀) := by simp [Delta0]
      rw [hval]
      let g : ℝ → ℝ := fun δ => P.β * (P.ρ * (P.γ₁ - P.γ₀) / (1 - P.ρA * δ))
      have hg : ContinuousAt g 0 := by
        have h2 : ContinuousAt (fun δ => 1 - P.ρA * δ) 0 := by fun_prop
        have h2' : (fun δ => 1 - P.ρA * δ) 0 ≠ 0 := by simp
        exact continuousAt_const.mul (continuousAt_const.div h2 h2')
      have hg0 : g 0 = P.β * P.ρ * (P.γ₁ - P.γ₀) := by simp [g]; ring
      have hlim : Tendsto g (𝓝[>] 0) (𝓝 (P.β * P.ρ * (P.γ₁ - P.γ₀))) := by
        have := hg.tendsto; rw [hg0] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      refine hlim.congr' ?_
      filter_upwards [eventually_grip] with δ hδ
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := P.withGrip_fields hδ
      rw [Delta_one, h1, h2, h4, h5, h6, h8]
  · -- p = 0
    rw [← hp0]
    have hval : P.Delta0 0 = P.β * (1 - P.ρ) * (P.γ₁ - P.γ₀) := by simp [Delta0]
    rw [hval]
    let g : ℝ → ℝ := fun δ => P.β * ((1 - P.ρ) * (P.γ₁ - P.γ₀) / (1 - P.ρ * δ))
    have hg : ContinuousAt g 0 := by
      have h2 : ContinuousAt (fun δ => 1 - P.ρ * δ) 0 := by fun_prop
      have h2' : (fun δ => 1 - P.ρ * δ) 0 ≠ 0 := by simp
      exact continuousAt_const.mul (continuousAt_const.div h2 h2')
    have hg0 : g 0 = P.β * (1 - P.ρ) * (P.γ₁ - P.γ₀) := by simp [g]; ring
    have hlim : Tendsto g (𝓝[>] 0) (𝓝 (P.β * (1 - P.ρ) * (P.γ₁ - P.γ₀))) := by
      have := hg.tendsto; rw [hg0] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine hlim.congr' ?_
    filter_upwards [eventually_grip] with δ hδ
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := P.withGrip_fields hδ
    rw [Delta_zero, h1, h3, h5, h6, h8]

/-- The best response to an arbitrary penalty function `D` at `p` (the doc's `β(p)` with `D` in
place of `Δ`): `P.bestResp = bestRespOf P.α P.Delta` definitionally.
Source: [[two-lesions-doc-2026-09-18]] §3 (the best response)
Kind: D -/
def bestRespOf (α : ℝ) (D : ℝ → ℝ) (p : ℝ) : Set ℝ :=
  {b | (α > D p → b = 1) ∧ (α < D p → b = 0) ∧ 0 ≤ b ∧ b ≤ 1}

/-- The fixed points in `[0, 1]` of the best-response map of `D`.
Source: doc §3
Kind: D -/
def fixedPtsOf (α : ℝ) (D : ℝ → ℝ) : Set ℝ := {p ∈ Icc 0 1 | p ∈ bestRespOf α D p}

/-- `P.bestResp` is `bestRespOf P.α P.Delta`. Source: none: infrastructure. Kind: L -/
theorem bestResp_eq_bestRespOf : P.bestResp = bestRespOf P.α P.Delta := by
  unfold bestResp bestRespOf; rfl

/-- `P.fixedPts` is `fixedPtsOf P.α P.Delta`. Source: none: infrastructure. Kind: L -/
theorem fixedPts_eq_fixedPtsOf : P.fixedPts = fixedPtsOf P.α P.Delta := by
  unfold fixedPts fixedPtsOf IsFixedPt bestResp bestRespOf; rfl

/-- **`Δ₀`'s best-response map has `0` as its unique fixed point** under (H) — reading one of
the amendment: the ideal evidential agent abstains.
Source: [[two-lesions-doc-2026-09-18]] §4 Corollary ("The best-response map of `Δ₀` has `0` as
its unique fixed point")
Kind: P
Fidelity: exact
Hyps: (a) (H) -/
theorem corollary_delta0_unique (hH : P.HypH) : fixedPtsOf P.α P.Delta0 = {0} := by
  unfold HypH at hH
  have hγ : 0 ≤ P.γ₁ - P.γ₀ := sub_nonneg.mpr P.γ₀_le_γ₁
  have hβγ : 0 ≤ P.β * (P.γ₁ - P.γ₀) := mul_nonneg P.β_pos.le hγ
  have h0 : P.α < P.β * (1 - P.ρ) * (P.γ₁ - P.γ₀) := by
    have := mul_le_mul_of_nonneg_left (min_le_right P.ρ (1 - P.ρ)) hβγ
    linarith [show P.β * (P.γ₁ - P.γ₀) * (1 - P.ρ) = P.β * (1 - P.ρ) * (P.γ₁ - P.γ₀) by ring]
  have h1 : P.α < P.β * P.ρ * (P.γ₁ - P.γ₀) := by
    have := mul_le_mul_of_nonneg_left (min_le_left P.ρ (1 - P.ρ)) hβγ
    linarith [show P.β * (P.γ₁ - P.γ₀) * P.ρ = P.β * P.ρ * (P.γ₁ - P.γ₀) by ring]
  ext p
  simp only [fixedPtsOf, bestRespOf, mem_setOf_eq, mem_Icc, mem_singleton_iff]
  constructor
  · rintro ⟨⟨hp0, hp1⟩, hgt, hlt, -, -⟩
    by_contra hne
    rcases hp1.lt_or_eq with hp1 | hp1
    · have hD : P.Delta0 p = 0 := by simp [Delta0, hne, hp1.ne]
      have := hgt (by rw [hD]; exact P.α_pos)
      exact hp1.ne this
    · subst hp1
      have hD : P.Delta0 1 = P.β * P.ρ * (P.γ₁ - P.γ₀) := by simp [Delta0]
      have := hlt (by rw [hD]; exact h1)
      exact one_ne_zero this
  · rintro rfl
    have hD : P.Delta0 0 = P.β * (1 - P.ρ) * (P.γ₁ - P.γ₀) := by simp [Delta0]
    refine ⟨⟨le_rfl, zero_le_one⟩, fun h => absurd h (by rw [hD]; exact not_lt.mpr h0.le),
      fun _ => rfl, le_rfl, zero_le_one⟩

/-- **The two readings differ**: reading one's fixed-point set `{0}` is not reading two's limit
set `{0, 1}`.
Source: [[two-lesions-doc-2026-09-18]] §4 Corollary; "Two readings of the amendment"
Kind: L (the content is `corollary_delta0_unique` + `corollary_limits`; this is the comparison)
Fidelity: exact -/
theorem corollary_readings_differ (hH : P.HypH) :
    fixedPtsOf P.α P.Delta0 = {0} ∧
    Tendsto P.rootLo (𝓝[>] 0) (𝓝 0) ∧ Tendsto P.rootHi (𝓝[>] 0) (𝓝 1) ∧
    ({0, 1} : Set ℝ) ≠ {0} := by
  refine ⟨P.corollary_delta0_unique hH, (P.corollary_limits).1, (P.corollary_limits).2, ?_⟩
  intro h
  have : (1 : ℝ) ∈ ({0, 1} : Set ℝ) := by simp
  rw [h] at this
  simp at this

end DlParams

end Cleanroom.Decision.DpTwoLesions
