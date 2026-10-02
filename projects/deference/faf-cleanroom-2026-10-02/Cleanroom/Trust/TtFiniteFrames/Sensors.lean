import Cleanroom.Trust.TtFiniteFrames.Blackwell
import Mathlib.Data.Fin.VecNotation

/-!
# Blackwell monotonicity for the corrigibility run's binary sensors

Package `tt-finite-frames`, Target B6 (corr-wf13-010, miri I9.4 and I10.1).

* **(a)** `never_pays_for_garbling`: a T-agent never pays any positive cost to move its sensor
  down the Blackwell order — `bayesValue μ k₂ u − c < bayesValue μ k₁ u` for every garbling `k₂`
  of `k₁` and every `c > 0` (B1).
* **(b)** the **binary sensor** `(α, β)` — `P(press | good) = α`, `P(press | bad) = β` — and the
  **parallelogram**: `(α', β')` is a garbling of `(α, β)` iff `(α', β') = (αp + (1−α)q,
  βp + (1−β)q)` for some `p, q ∈ [0,1]`, the image of the unit square, i.e. the parallelogram
  with vertices `(0,0), (α,β), (1−α,1−β), (1,1)`. Corollaries: proportional suppression
  `(λα, λβ)` and the constant sensors `(c, c)` are garblings; the targeted suppression `(α, β')`
  of `(α, β)` with `α < β` is a garbling iff `α(1−β)/(1−α) ≤ β' ≤ β`, **provided `α ≤ 1/2`** —
  for `α > 1/2` the lower end is `1 − β(1−α)/α` instead (finding B6-corollary in the package
  findings; miri I9.4's instance has `α = 1/20`, so its number stands).
* **(c)** `positive/ddb.md` open problem 3 (Value monotone under garbling for modest frames — the
  corrigibility workflow's own conjecture, corr-wf13-010; DDB fn 15 is only its pointer, and DDB
  §5 lists no such problem: finding F-B6c) is `recorded only`: its naive frame-level reading is
  refuted by G4 (`Weatherson.lean`).
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell

noncomputable section

set_option linter.unusedSectionVars false

variable {W S T : Type} [Fintype W] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

/-! ## (a) never pay for a garbling -/

/-- **Never pays for a garbling.** If `k₂` is a garbling of `k₁`, then for every prior in the
simplex, every menu and every cost `c > 0`, `bayesValue μ k₂ u − c < bayesValue μ k₁ u`: the
garbled sensor at any positive price is strictly worse than the honest one for free.
Source: corr-wf13-010; miri I10.1 ("never pays any cost, however small, to move the sensor down
the Blackwell order")
Kind: L (from B1)
Fidelity: exact
Hyps: (a) `h`, `hμ` -/
theorem never_pays_for_garbling {k₁ : Experiment W S} {k₂ : Experiment W T}
    (h : BlackwellLE k₂ k₁) {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W) {n : ℕ}
    (u : Fin (n + 1) → W → ℝ) {c : ℝ} (hc : 0 < c) :
    bayesValue μ k₂ u - c < bayesValue μ k₁ u := by
  have := moreValuable_of_blackwellLE h μ hμ n u
  linarith

/-! ## (b) binary sensors and the parallelogram -/

/-- **The binary sensor** `(α, β)`: states `0 = good`, `1 = bad`; signals `0 = press`,
`1 = silence`; `P(press | good) = α`, `P(press | bad) = β`.
Source: corr-wf13-010; miri I9.4 (the sensor `(α, β)`)
Kind: D
Fidelity: exact -/
def binarySensor (α β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    Experiment (Fin 2) (Fin 2) where
  k := ![![α, 1 - α], ![β, 1 - β]]
  k_mem := by
    intro w
    fin_cases w
    · refine ⟨fun s => ?_, ?_⟩
      · fin_cases s <;> simp <;> linarith [hα.1, hα.2]
      · simp [Fin.sum_univ_two]
    · refine ⟨fun s => ?_, ?_⟩
      · fin_cases s <;> simp <;> linarith [hβ.1, hβ.2]
      · simp [Fin.sum_univ_two]

/-- The parallelogram membership predicate: `(α', β')` is `(αp + (1−α)q, βp + (1−β)q)` for some
`p, q ∈ [0, 1]`.
Source: miri I9.4 ("the Blackwell parallelogram of `(α, β)`")
Kind: D
Fidelity: exact -/
def InParallelogram (α β α' β' : ℝ) : Prop :=
  ∃ p q : ℝ, p ∈ Set.Icc (0 : ℝ) 1 ∧ q ∈ Set.Icc (0 : ℝ) 1 ∧
    α' = α * p + (1 - α) * q ∧ β' = β * p + (1 - β) * q

/-- **The parallelogram.** `(α', β')` is a garbling of `(α, β)` iff it lies in the image of the
unit square under `(p, q) ↦ (αp + (1−α)q, βp + (1−β)q)` — the parallelogram with vertices
`(0,0), (α,β), (1−α,1−β), (1,1)`. (⇒) `p = g(press ↦ press)`, `q = g(silence ↦ press)`;
(⇐) that channel.
Source: miri I9.4; corr-wf13-010
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem blackwellLE_binarySensor_iff {α β α' β' : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hα' : α' ∈ Set.Icc (0 : ℝ) 1) (hβ' : β' ∈ Set.Icc (0 : ℝ) 1) :
    BlackwellLE (binarySensor α' β' hα' hβ') (binarySensor α β hα hβ) ↔
      InParallelogram α β α' β' := by
  constructor
  · rintro ⟨g, hg, hgar⟩
    refine ⟨g 0 0, g 1 0, ⟨(hg 0).1 0, ?_⟩, ⟨(hg 1).1 0, ?_⟩, ?_, ?_⟩
    · have := (hg 0).2
      rw [Fin.sum_univ_two] at this
      linarith [(hg 0).1 1]
    · have := (hg 1).2
      rw [Fin.sum_univ_two] at this
      linarith [(hg 1).1 1]
    · have := hgar 0 0
      simp [binarySensor, Fin.sum_univ_two] at this
      linarith
    · have := hgar 1 0
      simp [binarySensor, Fin.sum_univ_two] at this
      linarith
  · rintro ⟨p, q, hp, hq, hα'', hβ''⟩
    refine ⟨![![p, 1 - p], ![q, 1 - q]], ?_, ?_⟩
    · intro s
      fin_cases s
      · refine ⟨fun t => ?_, ?_⟩
        · fin_cases t <;> simp <;> linarith [hp.1, hp.2]
        · simp [Fin.sum_univ_two]
      · refine ⟨fun t => ?_, ?_⟩
        · fin_cases t <;> simp <;> linarith [hq.1, hq.2]
        · simp [Fin.sum_univ_two]
    · intro w t
      fin_cases w <;> fin_cases t <;> simp [binarySensor, Fin.sum_univ_two] <;> linarith

/-- **Proportional suppression is a garbling**: `(λα, λβ)` for `λ ∈ [0, 1]` (`p = λ`, `q = 0`).
Source: miri I9.4 ("proportional suppression … strict garblings")
Kind: L
Fidelity: exact -/
theorem inParallelogram_scale {α β lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    InParallelogram α β (lam * α) (lam * β) :=
  ⟨lam, 0, hlam, ⟨le_rfl, zero_le_one⟩, by ring, by ring⟩

/-- **Constant sensors are garblings**: `(c, c)` for `c ∈ [0, 1]` (`p = q = c`).
Source: miri I10.1 ("physically preventing the press … and forcing it … are both constant, hence
maximally garbled, sensors")
Kind: L
Fidelity: exact -/
theorem inParallelogram_const {α β c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    InParallelogram α β c c :=
  ⟨c, c, hc, hc, by ring, by ring⟩

/-- **Targeted suppression, necessity.** If `(α, β')` lies in the parallelogram of `(α, β)` with
`α < 1` and `α ≤ β`, then `α(1−β)/(1−α) ≤ β' ≤ β`. (Holds for every `α < 1`.)
Source: miri I9.4 (the "iff" there; this is the half that holds without `α ≤ 1/2`)
Kind: P
Fidelity: exact (necessity)
Hyps: (a) as stated -/
theorem targeted_necessary {α β β' : ℝ} (hα1 : α < 1) (hαβ : α ≤ β)
    (h : InParallelogram α β α β') : α * (1 - β) / (1 - α) ≤ β' ∧ β' ≤ β := by
  obtain ⟨p, q, hp, hq, hα', hβ'⟩ := h
  have h1α : 0 < 1 - α := by linarith
  -- `(1 − α) q = α (1 − p)`
  have hq' : (1 - α) * q = α * (1 - p) := by linarith
  constructor
  · rw [div_le_iff₀ h1α]
    nlinarith [hp.1, hq.1]
  · nlinarith [hp.2, hq.1, hp.1]

/-- **Targeted suppression, sufficiency (for `α ≤ 1/2`).** If `0 ≤ α ≤ 1/2`, `α < β ≤ 1` and
`α(1−β)/(1−α) ≤ β' ≤ β`, then `(α, β')` lies in the parallelogram of `(α, β)`: take
`p = (β' − L)/(β − L)` with `L = α(1−β)/(1−α)` and `q = α(1−p)/(1−α) ≤ α/(1−α) ≤ 1`. For
`α > 1/2` the constraint `q ≤ 1` bites and the lower end of the admissible `β'` rises to
`1 − β(1−α)/α`: the "iff" of miri I9.4 needs `α ≤ 1/2` (its instance has `α = 1/20`).
Source: miri I9.4 (corrected)
Kind: P
Fidelity: variant: the source's "iff `β' ≥ α(1−β)/(1−α)`" is proved with the implicit upper
bound `β' ≤ β` made explicit and under `α ≤ 1/2`
Hyps: (a) as stated -/
theorem targeted_sufficient {α β β' : ℝ} (hα0 : 0 ≤ α) (hαh : α ≤ 1 / 2) (hαβ : α < β)
    (hβ1 : β ≤ 1) (hL : α * (1 - β) / (1 - α) ≤ β') (hβ' : β' ≤ β) :
    InParallelogram α β α β' := by
  have h1α : 0 < 1 - α := by linarith
  set L := α * (1 - β) / (1 - α) with hLdef
  have hLβ : L < β := by
    rw [hLdef, div_lt_iff₀ h1α]
    nlinarith
  set p := (β' - L) / (β - L) with hpdef
  have hp0 : 0 ≤ p := div_nonneg (by linarith) (by linarith)
  have hp1 : p ≤ 1 := by
    rw [hpdef, div_le_one (by linarith)]
    linarith
  set q := α * (1 - p) / (1 - α) with hqdef
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hα0 (by linarith)) h1α.le
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one h1α]
    nlinarith
  refine ⟨p, q, ⟨hp0, hp1⟩, ⟨hq0, hq1⟩, ?_, ?_⟩
  · rw [hqdef]
    field_simp
    ring
  · -- `β p + (1 − β) q = L + p (β − L) = β'`
    have hβL : β - L ≠ 0 := by linarith
    have key : (1 - β) * q = L * (1 - p) := by
      rw [hqdef, hLdef]; ring
    have hpL : p * (β - L) = β' - L := by
      rw [hpdef, div_mul_cancel₀ _ hβL]
    calc β' = L + p * (β - L) := by linarith
      _ = β * p + (1 - β) * q := by rw [key]; ring

/-- **Targeted suppression, the characterisation (for `α ≤ 1/2`).** For `0 ≤ α ≤ 1/2` and
`α < β ≤ 1`: `(α, β')` is a garbling of `(α, β)` iff `α(1−β)/(1−α) ≤ β' ≤ β`.
Source: miri I9.4 (corrected form)
Kind: C
Fidelity: variant: see `targeted_sufficient`
Hyps: (a) as stated -/
theorem targeted_iff {α β β' : ℝ} (hα0 : 0 ≤ α) (hαh : α ≤ 1 / 2) (hαβ : α < β) (hβ1 : β ≤ 1) :
    InParallelogram α β α β' ↔ (α * (1 - β) / (1 - α) ≤ β' ∧ β' ≤ β) :=
  ⟨targeted_necessary (by linarith) hαβ.le,
    fun h => targeted_sufficient hα0 hαh hαβ hβ1 h.1 h.2⟩

/-! ## Repair round 1: the `α ≥ 1/2` branch of targeted suppression; a Blackwell instance -/

/-- **Targeted suppression, sufficiency for `α ≥ 1/2`.** For `1/2 ≤ α < 1`, `α < β ≤ 1` and
`1 − β(1−α)/α ≤ β' ≤ β`, `(α, β')` lies in the parallelogram: take `q = α(β − β')/(β − α)`
and `p = 1 − (1−α) q / α`. The binding constraint is now `q ≤ 1` (at `β' = 1 − β(1−α)/α`,
`q = 1` and `p = (2α−1)/α`), and `p ≥ 0` follows because
`(1−α) β' − α(1−β) = [α β' − α + β(1−α)] + (2α−1)(β − β') ≥ 0`.
Source: miri I9.4 (corrected; the branch finding F-B6 asserted and audit r1 adversarial N5
asked to be proved)
Kind: P
Fidelity: variant: the `α ≥ 1/2` branch of the corrected I9.4
Hyps: (a) as stated -/
theorem targeted_sufficient_half {α β β' : ℝ} (hαh : 1 / 2 ≤ α) (hα1 : α < 1) (hαβ : α < β)
    (hL : 1 - β * (1 - α) / α ≤ β') (hβ' : β' ≤ β) : InParallelogram α β α β' := by
  have hα0 : 0 < α := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hβα : 0 < β - α := by linarith
  have hα0' := hα0.ne'
  have hβα' := hβα.ne'
  -- the lower bound without division: `(1 − β') α ≤ β (1 − α)`
  have hL' : (1 - β') * α ≤ β * (1 - α) := by
    rw [← le_div_iff₀ hα0]; linarith
  have hkey : (1 - α) * (β - β') ≤ β - α := by
    nlinarith [hL', mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * α - 1) (by linarith : (0 : ℝ) ≤ β - β')]
  set q := α * (β - β') / (β - α) with hqdef
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hα0.le (by linarith)) hβα.le
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one hβα]
    linarith [hL']
  have hp0' : (1 - α) * q ≤ α := by
    have : (1 - α) * q = α * ((1 - α) * (β - β')) / (β - α) := by rw [hqdef]; ring
    rw [this, div_le_iff₀ hβα]
    exact mul_le_mul_of_nonneg_left hkey hα0.le
  set p := 1 - (1 - α) * q / α with hpdef
  have hp0 : 0 ≤ p := by
    rw [hpdef, sub_nonneg, div_le_one hα0]; exact hp0'
  have hp1 : p ≤ 1 := by
    rw [hpdef]; exact sub_le_self _ (div_nonneg (mul_nonneg h1α.le hq0) hα0.le)
  refine ⟨p, q, ⟨hp0, hp1⟩, ⟨hq0, hq1⟩, ?_, ?_⟩
  · rw [hpdef]; field_simp; ring
  · rw [hpdef, hqdef]; field_simp; ring

/-- **Targeted suppression, the characterisation for `α ≥ 1/2`.** For `1/2 ≤ α < 1` and
`α < β ≤ 1`: `(α, β')` is a garbling of `(α, β)` iff `1 − β(1−α)/α ≤ β' ≤ β`. Necessity:
with `(1−α) q = α (1−p)`, `β(1−α) − (1−β') α = (β − α)(1 − q) ≥ 0`. Together with
`targeted_iff` (`α ≤ 1/2`) this is the complete corrected form of miri I9.4's "iff".
Source: miri I9.4 (corrected form, `α ≥ 1/2` branch; finding F-B6)
Kind: C
Fidelity: variant: see `targeted_sufficient_half`
Hyps: (a) as stated -/
theorem targeted_iff_half {α β β' : ℝ} (hαh : 1 / 2 ≤ α) (hα1 : α < 1) (hαβ : α < β)
    (hβ1 : β ≤ 1) :
    InParallelogram α β α β' ↔ (1 - β * (1 - α) / α ≤ β' ∧ β' ≤ β) := by
  constructor
  · intro h
    refine ⟨?_, (targeted_necessary hα1 hαβ.le h).2⟩
    obtain ⟨p, q, hp, hq, hα', hβ'⟩ := h
    have hα0 : 0 < α := by linarith
    have hβα : 0 < β - α := by linarith
    have hq' : (1 - α) * q = α * (1 - p) := by linarith
    have hβq : β * ((1 - α) * q) = β * (α * (1 - p)) := by rw [hq']
    have hαβ' : α * β' = α * (β * p + (1 - β) * q) := by rw [hβ']
    have hgoal : (1 - β') * α ≤ β * (1 - α) := by
      nlinarith [hβq, hαβ', mul_nonneg hβα.le (sub_nonneg.2 hq.2)]
    have : 1 - β' ≤ β * (1 - α) / α := (le_div_iff₀ hα0).2 hgoal
    linarith
  · intro h
    exact targeted_sufficient_half hαh hα1 hαβ h.1 h.2

/-- The perfect sensor `(1, 0)` is not a garbling of the constant sensor `(1/2, 1/2)`: the
latter's parallelogram is the diagonal segment.
Source: none: audit r1 adversarial N10 (instance for `blackwell_iff`)
Kind: N+
Fidelity: n/a -/
theorem perfect_not_garbling_of_constant :
    ¬ BlackwellLE (binarySensor (1 : ℝ) 0 ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩)
      (binarySensor (1 / 2 : ℝ) (1 / 2) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩) := by
  intro h
  obtain ⟨p, q, _, _, h1, h2⟩ := (blackwellLE_binarySensor_iff _ _ _ _).1 h
  linarith

/-- **Blackwell's converse on an instance.** B2 produces a full-support prior and a menu on
which the perfect sensor is strictly more valuable than the constant one — the converse half of
`blackwell_iff` exercised on a concrete non-garbling.
Source: none: audit r1 adversarial N10 (instance for `blackwell_iff`)
Kind: N+
Fidelity: n/a -/
theorem perfect_beats_constant :
    ∃ μ : Fin 2 → ℝ, μ ∈ stdSimplex ℝ (Fin 2) ∧ (∀ w, 0 < μ w) ∧
      ∃ (n : ℕ) (u : Fin (n + 1) → Fin 2 → ℝ),
        bayesValue μ (binarySensor (1 / 2 : ℝ) (1 / 2) ⟨by norm_num, by norm_num⟩
            ⟨by norm_num, by norm_num⟩) u <
          bayesValue μ (binarySensor (1 : ℝ) 0 ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩) u :=
  exists_prior_menu_of_not_blackwellLE perfect_not_garbling_of_constant

end

end Cleanroom.Trust.TtFiniteFrames
