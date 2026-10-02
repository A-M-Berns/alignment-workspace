import Cleanroom.Found.LiAsympCalc.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# H2. The amplifier: integrals in Lean, affine rigidity, and the bounded impostor

Target H2 of [[li-asymp-calc-mandate]] (trust-lab-2-044, 068; `lean-deference`
`FrozenDeliberation.lean:123–156`; [[AUDIT]] §3.7, where the integral was hand-evaluated).

* The two cut integrals of `amp c e = (1 + 2c) e - c` are computed by `intervalIntegral`
  (`integral_id`, `integral_const`), and the sign lemmas are restated with the integral as the
  cut value.
* (a) **Affine rigidity**: an affine `g` into `[0,1]` passing both cut families is the identity.
* (b) **The bounded impostor** `gimp e = min (2e) 1`: continuous, `[0,1] → [0,1]`, not the
  identity, passes both cut families — so the cut families alone do not pin the amplifier
  down; affinity is load-bearing in (a).
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology intervalIntegral

/-! ### Integrals of affine functions -/

/-- `∫_a^b (k e + m) de = k (b² − a²)/2 + m (b − a)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem integral_linear (a b k m : ℝ) :
    ∫ e in a..b, (k * e + m) = k * (b ^ 2 - a ^ 2) / 2 + m * (b - a) := by
  have hf : IntervalIntegrable (fun e : ℝ => k * e) MeasureTheory.volume a b :=
    (by fun_prop : Continuous (fun e : ℝ => k * e)).intervalIntegrable a b
  have hg : IntervalIntegrable (fun _ : ℝ => m) MeasureTheory.volume a b :=
    continuous_const.intervalIntegrable a b
  have h1 : ∫ e in a..b, (k * e + m) = (∫ e in a..b, k * e) + ∫ e in a..b, m :=
    integral_add hf hg
  rw [h1, integral_const_mul, integral_id, integral_const, smul_eq_mul]
  ring

/-! ### The amplifier integrals -/

/-- `∫_t^1 amp c e de = (1 + 2c)(1 - t²)/2 - c(1 - t)`, in `intervalIntegral`.
Source: `lean-deference` `FrozenDeliberation.lean:123–156`; [[AUDIT]] §3.7
Kind: P
Fidelity: exact (the integration step the earlier Lean hand-evaluated)
Hyps: (a) none -/
theorem integral_amp_upper (c t : ℝ) :
    ∫ e in t..1, amp c e = (1 + 2 * c) * (1 - t ^ 2) / 2 - c * (1 - t) := by
  have h : ∫ e in t..1, amp c e = ∫ e in t..1, ((1 + 2 * c) * e + (-c)) := by
    apply integral_congr
    intro e _
    simp only [amp]
    ring
  rw [h, integral_linear]
  ring

/-- `∫_0^t amp c e de = (1 + 2c) t²/2 - c t`.
Source: `lean-deference` `FrozenDeliberation.lean:123–156`; [[AUDIT]] §3.7
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem integral_amp_lower (c t : ℝ) :
    ∫ e in (0 : ℝ)..t, amp c e = (1 + 2 * c) * t ^ 2 / 2 - c * t := by
  have h : ∫ e in (0 : ℝ)..t, amp c e = ∫ e in (0 : ℝ)..t, ((1 + 2 * c) * e + (-c)) := by
    apply integral_congr
    intro e _
    simp only [amp]
    ring
  rw [h, integral_linear]
  ring

/-- Upper cut, with the integral as the cut value: `t(1 - t) ≤ ∫_t^1 amp c` for `c ≥ 0`,
`t ∈ [0,1]` (the gap is `(1-t)/2 · ((1-t) + 2ct)`).
Source: `lean-deference` `FrozenDeliberation.lean` (`amp_upper_cut_nonneg`), restated
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem amp_upper_cut {c t : ℝ} (hc : 0 ≤ c) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t * (1 - t) ≤ ∫ e in t..1, amp c e := by
  rw [integral_amp_upper]
  nlinarith [ht.1, ht.2, mul_nonneg hc (mul_nonneg ht.1 (sub_nonneg.2 ht.2))]

/-- Lower cut, with the integral as the cut value: `∫_0^t amp c ≤ t²` for `c ≥ 0`, `t ∈ [0,1]`.
Source: `lean-deference` `FrozenDeliberation.lean`, restated
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem amp_lower_cut {c t : ℝ} (hc : 0 ≤ c) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ e in (0 : ℝ)..t, amp c e ≤ t ^ 2 := by
  rw [integral_amp_lower]
  nlinarith [ht.1, ht.2, mul_nonneg hc (mul_nonneg ht.1 (sub_nonneg.2 ht.2))]

/-! ### (a) Affine rigidity -/

/-- **Affine rigidity** (H2 (a)): if `g e = α e + β` maps `[0,1]` into `[0,1]` and passes both
cut families — `∫_0^t g ≤ t²` and `t(1-t) ≤ ∫_t^1 g` for every `t ∈ [0,1]` — then
`α = 1 ∧ β = 0`. The range hypothesis is used (`β ≥ 0`, `α + β ≤ 1`); the cuts give `β ≤ 0`
(lower cut at `t = β/4`) and `α ≥ 1` (upper cut at `t = (1+α)/2`). Read it as "the only
`[0,1]`-valued affine map passing both cuts is the identity", **not** as "the cuts pin the
amplifier": every amplifier `amp c`, `c > 0`, passes both cut families and fails only the range
(`amp_passes_cuts_fails_range`). The hypothesis package is inhabited by the identity
(`affine_rigidity_witness`), which by this theorem is its only inhabitant. This is exactly
trust-lab-068's statement (range hypothesis included), now kernel-checked.
Source: trust-lab-068 (the rigidity claim, with the range hypothesis); trust-lab-2-044 (integral hygiene)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem affine_rigidity {α β : ℝ}
    (hrange : ∀ e ∈ Set.Icc (0 : ℝ) 1, α * e + β ∈ Set.Icc (0 : ℝ) 1)
    (hlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∫ e in (0 : ℝ)..t, (α * e + β) ≤ t ^ 2)
    (hup : ∀ t ∈ Set.Icc (0 : ℝ) 1, t * (1 - t) ≤ ∫ e in t..1, (α * e + β)) :
    α = 1 ∧ β = 0 := by
  simp only [integral_linear] at hlow hup
  have h0 : 0 ≤ β ∧ β ≤ 1 := by
    have := hrange 0 (Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩)
    rw [Set.mem_Icc] at this
    constructor <;> linarith [this.1, this.2]
  have h1 : 0 ≤ α + β ∧ α + β ≤ 1 := by
    have := hrange 1 (Set.mem_Icc.2 ⟨zero_le_one, le_rfl⟩)
    rw [Set.mem_Icc] at this
    constructor <;> linarith [this.1, this.2]
  have hup0 : 0 ≤ α / 2 + β := by
    have := hup 0 (Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩)
    norm_num at this
    linarith
  have hβ : β = 0 := by
    by_contra hne
    have hβpos : 0 < β := lt_of_le_of_ne h0.1 (Ne.symm hne)
    have ht : β / 4 ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.2 ⟨by linarith, by linarith [h0.2]⟩
    have hl := hlow (β / 4) ht
    have hα6 : (0 : ℝ) < α + 6 := by linarith [h0.2]
    nlinarith [hl, mul_pos (mul_pos hβpos hβpos) hα6]
  subst hβ
  refine ⟨?_, rfl⟩
  have hα1 : α ≤ 1 := by linarith [h1.2]
  by_contra hne
  have hαlt : α < 1 := lt_of_le_of_ne hα1 hne
  have hα0 : 0 ≤ α := by linarith [h1.1]
  have ht : (1 + α) / 2 ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.2 ⟨by linarith, by linarith⟩
  have hu := hup ((1 + α) / 2) ht
  have hpos : (0 : ℝ) < (1 - α) * (1 - α) * (2 + α) :=
    mul_pos (mul_pos (sub_pos.2 hαlt) (sub_pos.2 hαlt)) (by linarith)
  nlinarith [hu, hpos]

/-- **The amplifier passes both cuts and fails only the range**: for every `c > 0`, `amp c`
satisfies both cut families of `affine_rigidity` on `[0,1]` and violates its range hypothesis
(`amp c 0 = -c < 0`). So the cut families alone do not exclude the amplifier; boundedness does
(trust-lab-068: "the affine class is exactly where boundedness bites").
Source: trust-lab-068; audit round 1, adversarial probe 5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem amp_passes_cuts_fails_range {c : ℝ} (hc : 0 < c) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∫ e in (0 : ℝ)..t, amp c e ≤ t ^ 2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, t * (1 - t) ≤ ∫ e in t..1, amp c e) ∧
      ¬ (∀ e ∈ Set.Icc (0 : ℝ) 1, amp c e ∈ Set.Icc (0 : ℝ) 1) := by
  refine ⟨fun t ht => amp_lower_cut hc.le ht, fun t ht => amp_upper_cut hc.le ht, ?_⟩
  intro h
  have := (h 0 ⟨le_rfl, zero_le_one⟩).1
  unfold amp at this
  linarith

/-- **Affine-rigidity witness (N−)**: the identity (`α = 1`, `β = 0`) inhabits the full
hypothesis package of `affine_rigidity` — range into `[0,1]` and both cut families. Graded N−
because, by the theorem itself, the identity is the package's only inhabitant: the witness
checks that the package is consistent (the rigidity is not an artifact of an unsatisfiable
hypothesis), nothing more.
Source: trust-lab-068
Kind: N-
Fidelity: n/a
Hyps: n/a -/
theorem affine_rigidity_witness :
    (∀ e ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ) * e + 0 ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∫ e in (0 : ℝ)..t, ((1 : ℝ) * e + 0) ≤ t ^ 2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, t * (1 - t) ≤ ∫ e in t..1, ((1 : ℝ) * e + 0)) := by
  refine ⟨fun e he => by simpa using he, fun t ht => ?_, fun t ht => ?_⟩
  · rw [integral_linear]
    nlinarith [ht.1, ht.2]
  · rw [integral_linear]
    nlinarith [ht.1, ht.2, sq_nonneg (1 - t)]

/-! ### (b) The bounded impostor -/

/-- The impostor `gimp e = min (2e) 1`.
Source: trust-lab-2-044
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def gimp (e : ℝ) : ℝ := min (2 * e) 1

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma gimp_continuous : Continuous gimp :=
  (continuous_const.mul continuous_id).min continuous_const

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma gimp_eq_of_le {e : ℝ} (he : e ≤ 1 / 2) : gimp e = 2 * e := by
  unfold gimp
  exact min_eq_left (by linarith)

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma gimp_eq_of_ge {e : ℝ} (he : 1 / 2 ≤ e) : gimp e = 1 := by
  unfold gimp
  exact min_eq_right (by linarith)

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma integral_gimp_lower_of_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    ∫ e in (0 : ℝ)..t, gimp e = t ^ 2 := by
  have h : ∫ e in (0 : ℝ)..t, gimp e = ∫ e in (0 : ℝ)..t, (2 * e + 0) := by
    apply integral_congr
    intro e he
    rw [Set.uIcc_of_le ht0] at he
    rw [gimp_eq_of_le (by linarith [he.2])]
    ring
  rw [h, integral_linear]
  ring

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma integral_gimp_half : ∫ e in (0 : ℝ)..(1 / 2), gimp e = 1 / 4 := by
  rw [integral_gimp_lower_of_le (by norm_num) le_rfl]
  norm_num

/-- Supporting lemma (a proof step, not a headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
lemma integral_gimp_lower_of_ge {t : ℝ} (ht : 1 / 2 ≤ t) :
    ∫ e in (0 : ℝ)..t, gimp e = t - 1 / 4 := by
  have hadj : (∫ e in (0 : ℝ)..(1 / 2), gimp e) + ∫ e in (1 / 2 : ℝ)..t, gimp e =
      ∫ e in (0 : ℝ)..t, gimp e :=
    integral_add_adjacent_intervals (gimp_continuous.intervalIntegrable _ _)
      (gimp_continuous.intervalIntegrable _ _)
  have h : ∫ e in (1 / 2 : ℝ)..t, gimp e = ∫ e in (1 / 2 : ℝ)..t, (0 * e + 1) := by
    apply integral_congr
    intro e he
    rw [Set.uIcc_of_le ht] at he
    rw [gimp_eq_of_ge he.1]
    ring
  rw [← hadj, integral_gimp_half, h, integral_linear]
  ring

/-- `∫_0^t gimp`, both regimes.
Source: trust-lab-2-044
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem integral_gimp_lower {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ e in (0 : ℝ)..t, gimp e = if t ≤ 1 / 2 then t ^ 2 else t - 1 / 4 := by
  split_ifs with h
  · exact integral_gimp_lower_of_le ht.1 h
  · exact integral_gimp_lower_of_ge (le_of_not_ge h)

/-- `∫_t^1 gimp = 3/4 - ∫_0^t gimp`.
Source: trust-lab-2-044
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem integral_gimp_upper (t : ℝ) :
    ∫ e in t..1, gimp e = 3 / 4 - ∫ e in (0 : ℝ)..t, gimp e := by
  have h : (∫ e in (0 : ℝ)..t, gimp e) + ∫ e in t..1, gimp e = ∫ e in (0 : ℝ)..1, gimp e :=
    integral_add_adjacent_intervals (gimp_continuous.intervalIntegrable _ _)
      (gimp_continuous.intervalIntegrable _ _)
  have h1 : ∫ e in (0 : ℝ)..1, gimp e = 3 / 4 := by
    rw [integral_gimp_lower_of_ge (by norm_num)]
    norm_num
  linarith

/-- **The bounded impostor** (H2 (b)): `gimp` is continuous, maps `[0,1]` into `[0,1]`, differs
from the identity (`gimp (1/4) = 1/2`), and passes both cut families. So the cut families do not
single out the amplifier without the affinity hypothesis of `affine_rigidity`.
Source: trust-lab-2-044, 068
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem gimp_impostor :
    Continuous gimp ∧ (∀ e ∈ Set.Icc (0 : ℝ) 1, gimp e ∈ Set.Icc (0 : ℝ) 1) ∧
      gimp (1 / 4) ≠ 1 / 4 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∫ e in (0 : ℝ)..t, gimp e ≤ t ^ 2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, t * (1 - t) ≤ ∫ e in t..1, gimp e) := by
  refine ⟨gimp_continuous, fun e he => ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · unfold gimp
    constructor
    · exact le_min (by linarith [he.1]) zero_le_one
    · exact min_le_right _ _
  · rw [gimp_eq_of_le (by norm_num)]
    norm_num
  · rw [integral_gimp_lower ht]
    split_ifs with h
    · exact le_rfl
    · nlinarith [ht.1, ht.2]
  · rw [integral_gimp_upper, integral_gimp_lower ht]
    split_ifs with h
    · nlinarith [ht.1, ht.2]
    · nlinarith [ht.1, ht.2]

end Cleanroom.Found.LiAsympCalc
