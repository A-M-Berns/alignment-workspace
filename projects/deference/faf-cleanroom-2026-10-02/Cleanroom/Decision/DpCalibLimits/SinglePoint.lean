import Cleanroom.Decision.DpCalibLimits.Rays

/-!
# T2(d), the surviving neighbour — ray-independence at a single point with two actions

[[dp-calib-limits-mandate]] T2(d) (P07-1′ refinement (ii), `P07.md` line 32: "the
ray-dependence of SE-18′(b) … needs two *points* trembling at different rates and an observation
the untrembled procedure never realizes"; the survey headline dp-sl-029 "absent from single-point
classes" is the run's compression of it — retargeted in repair round 1).

`TwoRoute.lean` refutes "needs two points" at three actions (`threeAct_ray_dependent`). The
surviving neighbour is the two-action statement, **proved here in repair round 1** (it was stated
OPEN in the first round): on a tree with a single point carrying two actions, the limiting
conditional along a full-support ray starting at `C` does not depend on the ray.

The argument, as formalized. Along any ray a leaf's polynomial is `C(c(ℓ)) · w_a^{#a(ℓ)} ·
w_b^{#b(ℓ)}` (`leafLawPolyRay_eq_pow`; `#x(ℓ)` the number of `x`-draws on the path,
`actCount`). If `C(d)` is mixed, every ray has order `0` at every chance-positive leaf and the
limit is the strict conditional (`limitCondRay_eq_of_pos`), or `O` is chance-null and every ray
gives the junk `0`. If `C(d) = δ_s` with `t` the other act, write `w_t = X^j · α` with
`j = ord(w_t) ≥ 1` and `α(0) = trailingCoeff(w_t) > 0`, and `w_s(0) = 1`; then `nuPolyRay R Y =
X^{j·n_min} · q_Y` with `n_min` the least `#t` over the chance-positive `O`-leaves and
`q_Y(0) = α(0)^{n_min} · ∑_{ℓ ⊨ Y, c(ℓ) > 0, #t(ℓ) = n_min} c(ℓ)` (`levelPoly_eval_zero`), so
`limitCondRay R X O = q_{X∩O}(0)/q_O(0)` (`limitCondRay_of_factor`) and `α(0)^{n_min}` cancels:
the value is the ray-free `levelMass` ratio (`limitCondRay_eq_levelMass`). `n_min` and the chance
weights are data of the tree, not of the ray.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ## Draw counts and the leaf polynomial along a ray -/

/-- The number of `x`-draws on a leaf's root path, on a one-point `Act2` tree.
Source: none: infrastructure (the pattern of `a`-draws of [[decision-problems-v2]] Proposition 4,
counted). Kind: D -/
def actCount (x : Act2) : (B : Tree Ω Unit (fun _ => Act2) ℚ) → B.Leaves → ℕ
  | .leaf _ _, _ => 0
  | .chance _ _ child, ⟨i, ℓ⟩ => actCount x (child i) ℓ
  | .decision _ child, ⟨y, ℓ⟩ => (if y = x then 1 else 0) + actCount x (child y) ℓ

/-- **The leaf polynomial along a ray on a one-point `Act2` tree** is
`C(c(ℓ)) · w_a^{#a(ℓ)} · w_b^{#b(ℓ)}`. Source: none: infrastructure. Kind: L -/
theorem leafLawPolyRay_eq_pow (R : Ray Unit (fun _ => Act2) ℚ) :
    (B : Tree Ω Unit (fun _ => Act2) ℚ) → ∀ ℓ,
      leafLawPolyRay R B ℓ = Polynomial.C (chanceWeight B ℓ) *
        (R.w () .a) ^ actCount .a B ℓ * (R.w () .b) ^ actCount .b B ℓ
  | .leaf _ _, _ => by simp [leafLawPolyRay, chanceWeight, actCount]
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLawPolyRay, chanceWeight_chance, actCount, Polynomial.C_mul]
      rw [leafLawPolyRay_eq_pow R (child i) ℓ]; ring
  | .decision d child, ⟨y, ℓ⟩ => by
      cases d
      simp only [leafLawPolyRay, chanceWeight_decision, actCount]
      rw [leafLawPolyRay_eq_pow R (child y) ℓ]
      cases y <;> simp <;> ring

/-- The same with the two acts in either order. Source: none: infrastructure. Kind: L -/
theorem leafLawPolyRay_eq_pow' (R : Ray Unit (fun _ => Act2) ℚ) (B : Tree Ω Unit (fun _ => Act2) ℚ)
    (t s : Act2) (hts : t ≠ s) (ℓ : B.Leaves) :
    leafLawPolyRay R B ℓ = Polynomial.C (chanceWeight B ℓ) *
      (R.w () t) ^ actCount t B ℓ * (R.w () s) ^ actCount s B ℓ := by
  rw [leafLawPolyRay_eq_pow]
  cases t <;> cases s
  · exact absurd rfl hts
  · rfl
  · ring
  · exact absurd rfl hts

/-! ## The ray-free level data of `O` -/

section level

variable (B : Tree Ω Unit (fun _ => Act2) ℚ)

/-- The chance-positive `O`-leaves. Source: none: infrastructure. Kind: D -/
def posLeaves (O : Finset Ω) : Finset B.Leaves :=
  (worldEv B O).filter fun ℓ => chanceWeight B ℓ ≠ 0

/-- The least number of `t`-draws over the chance-positive `O`-leaves (`0` if there are none).
Source: none: infrastructure (the "first level giving `O` mass" of P07 I2′'s LPS reading, for a
pure label). Kind: D -/
noncomputable def minCount (t : Act2) (O : Finset Ω) : ℕ :=
  if h : (posLeaves B O).Nonempty then ((posLeaves B O).image (actCount t B)).min' (h.image _)
  else 0

/-- The level mass of `Y` at `t`-count `n`: the chance weights of the chance-positive `Y`-leaves
with exactly `n` `t`-draws. Source: none: infrastructure. Kind: D -/
def levelMassAt (t : Act2) (n : ℕ) (Y : Finset Ω) : ℚ :=
  ∑ ℓ ∈ worldEv B Y, if chanceWeight B ℓ ≠ 0 ∧ actCount t B ℓ = n then chanceWeight B ℓ else 0

/-- **The ray-free level mass**: the chance weight of the `Y`-leaves at the minimal `t`-count of
`O`. The limiting conditional of `X` given `O` along *any* full-support ray of `δ_s` is
`levelMass t O (X ∩ O) / levelMass t O O`. Source: none: infrastructure. Kind: D -/
noncomputable def levelMass (t : Act2) (O Y : Finset Ω) : ℚ :=
  levelMassAt B t (minCount B t O) Y

/-- Below the minimal count there is nothing: every chance-positive `O`-leaf has at least
`minCount` `t`-draws. Source: none: infrastructure. Kind: L -/
theorem minCount_le (t : Act2) (O : Finset Ω) (ℓ : B.Leaves) (hℓ : ℓ ∈ worldEv B O)
    (hc : chanceWeight B ℓ ≠ 0) : minCount B t O ≤ actCount t B ℓ := by
  have hmem : ℓ ∈ posLeaves B O := Finset.mem_filter.mpr ⟨hℓ, hc⟩
  have hne : (posLeaves B O).Nonempty := ⟨ℓ, hmem⟩
  unfold minCount
  rw [dif_pos hne]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hmem)

/-- The minimal count is attained when some chance-positive `O`-leaf exists.
Source: none: infrastructure. Kind: L -/
theorem exists_minCount (t : Act2) (O : Finset Ω) (hne : (posLeaves B O).Nonempty) :
    ∃ ℓ ∈ worldEv B O, chanceWeight B ℓ ≠ 0 ∧ actCount t B ℓ = minCount B t O := by
  unfold minCount
  rw [dif_pos hne]
  obtain ⟨ℓ, hℓ, h⟩ := Finset.mem_image.mp (Finset.min'_mem _ (hne.image (actCount t B)))
  obtain ⟨hℓO, hc⟩ := Finset.mem_filter.mp hℓ
  exact ⟨ℓ, hℓO, hc, h⟩

/-- The level mass of `O` at its own minimal count is positive when some chance-positive
`O`-leaf exists. Source: none: infrastructure. Kind: L -/
theorem levelMass_pos (t : Act2) (O : Finset Ω) (hne : (posLeaves B O).Nonempty) :
    0 < levelMass B t O O := by
  obtain ⟨ℓ₀, hℓ₀, hc₀, hn₀⟩ := exists_minCount B t O hne
  unfold levelMass levelMassAt
  have hnn : ∀ ℓ ∈ worldEv B O,
      0 ≤ (if chanceWeight B ℓ ≠ 0 ∧ actCount t B ℓ = minCount B t O then chanceWeight B ℓ
        else 0) := fun ℓ _ => by
    split_ifs
    · exact chanceWeight_nonneg B ℓ
    · exact le_rfl
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnn hℓ₀)
  rw [if_pos ⟨hc₀, hn₀⟩]
  exact lt_of_le_of_ne (chanceWeight_nonneg B ℓ₀) (Ne.symm hc₀)

/-- With no chance-positive `O`-leaf the level mass of `O` is `0`.
Source: none: infrastructure. Kind: L -/
theorem levelMass_eq_zero (t : Act2) (O : Finset Ω) (hne : ¬ (posLeaves B O).Nonempty) :
    levelMass B t O O = 0 := by
  unfold levelMass levelMassAt
  refine Finset.sum_eq_zero fun ℓ hℓ => ?_
  rw [if_neg]
  rintro ⟨hc, -⟩
  exact hne ⟨ℓ, Finset.mem_filter.mpr ⟨hℓ, hc⟩⟩

end level

/-! ## The factorisation along a ray of a pure label -/

section factor

variable (B : Tree Ω Unit (fun _ => Act2) ℚ) (R : Ray Unit (fun _ => Act2) ℚ)

/-- The cofactor polynomial of `nuPolyRay R Y` after `X^{j·n}` is pulled out, where `w_t = X^j · α`.
Source: none: infrastructure. Kind: D -/
noncomputable def levelPoly (t s : Act2) (α : Polynomial ℚ) (j n : ℕ) (Y : Finset Ω) :
    Polynomial ℚ :=
  ∑ ℓ ∈ worldEv B Y, if chanceWeight B ℓ = 0 then 0 else
    Polynomial.X ^ (j * (actCount t B ℓ - n)) *
      (Polynomial.C (chanceWeight B ℓ) * α ^ actCount t B ℓ * (R.w () s) ^ actCount s B ℓ)

/-- **`nuPolyRay R Y = X^{j·n} · levelPoly`** when `w_t = X^j · α` and every chance-positive
`Y`-leaf has at least `n` `t`-draws. Source: none: infrastructure. Kind: L -/
theorem nuPolyRay_eq_X_pow_mul_levelPoly (t s : Act2) (hts : t ≠ s) (α : Polynomial ℚ) (j n : ℕ)
    (hw : R.w () t = Polynomial.X ^ j * α) (Y : Finset Ω)
    (hn : ∀ ℓ ∈ worldEv B Y, chanceWeight B ℓ ≠ 0 → n ≤ actCount t B ℓ) :
    nuPolyRay R B Y = Polynomial.X ^ (j * n) * levelPoly B R t s α j n Y := by
  unfold nuPolyRay levelPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [leafLawPolyRay_eq_pow' R B t s hts ℓ]
  by_cases hc : chanceWeight B ℓ = 0
  · simp [hc]
  · rw [if_neg hc, hw, mul_pow, ← pow_mul,
      show j * actCount t B ℓ = j * n + j * (actCount t B ℓ - n) by
        rw [← Nat.mul_add, Nat.add_sub_cancel' (hn ℓ hℓ hc)],
      pow_add]
    ring

/-- **The cofactor at `ε = 0`** is `α(0)^n` times the level mass at count `n`, given `j ≥ 1`,
`w_s(0) = 1`, and that every chance-positive `Y`-leaf has at least `n` `t`-draws.
Source: none: infrastructure. Kind: L -/
theorem levelPoly_eval_zero (t s : Act2) (α : Polynomial ℚ) (j n : ℕ) (hj : 0 < j)
    (hs : (R.w () s).eval 0 = 1) (Y : Finset Ω)
    (hn : ∀ ℓ ∈ worldEv B Y, chanceWeight B ℓ ≠ 0 → n ≤ actCount t B ℓ) :
    (levelPoly B R t s α j n Y).eval 0 = α.eval 0 ^ n * levelMassAt B t n Y := by
  unfold levelPoly levelMassAt
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  by_cases hc : chanceWeight B ℓ = 0
  · simp [hc]
  · by_cases hcount : actCount t B ℓ = n
    · simp only [hc, if_false, hcount, Nat.sub_self, Nat.mul_zero, pow_zero, one_mul,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, hs, one_pow, mul_one,
        ne_eq, not_false_eq_true, and_self, if_true]
      ring
    · have hlt : n < actCount t B ℓ := lt_of_le_of_ne (hn ℓ hℓ hc) (Ne.symm hcount)
      have hne : j * (actCount t B ℓ - n) ≠ 0 :=
        Nat.pos_iff_ne_zero.mp (Nat.mul_pos hj (Nat.sub_pos_of_lt hlt))
      simp [hc, hcount, Polynomial.eval_mul, Polynomial.eval_pow, zero_pow hne]

end factor

/-! ## The ray-free value for a pure label -/

/-- **Along any full-support ray of a pure label `δ_s`, the limiting conditional is the ray-free
level-mass ratio**: `limitCondRay R B X O = levelMass t O (X ∩ O) / levelMass t O O`, where `t`
is the unsupported act. The ray enters only through `w_t = X^j · α`, and `α(0)^{n_min}` cancels
between numerator and denominator; the junk case (no chance-positive `O`-leaf) is `0 = 0/0`.
Source: P07-1′ (ii) restricted to two actions; P07 I2′ (the LPS reading); mandate T2(d)
Kind: P
Fidelity: exact
Hyps: (a) `IsRayOf R C`, (a) `R.FullSupport`, (a) `C(d)(t) = 0` with `t ≠ s` -/
theorem limitCondRay_eq_levelMass (B : Tree Ω Unit (fun _ => Act2) ℚ)
    (R : Ray Unit (fun _ => Act2) ℚ) (C : Proc Unit (fun _ => Act2) ℚ) (hR : IsRayOf R C)
    (hf : R.FullSupport) (t s : Act2) (hts : t ≠ s) (ht : (C ()).w t = 0) (X O : Finset Ω) :
    limitCondRay R B X O = levelMass B t O (X ∩ O) / levelMass B t O O := by
  -- the supported act has weight `1`
  have hs1 : (C ()).w s = 1 := by
    have := (C ()).sum_one
    rw [Act2.sum_univ] at this
    cases t <;> cases s <;> first | exact absurd rfl hts | linarith
  -- `w_t = X^j · α`, `j ≥ 1`, `α(0) > 0`; `w_s(0) = 1`
  set wt := R.w () t with hwt_def
  have hwt0 : wt.coeff 0 = 0 := by rw [hwt_def, hR () t, ht]
  have hwtne : wt ≠ 0 := hf () t
  have htc : 0 < wt.trailingCoeff := R.posTrail () t hwtne
  set j := wt.natTrailingDegree with hj_def
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exfalso
      have := htc
      rw [Polynomial.trailingCoeff, ← hj_def, h, hwt0] at this
      exact lt_irrefl 0 this
    · exact h
  obtain ⟨α, hα⟩ : Polynomial.X ^ j ∣ wt :=
    Polynomial.X_pow_dvd_iff.mpr fun d hd => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  have hα0 : α.eval 0 = wt.trailingCoeff := by
    have := congrArg (fun r : Polynomial ℚ => r.coeff j) hα
    rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at this
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.trailingCoeff]; exact this.symm
  have hαpos : 0 < α.eval 0 := by rw [hα0]; exact htc
  have hws : (R.w () s).eval 0 = 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hR () s, hs1]
  by_cases hne : (posLeaves B O).Nonempty
  · -- the generic case: pull `X^{j·n_min}` out of numerator and denominator
    set n := minCount B t O with hn_def
    have hnO : ∀ ℓ ∈ worldEv B O, chanceWeight B ℓ ≠ 0 → n ≤ actCount t B ℓ :=
      fun ℓ hℓ hc => minCount_le B t O ℓ hℓ hc
    have hnXO : ∀ ℓ ∈ worldEv B (X ∩ O), chanceWeight B ℓ ≠ 0 → n ≤ actCount t B ℓ :=
      fun ℓ hℓ hc => minCount_le B t O ℓ (worldEv_inter_subset B X O hℓ) hc
    have hO := nuPolyRay_eq_X_pow_mul_levelPoly B R t s hts α j n hα O hnO
    have hXO := nuPolyRay_eq_X_pow_mul_levelPoly B R t s hts α j n hα (X ∩ O) hnXO
    have hqO := levelPoly_eval_zero B R t s α j n hj hws O hnO
    have hqXO := levelPoly_eval_zero B R t s α j n hj hws (X ∩ O) hnXO
    have hqO0 : (levelPoly B R t s α j n O).eval 0 ≠ 0 := by
      rw [hqO]
      exact mul_ne_zero (pow_ne_zero _ hαpos.ne') (levelMass_pos B t O hne).ne'
    rw [limitCondRay_of_factor R B X O (j * n) _ _ hO hXO hqO0, hqO, hqXO]
    unfold levelMass
    exact mul_div_mul_left _ _ (pow_ne_zero _ hαpos.ne')
  · -- no chance-positive `O`-leaf: both sides are the junk `0`
    have hzero : nuPolyRay R B O = 0 := by
      unfold nuPolyRay
      refine Finset.sum_eq_zero fun ℓ hℓ => ?_
      have hc : chanceWeight B ℓ = 0 := by
        by_contra hc
        exact hne ⟨ℓ, Finset.mem_filter.mpr ⟨hℓ, hc⟩⟩
      rw [leafLawPolyRay_eq_pow' R B t s hts ℓ, hc]
      simp
    unfold limitCondRay
    rw [hzero, levelMass_eq_zero B t O hne]
    simp

/-! ## The theorem -/

/-- **Ray-independence at a single point with two actions**: for a tree with one point carrying
`Act2`, any two full-support rays starting at the same `C` give the same limiting conditional at
every `X`, `O`. The surviving neighbour of P07-1′ (ii)'s refuted "needs two points" (refuted at
three actions by `threeAct_ray_dependent`): with two actions the off-support act's order is the
only free choice and its leading coefficient cancels (`limitCondRay_eq_levelMass`); with a mixed
label every ray has order `0` (`limitCondRay_eq_of_pos`) or `O` is chance-null for every ray.
Stated OPEN in the first round; proved in repair round 1.
Source: P07-1′ refinement (ii) (`P07.md` line 32), restricted to two actions; survey dp-sl-029;
mandate T2(d)
Kind: P
Fidelity: exact (the two-action, single-point statement)
Hyps: (a) both rays start at `C` and are full-support -/
theorem twoAct_single_point_ray_independent (B : Tree Ω Unit (fun _ => Act2) ℚ)
    (C : Proc Unit (fun _ => Act2) ℚ)
    (R R' : Ray Unit (fun _ => Act2) ℚ) (hR : IsRayOf R C) (hR' : IsRayOf R' C)
    (hf : R.FullSupport) (hf' : R'.FullSupport) (X O : Finset Ω) :
    limitCondRay R B X O = limitCondRay R' B X O := by
  by_cases hmix : ∀ x, 0 < (C ()).w x
  · -- mixed label: order `0` everywhere, or `O` chance-null for every ray
    by_cases hO : 0 < nu C B O
    · rw [limitCondRay_eq_of_pos R hR B X O hO, limitCondRay_eq_of_pos R' hR' B X O hO]
    · have hnu : nu C B O = 0 := le_antisymm (not_lt.mp hO) (nu_nonneg C B O)
      have hleaf : ∀ ℓ ∈ worldEv B O, leafLaw C B ℓ = 0 := by
        unfold nu mass at hnu
        exact (Finset.sum_eq_zero_iff_of_nonneg fun ℓ _ => leafLaw_nonneg C B ℓ).mp hnu
      have hz : ∀ R₀ : Ray Unit (fun _ => Act2) ℚ, IsRayOf R₀ C → nuPolyRay R₀ B O = 0 := by
        intro R₀ hR₀
        unfold nuPolyRay
        refine Finset.sum_eq_zero fun ℓ hℓ => ?_
        have h0 := coeff_zero_leafLawPolyRay R₀ hR₀ B ℓ
        rw [hleaf ℓ hℓ, leafLawPolyRay_eq_pow, Polynomial.coeff_zero_eq_eval_zero,
          Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow,
          Polynomial.eval_C, ← Polynomial.coeff_zero_eq_eval_zero,
          ← Polynomial.coeff_zero_eq_eval_zero, hR₀ () .a, hR₀ () .b] at h0
        have hc : chanceWeight B ℓ = 0 := by
          rcases mul_eq_zero.mp h0 with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact h
            · exact absurd h (pow_ne_zero _ (hmix .a).ne')
          · exact absurd h (pow_ne_zero _ (hmix .b).ne')
        rw [leafLawPolyRay_eq_pow, hc]
        simp
      unfold limitCondRay
      rw [hz R hR, hz R' hR']
      simp
  · -- a pure label: some act has weight `0`; the value is the ray-free level-mass ratio
    push Not at hmix
    obtain ⟨t, ht⟩ := hmix
    have ht0 : (C ()).w t = 0 := le_antisymm ht ((C ()).nonneg t)
    cases t
    · rw [limitCondRay_eq_levelMass B R C hR hf .a .b (by decide) ht0 X O,
        limitCondRay_eq_levelMass B R' C hR' hf' .a .b (by decide) ht0 X O]
    · rw [limitCondRay_eq_levelMass B R C hR hf .b .a (by decide) ht0 X O,
        limitCondRay_eq_levelMass B R' C hR' hf' .b .a (by decide) ht0 X O]

end Cleanroom.Decision.DpCalibLimits
