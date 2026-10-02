import Cleanroom.Decision.DpCalibLimits.Popper

/-!
# T2(a),(b),(e) — Rays: the uniform ray, ray-independence at realized observations, Lemma 2
for every ray

[[dp-calib-limits-mandate]] T2 (dp-sl-2-012, dp-sl-029 ray clause, SE-18′(b), P04 Open 11).

* `nuPolyRay_uniform` etc.: the uniform ray's polynomials are `dp-calibration`'s.
* **Ray-independence at realized observations** (`limitCondRay_eq_of_pos`): for every ray
  starting at `C`, where `ν_C(O) > 0` the limiting conditional is the strict one; corollary
  `limitValRay_eq_of_pos`: where `ν_C(a ∧ O_d) > 0` the limiting act value is the strict
  conditional expectation for every ray. So ray-relativity can decide an argmax only through a
  `C`-null act event (the two-route witness is in `TwoRoute.lean`).
* **Lemma 2 for every ray** (`limitOCRayAt_imp_strictOCAt`): ray-limit calibration refines
  strict calibration, for every ray starting at `C` — the refinement is ray-free.
* Factorisation lemmas (`limitCondRay_of_factor`, `limitValRay_of_factor`): a limit along a
  ray from an explicit `X^k · q` form, for the concrete witnesses.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Positively-trailing helpers for concrete rays -/

section posTrailHelpers

/-- A polynomial with positive constant term is positively trailing (order `0`).
Source: none: infrastructure. Kind: L -/
theorem posTrail_of_coeff_zero_pos {p : Polynomial K} (h : 0 < p.coeff 0) : PosTrail p := by
  intro _
  have hdeg : p.natTrailingDegree = 0 :=
    Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero h.ne')
  rw [Polynomial.trailingCoeff, hdeg]; exact h

/-- `X` is positively trailing. Source: none: infrastructure. Kind: L -/
theorem PosTrail.X : PosTrail (Polynomial.X : Polynomial K) := by
  intro _
  rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X, Polynomial.coeff_X_one]
  exact one_pos

/-- Powers of positively trailing polynomials are positively trailing.
Source: none: infrastructure. Kind: L -/
theorem PosTrail.pow {p : Polynomial K} (hp : PosTrail p) : ∀ n : ℕ, PosTrail (p ^ n)
  | 0 => by rw [pow_zero]; exact PosTrail.C zero_le_one
  | n + 1 => by rw [pow_succ]; exact PosTrail.mul (PosTrail.pow hp n) hp

/-- The order of `X^k · q` with `q.eval 0 ≠ 0` is `k`, and its coefficient there is
`q.eval 0`. Source: none: infrastructure. Kind: L -/
theorem natTrailingDegree_X_pow_mul_eq {q : Polynomial K} (k : ℕ) (hq : q.eval 0 ≠ 0) :
    (Polynomial.X ^ k * q).natTrailingDegree = k ∧
      (Polynomial.X ^ k * q).coeff k = q.eval 0 := by
  have hq0 : q.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
  have hqne : q ≠ 0 := fun h => hq0 (by rw [h, Polynomial.coeff_zero])
  have hdq : q.natTrailingDegree = 0 :=
    Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero hq0)
  refine ⟨?_, ?_⟩
  · rw [mul_comm, Polynomial.natTrailingDegree_mul_X_pow hqne, hdq, zero_add]
  · rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]

end posTrailHelpers

section rays

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ## The uniform ray is Definition 10's -/

/-- Along the uniform ray the leaf polynomials are `dp-calibration`'s `leafLawPoly`.
Source: none: infrastructure. Kind: L -/
theorem leafLawPolyRay_uniform (C : Proc ι acts K) :
    (B : Tree Ω ι acts K) → ∀ ℓ, leafLawPolyRay (uniformRay C) B ℓ = leafLawPoly C B ℓ
  | .leaf _ _, _ => rfl
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLawPolyRay, leafLawPoly, leafLawPolyRay_uniform C (child i) ℓ]
  | .decision d child, ⟨a, ℓ⟩ => by
      simp only [leafLawPolyRay, leafLawPoly, leafLawPolyRay_uniform C (child a) ℓ]
      rfl

/-- `nuPolyRay (uniformRay C) = nuPoly C`.
Source: mandate §3.3 (`nuPolyRay (uniformRay C) B X = nuPoly C B X`)
Kind: L -/
theorem nuPolyRay_uniform (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    nuPolyRay (uniformRay C) B X = nuPoly C B X :=
  Finset.sum_congr rfl fun ℓ _ => leafLawPolyRay_uniform C B ℓ

/-- `payPolyRay (uniformRay C) = payPoly C`. Source: mandate §3.3. Kind: L -/
theorem payPolyRay_uniform (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    payPolyRay (uniformRay C) B X = payPoly C B X :=
  Finset.sum_congr rfl fun ℓ _ => by rw [leafLawPolyRay_uniform]

/-- `limitCondRay (uniformRay C) = limitCond C`. Source: mandate §3.3. Kind: L -/
theorem limitCondRay_uniform (C : Proc ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω) :
    limitCondRay (uniformRay C) B X O = limitCond C B X O := by
  unfold limitCondRay limitCond; rw [nuPolyRay_uniform, nuPolyRay_uniform]

/-- `limitValRay (uniformRay C) = limitVal C`. Source: mandate §3.3. Kind: L -/
theorem limitValRay_uniform (C : Proc ι acts K) (B : Tree Ω ι acts K) (Y : Finset Ω) :
    limitValRay (uniformRay C) B Y = limitVal C B Y := by
  unfold limitValRay limitVal; rw [nuPolyRay_uniform, payPolyRay_uniform]

/-- The uniform ray starts at `C`. Source: mandate §3.3. Kind: L -/
theorem isRayOf_uniformRay (C : Proc ι acts K) : IsRayOf (uniformRay C) C := by
  intro d a
  simp [uniformRay, trembleW, Polynomial.coeff_add, Polynomial.coeff_C]

/-! ## Order lemmas along a ray -/

variable (R : Ray ι acts K)

/-- `nuPolyRay` as an indicator sum over all leaves. Source: none: infrastructure. Kind: L -/
theorem nuPolyRay_eq_sum (B : Tree Ω ι acts K) (X : Finset Ω) :
    nuPolyRay R B X = ∑ ℓ, if world B ℓ ∈ X then leafLawPolyRay R B ℓ else 0 := by
  unfold nuPolyRay worldEv; rw [Finset.sum_filter]

/-- `payPolyRay` as an indicator sum over all leaves. Source: none: infrastructure. Kind: L -/
theorem payPolyRay_eq_sum (B : Tree Ω ι acts K) (X : Finset Ω) :
    payPolyRay R B X =
      ∑ ℓ, if world B ℓ ∈ X then leafLawPolyRay R B ℓ * Polynomial.C (payoff B ℓ) else 0 := by
  unfold payPolyRay worldEv; rw [Finset.sum_filter]

/-- Leaf polynomials along a ray are positively trailing. Source: none: infrastructure. Kind: L -/
theorem posTrail_leafLawPolyRay : (B : Tree Ω ι acts K) → ∀ ℓ, PosTrail (leafLawPolyRay R B ℓ)
  | .leaf _ _, _ => by
      intro _
      rw [show (leafLawPolyRay R (.leaf _ _) _ : Polynomial K) = Polynomial.C 1 by
        simp [leafLawPolyRay]]
      exact PosTrail.C zero_le_one (by simp)
  | .chance _ β child, ⟨i, ℓ⟩ =>
      PosTrail.mul (PosTrail.C (β.nonneg i)) (posTrail_leafLawPolyRay (child i) ℓ)
  | .decision d child, ⟨a, ℓ⟩ =>
      PosTrail.mul (R.posTrail d a) (posTrail_leafLawPolyRay (child a) ℓ)

/-- `nuPolyRay` is positively trailing. Source: none: infrastructure. Kind: L -/
theorem posTrail_nuPolyRay (B : Tree Ω ι acts K) (X : Finset Ω) : PosTrail (nuPolyRay R B X) :=
  PosTrail.sum _ _ fun ℓ _ => posTrail_leafLawPolyRay R B ℓ

/-- The trailing coefficient of a non-zero `nuPolyRay` is positive.
Source: none: infrastructure. Kind: L -/
theorem trailingCoeff_nuPolyRay_pos (B : Tree Ω ι acts K) (X : Finset Ω)
    (h : nuPolyRay R B X ≠ 0) : 0 < (nuPolyRay R B X).trailingCoeff :=
  posTrail_nuPolyRay R B X h

/-- The order of `nuPolyRay (X ∩ O)` is at least that of `nuPolyRay O` (when non-zero).
Source: none: infrastructure. Kind: L -/
theorem natTrailingDegree_nuPolyRay_mono (B : Tree Ω ι acts K) (X O : Finset Ω)
    (h : nuPolyRay R B (X ∩ O) ≠ 0) :
    (nuPolyRay R B O).natTrailingDegree ≤ (nuPolyRay R B (X ∩ O)).natTrailingDegree := by
  unfold nuPolyRay at h ⊢
  exact PosTrail.natTrailingDegree_sum_mono (worldEv_inter_subset B X O) _
    (fun ℓ _ => posTrail_leafLawPolyRay R B ℓ) h

variable {C : Proc ι acts K}

/-- The constant coefficient of a leaf polynomial along a ray starting at `C` is `μ_C(ℓ)`.
Source: P07 I2′ (the ray starts at `C`); mandate §3.3 (`coeff_zero_nuPolyRay = nu C`)
Kind: L -/
theorem coeff_zero_leafLawPolyRay (h : IsRayOf R C) :
    (B : Tree Ω ι acts K) → ∀ ℓ, (leafLawPolyRay R B ℓ).coeff 0 = leafLaw C B ℓ
  | .leaf _ _, _ => by simp [leafLawPolyRay, leafLaw]
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLawPolyRay, leafLaw_chance, Polynomial.coeff_C_mul]
      rw [coeff_zero_leafLawPolyRay h (child i) ℓ]
  | .decision d child, ⟨a, ℓ⟩ => by
      simp only [leafLawPolyRay, leafLaw_decision, Polynomial.mul_coeff_zero]
      rw [coeff_zero_leafLawPolyRay h (child a) ℓ, h d a]

/-- `nuPolyRay` at `ε = 0` is `ν_C` for a ray starting at `C`.
Source: mandate §3.3
Kind: L -/
theorem coeff_zero_nuPolyRay (h : IsRayOf R C) (B : Tree Ω ι acts K) (X : Finset Ω) :
    (nuPolyRay R B X).coeff 0 = nu C B X := by
  unfold nuPolyRay nu mass
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun ℓ _ => coeff_zero_leafLawPolyRay R h B ℓ

/-- `payPolyRay` at `ε = 0` is `paySum C` for a ray starting at `C`.
Source: mandate §3.3
Kind: L -/
theorem coeff_zero_payPolyRay (h : IsRayOf R C) (B : Tree Ω ι acts K) (X : Finset Ω) :
    (payPolyRay R B X).coeff 0 = paySum C B X := by
  unfold payPolyRay paySum
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun ℓ _ => by
    rw [Polynomial.coeff_mul_C, coeff_zero_leafLawPolyRay R h B ℓ]

/-- Where `ν_C(O) > 0`, `nuPolyRay R O` has order `0` and is non-zero, for every ray starting
at `C`. Source: none: infrastructure. Kind: L -/
theorem natTrailingDegree_nuPolyRay_eq_zero (h : IsRayOf R C) (B : Tree Ω ι acts K)
    (O : Finset Ω) (hpos : 0 < nu C B O) :
    (nuPolyRay R B O).natTrailingDegree = 0 ∧ nuPolyRay R B O ≠ 0 := by
  have hne : (nuPolyRay R B O).coeff 0 ≠ 0 := by rw [coeff_zero_nuPolyRay R h]; exact hpos.ne'
  refine ⟨Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero hne), ?_⟩
  intro hz; rw [hz, Polynomial.coeff_zero] at hne; exact hne rfl

/-! ## Ray-independence at realized observations -/

/-- **Ray-independence at realized observations**: for every ray starting at `C`, where
`ν_C(O) > 0` the limiting conditional along the ray is the strict one,
`ν_C(X ∩ O) / ν_C(O)` — order `0` dominates. Generalises `limitCond_eq_of_pos`.
Source: P07 I2′ ("at a single point with realized `O_d` there is nothing to choose");
dp-sl-029 (ray clause); SE-18′(b) ("approved at the Definition-10 (ray) state under the
added hypothesis `ν_{C₀}(a ∧ O_d) > 0`")
Kind: C (regraded from P in repair round 1: the ray generalisation of `dp-calibration`'s
`limitCond_eq_of_pos`, graded L there; the content is `natTrailingDegree_nuPolyRay_eq_zero`
and `coeff_zero_nuPolyRay` under `IsRayOf`)
Fidelity: exact
Hyps: (a) `IsRayOf R C`, (a) `0 < ν_C(O)` -/
theorem limitCondRay_eq_of_pos (h : IsRayOf R C) (B : Tree Ω ι acts K) (X O : Finset Ω)
    (hpos : 0 < nu C B O) : limitCondRay R B X O = nu C B (X ∩ O) / nu C B O := by
  unfold limitCondRay
  rw [(natTrailingDegree_nuPolyRay_eq_zero R h B O hpos).1, coeff_zero_nuPolyRay R h,
    coeff_zero_nuPolyRay R h]

/-- **Corollary: at a realized act event the limiting act value is the strict conditional
expectation, for every ray.** So ray-relativity can decide an argmax only through a `C`-null
act event.
Source: SE-18′(b); P07 I2′ ("the selection decides the argmax only at observations the
untrembled procedure never realizes")
Kind: L (regraded from P in repair round 1: the corollary of `limitCondRay_eq_of_pos`'s
mechanism for the value)
Fidelity: exact
Hyps: (a) `IsRayOf R C`, (a) `0 < ν_C(Y)` -/
theorem limitValRay_eq_of_pos (h : IsRayOf R C) (B : Tree Ω ι acts K) (Y : Finset Ω)
    (hpos : 0 < nu C B Y) : limitValRay R B Y = paySum C B Y / nu C B Y := by
  unfold limitValRay
  rw [(natTrailingDegree_nuPolyRay_eq_zero R h B Y hpos).1, coeff_zero_nuPolyRay R h,
    coeff_zero_payPolyRay R h]

/-- The uniform-ray instance: where `ν_C(Y) > 0`, `limitVal C B Y = condExp C B Y`.
Source: SE-18′(b); `calibration.md` D4
Kind: L -/
theorem limitVal_eq_of_pos (C : Proc ι acts K) (B : Tree Ω ι acts K) (Y : Finset Ω)
    (hpos : 0 < nu C B Y) : limitVal C B Y = condExp C B Y := by
  rw [← limitValRay_uniform, limitValRay_eq_of_pos (uniformRay C) (isRayOf_uniformRay C) B Y hpos]
  rfl

/-! ## Lemma 2 for every ray -/

/-- **Lemma 2 along every ray**: ray-limit calibration at `d` implies strict calibration at
`d`, for every ray starting at `C`. The refinement of strict calibration by Definition 10 is
ray-free (this answers Q-traps' clause (i), `Traps.lean`).
Source: [[decision-problems-v2]] §3.1 Lemma 2, read along a ray (P07 I2′, I3′)
Kind: P
Fidelity: exact (both clauses)
Hyps: (a) `IsRayOf R C`, (a) `LimitOCRayAt` -/
theorem limitOCRayAt_imp_strictOCAt (h : IsRayOf R C) (s : ι → State Ω K) (obs : ι → Finset Ω)
    (B : Tree Ω ι acts K) (d : ι) (hl : LimitOCRayAt R s obs B d) : StrictOCAt s obs C B d := by
  intro hpos
  obtain ⟨hdeg, hne⟩ := natTrailingDegree_nuPolyRay_eq_zero R h B (obs d) hpos
  obtain ⟨h1, h2⟩ := hl hne
  refine ⟨fun X => ?_, fun X hX hXO => ?_⟩
  · rw [h1 X, limitCondRay_eq_of_pos R h B X (obs d) hpos]
    exact div_mul_cancel₀ _ hpos.ne'
  · have hlc : 0 < limitCondRay R B X (obs d) := by rw [← h1 X]; exact hX
    have := h2 X hlc
    rwa [(natTrailingDegree_nuPolyRay_eq_zero R h B (X ∩ obs d) hXO).1,
      coeff_zero_nuPolyRay R h, coeff_zero_payPolyRay R h] at this

/-- The uniform ray's `LimitOCRayAt` is `dp-calibration`'s `LimitOCAt`.
Source: none: infrastructure. Kind: L -/
theorem limitOCRayAt_uniform_iff (C : Proc ι acts K) (s : ι → State Ω K) (obs : ι → Finset Ω)
    (B : Tree Ω ι acts K) (d : ι) :
    LimitOCRayAt (uniformRay C) s obs B d ↔ LimitOCAt s obs C B d := by
  unfold LimitOCRayAt LimitOCAt
  simp only [nuPolyRay_uniform, payPolyRay_uniform, limitCondRay_uniform]

/-! ## Limits from an explicit factorisation -/

/-- A limiting conditional along a ray from an explicit `X^k · q` form of numerator and
denominator with `q.eval 0 ≠ 0`. Source: none: infrastructure. Kind: L -/
theorem limitCondRay_of_factor (B : Tree Ω ι acts K) (X O : Finset Ω) (k : ℕ)
    (q q' : Polynomial K) (hO : nuPolyRay R B O = Polynomial.X ^ k * q)
    (hX : nuPolyRay R B (X ∩ O) = Polynomial.X ^ k * q') (hq : q.eval 0 ≠ 0) :
    limitCondRay R B X O = q'.eval 0 / q.eval 0 := by
  unfold limitCondRay
  obtain ⟨hdeg, hcoeff⟩ := natTrailingDegree_X_pow_mul_eq (K := K) k hq
  rw [hO, hX, hdeg, hcoeff, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    Polynomial.coeff_zero_eq_eval_zero]

/-- A limiting act value along a ray from an explicit `X^k · q` form.
Source: none: infrastructure. Kind: L -/
theorem limitValRay_of_factor (B : Tree Ω ι acts K) (Y : Finset Ω) (k : ℕ)
    (q r : Polynomial K) (hn : nuPolyRay R B Y = Polynomial.X ^ k * q)
    (hp : payPolyRay R B Y = Polynomial.X ^ k * r) (hq : q.eval 0 ≠ 0) :
    limitValRay R B Y = r.eval 0 / q.eval 0 := by
  unfold limitValRay
  obtain ⟨hdeg, hcoeff⟩ := natTrailingDegree_X_pow_mul_eq (K := K) k hq
  rw [hn, hp, hdeg, hcoeff, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    Polynomial.coeff_zero_eq_eval_zero]

/-- The uniform-ray instance of `limitValRay_of_factor`. Source: none: infrastructure. Kind: L -/
theorem limitVal_of_factor (C : Proc ι acts K) (B : Tree Ω ι acts K) (Y : Finset Ω) (k : ℕ)
    (q r : Polynomial K) (hn : nuPoly C B Y = Polynomial.X ^ k * q)
    (hp : payPoly C B Y = Polynomial.X ^ k * r) (hq : q.eval 0 ≠ 0) :
    limitVal C B Y = r.eval 0 / q.eval 0 := by
  rw [← limitValRay_uniform]
  exact limitValRay_of_factor (uniformRay C) B Y k q r (by rw [nuPolyRay_uniform, hn])
    (by rw [payPolyRay_uniform, hp]) hq

end rays

end Cleanroom.Decision.DpCalibLimits
