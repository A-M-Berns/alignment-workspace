import Cleanroom.Decision.DpCalibration.HypWitnesses
import Cleanroom.Found.DpCoreTree.Shadow

/-!
# Remark 3.5: desirability calibration factors through the shadow; SSC does not (T11)

* `nu_eq_sum_shadow`, `paySum_eq_sum_shadow` — `ν(X)` and the payoff mass `∑_{λ(ℓ)∈X} μ(ℓ) r(ℓ)`
  are sums of the shadow `B̂(C)` over `X × R`, for any finite `R` containing every payoff.
* `condPayoff_eq_of_shadow_eq` — two problems with the same shadow have the same `ν` and the same
  payoff mass on every event; hence both clauses of strict OC at a point are a functional of the
  shadow (`strictClausesAt_of_shadow_eq`, `strictOCAt_of_shadow_eq`).
* `paySum_of_supervenient`, `strictClause2At_iff_of_supervenient` — when `r = u ∘ λ`, clause 2
  is a function of `ν` and `u` alone.
* `perRunSSC_not_shadow_functional` — per-run SSC is **not** a functional of the shadow (N+):
  `toldYouSo` and `insertQuery d₁₀ toldYouSo` have the same shadow (`dp-core-tree`'s
  `shadow_insertQuery`) and different `occ(d₁₀)` (`occ_insertQuery`); with `C = (½ on ten; ten)`
  the stipulated state `δ_{(10,10)}` is per-run SSC at `d₁₀` on the first and not on the second.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## `ν` and the payoff mass from the shadow -/

/-- Summing an `(ω, r)`-indicator over `X × R` collapses to the `X`-indicator when `R` contains
the leaf's payoff. Source: none: infrastructure. Kind: L -/
theorem sum_ite_world_payoff (B : Tree Ω ι acts K) (R : Finset K) (hR : ∀ ℓ, payoff B ℓ ∈ R)
    (X : Finset Ω) (g : B.Leaves → K) (ℓ : B.Leaves) :
    (∑ ω ∈ X, ∑ r ∈ R, if world B ℓ = ω ∧ payoff B ℓ = r then g ℓ else 0) =
      if world B ℓ ∈ X then g ℓ else 0 := by
  have hin : ∀ ω, (∑ r ∈ R, if world B ℓ = ω ∧ payoff B ℓ = r then g ℓ else 0) =
      if world B ℓ = ω then g ℓ else 0 := by
    intro ω
    by_cases hω : world B ℓ = ω
    · simp [hω, hR ℓ]
    · simp [hω]
  simp [hin]

/-- **`ν` is a function of the shadow**: for any finite `R` containing every payoff of `B`,
`ν(X) = ∑_{ω ∈ X} ∑_{r ∈ R} B̂(C)(ω, r)`.
Source: [[decision-problems-v2]] §3.1 Remark 3.5 ("`ν` … [is] determined by `B̂(C)`")
Kind: P
Fidelity: exact
Hyps: (a) `R ⊇ payoffs(B)` -/
theorem nu_eq_sum_shadow (C : Proc ι acts K) (B : Tree Ω ι acts K) (R : Finset K)
    (hR : ∀ ℓ, payoff B ℓ ∈ R) (X : Finset Ω) :
    nu C B X = ∑ ω ∈ X, ∑ r ∈ R, shadow C B (ω, r) := by
  rw [nu_eq_sum]
  simp only [shadow]
  symm
  calc ∑ ω ∈ X, ∑ r ∈ R, ∑ ℓ, (if world B ℓ = ω ∧ payoff B ℓ = r then leafLaw C B ℓ else 0)
      = ∑ ω ∈ X, ∑ ℓ, ∑ r ∈ R,
          (if world B ℓ = ω ∧ payoff B ℓ = r then leafLaw C B ℓ else 0) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ ℓ, ∑ ω ∈ X, ∑ r ∈ R,
          (if world B ℓ = ω ∧ payoff B ℓ = r then leafLaw C B ℓ else 0) := Finset.sum_comm
    _ = ∑ ℓ, (if world B ℓ ∈ X then leafLaw C B ℓ else 0) :=
        Finset.sum_congr rfl fun ℓ _ => sum_ite_world_payoff B R hR X _ ℓ

/-- **The payoff mass is a function of the shadow**: `∑_{λ(ℓ)∈X} μ(ℓ) r(ℓ) = ∑_{ω ∈ X} ∑_{r ∈ R}
r · B̂(C)(ω, r)` for any finite `R` containing every payoff.
Source: [[decision-problems-v2]] §3.1 Remark 3.5 ("the conditional payoffs … [are] determined
by `B̂(C)`")
Kind: P
Fidelity: exact
Hyps: (a) `R ⊇ payoffs(B)` -/
theorem paySum_eq_sum_shadow (C : Proc ι acts K) (B : Tree Ω ι acts K) (R : Finset K)
    (hR : ∀ ℓ, payoff B ℓ ∈ R) (X : Finset Ω) :
    paySum C B X = ∑ ω ∈ X, ∑ r ∈ R, r * shadow C B (ω, r) := by
  have key : ∀ ω r, r * shadow C B (ω, r) =
      ∑ ℓ, if world B ℓ = ω ∧ payoff B ℓ = r then leafLaw C B ℓ * payoff B ℓ else 0 := by
    intro ω r
    simp only [shadow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    split_ifs with h
    · rw [h.2]; ring
    · exact mul_zero r
  simp only [key]
  rw [paySum_eq_sum_ite]
  symm
  calc ∑ ω ∈ X, ∑ r ∈ R, ∑ ℓ,
        (if world B ℓ = ω ∧ payoff B ℓ = r then leafLaw C B ℓ * payoff B ℓ else 0)
      = ∑ ω ∈ X, ∑ ℓ, ∑ r ∈ R,
          (if world B ℓ = ω ∧ payoff B ℓ = r then leafLaw C B ℓ * payoff B ℓ else 0) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ ℓ, ∑ ω ∈ X, ∑ r ∈ R,
          (if world B ℓ = ω ∧ payoff B ℓ = r then leafLaw C B ℓ * payoff B ℓ else 0) :=
        Finset.sum_comm
    _ = ∑ ℓ, (if world B ℓ ∈ X then leafLaw C B ℓ * payoff B ℓ else 0) :=
        Finset.sum_congr rfl fun ℓ _ =>
          sum_ite_world_payoff B R hR X (fun ℓ => leafLaw C B ℓ * payoff B ℓ) ℓ

/-- **Remark 3.5, the factoring half (`condPayoff_eq_of_shadow_eq`)**: two problems over the
same worlds with the same shadow have the same `ν(X)` and the same payoff mass
`∑_{λ(ℓ)∈X} μ(ℓ) r(ℓ)` on every event — so the conditional payoff `𝔼[r | X]` and clause 2 of
strict OC are functionals of the shadow.
Source: [[decision-problems-v2]] §3.1 Remark 3.5 ("desirability calibration … factors through
`B̂(C)`"); mandate T11
Kind: P
Fidelity: exact
Hyps: (a) `shadow C B = shadow C' B'` -/
theorem condPayoff_eq_of_shadow_eq {C C' : Proc ι acts K} {B B' : Tree Ω ι acts K}
    (h : shadow C B = shadow C' B') (X : Finset Ω) :
    nu C B X = nu C' B' X ∧ paySum C B X = paySum C' B' X := by
  obtain ⟨R, hR, hR'⟩ : ∃ R : Finset K, (∀ ℓ, payoff B ℓ ∈ R) ∧ (∀ ℓ, payoff B' ℓ ∈ R) :=
    ⟨Finset.univ.image (payoff B) ∪ Finset.univ.image (payoff B'),
      fun ℓ => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ ℓ)),
      fun ℓ => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ ℓ))⟩
  constructor
  · rw [nu_eq_sum_shadow C B R hR X, nu_eq_sum_shadow C' B' R hR' X, h]
  · rw [paySum_eq_sum_shadow C B R hR X, paySum_eq_sum_shadow C' B' R hR' X, h]

/-- **Both strict clauses at a point are a functional of the shadow.**
Source: [[decision-problems-v2]] §3.1 Remark 3.5; mandate T11
Kind: C
Fidelity: exact
Hyps: (a) `shadow C B = shadow C' B'` -/
theorem strictClausesAt_of_shadow_eq {C C' : Proc ι acts K} {B B' : Tree Ω ι acts K}
    (h : shadow C B = shadow C' B') (s : ι → State Ω K) (obs : ι → Finset Ω) (d : ι) :
    StrictClausesAt s obs C B d ↔ StrictClausesAt s obs C' B' d := by
  have hnu : ∀ X, nu C B X = nu C' B' X := fun X => (condPayoff_eq_of_shadow_eq h X).1
  have hpay : ∀ X, paySum C B X = paySum C' B' X := fun X => (condPayoff_eq_of_shadow_eq h X).2
  unfold StrictClausesAt StrictClause1At StrictClause2At
  simp only [hnu, hpay]

/-- **Strict OC at a point is a functional of the shadow** (guard included).
Source: [[decision-problems-v2]] §3.1 Remark 3.5; mandate T11
Kind: C
Fidelity: exact
Hyps: (a) `shadow C B = shadow C' B'` -/
theorem strictOCAt_of_shadow_eq {C C' : Proc ι acts K} {B B' : Tree Ω ι acts K}
    (h : shadow C B = shadow C' B') (s : ι → State Ω K) (obs : ι → Finset Ω) (d : ι) :
    StrictOCAt s obs C B d ↔ StrictOCAt s obs C' B' d := by
  unfold StrictOCAt
  rw [(condPayoff_eq_of_shadow_eq h (obs d)).1, strictClausesAt_of_shadow_eq h s obs d]

/-! ## The supervenient case `r = u ∘ λ` -/

/-- When the payoff supervenes on the world (`r = u ∘ λ`), the payoff mass on `X` is
`∑_{ω ∈ X} u(ω) · ν({ω})`: a function of `ν` and `u`.
Source: [[decision-problems-v2]] §3.1 Remark 3.5 (supervenient corollary); mandate T11
Kind: L
Fidelity: exact
Hyps: (a) `∀ ℓ, r(ℓ) = u(λ(ℓ))` -/
theorem paySum_of_supervenient (C : Proc ι acts K) (B : Tree Ω ι acts K) (u : Ω → K)
    (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ)) (X : Finset Ω) :
    paySum C B X = ∑ ω ∈ X, u ω * nu C B {ω} := by
  rw [paySum_eq_sum_ite]
  simp only [nu_eq_sum, Finset.mem_singleton, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs <;> simp [hu ℓ, mul_comm]

/-- Under `r = u ∘ λ`, clause 2 of strict OC at `d` reads `V_{s_d}(X) · ν(X ∧ O_d) =
∑_{ω ∈ X ∧ O_d} u(ω) ν({ω})` on the guarded events: a function of `ν` and `u` alone.
Source: [[decision-problems-v2]] §3.1 Remark 3.5 (supervenient corollary); mandate T11
Kind: L
Fidelity: exact
Hyps: (a) `∀ ℓ, r(ℓ) = u(λ(ℓ))` -/
theorem strictClause2At_iff_of_supervenient (s : ι → State Ω K) (obs : ι → Finset Ω)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (u : Ω → K)
    (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ)) (d : ι) :
    StrictClause2At s obs C B d ↔
      ∀ X, 0 < (s d).pr X → 0 < nu C B (X ∩ obs d) →
        (s d).V X * nu C B (X ∩ obs d) = ∑ ω ∈ X ∩ obs d, u ω * nu C B {ω} := by
  unfold StrictClause2At
  simp only [paySum_of_supervenient C B u hu]

/-! ## Per-run SSC does not factor through the shadow (N+) -/

/-- **Per-run SSC does not factor through the shadow** (Remark 3.5's second half): on
`toldYouSo` with `C = (½ on ten; ten)`, the stipulated state `δ_{(10,10)}` is per-run SSC at
`d₁₀` (`μ(occ(d₁₀)) = ½ > 0`), while on `insertQuery d₁₀ toldYouSo` — same shadow
(`shadow_insertQuery`), `occ(d₁₀)` now every run (`occ_insertQuery`, mass `1`) — it is not:
clause 1 at `X = {(10,10)}` would read `1 · 1 = ν({(10,10)}) = ½`.
Source: [[decision-problems-v2]] §3.1 Remark 3.5 ("SSC … does not"), §3.1 "The extensional
shadow"; mandate T11
Kind: N+
Fidelity: exact
Hyps: none -/
theorem perRunSSC_not_shadow_functional :
    shadow (procMixTen (1/2) (by norm_num) (by norm_num)) (insertQuery .ten toldYouSo) =
      shadow (procMixTen (1/2) (by norm_num) (by norm_num)) toldYouSo ∧
    0 < mass (procMixTen (1/2) (by norm_num) (by norm_num)) toldYouSo (occ .ten toldYouSo) ∧
    PerRunSSCAt tysState (procMixTen (1/2) (by norm_num) (by norm_num)) toldYouSo .ten ∧
    ¬ PerRunSSCAt tysState (procMixTen (1/2) (by norm_num) (by norm_num))
      (insertQuery .ten toldYouSo) .ten := by
  refine ⟨shadow_insertQuery _ .ten toldYouSo, ?_, ?_, ?_⟩
  · rw [tys_mass_occ_ten]; simp [procMixTen, mixRoot]
  · exact (tys_perRun_iff_strict_ten _ tysState).mpr (tys_strictOCAt_ten_of_pure _ rfl)
  · intro h
    have hocc : occ .ten (insertQuery .ten toldYouSo) = Finset.univ :=
      occ_insertQuery .ten toldYouSo
    have hmass : mass (procMixTen (1/2) (by norm_num) (by norm_num)) (insertQuery .ten toldYouSo)
        (occ .ten (insertQuery .ten toldYouSo)) = 1 := by
      rw [hocc]; exact mass_univ _ _
    obtain ⟨h1, -⟩ := h (by rw [hmass]; exact one_pos)
    have hX := h1 {(Five10.ten, Five10.ten)}
    rw [hmass, hocc, Finset.inter_univ, mul_one] at hX
    have hnu : nu (procMixTen (1/2) (by norm_num) (by norm_num)) (insertQuery .ten toldYouSo)
        {(Five10.ten, Five10.ten)} =
        nu (procMixTen (1/2) (by norm_num) (by norm_num)) toldYouSo {(Five10.ten, Five10.ten)} :=
      (condPayoff_eq_of_shadow_eq (shadow_insertQuery _ .ten toldYouSo) _).1
    -- `mass C B' (worldEv B' X)` is `nu C B' X` by definition
    have hX' : (tysState .ten).pr {(Five10.ten, Five10.ten)} =
        nu (procMixTen (1/2) (by norm_num) (by norm_num)) (insertQuery .ten toldYouSo)
          {(Five10.ten, Five10.ten)} := hX
    rw [hnu, tys_nu] at hX'
    simp only [tysState] at hX'
    rw [State.dirac_pr] at hX'
    simp [procMixTen, mixRoot] at hX'

end Cleanroom.Decision.DpCalibration
