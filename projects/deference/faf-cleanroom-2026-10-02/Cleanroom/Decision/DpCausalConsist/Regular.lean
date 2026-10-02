import Cleanroom.Decision.DpCausalConsist.Defs

/-!
# `dp-causal-consist`: support regularity of the calibrated and conditioned states

`mixState` reads each component's desirability on that component's support (`Defs.lean`). This
file shows the states the package mixes are support-regular — `calibratedState` (its `V` is a
ratio of run sums, and a null world carries no run mass) and `jeffreyCond` of a support-regular
state — so the mandate's mixture formula `mixState_V_of_suppRegular` applies to `kPart` of a
calibrated state (`TbTheta.lean`) and to `cf^G`-mixtures (`Mixture.lean`).
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  Finset

section regular

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A leaf whose world has no run mass has none itself: `ν{λ(ℓ)} = 0 → μ(ℓ) = 0`.
Source: none: infrastructure
Kind: L -/
theorem leafLaw_eq_zero_of_nu_singleton (C : Proc ι acts K) (B : Tree Ω ι acts K) (ℓ : B.Leaves)
    (h : nu C B {world B ℓ} = 0) : leafLaw C B ℓ = 0 := by
  rw [nu_eq_sum] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg fun ℓ' _ => by
    split_ifs
    · exact leafLaw_nonneg C B ℓ'
    · exact le_rfl).mp h ℓ (Finset.mem_univ ℓ)
  simpa using this

/-- Removing null worlds from an event does not change `ν`.
Source: none: infrastructure
Kind: L -/
theorem nu_inter_filter_pos (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    nu C B (X ∩ Finset.univ.filter fun ω => 0 < nu C B {ω}) = nu C B X := by
  rw [nu_eq_sum, nu_eq_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hX : world B ℓ ∈ X
  · by_cases hp : 0 < nu C B {world B ℓ}
    · simp [hX, hp]
    · have h0 : nu C B {world B ℓ} = 0 := le_antisymm (not_lt.mp hp) (nu_nonneg C B _)
      simp [hX, hp, leafLaw_eq_zero_of_nu_singleton C B ℓ h0]
  · simp [hX]

/-- Removing null worlds from an event does not change `paySum`.
Source: none: infrastructure
Kind: L -/
theorem paySum_inter_filter_pos (C : Proc ι acts K) (B : Tree Ω ι acts K) (X : Finset Ω) :
    paySum C B (X ∩ Finset.univ.filter fun ω => 0 < nu C B {ω}) = paySum C B X := by
  rw [paySum_eq_sum_ite, paySum_eq_sum_ite]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hX : world B ℓ ∈ X
  · by_cases hp : 0 < nu C B {world B ℓ}
    · simp [hX, hp]
    · have h0 : nu C B {world B ℓ} = 0 := le_antisymm (not_lt.mp hp) (nu_nonneg C B _)
      simp [hX, hp, leafLaw_eq_zero_of_nu_singleton C B ℓ h0]
  · simp [hX]

/-- The support of the calibrated state is the positive worlds of `O`.
Source: none: infrastructure
Kind: L -/
theorem supp_calibratedState (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω)
    (h : 0 < nu C B O) :
    supp (calibratedState C B O h) = O ∩ Finset.univ.filter fun ω => 0 < nu C B {ω} := by
  ext ω
  simp only [mem_supp, calibratedState, nuCondDistr, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hO : ω ∈ O
  · simp only [hO, if_true, true_and]
    constructor
    · intro hpos
      by_contra hc
      have : nu C B {ω} = 0 := le_antisymm (not_lt.mp hc) (nu_nonneg C B _)
      rw [this, zero_div] at hpos
      exact lt_irrefl _ hpos
    · intro hpos; exact div_pos hpos h
  · simp [hO]

/-- **The calibrated state is support-regular.**
Source: none: infrastructure (v2 Definition 8: `V` is a ratio of run sums)
Kind: L -/
theorem suppRegular_calibratedState (C : Proc ι acts K) (B : Tree Ω ι acts K) (O : Finset Ω)
    (h : 0 < nu C B O) : SuppRegular (calibratedState C B O h) := by
  intro X
  rw [calibratedState_V, calibratedState_V, supp_calibratedState]
  have hset : X ∩ (O ∩ Finset.univ.filter fun ω => 0 < nu C B {ω}) ∩ O
      = (X ∩ O) ∩ Finset.univ.filter fun ω => 0 < nu C B {ω} := by
    ext ω; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rw [hset, nu_inter_filter_pos, paySum_inter_filter_pos]

/-- The support of a Jeffrey-conditioned state is the support of the state within `O`.
Source: none: infrastructure
Kind: L -/
theorem supp_jeffreyCond (s : State Ω K) (O : Finset Ω) (h : 0 < s.pr O) :
    supp (jeffreyCond s O h) = supp s ∩ O := by
  ext ω
  simp only [mem_supp, jeffreyCond, Finset.mem_inter]
  by_cases hO : ω ∈ O
  · simp only [hO, if_true, and_true]
    constructor
    · intro hpos
      by_contra hc
      have : s.P.w ω = 0 := le_antisymm (not_lt.mp hc) (s.P.nonneg ω)
      rw [this, zero_div] at hpos
      exact lt_irrefl _ hpos
    · intro hpos; exact div_pos hpos h
  · simp [hO]

/-- **Jeffrey conditioning preserves support regularity.**
Source: none: infrastructure
Kind: L -/
theorem suppRegular_jeffreyCond (s : State Ω K) (hs : SuppRegular s) (O : Finset Ω)
    (h : 0 < s.pr O) : SuppRegular (jeffreyCond s O h) := by
  intro X
  rw [jeffreyCond_V, jeffreyCond_V, supp_jeffreyCond]
  have hset : X ∩ (supp s ∩ O) ∩ O = (X ∩ O) ∩ supp s := by
    ext ω; simp only [Finset.mem_inter]; tauto
  rw [hset, hs (X ∩ O)]

/-- `kPart`'s components are support-regular when the state is.
Source: none: infrastructure
Kind: L -/
theorem suppRegular_kPartComp {E : Type} [Fintype E] [DecidableEq E] (s : State Ω K)
    (hs : SuppRegular s) (A : Finset Ω) (exo : Ω → E) (e : E) :
    SuppRegular (kPartComp s A exo e) := by
  unfold kPartComp
  split_ifs with h1 h2
  · exact suppRegular_jeffreyCond s hs _ h1
  · exact suppRegular_jeffreyCond s hs _ h2
  · exact hs

/-- **The K-partition state's desirability, on a support-regular state**:
`V(X) = ∑_e P(e) P_e(X) V_e(X) / ∑_e P(e) P_e(X)` with `P_e`, `V_e` the components.
Source: [[non-responsiveness]] "Axiom NR" (the K-partition sum); mandate T8
Kind: L -/
theorem kPart_V_of_suppRegular {E : Type} [Fintype E] [DecidableEq E] (s : State Ω K)
    (hs : SuppRegular s) (A : Finset Ω) (exo : Ω → E) (X : Finset Ω) :
    (kPart s A exo).V X =
      (∑ e, s.pr (cell exo e) * (kPartComp s A exo e).pr X * (kPartComp s A exo e).V X)
        / ∑ e, s.pr (cell exo e) * (kPartComp s A exo e).pr X :=
  mixState_V_of_suppRegular _ _ (fun e => suppRegular_kPartComp s hs A exo e) X

end regular

end Cleanroom.Decision.DpCausalConsist
