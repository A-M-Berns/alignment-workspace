import Cleanroom.Decision.DpFirstpersonSc.License

/-!
# AN-3′'s `V`-clause criterion — T3(b), second half, of [[dp-firstperson-sc-mandate]]

Given the `P`-clause (the per-run state's `P` is `ν(· | X)` with `X` the per-run support —
`occState_P_eq_nuCondDistr_iff` gives the criterion for that), the per-run state's `V` agrees with
the strict-OC state's `V` at `X` on every event of positive probability **iff** for every world
`w` realized on occ-leaves the `μ`-mean payoff over the occ-leaves of `w` equals the `μ`-mean over
all leaves of `w`, in multiplicative form `occPay{w} · ν{w} = paySum{w} · μ(occEv{w})`
(`occState_V_eq_calibratedState_iff`). The instance-blind tree (`WitnessesAn3.lean`,
`blind_V_criterion_fails`) is the N+ where the `P`-clause holds and this fails.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- `paySum X = ∑_{ω ∈ X} paySum {ω}`. Source: none: infrastructure. Kind: L -/
theorem paySum_eq_sum_singleton (X : Finset Ω) : paySum C B X = ∑ ω ∈ X, paySum C B {ω} := by
  simp only [paySum_eq_sum_ite, Finset.mem_singleton]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.sum_ite_eq]

/-- `occPay` as an indicator sum over `occ(d)`. Source: none: infrastructure. Kind: L -/
theorem occPay_eq_sum (X : Finset Ω) :
    occPay C B d X = ∑ ℓ ∈ occ d B, if world B ℓ ∈ X then leafLaw C B ℓ * payoff B ℓ else 0 := by
  unfold occPay; rw [occEv_eq_filter, Finset.sum_filter]

/-- `occPay X = ∑_{ω ∈ X} occPay {ω}`. Source: none: infrastructure. Kind: L -/
theorem occPay_eq_sum_singleton (X : Finset Ω) :
    occPay C B d X = ∑ ω ∈ X, occPay C B d {ω} := by
  simp only [occPay_eq_sum, Finset.mem_singleton]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.sum_ite_eq]

/-- A world of zero occurrence mass has zero occurrence payoff mass. Source: none: infrastructure.
Kind: L -/
theorem occPay_singleton_eq_zero (ω : Ω) (h : Tree.mass C B (occEv B d {ω}) = 0) :
    occPay C B d {ω} = 0 := by
  unfold occPay
  rw [mass_eq_zero_iff] at h
  exact Finset.sum_eq_zero fun ℓ hℓ => by rw [h ℓ hℓ, zero_mul]

/-- The per-run support has positive `ν`-mass. Source: none: infrastructure. Kind: L -/
theorem nu_perRunSupport_pos (h : 0 < Tree.mass C B (occ d B)) :
    0 < nu C B (perRunSupport C B d) := by
  rw [nu_eq_sum_singleton]
  calc 0 < Tree.mass C B (occ d B) := h
    _ = ∑ ω ∈ perRunSupport C B d, Tree.mass C B (occEv B d {ω}) := mass_occ_eq_sum_support C B d
    _ ≤ ∑ ω ∈ perRunSupport C B d, nu C B {ω} :=
        Finset.sum_le_sum fun ω _ => mass_occEv_singleton_le_nu C B d ω

/-- **AN-3′, the `V`-clause criterion**: under the `P`-clause (the per-run `P` is `ν(· | X)`, `X`
the per-run support), the per-run state's `V` agrees with the strict state's `V` at `X` on every
event of positive probability iff, for every world `w` of the support, the `μ`-mean payoff over
the occ-leaves of `w` equals the `μ`-mean over all leaves of `w`
(`occPay{w} · ν{w} = paySum{w} · μ(occEv{w})`). With `occState_P_eq_nuCondDistr_iff` this is the
full "per-run SSC = strict OC at some event" criterion; expressibility implies it (no world
straddles the sides); non-expressibility decides nothing (`WitnessesAn3.lean`).
Source: `anticipation.md` AN-3′ ("`V`-clause: additionally iff, for every world `w` realized on
occ-leaves, the `μ`-mean payoff over the occ-leaves of `w` equals the `μ`-mean over all leaves of
`w`"); v2 Q3
Kind: P
Fidelity: exact (multiplicative form; events of positive probability)
Hyps: (a) `μ(occ(d)) > 0`; (a) the `P`-clause at the per-run support -/
theorem occState_V_eq_calibratedState_iff (h : 0 < Tree.mass C B (occ d B))
    (hX : 0 < nu C B (perRunSupport C B d))
    (hP : (occState C B d h).P = nuCondDistr C B (perRunSupport C B d) hX) :
    (∀ Y, 0 < nu C B (Y ∩ perRunSupport C B d) →
        (occState C B d h).V Y = (calibratedState C B (perRunSupport C B d) hX).V Y) ↔
      ∀ ω ∈ perRunSupport C B d,
        occPay C B d {ω} * nu C B {ω} = paySum C B {ω} * Tree.mass C B (occEv B d {ω}) := by
  have hw0 : ∀ ω, (occState C B d h).P.w ω =
      Tree.mass C B (occEv B d {ω}) / Tree.mass C B (occ d B) := fun _ => rfl
  have hw : ∀ ω, Tree.mass C B (occEv B d {ω}) / Tree.mass C B (occ d B) =
      if ω ∈ perRunSupport C B d then nu C B {ω} / nu C B (perRunSupport C B d) else 0 := by
    intro ω
    have := congrArg (fun P : FinDistr K Ω => P.w ω) hP
    simp only [hw0, nuCondDistr] at this
    exact this
  have hsub : ∀ ω ∈ perRunSupport C B d, {ω} ∩ perRunSupport C B d = {ω} := fun ω hω =>
    Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hω)
  have hm_of_mem : ∀ ω ∈ perRunSupport C B d, Tree.mass C B (occEv B d {ω}) =
      (Tree.mass C B (occ d B) / nu C B (perRunSupport C B d)) * nu C B {ω} := by
    intro ω hω
    have := hw ω
    rw [if_pos hω, div_eq_div_iff h.ne' hX.ne'] at this
    rw [div_mul_eq_mul_div, eq_div_iff hX.ne', this, mul_comm]
  have hm_zero : ∀ ω, ω ∉ perRunSupport C B d → Tree.mass C B (occEv B d {ω}) = 0 := by
    intro ω hω
    simp only [perRunSupport, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hω
    exact le_antisymm hω (Tree.mass_nonneg C B _)
  have hm_pos : ∀ ω ∈ perRunSupport C B d, 0 < Tree.mass C B (occEv B d {ω}) := by
    intro ω hω
    simpa only [perRunSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hω
  have hnu_pos : ∀ ω ∈ perRunSupport C B d, 0 < nu C B {ω} := fun ω hω =>
    lt_of_lt_of_le (hm_pos ω hω) (mass_occEv_singleton_le_nu C B d ω)
  have hc : 0 < Tree.mass C B (occ d B) / nu C B (perRunSupport C B d) := div_pos h hX
  constructor
  · intro hV ω hω
    have hpos : 0 < nu C B ({ω} ∩ perRunSupport C B d) := by
      rw [hsub ω hω]; exact hnu_pos ω hω
    have := hV {ω} hpos
    rw [occState_V, calibratedState_V, hsub ω hω,
      div_eq_div_iff (hm_pos ω hω).ne' (hnu_pos ω hω).ne'] at this
    exact this
  · intro hcrit Y hY
    rw [occState_V, calibratedState_V]
    have hpay : occPay C B d Y =
        (Tree.mass C B (occ d B) / nu C B (perRunSupport C B d)) *
          paySum C B (Y ∩ perRunSupport C B d) := by
      rw [occPay_eq_sum_singleton C B d Y, paySum_eq_sum_singleton C B (Y ∩ perRunSupport C B d),
        Finset.mul_sum, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases hω : ω ∈ perRunSupport C B d
      · rw [if_pos hω]
        have hcrit' := hcrit ω hω
        rw [hm_of_mem ω hω] at hcrit'
        have key : occPay C B d {ω} * nu C B {ω} =
            (Tree.mass C B (occ d B) / nu C B (perRunSupport C B d) * paySum C B {ω}) *
              nu C B {ω} := by
          rw [hcrit']; ring
        exact mul_right_cancel₀ (hnu_pos ω hω).ne' key
      · rw [if_neg hω]
        exact occPay_singleton_eq_zero C B d ω (hm_zero ω hω)
    have hmass : Tree.mass C B (occEv B d Y) =
        (Tree.mass C B (occ d B) / nu C B (perRunSupport C B d)) *
          nu C B (Y ∩ perRunSupport C B d) := by
      rw [← sum_mass_occEv_singleton C B d Y, nu_eq_sum_singleton C B (Y ∩ perRunSupport C B d),
        Finset.mul_sum, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases hω : ω ∈ perRunSupport C B d
      · rw [if_pos hω]; exact hm_of_mem ω hω
      · rw [if_neg hω]; exact hm_zero ω hω
    rw [hpay, hmass, mul_div_mul_left _ _ hc.ne']

end Cleanroom.Decision.DpFirstpersonSc
