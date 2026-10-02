import Cleanroom.Decision.DpFirstpersonSc.Dogmatic
import Cleanroom.Decision.DpFirstpersonSc.WitnessesNewcomb

/-!
# Witnesses for T6: the two failures of the unconditional converse of Proposition 1

* **AN-14(ii)'s refutation, `⟹` without `ν(O_d) > 0` at reachable points** — TN-V2 with a
  perfect predictor (`p = 1`) and the one-boxer `(1,1)`, the strict-OC state installed at `d_F`
  and anything at `d_E`: `StrictOC` holds (`d_F` calibrated, `d_E` vacuous since `ν(O_E) = 0`),
  but `d_E` is reachable (queried hypothetically at the root on every run, `μ(occ(d_E)) = 1`) and
  `P_{s₀}(O_E) = 0`, so the dogmatic existential fails (`tnV2_perfect_strictOC_not_dogmatic`).
* **The missing hypothesis of the `⟸` (finding F3)** — Told-You-So under take-5 at both points
  with the radical observation `O = ⊤` at both points and the stipulated states: the dogmatic
  epistemology holds (`d₅` reachable and `s₅ = δ_{(5,5)} = ν`; `d₁₀` unreachable, vacuous) while
  strict OC fails at `d₁₀` (`ν(⊤) = 1 > 0` demands `s₁₀ = δ_{(5,5)}`, but `s₁₀ = δ_{(10,10)}`):
  `tys_dogmatic_not_strictOC`. So AN-14(ii)'s iff needs *both* coincidences
  (`strictOC_iff_dogmatic`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-! ## TN-V2, perfect predictor, one-boxer -/

section tnV2

variable (L S : ℚ)

/-- V2 with a perfect predictor. Source: [[decision-problems-v2]] Observation 1. Kind: D -/
abbrev tnV2Perfect : Tree TnW TnPt (fun _ => Box) ℚ := tnV2 1 (by norm_num) (by norm_num) L S

/-- `ν(O_E) = 0` under the one-boxer with a perfect predictor: every run ends full.
Source: `anticipation.md` AN-14(ii) ("`ν(O_E) = 0`")
Kind: L -/
theorem tnV2_perfect_large_nu_E : nu procLarge (tnV2Perfect L S) (tnObs .E) = 0 := by
  rw [nu_eq_sum, tnV2_sum]
  simp only [tnV2_world, tnV2_leafLaw]
  simp [box_sum_univ, Fin.sum_univ_two, procLarge, tnObs]

/-- `ν(O_F) = 1 > 0` under the one-boxer with a perfect predictor. Source: none: infrastructure.
Kind: L -/
theorem tnV2_perfect_large_nu_F_pos : 0 < nu procLarge (tnV2Perfect L S) (tnObs .F) := by
  rw [nu_eq_sum, tnV2_sum]
  simp only [tnV2_world, tnV2_leafLaw]
  simp [box_sum_univ, Fin.sum_univ_two, procLarge, tnObs]

/-- `d_E` is queried on V2. Source: none: infrastructure. Kind: L -/
theorem tnV2_E_queried : TnPt.E ∈ queried (tnV2Perfect L S) := by
  unfold tnV2Perfect tnV2
  simp [queried_decision]

/-- The states of the refutation: the strict-OC state at `d_F`, the default state at `d_E`.
Source: `anticipation.md` AN-14(ii) ("strict-OC state installed at `d_F`")
Kind: D -/
noncomputable def tnV2PerfectStates : TnPt → State TnW ℚ := fun d =>
  if d = .F then calibratedState procLarge (tnV2Perfect L S) (tnObs .F)
    (tnV2_perfect_large_nu_F_pos L S) else State.trivial

/-- **The unconditional converse of Proposition 1 is refuted (`⟹`)**: on V2 with a perfect
predictor and the one-boxer, strict OC holds at every queried point (`d_F` calibrated, `d_E`
vacuous) yet the dogmatic epistemology relative to the prior state fails — `d_E` is reachable
with `P_{s₀}(O_E) = ν(O_E) = 0`.
Source: `anticipation.md` AN-14(ii) ("Without it the `⟹` fails: TN-V2, `p = 1`, `(1,1)` …"),
Dead 5 ("AN-14(ii)'s unconditional converse … Killer: TN-V2, `p = 1`, `(1,1)` — `d_E` reachable,
`ν(O_E) = 0`")
Kind: N+
Fidelity: exact -/
theorem tnV2_perfect_strictOC_not_dogmatic :
    StrictOC (tnV2PerfectStates L S) tnObs procLarge (tnV2Perfect L S) ∧
    ¬ DogmaticEpistemology tnObs procLarge (tnV2Perfect L S)
        (priorState procLarge (tnV2Perfect L S)) (tnV2PerfectStates L S) := by
  constructor
  · intro d _ hpos
    cases d
    · exact strictClausesAt_calibratedState tnObs procLarge (tnV2Perfect L S) _ .F
        (tnV2_perfect_large_nu_F_pos L S) (by simp [tnV2PerfectStates])
    · exfalso
      rw [tnV2_perfect_large_nu_E] at hpos
      exact lt_irrefl 0 hpos
  · intro hdog
    have hr : Reachable procLarge (tnV2Perfect L S) .E := by
      unfold Reachable
      rw [tnV2_occ_E, mass_univ]; exact zero_lt_one
    obtain ⟨h, -⟩ := hdog .E (tnV2_E_queried L S) hr
    rw [priorState_pr, tnV2_perfect_large_nu_E] at h
    exact lt_irrefl 0 h

end tnV2

/-! ## Told-You-So with the radical observation -/

section tys

/-- The radical observation `O = ⊤` at both Told-You-So points. Source: mandate T6 (finding F3's
witness design). Kind: D -/
def tysTop : Five10 → Finset TysW := fun _ => Finset.univ

/-- `occ(d₁₀)` is null under take-5 at both points. Source: [[decision-problems-v2]] Lemma 2
proof. Kind: L -/
theorem tys_take5_occ_ten_null : mass procTake5 toldYouSo (occ .ten toldYouSo) = 0 := by
  rw [mass_eq_sum_ite', tys_sum]
  simp only [mem_occ]
  have c1 : count .ten toldYouSo ⟨.five, ()⟩ = 0 := by simp [toldYouSo, count_decision]
  have c2 : count .ten toldYouSo ⟨.ten, .ten, ()⟩ = 1 := by simp [toldYouSo, count_decision]
  have c3 : count .ten toldYouSo ⟨.ten, .five, ()⟩ = 1 := by simp [toldYouSo, count_decision]
  rw [c1, c2, c3]
  simp [toldYouSo, leafLaw_decision, procTake5]

/-- `d₁₀` is not reachable under take-5, although `ν(⊤) = 1 > 0`: the mismatch the `⟸` of the
converse needs excluded.
Source: mandate T6; finding F3
Kind: L -/
theorem tys_take5_ten_unreachable_pos :
    ¬ Reachable procTake5 toldYouSo .ten ∧ 0 < nu procTake5 toldYouSo (tysTop .ten) := by
  constructor
  · unfold Reachable; rw [tys_take5_occ_ten_null]; exact lt_irrefl 0
  · rw [show tysTop Five10.ten = Finset.univ from rfl, nu_univ]; exact zero_lt_one

/-- The prior state's desirability of an event containing `(5,5)` under take-5 is `5`.
Source: none: infrastructure. Kind: L -/
theorem tys_take5_priorState_V (X : Finset TysW) (hX : (Five10.five, Five10.five) ∈ X) :
    (priorState procTake5 toldYouSo).V X = 5 := by
  rw [priorState_V, tys_paySum, tys_nu]
  simp [hX, procTake5]

/-- **Finding F3's witness: the dogmatic epistemology does not imply strict OC without "every
`ν`-positive queried observation is reachable"**: on Told-You-So under take-5 with `O = ⊤` at both
points and the stipulated states, the dogmatic epistemology relative to the prior state holds
(`d₅`: reachable, `s₅ = δ_{(5,5)}` agrees with `ν` conditioned on `⊤`; `d₁₀`: unreachable,
vacuous) while strict OC fails at `d₁₀` (`ν(⊤) > 0` demands `δ_{(5,5)}`, the stipulated state is
`δ_{(10,10)}`).
Source: `anticipation.md` AN-14(ii) (the stated iff, whose `⟸` this refutes as stated);
[[decision-problems-v2]] Definition 19
Kind: N+
Fidelity: exact -/
theorem tys_dogmatic_not_strictOC :
    DogmaticEpistemology tysTop procTake5 toldYouSo (priorState procTake5 toldYouSo) tysState ∧
    ¬ StrictOC tysState tysTop procTake5 toldYouSo := by
  constructor
  · intro d _ hr
    cases d
    · have h : 0 < (priorState procTake5 toldYouSo).pr (tysTop .five) := by
        rw [priorState_pr, show tysTop Five10.five = Finset.univ from rfl, nu_univ]
        exact zero_lt_one
      refine ⟨h, ?_, fun X hX => ?_⟩
      · apply FinDistr.ext'
        intro ω
        show (if ω = (Five10.five, Five10.five) then (1 : ℚ) else 0) =
          if ω ∈ (Finset.univ : Finset TysW) then (priorState procTake5 toldYouSo).P.w ω /
            (priorState procTake5 toldYouSo).pr Finset.univ else 0
        have hp : (priorState procTake5 toldYouSo).P.w ω = nu procTake5 toldYouSo {ω} := by
          have := priorState_pr procTake5 toldYouSo {ω}
          simp only [State.pr, probOf_singleton] at this
          exact this
        rw [if_pos (Finset.mem_univ ω), hp, priorState_pr, nu_univ, div_one, tys_nu]
        rcases ω with ⟨n, m⟩
        cases n <;> cases m <;> simp [procTake5]
      · rw [jeffreyCond_V, show tysTop Five10.five = Finset.univ from rfl, Finset.inter_univ]
        have hX5 : (Five10.five, Five10.five) ∈ X := by
          by_contra hc
          simp only [tysState, State.dirac_pr, hc, if_false] at hX
          exact lt_irrefl 0 hX
        rw [tys_take5_priorState_V X hX5]
        rfl
    · exfalso
      exact (tys_take5_ten_unreachable_pos).1 hr
  · intro hoc
    have := (hoc .ten (tys_queried .ten) (tys_take5_ten_unreachable_pos).2).1
      {(Five10.ten, Five10.ten)}
    rw [tysTop] at this
    simp only [Finset.inter_univ, nu_univ, mul_one] at this
    rw [tys_nu] at this
    simp [tysState, State.dirac, State.ofConst, FinDistr.pure_w, procTake5] at this

end tys

end Cleanroom.Decision.DpFirstpersonSc
