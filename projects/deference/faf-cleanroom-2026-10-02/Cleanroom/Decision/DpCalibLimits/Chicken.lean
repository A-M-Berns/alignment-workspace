import Cleanroom.Decision.DpCalibLimits.Defs

/-!
# T9 — The anti-zero-respecting (p-chicken) rule: no deterministic calibrated instantiation at
recorded points; fixed-point-free under advocacy with a unique maximiser

[[dp-calib-limits-mandate]] T9 (dp-sl-037, P10-8′, P04 Import 5, SL-13).

* `chicken_not_strict_of_deterministic_recorded`: at a recorded positive point, a deterministic
  `C(d) = δ_{a₀}` that is strictly calibrated has `P_{s_d}(a₀) = 1 > 1 − ε`, so the rule demands
  `C(d)(a₀) = 0` — contradiction. Lifted to abstract problems all of whose instances record at
  `d` (`chicken_inconsistent_on_recorded`).
* `chicken_no_fixed_point_of_unique_max`: self-transparency + `argmax = {a*}` + `T_EDT`
  approval force `C(d) = δ_{a*}` and `P(a*) = 1`, and the rule fires: no fixed point of "EDT
  + p-chicken" exists at such a point for any `ε ∈ (0, 1)`. Any advocacy theory with a unique
  maximiser behaves the same (the proof uses only the argmax singleton).
* Witness N+ on Told-You-So at `d₁₀` under `(ten, ten)`: recorded for every procedure
  (`tys_recordsFor_ten`), `ν(O₁₀) = 1`, strictly calibrated (`tys_take10_strictOC`),
  self-transparent, `argmax = {ten}`, approved — both theorems apply
  (`tys_chicken_instance`, `tys_chicken_refuses`).
* **Dead sharpening, recorded not proved** (P10-8′ Dead): "the EDT + p-chicken fixed point is at
  `1 − ε`" — the survivor is fixed-point-freeness. The XOR fixed point under 6′ (T9(d),
  stretch) is not attempted (it needs `dp-dutch-book`'s XOR tree).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

section general

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
  (B : Tree Ω ι acts K)

/-- **No deterministic strictly-calibrated instantiation obeys the chicken rule at a recorded
positive point**: `P_{s_d}(a₀) = 1` (`selfCertain_of_deterministic`) exceeds `1 − ε`, so the
rule demands `C(d)(a₀) = 0`, but `C(d)(a₀) = 1`.
Source: P10-8′; P04 Import 5 (the anti-zero-respecting rule); dp-sl-037
Kind: C
Fidelity: exact (per point, with the positivity guard)
Hyps: (a) `C d = δ_{a₀}`, (a) `RecordsFor`, (a) `0 < ν(O_d)`, (a) `StrictOCAt`, (a) `0 < ε` -/
theorem chicken_not_strict_of_deterministic_recorded (s : ι → State Ω K) {d : ι} (a₀ : acts d)
    (hC : C d = FinDistr.pure a₀) (hrec : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d) (ε : K) (hε : 0 < ε) :
    ¬ AntiZeroRespectingAt actEv C s ε d := by
  intro hchk
  obtain ⟨h1, -⟩ := selfCertain_of_deterministic obs actEv C B s a₀ hC hrec hpos hs
  have := hchk a₀ (by rw [h1]; linarith)
  rw [hC, FinDistr.pure_w, if_pos rfl] at this
  exact one_ne_zero this

/-- **Lift to abstract problems**: if every instantiation records at `d` with `ν(O_d) > 0`, no
strictly calibrated instantiation obeys the chicken rule at `d` for a deterministic `C`
(a `MakesInconsistent`-style statement).
Source: P10-8′; mandate T9(b)
Kind: L
Fidelity: exact -/
theorem chicken_inconsistent_on_recorded (AP : AbstractProblem Ω ι acts K) {d : ι} (a₀ : acts d)
    (hC : C d = FinDistr.pure a₀)
    (hrec : ∀ I ∈ AP, RecordsFor obs actEv C I.B d ∧ 0 < nu C I.B (obs d)) (ε : K)
    (hε : 0 < ε) :
    ∀ I ∈ AP, d ∈ queried I.B → IsCalibrated .strict obs I.s C I.B →
      ¬ AntiZeroRespectingAt actEv C I.s ε d :=
  fun I hI hd hcal =>
    chicken_not_strict_of_deterministic_recorded obs actEv C I.B I.s a₀ hC (hrec I hI).1
      (hrec I hI).2 (hcal d hd) ε hε

/-- **Fixed-point-freeness of EDT + p-chicken under a unique maximiser**: self-transparency,
`argmax_{A_d^+} V = {a*}` and `T_EDT` approval force `C(d) = δ_{a*}` and `P_{s_d}(a*) = 1`, and
the rule then demands `C(d)(a*) = 0`. The proof uses only the argmax singleton, so any
advocacy theory with a unique maximiser has no fixed point with the chicken rule.
Source: P10-8′ ("the survivor is fixed-point-freeness"); SL-13; dp-sl-037
Kind: C
Fidelity: exact
Hyps: (a) `SelfTransparent`, (a) `argmaxPlus = {a*}`, (a) `TEdtAt`, (a) `0 < ε < 1` -/
theorem chicken_no_fixed_point_of_unique_max (s : ι → State Ω K) {d : ι} (aStar : acts d)
    (hst : SelfTransparent s actEv C d) (hmax : argmaxPlus s actEv d = {aStar})
    (hT : TEdtAt s actEv C d) (ε : K) (hε : 0 < ε) (hε1 : ε < 1)
    (hchk : AntiZeroRespectingAt actEv C s ε d) : False := by
  have hne : (APlus s actEv d).Nonempty :=
    ⟨aStar, argmaxPlus_subset s actEv d (by rw [hmax]; exact Finset.mem_singleton_self _)⟩
  have hsupp : ∀ a, 0 < (C d).w a → a = aStar := fun a ha => by
    have := hT hne a ha
    rw [hmax, Finset.mem_singleton] at this
    exact this
  have hone : (C d).w aStar = 1 := by
    have := (C d).sum_one
    rw [Finset.sum_eq_single aStar] at this
    · exact this
    · intro b _ hb
      by_contra h
      exact hb (hsupp b (lt_of_le_of_ne ((C d).nonneg b) (Ne.symm h)))
    · intro h; exact absurd (Finset.mem_univ _) h
  have := hchk aStar (by rw [hst aStar, hone]; linarith)
  rw [hone] at this
  exact one_ne_zero this

end general

/-! ## Witness: Told-You-So at `d₁₀` under `(ten, ten)` -/

/-- **The hypothesis packages of both chicken theorems are inhabited on Told-You-So at `d₁₀`
under `(ten, ten)`**: recorded for every procedure, `ν(O₁₀) = 1`, strictly calibrated with
`tysState`, deterministic, self-transparent, `argmax = {ten}` and approved.
Source: mandate T9 (witness: a recorded point with a strict maximum — `ten ↦ 10 > 5`);
`dp-calibration` `tys_recordsFor_ten`, `tys_take10_strictOC`
Kind: N+
Fidelity: exact
Hyps: none -/
theorem tys_chicken_instance :
    RecordsFor tysObs tysActEv procTake10 toldYouSo .ten ∧
    0 < nu procTake10 toldYouSo (tysObs .ten) ∧
    StrictOCAt tysState tysObs procTake10 toldYouSo .ten ∧
    procTake10 .ten = FinDistr.pure .ten ∧
    SelfTransparent tysState tysActEv procTake10 .ten ∧
    argmaxPlus tysState tysActEv .ten = {.ten} ∧
    TEdtAt tysState tysActEv procTake10 .ten := by
  have hrec := tys_recordsFor_ten procTake10
  have hpos : 0 < nu procTake10 toldYouSo (tysObs .ten) := by
    rw [tys_nu_obs_ten]; simp [procTake10]
  have hs : StrictOCAt tysState tysObs procTake10 toldYouSo .ten :=
    tys_take10_strictOC .ten (tys_queried .ten)
  have hC : procTake10 .ten = FinDistr.pure .ten := by
    apply FinDistr.ext'; intro a; simp [procTake10]
  obtain ⟨hA, hT⟩ := tEdtAt_of_deterministic_recorded tysState tysActEv tysObs procTake10 toldYouSo
    .ten hC hrec hpos hs
  refine ⟨hrec, hpos, hs, hC, selfTransparent_of_recordsFor_strict tysObs tysActEv procTake10
    toldYouSo tysState hrec hpos hs, ?_, hT⟩
  have hsub : argmaxPlus tysState tysActEv .ten ⊆ {Five10.ten} := by
    rw [← hA]; exact argmaxPlus_subset _ _ _
  exact (Finset.Nonempty.subset_singleton_iff
    (argmaxPlus_nonempty _ _ _ (by rw [hA]; exact Finset.singleton_nonempty _))).mp hsub

/-- **On Told-You-So at `d₁₀` the chicken rule is refused by both routes** for every `ε ∈ (0,1)`:
the deterministic-recorded route and the fixed-point route.
Source: P10-8′; mandate T9 (witness)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem tys_chicken_refuses (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) :
    ¬ AntiZeroRespectingAt tysActEv procTake10 tysState ε .ten := by
  obtain ⟨hrec, hpos, hs, hC, hst, hmax, hT⟩ := tys_chicken_instance
  intro hchk
  exact chicken_no_fixed_point_of_unique_max tysActEv procTake10 tysState .ten hst hmax hT ε hε
    hε1 hchk

end Cleanroom.Decision.DpCalibLimits
