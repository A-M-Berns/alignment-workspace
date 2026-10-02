import Cleanroom.Decision.DpCalibLimits.AppendixB
import Cleanroom.Decision.DpCalibLimits.Rays

/-!
# T13 — Q-traps: trap rays, Lemma 2 survives, and the price (the device is silent on a trap)

[[dp-calib-limits-mandate]] T13 (dp-sl-2-023, P07 I3′, Open 10) — the nearest well-posed
versions of Q-traps' static question.

* A **trap ray** (`IsTrapRay`): a ray starting at `C` whose weight on a stipulated trap act `a`
  with `C(d)(a) = 0` is the zero polynomial (no `ε`-term: the trap is never explored).
* **(i) Lemma 2 survives every ray**, trap rays included (`limitOCRayAt_imp_strictOCAt_trap`):
  the refinement of strict calibration is ray-free (T2(e) restated).
* **(ii) The price** (`nuPolyRay_trap_eq_zero`, `advice_silent_on_trap`): at a trap act the
  event polynomial vanishes (every leaf in the `a`-event takes the `a`-edge, whose weight is
  `0`), so `limitValRay` at `a` is junk and the D4-analogue along the ray never compares `a` —
  the device is *silent* on the trap: it neither approves nor rejects it. N+ on the one-point
  two-action tree `t1` with `C = δ_b` and trap act `a` (`t1_trap_instance`).
* **(iii)** per-act rays reopen ray dependence: `twoRoute_values` (T2(c)).
* Clause (ii) of the source's question (pricing the refuser trap of DY-13–15) is dynamic and
  out of scope.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

section traps

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- **A trap ray**: starts at `C`, and the stipulated trap act `a` (with `C(d)(a) = 0`) gets
the zero polynomial — no exploration of the trap.
Source: P07 I3′ ("per-act tremble weights `ε_a` with `ε_a = 0` permitted at stipulated traps")
Kind: D -/
def IsTrapRay (R : Ray ι acts K) (C : Proc ι acts K) (d : ι) (a : acts d) : Prop :=
  IsRayOf R C ∧ (C d).w a = 0 ∧ R.w d a = 0

/-- **(i) Lemma 2 survives every trap ray**: ray-limit calibration refines strict calibration
along a trap ray too (T2(e) restated).
Source: P07 I3′ ("keeps Lemma 2's refinement of strict calibration?"); mandate T13(i)
Kind: L
Fidelity: exact -/
theorem limitOCRayAt_imp_strictOCAt_trap (R : Ray ι acts K) (C : Proc ι acts K) {d : ι}
    {a : acts d} (h : IsTrapRay R C d a) (s : ι → State Ω K) (obs : ι → Finset Ω)
    (B : Tree Ω ι acts K) (d' : ι) (hl : LimitOCRayAt R s obs B d') : StrictOCAt s obs C B d' :=
  limitOCRayAt_imp_strictOCAt R h.1 s obs B d' hl

/-- A leaf whose path takes a `d`-edge of zero ray weight has zero leaf polynomial.
Source: none: infrastructure. Kind: L -/
theorem leafLawPolyRay_eq_zero_of_mem_draws (R : Ray ι acts K) {d : ι} {a : acts d}
    (hz : R.w d a = 0) :
    (B : Tree Ω ι acts K) → ∀ ℓ, (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ → leafLawPolyRay R B ℓ = 0
  | .leaf _ _, _, h => by simp at h
  | .chance _ β child, ⟨i, ℓ⟩, h => by
      rw [draws_chance] at h
      simp only [leafLawPolyRay]
      rw [leafLawPolyRay_eq_zero_of_mem_draws R hz (child i) ℓ h, mul_zero]
  | .decision d' child, ⟨b, ℓ⟩, h => by
      rw [draws_decision, List.mem_cons] at h
      simp only [leafLawPolyRay]
      rcases h with h | h
      · obtain ⟨rfl, hb⟩ := Sigma.mk.inj_iff.mp h
        have hab := eq_of_heq hb
        subst hab
        rw [hz, zero_mul]
      · rw [leafLawPolyRay_eq_zero_of_mem_draws R hz (child b) ℓ h, mul_zero]

/-- **(ii) The price**: along a trap ray the trap act's event polynomial vanishes, when every
leaf in the `a`-event takes the `a`-edge somewhere on its path (the action event records the
draw). So `limitValRay` at `a` is junk and no tremble device along the ray compares `a`.
Source: P07 I3′ (Q-traps); mandate T13(ii)
Kind: P
Fidelity: exact
Hyps: (a) `IsTrapRay`, (a) the `a`-event records the `a`-draw -/
theorem nuPolyRay_trap_eq_zero (R : Ray ι acts K) (C : Proc ι acts K) {d : ι} {a : acts d}
    (h : IsTrapRay R C d a) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (B : Tree Ω ι acts K)
    (hrec : ∀ ℓ, world B ℓ ∈ actEv d a → (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ) :
    nuPolyRay R B (actEv d a ∩ obs d) = 0 := by
  unfold nuPolyRay
  apply Finset.sum_eq_zero
  intro ℓ hℓ
  rw [mem_worldEv, Finset.mem_inter] at hℓ
  exact leafLawPolyRay_eq_zero_of_mem_draws R h.2.2 B ℓ (hrec ℓ hℓ.1)

/-- **The D4-analogue along a ray** (`limitValRay` in place of `limitVal`): the advice device
read along `R`.
Source: `calibration.md` D4 along a ray (P07 I2′); mandate T13(ii) ("the D4-analogue over `R`")
Kind: D -/
def AdviceEdtRay (R : Ray ι acts K) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) : Prop :=
  ∀ d ∈ queried B, nuPolyRay R B (obs d) ≠ 0 → (∃ b, nuPolyRay R B (actEv d b ∩ obs d) ≠ 0) →
    ∀ a, 0 < (C d).w a →
    nuPolyRay R B (actEv d a ∩ obs d) ≠ 0 ∧
    ∀ b, nuPolyRay R B (actEv d b ∩ obs d) ≠ 0 →
      limitValRay R B (actEv d b ∩ obs d) ≤ limitValRay R B (actEv d a ∩ obs d)

/-- **The device is silent on the trap**: along a trap ray, `AdviceEdtRay` at `d` is exactly the
same condition with the trap act removed from every comparison — no clause of the device
mentions `a` (its guard `nuPolyRay (a ∧ O_d) ≠ 0` fails, and `C(d)(a) = 0` keeps it out of the
support).
Source: P07 I3′; mandate T13(ii) ("every tremble device … is *silent* on `a`")
Kind: C (regraded from P in repair round 1: clause bookkeeping over `nuPolyRay_trap_eq_zero`
and `C(d)(a) = 0`)
Fidelity: exact
Hyps: (a) `IsTrapRay`, (a) the `a`-event records the `a`-draw -/
theorem advice_silent_on_trap (R : Ray ι acts K) (C : Proc ι acts K) {d : ι} {a : acts d}
    (h : IsTrapRay R C d a) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
    (B : Tree Ω ι acts K)
    (hrec : ∀ ℓ, world B ℓ ∈ actEv d a → (⟨d, a⟩ : Σ d, acts d) ∈ draws B ℓ) :
    (nuPolyRay R B (obs d) ≠ 0 → (∃ b, nuPolyRay R B (actEv d b ∩ obs d) ≠ 0) →
      ∀ a', 0 < (C d).w a' →
      nuPolyRay R B (actEv d a' ∩ obs d) ≠ 0 ∧
      ∀ b, nuPolyRay R B (actEv d b ∩ obs d) ≠ 0 →
        limitValRay R B (actEv d b ∩ obs d) ≤ limitValRay R B (actEv d a' ∩ obs d)) ↔
    (nuPolyRay R B (obs d) ≠ 0 → (∃ b, b ≠ a ∧ nuPolyRay R B (actEv d b ∩ obs d) ≠ 0) →
      ∀ a', a' ≠ a → 0 < (C d).w a' →
      nuPolyRay R B (actEv d a' ∩ obs d) ≠ 0 ∧
      ∀ b, b ≠ a → nuPolyRay R B (actEv d b ∩ obs d) ≠ 0 →
        limitValRay R B (actEv d b ∩ obs d) ≤ limitValRay R B (actEv d a' ∩ obs d)) := by
  have hz := nuPolyRay_trap_eq_zero R C h obs actEv B hrec
  constructor
  · intro H hO ⟨b, _, hb⟩ a' _ ha'
    obtain ⟨h1, h2⟩ := H hO ⟨b, hb⟩ a' ha'
    exact ⟨h1, fun b' _ hb' => h2 b' hb'⟩
  · intro H hO ⟨b, hb⟩ a' ha'
    have hba : b ≠ a := fun hba => hb (by rw [hba]; exact hz)
    have ha'a : a' ≠ a := fun haa => by rw [haa, h.2.1] at ha'; exact lt_irrefl 0 ha'
    obtain ⟨h1, h2⟩ := H hO ⟨b, hba, hb⟩ a' ha'a ha'
    refine ⟨h1, fun b' hb' => ?_⟩
    have hb'a : b' ≠ a := fun hba => hb' (by rw [hba]; exact hz)
    exact h2 b' hb'a hb'

end traps

/-! ## N+: the one-point two-action tree `t1` with `C = δ_b` and trap act `a` -/

/-- `δ_b` on `t1`. Source: mandate T13(ii) (witness). Kind: D -/
def procB1 : Proc Unit (fun _ => Act2) ℚ := fun _ => FinDistr.pure .b

/-- The trap ray on `t1`: `w a = 0`, `w b = 1`. Source: mandate T13(ii). Kind: D -/
noncomputable def t1TrapRay : Ray Unit (fun _ => Act2) ℚ where
  w := fun _ x => match x with
    | .a => 0
    | .b => Polynomial.C 1
  sum_one _ := by rw [Act2.sum_univ]; simp
  posTrail _ x := by
    cases x
    · exact PosTrail.zero
    · exact PosTrail.C zero_le_one

/-- **The trap package on `t1`**: `t1TrapRay` is a trap ray for `δ_b` at `a`, the `a`-event
records the `a`-draw, and the trap act's event polynomial vanishes — the device is silent on
`a`. Source: mandate T13(ii). Kind: N+. Fidelity: exact. Hyps: none -/
theorem t1_trap_instance :
    IsTrapRay t1TrapRay procB1 () .a ∧
    (∀ ℓ : t1.Leaves, world t1 ℓ ∈ t1ActEv () .a → (⟨(), Act2.a⟩ : Σ d : Unit, Act2) ∈ draws t1 ℓ) ∧
    nuPolyRay t1TrapRay t1 (t1ActEv () .a ∩ t1Obs ()) = 0 := by
  have hrec : ∀ ℓ : t1.Leaves, world t1 ℓ ∈ t1ActEv () .a →
      (⟨(), Act2.a⟩ : Σ d : Unit, Act2) ∈ draws t1 ℓ := by
    rintro ⟨x, _⟩ hx
    cases x
    · simp [t1, draws]
    · simp [t1, t1ActEv] at hx
  have htrap : IsTrapRay t1TrapRay procB1 () .a :=
    ⟨fun _ x => by cases x <;> simp [t1TrapRay, procB1], by simp [procB1], rfl⟩
  exact ⟨htrap, hrec, nuPolyRay_trap_eq_zero t1TrapRay procB1 htrap t1Obs t1ActEv t1 hrec⟩

end Cleanroom.Decision.DpCalibLimits
