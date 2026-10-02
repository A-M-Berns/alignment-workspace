import Cleanroom.Decision.DpEdtUdtFair.Theorem3

/-!
# The devices on `𝔉`: D2 ≡ D3 (T12(a))

`calibration.md` CA-16′: on `𝔉` the observation-conditioned tremble device (D2,
`EventTrembleEdtConsistent`) and the occurrence-weighted one (D3, `OccTrembleEdtConsistent`,
Theorem 1's evaluator under `C^ε`) are one condition. Route: `fiberForced B (ofProc C' B) d a =
siaSum C' B d a` (`fiberForced_eq_siaSum`, both are the fiber sum of `forcedBelow`), and on strongly
fair trees `siaSum C' B d a = fiberMass_d(C') · Q_{C'}(d, a)` (`dp-local-opt`'s
`siaSum_eq_fiberMass_mul_of_iso` with the reference `refChildren`); D2 in `Q`-form
(`FairClass.eventTremble_iff_Q`) then compares the same values, up to the positive factor
`fiberMass` (`FairClass.fiberMass_pos`).

**No evented chance is used**: A36(iv)'s EC-free form holds (dp-cf-2-063 note 2 settled; findings).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

omit [Fintype Ω] [DecidableEq Ω] in
/-- `dp-calibration`'s `fiberForced` at the tied node policy is `dp-local-opt`'s `siaSum`
(both are `∑_{q ∈ F_d} forcedBelow`; the casts along `pt B q = d` agree).
Source: `calibration.md` D3 ("`dp-local-opt` owns the functional; this is its name here")
Kind: L -/
theorem fiberForced_eq_siaSum [∀ d, Nonempty (acts d)] (C : Proc ι acts K)
    (B : Tree Ω ι acts K) (d : ι) (a : acts d) :
    fiberForced B (NodePolicy.ofProc C B) d a = siaSum C B d a := by
  rw [siaSum_eq_sum_fiber_forcedBelow]
  unfold fiberForced
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with h
  · subst h; rfl
  · rfl

/-- On strongly fair trees `siaSum C B d a = fiberMass_d(C) · Q_C(d, a)` at every queried `d`.
Source: A36 Lemma 4 ("Theorem 1's weighted sum at `d` is `𝔼_μ[#_d] · G(C, a)` with `G`
node-independent"); `dp-local-opt`'s `siaSum_eq_fiberMass_mul_of_iso`
Kind: C -/
theorem stronglyFair_siaSum_eq [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (hB : StronglyFair B) (C : Proc ι acts K) {d : ι} (hd : d ∈ queried B) (a : acts d) :
    siaSum C B d a = fiberMass C B d * Q C B d a :=
  siaSum_eq_fiberMass_mul_of_iso C d (refChildren B d) B (stronglyFair_iso_ref hB hd) a

section ca16

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- **CA-16′ — on `𝔉`, D2 ≡ D3**: event-tremble-EDT-consistency and occurrence-tremble-EDT-
consistency coincide. Both compare `Q_{C^ε}(d, ·)` at every queried `d` (D2 through Step 1, D3
through `fiberForced = siaSum = fiberMass · Q`), and `fiberMass_d(C^ε) > 0` on `𝔉`. The
equivalence is exact only because of that positivity (proved, not assumed). No evented chance is
used: A36(iv)'s EC-free form holds.
Source: `calibration.md` CA-16′ ("on `𝔉`, D2 ≡ D3 at every `ε`"); A36 (iv); dp-cf-042,
dp-cf-2-053; dp-cf-2-063 note 2 (the EC doubt, settled)
Kind: C
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.eventTremble_iff_occTremble [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K) :
    EventTrembleEdtConsistent obs actEv C B ↔ OccTrembleEdtConsistent C B := by
  rw [h.eventTremble_iff_Q C]
  unfold OccTrembleEdtConsistent
  constructor
  · rintro ⟨ε₀, hε₀, hQ⟩
    refine ⟨ε₀, hε₀, fun ε h0 h1 hlt d hd a ha b => ?_⟩
    rw [fiberForced_eq_siaSum, fiberForced_eq_siaSum, stronglyFair_siaSum_eq h.stronglyFair _ hd,
      stronglyFair_siaSum_eq h.stronglyFair _ hd]
    exact mul_le_mul_of_nonneg_left (hQ ε h0 h1 hlt d hd a ha b) (fiberMass_nonneg _ B d)
  · rintro ⟨ε₀, hε₀, hocc⟩
    refine ⟨ε₀, hε₀, fun ε h0 h1 hlt d hd a ha b => ?_⟩
    have := hocc ε h0 h1 hlt d hd a ha b
    rw [fiberForced_eq_siaSum, fiberForced_eq_siaSum, stronglyFair_siaSum_eq h.stronglyFair _ hd,
      stronglyFair_siaSum_eq h.stronglyFair _ hd] at this
    exact le_of_mul_le_mul_left this (h.fiberMass_pos (tremble_fullSupport C ε h0 h1) hd)

/-- On `𝔉`, D3 implies optimality too (CA-16′ + Theorem 3).
Source: `calibration.md` CA-16′ ("all three imply optimality")
Kind: C -/
theorem occTrembleEdt_isOptimal_of_fairClass [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C : Proc ι acts K}
    (hC : OccTrembleEdtConsistent C B) : IsOptimal C B :=
  eventTrembleEdt_isOptimal_of_fairClass h ((h.eventTremble_iff_occTremble C).mpr hC)

end ca16

end Cleanroom.Decision.DpEdtUdtFair
