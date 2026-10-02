import Cleanroom.Decision.DpEdtUdtFair.Necessity
import Cleanroom.Decision.DpEdtUdtFair.Threat
import Cleanroom.Decision.DpFairnessReloc.RelocateThms

/-!
# FR-14: "Newcomblike" in three senses, and the verdict table (T10)

Definitions of record, parametric in a device `Dev : Proc → Tree → Prop`:

* `N1 Dev B` (value divergence): some `Dev`-consistent procedure is not optimal;
* `N2 Dev B` (set divergence): the `Dev`-consistent set is not the optimal set;
* `N3 Dev B` (updateful/updateless divergence — **reading chosen here, ATTRIBUTION-UNVETTED**):
  some `Dev`-consistent `C` whose lift `lift (queried B) C` is not a best policy at the relocated
  root `relocRoot (queried B) B` (the top repair). The source leaves N3 under-specified ("the
  node-level verdict differs from the policy-level (relocated-root) verdict on corresponding
  problems"); the relocated-root "verdict" is read as optimality of the lifted policy among lifted
  policies, which by `AlmostFair.value_reloc` is the input tree's optimality.

Verdict table with `Dev := EventTrembleEdtConsistent obs actEv`, on `𝔉`: `¬ N1`
(`fairClass_not_N1`, Theorem 3); `N2` holds on `fr12` (`fr12_N2`: "survives only as refinement",
`{D2} ⊊ {optimal}`); `¬ N3` (`fairClass_not_N3`). With `Dev :=` strict-OC EDT or masked EDT: `N1`
holds on `threat ∈ 𝔉` (`threat_N1_strict`, `threat_N1_masked`). On the almost-fair class `N1` holds
for D2 (`twoStag_N1_eventTremble`, Proposition ID-R).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

section defs

variable (Dev : Proc ι acts K → Tree Ω ι acts K → Prop) (B : Tree Ω ι acts K)

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- **N1, value divergence**: some `Dev`-consistent procedure fails optimality.
Source: `fair-repair.md` FR-14 ("(N1) *value divergence*: some EDT-consistent (in the stated
sense) procedure fails `V`-optimality")
Kind: D
Fidelity: exact -/
def N1 : Prop := ∃ C, Dev C B ∧ ¬ IsOptimal C B

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- **N2, set divergence**: the `Dev`-consistent set is not the optimal set.
Source: `fair-repair.md` FR-14 ("(N2) *set divergence*: the EDT-consistent set ≠ the optimal set")
Kind: D
Fidelity: exact -/
def N2 : Prop := ¬ ∀ C, Dev C B ↔ IsOptimal C B

omit [Fintype Ω] [DecidableEq Ω] in
/-- **N3, updateful/updateless divergence (reading chosen here; ATTRIBUTION-UNVETTED)**: some
`Dev`-consistent `C` whose lift is not a best policy at the relocated root of the top repair
(`relocRoot (queried B) B`, `dp-fairness-reloc`), among lifted policies.
Source: `fair-repair.md` FR-14 ("(N3) *updateful/updateless divergence*: the node-level verdict
differs from the policy-level (relocated-root) verdict on corresponding problems") — the source
does not fix the policy-level verdict; this file reads it as optimality of the lifted policy
Kind: D
Fidelity: variant: one reading of an under-specified clause (the docstring names it) -/
def N3 : Prop :=
  ∃ C, Dev C B ∧ ¬ ∀ C' : Proc ι acts K,
    value (lift (queried B) C') (relocRoot (queried B) B) ≤
      value (lift (queried B) C) (relocRoot (queried B) B)

end defs

section verdicts

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- **FR-14, N1 fails on `𝔉` for D2**: every event-tremble-EDT-consistent procedure is optimal
(Theorem 3).
Source: `fair-repair.md` FR-14 ("N1 fails (FR-11)"); A36 (ii)
Kind: C
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem fairClass_not_N1 [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) : ¬ N1 (EventTrembleEdtConsistent obs actEv) B :=
  fun ⟨_, hD2, hnot⟩ => hnot (eventTrembleEdt_isOptimal_of_fairClass h hD2)

/-- **`N3` collapses to `N1` on almost-fair trees** under the reading of record: relocation
preserves values (`AlmostFair.value_reloc`), so "the lift of `C` is not a best lifted policy at the
relocated root" is "`C` is not optimal", and `fairClass_not_N3` is `fairClass_not_N1` after two
rewrites. FR-14's third sense is therefore not tested by this package beyond its first; a reading
with its own content would calibrate the relocated root and evaluate `T_EDT` there
(`dp-fairness-reloc`'s `AlmostFair.topRepair_best_act`), which is not formalised.
Source: `fair-repair.md` FR-14 (N3), FR-6; audit round 1 (N1/NB5)
Kind: L
Fidelity: n/a -/
theorem almostFair_N3_iff_N1 [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K} (hAF : AlmostFair B)
    (Dev : Proc ι acts K → Tree Ω ι acts K → Prop) : N3 Dev B ↔ N1 Dev B := by
  unfold N3 N1 IsOptimal
  simp only [AlmostFair.value_reloc hAF]

/-- **FR-14, N3 fails on `𝔉` for D2**: a D2-consistent `C` is optimal, and relocation preserves
values on almost-fair trees (`AlmostFair.value_reloc`), so its lift is a best lifted policy at the
relocated root.
Source: `fair-repair.md` FR-14 ("N3 fails — the relocated form of a fair tree is `∼`-trivial");
`fair-repair.md` FR-6
Kind: C
Fidelity: exact (in the N3 reading of record)
Hyps: (a) `FairClass` -/
theorem fairClass_not_N3 [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) : ¬ N3 (EventTrembleEdtConsistent obs actEv) B := by
  rintro ⟨C, hD2, hnot⟩
  apply hnot
  intro C'
  have hAF := StronglyFair.almostFair B h.stronglyFair
  rw [AlmostFair.value_reloc hAF, AlmostFair.value_reloc hAF]
  exact eventTrembleEdt_isOptimal_of_fairClass h hD2 C'

/-- **FR-14, N2 survives as refinement**: on `fr12 ∈ 𝔉` the D2-consistent set is a proper subset
of the optimal set (`(out, y)` is optimal and D2-rejected), so `N2` holds; together with
`fairClass_not_N1`, D2 is more selective than optimality, never worse.
Source: `fair-repair.md` FR-14 ("N2 survives only as refinement (FR-12)"); A36 (i)(ii)
Kind: N+
Fidelity: exact -/
theorem fr12_N2 : N2 (EventTrembleEdtConsistent twoObs twoActEv) fr12 := by
  intro hall
  obtain ⟨-, hopt, hnot, -⟩ := fr12_outY_isOptimal_not_eventTremble
  exact hnot ((hall outY).mpr hopt)

/-- The verdict table on `𝔉` for D2, assembled: `¬ N1`, `N2` (on `fr12`), `¬ N3`.
Source: `fair-repair.md` FR-14; A36 (ii)(vi)
Kind: C -/
theorem fr14_table :
    (∀ (B : Tree Ω ι acts K) [∀ d, Nonempty (acts d)], FairClass obs actEv B →
      ¬ N1 (EventTrembleEdtConsistent obs actEv) B ∧ ¬ N3 (EventTrembleEdtConsistent obs actEv) B) ∧
    N2 (EventTrembleEdtConsistent twoObs twoActEv) fr12 :=
  ⟨fun B _ h => ⟨fairClass_not_N1 h, fairClass_not_N3 h⟩, fr12_N2⟩

/-- **N1 holds on `𝔉` for strict-OC EDT**: on `threat`, `(a, y)` is strict-OC-EDT-consistent (with
a stipulated state at the null observation) and not optimal.
Source: `fair-repair.md` FR-14 ("With EDT taken strictly (untrembled) instead, N1 holds even on
fair trees"); `identity.md` ID-23 rider (a′)
Kind: N+ -/
theorem threat_N1_strict :
    FairClass twoObs twoActEv threat ∧
    N1 (fun C B => ∃ s : Pt2 → State TwoW ℚ, StrictOC s twoObs C B ∧ TEdt s twoActEv C B) threat := by
  obtain ⟨hF, -, -, -, -, hs, -, -, hnot, -⟩ := threat_outY_untrembled
  exact ⟨hF, outY, hs, hnot⟩

/-- **N1 holds on `𝔉` for masked EDT** (LF, vacuity reading), on `threat`.
Source: `identity.md` ID-22 (M0); A36 (iii)
Kind: N+ -/
theorem threat_N1_masked :
    N1 (fun C B => ∃ s : Pt2 → State TwoW ℚ, MaskedOC s twoObs C B ∧ TEdt s twoActEv C B) threat := by
  obtain ⟨-, -, -, -, -, -, hs, -, hnot, -⟩ := threat_outY_untrembled
  exact ⟨outY, hs, hnot⟩

/-- **Proposition ID-R: N1 holds on the almost-fair class even for D2** — the Stag Hunt's `(H, H)`.
Source: `identity.md` ID-23 (Proposition ID-R: "ID-R HOLDS (the Stag Hunt)")
Kind: N+ -/
theorem twoStag_N1_eventTremble :
    AlmostFair twoStag ∧ ¬ StronglyFair twoStag ∧
    N1 (EventTrembleEdtConsistent stagObs stagActEv) twoStag := by
  obtain ⟨hAF, -, -, -, hnsf, hD2, hnot, -⟩ := twoStag_HH_eventTremble_not_optimal
  exact ⟨hAF, hnsf, profHH, hD2, hnot⟩

end verdicts

end Cleanroom.Decision.DpEdtUdtFair
