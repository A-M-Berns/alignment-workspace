import Cleanroom.Decision.DpEdtUdtFair.FairClass
import Cleanroom.Decision.DpCalibration.Corollaries
import Cleanroom.Decision.DpCalibration.Chain

/-!
# Recording and mixed labels on `𝔉` (T11): compositions of `dp-calibration`'s CA-12′ rows

On `𝔉` every queried point records for every procedure and realizes its observation, so
`dp-calibration`'s CA-12′ consequences apply at every queried point under every full-support
procedure with no further hypothesis:

* `FairClass.V_actEv_eq` — the strict act values at `d` are `C(d)`-independent
  (`V_actEv_eq_of_recordsForAll`);
* `FairClass.hd` — `H_d` (coverage and a.s. subtree-veridicality at every `d`-node) holds at every
  queried point for **every** procedure, so `FairClass.zo2_chain` instantiates `dp-calibration`'s
  ZO-2 chain on `𝔉` with no further hypothesis (the coincidence theorem of T2(a));
* the remaining clauses of T11 are cited, not restated: every deterministic `C` with `ν_C(O_d) > 0`
  is strictly-calibrated-and-approved at `d` (`tEdtAt_of_deterministic_recorded`); a properly
  mixed strictly-calibrated-and-approved label exists iff two supported actions tie
  (`tie_of_mixed_approved`) and is never forced (`tEdtAt_of_support_subset_of_recordsForAll`,
  the per-point form; the `𝔉`-level deterministic-selection corollary is **not shipped**, see
  the report); the relocated output records at `d̂` (`dp-fairness-reloc`'s `recordsForAll_root`).
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
variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- **CA-12′ on `𝔉`**: the strict act values at a queried `d` are `C(d)`-independent — for
full-support `C`, `C'` agreeing off `d`, strict states `s`, `s'`, and an act `a` in both `A_d^+`,
`V_{s_d}(a) = V_{s'_d}(a)`. The positivities `ν(O_d) > 0` are derived from `𝔉`.
Source: `calibration.md` CA-12′ ("the act values at `d` are `C(d)`-independent"); mandate T11(a)
Kind: C
Fidelity: exact
Hyps: (a) `FairClass`, (a) full support, (a) agreement off `d`, (a) strict OC at `d` -/
theorem FairClass.V_actEv_eq [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {d : ι} (hd : d ∈ queried B) {C C' : Proc ι acts K}
    (hoff : ∀ d', d' ≠ d → C d' = C' d') (hC : C.FullSupport) (hC' : C'.FullSupport)
    {s s' : ι → State Ω K} (hs : StrictOCAt s obs C B d) (hs' : StrictOCAt s' obs C' B d)
    (a : acts d) (ha : a ∈ APlus s actEv d) (ha' : a ∈ APlus s' actEv d) :
    (s d).V (actEv d a) = (s' d).V (actEv d a) :=
  V_actEv_eq_of_recordsForAll obs actEv B (h.frec d hd) hoff
    (nu_obs_pos h.pruned (h.realized d hd) hC) (nu_obs_pos h.pruned (h.realized d hd) hC') hs hs'
    a ha ha'

/-- **`H_d` for every procedure on `𝔉`**: at every queried `d`, coverage (every positive `O_d`-run
meets a `d`-node — recording's count clause) and a.s. subtree-veridicality of every `d`-node
(`FairClass.subtreeVeridical`, which holds for every leaf).
Source: `zoo.md` ZO-2 ("`H_d` holds for every procedure on fair trees"); v2 Proposition 3
Kind: C
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.hd [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K) :
    ∀ d ∈ queried B, Covers obs C B d ∧ ∀ q, pt B q = d → SubtreeVeridicalAS obs C B q := by
  intro d hd
  refine ⟨fun ℓ hpos hobs => ?_, fun q hq ℓ hℓ _ => h.subtreeVeridical hd q hq ℓ hℓ⟩
  have := (h.frec d hd C ℓ hpos hobs).1
  omega

/-- **ZO-2's chain on `𝔉`** (the coincidence theorem of T2(a)): for every procedure and state
assignment, `LimitOC → StrictOC`, `StrictOC ↔ PerRunSSC`, `PerRunSSC ↔ PerOccSSC` — the
hypotheses `H_d` and almost-fairness of `dp-calibration`'s `zo2_chain` are derived from `𝔉`.
Source: `zoo.md` ZO-2; mandate T2(a) ("`zo2_chain` applies with no extra hypothesis on `𝔉`")
Kind: C
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.zo2_chain [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K) (s : ι → State Ω K) :
    (LimitOC s obs C B → StrictOC s obs C B) ∧
    (StrictOC s obs C B ↔ PerRunSSC s C B) ∧
    (PerRunSSC s C B ↔ PerOccSSC s C B) :=
  DpCalibration.zo2_chain C B obs s (h.hd C) (StronglyFair.almostFair B h.stronglyFair)

end Cleanroom.Decision.DpEdtUdtFair
