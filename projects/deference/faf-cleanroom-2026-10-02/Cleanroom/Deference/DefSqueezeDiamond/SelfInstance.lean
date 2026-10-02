import Cleanroom.Deference.DefSqueezeDiamond.GapMesh
import Cleanroom.Deference.DefSqueezeDiamond.ProbeFollower
import Cleanroom.Deference.DefSqueezeDiamond.Diamond
import Cleanroom.Deference.DefSqueezeDiamond.PaperArrows
import Cleanroom.Deference.DefSqueezeDiamond.Fragment

/-!
# `def-squeeze-diamond` · SelfInstance: the diamond's hypothesis package inhabited (repair
round 1: audit r1 fidelity B1 / adversarial B2)

Round 1 found that `diamond` (load-bearing 5) had no inhabitant of its full hypothesis package:
`PinnedGapPackages` was inhabited per literal-indicator source only, `PinnedProbeMenus` nowhere.
With `GapMesh` (the gap quotes of every e.c. valued source, both signs) and `ProbeFollower`
(the probe follower of every e.c. valued gap bet), both clauses are theorems for the self-expert
over the paper's inductor:

* `pinnedGapPackages_self : PinnedGapPackages (paperDP T) (Expert.self …)` — gap quotes
  `gapQuote_meshPlus/Minus` (with the given `Y` substituted into the `reflects` field), pins
  `selfPinGap`, ramp quotes `paperExpert_rampQuotesAvailable`;
* `pinnedProbeMenus_self : PinnedProbeMenus (paperDP T) (Expert.self …)` — the same gap quotes
  and pins, followers `probeData_self` at every margin;
* `diamond_self_instance` — **`diamond` applied with every clause discharged** for the
  self-expert: the five-clause conjunction as an instance of the composition, every hypothesis
  (a). This is the witness load-bearing 5 asked for ("instantiated for the self-expert, (a)
  throughout"); `diamond_self` (the `T`-shaped consistency check whose first three clauses
  discard their antecedent) remains as what the mandate's 5b named.
* `squeeze_self` — the squeeze with every input a theorem on **every** e.c. valued source
  (the general form of `squeeze_self_indicator`); `towerValued_self_via_pinned`,
  `towerValued_self_via_fragment` — `towerValued_of_totalTrust_pinned` and
  `towerValued_of_gapFragment` run on the self-expert with their clause discharged.
* `pinnedGapPackagesBase_paperExpert : PinnedGapPackagesBase T DPH (paperExpert T f DPH)` for
  **any** extending novice `DPH` — the mesh gap quotes are reflected in `paperDP T`-worlds,
  hence in `DPH`-worlds, and the pins are the expert's own (`ExpertPin` mentions only `E.A`,
  `E.f`, definitionally the self-expert's). Hence `towerValuedBase_of_totalTrustBase'`: Total
  Trust ⟹ Tower for a distinct novice with **one** hypothesis left (the deference predicate),
  closing load-bearing 3's arrow out of Total Trust; and the mandate's literal
  `towerValuedBase_of_totalTrust`.

Theorem file (imports the construction files). Single market (self) / one-way.
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows Cleanroom.Deference.DefLatticeArrows.Witness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-! ## The pinned packages for the self-expert -/

/-- **The pinned gap packages hold for the self-expert on every e.c. valued source** (a): for
every e.c. valued `Z` with e.c. quote `Y`, both mesh gap quotes exist (`gapQuote_meshPlus`,
`gapQuote_meshMinus`, their `reflects` field restated for the given `Y`), are pinned at `½` by
`selfPinGap`, and have ramp quotes by `paperRampQuote`.
Source: mandate target 4b (the pinned forms, design decision 4); target 5a (the clause `hgap`)
Kind: C
Fidelity: exact (the general e.c. class; gaps within `1/(n+1)`)
Hyps: (a); `hf` -/
theorem pinnedGapPackages_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    PinnedGapPackages (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) := by
  intro Z Y hZ hY hZv hR
  let qP0 := gapQuote_meshPlus T f hZ hZv
  let qM0 := gapQuote_meshMinus T f hZ hZv
  let qP : GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) Z Y 1
      (meshGapPlus T f hZ) :=
    { codes := qP0.codes, slack := qP0.slack, slack_tendsto := qP0.slack_tendsto,
      source_valued := qP0.source_valued, reflects := hR, gap_reflected := qP0.gap_reflected }
  let qM : GapQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) Z Y (-1)
      (meshGapMinus T f hZ) :=
    { codes := qM0.codes, slack := qM0.slack, slack_tendsto := qM0.slack_tendsto,
      source_valued := qM0.source_valued, reflects := hR, gap_reflected := qM0.gap_reflected }
  exact ⟨_, _, qP, qM, selfPinGap T f hf (Or.inl rfl) hZ qP, selfPinGap T f hf (Or.inr rfl) hZ qM,
    paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective qP.codes qP.gap_valued,
    paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective qM.codes qM.gap_valued⟩

/-- **The pinned probe menus hold for the self-expert on every e.c. valued source** (a): the
mesh gap quotes, pinned by `selfPinGap`, with the probe follower `probeData_self` at every
margin.
Source: mandate target 4b (the probe package); target 5a (the clause `hprobe`)
Kind: C
Fidelity: exact (the general e.c. class)
Hyps: (a); `hf` -/
theorem pinnedProbeMenus_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    PinnedProbeMenus (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) := by
  intro Z Y hZ hY hZv hR
  obtain ⟨G, G', qP, qM, pinP, pinM, -, -⟩ := pinnedGapPackages_self T f hf Z Y hZ hY hZv hR
  exact ⟨G, G', qP, qM, pinP, pinM, fun ε hε hε1 =>
    ⟨⟨_, ⟨probeData_self T f hε hε1 qP.codes qP.gap_valued⟩⟩,
      ⟨_, ⟨probeData_self T f hε hε1 qM.codes qM.gap_valued⟩⟩⟩⟩

/-! ## The diamond, instantiated with every clause discharged -/

/-- **The diamond for the self-expert as an instance of the composition** (load-bearing 5's
witness): `diamond` applied to the self-expert over the paper's inductor with every hypothesis
a theorem — `pinnedGapPackages_self`, `pinnedProbeMenus_self`, `selfPinK`, the product and
conditional quotes (`paperExpert_productQuotesAvailable`, `paperExpert_condQuotesReflected`),
the folds (`selfFoldsAt_ramps`, `selfFoldsCondOver`), the quotes (`quotesAvailable_self`),
`paperDP_hworld`. The conjunction is the same as `diamond_self`'s; the difference is that
here every clause of the composition is *discharged* rather than the vertices being proved
directly (design decision 1: the self-expert's vertices are theorems, so this is the
composition's non-vacuity, not a new vertex).
Source: mandate target 5b ("`diamond_self` … every clause (a)"); load-bearing 5
Kind: N+ (the full hypothesis package of `diamond` inhabited; the composition run)
Fidelity: exact (`diamond`'s conclusion at the self-expert)
Hyps: (a) none; `hf` -/
theorem diamond_self_instance (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    (TotalTrust (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) ↔
      TowerValued (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) ∧
    (TowerValued (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) ↔
      CondTower (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) ∧
    (Value (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) →
      TowerValued (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) ∧
    (TowerValued (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) →
      SelfEndorsesGE (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) →
      Value (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f)) ∧
    (TotalTrust (liaHistory (paperDP T)) (paperDP T)
        (Expert.self (liaHistory (paperDP T)) (paperDP T) f) →
      ∀ (s δ : ℚ) (X W XW : ℕ → LUV), 0 < δ → LUV.MachineThresholdCodeSeq X →
      WeightQuote (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) X
        (rampAbove δ s) W XW →
      (fun n => (twoOptionComb s XW W n).expect (liaHistory (paperDP T)) n) ≳ₙ
        (fun _ => (s : ℝ))) :=
  diamond (Expert.self (liaHistory (paperDP T)) (paperDP T) f)
    (pinnedGapPackages_self T f hf) (pinnedProbeMenus_self T f hf) (selfPinK T f)
    (fun _ _ _ => ⟨paperExpert_productQuotesAvailable T f (extendsBase_self T) _,
      paperExpert_productQuotesAvailable T f (extendsBase_self T) _⟩)
    (selfFoldsAt_ramps T f hf) (paperExpert_condQuotesReflected T f (extendsBase_self T))
    (selfFoldsCondOver T f hf) (quotesAvailable_self T f) (paperDP_hworld T)

/-- **The squeeze runs with every input a theorem on every e.c. valued source** — the general
form of `squeeze_self_indicator`: for an e.c. valued `Z` and an e.c. quote `Y` of the
self-expert's deferred estimate, `E_n(Z_n) ≈ₙ E_n(Y_n)` through
`tower_instance_of_totalTrust_gapBets` with the mesh gap quotes, the pins `selfPinGap`, the ramp
packages `paperRampQuote` and the TT instances `selfTotalTrust`. (The conclusion is also
`towerValued_self` directly; this is the squeeze *run*, design decision 1.)
Source: mandate target 2e; [[centered-bet-squeeze]] §2; root-deference-007 Steps 0–3
Kind: C (self run; conclusion independently a theorem)
Fidelity: exact (rescaled; the general e.c. class)
Hyps: (a) none; `hf` -/
theorem squeeze_self (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f)
    {Z Y : ℕ → LUV} (hZ : LUV.MachineThresholdCodeSeq Z) (hY : LUV.MachineThresholdCodeSeq Y)
    (hZv : Valued (paperDP T) Z)
    (hR : Reflects (paperDP T) (Expert.self (liaHistory (paperDP T)) (paperDP T) f) Z Y) :
    (fun n => (Z n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (Y n).expect (liaHistory (paperDP T)) n) := by
  obtain ⟨G, G', qP, qM, -, -, -, -⟩ := pinnedGapPackages_self T f hf Z Y hZ hY hZv hR
  exact squeeze_self_of_gapQuotes T f hf hZ hY qP qM

/-- `towerValued_of_totalTrust_pinned` run on the self-expert with its clause discharged (the
conclusion is also `towerValued_self`; this witnesses the `L` row's full package).
Source: mandate target 5a
Kind: N+ (the full package of `towerValued_of_totalTrust_pinned` inhabited)
Fidelity: exact
Hyps: (a) none; `hf` -/
theorem towerValued_self_via_pinned (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    TowerValued (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  towerValued_of_totalTrust_pinned (selfTotalTrust T f hf.injective)
    (pinnedGapPackages_self T f hf) (paperDP_hworld T)

/-- `towerValued_of_gapFragment` run on the self-expert with its clause discharged: the
fragment of Total Trust (`gapFragment_of_totalTrust` of `selfTotalTrust`) and the pinned gap
packages give Tower.
Source: mandate target 3a
Kind: N+ (the full package of `towerValued_of_gapFragment` inhabited)
Fidelity: exact
Hyps: (a) none; `hf` -/
theorem towerValued_self_via_fragment (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) :
    TowerValued (liaHistory (paperDP T)) (paperDP T)
      (Expert.self (liaHistory (paperDP T)) (paperDP T) f) :=
  towerValued_of_gapFragment (gapFragment_of_totalTrust (selfTotalTrust T f hf.injective))
    (pinnedGapPackages_self T f hf) (paperDP_hworld T)

/-! ## The paper expert read by a distinct novice: the gap clause discharged -/

section Novice

variable {DPH : DeductiveProcess}

/-- **The pinned gap packages on base-valued sources hold for the paper expert over any
extending novice** (a): the mesh gap quotes are reflected in every `paperDP T`-world, hence in
every `DPH`-world (`hext`); the pins are the self-expert's (`ExpertPin` mentions only `E.A`,
`E.f`); the gap LUVs are base-valued (`GapQuote.gap_valued` of the `paperDP T` quote).
Source: mandate target 4b (the gap package for the paper expert); design decision 4
Kind: C
Fidelity: exact (base-valued sources; gaps within `1/(n+1)`)
Hyps: (a); `hext`, `hf` -/
theorem pinnedGapPackagesBase_paperExpert (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) (hext : ExtendsBase T DPH) :
    PinnedGapPackagesBase T DPH (paperExpert T f DPH) := by
  intro Z Y hZ hY hZv hR
  let qP0 := gapQuote_meshPlus T f hZ hZv
  let qM0 := gapQuote_meshMinus T f hZ hZv
  let qP : GapQuote DPH (paperExpert T f DPH) Z Y 1 (meshGapPlus T f hZ) :=
    { codes := qP0.codes, slack := qP0.slack, slack_tendsto := qP0.slack_tendsto,
      source_valued := fun n v hv => hZv n v (hext v hv), reflects := hR,
      gap_reflected := fun n v hv z hz => qP0.gap_reflected n v (hext v hv) z hz }
  let qM : GapQuote DPH (paperExpert T f DPH) Z Y (-1) (meshGapMinus T f hZ) :=
    { codes := qM0.codes, slack := qM0.slack, slack_tendsto := qM0.slack_tendsto,
      source_valued := fun n v hv => hZv n v (hext v hv), reflects := hR,
      gap_reflected := fun n v hv z hz => qM0.gap_reflected n v (hext v hv) z hz }
  exact ⟨_, _, qP, qM, selfPinGap T f hf (Or.inl rfl) hZ qP0, selfPinGap T f hf (Or.inr rfl) hZ qM0,
    qP0.gap_valued, qM0.gap_valued⟩

variable {P : History} [IsLogicalInductor P DPH]

/-- **Total Trust ⟹ Tower for a distinct novice, with one hypothesis left** (load-bearing 3's
arrow out of Total Trust): `towerValuedBase_of_totalTrustBase` with its gap clause discharged by
`pinnedGapPackagesBase_paperExpert`. Every hypothesis (a) except `hT`.
Source: mandate target 4c (`towerValuedBase_of_totalTrust`); [[centered-bet-squeeze]] §2
Kind: C
Fidelity: weaker: sources valued over the expert's process (finding F3); rescaled
Hyps: (a) except `hT` (the deference hypothesis); `hext`, `hf`, `hworld` -/
theorem towerValuedBase_of_totalTrustBase' (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) (hext : ExtendsBase T DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hT : TotalTrustBase T P DPH (paperExpert T f DPH)) :
    TowerValuedBase T P DPH (paperExpert T f DPH) :=
  towerValuedBase_of_totalTrustBase T f hf hext hworld (pinnedGapPackagesBase_paperExpert T f hf hext)
    hT

/-- **The mandate's literal arrow** `towerValuedBase_of_totalTrust`: from the unrestricted
`TotalTrust P DPH E` (which implies `TotalTrustBase`) to Tower on base-valued sources, one
hypothesis left.
Source: mandate target 4c (as stated); finding M3
Kind: L
Fidelity: weaker: conclusion on base-valued sources (F3)
Hyps: (a) except `hT`; `hext`, `hf`, `hworld` -/
theorem towerValuedBase_of_totalTrust (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) (hext : ExtendsBase T DPH)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hT : TotalTrust P DPH (paperExpert T f DPH)) :
    TowerValuedBase T P DPH (paperExpert T f DPH) :=
  towerValuedBase_of_totalTrustBase' T f hf hext hworld (totalTrustBase_of_totalTrust T hT)

end Novice

/-- The diamond's self-instance over `𝗣𝗔` at `succDeferral`, and the one-hypothesis arrow for
the ledger novice: no binder left unwitnessed (design decision 7).
Source: mandate design decision 7
Kind: L
Fidelity: n/a -/
example : PinnedGapPackages (paperDP 𝗣𝗔)
      (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) ∧
    PinnedProbeMenus (paperDP 𝗣𝗔)
      (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) :=
  ⟨pinnedGapPackages_self 𝗣𝗔 succDeferral succDeferral_strict,
    pinnedProbeMenus_self 𝗣𝗔 succDeferral succDeferral_strict⟩

example (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (ledgerProcess (paperDP 𝗣𝗔) a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess (paperDP 𝗣𝗔) a e).D n))
    (hT : TotalTrustBase 𝗣𝗔 P (ledgerProcess (paperDP 𝗣𝗔) a e)
      (paperExpert 𝗣𝗔 succDeferral (ledgerProcess (paperDP 𝗣𝗔) a e))) :
    TowerValuedBase 𝗣𝗔 P (ledgerProcess (paperDP 𝗣𝗔) a e)
      (paperExpert 𝗣𝗔 succDeferral (ledgerProcess (paperDP 𝗣𝗔) a e)) :=
  towerValuedBase_of_totalTrustBase' 𝗣𝗔 succDeferral succDeferral_strict
    (extendsBase_ledger 𝗣𝗔 a e) hworld hT

end

end Cleanroom.Deference.DefSqueezeDiamond
