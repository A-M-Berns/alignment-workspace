import Cleanroom.Deference.DefSqueezeDiamond.PaperExpert
import Cleanroom.Deference.DefSelfTrust.Transfer

/-!
# `def-squeeze-diamond` · PaperArrows: the arrows for a distinct novice, with one hypothesis left
(target 4c)

For the paper expert `paperExpert T f DPH` read by a novice `P` over an extending process
`DPH` (`ExtendsBase T DPH`), the Tower and Total-Trust vertices of record are the
**base-restricted** predicates (design decision 4): `TowerValuedBase` (Tower on e.c. sources
valued over the *expert's* process `paperDP T`) and `TotalTrustBase` (both soft faces on such
sources). The restriction is forced, not chosen: FAF's product quote `estXW` of a source `X` is
reflected only in worlds where `X` is valued, and the expert's fold `E*(XW_n) ≈ₙ wt·E*(X_n)` is
provability induction over the *expert's* process, which needs the world bound in every
`paperDP T`-world — a source valued only over `DPH` has no such bound (finding F3: the
unrestricted `TotalTrust P DPH E` quantifies over bets the expert's theory does not value, so
the arrows close only class-relatively; this is the mandate's "the honest object is
class-relative").

**Tower ⟹ Total Trust, with one hypothesis** (`totalTrustBase_of_towerValuedBase`): for an
arbitrary `DPH`-`WeightQuote` `(W, XW)` of a base-valued source, both quotes are transported to
FAF's own `estW`/`estXW` by the T0 transfer (`expect_asympEq_of_reflected_within/_exact` over
`(P, DPH)`: both pairs are valued at the same numbers in `DPH`-worlds), the soft-TT instance at
FAF's quotes is `softAbove_instance` with the Tower instance at `estXW` (base-valued) and the
fold — a theorem (`selfFoldsAt_rampAbove`: the fold is a statement about the expert's prices
alone, the same proposition for `paperExpert` and `Expert.self`) — and the inequality comes
back along the transfer. Every hypothesis is (a) except `hT`, the deference predicate.

**Total Trust ⟹ Tower** (`towerValuedBase_of_totalTrustBase`) takes the pinned gap packages
as a disclosed clause `PinnedGapPackagesBase` (the gap LUV is not built in this package; the
pins on FAF-built gap LUVs would be `selfPinGap`'s). One-way throughout.
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-! ## The base-restricted vertices -/

/-- **Tower on sources valued over the expert's process**: `E^H_n(X_n) ≈ₙ E^H_n(Y_n)` for every
e.c. `X` valued in every `paperDP T`-world and every e.c. `Y` reflecting `E*(X)` over `DPH`.
Source: mandate design decision 4 (`TowerValuedBase`)
Kind: D
Fidelity: weaker: sources valued over the expert's process -/
def TowerValuedBase (P : History) (DPH : DeductiveProcess) (E : Expert DPH) : Prop :=
  ∀ X Y : ℕ → LUV, LUV.MachineThresholdCodeSeq X → LUV.MachineThresholdCodeSeq Y →
    Valued (paperDP T) X → Reflects DPH E X Y →
      (fun n => (X n).expect P n) ≈ₙ (fun n => (Y n).expect P n)

/-- The above-threshold inequality on sources valued over the expert's process.
Source: mandate target 4d ("`ThresholdIneqAboveOn` over the class of `paperDP T`-valued sources")
Kind: D
Fidelity: weaker: sources valued over the expert's process -/
def ThresholdIneqAboveBase (P : History) (DPH : DeductiveProcess) (E : Expert DPH) (wt : ℝ → ℝ)
    (s : ℚ) : Prop :=
  ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X → Valued (paperDP T) X →
    WeightQuote DPH E X wt W XW →
      (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≳ₙ (fun _ => (0 : ℝ))

/-- The below-threshold inequality on sources valued over the expert's process.
Source: mandate target 4d
Kind: D
Fidelity: weaker: sources valued over the expert's process -/
def ThresholdIneqBelowBase (P : History) (DPH : DeductiveProcess) (E : Expert DPH) (wt : ℝ → ℝ)
    (s : ℚ) : Prop :=
  ∀ X W XW : ℕ → LUV, LUV.MachineThresholdCodeSeq X → Valued (paperDP T) X →
    WeightQuote DPH E X wt W XW →
      (fun n => (XW n).expect P n - (s : ℝ) * (W n).expect P n) ≲ₙ (fun _ => (0 : ℝ))

/-- **Total Trust on sources valued over the expert's process**: both soft faces at every
rational threshold and positive width, restricted to base-valued sources.
Source: mandate target 4d (the class-relative honest object); [[deference-notions]] §Total Trust
Kind: D
Fidelity: weaker: sources valued over the expert's process -/
def TotalTrustBase (P : History) (DPH : DeductiveProcess) (E : Expert DPH) : Prop :=
  ∀ s δ : ℚ, 0 < δ → ThresholdIneqAboveBase T P DPH E (rampAbove δ s) s ∧
    ThresholdIneqBelowBase T P DPH E (rampBelow δ s) s

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- `TowerValued` implies its base restriction over an extending process.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem towerValuedBase_of_towerValued {P : History} {DPH : DeductiveProcess} {E : Expert DPH}
    (hext : ExtendsBase T DPH) (hT : TowerValued P DPH E) : TowerValuedBase T P DPH E :=
  fun X Y hX hY hv hR => hT X Y hX hY (fun n v hv' => hv n v (hext v hv')) hR

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- `TotalTrust` implies its base restriction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem totalTrustBase_of_totalTrust {P : History} {DPH : DeductiveProcess} {E : Expert DPH}
    (hT : TotalTrust P DPH E) : TotalTrustBase T P DPH E :=
  fun s δ hδ => ⟨fun X W XW hX _ q => (hT s δ hδ).1 X W XW hX q,
    fun X W XW hX _ q => (hT s δ hδ).2 X W XW hX q⟩

omit [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] in
/-- Over the expert's own process the base restriction is the predicate itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem towerValuedBase_paperDP_iff {P : History} {E : Expert (paperDP T)} :
    TowerValuedBase T P (paperDP T) E ↔ TowerValued P (paperDP T) E := Iff.rfl

/-! ## 4c — Tower ⟹ Total Trust for a distinct novice, one hypothesis left -/

section Arrows

variable {P : History} {DPH : DeductiveProcess} [IsLogicalInductor P DPH]
  (f : DeferralFunction)

/-- FAF's above-ramp product of a base-valued source is base-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem estXW_valued (hf : StrictlyIncreasingDeferral f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X)
    (hXv : Valued (paperDP T) X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) :
    Valued (paperDP T) (estXW T f hX hδ s) := by
  intro n v hv
  obtain ⟨x, hx⟩ := hXv n v hv
  obtain ⟨z, hz, -⟩ := estXW_reflected T f hf.injective hX hδ s n v hv hx
  exact ⟨z, hz⟩

/-- FAF's below-ramp product of a base-valued source is base-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem estXWBelow_valued (hf : StrictlyIncreasingDeferral f) {X : ℕ → LUV}
    (hX : LUV.MachineThresholdCodeSeq X)
    (hXv : Valued (paperDP T) X) {δ : ℚ} (hδ : 0 < δ) (s : ℚ) :
    Valued (paperDP T) (estXWBelow T f hX hδ s) := by
  intro n v hv
  obtain ⟨x, hx⟩ := hXv n v hv
  obtain ⟨z, hz, -⟩ := estXWBelow_reflected T f hf.injective hX hδ s n v hv hx
  exact ⟨z, hz⟩

/-- **The above face of Total Trust for a distinct novice, from the base Tower** (the arrow,
per threshold and width): any `DPH`-ramp quote of a base-valued source is transported to FAF's
quote, where the soft-TT instance follows from the Tower instance and the expert's fold.
Source: mandate target 4c (`totalTrust_of_towerValuedBase`); [[tower-implies-total-trust]]
Kind: C
Fidelity: weaker: sources valued over the expert's process
Hyps: (a) except `hT` (the deference predicate); `hext`, `hf`, `hworld` -/
theorem thresholdIneqAboveBase_of_towerValuedBase (hf : StrictlyIncreasingDeferral f)
    (hext : ExtendsBase T DPH) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hT : TowerValuedBase T P DPH (paperExpert T f DPH)) (s : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    ThresholdIneqAboveBase T P DPH (paperExpert T f DPH) (rampAbove δ s) s := by
  intro X W XW hX hXv q
  have hinj := hf.injective
  let qf := paperRampQuote T f hext hinj hX hXv hδ s
  obtain ⟨Y, hY, hYr⟩ := paperExpert_quotesAvailable T f hext _ qf.product_codes
  have hW : (fun n => (W n).expect P n) ≈ₙ (fun n => (estW T f hX hδ s n).expect P n) :=
    expect_asympEq_of_reflected_exact (P := P) (DP := DPH) q.weight_codes qf.weight_codes
      (fun n _ => rampAbove δ s ((paperExpert T f DPH).estimate X n))
      (fun n v hv => q.weight_reflected n v hv) (fun n v hv => qf.weight_reflected n v hv) hworld
  have hXW : (fun n => (XW n).expect P n) ≈ₙ (fun n => (estXW T f hX hδ s n).expect P n) :=
    expect_asympEq_of_reflected_within (P := P) (DP := DPH) q.product_codes qf.product_codes
      (fun n v => worldValue v (X n) * rampAbove δ s ((paperExpert T f DPH).estimate X n))
      q.slack_tendsto qf.slack_tendsto
      (fun n v hv => by
        obtain ⟨x, hx⟩ := q.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := q.product_reflected n v hv x hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩)
      (fun n v hv => by
        obtain ⟨x, hx⟩ := qf.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := qf.product_reflected n v hv x hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩) hworld
  have hfold : ExpertFoldAt DPH (paperExpert T f DPH) X (rampAbove δ s) (estXW T f hX hδ s) :=
    selfFoldsAt_rampAbove T f hf s hδ X _ _ hX
      (paperRampQuote T f (extendsBase_self T) hinj hX hXv hδ s)
  have hTTf := softAbove_instance (P := P) hδ qf hY hYr
    (hT _ Y qf.product_codes hY (estXW_valued T f hf hX hXv hδ s) hYr) hfold hworld
  exact asympGE_zero_of_asympEq_pair (s : ℝ) hXW hW hTTf

/-- **The below face**, likewise.
Source: mandate target 4c
Kind: C
Fidelity: weaker: sources valued over the expert's process
Hyps: (a) except `hT`; `hext`, `hf`, `hworld` -/
theorem thresholdIneqBelowBase_of_towerValuedBase (hf : StrictlyIncreasingDeferral f)
    (hext : ExtendsBase T DPH) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hT : TowerValuedBase T P DPH (paperExpert T f DPH)) (s : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    ThresholdIneqBelowBase T P DPH (paperExpert T f DPH) (rampBelow δ s) s := by
  intro X W XW hX hXv q
  have hinj := hf.injective
  let qf := paperRampQuoteBelow T f hext hinj hX hXv hδ s
  obtain ⟨Y, hY, hYr⟩ := paperExpert_quotesAvailable T f hext _ qf.product_codes
  have hW : (fun n => (W n).expect P n) ≈ₙ (fun n => (estWBelow T f hX hδ s n).expect P n) :=
    expect_asympEq_of_reflected_exact (P := P) (DP := DPH) q.weight_codes qf.weight_codes
      (fun n _ => rampBelow δ s ((paperExpert T f DPH).estimate X n))
      (fun n v hv => q.weight_reflected n v hv) (fun n v hv => qf.weight_reflected n v hv) hworld
  have hXW : (fun n => (XW n).expect P n) ≈ₙ
      (fun n => (estXWBelow T f hX hδ s n).expect P n) :=
    expect_asympEq_of_reflected_within (P := P) (DP := DPH) q.product_codes qf.product_codes
      (fun n v => worldValue v (X n) * rampBelow δ s ((paperExpert T f DPH).estimate X n))
      q.slack_tendsto qf.slack_tendsto
      (fun n v hv => by
        obtain ⟨x, hx⟩ := q.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := q.product_reflected n v hv x hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩)
      (fun n v hv => by
        obtain ⟨x, hx⟩ := qf.source_valued n v hv
        obtain ⟨z, hz, hb⟩ := qf.product_reflected n v hv x hx
        exact ⟨z, hz, by rwa [worldValue_eq hx]⟩) hworld
  have hfold : ExpertFoldAt DPH (paperExpert T f DPH) X (rampBelow δ s)
      (estXWBelow T f hX hδ s) :=
    selfFoldsAt_rampBelow T f hf s hδ X _ _ hX
      (paperRampQuoteBelow T f (extendsBase_self T) hinj hX hXv hδ s)
  have hTTf := softBelow_instance (P := P) hδ qf hY hYr
    (hT _ Y qf.product_codes hY (estXWBelow_valued T f hf hX hXv hδ s) hYr) hfold hworld
  exact asympLE_zero_of_asympEq_pair (s : ℝ) hXW hW hTTf

/-- **4c. Tower ⟹ Total Trust for a distinct novice, one hypothesis left** (load-bearing 3,
the arrow out of the tower): for the paper expert read by any inductor `P` over an extending
process `DPH`, `TowerValuedBase → TotalTrustBase` with every existence and fold clause
discharged (a). Only the antecedent remains. One-way.
Source: mandate target 4c (`totalTrust_of_towerValuedBase`); [[tower-implies-total-trust]]
§Place in the circuit
Kind: C
Fidelity: weaker: sources valued over the expert's process (finding F3)
Hyps: (a) except the deference predicate `hT`; `hext` (data), `hf`, `hworld` -/
theorem totalTrustBase_of_towerValuedBase (hf : StrictlyIncreasingDeferral f)
    (hext : ExtendsBase T DPH) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hT : TowerValuedBase T P DPH (paperExpert T f DPH)) :
    TotalTrustBase T P DPH (paperExpert T f DPH) :=
  fun s δ hδ => ⟨thresholdIneqAboveBase_of_towerValuedBase T f hf hext hworld hT s hδ,
    thresholdIneqBelowBase_of_towerValuedBase T f hf hext hworld hT s hδ⟩

/-! ## Total Trust ⟹ Tower for a distinct novice, over pinned gap packages -/

/-- **Pinned gap packages on base-valued sources** (design decision 4): for every e.c.
base-valued `Z` with e.c. quote `Y`, both gap quotes exist, are base-valued, and are pinned at
`½` by the expert. A disclosed clause: the gap LUV is not built in this package.
Source: mandate design decision 4 ("pinned packages rather than `GapPackagesAvailable ∧
`ExpertPinsGaps` separately")
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def PinnedGapPackagesBase (DPH : DeductiveProcess) (E : Expert DPH) : Prop :=
  ∀ Z Y : ℕ → LUV, LUV.MachineThresholdCodeSeq Z → LUV.MachineThresholdCodeSeq Y →
    Valued (paperDP T) Z → Reflects DPH E Z Y → ∃ G G' : ℕ → LUV,
      ∃ _qP : GapQuote DPH E Z Y 1 G, ∃ _qM : GapQuote DPH E Z Y (-1) G',
        ExpertPin E G (1 / 2) ∧ ExpertPin E G' (1 / 2) ∧
          Valued (paperDP T) G ∧ Valued (paperDP T) G'

/-- **Total Trust ⟹ Tower for a distinct novice, over pinned gap packages**: the squeeze
(`tower_instance_of_totalTrust_gapBets`) with the ramp packages on the gap LUVs from
`paperRampQuote` (a) and their TT instances from `TotalTrustBase` (the gap LUVs are
base-valued); the pins are the clause.
Source: mandate target 4c (`towerValuedBase_of_totalTrust`); [[centered-bet-squeeze]] §2
Kind: L
Fidelity: weaker: sources valued over the expert's process; rescaled
Hyps: (c) `PinnedGapPackagesBase` (the gap LUVs and their pins); `TotalTrustBase` is the
deference hypothesis; `hext`, `hf`, `hworld` -/
theorem towerValuedBase_of_totalTrustBase (hf : StrictlyIncreasingDeferral f)
    (hext : ExtendsBase T DPH) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hgap : PinnedGapPackagesBase T DPH (paperExpert T f DPH))
    (hT : TotalTrustBase T P DPH (paperExpert T f DPH)) :
    TowerValuedBase T P DPH (paperExpert T f DPH) := by
  intro Z Y hZ hY hZv hR
  obtain ⟨G, G', qP, qM, pinP, pinM, hGv, hG'v⟩ := hgap Z Y hZ hY hZv hR
  refine tower_instance_of_totalTrust_gapBets hZ hY qP qM pinP pinM
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩)
    (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩) hworld
  · have hδ : (0 : ℚ) < ε / 2 := by positivity
    exact ⟨_, _, paperRampQuote T f hext hf.injective qP.codes hGv hδ (1 / 2 - ε),
      (hT (1 / 2 - ε) (ε / 2) hδ).1 G _ _ qP.codes hGv
        (paperRampQuote T f hext hf.injective qP.codes hGv hδ (1 / 2 - ε))⟩
  · have hδ : (0 : ℚ) < ε / 2 := by positivity
    exact ⟨_, _, paperRampQuote T f hext hf.injective qM.codes hG'v hδ (1 / 2 - ε),
      (hT (1 / 2 - ε) (ε / 2) hδ).1 G' _ _ qM.codes hG'v
        (paperRampQuote T f hext hf.injective qM.codes hG'v hδ (1 / 2 - ε))⟩

end Arrows

/-- Target 4c over `𝗣𝗔` at `succDeferral` with the ledger novice: no binder left unwitnessed
(the antecedent is a hypothesis; its only known inhabitant is the diagonal, report §4d).
Source: mandate design decision 7
Kind: L
Fidelity: n/a -/
example (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) (P : History)
    [IsLogicalInductor P (ledgerProcess (paperDP 𝗣𝗔) a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess (paperDP 𝗣𝗔) a e).D n))
    (hT : TowerValuedBase 𝗣𝗔 P (ledgerProcess (paperDP 𝗣𝗔) a e)
      (paperExpert 𝗣𝗔 succDeferral (ledgerProcess (paperDP 𝗣𝗔) a e))) :
    TotalTrustBase 𝗣𝗔 P (ledgerProcess (paperDP 𝗣𝗔) a e)
      (paperExpert 𝗣𝗔 succDeferral (ledgerProcess (paperDP 𝗣𝗔) a e)) :=
  totalTrustBase_of_towerValuedBase 𝗣𝗔 succDeferral succDeferral_strict
    (extendsBase_ledger 𝗣𝗔 a e) hworld hT

end

end Cleanroom.Deference.DefSqueezeDiamond
