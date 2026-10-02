import Cleanroom.Deference.DefSqueezeDiamond.Diamond

/-!
# `def-squeeze-diamond` · Fragment: the fragment of Total Trust the squeeze spends (target 3)

lean-deference-2-014: the centered-bet squeeze "spends an *unusual* fragment of TT … which a
forced family has no reason to contain"; vq-wiki-012 §Remarks: "threshold-zero Total Trust
already suffices". Over FAF, after the rescaling `[−1,1] → [0,1]` (threshold `0 → ½`), the
fragment `tower_instance_of_totalTrust_gapBets` consumes is contained in `GapFragment` — a
*sufficient* fragment, one width `ε/2` per threshold (the squeeze itself accepts any `δ < ε`,
`GapBets.lean` l. 188; the mandate prescribed `ε/2`):

* the **above** face only (no below face);
* at thresholds `½ − ε` with width `ε/2`, for `0 < ε ≤ ½` (nothing at or above `½`);
* on sources that are **gap LUVs** of some e.c. valued source (`IsGapSource`), nothing else.

`gapFragment_of_totalTrust` (`L`) is the inclusion; `towerValued_of_gapFragment` is the squeeze
from the fragment alone, over the pinned gap packages. This is what a forcing construction must
force to obtain the tower; the faithful-acceleration family forces gate-weighted instances on
specific bets, which is not this fragment ([[value-iff-mart]] §Where separations survive,
item 3) — recorded, nothing about forcing is proved here.

**The identification (3b).** lean-deference-033 (`CenteredSqueeze` Steps 1–3),
lean-deference-071 ("Lemma 1 twice"), root-deference-007 §2 and
[[total-trust-implies-mart]] (gap bets) are one theorem over FAF,
`tower_instance_of_totalTrust_gapBets`, with Step 0 = `selfPinGap` (self) /
`PinnedGapPackagesBase` (paper expert, distinct novice) / `(c)` (ledger expert). root-007 §6's
scrutiny items: (i) "eventually-constant weights are legal TT instances" = `ramp_eventually_one`
with the ramp `WeightQuote` (a); (ii) "`D_n` is in the e.c. class the TT quantifier ranges
over" = `GapQuote.codes` (a when the package is FAF-built). The exact finite pinch
(`def-lattice-arrows` `Amplifier.lean`, `exact_pinch`) is root-007 §2's "exact finite version"
— cited, not re-proved. See the ledger's route table.
-/

namespace Cleanroom.Deference.DefSqueezeDiamond

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-- **A gap source**: an e.c. LUV family that is the rescaled gap quote (`a = ±1`) of some
e.c. valued source.
Source: mandate target 3a
Kind: D
Fidelity: exact -/
def IsGapSource (DP : DeductiveProcess) (E : Expert DP) (G : ℕ → LUV) : Prop :=
  ∃ (Z Y : ℕ → LUV) (a : ℚ), (a = 1 ∨ a = -1) ∧ Nonempty (GapQuote DP E Z Y a G)

/-- **The gap fragment of Total Trust**: the above-threshold inequality at thresholds `½ − ε`
with width `ε/2` (`0 < ε ≤ ½`), on gap sources only — a sufficient fragment for the squeeze
(which accepts any width `δ < ε`; `ε/2` is the mandate's choice) and nothing beyond it: no below
face, no threshold at or above `½`, no non-gap source.
Source: mandate target 3a; lean-deference-2-014; vq-wiki-012 §Remarks; root-deference-007 §6
Kind: D
Fidelity: variant: a sufficient fragment at width `ε/2` (the squeeze accepts any `δ < ε`); the
rescaled form of "Lemma 1 twice at threshold 0" -/
def GapFragment (P : History) (DP : DeductiveProcess) (E : Expert DP) : Prop :=
  ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 → ∀ G W XW : ℕ → LUV, IsGapSource DP E G →
    LUV.MachineThresholdCodeSeq G → WeightQuote DP E G (rampAbove (ε / 2) (1 / 2 - ε)) W XW →
      (fun n => (XW n).expect P n - ((1 / 2 - ε : ℚ) : ℝ) * (W n).expect P n) ≳ₙ
        (fun _ => (0 : ℝ))

/-- **Total Trust contains the gap fragment** (`L`): the fragment is a restriction of the above
face.
Source: mandate target 3a (`gapFragment_of_totalTrust`)
Kind: L
Fidelity: exact -/
theorem gapFragment_of_totalTrust {E : Expert DP} (hT : TotalTrust P DP E) :
    GapFragment P DP E :=
  fun ε hε _ G W XW _ hG q => hT.above P DP (1 / 2 - ε) (ε / 2) (by positivity) G W XW hG q

/-- **The squeeze from the fragment alone**: `GapFragment` and the pinned gap packages give
`TowerValued` — `tower_instance_of_totalTrust_gapBets` with its TT instances drawn from the
fragment (the gap LUVs are gap sources by construction).
Source: mandate target 3a (`towerValued_of_gapFragment`); [[centered-bet-squeeze]] §2;
[[total-trust-implies-mart]] §Threshold-range remark
Kind: C
Fidelity: weaker: on valued sources; rescaled
Hyps: (c) `PinnedGapPackages`; `GapFragment` is the (fragment of the) deference hypothesis;
`hworld` -/
theorem towerValued_of_gapFragment [IsLogicalInductor P DP] {E : Expert DP}
    (hF : GapFragment P DP E) (hg : PinnedGapPackages DP E)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    TowerValued P DP E := by
  intro Z Y hZ hY hval hR
  obtain ⟨G, G', qP, qM, pinP, pinM, hrP, hrM⟩ := hg Z Y hZ hY hval hR
  refine tower_instance_of_totalTrust_gapBets hZ hY qP qM pinP pinM
    (fun ε hε hε2 => ⟨ε / 2, by positivity, by linarith, ?_⟩)
    (fun ε hε hε2 => ⟨ε / 2, by positivity, by linarith, ?_⟩) hworld
  · obtain ⟨W, XW, ⟨q⟩⟩ := hrP (1 / 2 - ε) (ε / 2) (by positivity)
    exact ⟨W, XW, q, hF ε hε hε2 G W XW ⟨Z, Y, 1, Or.inl rfl, ⟨qP⟩⟩ qP.codes q⟩
  · obtain ⟨W, XW, ⟨q⟩⟩ := hrM (1 / 2 - ε) (ε / 2) (by positivity)
    exact ⟨W, XW, q, hF ε hε hε2 G' W XW ⟨Z, Y, -1, Or.inr rfl, ⟨qM⟩⟩ qM.codes q⟩

/-- **The fragment is strictly a restriction**: it says nothing at threshold `½` or above, on
the below face, or on non-gap sources — the quantifier bounds `ε ≤ ½` and `IsGapSource` are
part of the definition (the mandate's "and nothing else"), recorded as the predicate's shape.
Source: mandate target 3a (the docstring remark)
Kind: L
Fidelity: n/a -/
theorem gapFragment_iff {E : Expert DP} :
    GapFragment P DP E ↔ ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 → ∀ G W XW : ℕ → LUV,
      IsGapSource DP E G → LUV.MachineThresholdCodeSeq G →
        WeightQuote DP E G (rampAbove (ε / 2) (1 / 2 - ε)) W XW →
          (fun n => (XW n).expect P n - ((1 / 2 - ε : ℚ) : ℝ) * (W n).expect P n) ≳ₙ
            (fun _ => (0 : ℝ)) := Iff.rfl

end

end Cleanroom.Deference.DefSqueezeDiamond
