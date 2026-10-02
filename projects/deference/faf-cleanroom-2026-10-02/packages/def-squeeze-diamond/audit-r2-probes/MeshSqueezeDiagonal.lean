import Cleanroom.Deference.DefSqueezeDiamond.SelfInstance
import Cleanroom.Deference.DefSqueezeDiamond.Witness

/-!
# audit r2 (adversarial) probe: the repair-round-1 general-class constructions instantiated on
the diagonal family

The ledger's Witness cells for `pinnedGapPackages_self`, `squeeze_self`, `meshGapPlus_reflected` /
`meshGapMinus_reflected` and `gapQuote_meshPlus` / `gapQuote_meshMinus` say "N+ (the diagonal
family through `squeeze_self`)", but no declaration in the package applies any of them to the
diagonal family (`grep` over `Cleanroom/`: the names occur only in their own files and in
docstrings). The theorems have no antecedent beyond the source being e.c. and valued, so the
non-vacuity question is only whether the class is inhabited by a non-degenerate member; this
probe makes the ledger's cited instantiation machine-checked: FAF's diagonal family
`χ_n ↔ P_n(χ_n) < ½` (undecided, non-constant payout) as the literal-indicator source, over
`𝗣𝗔` at `succDeferral`, with FAF's closed deferred-expectation quote as `Y`:

* the two mesh gap quotes of the diagonal source (`gapQuote_meshPlus` / `_Minus`);
* the pinned gap packages and the pinned probe menus applied to it (the existential body);
* the probe follower of its positive mesh gap at margin `½` (`probeData_self`);
* `squeeze_self` on it: `E_n(1(χ_n)) ≈ₙ E_n(⌜P_{n+1}(χ_n)⌝)` through the mesh gap bets.

Positive check; not imported by the library.
-/

namespace Cleanroom.Deference.DefSqueezeDiamond.AuditR2

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefSelfTrust
open Cleanroom.Deference.DefLatticeArrows Cleanroom.Deference.DefLatticeArrows.Witness
open Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-- The diagonal source: the literal indicator of FAF's diagonal family at `½`. -/
abbrev diagX : ℕ → LUV := fun n => literalIndicator (diagFamily 𝗣𝗔 n)

theorem diagX_codes : LUV.MachineThresholdCodeSeq diagX :=
  literalIndicator_machineThresholdCodeSeq (diagFamily_codes 𝗣𝗔)

theorem diagX_valued : Valued (paperDP 𝗣𝗔) diagX :=
  fun _ _ hv => ⟨_, literalIndicator_valuesAt _ _ hv⟩

/-- FAF's closed quote of the self-expert's deferred estimate of the diagonal source. -/
abbrev diagY : ℕ → LUV :=
  (paperDeferredExpectationQuoteCode 𝗣𝗔 succDeferral diagX diagX_codes).luv

theorem diagY_codes : LUV.MachineThresholdCodeSeq diagY :=
  (paperDeferredExpectationQuoteCode 𝗣𝗔 succDeferral diagX diagX_codes).poly

theorem diagY_reflects :
    Reflects (paperDP 𝗣𝗔) (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral)
      diagX diagY :=
  closedQuote_reflects 𝗣𝗔 succDeferral diagX diagX_codes

/-- The two mesh gap quotes of the diagonal source. -/
example : GapQuote (paperDP 𝗣𝗔) (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral)
    diagX diagY 1 (meshGapPlus 𝗣𝗔 succDeferral diagX_codes) :=
  gapQuote_meshPlus 𝗣𝗔 succDeferral diagX_codes diagX_valued

example : GapQuote (paperDP 𝗣𝗔) (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral)
    diagX diagY (-1) (meshGapMinus 𝗣𝗔 succDeferral diagX_codes) :=
  gapQuote_meshMinus 𝗣𝗔 succDeferral diagX_codes diagX_valued

/-- The pinned gap packages, applied to the diagonal source: the existential body. -/
example : ∃ G G' : ℕ → LUV,
    ∃ _qP : GapQuote (paperDP 𝗣𝗔) (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral)
      diagX diagY 1 G,
    ∃ _qM : GapQuote (paperDP 𝗣𝗔) (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral)
      diagX diagY (-1) G',
      ExpertPin (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) G (1 / 2) ∧
      ExpertPin (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) G' (1 / 2) ∧
      RampQuotesAvailable (paperDP 𝗣𝗔)
        (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) G ∧
      RampQuotesAvailable (paperDP 𝗣𝗔)
        (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral) G' :=
  pinnedGapPackages_self 𝗣𝗔 succDeferral succDeferral_strict diagX diagY diagX_codes diagY_codes
    diagX_valued diagY_reflects

/-- The probe follower of the diagonal source's positive mesh gap at margin `½`. -/
example : ProbeData (paperDP 𝗣𝗔) (Expert.self (liaHistory (paperDP 𝗣𝗔)) (paperDP 𝗣𝗔) succDeferral)
    (1 / 2) (meshGapPlus 𝗣𝗔 succDeferral diagX_codes)
    (probeFollower 𝗣𝗔 succDeferral (ε := 1 / 2) (by norm_num)
      (gapQuote_meshPlus 𝗣𝗔 succDeferral diagX_codes diagX_valued).codes)
    (gapQuote_meshPlus 𝗣𝗔 succDeferral diagX_codes diagX_valued).codes :=
  probeData_self 𝗣𝗔 succDeferral (ε := 1 / 2) (by norm_num) (by norm_num)
    (gapQuote_meshPlus 𝗣𝗔 succDeferral diagX_codes diagX_valued).codes
    (gapQuote_meshPlus 𝗣𝗔 succDeferral diagX_codes diagX_valued).gap_valued

/-- `squeeze_self` on the diagonal source: the squeeze run through the mesh gap bets. -/
example :
    (fun n => (diagX n).expect (liaHistory (paperDP 𝗣𝗔)) n) ≈ₙ
      (fun n => (diagY n).expect (liaHistory (paperDP 𝗣𝗔)) n) :=
  squeeze_self 𝗣𝗔 succDeferral succDeferral_strict diagX_codes diagY_codes diagX_valued
    diagY_reflects

end

end Cleanroom.Deference.DefSqueezeDiamond.AuditR2
