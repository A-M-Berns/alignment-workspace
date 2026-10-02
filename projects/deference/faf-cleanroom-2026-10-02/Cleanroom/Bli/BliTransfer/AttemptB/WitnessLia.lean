import Cleanroom.Bli.BliTransfer.AttemptB.WitnessMap
import Cleanroom.Bli.BliTransfer.AttemptB.Clamp
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `bli-transfer` · attempt B · WitnessLia: the hypothesis packages at FAF's LIA

The only file importing the construction (`Construction.Paper.TheoremDP`, which pulls
`LIACompiler`). It instantiates the abstract witnesses at the one non-degenerate inductor FAF
has: `paperLIA 𝗜𝚺₁ : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁)`
(`Construction/Paper/TheoremDP.lean:442` — the mandate reports the name `paperLIA` as absent
at this pin; it exists there as a `noncomputable abbrev` taking `[T.Δ₁]`), over a process with
consistent worlds (`paperDP_hworld 𝗜𝚺₁`, trap (v)).

* `transfer_witness_lia` — T1's full hypothesis package: the LIA is an inductor, its process
  has consistent worlds, and there are `ov`, `E`, a machine-checked oracle, a changed price at
  a day-large sentence, and a presented trader the rewrite changes and which does not exploit
  the overlay (`WitnessMap.transfer_witness`).
* `clamp_lia_not_isLogicalInductor` — T3's refutation is not vacuous: the LIA *is* an
  inductor and its clamp is *not*.

Sources: mandate T1.5, T3; `Construction/Paper/TheoremDP.lean`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-- **T1's hypothesis package at the LIA over `paperDP 𝗜𝚺₁`**: an inductor, a process with
consistent worlds, a re-pricing with an expression map and a machine-checked splice oracle that
changes a day-large price, and a presented trader the rewrite changes and which does not
exploit the overlay.
Source: mandate T1.5
Kind: N+
Fidelity: n/a (finite-support map; see `WitnessMap.lean`)
Hyps: (a) -/
theorem transfer_witness_lia :
    IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) ∧
    (∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
    ∃ (ov : ℕ → Sentence → ℚ) (E : ExprMap (liaHistory (paperDP 𝗜𝚺₁)) ov)
      (_ : SpliceOracle E.expr),
      overlay (liaHistory (paperDP 𝗜𝚺₁)) ov ≠ liaHistory (paperDP 𝗜𝚺₁) ∧
      ∃ Tr : Trader, SpliceBuiltTrader Tr ∧ E.spliceTrader Tr ≠ Tr ∧
        ¬ Tr.Exploits (overlay (liaHistory (paperDP 𝗜𝚺₁)) ov) (paperDP 𝗜𝚺₁) := by
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) := paperLIA 𝗜𝚺₁
  exact ⟨inferInstance, paperDP_hworld 𝗜𝚺₁, transfer_witness _ _⟩

/-- **T3's refutation at the LIA**: the LIA over `paperDP 𝗜𝚺₁` is a logical inductor and its
clamp is not.
Source: mandate T3
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem clamp_lia_not_isLogicalInductor :
    IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) ∧
    ¬ IsLogicalInductor (clamp (liaHistory (paperDP 𝗜𝚺₁))) (paperDP 𝗜𝚺₁) :=
  ⟨paperLIA 𝗜𝚺₁, clamp_not_isLogicalInductor _ _ (paperDP_hworld 𝗜𝚺₁)⟩

end Cleanroom.Bli.BliTransfer.AttemptB
