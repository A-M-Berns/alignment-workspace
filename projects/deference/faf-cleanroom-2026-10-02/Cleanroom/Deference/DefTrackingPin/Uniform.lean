import Cleanroom.Deference.DefTrackingPin.Pin

/-!
# `def-tracking-pin` · Uniform: pinning over a countable family of items at once (extension)

The mandate's extension asks for a quantitative T1 (an explicit `ε_n`) and, as the cheaper
fallback that still serves `def-frozen-sibling`, the **uniform** pinning over all items of a ledger
at once — one reader, every `j`. The rate is not attempted (report §Extension: FAF's
`affine_provind_*` are stated `∀ ε, ∀ᶠ n` with no modulus, and `IsLogicalInductor` is a `Prop`
that exposes no trader budget to extract one from). The uniform forms are here, so that
dependents do not re-derive them: T1 and T3 at the ledger, quantified over `j`, each an instance
of the per-item theorem (kind L, said so). Reader `P`; one-way.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane
open Filter Topology

/-- **Uniform T1 at the ledger**: one reader `P` over the ledger process tracks every item's table
at once, given a `P`-generable approximant per item. Per-item instance of `pinning_ledger`.
Reader `P`; one-way.
Source: mandate, extension (uniform pinning); anson-042
Kind: L (the `∀ j` instance of `pinning_ledger`)
Fidelity: variant: plain trader class (as `pinning_ofApprox`)
Hyps: (c) `hz` per item (as `pinning_ofApprox`); all else (a) -/
theorem pinning_ledger_uniform (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1)
    (zhat : ℕ → ℕ → ℚ) (hz : ∀ j, PGenerableRat P (zhat j))
    (hlim : ∀ j, Tendsto (fun n => (zhat j n : ℝ) - a j n) atTop (𝓝 0)) :
    ∀ j, (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ)) :=
  fun j => pinning_ledger P base a e hworld hmem j (zhat j) (hz j) (hlim j)

/-- **Uniform T3 at the ledger**: one reader `P` tracks every item whose table converges (to any
real), with no generability. Per-item instance of `pinning_ofTendsto` at `ledgerLuv_determinedVia`.
Reader `P`; one-way.
Source: mandate, extension (uniform pinning); anson-030; anson-043
Kind: L (the `∀ j` instance of `pinning_ofTendsto`)
Fidelity: exact
Hyps: (a) none -/
theorem pinning_ledger_uniform_ofTendsto (P : History) (base : DeductiveProcess)
    (a : ℕ → ℕ → ℚ) (e : ℕ → PublicationSchedule) [IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (L : ℕ → ℝ)
    (hconv : ∀ j, Tendsto (fun n => (a j n : ℝ)) atTop (𝓝 (L j))) :
    ∀ j, (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ)) :=
  fun j => pinning_ofTendsto (P := P) (ledgerLuv_thresholdCodes j) hworld
    (fun n => ledgerLuv_determinedVia base a e hmem j n) (hconv j)

end Cleanroom.Deference.DefTrackingPin
