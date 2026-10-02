import Cleanroom.Trust.LegitLiRegister.Diagonal
import Cleanroom.Deference.DefTrackingPin.Pin

/-!
# `legit-li-register` · Filtered: the legitimacy-filtered sealed sibling (Target 16)

trust-lab-2-041 / scout-deference-core Q5: let `λ_n` be a filter on the sealed sibling's
deliberation and `Y^λ_n` the filtered target; (i) which of T1's hypotheses need re-verification
for `a^λ_n := 𝔼^A_n(C^λ_n)`; (ii) a quote-dependent filter `λ_n = 𝟙[a_n ≤ ½]` reproduces the
`½`-gap; (iii) a filter that never settles makes the filtered contract leave `G`.

(i) **T1 is parametric in the target**: `tracking_fields` is T1 with the carrier unbundled — the
reader `A`, its base, the table `Y`, the settlement schedule, settlement (`hdet`), the stage
non-vacuity, and `a_eq`; **no hypothesis reads where `Y` came from**. A filtered settlement `Y^λ`
is just another table; the "(A1)–(A5) to re-verify" are these fields and none of them mentions
the filter. So the filtered construction **certifies nothing about the filter** — the scout's
pre-registered fake (defining legitimacy as "whatever makes T1 work") is exactly what this
exposes (findings F9).
(ii) The arithmetic core of Claim 1 at the filter: `|λ_n − a_n| ≥ ½` with `λ_n = 𝟙[a_n ≤ ½]`
(`filter_half_gap`), and eventually `½ − δ ≤ |λ_n − Y_n|` once `a ≈ₙ Y` (`filter_half_gap_eventually`).
(iii) is recorded in the report (a never-settling filter conjoined to the contract is undecided,
hence off `G` by `DecidedBy`'s definition; no carrier with a filtered contract is built here).
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefTrackingPin
open Filter Topology

/-- **T1 with its fields explicit** — the hypotheses `tracking` actually uses, and nothing about
the provenance of the table `Y`: the reader `A` is an inductor over its base plus the contract
ledger settled to `Y`; every stage is satisfiable; the contract LUV is determined at `Y n`
(settlement); the published number is the reader's expectation of the contract LUV; and `hz`.
A filtered table `Y^λ` satisfies the same package verbatim.
Source: trust-lab-2-041 (i) ("state which of (A1)–(A5) need re-verification"); `def-frozen-sibling` `tracking`; mandate Target 16 (i)
Kind: L (`pinning_ofApprox`, unbundled)
Fidelity: exact (T1's hypothesis package made explicit)
Hyps: (c) `hz` (checklist row 6); all else (a) -/
theorem tracking_fields (A : History) (DPA0 : DeductiveProcess) (Y : ℕ → ℚ)
    (σ : PublicationSchedule)
    [IsLogicalInductor A (ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ))]
    (hworld : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith ((ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ)).D n))
    (hdet : ∀ n, LUV.DeterminedVia (ledgerLuv 0 n)
      (ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ)) (Y n))
    (a : ℕ → ℚ) (a_eq : ∀ n, (a n : ℝ) = (ledgerLuv 0 n).expect A n)
    (zhat : ℕ → ℚ) (hz : PGenerableRat A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - Y n) atTop (𝓝 0)) :
    (fun n => (a n : ℝ)) ≈ₙ (fun n => (Y n : ℝ)) := by
  have h := pinning_ofApprox (P := A) (DP := ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ))
    (ledgerLuv_thresholdCodes 0) hworld (v := fun n => (Y n : ℝ)) hdet zhat hz hlim
  have he : (fun n => (a n : ℝ)) = fun n => (ledgerLuv 0 n).expect A n := funext a_eq
  rw [he]
  exact h

/-- **A quote-dependent filter reproduces the `½`-gap** (ii): `|𝟙[a_n ≤ ½] − a_n| ≥ ½` at every
day — Claim 1's arithmetic core read at the filter.
Source: trust-lab-2-041 (ii); mandate Target 16 (ii)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem filter_half_gap (a : ℕ → ℝ) (n : ℕ) :
    (1 / 2 : ℝ) ≤ |(if a n ≤ 1 / 2 then (1 : ℝ) else 0) - a n| :=
  abs_indicator_half_sub_ge_half (a n)

/-- The `½`-gap against the verdict, eventually, once the quote tracks it.
Source: trust-lab-2-041 (ii); mandate Target 16 (ii)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem filter_half_gap_eventually {a Y : ℕ → ℝ} (h : a ≈ₙ Y) :
    ∀ δ > 0, ∀ᶠ n in atTop,
      (1 / 2 : ℝ) - δ ≤ |(if a n ≤ 1 / 2 then (1 : ℝ) else 0) - Y n| :=
  eventually_half_sub_le_of_asympEq h

end Cleanroom.Trust.LegitLiRegister
