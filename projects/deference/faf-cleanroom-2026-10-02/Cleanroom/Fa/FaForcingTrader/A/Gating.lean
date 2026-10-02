import Cleanroom.Fa.FaForcingTrader.A.TheoremSS
import Cleanroom.Fa.FaTheoremA.LemmaP

/-!
# `fa-forcing-trader` · angle A · Gating: the trust-lab gating facts over FAF (T12 (b), (c))

* (b) trust-lab-046's "gating breaks calibration": over FAF, `evenDays` *is* generable
  (fa-theorem-a's `evenDays_pgenerable`), so a scenario in which the all-days weighting is
  calibrated but the even-days gate of it carries a persistent bias **cannot be an inductor's** —
  it is fa-theorem-a's `engine_no_persistent_bias` at the gate `evenDays · W`. Kind L: one
  instantiation; the lab's abstract scenario is the real-sequence contrapositive.
* (c) trust-lab-048's "gate silence": a gate with bounded total mass is not a divergent weighting,
  so every averaged statement on it is vacuous. Kind L.
* (a) is `gated_theoremSS` (TheoremSS.lean). (d)–(f) are findings (report §T12), not built.
-/

namespace Cleanroom.Fa.FaForcingTrader.A

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Cleanroom.Fa.FaForcingTrader
  Filter Topology

/-- **T12 (b). An error-correlated even-days gate with a persistent bias is not an inductor's.**
For any inductor `A` with a quote package and any generable `W`: it is impossible that the gate
`evenDays · W` is divergent in `A`'s prices and that, from some day on, the quote exceeds the
realized value by a fixed `c > 0` wherever that gate is positive. This is
`engine_no_persistent_bias` at `evenDays.mul W`; trust-lab-046's scenario (calibrated on `w ≡ 1`,
biased on the even days) is thereby excluded for inductors — the FAF reading of "gating breaks
calibration" is that the gated class is still generable, so the criterion sees the gate.
Scope: one-way; the (c) is `pkg.reflected`.
Source: trust-lab-046; fa-theorem-a `engine_no_persistent_bias`, `evenDays_pgenerable`
Kind: L
Fidelity: exact (one instantiation)
Hyps: (a) `hworldA`, `hW`; (c) `pkg.reflected`. -/
theorem not_inductor_of_gated_bias {H A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    {W : ℕ → EF} (hW : PGenerableWeighting W) :
    ¬ (DivergentWeighting (fun n => EF.mul (evenDays n) (W n)) A ∧ ∃ c > 0, ∃ N, ∀ n ≥ N,
        0 < (EF.mul (evenDays n) (W n)).denote A → c ≤ quoteSeq Y A n - realized H f X n) :=
  engine_no_persistent_bias pkg hworldA (evenDays_pgenerable.mul hW)

/-- **T12 (c). Gate silence**: a weighting with bounded total mass is not divergent, so no averaged
statement on it has content.
Source: trust-lab-048
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bounded_gate_mass_not_divergent {W : ℕ → EF} {P : History} {M : ℝ}
    (hM : ∀ n, prefixSum (fun i => (W i).denote P) n ≤ M) : ¬ DivergentWeighting W P := by
  intro hdiv
  obtain ⟨n, hn⟩ := (hdiv.2.eventually (eventually_gt_atTop M)).exists
  linarith [hM n]

end Cleanroom.Fa.FaForcingTrader.A
