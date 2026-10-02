import Cleanroom.Deference.DefFrozenSibling.OnG

/-!
# Audit round 3 (fidelity) probe — at `timely_cofinite_const`'s pins, `hz` is discharged and the
regime is quote-redundant

Bearing: the nine on-`G` two-way rows read `partial: over timely_cofinite_const and hz at that
pair` (ledger header, the `engineA_truth`/`condTower_onG`/`valueTwoOption_onG`/… rows,
`open.txt`: "plus hz there for the hz rows"). But at those pins the diagonal property *is* an
`A`-generable approximant: `ẑ := Y0` is a `MachineRatCodes` (`Y0_machineRatCodes`) and
`cofinite_const_iff` turns the OPEN's last conjunct into `Y0 − S.Y → 0`. So the residual of every
on-`G` two-way row at that pair is the OPEN alone — no (c) survives — and the same holds for the
three global rows (`tracking`, `metaTrust`, `metaTrust_expect`) at that pair, where the ledger
files them under `frozenSystem_exists` "with `hz` undischarged". Second, the two polarity
certificates of `engineA_truth_ofPattern` hold at *any* system with those pins, so the OPEN pair
of record for the on-`G` rows is itself in the quote-redundant regime of findings F4.

Not imported by the library.
-/

namespace Cleanroom.Deference.DefFrozenSibling.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair Cleanroom.Deference.DefFrozenSibling
open Filter Topology

/-- At the pins of `timely_cofinite_const`, the diagonal property supplies T1's `hz` package with
`ẑ := Y0`: the alternating table is generable at `A` and `Y0 − S.Y → 0`.
Source: audit probe. Kind: L. Fidelity: n/a -/
theorem hz_of_diagonal (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    PGenerableRat S.A Y0 ∧ Tendsto (fun n => (Y0 n : ℝ) - S.Y n) atTop (𝓝 0) := by
  refine ⟨PGenerableRat.ofMachineRatCodes Y0_machineRatCodes _, ?_⟩
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨δ, hδ0, hδr⟩ := exists_rat_btwn hr
  have hδ0' : (0 : ℚ) < δ := by exact_mod_cast hδ0
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hdiag δ hδ0')
  refine ⟨N, fun n hn => ?_⟩
  have h := (cofinite_const_iff S hb hc hF δ n).1 (hN n hn)
  have h1 : |(Y0 n : ℝ) - S.Y n| ≤ (δ : ℝ) := by
    rw [abs_sub_comm]
    exact_mod_cast h
  rw [Real.dist_eq, sub_zero]
  exact h1.trans_lt hδr

/-- T1 at the pins with the diagonal property, no residual (c).
Source: audit probe. Kind: L. Fidelity: n/a -/
theorem tracking_of_diagonal (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    (fun n => (S.a n : ℝ)) ≈ₙ (fun n => (S.Y n : ℝ)) :=
  tracking S Y0 (hz_of_diagonal S hb hc hF hdiag).1 (hz_of_diagonal S hb hc hF hdiag).2

/-- The conditional tower at the pins with the diagonal property, along the whole sequence, no
residual (c): the `hz`-rows' residual at `timely_cofinite_const` is the OPEN alone.
Source: audit probe. Kind: L. Fidelity: n/a -/
theorem condTower_of_diagonal (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    (fun n => S.Hplus n (S.contract n)) ≈ₙ (fun n => (ledgerLuv 0 n).expect S.Hplus n) := by
  obtain ⟨ε, hε, -, hT⟩ :=
    timely_all_of_diagonal S (fun n => (pinned_base0_decided S hb hc hF n).1) hdiag
  obtain ⟨hz, hlim⟩ := hz_of_diagonal S hb hc hF hdiag
  have h := condTower_onG S ε hε (UnaryRuler.const 0) (fun n _ => hT n) Y0 hz hlim
  rw [asympEq_iff_eventuallyWithin]
  intro δ hδ
  filter_upwards [h δ hδ] with n hn
  exact hn rfl

/-- `hpat₁` at any system with the three pins (the "decided true" subfamily is e.c.): the OPEN
pair of record for the on-`G` rows is in the quote-redundant regime.
Source: audit probe. Kind: L. Fidelity: n/a -/
theorem hpat₁_of_pins (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral) :
    MachineSentenceCodes
      (fun n => if (fun _ : ℕ => 0) n = 0 ∧ truthAt S n = 1 then S.contract n else ⊤) :=
  (MachineSentenceCodes.ifZero contract5_codes (MachineSentenceCodes.const ⊤) evenZero_ruler).of_eq
    (fun n => by
      rw [(pinned_base0_decided S hb hc hF n).2, hc]
      unfold Y0
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h])

/-- `hpat₀` at any system with the three pins.
Source: audit probe. Kind: L. Fidelity: n/a -/
theorem hpat₀_of_pins (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral) :
    MachineSentenceCodes
      (fun n => if (fun _ : ℕ => 0) n = 0 ∧ truthAt S n = 0 then S.contract n
        else ∼(⊤ : Sentence)) :=
  (MachineSentenceCodes.ifZero contract5_codes (MachineSentenceCodes.const (∼(⊤ : Sentence)))
    flip_ruler).of_eq (fun n => by
      rw [(pinned_base0_decided S hb hc hF n).2, hc]
      unfold Y0
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h])

end Cleanroom.Deference.DefFrozenSibling.AuditR3
