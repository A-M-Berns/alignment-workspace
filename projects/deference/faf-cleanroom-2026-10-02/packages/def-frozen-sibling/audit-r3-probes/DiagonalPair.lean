import Cleanroom.Deference.DefFrozenSibling.OnG

/-!
# Audit round 3 (adversarial) probe — the OPEN pair of record, read closely

The ledger files the nine on-`G` two-way rows as `partial: over timely_cofinite_const` "and `hz`
at that pair", and the three global two-way rows (`tracking`, `metaTrust`, `metaTrust_expect`) as
`partial: over frozenSystem_exists`, "where `hz` has no discharge". This probe shows, at any
system with `timely_cofinite_const`'s three process pins (shared process `base0`, contracts
`contract5`, horizon `succDeferral`) and its diagonal property:

1. **`hz` is free.** `Y0` is a `MachineRatCodes`, so `PGenerableRat S.A Y0` holds at *every*
   system (`hz_of_pins`), and the diagonal property *is* `hlim : Y0 − S.Y → 0`
   (`hlim_of_diagonal`). Hence T1 (`tracking_of_diagonal`), T2 (`metaTrust_of_diagonal`,
   `metaTrust_expect_of_diagonal`) and the H-side engine (`condTower_of_diagonal`) are all
   discharged there with **no hypothesis beyond the OPEN row's own conjuncts** — the "plus `hz`
   there" of the Status cells is automatic, and the three global rows have a conditional two-way
   instance at this pair too.
2. **The pair of record is in the quote-redundant regime.** The polarity pattern of `contract5`
   over `base0` is even/odd, so the two certificates of `engineA_truth_ofPattern` exist at any
   system with the pins (`hpat₁_of_pins`, `hpat₀_of_pins`) and the `hz`-free route reaches
   `engineA_truth`'s conclusion there (`engineA_truth_of_diagonal_noHz`). So **every** two-way
   instance the package has or conditionally has — `onGSystem` and the `timely_cofinite_const`
   pair alike — lives where findings F4 says the quote does no work. The package says this of
   `onGSystem` only.

Not imported by the library.
-/

namespace Cleanroom.Deference.DefFrozenSibling.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair Cleanroom.Deference.DefFrozenSibling
open Filter Topology

/-- `hz` at every system: the alternating table is machine-metered, hence generable at any market. -/
theorem hz_of_pins (S : FrozenSystem) : PGenerableRat S.A Y0 :=
  PGenerableRat.ofMachineRatCodes Y0_machineRatCodes _

/-- The diagonal property at the pins is `hlim`: `Y0 − S.Y → 0`. -/
theorem hlim_of_diagonal (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    Tendsto (fun n => (Y0 n : ℝ) - S.Y n) atTop (𝓝 0) := by
  obtain ⟨ε, hε, -, hT⟩ :=
    timely_all_of_diagonal S (fun n => (pinned_base0_decided S hb hc hF n).1) hdiag
  refine squeeze_zero_norm' (Filter.Eventually.of_forall fun n => ?_) hε
  have h := (hT n).2
  rw [(pinned_base0_decided S hb hc hF n).2] at h
  have h' : |(S.Y n : ℝ) - (Y0 n : ℝ)| ≤ (ε n : ℝ) := by exact_mod_cast h
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact h'

/-- T1 at the pair of record, with no `hz` hypothesis: `a ≈ₙ Y`. -/
theorem tracking_of_diagonal (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    (fun n => (S.a n : ℝ)) ≈ₙ (fun n => (S.Y n : ℝ)) :=
  tracking S Y0 (hz_of_pins S) (hlim_of_diagonal S hb hc hF hdiag)

/-- T2b at the pair of record, no `hz`. -/
theorem metaTrust_of_diagonal (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) {ε₀ : ℚ} (hε₀ : 0 < ε₀) :
    (fun n => S.Hplus n (calSentence ε₀ n)) ≈ₙ fun _ => 1 :=
  metaTrust S hε₀ Y0 (hz_of_pins S) (hlim_of_diagonal S hb hc hF hdiag)

/-- T2a at the pair of record, no `hz`. -/
theorem metaTrust_expect_of_diagonal (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    (fun n => (ledgerLuv 0 n).expect S.Hplus n) ≈ₙ (fun n => (ledgerLuv 1 n).expect S.Hplus n) :=
  metaTrust_expect S Y0 (hz_of_pins S) (hlim_of_diagonal S hb hc hF hdiag)

/-- The H-side engine (conditional tower) at the pair of record, `t ≡ 0`, no `hz`: so the
`hz`-rows are partial over `timely_cofinite_const` alone. -/
theorem condTower_of_diagonal (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    ∃ ε : ℕ → ℚ, Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧ (∀ n, Timely S ε n) ∧
      AgreeAlong (fun _ => 0) (fun n => S.Hplus n (S.contract n))
        (fun n => (ledgerLuv 0 n).expect S.Hplus n) := by
  obtain ⟨ε, hε, -, hT⟩ :=
    timely_all_of_diagonal S (fun n => (pinned_base0_decided S hb hc hF n).1) hdiag
  exact ⟨ε, hε, hT, condTower_onG S ε hε (UnaryRuler.const 0) (fun n _ => hT n) Y0 (hz_of_pins S)
    (hlim_of_diagonal S hb hc hF hdiag)⟩

/-- `hpat₁` at any system with the pins, `t ≡ 0`: the "decided true" subfamily is e.c. -/
theorem hpat₁_of_pins (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral) :
    MachineSentenceCodes
      (fun n => if (fun _ : ℕ => 0) n = 0 ∧ truthAt S n = 1 then S.contract n else ⊤) :=
  (MachineSentenceCodes.ifZero contract5_codes (MachineSentenceCodes.const ⊤) evenZero_ruler).of_eq
    (fun n => by
      rw [(pinned_base0_decided S hb hc hF n).2, hc]
      unfold Y0
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h])

/-- `hpat₀` at any system with the pins, `t ≡ 0`: the "decided false" subfamily is e.c. -/
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

/-- The pair of record is quote-redundant: at any system with the pins and the diagonal property,
the `hz`-free pattern route reaches `engineA_truth`'s conclusion along the whole sequence. -/
theorem engineA_truth_of_diagonal_noHz (S : FrozenSystem) (hb : S.base = base0)
    (hc : S.contract = contract5) (hF : S.F = succDeferral)
    (hdiag : ∀ δ : ℚ, 0 < δ → ∀ᶠ n in atTop, Timely S (fun _ => δ) n) :
    ∃ ε : ℕ → ℚ, Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧ (∀ n, Timely S ε n) ∧
      AgreeAlong (fun _ => 0) (fun n => (S.a n : ℝ)) (fun n => (truthAt S n : ℝ)) := by
  obtain ⟨ε, hε, -, hT⟩ :=
    timely_all_of_diagonal S (fun n => (pinned_base0_decided S hb hc hF n).1) hdiag
  exact ⟨ε, hε, hT, engineA_truth_ofPattern S ε hε (UnaryRuler.const 0) (fun n _ => hT n)
    (hpat₁_of_pins S hb hc hF) (hpat₀_of_pins S hb hc hF)⟩

end Cleanroom.Deference.DefFrozenSibling.AuditR3
