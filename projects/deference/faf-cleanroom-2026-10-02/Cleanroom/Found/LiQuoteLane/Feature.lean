import Cleanroom.Found.LiQuoteLane.Codes
import Cleanroom.Found.LiAsympCalc.Ramp
import LogicalInduction.Construction.Quotation.DeferralFibre

/-!
# `li-quote-lane` · Feature: the ledger price feature is a legal feature (T4.2)

FAF's `EF` (`Framework/Criterion.lean`) has no constructor for an externally posted number: a
rational sequence is `PGenerableRat P q` only through a feature progression that denotes it,
and for the raw constant `EF.const (a n)` that means the *digits of `a n`* are machine-written
(`MachineRatCodes`, `PGenerableRat.ofMachineRatCodes`) — the corpus's hypothesis (L). So "a
published number is a legal feature of the reader's market" (trust-lab-013, trust-lab-2-009) is
not statable over FAF as written; this file proves what *is*:

* `ledgerFeature j n`, the price feature of the day-`n` threshold bundle of the ledger LUV, is a
  `PGenerableWeighting` (`ledgerFeature_pgenerable`) and denotes `𝔼^H_n(α_{j,n})`
  (`ledgerFeature_denote`);
* the ramp `ledgerRamp j t δ n = Ind_δ(𝔼^H_n(α_{j,n}) > t)` is a `PGenerableWeighting`
  (`ledgerRamp_pgenerable`) and is within `|𝔼^H_n(α_{j,n}) − a_n| / δ` of the ramp of the
  published number (`ledgerRamp_tracks`, [[route-recurring-ccee]] §2 (R2) verbatim — vq-wiki-048 (d);
  not [[route-sparse-schedule]] §5.3's threshold-atom indicator, which that note calls defective).

What the feature *tracks* is the reader's expectation of the ledger LUV. That it tends to the
published number is `readability` (`Readability.lean`), which — as the source's own §5.3 says
and the mandate's T3.1 did not — needs (L): see `Readability.lean` and findings F2.

Scope: one-way.
-/

namespace Cleanroom.Found.LiQuoteLane

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- The ledger price feature denotes the reader's day-`n` expectation of the ledger LUV.
Source: mandate T4.2; FAF `priceFeature_denote`, `expectAffine_price`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerFeature_denote (P : History) (j n : ℕ) :
    (ledgerFeature j n).denote P = (ledgerLuv j n).expect P n := by
  unfold ledgerFeature
  rw [AffineCombination.priceFeature_denote, LUV.expectAffine_price]

/-- A constant feature progression is a `PGenerableWeighting`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem pgenerableWeighting_const (q : ℚ) : PGenerableWeighting (fun _ : ℕ => EF.const q) where
  polySeg := MachineSpliceStream.serialize_const q
  rank_le := fun _ => by simp
  closed := fun _ _ _ => by simp [EF.denote]

/-- **T4.2 (headline). The ledger price feature is a legal feature progression** (FAF's
`PGenerableWeighting`: machine-metered serialization, rank `≤ n` — every price inside is a
day-`n` price — closed denotation). The serialization is FAF's `PolySequence.priceFeature_polySeg`
on the day-`n` threshold mesh of the ledger LUV, whose `PolySequence` certificate is
`expectAffineSeq_polySequence` at the e.c. certificate `ledgerLuv_thresholdCodes` (T1.3). **What
this makes legal is the reader's day-`n` *estimate* `𝔼^P_n(α_{j,n})` of the published number**
(`ledgerFeature_denote`) — the feature does not mention the table `a` at all; the FAF-faithful
form of "a published bounded number is a legal feature of the reader's market" is: its estimate
is legal, through the decided sentences that name the number, and *equality* of that estimate
with the number is L4 (`readability`), which costs `hL`. Scope: one-way.
Source: [[route-recurring-ccee]] §2 (R2) (vq-wiki-048 (d): `â_n := 𝔼^H_n(⌜a_n⌝)`); [[route-sparse-schedule]] §5.1–5.3; trust-lab-013; trust-lab-2-009
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerFeature_pgenerable (j : ℕ) : PGenerableWeighting (fun n => ledgerFeature j n) := by
  have hpoly := LUV.expectAffineSeq_polySequence (fun n => ledgerLuv j n)
    (ledgerLuv_thresholdCodes j)
  refine { polySeg := ?_, rank_le := ?_, closed := ?_ }
  · refine (hpoly.priceFeature_polySeg.comp (UnaryRuler.id.pair UnaryRuler.id)).of_eq
      fun n => ?_
    simp only [Nat.unpair_pair]
    rfl
  · intro n
    refine AffineCombination.priceFeature_rank _ (Nat.zero_le n) (by simp [LUV.expectAffine]) ?_
    intro p hp
    simp only [LUV.expectAffine, List.mem_map, List.mem_range] at hp
    obtain ⟨i, -, rfl⟩ := hp
    simp
  · intro n ρ V
    exact hpoly.priceFeature_closed n n ρ V

/-- The ramp of the ledger price feature: `Ind_δ(𝔼^H_n(α_{j,n}) > t)` as an expressible feature
(FAF's `ctsIndFeature` at constant width `δ` and constant threshold `t`).
Source: [[route-recurring-ccee]] §2 (R2) (vq-wiki-048 (d): `ũ_n := Ind_δ(â_n > t)`); [[faithful-acceleration]] §5 (the gate `g_n`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def ledgerRamp (j : ℕ) (t δ : ℚ) (n : ℕ) : EF :=
  ctsIndFeature (fun _ => δ) (fun n => ledgerFeature j n) (fun _ => EF.const t) n

/-- **The ramp of the ledger price feature is a legal feature progression.**
Source: [[route-recurring-ccee]] §2 (R2) (vq-wiki-048 (d)); FAF `ctsIndFeature_generated`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem ledgerRamp_pgenerable (j : ℕ) (t δ : ℚ) : PGenerableWeighting (ledgerRamp j t δ) :=
  ctsIndFeature_generated _ _ _ (MachineRatCodes.const (1 / δ)) (ledgerFeature_pgenerable j)
    (pgenerableWeighting_const t)

/-- The ramp denotes `ctsInd δ (𝔼^H_n(α_{j,n})) t` for a positive width.
Source: mandate T4.2; FAF `ctsIndFeature_denote`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerRamp_denote (j : ℕ) {t δ : ℚ} (hδ : 0 < δ) (P : History) (n : ℕ) :
    (ledgerRamp j t δ n).denote P = ctsInd δ ((ledgerLuv j n).expect P n) (t : ℝ) := by
  unfold ledgerRamp
  rw [ctsIndFeature_denote _ _ _ (fun _ => hδ), ledgerFeature_denote]
  simp

/-- The ramp `ctsInd δ · t` is `1/δ`-Lipschitz in its argument.
Source: none: infrastructure ([[route-recurring-ccee]] §2 (R2)'s `|ũ_n − u_n| ≤ |â_n − a_n|/δ`)
Kind: L
Fidelity: n/a -/
theorem abs_ctsInd_sub_ctsInd_le {δ : ℚ} (hδ : 0 < δ) (x y t : ℝ) :
    |ctsInd δ x t - ctsInd δ y t| ≤ |x - y| / δ := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  calc |min 1 (max 0 ((x - t) / (δ : ℝ))) - min 1 (max 0 ((y - t) / (δ : ℝ)))|
      ≤ max |(1 : ℝ) - 1| |max 0 ((x - t) / (δ : ℝ)) - max 0 ((y - t) / (δ : ℝ))| :=
        abs_min_sub_min_le_max _ _ _ _
    _ = |max 0 ((x - t) / (δ : ℝ)) - max 0 ((y - t) / (δ : ℝ))| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
    _ ≤ max |(0 : ℝ) - 0| |(x - t) / (δ : ℝ) - (y - t) / (δ : ℝ)| :=
        abs_max_sub_max_le_max _ _ _ _
    _ = |(x - t) / (δ : ℝ) - (y - t) / (δ : ℝ)| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
    _ = |x - y| / δ := by
        rw [show (x - t) / (δ : ℝ) - (y - t) / (δ : ℝ) = (x - y) / (δ : ℝ) by ring, abs_div,
          abs_of_pos hδR]

/-- **T4.2, tracking (vq-wiki-048 (d) verbatim):** the ramp of the ledger price feature is within
`|𝔼^H_n(α_{j,n}) − a j n| / δ` of the ramp of the published number. Whether the right side
vanishes is `readability` (`Readability.lean`), which needs (L).
Source: [[route-recurring-ccee]] §2 (R2) (vq-wiki-048 (d): `|ũ_n − u_n| ≤ |â_n − a_n|/δ`, "R2 works iff `â_n → a_n`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerRamp_tracks (j : ℕ) {t δ : ℚ} (hδ : 0 < δ) (P : History) (a : ℕ → ℕ → ℚ)
    (n : ℕ) :
    |(ledgerRamp j t δ n).denote P - ctsInd δ (a j n) t| ≤
      |(ledgerLuv j n).expect P n - a j n| / δ := by
  rw [ledgerRamp_denote j hδ]
  exact abs_ctsInd_sub_ctsInd_le hδ _ _ _

end Cleanroom.Found.LiQuoteLane
