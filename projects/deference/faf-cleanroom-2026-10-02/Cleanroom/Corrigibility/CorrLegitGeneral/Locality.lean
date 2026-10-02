import Cleanroom.Corrigibility.CorrLegitGeneral.Defs

/-!
# corr-legit-general — T3(a): locality is forced (the global criterion gives positive access to
legitimacy)

Under the *global* `L`-conditioned criterion every positive-mass legitimate candidate is
certain of its own legitimacy: `LegitimizingTT π F L → ∀ w ∈ L, 0 < π w → P_w(L) = 1`. The
proof is one line with `X = 𝟙_L` (or `𝟙_{supp π_L}`) in the below-threshold inequality, which
is DDB's Lemma 7.2.4 for `π_L` in Total-Trust form. The variable `𝟙_L` is not `Q`-measurable
for a question that does not separate `L`, so the local criterion escapes the proof — and the
leak witness (`WitnessesLeak.lean`, T3(b)) shows it escapes the conclusion too.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Lemma 7.2.4 in Total-Trust form, one line.** If `π` totally trusts the frame, every
support candidate is certain of the support: `0 < π w → P_w(W_π) = 1`. Proof: with
`X = 𝟙_{W_π}` and `s = P_w(W_π) ≤ 1`, every term of the below-threshold sum is `≥ 0`
(`π` vanishes off `W_π`, `X = 1` on it), and the term at `w` is `π w · (1 − s)`; the sum is
`≤ 0`, so `s = 1`.
Source: [[Deference Done Better]] App. B Lemma 7.2.4 l. 510; [[legitimacy-general-final]]
Proofs l. 91 (the one-liner)
Kind: P
Fidelity: exact (hypotheses weakened: Total Trust in place of hull + modest informedness)
Hyps: (a) `∀ v, 0 ≤ π v`, `TotalTrust π F`, `0 < π w` -/
theorem TotalTrust.mass_supp_eq_one {π : W → ℝ} (hπ : ∀ v, 0 ≤ π v) {F : Frame W}
    (h : TotalTrust π F) {w : W} (hw : 0 < π w) : mass (F.P w) (supp π) = 1 := by
  set s := mass (F.P w) (supp π) with hs
  have hs1 : s ≤ 1 := mass_le_one (F.P_mem w) (supp π)
  have hd := totalTrust_iff_dual.1 h (ind (supp π)) s
  have hterm : ∀ v,
      0 ≤ π v * (ind (supp π) v - s) * (if E (F.P v) (ind (supp π)) ≤ s then 1 else 0) := by
    intro v
    by_cases hv : 0 < π v
    · have hvA : ind (supp π) v = 1 := by simp [ind, hv]
      rw [hvA]
      split_ifs
      · exact mul_nonneg (mul_nonneg hv.le (by linarith)) zero_le_one
      · simp
    · have hv0 : π v = 0 := le_antisymm (not_lt.1 hv) (hπ v)
      rw [hv0]; simp
  have hwterm : π w * (1 - s) ≤
      ∑ v, π v * (ind (supp π) v - s) * (if E (F.P v) (ind (supp π)) ≤ s then 1 else 0) := by
    have hwA : ind (supp π) w = 1 := by simp [ind, hw]
    have hwE : E (F.P w) (ind (supp π)) ≤ s := by rw [E_ind]
    calc π w * (1 - s)
        = π w * (ind (supp π) w - s) * (if E (F.P w) (ind (supp π)) ≤ s then 1 else 0) := by
          rw [hwA, if_pos hwE, mul_one]
      _ ≤ _ := single_le_sum (fun v _ => hterm v) (mem_univ w)
  have hle : π w * (1 - s) ≤ 0 := hwterm.trans hd
  have h1 : 1 - s ≤ 0 := by
    by_contra hc
    exact absurd hle (not_le.2 (mul_pos hw (not_le.1 hc)))
  linarith

/-- **Positive access to legitimacy, support form** (Statement 2(a), ddb I5.3): under the global
`L`-conditioned criterion, every positive-mass legitimate candidate is certain of the legitimate
support: `P_w(L ∩ W_π) = 1`.
Source: [[ddb]] I5.3 l. 129; [[legitimacy-general-final]] Statement 2(a) l. 44
Kind: C
Fidelity: exact
Hyps: (a) `∀ v, 0 ≤ π v`, `LegitimizingTT π F L`, `w ∈ L`, `0 < π w` -/
theorem legitimizingTT_mass_legitSupp {π : W → ℝ} (hπ : ∀ v, 0 ≤ π v) {F : Frame W}
    {L : Finset W} (h : LegitimizingTT π F L) {w : W} (hw : w ∈ L) (hπw : 0 < π w) :
    mass (F.P w) (L ∩ supp π) = 1 := by
  have := TotalTrust.mass_supp_eq_one (restrict_nonneg hπ L) h (restrict_pos_of_mem hw hπw)
  rwa [supp_restrict] at this

/-- **Locality is forced (the global form)**: under `LegitimizingTT π F L`, every positive-mass
legitimate candidate is certain of `L` — a legitimate successor is certain of the legitimacy of
the transition it just underwent.
Source: [[legitimacy]] R5.2 l. 99; [[ddb]] I5.3 l. 129; [[legitimacy-general-final]]
Statement 2(a) l. 44, Statement 13 l. 77; corr-wf14-033, corr-wf13-035, corr-wf14b-053
Kind: C
Fidelity: exact
Hyps: (a) `∀ v, 0 ≤ π v`, `LegitimizingTT π F L`, `w ∈ L`, `0 < π w` -/
theorem legitimizingTT_certain_of_legit {π : W → ℝ} (hπ : ∀ v, 0 ≤ π v) {F : Frame W}
    {L : Finset W} (h : LegitimizingTT π F L) {w : W} (hw : w ∈ L) (hπw : 0 < π w) :
    mass (F.P w) L = 1 :=
  le_antisymm (mass_le_one (F.P_mem w) L)
    (calc (1 : ℝ) = mass (F.P w) (L ∩ supp π) := (legitimizingTT_mass_legitSupp hπ h hw hπw).symm
      _ ≤ mass (F.P w) L := mass_mono (F.P_mem w).1 inter_subset_left)

/-- **Absolute continuity, the weaker corollary** (Statement 2(a)'s "`Q ≪ P_{t₁}`"): every
positive-mass legitimate candidate is certain of the judge's support.
Source: [[legitimacy-general-final]] Statement 2(a) l. 44; mandate Known issues 7
Kind: L
Fidelity: exact (absolute continuity on a finite carrier is `P_w(W_π) = 1`)
Hyps: (a) as `legitimizingTT_certain_of_legit` -/
theorem legitimizingTT_absCont {π : W → ℝ} (hπ : ∀ v, 0 ≤ π v) {F : Frame W} {L : Finset W}
    (h : LegitimizingTT π F L) {w : W} (hw : w ∈ L) (hπw : 0 < π w) :
    mass (F.P w) (supp π) = 1 :=
  le_antisymm (mass_le_one (F.P_mem w) (supp π))
    (calc (1 : ℝ) = mass (F.P w) (L ∩ supp π) := (legitimizingTT_mass_legitSupp hπ h hw hπw).symm
      _ ≤ mass (F.P w) (supp π) := mass_mono (F.P_mem w).1 inter_subset_right)

/-- **A successor with residual credence in `¬L` is illegitimate with certainty**: under the
global criterion, a world `w ∈ L` whose expert state gives positive probability to `Lᶜ` has
`π w = 0`.
Source: [[legitimacy-general-final]] Statement 2(a) l. 44 ("a successor entertaining 'I may
have been illegitimately modified' is illegitimate with certainty"), Statement 13 l. 77
Kind: L
Fidelity: exact
Hyps: (a) `∀ v, 0 ≤ π v`, `LegitimizingTT π F L`, `0 < P_w(Lᶜ)`, `w ∈ L` -/
theorem legitimizingTT_residual_illegit {π : W → ℝ} (hπ : ∀ v, 0 ≤ π v) {F : Frame W}
    {L : Finset W} (h : LegitimizingTT π F L) {w : W} (hq : 0 < mass (F.P w) Lᶜ) (hw : w ∈ L) :
    π w = 0 := by
  by_contra hne
  have hpos : 0 < π w := lt_of_le_of_ne (hπ w) (Ne.symm hne)
  have h1 := legitimizingTT_certain_of_legit hπ h hw hpos
  have h2 : mass (F.P w) L + mass (F.P w) Lᶜ = 1 := by
    rw [compl_eq_univ_sdiff, ← mass_univ (F.P_mem w)]
    have := mass_inter_add_mass_sdiff (F.P w) univ L
    rwa [univ_inter] at this
  linarith

/-- The global criterion with `L = univ` says nothing about legitimacy: the conclusion is
`P_w(univ) = 1`, true of every row. (Recorded so the trap is visible; the witnesses carry
`0 < mass π Lᶜ`.)
Source: mandate T3 (trap)
Kind: L
Fidelity: n/a -/
theorem mass_univ_row (F : Frame W) (w : W) : mass (F.P w) univ = 1 := mass_univ (F.P_mem w)

end

end Cleanroom.Corrigibility.CorrLegitGeneral
