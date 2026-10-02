import Cleanroom.Deference.DefArgmaxValue.Theorem
import Cleanroom.Deference.DefArgmaxValue.Refuted
import Cleanroom.Deference.DefArgmaxValue.Characterize
import Cleanroom.Deference.DefSelfTrust.Est

/-!
# `def-argmax-value` · NotImplied: H3 is not implied by the other hypotheses of the scoped theorem —
assembled in Lean on the liar probe (repair round 1; audit r1 fidelity item 4)

The central audit item of lean-deference-2-025 (AUDIT §3.3): `scoped_value` is not a squeeze
because its scope condition H3 is a condition on the menu that the rest of the hypothesis package
does not imply. The package argued this in docstrings; here it is one theorem:

* `probeComposite` — the composite `½(S − const s + 1)` of the honest follower against the
  constant option on the probe menu, a select of constants (`½` when `χ_n`, `(1 − s)/2` otherwise);
* `probe_value_instance_refuted` — the conclusion of `scoped_value` at `i = 1` fails on the probe
  (`E^P(S) → s² < s ← E^P(const s)`, the computation of `value_refuted`);
* `h3_not_implied_by_rest` — the conjunction: on the probe menu, Total Trust (`selfTotalTrust`),
  the fold clause at the probe's package (`concentrationFolds_self`), the follower's `Follows`,
  ramp quotes on the composite (`paperExpert_rampQuotesAvailable`) **all hold**, while
  `CondStableOn` fails (`condStableOn_probe_refuted`) and the conclusion fails;
* `scoped_value_probe_of_h3` — `scoped_value` applied to the probe with every binder but H3
  discharged: H3 alone would give the conclusion;
* `condStableOn_probe_refuted'` — hence H3 fails on the probe, by modus tollens through the scoped
  theorem (an independent re-derivation of `condStableOn_probe_refuted`: the two proofs agree);
* `condStableOn_probe_refuted_any_package` (repair round 2, audit r2 fidelity N4) — H3 fails on
  the probe *menu*, for every selection package of the self-expert on it, so the conjunction
  above is a statement about the menu and not about `probePackage`.

Single market (self); every input a theorem of the package.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
variable (f : DeferralFunction) (s : ℚ)

omit [Entailment.Consistent T] in
/-- **The probe composite** `½(S − const s + 1)` of the honest follower against option `1`: valued
`½` when `χ_n` holds (`S = s`), `(1 − s)/2` otherwise (`S = 0`) — a select of constants, slack `0`.
Source: mandate target 8a (the composite); audit r1 fidelity item 4
Kind: D
Fidelity: exact (slack `0`) -/
def probeComposite (hs : 0 ≤ s ∧ s ≤ 1) :
    Composite (paperDP T) (probeFollower T f s hs.1) ((probeMenu T f s hs.1).O 1) where
  D := selectLUV (liarSentence T f s hs.1) (fun _ => constLUV (1 / 2))
    (fun _ => constLUV ((1 - s) / 2))
  codes := selectLUV_codes (liarSentence_codes T f s hs.1) (constLUV_codes (by norm_num))
    (constLUV_codes (by linarith [hs.2]))
  slack := fun _ => 0
  slack_tendsto := tendsto_const_nhds
  reflected := fun n v hv xS xO hxS hxO => by
    have hS := probeFollower_valuesAt T f s hs n v hv
    have hK : v.ValuesAt ((probeMenu T f s hs.1).O 1 n) (s : ℝ) := by
      simp only [probeMenu_O_one]
      exact constLUV_valuesAt hs v
    rw [hxS.eq hS, hxO.eq hK]
    have hsel := selectLUV_valuesAt (liarSentence T f s hs.1) (fun _ => constLUV (1 / 2))
      (fun _ => constLUV ((1 - s) / 2)) n v (constLUV_valuesAt (s := 1 / 2) (by norm_num) v)
      (constLUV_valuesAt (s := (1 - s) / 2) ⟨by linarith [hs.2], by linarith [hs.1]⟩ v)
    refine ⟨_, hsel, ?_⟩
    unfold PCWorld.payout
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- **The conclusion of the scoped theorem fails on the probe at `i = 1`**:
`E^P_n(S_n) → s² < s ← E^P_n(const s)` (the computation inside `value_refuted`, as the instance).
Source: [[loop-direction]] §The liar probe (2); mandate target 1c(2)
Kind: refuted
Fidelity: exact
Hyps: (a); `hf` -/
theorem probe_value_instance_refuted (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ¬ ((fun n => (probeFollower T f s hs0.le n).expect (liaHistory (paperDP T)) n) ≳ₙ
        (fun n => ((probeMenu T f s hs0.le).O 1 n).expect (liaHistory (paperDP T)) n)) := by
  have hs : 0 ≤ s ∧ s ≤ 1 := ⟨hs0.le, hs1.le⟩
  simp only [probeMenu_O_one]
  refine not_asympGE_of_tendsto_neg (c := (s : ℝ) * s - s) ?_ ?_
  · have h0 : (0 : ℝ) < s := by exact_mod_cast hs0
    have h1 : (s : ℝ) < 1 := by exact_mod_cast hs1
    nlinarith
  · have hS := probeFollower_expect T f s hs
    unfold AsympEq at hS
    have hpn := liarPresentPrice_tendsto_s T f s hf hs0 hs1
    have hc := tendsto_of_asympEq_const (expect_constLUV_asympEq (P := liaHistory (paperDP T))
      (DP := paperDP T) hs (paperDP_hworld T))
    have := (hS.add (hpn.const_mul (s : ℝ))).sub hc
    refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
    ring

/-- **H3 is not implied by the rest** (lean-deference-2-025's audit item, machine-checked): on the
liar probe, every hypothesis of `scoped_value` other than `CondStableOn` holds — Total Trust, the
fold clause at the probe's own package, `Follows`, ramp quotes on the composite — while
`CondStableOn` fails and the conclusion fails. So H3 is a genuine scope condition, and
`scoped_value` is not a squeeze (AUDIT §3.3).
Source: lean-deference-2-025; mandate target 8 (docstring clause), Context (iv); audit r1
fidelity item 4
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem h3_not_implied_by_rest (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1) :
    TotalTrust (liaHistory (paperDP T)) (paperDP T) ((selfExpert T f).recast (paperDP T)) ∧
    ConcentrationFolds (paperDP T) (selfExpert T f) (probeMenu T f s hs0.le) (probeI T f s hs0.le) ∧
    Follows (paperDP T) (selfExpert T f) (probeMenu T f s hs0.le) (probeFollower T f s hs0.le) ∧
    RampQuotesAvailable (paperDP T) ((selfExpert T f).recast (paperDP T))
      (probeComposite T f s ⟨hs0.le, hs1.le⟩).D ∧
    ¬ CondStableOn (probeMenu T f s hs0.le) (probePackage T f s ⟨hs0.le, hs1.le⟩) ∧
    ¬ ((fun n => (probeFollower T f s hs0.le n).expect (liaHistory (paperDP T)) n) ≳ₙ
        (fun n => ((probeMenu T f s hs0.le).O 1 n).expect (liaHistory (paperDP T)) n)) := by
  have hs : 0 ≤ s ∧ s ≤ 1 := ⟨hs0.le, hs1.le⟩
  refine ⟨selfTotalTrust T f hf.injective,
    concentrationFolds_self T f hf (probeMenu T f s hs.1) (probePackage T f s hs),
    probeFollower_follows T f s hs,
    paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective
      (probeComposite T f s hs).codes ((probeComposite T f s hs).valued
        (follows_valued (probeMenu_valued T f s hs) (probeFollower_follows T f s hs))
        (probeMenu_valued T f s hs 1)),
    condStableOn_probe_refuted T f s hf hs0 hs1,
    probe_value_instance_refuted T f s hf hs0 hs1⟩

/-- **`scoped_value` on the probe with every binder but H3 discharged**: conditional-stability
alone would give the conclusion at `i = 1`. (The antecedent is false — `condStableOn_probe_refuted`
— so this is a statement about the theorem's binders, not about the probe.)
Source: audit r1 fidelity item 4
Kind: L
Fidelity: exact
Hyps: (a); `hf`; `h3` (false on the probe) -/
theorem scoped_value_probe_of_h3 (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s) (hs1 : s < 1)
    (h3 : CondStableOn (probeMenu T f s hs0.le) (probePackage T f s ⟨hs0.le, hs1.le⟩)) :
    (fun n => (probeFollower T f s hs0.le n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => ((probeMenu T f s hs0.le).O 1 n).expect (liaHistory (paperDP T)) n) := by
  have hs : 0 ≤ s ∧ s ≤ 1 := ⟨hs0.le, hs1.le⟩
  exact scoped_value (DPE := paperDP T) (DPH := paperDP T) (fun _ hv => hv) hf
    (probeMenu_valued T f s hs) (probePackage T f s hs)
    (concentrationFolds_self T f hf (probeMenu T f s hs.1) (probePackage T f s hs)) h3
    (probeFollower_codes T f s hs.1) (probeFollower_follows T f s hs) 1 (probeComposite T f s hs)
    (selfTotalTrust T f hf.injective)
    (paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective
      (probeComposite T f s hs).codes ((probeComposite T f s hs).valued
        (follows_valued (probeMenu_valued T f s hs) (probeFollower_follows T f s hs))
        (probeMenu_valued T f s hs 1)))
    (paperDP_hworld T) (paperDP_hworld T)

/-- **H3 fails on the probe, by modus tollens through the scoped theorem** — an independent
re-derivation of `condStableOn_probe_refuted` (whose proof computes the deficit `−s(1−s)` directly):
the conclusion fails (`probe_value_instance_refuted`), every other hypothesis holds, so H3 cannot.
Source: audit r1 fidelity item 4 (consistency check of the two routes)
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStableOn_probe_refuted' (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) :
    ¬ CondStableOn (probeMenu T f s hs0.le) (probePackage T f s ⟨hs0.le, hs1.le⟩) :=
  fun h3 => probe_value_instance_refuted T f s hf hs0 hs1 (scoped_value_probe_of_h3 T f s hf hs0 hs1 h3)

/-- Instance line at `𝗣𝗔`, `succDeferral`, `s = ½`. -/
example : ¬ CondStableOn (probeMenu 𝗣𝗔 succDeferral (1 / 2) (by norm_num))
    (probePackage 𝗣𝗔 succDeferral (1 / 2) ⟨by norm_num, by norm_num⟩) :=
  condStableOn_probe_refuted' 𝗣𝗔 succDeferral (1 / 2)
    Cleanroom.Found.LiQuoteLane.succDeferral_strict (by norm_num) (by norm_num)

/-- **H3 fails on the probe menu for every selection package of the self-expert** — through the
package-independence of `CondStableOn` (`condStableOn_iff_selfEndorseGE_instance` with
`concentrates_self`) and the refuted instance `selfEndorseGE_instance_refuted`. Makes
`h3_not_implied_by_rest` a statement about the menu, not about `probePackage`.
Source: audit r2 fidelity N4; mandate target 4c
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStableOn_probe_refuted_any_package (hf : StrictlyIncreasingDeferral f) (hs0 : 0 < s)
    (hs1 : s < 1) {I Q : Fin 2 → ℕ → LUV}
    (pkg : SelectionPackage (paperDP T) (selfExpert T f) (probeMenu T f s hs0.le) I Q) :
    ¬ CondStableOn (probeMenu T f s hs0.le) pkg :=
  fun h => selfEndorseGE_instance_refuted T f s hf hs0 hs1
    ((condStableOn_iff_selfEndorseGE_instance hf (probeMenu_valued T f s ⟨hs0.le, hs1.le⟩) pkg
      (concentrates_self T f hf _ pkg) (probeFollower_codes T f s hs0.le)
      (probeFollower_follows T f s ⟨hs0.le, hs1.le⟩) (paperDP_hworld T)).1 h)

end

end Cleanroom.Deference.DefArgmaxValue
