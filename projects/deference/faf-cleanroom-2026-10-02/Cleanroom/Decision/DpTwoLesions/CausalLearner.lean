import Cleanroom.Decision.DpTwoLesions.FixedPoints
import Cleanroom.Decision.DpTwoLesions.Lift

/-!
# T13 — Proposition 7, the policy value, and the §6 sentence refuted under the lab CDT

Proposition 7 is definitional: the untagged causal learner's estimate (Definition 4: the
empirical frequency of cancer among the episodes in which it performed the act) **is** the
evidential conditional, `rfl`; the tagged one likewise on the tagged tree. The lab CDT of the
exchange (`labCdtDo`: the population cancer rate `ργ₁ + (1−ρ)γ₀`, the `do`-law on this tree,
act- and label-independent) prefers smoking, and the policy value
`V(p) = α(ρδL + κp) − β·popRate` is affine with slope `ακ > 0` — so at the untagged
evidential fixed point `p = 0` (under (H)) the lab CDT's verdict is `V`-optimal and the
untagged evidential learner's abstention is not: the §6 sentence "on no construal does the
causal learner outperform the evidential learner" is refuted under the lab-CDT construal
(ATTRIBUTION-UNVETTED that the doc's "causal learner" could mean it; the exchange's proposal),
and survives for rendering (i) (Proposition 7). Coherence (Definition 22) and Theorem 1's
condition hold at the smoke label.
Serves [[dp-two-lesions-mandate]] T13 (dp-core-080, 092, 2-027).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace DlParams

variable (P : DlParams K)

/-! ## Proposition 7: the two learners compute the same numbers -/

/-- **The untagged causal learner's estimate** (Definition 4): the frequency of cancer among the
episodes in which the agent performed the act — forced and chosen alike, since it cannot tell
them apart — as a quotient of `ν` at the label.
Source: [[two-lesions-doc-2026-09-18]] §6 Definition 4 ("estimates the effect of an act on an
outcome by the empirical frequency of the outcome among the episodes in which it performed the
act")
Kind: D -/
def untaggedCausalEst (p : K) (a : Bool) : K := P.nuP p (evCancer ∩ evAct a) / P.nuP p (evAct a)

/-- The untagged evidential learner's conditional `P_p(cancer | act)`.
Source: [[two-lesions-doc-2026-09-18]] §3
Kind: D -/
def evidentialCond (p : K) (a : Bool) : K := P.nuP p (evCancer ∩ evAct a) / P.nuP p (evAct a)

/-- **Proposition 7, untagged**: the causal learner's estimate *is* the evidential conditional —
by definition (`rfl`); hence identical best-response maps, fixed points and trajectories.
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 7 ("compute identical conditionals from
identical records"); Corollary ("Propositions 1 through 5 hold verbatim of the untagged causal
learner")
Kind: D (definitional, as the mandate grades it: the content is that Definition 4 names the
same number)
Fidelity: exact -/
theorem prop7_untagged : P.untaggedCausalEst = P.evidentialCond := rfl

/-- `Δ` is the causal learner's difference too. Source: doc §6 Proposition 7. Kind: L -/
theorem Delta_eq_untaggedCausal (p : K) :
    P.Delta p = P.β * (P.untaggedCausalEst p true - P.untaggedCausalEst p false) := rfl

/-- **The tagged causal learner's estimate**: cancer among the agent's own (chosen) episodes
with the act, on the tagged tree.
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 7 proof ("The tagged causal learner
excludes the forced episodes")
Kind: D -/
def taggedCausalEst (p : K) (a : Bool) : K :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    nu (procBoolK p h.1 h.2) P.overwriteFull (evCancerF ∩ evActF a ∩ evChosen) /
      nu (procBoolK p h.1 h.2) P.overwriteFull (evActF a ∩ evChosen)
  else 0

/-- The tagged evidential learner's conditional `P_p(cancer | act, chosen)`.
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 6
Kind: D -/
def taggedEvidentialCond (p : K) (a : Bool) : K :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    nu (procBoolK p h.1 h.2) P.overwriteFull (evCancerF ∩ evActF a ∩ evChosen) /
      nu (procBoolK p h.1 h.2) P.overwriteFull (evActF a ∩ evChosen)
  else 0

/-- **Proposition 7, tagged**: `rfl` again.
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 7; Corollary ("Proposition 6 holds
verbatim of the tagged causal learner")
Kind: D
Fidelity: exact -/
theorem prop7_tagged : P.taggedCausalEst = P.taggedEvidentialCond := rfl

/-! ## The policy value -/

/-- `V` on `overwrite P` as a 24-term sum. Source: none: infrastructure. Kind: L -/
theorem overwrite_value (C : Proc Unit (fun _ => Bool) K) :
    value C P.overwrite =
      ∑ i : Fin 3, ∑ m' : Bool, ∑ j : Fin 2, ∑ k : Fin 2,
        leafLaw C P.overwrite ⟨i, m', j, k, ()⟩ * P.pay (actOf i m' j) (decide (k = 0)) := by
  unfold value
  rw [overwrite_sum]
  rfl

/-- **The policy value is affine in the label**: `V(p) = α(ρδL + κp) − β(ργ₁ + (1−ρ)γ₀)`,
from `value` on the overwrite tree; slope `ακ > 0`.
Source: dp-core-092 (the policy value); `dp-core-tree`'s `AlmostFair.value_interpolation` gives
the affinity abstractly, here it is computed
Kind: P
Fidelity: exact
Hyps: none -/
theorem VP_eq_affine (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.VP p = P.α * (P.ρ * P.δL + P.kappa * p) - P.β * P.popRate := by
  rw [P.VP_eq h0 h1, overwrite_value]
  simp only [overwrite_leafLaw, procBoolK_w]
  conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two, pay]
  unfold kappa popRate
  ring

/-- `V(1) − V(0) = ακ > 0`. Source: dp-core-092. Kind: P. Fidelity: exact. Hyps: none -/
theorem VP_one_sub_VP_zero : P.VP 1 - P.VP 0 = P.α * P.kappa ∧ 0 < P.α * P.kappa := by
  rw [P.VP_eq_affine 1 zero_le_one le_rfl, P.VP_eq_affine 0 le_rfl zero_le_one]
  exact ⟨by ring, mul_pos P.α_pos P.kappa_pos⟩

/-- `V` is monotone in the label on `[0, 1]`. Source: dp-core-092. Kind: L -/
theorem VP_mono {p q : K} (hp0 : 0 ≤ p) (hq1 : q ≤ 1) (hpq : p ≤ q) : P.VP p ≤ P.VP q := by
  rw [P.VP_eq_affine p hp0 (le_trans hpq hq1), P.VP_eq_affine q (le_trans hp0 hpq) hq1]
  nlinarith [mul_pos P.α_pos P.kappa_pos]

/-- Every one-point procedure on `Bool` is a label. Source: none: infrastructure. Kind: L -/
theorem proc_eq_procBoolK (C : Proc Unit (fun _ => Bool) K) :
    C = procBoolK ((C ()).w true) ((C ()).nonneg true) ((C ()).w_le_one true) := by
  funext d
  cases d
  ext b
  have hsum := (C ()).sum_one
  rw [Fintype.sum_bool] at hsum
  cases b
  · simp only [procBoolK_w, Bool.false_eq_true, if_false]; linarith
  · rfl

/-- **The smoke label is optimal** among all procedures on the overwrite tree
(`dp-local-opt`'s `IsOptimal`).
Source: dp-core-092; [[iv-design-draw-as-instrument]] §6 ("the disposition-level estimand is the
one that is right in every row")
Kind: P
Fidelity: exact
Hyps: none -/
theorem isOptimal_smoke :
    Cleanroom.Decision.DpLocalOpt.IsOptimal (procBoolK (1 : K) zero_le_one le_rfl) P.overwrite := by
  intro C'
  rw [proc_eq_procBoolK C', ← P.VP_eq, ← P.VP_eq]
  exact P.VP_mono ((C' ()).nonneg true) le_rfl ((C' ()).w_le_one true)

/-- **Coherence (Definition 22, mixed) at the smoke label**: every deviation at `d` is weakly
worse.
Source: [[decision-problems-v2]] Definition 22 (via `dp-local-opt`'s `CoherentAt`); dp-core-2-005
("`thm1At`/`CoherentAt` at `p = 1` hold and coincide")
Kind: P
Fidelity: exact
Hyps: none -/
theorem coherentAt_smoke :
    Cleanroom.Decision.DpLocalOpt.CoherentAt (procBoolK (1 : K) zero_le_one le_rfl) P.overwrite
      () := by
  intro m
  rw [proc_eq_procBoolK ((procBoolK (1 : K) zero_le_one le_rfl).deviate () m), ← P.VP_eq,
    ← P.VP_eq]
  exact P.VP_mono (FinDistr.nonneg _ _) le_rfl (FinDistr.w_le_one _ _)

/-- **Theorem 1's condition at the smoke label** (from coherence).
Source: [[decision-problems-v2]] §8 Theorem 1 (via `dp-local-opt`'s `thm1At_of_coherentAt`)
Kind: C
Fidelity: exact
Hyps: none -/
theorem thm1At_smoke :
    Cleanroom.Decision.DpLocalOpt.Thm1At (procBoolK (1 : K) zero_le_one le_rfl) P.overwrite () :=
  Cleanroom.Decision.DpLocalOpt.thm1At_of_coherentAt _ _ _ P.coherentAt_smoke

/-! ## The lab CDT and the §6 sentence -/

/-- **The lab CDT's `do`-law** (rendering (iv) of the direction note, the exchange's proposal):
the population cancer rate `P_p(cancer)` — act- and label-independent.
Source: [[two-lesions-exchange-2026-09-19]] line 63 ("CDT's `do(smoke) = ε_L`");
`defining-cdt-in-the-learning-setting.md` §3 (rendering (iv)); mandate §3.7. ATTRIBUTION-UNVETTED
that the doc's §6 "causal learner" may mean this object
Kind: D -/
def labCdtDo (p : K) : K := P.nuP p evCancer

/-- The lab CDT's `do`-law is the population rate, for every label and either act.
Source: [[two-lesions-exchange-2026-09-19]] line 63
Kind: P
Fidelity: exact
Hyps: none -/
theorem labCdtDo_eq (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : P.labCdtDo p = P.popRate := by
  unfold labCdtDo popRate
  exact nuP_cancer P p h0 h1

/-- The lab CDT's act values: `α − β·do` for smoking, `−β·do` for abstaining. Source: mandate
§3.7. Kind: D -/
def labCdtValue (p : K) (a : Bool) : K := (if a then P.α else 0) - P.β * P.labCdtDo p

/-- **The lab CDT smokes at every label**: `labCdtValue p true > labCdtValue p false`.
Source: [[two-lesions-exchange-2026-09-19]] line 55 ("it smokes in the double lesion")
Kind: P
Fidelity: exact
Hyps: none -/
theorem labCdt_smokes (p : K) : P.labCdtValue p false < P.labCdtValue p true := by
  unfold labCdtValue; simp; exact P.α_pos

/-- **The §6 sentence refuted under the lab-CDT construal** (the three-part row, mandate rule 3).
Source sentence (doc §6): "On no construal does the causal learner outperform the evidential
learner in the calibrated problem, except by being handed in advance what the calibration
requirement forbids it to be handed." Reading: "causal learner" = the lab CDT (ATTRIBUTION-
UNVETTED; the exchange's proposal, line 63). Refuted statement: under (H), at the untagged
evidential learner's fixed point `p = 0` (`β(0) = {0}`: it abstains), the lab CDT's verdict is
smoke, and the smoke label is strictly better in policy value (`V(1) − V(0) = ακ > 0`) and
optimal among all procedures — the lab CDT outperforms. Survivor: for rendering (i)
(Proposition 7) the sentence holds, the two learners being the same learner.
Source: [[two-lesions-doc-2026-09-18]] §6 (the sentence); [[two-lesions-exchange-2026-09-19]]
line 63 ("restating §6's conclusion"); `defining-cdt-in-the-learning-setting.md` line 94
(dp-core-2-027)
Kind: P
Fidelity: exact for the lab-CDT reading; reading-dependent (see the row)
Hyps: (a) (H) -/
theorem sect6_refuted_labCdt (hH : P.HypH) :
    P.IsFixedPt 0 ∧ P.bestResp 0 = {0} ∧
    (∀ p : K, P.labCdtValue p false < P.labCdtValue p true) ∧
    P.VP 0 < P.VP 1 ∧
    Cleanroom.Decision.DpLocalOpt.IsOptimal (procBoolK (1 : K) zero_le_one le_rfl) P.overwrite := by
  obtain ⟨h1, h2⟩ := P.VP_one_sub_VP_zero
  exact ⟨P.prop1 hH, P.prop1_bestResp hH, P.labCdt_smokes, by linarith, P.isOptimal_smoke⟩

end DlParams

end Cleanroom.Decision.DpTwoLesions
