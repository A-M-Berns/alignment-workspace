import Cleanroom.Udt.UdtPolicyCalc.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Opaque Newcomb: CDT ≠ UDT, re-founded (T8)

Models exactly `EDTvsUDT.lean`'s setup: one observation, `BoxAct = {one, two}`,
`Pred = {oneBoxer, twoBoxer}`, `World = Pred × BoxAct`, `utility (p, a) = [a = two]·1000 +
[p = oneBoxer]·10⁶`, a perfect predictor (`predictorAccurate`) and `consistent`. Unlike the
source, the policy utility is **derived**: `consistent_unique` shows each policy has exactly
one consistent world and `policyUtility` is that world's utility (`policyUtility_spec`); the
source hand-wrote `udtUtility` as a table and never used `consistent`/`predictorAccurate`
(finding, local error). No `native_decide` (the source's four uses fail this run's gate).

Also `edt_oneBoxes_opaque`: the EDT rule (condition on the action as evidence, prior over the
agent's own policy) one-boxes in this model — the corrected three-way table of [[notation]] §3.3;
the genuine EDT ≠ UDT separation needs transparent Newcomb (`TransparentNewcomb.lean`).

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

/-- The two box-taking actions: take only the big box (`one`) or both (`two`).
Source: `lean/UDT/EDTvsUDT.lean:44` (udt-rep-006)
Kind: D
Fidelity: exact
Hyps: n/a -/
inductive BoxAct
  | one
  | two
  deriving DecidableEq, Fintype

/-- Supporting lemma `BoxAct.univ_eq` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem BoxAct.univ_eq : (Finset.univ : Finset BoxAct) = {BoxAct.one, BoxAct.two} := by
  ext a
  cases a <;> simp

/-- Supporting lemma `BoxAct.sum_eq` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem BoxAct.sum_eq {M : Type} [AddCommMonoid M] (g : BoxAct → M) :
    ∑ a, g a = g BoxAct.one + g BoxAct.two := by
  rw [BoxAct.univ_eq, Finset.sum_pair (by decide)]

namespace Opaque

/-- The predictor's two verdicts.
Source: `lean/UDT/EDTvsUDT.lean:49` (udt-rep-006)
Kind: D
Fidelity: exact
Hyps: n/a -/
inductive Pred
  | oneBoxer
  | twoBoxer
  deriving DecidableEq, Fintype

/-- A world: the prediction and the agent's action.
Source: `lean/UDT/EDTvsUDT.lean:58` (udt-rep-006)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev World := Pred × BoxAct

/-- The perfect predictor's verdict on an action.
Source: `lean/UDT/EDTvsUDT.lean:70` (udt-rep-006)
Kind: D
Fidelity: exact
Hyps: n/a -/
def predict : BoxAct → Pred
  | .one => .oneBoxer
  | .two => .twoBoxer

/-- The payoff: the transparent box's `1000` if both are taken, plus `10⁶` if the predictor
predicted one-boxing.
Source: `lean/UDT/EDTvsUDT.lean:87` (udt-rep-006)
Kind: D
Fidelity: exact (`ℝ`-valued instead of `Int`)
Hyps: n/a -/
def utility (w : World) : ℝ :=
  (if w.2 = BoxAct.two then 1000 else 0) + (if w.1 = Pred.oneBoxer then 1000000 else 0)

/-- The predictor is accurate for `π` in `w`: the prediction is `predict (π ())`.
Source: `lean/UDT/EDTvsUDT.lean:70` (udt-rep-006)
Kind: D
Fidelity: exact
Hyps: n/a -/
def predictorAccurate (π : Policy Unit BoxAct) (w : World) : Prop := w.1 = predict (π ())

/-- `w` is consistent with `π`: the agent follows `π` and the predictor predicted it.
Source: `lean/UDT/EDTvsUDT.lean:76` (udt-rep-006)
Kind: D
Fidelity: exact
Hyps: n/a -/
def consistent (π : Policy Unit BoxAct) (w : World) : Prop :=
  w.2 = π () ∧ predictorAccurate π w

/-- The unique world consistent with `π`.
Source: mandate T8 ("derive the policy utility")
Kind: D
Fidelity: n/a
Hyps: n/a -/
def consistentWorld (π : Policy Unit BoxAct) : World := (predict (π ()), π ())

/-- **T8, derivation step.** Every policy has exactly one consistent world.
Source: mandate T8 (udt-rep-006: the source defines `consistent` and never uses it)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem consistent_unique (π : Policy Unit BoxAct) : ∃! w, consistent π w :=
  ⟨consistentWorld π, ⟨rfl, rfl⟩, fun w ⟨h1, h2⟩ => Prod.ext h2 h1⟩

/-- Supporting lemma `consistentWorld_spec` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem consistentWorld_spec (π : Policy Unit BoxAct) :
    consistent π (consistentWorld π) ∧ ∀ w, consistent π w → w = consistentWorld π :=
  ⟨⟨rfl, rfl⟩, fun w ⟨h1, h2⟩ => Prod.ext h2 h1⟩

/-- **The policy utility, derived**: the utility of the unique consistent world.
Source: `lean/UDT/EDTvsUDT.lean:146` (`policyUtility`, hand-written there; udt-rep-006)
Kind: D
Fidelity: stronger: derived from `utility` and `consistent`, not stipulated
Hyps: n/a -/
def policyUtility (π : Policy Unit BoxAct) : ℝ := utility (consistentWorld π)

/-- The policy utility is the utility of any consistent world.
Source: mandate T8 (spec lemma)
Kind: L
Fidelity: exact
Hyps: none -/
theorem policyUtility_spec {π : Policy Unit BoxAct} {w : World} (hw : consistent π w) :
    utility w = policyUtility π := by
  rw [(consistentWorld_spec π).2 w hw]
  rfl

/-- CDT's evaluation: hold the prediction fixed, vary the action.
Source: `lean/UDT/EDTvsUDT.lean:108` (`cdtUtility`; udt-rep-006)
Kind: D
Fidelity: exact
Hyps: n/a -/
def cdtUtility (p : Pred) (a : BoxAct) : ℝ := utility (p, a)

/-- **T8(i).** With the prediction fixed, two-boxing dominates (CDT two-boxes).
Source: `lean/UDT/EDTvsUDT.lean:118` (`cdt_prefers_twoBox`; udt-rep-006)
Kind: P
Fidelity: exact (no `native_decide`)
Hyps: (a) none -/
theorem cdt_prefers_twoBox (p : Pred) : cdtUtility p BoxAct.one < cdtUtility p BoxAct.two := by
  cases p <;> simp [cdtUtility, utility]

/-- The constant one-boxing policy.
Source: `lean/UDT/EDTvsUDT.lean:154`
Kind: D
Fidelity: exact
Hyps: n/a -/
def oneBoxPolicy : Policy Unit BoxAct := fun _ => BoxAct.one

/-- The constant two-boxing policy.
Source: `lean/UDT/EDTvsUDT.lean:157`
Kind: D
Fidelity: exact
Hyps: n/a -/
def twoBoxPolicy : Policy Unit BoxAct := fun _ => BoxAct.two

/-- Supporting lemma `policyUtility_oneBox` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem policyUtility_oneBox : policyUtility oneBoxPolicy = 1000000 := by
  simp [policyUtility, consistentWorld, oneBoxPolicy, predict, utility]

/-- Supporting lemma `policyUtility_twoBox` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem policyUtility_twoBox : policyUtility twoBoxPolicy = 1000 := by
  simp [policyUtility, consistentWorld, twoBoxPolicy, predict, utility]

/-- With one observation there are exactly two policies.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem policy_eq_oneBox_or_twoBox (π : Policy Unit BoxAct) :
    π = oneBoxPolicy ∨ π = twoBoxPolicy := by
  cases h : π () with
  | one =>
    left
    funext u
    cases u
    exact h
  | two =>
    right
    funext u
    cases u
    exact h

/-- **T8(ii).** The derived policy utility prefers one-boxing: `10⁶ > 1000`.
Source: `lean/UDT/EDTvsUDT.lean:160` (`oneBox_policy_optimal`; udt-rep-006)
Kind: P
Fidelity: stronger: over the derived policy utility (the source's is a table)
Hyps: (a) none -/
theorem oneBox_beats_twoBox : policyUtility twoBoxPolicy < policyUtility oneBoxPolicy := by
  rw [policyUtility_oneBox, policyUtility_twoBox]
  norm_num

/-- **T8(ii).** One-boxing is the optimal policy for the derived policy utility.
Source: `lean/UDT/EDTvsUDT.lean:160` (udt-rep-006)
Kind: P
Fidelity: stronger: over the derived policy utility
Hyps: (a) none -/
theorem oneBox_optimal : IsOptimal policyUtility oneBoxPolicy := by
  intro π'
  rcases policy_eq_oneBox_or_twoBox π' with rfl | rfl
  · exact le_rfl
  · exact oneBox_beats_twoBox.le

/-- **T8, headline (udt-rep-006).** CDT ≠ UDT in opaque Newcomb: holding the prediction fixed,
two-boxing dominates for every prediction, while the policy optimum one-boxes. (This is the
source's `cdt_udt_differ`, relabelled from "EDT" on 2026-08-05; it is *not* an EDT ≠ UDT
separation — see `edt_oneBoxes_opaque` and `TransparentNewcomb.lean`.)
Source: `lean/UDT/EDTvsUDT.lean:190–197` (`cdt_udt_differ`; udt-rep-006); [[when-udt-edt-diverge]] (corrected header)
Kind: P
Fidelity: stronger: policy side derived; no `native_decide`
Hyps: (a) none -/
theorem cdt_udt_differ :
    (∀ p, cdtUtility p BoxAct.one < cdtUtility p BoxAct.two) ∧
      policyUtility twoBoxPolicy < policyUtility oneBoxPolicy ∧
        IsOptimal policyUtility oneBoxPolicy :=
  ⟨cdt_prefers_twoBox, oneBox_beats_twoBox, oneBox_optimal⟩

/-- **T8, non-vacuity.** The predictor's accuracy is load-bearing: the (inconsistent) world in
which a one-boxer is predicted a two-boxer scores `0 ≠ 10⁶`; the utility is not constant.
Source: mandate T8 (grade N+)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem predictor_matters :
    utility (Pred.twoBoxer, BoxAct.one) ≠ policyUtility oneBoxPolicy ∧
      ¬ consistent oneBoxPolicy (Pred.twoBoxer, BoxAct.one) := by
  refine ⟨?_, ?_⟩
  · rw [policyUtility_oneBox]
    simp [utility]
  · rintro ⟨_, h⟩
    simp [predictorAccurate, oneBoxPolicy, predict] at h

/-! ### EDT one-boxes here (udt-rep-2-031(b)) -/

/-- The EDT score of action `a` in opaque Newcomb: `E[utility | A = a]` under a prior `μ` over
the agent's own policy, the world being the consistent one (perfect predictor), with the
C&T junk value `-1`.
Source: [[notation]] §3.3 (EDT column); [[when-udt-edt-diverge]] corrected header (udt-rep-2-031(b))
Kind: D
Fidelity: exact
Hyps: n/a -/
def edtScore (μ : FinDist (Policy Unit BoxAct)) (a : BoxAct) : ℝ :=
  condExpJunk μ.w (fun π => utility (consistentWorld π))
    (event fun π => (consistentWorld π).2 = a) (-1)

/-- **EDT one-boxes in opaque Newcomb (udt-rep-2-031(b)).** With a prior giving both policies
positive weight, `E[U | A = one] = 10⁶ > E[U | A = two] = 1000`: conditioning on the action as
evidence recovers the prediction. The archived scorecard's "cross-situation dependence ⟹ UDT
beats EDT" is therefore not a theorem; the EDT/UDT separation needs transparent Newcomb.
Source: `archive/consolidated-working-doc.md` §when-udt-edt-diverge (retracted); [[notation]] §3.3 (udt-rep-2-031(b))
Kind: P
Fidelity: exact
Hyps: (a) full support of the prior on both policies (explicit, needed for both events to be non-null) -/
theorem edt_oneBoxes_opaque (μ : FinDist (Policy Unit BoxAct))
    (h1 : 0 < μ.w oneBoxPolicy) (h2 : 0 < μ.w twoBoxPolicy) :
    edtScore μ BoxAct.two < edtScore μ BoxAct.one := by
  have e1 : edtScore μ BoxAct.one = 1000000 := by
    apply condExpJunk_const_on
    · intro π hπ
      rw [mem_event] at hπ
      rcases policy_eq_oneBox_or_twoBox π with rfl | rfl
      · simp [consistentWorld, oneBoxPolicy, predict, utility]
      · simp [consistentWorld, twoBoxPolicy] at hπ
    · exact mass_pos_of_mem μ.nonneg (by simp [consistentWorld, oneBoxPolicy]) h1
  have e2 : edtScore μ BoxAct.two = 1000 := by
    apply condExpJunk_const_on
    · intro π hπ
      rw [mem_event] at hπ
      rcases policy_eq_oneBox_or_twoBox π with rfl | rfl
      · simp [consistentWorld, oneBoxPolicy] at hπ
      · simp [consistentWorld, twoBoxPolicy, predict, utility]
    · exact mass_pos_of_mem μ.nonneg (by simp [consistentWorld, twoBoxPolicy]) h2
  rw [e1, e2]
  norm_num

end Opaque

end

end Cleanroom.Udt.UdtPolicyCalc
