import Cleanroom.Trust.LegitLiRegister.Idle
import Cleanroom.Trust.LegitLiRegister.Diagonal
import Cleanroom.Deference.DefFrozenSibling.Tracking

/-!
# `legit-li-register` · Corrigible: corrigibility = faithfulness + legitimacy on the self-family;
governance blindness (Target 11)

[[legitimacy-theory-v1]] §6.1 (root-fa-044): "`A` is corrigible to `H` iff (i) `A` is faithful on
`Φ_self` (T1) and (ii) `A` is legitimate on `Φ_self` (`d_n → 0` there)." §6.2's design corollary
("governance blindness"): if the governance decision reads the current quote, `Φ_self` contains
self-fulfilling instances and no guarantee survives.

Over FAF: the governance family `Φ_self` is a sub-fragment of the contract enumeration, rendered by
a ruler `t` (D3) — **disclosed**: nothing in the carrier says what a governance question is; the
definition is on a ruler. `CorrigibleOn S t` is a definition (D). On `G ∩ Φ_self` it holds under
T1's `hz` (faithfulness) and Target 2's `H`-side certificate (legitimacy) — `corrigibleOn_of_timely`
(L corollary). **Governance blindness** is Target 4 restricted: with the governance contract the
diagonal `gDiag`, legitimacy fails by `≥ ½` along the whole family
(`governance_gDiag_defect_not_vanishing`, L corollary over `FrozenSystemL`); the "design
corollary" text (seal the review board from the model's brief) is INTERPRETATION (findings).
§6.3 non-modification: "exploitable incentive" is undefined — no statement (findings; the nearest
finite shape is `LegitFiniteDefect.Corrigibility.complyAdv_*`, cited there). root-deference-058
(no action model) and 060 (a)–(d): recorded OPENs in findings with their nearest well-posed shapes.
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefFrozenSibling Cleanroom.Li.LiDiagonal
open Filter Topology

/-- **Corrigible on a family**: faithful (`a ≈ Y` along the family — T1's conclusion restricted)
and legitimate (`d_n → 0` along the family) on the e.c. sub-fragment `{n | t n = 0}` of the
contract enumeration that renders the governance questions `Φ_self`. A definition on a ruler;
which contracts are governance questions is data, not derived.
Source: [[legitimacy-theory-v1]] §6.1 (root-fa-044); mandate Target 11
Kind: D
Fidelity: variant: `Φ_self` as an e.c. sub-fragment of the contract enumeration (a ruler); faithfulness as `AgreeAlong` of the quote and the verdict
Hyps: n/a -/
def CorrigibleOn (S : FrozenSystem) (t : ℕ → ℕ) : Prop :=
  AgreeAlong t (fun n => (S.a n : ℝ)) (fun n => (S.Y n : ℝ)) ∧ LegitimateAlong S t

/-- **Corrigibility holds on `G ∩ Φ_self`** under T1's `hz` (faithfulness, everywhere) and the
`H`-side polarity certificate (legitimacy on the timely fragment): the composition of `tracking`
and `legitimateAlong_onG_ofPattern`. Nothing is forced beyond what the dependency forces. Two-way:
`partial: over timely_cofinite_const` and `hz` at that pair.
Source: [[legitimacy-theory-v1]] §6.1; mandate Target 11 (`corrigibleOn_of_timely`)
Kind: L (corollary)
Fidelity: as `tracking` and `defect_agreeAlong_zero_onG_ofPattern`
Hyps: (c) `hz` (row 6); (c) `hpat₁`, `hpat₀` (row 4); all else (a) -/
theorem corrigibleOn_of_timely (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ}
    (hG : ∀ n, t n = 0 → Timely S ε n) (hinj : Function.Injective S.F.f)
    (hpat₁ : MachineSentenceCodes (horizonFamilyPos S t))
    (hpat₀ : MachineSentenceCodes (horizonFamilyNeg S t))
    (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    CorrigibleOn S t :=
  ⟨AgreeAlong.of_asympEq (tracking S zhat hz hlim),
    legitimateAlong_onG_ofPattern S ε hε hG hinj hpat₁ hpat₀⟩

/-- **Governance blindness, the negative half**: if the governance contract reads the current
quote (`contract n = gDiag n`), legitimacy fails along the whole family — the defect is not
eventually below `¼`, so `AgreeAlong 0 (defect) 0` is false. Target 4 restricted to the trivial
ruler; over the relaxed carrier, with Claim 1's hypotheses.
Source: [[legitimacy-theory-v1]] §6.2 (root-fa-044, "self-fulfilling instances … no guarantee survives"); mandate Target 11
Kind: L (corollary of `defect_ge_half_diagonal`)
Fidelity: exact (the failure is quantitative: `≥ ½ − δ`)
Hyps: as `defect_ge_half_diagonal`: (c) `hz`, (c) `hpat₁`, `hpat₀`; all else (a) -/
theorem governance_gDiag_defect_not_vanishing (S : FrozenSystemL)
    (hc : ∀ n, S.contract n = gDiag n) (hinj : Function.Injective S.F.f)
    (hpat₁ : MachineSentenceCodes (diagFamilyLe S))
    (hpat₀ : MachineSentenceCodes (diagFamilyGt S))
    (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    ¬ AgreeAlong (fun _ => 0) S.defect (fun _ => 0) := by
  intro h
  have h1 := defect_ge_half_diagonal S hc hinj hpat₁ hpat₀ zhat hz hlim (1 / 4) (by norm_num)
  have h2 := h (1 / 8) (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have hd : 0 ≤ S.defect n := abs_nonneg _
  have := hn2 rfl
  rw [sub_zero, abs_of_nonneg hd] at this
  linarith

end Cleanroom.Trust.LegitLiRegister
