import Cleanroom.Corrigibility.CorrLegitModif.Y1Model

/-!
# corr-legit-modif — T9: capability growth versus oversight quality

[[carey-everitt]] 2.4c l. 127: "As the agent becomes more capable than the overseers on the
domain where it might be pressed, the overseers' `α` *rises* (they misjudge a good plan more
often) while `ε` falls. The inequality then fails for every `h/c` short of infinity. We have no
theorem for this." The claim is ill-posed as stated (Known issues 5): `α = P(Pr | R)` is defined
relative to the world `ω`, not relative to the agent. The model the conjecture needs: `ω ∈ {R, W}`
with prior `ε`; the overseers' signal `h` with rates `(α_H, β_H)`; the agent's private signal `y`
with rates `(α_A, β_A)` — `P(y = w | R) = α_A`, `P(y = w | W) = β_A` — conditionally independent
given `ω`; the press is `[h says W]`.

Two readings. (a) **Refuted**: `rates_independent_of_agent` — `P(Pr | R) = α_H` and
`P(Pr | W) = β_H` whatever the agent's rates; "`α` rises with the agent's advantage" is false
under conditional independence. (b) **The surviving neighbour**: in the binding cell `y = r` the
posterior `P(W | Pr, y = r)` has masses `ε β_H (1 − β_A)` against `(1 − ε) α_H (1 − α_A)`; it is
antitone as the agent's signal sharpens (`bindW_antitone`) and for every finite `h/c` the
compliance condition `P(W | Pr, y = r) ≥ c/(c + h)` fails beyond a capability level
(`fails_beyond_level`): the claim survives as a statement about `ε` in the agent's cell, not
about `α` — the converse of common-prior deference (corr-wf13-008;
`CommonPrior.commonPriorRule_pressExpectOn_nonpos` is the nested positive side, cited). Witness
`capability_instance`: `ε = 1/10`, `(α_H, β_H) = (1/10, 9/10)`, `(c, h) = (1, 4)`; agent rates
`(3/10, 7/10)` comply (posterior `3/10 ≥ 1/5`), `(1/10, 9/10)` do not (`1/10 < 1/5`) — the
mandate's instance `(1/10, 9/10) → (1/100, 99/100)` has both sides below the threshold (findings).
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset

noncomputable section

/-- The joint on `(ω, h, y)` (`true` = `W`, press, `σ_A = w`): `P(ω) · P(h | ω) · P(y | ω)`, the
two signals conditionally independent given the world.
Source: [[carey-everitt]] 2.4c l. 127 (the model the conjecture needs); mandate T9
Kind: D
Fidelity: exact -/
def capJoint (ε αH βH αA βA : ℝ) : Bool × Bool × Bool → ℝ := fun p =>
  (if p.1 then ε else 1 - ε) *
    (if p.1 then (if p.2.1 then βH else 1 - βH) else (if p.2.1 then αH else 1 - αH)) *
    (if p.1 then (if p.2.2 then βA else 1 - βA) else (if p.2.2 then αA else 1 - αA))

/-- **`rates_independent_of_agent`** (the refuted reading): the press rates `P(Pr ∧ R) = (1 − ε) α_H`
and `P(Pr ∧ W) = ε β_H` do not depend on the agent's rates `(α_A, β_A)`.
Source: [[carey-everitt]] 2.4c l. 127 ("the overseers' `α` *rises*"); corr-wf13-2-090
Kind: T (refutation of the reading, by computation)
Fidelity: exact
Hyps: (a) none -/
theorem rates_independent_of_agent (ε αH βH αA βA : ℝ) :
    ∑ y, capJoint ε αH βH αA βA (false, true, y) = (1 - ε) * αH ∧
    ∑ y, capJoint ε αH βH αA βA (true, true, y) = ε * βH := by
  constructor <;> simp [capJoint, Fintype.sum_bool] <;> ring

/-- The binding cell's `W`-mass `P(W ∧ Pr ∧ y = r) = ε β_H (1 − β_A)`.
Source: mandate T9(b)
Kind: D
Fidelity: exact -/
def bindW (ε βH βA : ℝ) : ℝ := ε * βH * (1 - βA)

/-- The binding cell's `R`-mass `P(R ∧ Pr ∧ y = r) = (1 − ε) α_H (1 − α_A)`.
Source: mandate T9(b)
Kind: D
Fidelity: exact -/
def bindR (ε αH αA : ℝ) : ℝ := (1 - ε) * αH * (1 - αA)

/-- The binding-cell masses are the joint's.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bind_eq_joint (ε αH βH αA βA : ℝ) :
    capJoint ε αH βH αA βA (true, true, false) = bindW ε βH βA ∧
    capJoint ε αH βH αA βA (false, true, false) = bindR ε αH αA := by
  constructor <;> simp [capJoint, bindW, bindR]

/-- **Compliance in product form**: the posterior `numW/(numW + numR)` is at least `c/(c + h)` iff
`c · numR ≤ h · numW`.
Source: [[corr-three-step]] `complianceThreshold`; position statement §2.13(a)
Kind: D
Fidelity: exact (product form of `P(W | Pr, y = r) ≥ c/(c + h)`) -/
def Complies (c h numW numR : ℝ) : Prop := c * numR ≤ h * numW

/-- The product form is the ratio form under positivity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem complies_iff_posterior {c h numW numR : ℝ} (hc : 0 < c) (hh : 0 < h) (hW : 0 ≤ numW)
    (hR : 0 ≤ numR) (hpos : 0 < numW + numR) :
    Complies c h numW numR ↔ c / (c + h) ≤ numW / (numW + numR) := by
  unfold Complies
  rw [div_le_div_iff₀ (by linarith) hpos]
  constructor <;> intro h' <;> nlinarith

/-- **The binding-cell `W`-mass is antitone in the agent's true-positive rate**: sharpening the
agent's signal (`β_A ↑`) lowers `P(W ∧ Pr ∧ y = r)`.
Source: mandate T9(b) ("antitone as the agent's signal sharpens")
Kind: L
Fidelity: exact
Hyps: (a) `0 ≤ ε β_H` -/
theorem bindW_antitone {ε βH βA βA' : ℝ} (h0 : 0 ≤ ε * βH) (h : βA ≤ βA') :
    bindW ε βH βA' ≤ bindW ε βH βA := by
  unfold bindW
  nlinarith

/-- **`fails_beyond_level`** (the surviving neighbour): for every stake ratio, every informative
overseer (`α_H > 0`) and every agent false-positive rate `α_A < 1`, there is a level `b < 1` such
that for every true-positive rate `β_A > b` the compliance condition fails in the binding cell —
`P(W | Pr, y = r) < c/(c + h)`. The claim survives as a statement about the agent's posterior in
its own cell, not about `α`.
Source: [[carey-everitt]] 2.4c l. 127 ("fails for every `h/c` short of infinity"); corr-wf13-2-090
Kind: P
Fidelity: variant: the reading on the agent's cell (the `α`-reading is refuted)
Hyps: (a) `0 ≤ ε < 1`, `0 < α_H`, `0 ≤ β_H`, `α_A < 1`, `0 < c`, `0 < h` -/
theorem fails_beyond_level {ε αH βH αA c h : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hαH : 0 < αH)
    (hβH : 0 ≤ βH) (hαA : αA < 1) (hc : 0 < c) (hh : 0 < h) :
    ∃ b, b < 1 ∧ ∀ βA, b < βA → ¬ Complies c h (bindW ε βH βA) (bindR ε αH αA) := by
  set δ := c * bindR ε αH αA with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]; unfold bindR
    exact mul_pos hc (mul_pos (mul_pos (by linarith) hαH) (by linarith))
  set K := h * (ε * βH) with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hh.le (mul_nonneg hε0 hβH)
  have hKδ : 0 < K + δ := by linarith
  refine ⟨1 - δ / (K + δ), ?_, ?_⟩
  · have : 0 < δ / (K + δ) := div_pos hδ hKδ
    linarith
  · intro βA hb
    unfold Complies
    push_neg
    have h1 : 1 - βA < δ / (K + δ) := by linarith
    have h2 : K * (1 - βA) ≤ K * (δ / (K + δ)) := mul_le_mul_of_nonneg_left h1.le hK0
    have h3 : K * (δ / (K + δ)) < δ := by
      rw [← mul_div_assoc, div_lt_iff₀ hKδ]
      nlinarith
    calc h * bindW ε βH βA = K * (1 - βA) := by unfold bindW; rw [hKdef]; ring
      _ ≤ K * (δ / (K + δ)) := h2
      _ < δ := h3
      _ = c * bindR ε αH αA := hδdef

/-- **The instance** (`capability_instance`): `ε = 1/10`, `(α_H, β_H) = (1/10, 9/10)`,
`(c, h) = (1, 4)`. The press rates are `(1/10, 9/10)` for every agent; with agent rates
`(3/10, 7/10)` the binding-cell posterior is `3/10 ≥ 1/5` (complies), with `(1/10, 9/10)` it is
`1/10 < 1/5` (does not): the level is crossed between them.
Source: mandate T9 (witness, corrected: the mandate's `(1/10, 9/10) → (1/100, 99/100)` are both
below `1/5`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem capability_instance :
    (∀ αA βA, ∑ y, capJoint (1 / 10) (1 / 10) (9 / 10) αA βA (false, true, y) = 9 / 100 ∧
      ∑ y, capJoint (1 / 10) (1 / 10) (9 / 10) αA βA (true, true, y) = 9 / 100) ∧
    Complies 1 4 (bindW (1 / 10) (9 / 10) (7 / 10)) (bindR (1 / 10) (1 / 10) (3 / 10)) ∧
    ¬ Complies 1 4 (bindW (1 / 10) (9 / 10) (9 / 10)) (bindR (1 / 10) (1 / 10) (1 / 10)) ∧
    bindW (1 / 10) (9 / 10) (7 / 10) / (bindW (1 / 10) (9 / 10) (7 / 10) + bindR (1 / 10) (1 / 10) (3 / 10))
      = 3 / 10 ∧
    bindW (1 / 10) (9 / 10) (9 / 10) / (bindW (1 / 10) (9 / 10) (9 / 10) + bindR (1 / 10) (1 / 10) (1 / 10))
      = 1 / 10 := by
  refine ⟨fun αA βA => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := rates_independent_of_agent (1 / 10) (1 / 10) (9 / 10) αA βA
    rw [h1, h2]; norm_num
  all_goals norm_num [Complies, bindW, bindR]

end

end Cleanroom.Corrigibility.CorrLegitModif
