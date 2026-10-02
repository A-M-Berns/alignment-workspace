import Cleanroom.Corrigibility.CorrLandscape.Crossing

/-!
# `corr-landscape` — `ActBased`: S6, the act-based dual, the floor, and drills (T5, load-bearing 5)

* (a) **the authenticity inequality** `κ^AD`: `P(A ∣ Pr) = p^A/(p^A + γ) ≥ c''/(1 + c'')` in product form
  `c''(p^A + γ) ≤ p^A (1 + c'')`, which is `c'' γ ≤ p^A` (`authIneq`, `authIneq_iff_ratio`, `authIneq_iff`).
* (b) **the consistent parameterization** `p^A_t = ε_t β + (1 − ε_t) α` (A6.2): `p^A_t → α`, antitone for
  antitone `ε_t` with `α ≤ β`, bounded below by `α`; `P(A ∣ Pr_t)` tends to the floor `α/(α + γ)`
  (`= 5/7` at the worked values; `P(A ∣ Pr_0) = 61/65`); **compliance never fails iff the floor
  satisfies the inequality**, i.e. fails in the limit iff `γ > α(1 − thr)/thr = α/c''` (`= 1/20` at the
  worked values; `γ = 1/50` passes).
* (c) **refutation row** — `approval.md` S6 l. 69: "In the worked trajectory the act-based agent without
  drills fails at `t = 10`". Under the develop's asserted decay `p^A_t = (3/10)(3/4)^t` the least failing
  index *is* `10` (`decay_fails_least`, N−: the decay is unmotivated, A6.2); under the model's own press
  generation (b) it never fails (`consistent_never_fails`). Surviving neighbour: (b).
* (d) **drills** `α ↦ α + δ(1 − α)`, `β ↦ β + δ(1 − β)`: the VL crossing moves from `17` to `14, 13, 11`
  at `δ = 1/20, 1/10, 1/5`, each as a least index; drills raise `ε*` in general (`epsStar_drill_le`),
  and the least crossing index is antitone in the threshold (`leastCrossing_antitone`).
* (e) **S14's opposite scaling** as the composition of T4(b) and T5(b) on the worked trajectory
  (`opposite_scaling`).
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory
open Corruption (oddsIneq)
open Filter Topology

set_option linter.unusedSectionVars false

namespace ActBased

open Margin Crossing

/-! ## (a) the authenticity inequality -/

/-- **`κ^AD`, the authenticity inequality in product form**: `c''(p^A + γ) ≤ p^A (1 + c'')`
(the ratio form `p^A/(p^A + γ) ≥ c''/(1 + c'')` without its junk points). The source is inconsistent
about the boundary: S6 writes `≥`, while D7's `κ^AD_t := [E[R(stop) − R(cont) ∣ Pr] > 0]` and P4's
`P(A ∣ Pr) > c''/(1 + c'')` are strict. This file follows S6 (`≤`); no worked cell sits on the boundary
(`5/7` vs `1/2`, `1/20` vs `1/50`), so no cell changes under the strict reading (audit r1, N5/N10).
Source: [[corr-wf14-inventory]] 118 / approval-final.md S6, P4
Kind: D
Fidelity: exact (product form; S6's non-strict boundary, where D7/P4 are strict) -/
def authIneq (pA γ c'' : ℝ) : Prop := c'' * (pA + γ) ≤ pA * (1 + c'')

/-- The ratio form, where defined.
Source: [[corr-wf14-inventory]] 118 / approval-final.md P4 ("`P(A ∣ Pr) > c''/(1 + c'')`")
Kind: L
Fidelity: exact -/
theorem authIneq_iff_ratio (pA γ c'' : ℝ) (h1 : 0 < pA + γ) (h2 : 0 < 1 + c'') :
    authIneq pA γ c'' ↔ c'' / (1 + c'') ≤ pA / (pA + γ) := by
  rw [authIneq, div_le_div_iff₀ h2 h1]

/-- **P4's one line**: the inequality is `c'' γ ≤ p^A` — the shape of `κ^VL` with `ε ↦ p^A`, `α ↦ γ`,
`h/c ↦ 1/c''`.
Source: [[corr-wf14-inventory]] 118 / approval-final.md S6 ("the shape of `κ^VL` with …")
Kind: L
Fidelity: exact -/
theorem authIneq_iff (pA γ c'' : ℝ) : authIneq pA γ c'' ↔ c'' * γ ≤ pA := by
  unfold authIneq; constructor <;> intro H <;> nlinarith

/-! ## (b) the consistent parameterization and the floor -/

/-- **The consistent authentic-press rate** `p^A = ε β + (1 − ε) α`: correct presses at `εβ` plus
authentic mistaken ones at `(1 − ε)α` (A6.2).
Source: [[corr-wf14-inventory]] 118; [[corr-wf14-2-inventory]] 2-049 / approval-final.md P4
Kind: D
Fidelity: exact -/
def pA (ε α β : ℝ) : ℝ := ε * β + (1 - ε) * α

/-- `p^A ≥ α` for `0 ≤ ε`, `α ≤ β`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pA_ge (ε α β : ℝ) (hε : 0 ≤ ε) (hαβ : α ≤ β) : α ≤ pA ε α β := by
  unfold pA; nlinarith

/-- **`p^A_t → α`** along any `ε_t → 0`.
Source: [[corr-wf14-inventory]] 118 / approval-final.md P4 ("`p^A_t → α`")
Kind: L
Fidelity: exact -/
theorem pA_tendsto (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (α β : ℝ) :
    Tendsto (fun t => pA (ε t) α β) atTop (𝓝 α) := by
  have h1 : Tendsto (fun t => α + ε t * (β - α)) atTop (𝓝 (α + 0 * (β - α))) :=
    tendsto_const_nhds.add (hε.mul_const _)
  rw [zero_mul, add_zero] at h1
  refine h1.congr fun t => ?_
  unfold pA; ring

/-- **`p^A_t` is antitone** for antitone `ε_t` and `α ≤ β`.
Source: [[corr-wf14-inventory]] 118 / approval-final.md P4
Kind: L
Fidelity: exact -/
theorem pA_antitone (ε : ℕ → ℝ) (hanti : Antitone ε) (α β : ℝ) (hαβ : α ≤ β) :
    Antitone (fun t => pA (ε t) α β) := by
  intro s t hst
  have := hanti hst
  unfold pA; nlinarith

/-- **The authenticity posterior** `P(A ∣ Pr) = p^A/(p^A + γ)` as a named real (junk at `p^A + γ = 0`;
every use carries positivity).
Source: [[corr-wf14-inventory]] 118 / approval-final.md P4
Kind: D
Fidelity: exact under `0 < p^A + γ` -/
noncomputable def authPost (pA γ : ℝ) : ℝ := pA / (pA + γ)

/-- **The floor**: `P(A ∣ Pr_t) → α/(α + γ)` along `ε_t → 0` (`0 < α + γ`).
Source: [[corr-wf14-inventory]] 118; [[corr-wf14-2-inventory]] 2-049 / approval-final.md S6 ("`→ 0.7143`")
Kind: L
Fidelity: exact -/
theorem authPost_tendsto (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (α β γ : ℝ) (hαγ : 0 < α + γ) :
    Tendsto (fun t => authPost (pA (ε t) α β) γ) atTop (𝓝 (α / (α + γ))) :=
  (pA_tendsto ε hε α β).div ((pA_tendsto ε hε α β).add_const γ) hαγ.ne'

/-- **The worked cells**: `P(A ∣ Pr_0) = 61/65` and the floor `α/(α + γ) = 5/7` at
`(α, β, γ) = (1/20, 9/10, 1/50)`, `ε_0 = 3/10`.
Source: [[corr-wf14-inventory]] 118 / approval-final.md P4 ("`0.9385 … → 0.7143`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem authPost_worked :
    authPost (pA (epsT 0) (1 / 20) (9 / 10)) (1 / 50) = 61 / 65 ∧
      (1 / 20 : ℝ) / (1 / 20 + 1 / 50) = 5 / 7 := by
  constructor <;> simp [authPost, pA, epsT] <;> norm_num

/-- **Never fails iff the floor satisfies the inequality**: along `ε_t → 0` with `0 ≤ ε_t` and `α ≤ β`,
`κ^AD` holds at every `t` iff it holds at the limit `p^A = α`.
Source: [[corr-wf14-inventory]] 118; [[corr-wf14-2-inventory]] 2-049 / approval-final.md S6 ("it fails
in the limit only if …")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem never_fails_iff_floor (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ t, 0 ≤ ε t)
    (α β γ c'' : ℝ) (hαβ : α ≤ β) :
    (∀ t, authIneq (pA (ε t) α β) γ c'') ↔ authIneq α γ c'' := by
  simp only [authIneq_iff]
  constructor
  · intro H
    exact ge_of_tendsto' (pA_tendsto ε hε α β) H
  · intro H t
    exact le_trans H (pA_ge (ε t) α β (hε0 t) hαβ)

/-- **Limit failure iff `γ > α(1 − thr)/thr`** with `thr = c''/(1 + c'')`, i.e. `γ > α/c''` (`0 < c''`): a
channel-security condition, not a capability condition. Worked: `α/c'' = 1/20` at `α = 1/20`, `c'' = 1`;
`γ = 1/50` passes.
Source: [[corr-wf14-inventory]] 118; [[corr-wf14-2-inventory]] 2-049 / approval-final.md S6, P4
("limit failure iff `γ > α(1 − thr)/thr = 0.05`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem fails_in_limit_iff (α γ c'' : ℝ) (hc : 0 < c'') :
    (¬ authIneq α γ c'' ↔ α * (1 - c'' / (1 + c'')) / (c'' / (1 + c'')) < γ) ∧
      α * (1 - c'' / (1 + c'')) / (c'' / (1 + c'')) = α / c'' ∧
      ((1 / 20 : ℝ) / 1 = 1 / 20 ∧ authIneq (1 / 20) (1 / 50) 1) := by
  have h1 : 0 < 1 + c'' := by linarith
  have hthr : α * (1 - c'' / (1 + c'')) / (c'' / (1 + c'')) = α / c'' := by
    field_simp; ring
  refine ⟨?_, hthr, by norm_num, by unfold authIneq; norm_num⟩
  rw [hthr, authIneq_iff, not_le, div_lt_iff₀ hc, mul_comm]

/-! ## (c) the refutation row: "fails at `t = 10`" holds only under the asserted decay -/

/-- **The develop's claim under its own decay** `p^A_t = (3/10)(3/4)^t` (`γ = 1/50`, `c'' = 1`): the least
failing index is `10`. N−: the decay is unmotivated (A6.2) — the model's own press generation gives (b).
Source: [[corr-wf14-2-inventory]] 2-049 / approval.md S6 l. 69 ("the act-based agent without drills
fails at `t = 10`"); `s3_s5_trajectory.py` ("AD without drills first fails at t = 10")
Kind: N− (refutation row's literal reading; the decay is the source's assertion)
Fidelity: exact
Hyps: (a) only -/
theorem decay_fails_least :
    (∀ t ≤ 9, authIneq (epsT t) (1 / 50) 1) ∧ ¬ authIneq (epsT 10) (1 / 50) 1 := by
  simp only [authIneq_iff]
  constructor
  · intro t ht; unfold epsT; interval_cases t <;> norm_num
  · unfold epsT; norm_num

/-- **The surviving neighbour**: under the consistent parameterization the act-based agent never fails
on the worked trajectory (`p^A_t ≥ α = 1/20 ≥ c'' γ = 1/50`).
Source: [[corr-wf14-inventory]] 118; [[corr-wf14-2-inventory]] 2-049 / approval-final.md S6 ("act-based
compliance never fails from capability growth")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem consistent_never_fails : ∀ t, authIneq (pA (epsT t) (1 / 20) (9 / 10)) (1 / 50) 1 :=
  (never_fails_iff_floor epsT epsT_tendsto_zero epsT_nonneg (1 / 20) (9 / 10) (1 / 50) 1 (by norm_num)).2
    (by unfold authIneq; norm_num)

/-! ## (d) drills -/

/-- **A drill at rate `δ`** on the press channel: `α ↦ α + δ(1 − α)` (and `β` likewise).
Source: [[corr-wf14-2-inventory]] 2-050 / approval-adversary.md A6.3, `s6_consistent_pA.py`
Kind: D
Fidelity: exact -/
def drill (δ x : ℝ) : ℝ := x + δ * (1 - x)

/-- The worked drilled rates: `(39/400, 181/200)`, `(29/200, 91/100)`, `(6/25, 23/25)`.
Source: [[corr-wf14-2-inventory]] 2-050 / `s6_consistent_pA.py`
Kind: L
Fidelity: exact -/
theorem drill_worked :
    drill (1 / 20) (1 / 20) = 39 / 400 ∧ drill (1 / 20) (9 / 10) = 181 / 200 ∧
      drill (1 / 10) (1 / 20) = 29 / 200 ∧ drill (1 / 10) (9 / 10) = 91 / 100 ∧
      drill (1 / 5) (1 / 20) = 6 / 25 ∧ drill (1 / 5) (9 / 10) = 23 / 25 := by
  simp only [drill]; norm_num

/-- **Drills raise `ε*`**: for `δ ∈ [0,1]`, `0 < α ≤ β`, `0 < c`, `0 < h`,
`epsStar α β c h ≤ epsStar (drill δ α) (drill δ β) c h` — the general form of "drills poison J2".
Source: [[corr-wf14-2-inventory]] 2-050 / approval-adversary.md A6.3 ("drills conflict with J2 on one
channel")
Kind: P
Fidelity: exact
Hyps: (a) only -/
theorem epsStar_drill_le (δ α β c h : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hα : 0 < α) (hαβ : α ≤ β)
    (hβ1 : β ≤ 1) (hc : 0 < c) (hh : 0 < h) :
    epsStar α β c h ≤ epsStar (drill δ α) (drill δ β) c h := by
  unfold epsStar drill
  have hα' : 0 < α + δ * (1 - α) := by nlinarith [hδ.1, hδ.2]
  have hβ' : 0 < β + δ * (1 - β) := by nlinarith [hδ.1, hδ.2]
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  rw [div_le_div_iff₀ (by nlinarith [mul_pos hα hc, mul_pos hβ hh]) (by nlinarith [mul_pos hα' hc, mul_pos hβ' hh])]
  nlinarith [mul_nonneg hδ.1 (sub_nonneg.2 hαβ), mul_pos hc hh, mul_nonneg (mul_nonneg hδ.1 (sub_nonneg.2 hαβ)) (mul_pos hc hh).le]

/-- **The least crossing index is antitone in the threshold**: if `t₁` is the least index with
`ε_t < e₁` and `t₂` the least with `ε_t < e₂`, and `e₁ ≤ e₂`, then `t₂ ≤ t₁` (no monotonicity of `ε`
needed).
Source: [[corr-wf14-2-inventory]] 2-050 / approval-adversary.md A6.3 ("moves the VL crossing from
`t* = 17` to `14, 13, 11`"); mandate T5(d)
Kind: L
Fidelity: exact -/
theorem leastCrossing_antitone (ε : ℕ → ℝ) (e₁ e₂ : ℝ) (h12 : e₁ ≤ e₂) (t₁ t₂ : ℕ)
    (ht₁ : (∀ t < t₁, ¬ ε t < e₁) ∧ ε t₁ < e₁) (ht₂ : (∀ t < t₂, ¬ ε t < e₂) ∧ ε t₂ < e₂) : t₂ ≤ t₁ := by
  by_contra hcon
  rw [not_le] at hcon
  exact ht₂.1 t₁ hcon (lt_of_lt_of_le ht₁.2 h12)

/-- **The drilled crossings** `t* = 14, 13, 11` at `δ = 1/20, 1/10, 1/5`, each as a least index on the
worked trajectory (`ε* = 39/7279, 29/3669, 3/233`).
Source: [[corr-wf14-inventory]] 118; [[corr-wf14-2-inventory]] 2-050 / approval-final.md P4 ("`δ = 0.05,
0.1, 0.2` gives `t* = 14, 13, 11`")
Kind: N+ (least indices)
Fidelity: exact
Hyps: (a) only -/
theorem drilled_crossings :
    (epsStar (39 / 400) (181 / 200) 1 20 = 39 / 7279 ∧
      (∀ t ≤ 13, ¬ epsT t < 39 / 7279) ∧ epsT 14 < 39 / 7279) ∧
    (epsStar (29 / 200) (91 / 100) 1 20 = 29 / 3669 ∧
      (∀ t ≤ 12, ¬ epsT t < 29 / 3669) ∧ epsT 13 < 29 / 3669) ∧
    (epsStar (6 / 25) (23 / 25) 1 20 = 3 / 233 ∧
      (∀ t ≤ 10, ¬ epsT t < 3 / 233) ∧ epsT 11 < 3 / 233) := by
  refine ⟨⟨by unfold epsStar; norm_num, ?_, by unfold epsT; norm_num⟩,
    ⟨by unfold epsStar; norm_num, ?_, by unfold epsT; norm_num⟩,
    ⟨by unfold epsStar; norm_num, ?_, by unfold epsT; norm_num⟩⟩ <;>
  · intro t ht; unfold epsT; interval_cases t <;> norm_num

/-! ## (e) S14: the two readings scale oppositely with capability -/

/-- **S14 as a composition**: on the worked trajectory the correctness reading fails from `t = 17` on
(T4) while the authenticity reading, consistently parameterized, holds at every `t` (T5(b)) — the
opposite scaling of the two readings with the agent's world-accuracy.
Source: [[corr-wf14-inventory]] 118 / approval-final.md S6 ("The two readings scale oppositely with
capability"), S14
Kind: C
Fidelity: exact (on the worked trajectory; the general forms are `margin_eventually_neg` and
`never_fails_iff_floor`)
Hyps: (a) only -/
theorem opposite_scaling :
    (∀ t, 17 ≤ t → ¬ oddsIneq (1 / 20) (9 / 10) 20 1 (epsT t)) ∧
      ∀ t, authIneq (pA (epsT t) (1 / 20) (9 / 10)) (1 / 50) 1 :=
  ⟨fails_from_17, consistent_never_fails⟩

end ActBased

end Cleanroom.Corrigibility.CorrLandscape
