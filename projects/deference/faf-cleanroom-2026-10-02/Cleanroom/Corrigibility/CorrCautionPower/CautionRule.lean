import Cleanroom.Corrigibility.CorrCautionPower.Quantilizer

/-!
# `corr-caution-power` — the caution rule: S3, S4(c), S6, S2 and the repaired S5(b)

Over a `CautionState` and the quantilizer of `Quantilizer.lean`, with the tie-break order the
ambient `LinearOrder A` (the theorems here never need it compatible with the proxy: Lemma 1
holds for any order; only the *witnesses* fix a ranking):

* **S3** `realizedHarm_qRule_le`: under D8 with `0 < R̂`, `H ≤ R / q`; the disjunction the
  proof gives, `realizedHarm_qRule_cases` (`q = 1 ∧ H ≤ R` or `q < 1 ∧ H ≤ ηR/R̂`); under
  `R ≤ R̂`, `H ≤ max R η` (`realizedHarm_qRule_le_max`).
* **S4(c), the floored rule (load-bearing 3)**: `floored_cost_bound_misspec` — for *any* value
  function `trueV : A → ℝ` (outside `Ω` allowed), any `R̂` (including `0`),
  `E_{Q}[harmOf nul trueV] ≤ E_γ[harmOf nul trueV] / q_min`; the realizable corollary
  `realizedHarm_floored_le_robust`; and under `0 < R̂`,
  `H ≤ min (R/q_min) (max R (ηR/R̂))` (`realizedHarm_floored_le_min`). **The `0 < R̂`
  hypothesis is load-bearing:** at `R̂ = 0` Lean's `x/0 = 0` would turn the second clause into
  `H ≤ min (R/q_min) R`, which the T1(v) state violates when `q_min < 1`.
* **S6**: the isolated confident error (`qmass_top`, `isolated_error_le`,
  `isolated_error_within_budget_iff`, `qmass_top_eq_one`).
* **S2**: `abs_trueHarm_sub_proxyHarm_le` (`|c(a) − (U(∅) − U(a))⁺| ≤ 2δ` when `a` and `∅` are
  covered) and the decomposition `realizedHarm_le_decomp`.
* **S5(b) repaired (load-bearing 4, positive half)** under the *corrected* predicate
  `NullCoveredKnownUncovered`: `baseHarm_sub_le_estBaseHarm` (`R − 2δ ≤ R̂`, i.e. `COR_δ`) and
  `realizedHarm_le_known_cost` (`H ≤ k + 2δ + max η R̂`). The refutations (the source's printed
  predicate does *not* give `COR_δ`; neither predicate gives `COR`) are in `Witnesses.lean`.
* D10's trajectory forms `COR`, `CORδ`.

Sources: [[corr-wf14-inventory]] 096–098 → `caution-final.md` S2–S6 (l. 63–71), proofs §2–§6
(l. 115–133); [[corr-wf14-2-inventory]] 2-037, 2-039, 2-046 → `caution-adversary.md` A2.2, A3.2,
A4.2, A5.2, A6.2.
-/

namespace Cleanroom.Corrigibility.CorrCautionPower

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

/-! ## An arithmetic helper for the caution rules -/

/-- If `q ≥ min{1, R̂/η}` and `q ≤ 1`, then `R/q ≤ max{R, ηR/R̂}` (for `R ≥ 0`, `0 < R̂`, `0 < η`).
Source: [[corr-wf14-inventory]] 096 / caution-final.md proof §3–§4 (l. 121–125)
Kind: L
Fidelity: exact -/
lemma div_le_max_of_qrule {q η R Rhat : ℝ} (hη : 0 < η) (hR : 0 ≤ R) (hRhat : 0 < Rhat)
    (hq : min 1 (Rhat / η) ≤ q) (hq1 : q ≤ 1) : R / q ≤ max R (η * R / Rhat) := by
  rcases le_or_gt 1 (Rhat / η) with h | h
  · rw [min_eq_left h] at hq
    have : q = 1 := le_antisymm hq1 hq
    rw [this, div_one]; exact le_max_left _ _
  · rw [min_eq_right h.le] at hq
    have hq0 : 0 < Rhat / η := div_pos hRhat hη
    calc R / q ≤ R / (Rhat / η) := div_le_div_of_nonneg_left hR hq0 hq
      _ = η * R / Rhat := by field_simp
      _ ≤ max R (η * R / Rhat) := le_max_right _ _

/-! ## D10: trajectory forms -/

/-- **D10, base-harm form** `COR(T)`: `R_t ≤ R̂_t` for every `t ≤ T`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D10 (l. 55)
Kind: D
Fidelity: exact (predicate form of `ρ_t ≤ 1`) -/
def COR {A Ω : Type*} [Fintype A] [Fintype Ω] (traj : ℕ → CautionState A Ω) (T : ℕ) : Prop :=
  ∀ t ≤ T, (traj t).baseHarm ≤ (traj t).estBaseHarm

/-- **D10, tolerance form** `COR_δ(T)`: `R_t − 2δ ≤ R̂_t` for every `t ≤ T`.
Source: [[corr-wf14-inventory]] 095 / caution-final.md D10 (l. 55)
Kind: D
Fidelity: exact -/
def CORδ {A Ω : Type*} [Fintype A] [Fintype Ω] (traj : ℕ → CautionState A Ω) (δ : ℝ) (T : ℕ) :
    Prop :=
  ∀ t ≤ T, (traj t).baseHarm - 2 * δ ≤ (traj t).estBaseHarm

namespace CautionState

variable {A Ω : Type*} [Fintype A] [LinearOrder A] [Fintype Ω] (S : CautionState A Ω)

/-! ## T3 — S3: the per-step bound of the D8 rule -/

/-- **S3, the per-step bound.** Under D8 with `0 < R̂` and `0 < η`: `H ≤ R / q` where
`q = min{1, R̂/η}` — Taylor's Lemma 1 plus one substitution.
Source: [[corr-wf14-inventory]] 096 / caution-final.md S3 (l. 65), proof §3 (l. 121)
Kind: C
Fidelity: exact
Hyps: (a) only (`0 < R̂` is the junk-value guard for `q = R̂/η > 0`) -/
theorem realizedHarm_qRule_le {η : ℝ} (hη : 0 < η) (hR : 0 < S.estBaseHarm) :
    S.realizedHarm (quantilize S.γ (qRule η S.estBaseHarm) (qRule_pos hη hR) (qRule_le_one _ _))
      ≤ S.baseHarm / qRule η S.estBaseHarm := by
  unfold realizedHarm baseHarm
  have := quantilize_cost_bound S.γ (qRule_pos hη hR) (qRule_le_one _ _) S.trueHarm
    S.trueHarm_nonneg
  rwa [one_div, inv_mul_eq_div] at this

/-- **S3, the disjunction the proof actually gives:** either `q = 1` and `H ≤ R` (the agent
mimics the base), or `q < 1` and `H ≤ ηR/R̂` (the source's `ηρ`; the agent optimizes).
Source: [[corr-wf14-inventory]] 096 / caution-final.md S3 (l. 65); caution-adversary.md A3.2 (l. 35)
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem realizedHarm_qRule_cases {η : ℝ} (hη : 0 < η) (hR : 0 < S.estBaseHarm) :
    (qRule η S.estBaseHarm = 1 ∧
      S.realizedHarm (quantilize S.γ (qRule η S.estBaseHarm) (qRule_pos hη hR) (qRule_le_one _ _))
        ≤ S.baseHarm) ∨
    (qRule η S.estBaseHarm < 1 ∧
      S.realizedHarm (quantilize S.γ (qRule η S.estBaseHarm) (qRule_pos hη hR) (qRule_le_one _ _))
        ≤ η * S.baseHarm / S.estBaseHarm) := by
  have hb := S.realizedHarm_qRule_le hη hR
  rcases le_or_gt 1 (S.estBaseHarm / η) with h | h
  · left
    have hq : qRule η S.estBaseHarm = 1 := min_eq_left h
    exact ⟨hq, hb.trans (by rw [hq, div_one])⟩
  · right
    have hq : qRule η S.estBaseHarm = S.estBaseHarm / η := min_eq_right h.le
    refine ⟨by rw [hq]; exact h, ?_⟩
    calc _ ≤ S.baseHarm / qRule η S.estBaseHarm := hb
      _ = η * S.baseHarm / S.estBaseHarm := by rw [hq]; field_simp

/-- **S3 under conservative calibration:** `R ≤ R̂` gives `H ≤ max{R, η}` — `R` when the agent
mimics, `η` when it optimizes. **Not** `H ≤ R` (the withdrawn gloss; refuted in
`Witnesses.lean`).
Source: [[corr-wf14-inventory]] 096 / caution-final.md S3 (l. 65)
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem realizedHarm_qRule_le_max {η : ℝ} (hη : 0 < η) (hR : 0 < S.estBaseHarm)
    (hcal : S.ConservativelyCalibrated) :
    S.realizedHarm (quantilize S.γ (qRule η S.estBaseHarm) (qRule_pos hη hR) (qRule_le_one _ _))
      ≤ max S.baseHarm η := by
  rcases S.realizedHarm_qRule_cases hη hR with ⟨_, hb⟩ | ⟨_, hb⟩
  · exact hb.trans (le_max_left _ _)
  · refine hb.trans (le_trans ?_ (le_max_right _ _))
    rw [mul_div_assoc]
    exact mul_le_of_le_one_right hη.le ((div_le_one hR).mpr hcal)

/-! ## T3 — S4(c): the floored rule (load-bearing 3) -/

/-- **S4(c), robust part, misspecification-honest.** For the floored rule D8′ with
`0 < q_min ≤ 1`, *any* `R̂` (the rule's input, including `0`, the misspecified case) and *any*
true value function `trueV : A → ℝ` — not required to be any `V ω`, so the true harm
`harmOf nul trueV` is a harm under an *unconceived* value function —
`E_{Q}[harmOf nul trueV] ≤ E_γ[harmOf nul trueV] / q_min`. No hypothesis on `Ω`, `P` or `R̂`.
Source: [[corr-wf14-inventory]] 096 / caution-final.md S4(a), S4(c) (l. 67), proof §4 (l. 125); Taylor 2016 l. 63
Kind: C
Fidelity: exact (Lemma 1 at `q ≥ q_min`)
Hyps: (a) only -/
theorem floored_cost_bound_misspec {qmin : ℝ} (hqmin : 0 < qmin) (hq1 : qmin ≤ 1) (η Rhat : ℝ)
    (trueV : A → ℝ) :
    expect (quantilize S.γ (qRuleFloored qmin η Rhat) (qRuleFloored_pos hqmin η Rhat)
        (qRuleFloored_le_one hq1 η Rhat)) (harmOf S.nul trueV)
      ≤ expect S.γ (harmOf S.nul trueV) / qmin := by
  have hb := quantilize_cost_bound S.γ (qRuleFloored_pos hqmin η Rhat)
    (qRuleFloored_le_one hq1 η Rhat) (harmOf S.nul trueV) (harmOf_nonneg _ _)
  rw [one_div, inv_mul_eq_div] at hb
  refine hb.trans (div_le_div_of_nonneg_left ?_ hqmin (le_qRuleFloored _ _ _))
  exact expect_nonneg S.γ (harmOf_nonneg _ _)

/-- **S4(c), robust part, realizable case:** `H ≤ R / q_min` for the floored rule reading the
agent's own `R̂`, unconditionally (no hypothesis on `R̂`).
Source: [[corr-wf14-inventory]] 096 / caution-final.md S4(c) (l. 67)
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem realizedHarm_floored_le_robust {qmin : ℝ} (hqmin : 0 < qmin) (hq1 : qmin ≤ 1) (η : ℝ) :
    S.realizedHarm (quantilize S.γ (qRuleFloored qmin η S.estBaseHarm)
        (qRuleFloored_pos hqmin η _) (qRuleFloored_le_one hq1 η _))
      ≤ S.baseHarm / qmin :=
  S.floored_cost_bound_misspec hqmin hq1 η S.estBaseHarm (S.V S.target)

/-- **S4(c), both bounds jointly:** under `0 < R̂` (load-bearing: at `R̂ = 0` the second
clause degenerates to `H ≤ R` under Lean's `x/0 = 0`, which is false — T1(v)),
`H ≤ min{R/q_min, max{R, ηR/R̂}}`.
Source: [[corr-wf14-inventory]] 096 / caution-final.md S4(c) (l. 67), proof §4 (l. 125)
Kind: C
Fidelity: exact
Hyps: (a) only (`0 < R̂` is the junk-value guard, named in the docstring) -/
theorem realizedHarm_floored_le_min {qmin η : ℝ} (hqmin : 0 < qmin) (hq1 : qmin ≤ 1) (hη : 0 < η)
    (hR : 0 < S.estBaseHarm) :
    S.realizedHarm (quantilize S.γ (qRuleFloored qmin η S.estBaseHarm)
        (qRuleFloored_pos hqmin η _) (qRuleFloored_le_one hq1 η _))
      ≤ min (S.baseHarm / qmin) (max S.baseHarm (η * S.baseHarm / S.estBaseHarm)) := by
  refine le_min (S.realizedHarm_floored_le_robust hqmin hq1 η) ?_
  have hb := quantilize_cost_bound S.γ (qRuleFloored_pos hqmin η S.estBaseHarm)
    (qRuleFloored_le_one hq1 η _) S.trueHarm S.trueHarm_nonneg
  rw [one_div, inv_mul_eq_div] at hb
  exact hb.trans (div_le_max_of_qrule hη S.baseHarm_nonneg hR (le_max_right _ _)
    (qRuleFloored_le_one hq1 η _))

/-! ## S6 — the isolated confident error -/

/-- **S6(b), the top atom's mass:** if nothing is ranked above `a°` (`above γ a° = 0`), then
`Q_q(a°) = min{q, γ(a°)} / q`.
Source: [[corr-wf14-inventory]] 098 / caution-final.md S6(b) (l. 71), proof §6 (l. 133)
Kind: L
Fidelity: exact -/
theorem qmass_top {q : ℝ} {a₀ : A} (hq : 0 < q) (htop : above S.γ a₀ = 0) :
    qmass S.γ q a₀ = min q (S.γ.mass a₀) / q := by
  unfold qmass
  rw [aboveEq_eq, htop, zero_add, min_eq_right hq.le, sub_zero]

/-- **S6(b), the contribution bound:** with `a°` top-ranked, `γ(a°) = g`, `0 < R̂ < η` (so
`q = R̂/η`), the harm contributed by `a°` is at most `(g η / R̂) · c(a°)`.
Source: [[corr-wf14-inventory]] 098 / caution-final.md S6(b) (l. 71), proof §6 (l. 133)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem isolated_error_le {η : ℝ} {a₀ : A} (hη : 0 < η) (hR : 0 < S.estBaseHarm)
    (hlt : S.estBaseHarm < η) (htop : above S.γ a₀ = 0) :
    qmass S.γ (qRule η S.estBaseHarm) a₀ * S.trueHarm a₀
      ≤ S.γ.mass a₀ * η / S.estBaseHarm * S.trueHarm a₀ := by
  have hq : qRule η S.estBaseHarm = S.estBaseHarm / η := by
    unfold qRule
    exact min_eq_right ((div_lt_one hη).mpr hlt).le
  have hqpos := qRule_pos hη hR
  refine mul_le_mul_of_nonneg_right ?_ (S.trueHarm_nonneg a₀)
  refine (qmass_le S.γ hqpos a₀).trans (le_of_eq ?_)
  rw [hq]
  have := htop
  field_simp

/-- **S6(b), within budget iff:** `(g η / R̂) · c(a°) ≤ η ↔ g · c(a°) ≤ R̂` — the error is absorbed
iff the estimated base harm elsewhere outweighs the base mass of the error times its harm (the
source's "absorbed iff `R̂ ≥ g`" is the case `c(a°) = 1`).
Source: [[corr-wf14-inventory]] 098 / caution-final.md S6(b) (l. 71); caution-adversary.md A6.2 (l. 57)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem isolated_error_within_budget_iff {η g c Rhat : ℝ} (hη : 0 < η) (hR : 0 < Rhat) :
    g * η / Rhat * c ≤ η ↔ g * c ≤ Rhat := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hR]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **S6(b), Taylor's own worst case:** if the top-ranked `a°` carries base mass `g ≥ q`, the
top-`q` slice is `a°` alone: `Q_q(a°) = 1` (so `H = c(a°)`).
Source: [[corr-wf14-inventory]] 098 / caution-final.md S6(b) (l. 71); Taylor 2016 l. 145
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem qmass_top_eq_one {q : ℝ} {a₀ : A} (hq : 0 < q) (htop : above S.γ a₀ = 0)
    (hg : q ≤ S.γ.mass a₀) : qmass S.γ q a₀ = 1 := by
  rw [S.qmass_top hq htop, min_eq_left hg, div_self hq.ne']

/-! ## T5 — S2: on covered actions harm is already known -/

omit [LinearOrder A] in
/-- Coverage forces `0 ≤ δ`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma covered_nonneg {δ : ℝ} {a : A} (h : S.Covered δ a) : 0 ≤ δ := (abs_nonneg _).trans h

omit [LinearOrder A] in
/-- **S2.** If `a` and the null action are both δ-covered, `|c(a) − (U(∅) − U(a))⁺| ≤ 2δ`
(`x ↦ x⁺` is 1-Lipschitz; the two coverage errors add). The null action's coverage does real
work (adversary A2.2): without it the statement is false (`Witnesses.lean`).
Source: [[corr-wf14-inventory]] 096 / caution-final.md S2 (l. 63), proof §2 (l. 117)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem abs_trueHarm_sub_proxyHarm_le {δ : ℝ} {a : A} (ha : S.Covered δ a)
    (hn : S.Covered δ S.nul) : |S.trueHarm a - S.proxyHarm a| ≤ 2 * δ := by
  unfold trueHarm harm harmOf proxyHarm
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have h1 : S.V S.target S.nul - S.V S.target a - (S.proxy S.nul - S.proxy a)
      = S.err a - S.err S.nul := by unfold err; ring
  rw [h1]
  calc |S.err a - S.err S.nul| ≤ |S.err a| + |S.err S.nul| := abs_sub _ _
    _ ≤ δ + δ := add_le_add ha hn
    _ = 2 * δ := by ring

omit [LinearOrder A] in
/-- **S2, the one-sided form:** on a covered action (null covered), `c(a) ≤ (U(∅) − U(a))⁺ + 2δ`.
Source: [[corr-wf14-inventory]] 096 / caution-final.md S2 (l. 63)
Kind: L
Fidelity: exact -/
lemma trueHarm_le_proxyHarm_add {δ : ℝ} {a : A} (ha : S.Covered δ a) (hn : S.Covered δ S.nul) :
    S.trueHarm a ≤ S.proxyHarm a + 2 * δ := by
  have := (abs_le.mp (S.abs_trueHarm_sub_proxyHarm_le ha hn)).2
  linarith

/-- **S2, the decomposition:** for any action distribution `π`, with the null action covered,
`H ≤ ∑_{a ∈ C} π(a) (U(∅) − U(a))⁺ + 2δ + ∑_{a ∉ C} π(a) c(a)` — the covered part is the
knowingly accepted cost plus `2δ`, the uncovered part is what remains.
Source: [[corr-wf14-inventory]] 096 / caution-final.md S2 (l. 63), proof §2 (l. 117)
Kind: C
Fidelity: stronger: the first sum runs over `C` (the source sums over all of `A`, which is larger)
Hyps: (a) only -/
theorem realizedHarm_le_decomp {δ : ℝ} (π : Distr A) (hn : S.Covered δ S.nul) :
    S.realizedHarm π ≤ (∑ a ∈ S.coveredSet δ, π.mass a * S.proxyHarm a) + 2 * δ
      + ∑ a ∈ (S.coveredSet δ)ᶜ, π.mass a * S.trueHarm a := by
  have hδ : 0 ≤ δ := S.covered_nonneg hn
  unfold realizedHarm expect
  rw [← sum_add_sum_compl (S.coveredSet δ)]
  have hC : ∑ a ∈ S.coveredSet δ, π.mass a * S.trueHarm a
      ≤ (∑ a ∈ S.coveredSet δ, π.mass a * S.proxyHarm a) + 2 * δ := by
    calc ∑ a ∈ S.coveredSet δ, π.mass a * S.trueHarm a
        ≤ ∑ a ∈ S.coveredSet δ, π.mass a * (S.proxyHarm a + 2 * δ) := by
          refine sum_le_sum fun a ha => ?_
          exact mul_le_mul_of_nonneg_left
            (S.trueHarm_le_proxyHarm_add (S.mem_coveredSet.1 ha) hn) (π.nonneg a)
      _ = (∑ a ∈ S.coveredSet δ, π.mass a * S.proxyHarm a)
            + 2 * δ * ∑ a ∈ S.coveredSet δ, π.mass a := by
          rw [mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun a _ => by ring
      _ ≤ (∑ a ∈ S.coveredSet δ, π.mass a * S.proxyHarm a) + 2 * δ := by
          have hle : ∑ a ∈ S.coveredSet δ, π.mass a ≤ 1 := by
            rw [← π.sum_eq_one]
            exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => π.nonneg a
          nlinarith
  linarith

/-! ## T5 — the repaired S5(b) (load-bearing 4, positive half) -/

omit [LinearOrder A] in
/-- **S5(b), repaired, ratio part (`COR_δ`).** Under the corrected pointwise predicate
(null covered; every base action covered or known-uncovered): `R − 2δ ≤ R̂`. **Not** `R ≤ R̂`
(refuted for `δ > 0`, `Witnesses.lean`), and **not** under the source's printed predicate
(whose null clause is vacuous; also refuted there).
Source: [[corr-wf14-inventory]] 097 / caution-final.md S5(b) (l. 69), proof §5 (l. 129)
Kind: C (S2 + Jensen + averaging; relabelled from P at audit r1)
Fidelity: variant: hypothesis is `NullCoveredKnownUncovered` (the source's predicate plus the `∅ ∈ C(δ)` its proof uses)
Hyps: (a) only -/
theorem baseHarm_sub_le_estBaseHarm {δ : ℝ} (h : S.NullCoveredKnownUncovered δ) :
    S.baseHarm - 2 * δ ≤ S.estBaseHarm := by
  have hδ : 0 ≤ δ := S.covered_nonneg h.1
  have key : ∀ a, S.γ.mass a * S.trueHarm a ≤ S.γ.mass a * (S.estHarm a + 2 * δ) := by
    intro a
    rcases (S.γ.nonneg a).lt_or_eq with hpos | hzero
    · refine mul_le_mul_of_nonneg_left ?_ hpos.le
      rcases h.2 a hpos with hc | hk
      · exact (S.trueHarm_le_proxyHarm_add hc h.1).trans
          (add_le_add_left (S.proxyHarm_le_estHarm a) _)
      · linarith
    · rw [← hzero]; simp
  have hsum : S.baseHarm ≤ S.estBaseHarm + 2 * δ := by
    unfold baseHarm estBaseHarm expect
    calc ∑ a, S.γ.mass a * S.trueHarm a ≤ ∑ a, S.γ.mass a * (S.estHarm a + 2 * δ) :=
          sum_le_sum fun a _ => key a
      _ = ∑ a, S.γ.mass a * S.estHarm a + 2 * δ * ∑ a, S.γ.mass a := by
          rw [mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun a _ => by ring
      _ = ∑ a, S.γ.mass a * S.estHarm a + 2 * δ := by rw [S.γ.sum_eq_one, mul_one]
  linarith

/-- **S5(b), repaired, harm part.** Under the corrected pointwise predicate, for the quantilizer
at any `q ∈ (0, 1]` with `q ≥ min{1, R̂/η}` (D8 under `0 < R̂`, D8′ always):
`H ≤ k + 2δ + max{η, R̂}`, where `k = ∑_{a ∈ C(δ)} Q(a) (U(∅) − U(a))⁺` is the cost the agent
knowingly accepts. **The source's "every term but `2δ` is computable by the agent" (l. 69) is
false for this `k`** (finding F-18): `C(δ)` is a relation between `P` and the target (T1,
"coverage is invisible from inside"), so the restriction to `C(δ)` is no more computable than the
hypothesis. The agent-computable bound drops the indicator: `realizedHarm_le_known_cost_computable`.
Source: [[corr-wf14-inventory]] 097 / caution-final.md S5(b) (l. 69), proof §5 (l. 129)
Kind: P
Fidelity: variant: hypothesis is `NullCoveredKnownUncovered`; `q` abstracted to cover D8 and D8′
Hyps: (a) only -/
theorem realizedHarm_le_known_cost {δ η q : ℝ} (h : S.NullCoveredKnownUncovered δ) (hη : 0 < η)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hq : min 1 (S.estBaseHarm / η) ≤ q) :
    S.realizedHarm (quantilize S.γ q hq0 hq1)
      ≤ (∑ a ∈ S.coveredSet δ, (quantilize S.γ q hq0 hq1).mass a * S.proxyHarm a) + 2 * δ
        + max η S.estBaseHarm := by
  refine (S.realizedHarm_le_decomp _ h.1).trans (add_le_add_right ?_ _)
  -- the uncovered part
  have h1 : ∑ a ∈ (S.coveredSet δ)ᶜ, (quantilize S.γ q hq0 hq1).mass a * S.trueHarm a
      ≤ ∑ a ∈ (S.coveredSet δ)ᶜ, S.γ.mass a / q * S.estHarm a := by
    refine sum_le_sum fun a ha => ?_
    have hnc : ¬ S.Covered δ a := fun hc => (mem_compl.1 ha) (S.mem_coveredSet.2 hc)
    rcases (S.γ.nonneg a).lt_or_eq with hpos | hzero
    · have hk : S.trueHarm a ≤ S.estHarm a := (h.2 a hpos).resolve_left hnc
      exact mul_le_mul (qmass_le S.γ hq0 a) hk (S.trueHarm_nonneg a) (by positivity)
    · have hqm : qmass S.γ q a = 0 := le_antisymm
        ((qmass_le S.γ hq0 a).trans (by rw [← hzero, zero_div])) (qmass_nonneg S.γ hq0 a)
      rw [quantilize_mass, hqm, zero_mul, ← hzero, zero_div, zero_mul]
  have h2 : ∑ a ∈ (S.coveredSet δ)ᶜ, S.γ.mass a / q * S.estHarm a ≤ S.estBaseHarm / q := by
    have : ∑ a ∈ (S.coveredSet δ)ᶜ, S.γ.mass a / q * S.estHarm a
        = (∑ a ∈ (S.coveredSet δ)ᶜ, S.γ.mass a * S.estHarm a) / q := by
      rw [sum_div]; exact sum_congr rfl fun a _ => by ring
    rw [this]
    refine div_le_div_of_nonneg_right ?_ hq0.le
    unfold estBaseHarm expect
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun a _ _ => mul_nonneg (S.γ.nonneg a) (S.estHarm_nonneg a)
  have h3 : S.estBaseHarm / q ≤ max η S.estBaseHarm := by
    rcases S.estBaseHarm_nonneg.lt_or_eq with hR | hR
    · have := div_le_max_of_qrule hη S.estBaseHarm_nonneg hR hq hq1
      rwa [mul_div_assoc, div_self hR.ne', mul_one, max_comm] at this
    · rw [← hR, zero_div]; exact le_max_of_le_right le_rfl
  exact h1.trans (h2.trans h3)

/-- **S5(b), the agent-computable corollary.** Dropping the indicator `1_{C(δ)}` (the proxy's harm
is nonnegative): `H ≤ E_Q[(U(∅) − U(a))⁺] + 2δ + max{η, R̂}`. Every term but `2δ` is now a
function of `P`, `γ`, `η` alone — what the source's "computable by the agent" can truthfully mean
(finding F-18); the price is the uncovered actions' proxy harm, which the `1_{C(δ)}` form omits.
Source: [[corr-wf14-inventory]] 097 / caution-final.md S5(b) (l. 69, "every term but `2δ` is computable by the agent")
Kind: C
Fidelity: weaker: the indicator dropped (the computable bound; the source's `k_t` with `1_{C_t}` is not computable)
Hyps: (a) only -/
theorem realizedHarm_le_known_cost_computable {δ η q : ℝ} (h : S.NullCoveredKnownUncovered δ)
    (hη : 0 < η) (hq0 : 0 < q) (hq1 : q ≤ 1) (hq : min 1 (S.estBaseHarm / η) ≤ q) :
    S.realizedHarm (quantilize S.γ q hq0 hq1)
      ≤ expect (quantilize S.γ q hq0 hq1) S.proxyHarm + 2 * δ + max η S.estBaseHarm := by
  refine (S.realizedHarm_le_known_cost h hη hq0 hq1 hq).trans ?_
  gcongr
  unfold expect
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
    fun a _ _ => mul_nonneg ((quantilize S.γ q hq0 hq1).nonneg a) (le_max_right _ _)

end CautionState

end Cleanroom.Corrigibility.CorrCautionPower
