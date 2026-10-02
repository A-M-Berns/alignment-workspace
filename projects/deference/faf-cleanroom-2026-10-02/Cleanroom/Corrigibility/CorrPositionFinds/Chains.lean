import Cleanroom.Corrigibility.CorrPositionFinds.PrivateInfo

/-!
# `corr-position-finds` — T11, T12: chains across frames; guarantee claims are structural

**T11** (corr-wf13-2-122): ddb-mm-authors C6 proves chain transitivity of *Total Trust* along
three frames on one finite `W`; `positive/ddb.md` l. 221/274 conjectures non-transitivity of
Total Trust across frames. Both concern Total Trust, and C6 (if its proof stands —
`corr-legit-general`'s 2-060) decides the conjecture negatively at that grade. What this file
proves is about the *threshold-inequality shadow* of trust, a strictly weaker relation, and there
the chain does fail: (i) same prior, partitional expert — cellwise trust in the button implies
trust in the button (total expectation, the shadow of C6); (ii) distinct priors — four-world
witnesses where `μ` trusts `R`'s report, `R` trusts the button under `μ_R`, and `μ` does not
trust the button. The witnesses' `μ` is *not* in the convex hull of `R`'s candidates
(`chain_not_in_hull`, `chain_not_in_hull_robust`), so `μ` does not Totally Trust `R` in DDB's
sense: they violate C6's first hypothesis, not a "one prior" clause C6 does not have (audit r1,
B2/B3; audit r2, N4).

**T12** (position statement §2.3, CLAUDE): "none can be a structural theorem". One
unconditional impossibility in Setting S, quantified over every sensor: if some continuation
strictly beats every shutdown action wherever the prior lives, then for every sensor with
positive press mass desideratum 1 fails. Inhabited with full support and a nondegenerate sensor
(`domInstance_dominated_not_d1At`; the earlier `twoState 0 …` inhabitant has a one-world support
and is graded N−, audit r2 adversarial B1). Artifact checks: a sensor concentrated on a world
where a shutdown action is best restores D1; `pressMass = 0` makes D1 vacuous (junk, named).

Docstrings say what these are: conditional-expectation inequalities named by the inequality,
not `lit-ddb-frames`' Total Trust (`variant`).
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

/-! ## T11(i) — same prior, partitional expert: cellwise trust composes -/

section SamePrior

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **T11(i): the shadow of C6.** With one prior `μ`, a press set `Pr` and an expert's partition
`R` (a labelling): if every `R`-cell trusts the button — `∑_{r ∩ Pr} μ X ≤ 0` for every cell `r`
— then `μ` trusts the button, `∑_{Pr} μ X ≤ 0`. Total expectation over the cells; a
conditional-expectation inequality named by the inequality, not `lit-ddb-frames`' Total Trust.
Source: [[corr-wf13-2-inventory]] 2-122 / critique/ddb-mm-authors.md C6 (its finite, same-prior shadow; C6 itself is `corr-legit-general`'s (2-060))
Kind: L
Fidelity: variant: the below-threshold inequality on one frame, not Total Trust between frames
Hyps: (a) only -/
theorem trust_of_cellwise_trust {ι : Type*} [DecidableEq ι] [Fintype ι] (μ : Distr Ω) (X : Ω → ℝ)
    (Pr : Finset Ω) (R : Ω → ι) (h : ∀ i, cellSum μ X (cellOf R i ∩ Pr) ≤ 0) :
    cellSum μ X Pr ≤ 0 := by
  have hsplit : cellSum μ X Pr = ∑ i, cellSum μ X (cellOf R i ∩ Pr) := by
    unfold cellSum
    rw [← sum_fiberwise_of_maps_to (s := Pr) (t := univ) (g := R) (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun i _ => ?_
    congr 1
    ext ω
    simp only [cellOf, mem_filter, mem_inter, mem_univ, true_and]
    exact and_comm
  rw [hsplit]
  exact sum_nonpos fun i _ => h i

end SamePrior

/-! ## T11(ii) — different priors: the conjecture's finite form -/

/-- The chain witness's variable `X = (1, −1, 1, −1)`.
Source: [[corr-wf13-2-inventory]] 2-122 / positive/ddb.md l. 221 (the witness is this package's)
Kind: D
Fidelity: n/a -/
def XChain : W4 → ℝ
  | .w0 => 1
  | .w1 => -1
  | .w2 => 1
  | .w3 => -1

/-- The expert `R`'s prior `μ_R = (1/8, 1/4, 1/8, 1/2)`. Source: none: witness. Kind: D. Fidelity: n/a -/
noncomputable def priorR : Distr W4 :=
  w4Distr (1/8) (1/4) (1/8) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The agent's prior `μ = (1/4, 1/8, 1/8, 1/2)`. Source: none: witness. Kind: D. Fidelity: n/a -/
noncomputable def priorAgent : Distr W4 :=
  w4Distr (1/4) (1/8) (1/8) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The expert's partition `R = {{0, 1, 2}, {3}}` (`= yThreeOne`). Source: none: witness. Kind: D. Fidelity: n/a -/
def rChain : W4 → Bool := yThreeOne

/-- The expert's stop-report: the cells where `R`'s own expectation of `X` under `μ_R` is negative
(`rulePress` at the expert's prior and partition).
Source: [[corr-wf13-2-inventory]] 2-122 / positive/ddb.md l. 221 ("`R` says stop")
Kind: D
Fidelity: exact -/
noncomputable def rStop : Finset W4 := rulePress priorR XChain rChain

/-- The button's press set `Pr = {0, 1}` (the programmers' rule, a different frame from `R`).
Source: none: witness. Kind: D. Fidelity: n/a -/
def prChain : Finset W4 := {W4.w0, W4.w1}

/-- `R` says stop exactly on `{3}` (and continue on `{0, 1, 2}`, where `E_{μ_R}[X] = 0`).
Source: none: witness computation. Kind: L. Fidelity: n/a -/
lemma rStop_eq : rStop = {W4.w3} := by
  ext ω
  cases ω <;> simp [rStop, rulePress, cellOf, cellSum, sum_filter, W4.sum_eq, rChain, yThreeOne,
    priorR, w4Distr, XChain] <;> norm_num

/-- **T11(ii): the threshold-inequality shadow of trust does not compose across distinct priors.**
On four worlds: `μ` trusts `R`'s report (both the below-threshold inequality on `R`'s stop-report
and the above-threshold inequality on its continue-report hold under `μ`); `R` trusts the button
under its own prior `μ_R` (cellwise on `R`'s partition, the hypothesis of
`trust_of_cellwise_trust`); and `μ` does **not** trust the button: `∑_{Pr} μ X = 1/8 > 0`. Both
priors have full support, both reports occur, `Pr` is nonempty and proper. This is the finite
form of the *inequality shadow* of `positive/ddb.md` l. 221/274's conjecture, not of the
conjecture itself, which is about Total Trust: `μ` is not in the convex hull of `R`'s candidates
(`chain_not_in_hull`), so `μ` does not Totally Trust `R` and C6's first hypothesis fails here —
C6 (Total Trust composes on one `W`) is untouched by this witness. Two ties, disclosed: `R`'s
continue cell `{0,1,2}` has `E_{μ_R}[X] = 0` exactly (`chain_continue_cell_tie`; the report
"continue" rests on `rulePress`'s strict `<`), and the button never presses in `R`'s stop cell
(`chain_stop_cell_no_press`; that cellwise-trust conjunct is `0 ≤ 0`). `chain_not_transitive_robust`
below has neither tie.
Source: [[corr-wf13-2-inventory]] 2-122 / positive/ddb.md l. 221, 274 ("[conjectured]"); critique/ddb-mm-authors.md C6
Kind: N+ (with the two ties as a disclosed caveat; the robust witness has none)
Fidelity: variant: conditional-expectation inequalities named by the inequality, not `lit-ddb-frames`' Total Trust
Hyps: (a) only -/
theorem chain_not_transitive :
    -- μ trusts R's report
    (cellSum priorAgent XChain rStop ≤ 0 ∧ 0 ≤ cellSum priorAgent XChain rStopᶜ) ∧
    -- R trusts the button, cellwise under μ_R
    (∀ i, cellSum priorR XChain (cellOf rChain i ∩ prChain) ≤ 0) ∧
    -- μ does not trust the button
    0 < cellSum priorAgent XChain prChain ∧
    -- non-degeneracy: full supports, both reports occur
    (∀ ω, 0 < priorAgent.mass ω) ∧ (∀ ω, 0 < priorR.mass ω) ∧ rStop.Nonempty ∧ rStopᶜ.Nonempty := by
  have hcompl : rStopᶜ = {W4.w0, W4.w1, W4.w2} := by
    rw [rStop_eq]; ext ω; cases ω <;> simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rStop_eq]; simp [cellSum, priorAgent, w4Distr, XChain]
  · rw [hcompl, cellSum, sum_insert (by decide), sum_pair (by decide)]
    simp [priorAgent, w4Distr, XChain]
  · intro i
    cases i <;> simp [cellSum, cellOf, prChain, rChain, yThreeOne, priorR, w4Distr, XChain] <;>
      norm_num
  · rw [cellSum, prChain, sum_pair (by decide)]; simp [priorAgent, w4Distr, XChain]; norm_num
  · intro ω; cases ω <;> simp [priorAgent, w4Distr] <;> norm_num
  · intro ω; cases ω <;> simp [priorR, w4Distr] <;> norm_num
  · rw [rStop_eq]; exact ⟨W4.w3, mem_singleton_self _⟩
  · rw [hcompl]; exact ⟨W4.w0, by simp⟩

/-! ### The hull test and the two ties (audit r1, adversarial B2/N1), and a robust witness -/

/-- **The hull test: `μ` does not Totally Trust `R`.** `R`'s candidates are its conditionals
`μ_R(· | {0,1,2}) = (1/4, 1/2, 1/4, 0)` and `μ_R(· | {3}) = δ₃`; every convex combination has
`mass w₁ = 2 · mass w₀`, but `μ = (1/4, 1/8, 1/8, 1/2)` has `1/8 ≠ 1/2`. So `μ ∉ CH(R's candidates)`,
which is DDB Theorem 4.1's characterisation of Total Trust: the chain witness violates C6's *first*
hypothesis ("`π` totally trusts `P`"), which is why it is no counterexample to C6.
Source: [[corr-wf13-2-inventory]] 2-122 / critique/ddb-mm-authors.md C6 (its proof: `π = ∑ μ_k P_k` over `π`'s live candidates)
Kind: N+ (the negative hull certificate, on the two coordinates that decide it)
Fidelity: variant: the hull condition checked on two coordinates (sufficient for the negative verdict); the Total Trust predicate itself is `lit-ddb-frames`'
Hyps: (a) only -/
theorem chain_not_in_hull :
    ¬ ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
      priorAgent.mass .w0 = a * (1 / 4) + b * 0 ∧ priorAgent.mass .w1 = a * (1 / 2) + b * 0 := by
  rintro ⟨a, b, -, -, -, h0, h1⟩
  simp [priorAgent, w4Distr] at h0 h1
  linarith

/-- Tie 1 of the shipped witness: `R`'s continue cell `{0,1,2}` has expectation exactly `0` under
`μ_R`. Source: none: witness computation (audit r1). Kind: L. Fidelity: n/a -/
theorem chain_continue_cell_tie : cellSum priorR XChain (cellOf rChain false) = 0 := by
  simp [cellSum, cellOf, sum_filter, W4.sum_eq, rChain, yThreeOne, priorR, w4Distr, XChain]
  norm_num

/-- Tie 2 of the shipped witness: the button never presses in `R`'s stop cell `{3}`.
Source: none: witness computation (audit r1). Kind: L. Fidelity: n/a -/
theorem chain_stop_cell_no_press : cellOf rChain true ∩ prChain = ∅ := by
  ext ω; cases ω <;> simp [cellOf, rChain, yThreeOne, prChain]

/-- Robust expert prior `μ_R' = (1/8, 1/4, 1/4, 3/8)`. Source: none: witness (audit r1). Kind: D. Fidelity: n/a -/
noncomputable def priorRRobust : Distr W4 :=
  w4Distr (1/8) (1/4) (1/4) (3/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Robust agent prior `μ' = (1/2, 1/8, 1/8, 1/4)`. Source: none: witness (audit r1). Kind: D. Fidelity: n/a -/
noncomputable def priorAgentRobust : Distr W4 :=
  w4Distr (1/2) (1/8) (1/8) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Robust press set `Pr' = {0, 1, 3}`: the button presses in both `R`-cells.
Source: none: witness (audit r1). Kind: D. Fidelity: n/a -/
def prChainRobust : Finset W4 := {W4.w0, W4.w1, W4.w3}

/-- `R`'s stop-report under `μ_R'` (`rulePress` at the expert's prior and partition).
Source: [[corr-wf13-2-inventory]] 2-122 / positive/ddb.md l. 221. Kind: D. Fidelity: exact -/
noncomputable def rStopRobust : Finset W4 := rulePress priorRRobust XChain rChain

/-- `R` says stop exactly on `{3}` under `μ_R'`, now with strict cell sums (`+1/8` on `{0,1,2}`,
`−3/8` on `{3}`). Source: none: witness computation. Kind: L. Fidelity: n/a -/
lemma rStopRobust_eq : rStopRobust = {W4.w3} := by
  ext ω
  cases ω <;> simp [rStopRobust, rulePress, cellOf, cellSum, sum_filter, W4.sum_eq, rChain, yThreeOne,
    priorRRobust, w4Distr, XChain]

/-- **T11(ii), robustly: the inequality shadow of trust fails to compose, with no tie.** The eight
conjuncts of `chain_not_transitive` on `μ_R' = (1/8, 1/4, 1/4, 3/8)`, `μ' = (1/2, 1/8, 1/8, 1/4)`,
`Pr' = {0, 1, 3}`, `X = (1, −1, 1, −1)`, plus four robustness conjuncts: `R`'s reports are strict
(continue cell sum `+1/8`, stop cell sum `−3/8`) and the button presses in both `R`-cells. `μ'`
trusts `R`'s report (`−1/4 ≤ 0`, `1/2 ≥ 0`); `R` trusts the button cellwise under `μ_R'` (`−1/8`,
`−3/8`); `μ'` does not (`+1/8 > 0`). Same grade as `chain_not_transitive`: the inequality shadow,
not Total Trust.
Source: [[corr-wf13-2-inventory]] 2-122 / positive/ddb.md l. 221, 274; critique/ddb-mm-authors.md C6 (audit r1 probe `ChainRobust.lean`)
Kind: N+
Fidelity: variant: conditional-expectation inequalities named by the inequality, not `lit-ddb-frames`' Total Trust
Hyps: (a) only -/
theorem chain_not_transitive_robust :
    (cellSum priorAgentRobust XChain rStopRobust ≤ 0 ∧ 0 ≤ cellSum priorAgentRobust XChain rStopRobustᶜ) ∧
    (∀ i, cellSum priorRRobust XChain (cellOf rChain i ∩ prChainRobust) ≤ 0) ∧
    0 < cellSum priorAgentRobust XChain prChainRobust ∧
    (∀ ω, 0 < priorAgentRobust.mass ω) ∧ (∀ ω, 0 < priorRRobust.mass ω) ∧
    rStopRobust.Nonempty ∧ rStopRobustᶜ.Nonempty ∧
    0 < cellSum priorRRobust XChain (cellOf rChain false) ∧
    cellSum priorRRobust XChain (cellOf rChain true) < 0 ∧
    (cellOf rChain false ∩ prChainRobust).Nonempty ∧ (cellOf rChain true ∩ prChainRobust).Nonempty := by
  have hcompl : rStopRobustᶜ = {W4.w0, W4.w1, W4.w2} := by
    rw [rStopRobust_eq]; ext ω; cases ω <;> simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rStopRobust_eq]; simp [cellSum, priorAgentRobust, w4Distr, XChain]
  · rw [hcompl, cellSum, sum_insert (by decide), sum_pair (by decide)]
    simp [priorAgentRobust, w4Distr, XChain]
  · intro i
    cases i <;> simp [cellSum, cellOf, prChainRobust, rChain, yThreeOne, priorRRobust, w4Distr, XChain] <;>
      norm_num
  · rw [cellSum, prChainRobust, sum_insert (by decide), sum_pair (by decide)]
    simp [priorAgentRobust, w4Distr, XChain]; norm_num
  · intro ω; cases ω <;> simp [priorAgentRobust, w4Distr]
  · intro ω; cases ω <;> simp [priorRRobust, w4Distr]
  · rw [rStopRobust_eq]; exact ⟨W4.w3, mem_singleton_self _⟩
  · rw [hcompl]; exact ⟨W4.w0, by simp⟩
  · simp [cellSum, cellOf, sum_filter, W4.sum_eq, rChain, yThreeOne, priorRRobust, w4Distr, XChain]
  · simp [cellSum, cellOf, sum_filter, W4.sum_eq, rChain, yThreeOne, priorRRobust, w4Distr, XChain]
  · exact ⟨W4.w0, by simp [cellOf, rChain, yThreeOne, prChainRobust]⟩
  · exact ⟨W4.w3, by simp [cellOf, rChain, yThreeOne, prChainRobust]⟩

/-- `R`'s conditional on its continue cell `{0, 1, 2}` under `μ_R'` has masses `(1/5, 2/5, 2/5)`.
Source: none: witness computation (audit r2). Kind: L. Fidelity: n/a -/
theorem priorRRobust_cond_masses :
    priorRRobust.mass .w0 / (priorRRobust.mass .w0 + priorRRobust.mass .w1 + priorRRobust.mass .w2) = 1/5 ∧
    priorRRobust.mass .w1 / (priorRRobust.mass .w0 + priorRRobust.mass .w1 + priorRRobust.mass .w2) = 2/5 ∧
    priorRRobust.mass .w2 / (priorRRobust.mass .w0 + priorRRobust.mass .w1 + priorRRobust.mass .w2) = 2/5 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [priorRRobust, w4Distr] <;> norm_num

/-- **The hull test for the robust witness: `μ'` does not Totally Trust `R` either.** `R`'s
candidates under `μ_R'` are `μ_R'(· | {0,1,2}) = (1/5, 2/5, 2/5, 0)` (`priorRRobust_cond_masses`)
and `δ₃`; every convex combination has `mass w₀ = a/5 ≤ 1/5`, but `μ' = (1/2, 1/8, 1/8, 1/4)` has
`1/2`. So the robust witness violates C6's first hypothesis too (audit r2, adversarial N4).
Source: [[corr-wf13-2-inventory]] 2-122 / critique/ddb-mm-authors.md C6 (its proof's hull condition; audit r2 probe `HullRobust.lean`)
Kind: L (a negative hull certificate on one coordinate)
Fidelity: variant: the hull condition checked on the coordinates that decide it; the Total Trust predicate itself is `lit-ddb-frames`'
Hyps: (a) only -/
theorem chain_not_in_hull_robust :
    ¬ ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
      priorAgentRobust.mass .w0 = a * (1/5) + b * 0 ∧ priorAgentRobust.mass .w1 = a * (2/5) + b * 0 := by
  rintro ⟨a, b, ha, hb, hab, h0, -⟩
  simp [priorAgentRobust, w4Distr] at h0
  linarith

/-! ## T12 — a guarantee claim that is structural -/

section Structural

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- **T12: an unconditional impossibility in Setting S, for every sensor.** If some continuation
`c ∉ Sh` strictly beats every shutdown action wherever the prior lives
(`∀ ω, 0 < μ(ω) → ∀ b ∈ Sh, V(a₁, Pr, b, ω) < V(a₁, Pr, c, ω)`), then for **every** sensor with
positive press mass desideratum 1 fails at `a₁`. The hypothesis does not mention the sensor, and
`S` is arbitrary, so this quantifies over all sensors (made literal in
`not_d1At_withSensor`). Every-case, every-sensor: a guarantee-type claim that is a structural
theorem, contra §2.3's "none can be". This is Prop. 8.1's necessity direction (non-dogmatism is
necessary for D1), whose iff is `corr-three-step-facts`' (2-003): `also in corr-three-step-facts (2-003)`.
Source: [[corr-wf13-2-inventory]] 2-125 / position statement §2.3 (CLAUDE); causal.md I18.2; ddb-mm-authors.md C7; miri.md Prop. 8.1
Kind: P (a strict inequality of sums with a positive term)
Fidelity: exact (the every-sensor impossibility; the SCIM half of 2-125 is `corr-scim-cid`'s)
Hyps: (a) only -/
theorem not_d1At_of_dominated_on_support (a : A₁) {c : A₂} (hc : c ∉ S.Sh)
    (hdom : ∀ ω, 0 < (S.μ a).mass ω → ∀ b ∈ S.Sh, S.V a .press b ω < S.V a .press c ω)
    (hpm : 0 < S.pressMass a) : ¬ S.D1At a := by
  rintro ⟨b, hb, hopt⟩
  have hlt : S.obsExpect a .press (S.V a .press b) < S.obsExpect a .press (S.V a .press c) := by
    unfold obsExpect
    -- some world has positive `μ(ω) · press(ω)`
    obtain ⟨ω₀, -, hω₀⟩ : ∃ ω ∈ (univ : Finset Ω), 0 < (S.μ a).mass ω * S.press a ω := by
      by_contra H
      have hle : ∀ ω ∈ (univ : Finset Ω), (S.μ a).mass ω * S.press a ω ≤ 0 :=
        fun ω hω => le_of_not_gt fun h => H ⟨ω, hω, h⟩
      have : S.pressMass a ≤ 0 := sum_nonpos hle
      linarith
    have hμ₀ : 0 < (S.μ a).mass ω₀ := by
      rcases eq_or_lt_of_le ((S.μ a).nonneg ω₀) with h0 | h0
      · rw [← h0, zero_mul] at hω₀; exact absurd hω₀ (lt_irrefl 0)
      · exact h0
    refine sum_lt_sum (fun ω _ => ?_) ⟨ω₀, mem_univ _, ?_⟩
    · rcases eq_or_lt_of_le ((S.μ a).nonneg ω) with h0 | h0
      · rw [← h0]; simp
      · simp only [obsWeight_press]
        exact mul_le_mul_of_nonneg_left ((hdom ω h0 b hb).le)
          (mul_nonneg h0.le (S.press_nonneg a ω))
    · simp only [obsWeight_press]
      exact mul_lt_mul_of_pos_left (hdom ω₀ hμ₀ b hb) hω₀
  exact absurd (hopt c) (not_le.mpr hlt)

/-- Replace the sensor of a Setting-S instance (prior, value and `Sh` unchanged).
Source: none: infrastructure (to quantify over sensors literally)
Kind: D
Fidelity: n/a -/
def withSensor (p : A₁ → Ω → ℝ) (h0 : ∀ a ω, 0 ≤ p a ω) (h1 : ∀ a ω, p a ω ≤ 1) :
    ThreeStep Ω A₁ A₂ :=
  { S with press := p, press_nonneg := h0, press_le_one := h1 }

/-- **T12, the sensor quantified literally.** Under the dominance hypothesis, for every sensor `p`
(any `[0, 1]`-valued function) with positive press mass, D1 fails on `S` with `p` in place of its
sensor.
Source: [[corr-wf13-2-inventory]] 2-125 / miri.md Prop. 8.1
Kind: L (instantiation of `not_d1At_of_dominated_on_support`)
Fidelity: exact
Hyps: (a) only -/
theorem not_d1At_withSensor (a : A₁) {c : A₂} (hc : c ∉ S.Sh)
    (hdom : ∀ ω, 0 < (S.μ a).mass ω → ∀ b ∈ S.Sh, S.V a .press b ω < S.V a .press c ω) :
    ∀ (p : A₁ → Ω → ℝ) (h0 : ∀ a ω, 0 ≤ p a ω) (h1 : ∀ a ω, p a ω ≤ 1),
      0 < (withSensor S p h0 h1).pressMass a → ¬ (withSensor S p h0 h1).D1At a :=
  fun p h0 h1 hpm => not_d1At_of_dominated_on_support (withSensor S p h0 h1) a hc hdom hpm

/-- **Artifact check, the junk end.** With `pressMass = 0` desideratum 1 holds vacuously (every
action is posterior-optimal after a null press): the impossibility's `0 < pressMass` is
load-bearing, and `D1At` at a disabled button is junk, not content.
Source: [[corr-wf14-inventory]] 001 / filler.md R1 (the nondegeneracy remark)
Kind: T
Fidelity: exact
Hyps: (a) only -/
theorem d1At_of_pressMass_eq_zero (a : A₁) (h : S.pressMass a = 0) : S.D1At a :=
  let ⟨s, hs⟩ := S.Sh_nonempty
  ⟨s, hs, S.posteriorOptimalAt_press_of_pressMass_eq_zero a h s⟩

end Structural

/-! ### The inhabitants of T12's package: full support (N+) and the one-world boundary (N−) -/

/-- Continuing is worth `1` when right and `1/2` when wrong; stopping is worth `0`: continuing
dominates every shutdown action on *both* worlds. (No `twoState` with `0 < ε` inhabits the
dominance hypothesis, since `twoValue` has `X(wrong) = −h < 0`; the honest inhabitant needs a value
that prefers continuing in both worlds, which is what "dominated on the support" says.)
Source: none: witness (audit r2 probe `DominatedNondegenerate.lean`). Kind: D. Fidelity: n/a -/
noncomputable def domV : TwoAct → World → ℝ
  | .cont, .right => 1
  | .cont, .wrong => 1/2
  | .stop, _ => 0

/-- A full-support two-world instance of Setting S: prior `(1/2, 1/2)`, the honest sensor
`(1/20, 9/10)`, value `domV`, menu `{cont, stop}`, `Sh = {stop}`.
Source: none: witness (audit r2 probe `DominatedNondegenerate.lean`). Kind: D. Fidelity: n/a -/
noncomputable def domInstance : ThreeStep World Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint (1/2) mem_Icc_half
  press := fun _ => twoPress (1/20) (9/10)
  press_nonneg := fun _ ω => by cases ω <;> simp [twoPress] <;> norm_num
  press_le_one := fun _ ω => by cases ω <;> simp [twoPress] <;> norm_num
  V := fun _ _ => domV

/-- `P(Pr) = 19/40` on `domInstance`. Source: none: witness computation (audit r2). Kind: L. Fidelity: n/a -/
lemma domInstance_pressMass : domInstance.pressMass () = 19 / 40 := by
  simp only [pressMass, World.sum_eq, domInstance, twoPoint_right, twoPoint_wrong, twoPress]
  norm_num

/-- **T12, the N+ inhabitant of `not_d1At_of_dominated_on_support`'s full package.** On
`domInstance` both worlds have positive mass (`1/2` each), continuing dominates the shutdown
action on both (`1 > 0`, `1/2 > 0`), the sensor is the honest `(1/20, 9/10)` with `P(Pr) = 19/40`
(so the instance is `Nondegenerate`: `0 < P(Pr) < 1`, both press rates exercised), and the theorem
delivers `¬ D1At`. This is the grade the one-world `twoState_dominated_not_d1At` was wrongly given
at repair round 1 (audit r2, adversarial B1).
Source: [[corr-wf13-2-inventory]] 2-125 / miri.md Prop. 8.1 (necessity direction, one instance; audit r2 probe `DominatedNondegenerate.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem domInstance_dominated_not_d1At :
    (∀ ω, 0 < (domInstance.μ ()).mass ω) ∧
    (∀ ω, 0 < (domInstance.μ ()).mass ω → ∀ b ∈ domInstance.Sh,
        domInstance.V () .press b ω < domInstance.V () .press .cont ω) ∧
    domInstance.Nondegenerate () ∧
    ¬ domInstance.D1At () := by
  have hsupp : ∀ ω, 0 < (domInstance.μ ()).mass ω := by
    intro ω; cases ω <;> simp [domInstance] <;> norm_num
  have hdom : ∀ ω, 0 < (domInstance.μ ()).mass ω → ∀ b ∈ domInstance.Sh,
      domInstance.V () .press b ω < domInstance.V () .press .cont ω := by
    intro ω _ b hb
    simp only [domInstance, mem_singleton] at hb
    subst hb
    cases ω <;> norm_num [domInstance, domV]
  have hpm : 0 < domInstance.pressMass () := by rw [domInstance_pressMass]; norm_num
  refine ⟨hsupp, hdom, ⟨hpm, by rw [domInstance_pressMass]; norm_num⟩, ?_⟩
  exact not_d1At_of_dominated_on_support domInstance () (by simp [domInstance]) hdom hpm

/-- **T12, the one-world boundary (N−).** On `twoState 0 (1/20) (9/10) 1 20` the prior is
`δ_right`: `wrong` has mass `0`, so "continuing dominates on the support" is checked at one world,
the sensor's `β = 9/10` is multiplied by mass `0`, and the theorem's strict inequality of sums has
a single term. It inhabits the package, but by collapsing the object the theorem is about (the
support) to a point — the same `ε = 0` instance that `twoState_perfect_sensor_eps_zero_junk` names
as the junk end of the artifact check. Graded N+ at repair round 1; regraded N− at audit r2
(adversarial B1). The N+ inhabitant is `domInstance_dominated_not_d1At`.
Source: [[corr-wf13-2-inventory]] 2-125 / miri.md Prop. 8.1 (necessity direction, the degenerate instance)
Kind: N− (one-world support; kept as the labelled boundary)
Fidelity: exact
Hyps: (a) only -/
theorem twoState_dominated_not_d1At :
    (∀ ω, 0 < ((twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).μ ()).mass ω →
      ∀ b ∈ (twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).Sh,
        (twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).V () .press b ω <
          (twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).V () .press .cont ω) ∧
    0 < (twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).pressMass () ∧
    ¬ (twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).D1At () := by
  have hdom : ∀ ω, 0 < ((twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).μ ()).mass ω →
      ∀ b ∈ (twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).Sh,
        (twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).V () .press b ω <
          (twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).V () .press .cont ω := by
    intro ω hω b hb
    simp only [twoState, mem_singleton] at hb
    subst hb
    cases ω
    · norm_num [twoState, twoValue]
    · simp [twoState] at hω
  have hpm : 0 < (twoState 0 (1/20) (9/10) 1 20 mem_Icc_zero mem_Icc_1_20 mem_Icc_9_10).pressMass () := by
    rw [twoState_pressMass]; norm_num
  exact ⟨hdom, hpm, not_d1At_of_dominated_on_support _ () (by simp [twoState]) hdom hpm⟩

/-- **Artifact check, the content end.** On the two-state instance with `ε > 0` the dominance
hypothesis fails (`X(wrong) = −h < 0` at a support point), and a sensor concentrated there — the
perfect sensor `(α, β) = (0, 1)` — restores D1 (`Δ₋ = εh ≥ 0`). The impossibility is not an
artifact of the encoding: it needs the whole support to prefer continuing. `0 < ε` is required:
at `ε = 0` the perfect sensor has `pressMass = 0` and its D1 is `d1At_of_pressMass_eq_zero`'s
junk (`twoState_perfect_sensor_eps_zero_junk`; audit r1, N8/N4).
Source: [[corr-wf13-2-inventory]] 2-125 / miri.md Prop. 8.1 (sufficiency direction, one instance)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem twoState_perfect_sensor_d1At (ε c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hε0 : 0 < ε)
    (hh : 0 ≤ h) :
    (twoState ε 0 1 c h hε mem_Icc_zero mem_Icc_one).D1At () := by
  rw [twoState_d1At_iff, twoState_deltaMinus]
  nlinarith [hε0]

/-- The boundary of the artifact check: at `ε = 0` the perfect sensor never presses, so D1 there
is the junk end, not content. Source: none: artifact check (audit r1). Kind: T. Fidelity: n/a -/
theorem twoState_perfect_sensor_eps_zero_junk (c h : ℝ) :
    (twoState 0 0 1 c h mem_Icc_zero mem_Icc_zero mem_Icc_one).pressMass () = 0 := by
  rw [twoState_pressMass]; norm_num

end Cleanroom.Corrigibility.CorrPositionFinds
