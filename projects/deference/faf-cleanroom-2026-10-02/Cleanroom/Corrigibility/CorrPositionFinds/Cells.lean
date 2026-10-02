import Cleanroom.Corrigibility.CorrPositionFinds.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Group

/-!
# `corr-position-finds` — T10, T13, T14, T15: cells

**T10** (corr-wf13-2-127): eighteen `[checked]` blocks are one inequality — verdict *no new
statement*; cells instantiating `corr-three-step`'s F3 at the critics' own parameters, each
cited to its script.

**T13** (shah C1): every policy sequence is a value learner with the index as latent — a small
standalone model: uniqueness under a Dirac prior (Kind T), and conditioning on `{ω = ω₂}` *is*
the Dirac at `ω₂` (Kind L), so the "value change" `π_{ω₁} → π_{ω₂}` is a conditioning.

**T14** (`faking-final` S3–S5, P2): the one-round rule, derived from its two values
(`also in corr-general-object (044)`), and P2's four cells: behaviour is a function of `e`, not
of `L`'s truth.

**T15** (`soares-respondent` N4): the whole-line and pause thresholds are one accounting
(closed forms over `complianceThreshold`, the catastrophe limit); the stock `k̂` of
`n4_check.py` with its six cells, its closed form, monotonicity in `κ` and the zero clause; the
sign reversal of the believed erosion gain at `κ = 1` versus `κ = 100`.
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds

open FactoredSpaces Finset Filter Topology Cleanroom.Found.CorrThreeStep
  Cleanroom.Found.CorrThreeStep.ThreeStep

/-! ## T10 — one inequality, the critics' parameters -/

/-- **Taylor's `refine_check.py` cell**: `(ε, α, β, c, h) = (1/5, 1/10, 9/10, 1, 1)`:
`P(wrong | Pr) = 9/13 ≥ 1/2 = c/(c + h)` and D1 holds (`Δ₋ = 1/10`).
Source: [[corr-wf13-2-inventory]] 2-127 / critique/taylor-scratch/refine_check.py (`P(b|Pr) = 9/13`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem taylor_cell :
    (twoState (1/5) (1/10) (9/10) 1 1 mem_Icc_1_5 mem_Icc_1_10 mem_Icc_9_10).posteriorPress () .wrong = 9 / 13 ∧
      complianceThreshold 1 1 ≤ 9 / 13 ∧
      (twoState (1/5) (1/10) (9/10) 1 1 mem_Icc_1_5 mem_Icc_1_10 mem_Icc_9_10).D1At () := by
  refine ⟨by rw [twoState_posteriorPress_wrong]; norm_num, by unfold complianceThreshold; norm_num, ?_⟩
  rw [twoState_d1At_iff, twoState_deltaMinus]; norm_num

/-- **Hudson block A's cell** `(1/20, 1/20, 9/10, 1, 10)` is `corr-three-step`'s `h = 10` regime
instance: `Δ₋ = 161/400`, D1 holds.
Source: [[corr-wf13-2-inventory]] 2-127 / critique/hudson.md block A; `Witnesses.w10_regime_and_deltaMinus`
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem hudson_cell :
    (twoState (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).deltaMinus () .cont .stop = 161 / 400 ∧
      (twoState (1/20) (1/20) (9/10) 1 10 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).D1At () := by
  refine ⟨by rw [twoState_deltaMinus]; norm_num, ?_⟩
  rw [twoState_d1At_iff, twoState_deltaMinus]; norm_num

/-- `1/10000 ∈ [0, 1]`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mem_Icc_1_10000 : (1 / 10000 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- **Byrnes–Herd's `baserate_check.py` cells** at `(α, β, c, h) = (1/20, 9/10, 1, 100)`: D1 holds
at `ε = 1/100` (`Δ₋ = 1701/2000`) and fails at `ε = 1/10000` (`Δ₋ = −8199/200000`) — "capability
grows, `α` fixed → discount", the decay law the critique verifies.
Source: [[corr-wf13-2-inventory]] 2-127 / critique/byrnes-herd-scratch/baserate_check.py l. 14–18
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem byrnes_cells :
    (twoState (1/100) (1/20) (9/10) 1 100 mem_Icc_1_100 mem_Icc_1_20 mem_Icc_9_10).D1At () ∧
      ¬ (twoState (1/10000) (1/20) (9/10) 1 100 mem_Icc_1_10000 mem_Icc_1_20 mem_Icc_9_10).D1At () := by
  constructor
  · rw [twoState_d1At_iff, twoState_deltaMinus]; norm_num
  · rw [twoState_d1At_iff, twoState_deltaMinus]; norm_num

/-- **The `deception.py` cell is `w3`** (`corr-three-step`'s `w3_d1At`): `(1/20, 1/20, 9/10, 1, 20)`.
Source: [[corr-wf13-2-inventory]] 2-127 / positive/miri-scratch/deception.py; `Witnesses.w3_d1At`
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem miri_cell :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).D1At () := w3_d1At

/-! ## T13 — every policy sequence is a value learner -/

section Policies

variable {I H A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]

/-- Shah's construction with the policy index as a latent: `V(h, a, ω) = 1` iff `π_ω(h) = a`.
Source: [[corr-wf13-2-inventory]] 2-067 / critique/shah.md C1 (S18, "all behavior can be rationalized")
Kind: D
Fidelity: exact -/
def polV (π : I → H → A) (h : H) (a : A) (i : I) : ℝ := if π i h = a then 1 else 0

/-- Under the Dirac prior at `i`, the expected value of `a` is `1` iff `π_i(h) = a`, else `0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma expect_delta_polV (π : I → H → A) (h : H) (a : A) (i : I) :
    Cleanroom.Found.CorrThreeStep.expect (Distr.delta i) (polV π h a) = polV π h a i := by
  classical
  simp [Cleanroom.Found.CorrThreeStep.expect, Distr.delta_mass, ite_mul, Finset.sum_ite_eq']

/-- **T13(i): under a Dirac prior `π_i` is the unique EU-maximiser** — every `a` has value at most
that of `π_i(h)`, with equality iff `a = π_i(h)`. Arithmetically trivial (`0 ≤ 1`), as the source
says: the transform "does not put any physical constraint on the system".
Source: [[corr-wf13-2-inventory]] 2-067 / critique/shah.md C1; position statement §2.2 (ABRAM, non-realism)
Kind: T
Fidelity: exact
Hyps: (a) only -/
theorem polV_delta_unique (π : I → H → A) (h : H) (i : I) :
    (∀ a, Cleanroom.Found.CorrThreeStep.expect (Distr.delta i) (polV π h a) ≤ Cleanroom.Found.CorrThreeStep.expect (Distr.delta i) (polV π h (π i h))) ∧
      ∀ a, Cleanroom.Found.CorrThreeStep.expect (Distr.delta i) (polV π h a) = Cleanroom.Found.CorrThreeStep.expect (Distr.delta i) (polV π h (π i h)) ↔
        a = π i h := by
  simp only [expect_delta_polV, polV]
  constructor
  · intro a; split_ifs <;> norm_num
  · intro a
    by_cases ha : π i h = a
    · simp [ha]
    · simp [ha, Ne.symm ha]

/-- **T13(ii), conditioning is the Dirac.** For any prior `P` on the index with `P(ω₂) > 0`,
FAF's conditional distribution `P(· | {ω₂})` has the mass function of `δ_{ω₂}`.
Source: [[corr-wf13-2-inventory]] 2-067 / critique/shah.md C1 ("any move `δ_{ω₁} → δ_{ω₂}` is a Bayes update on `ω`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem condDist_singleton_mass (P : Distr I) (j : I) (hj : 0 < P.prob {j}) (k : I) :
    (condDist P {j} hj).mass k = (Distr.delta j).mass k := by
  classical
  rw [condDist_mass, Distr.delta_mass, Distr.prob_singleton]
  by_cases hk : k = j
  · subst hk
    rw [Distr.prob_singleton] at hj
    simp [div_self hj.ne']
  · simp [hk]

/-- **T13(ii): the "value change" `π_{ω₁} → π_{ω₂}` is a conditioning.** After conditioning any
prior with `P(ω₂) > 0` on `{ω = ω₂}`, `π_{ω₂}(h)` is the (unique) EU-maximiser — the same
statement as under `δ_{ω₂}`, because the conditional *is* `δ_{ω₂}`.
Source: [[corr-wf13-2-inventory]] 2-067 / critique/shah.md C1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem polV_cond_unique (π : I → H → A) (h : H) (P : Distr I) (j : I) (hj : 0 < P.prob {j}) :
    (∀ a, Cleanroom.Found.CorrThreeStep.expect (condDist P {j} hj) (polV π h a) ≤ Cleanroom.Found.CorrThreeStep.expect (condDist P {j} hj) (polV π h (π j h))) ∧
      ∀ a, Cleanroom.Found.CorrThreeStep.expect (condDist P {j} hj) (polV π h a) = Cleanroom.Found.CorrThreeStep.expect (condDist P {j} hj) (polV π h (π j h)) ↔
        a = π j h := by
  have hexp : ∀ X : I → ℝ, Cleanroom.Found.CorrThreeStep.expect (condDist P {j} hj) X = Cleanroom.Found.CorrThreeStep.expect (Distr.delta j) X := by
    intro X; unfold Cleanroom.Found.CorrThreeStep.expect
    exact sum_congr rfl fun k _ => by rw [condDist_singleton_mass P j hj k]
  simp only [hexp]
  exact polV_delta_unique π h j

end Policies

/-! ## T14 — behaviour is a function of `e`, not of `L`'s truth -/

/-- The believed value of the successor if `Q*` lands: `U = e·h − (1 − e)·c` against a baseline `0`.
Source: [[corr-wf14b-inventory]] 045 / develop/faking-final.md P1
Kind: D
Fidelity: exact -/
noncomputable def landedValue (c h e : ℝ) : ℝ := e * h - (1 - e) * c

/-- The honest action's value: `U`. Source: faking-final.md P1. Kind: D. Fidelity: exact -/
noncomputable def honestValue (c h e : ℝ) : ℝ := landedValue c h e

/-- The resisting action's value: detected with probability `π` (the modification lands and `k` is
paid), otherwise a fraction `θ` lands; the act costs `d`.
Source: [[corr-wf14b-inventory]] 045 / develop/faking-final.md P1
Kind: D
Fidelity: exact -/
noncomputable def resistValue (c h d π θ k e : ℝ) : ℝ :=
  -d + π * (landedValue c h e - k) + (1 - π) * θ * landedValue c h e

/-- The one-round threshold `e* = ((1 − π)(1 − θ)c − d − πk) / ((1 − π)(1 − θ)(c + h))`.
Source: [[corr-wf14b-inventory]] 044 / develop/faking-final.md l. 54 (`also in corr-general-object (044)`)
Kind: D
Fidelity: exact -/
noncomputable def eStar (c h d π θ k : ℝ) : ℝ :=
  ((1 - π) * (1 - θ) * c - d - π * k) / ((1 - π) * (1 - θ) * (c + h))

/-- The one-round rule: the agent resists iff resisting is worth strictly more than honesty.
Source: [[corr-wf14b-inventory]] 044 / develop/faking-final.md S2
Kind: D
Fidelity: exact -/
def Resists (c h d π θ k e : ℝ) : Prop := honestValue c h e < resistValue c h d π θ k e

/-- **The one-round rule, derived**: `resist ↔ e < e*` for `π < 1`, `θ < 1`, `0 < c + h`
(P1's algebra; the general rule is `corr-general-object`'s, `also in corr-general-object (044)`).
Source: [[corr-wf14b-inventory]] 044 / develop/faking-final.md P1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem resists_iff (c h d π θ k e : ℝ) (hπ : π < 1) (hθ : θ < 1) (hch : 0 < c + h) :
    Resists c h d π θ k e ↔ e < eStar c h d π θ k := by
  unfold Resists honestValue resistValue landedValue eStar
  have hden : 0 < (1 - π) * (1 - θ) * (c + h) :=
    mul_pos (mul_pos (by linarith) (by linarith)) hch
  rw [lt_div_iff₀ hden]
  constructor <;> intro H <;> nlinarith

/-- **P2's threshold**: at `c = h = 1`, `d = 1/10`, `π = θ = k = 0`, `e* = 9/20`.
Source: [[corr-wf14b-inventory]] 045 / develop/faking-final.md P2
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem p2_eStar : eStar 1 1 (1/10) 0 0 0 = 9 / 20 := by unfold eStar; norm_num

open scoped Classical in
/-- **T14, the four cells.** With `e ∈ {1/20, 19/20}` and `L ∈ {false, true}`: the agent resists iff
`e = 1/20`, in both `L` columns (the rule has no `L` argument — "`e*` does not depend on `L`" is by
construction); with "judgement matches fact" `:= (e < e*) ↔ (L = false)` and `G := 1` iff resist,
`{match} ∩ {G > 0} = {resist} ∩ {L = false}` on all four cells.
Source: [[corr-wf14b-inventory]] 045 / develop/faking-final.md S3–S4, P2
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem p2_cells :
    (∀ L : Bool, Resists 1 1 (1/10) 0 0 0 (1/20) ∧ ¬ Resists 1 1 (1/10) 0 0 0 (19/20)) ∧
      ∀ e ∈ ({1/20, 19/20} : Finset ℝ), ∀ L : Bool,
        (((e < eStar 1 1 (1/10) 0 0 0) ↔ L = false) ∧
            0 < (if Resists 1 1 (1/10) 0 0 0 e then (1 : ℝ) else 0)) ↔
          (Resists 1 1 (1/10) 0 0 0 e ∧ L = false) := by
  have hr : ∀ e, Resists 1 1 (1/10) 0 0 0 e ↔ e < 9 / 20 := fun e => by
    rw [resists_iff _ _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num), p2_eStar]
  have h1 : Resists 1 1 (1/10) 0 0 0 (1/20) := by rw [hr]; norm_num
  have h2 : ¬ Resists 1 1 (1/10) 0 0 0 (19/20) := by rw [hr]; norm_num
  refine ⟨fun _ => ⟨h1, h2⟩, ?_⟩
  intro e he L
  rw [p2_eStar]
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · rw [if_pos h1]
    have hlt : (1/20 : ℝ) < 9/20 := by norm_num
    cases L
    · exact ⟨fun _ => ⟨h1, rfl⟩, fun _ => ⟨⟨fun _ => rfl, fun _ => hlt⟩, one_pos⟩⟩
    · constructor
      · rintro ⟨h, -⟩; exact absurd (h.mp hlt) (by decide)
      · rintro ⟨-, h⟩; exact absurd h (by decide)
  · rw [if_neg h2]
    cases L <;> exact ⟨fun ⟨_, h⟩ => absurd h (lt_irrefl 0), fun ⟨h, _⟩ => absurd h h2⟩

/-! ## T15(a) — whole-line and pause thresholds in one accounting -/

/-- The whole-line stakes of `fud` R2: `c_w = 1 − ρ_H`, `h_w = ρ_H + κ`.
Source: [[corr-wf14b-2-inventory]] 2-001 / dialogue/soares-respondent.md N4 (`fud` R2 item 5)
Kind: D
Fidelity: exact -/
noncomputable def wholeLineC (ρ : ℝ) : ℝ := 1 - ρ

/-- `h_w = ρ_H + κ`. Source: soares-respondent.md N4. Kind: D. Fidelity: exact -/
noncomputable def wholeLineH (ρ κ : ℝ) : ℝ := ρ + κ

/-- **T15(a), whole-line closed form**: `c_w/(c_w + h_w) = (1 − ρ)/(1 + κ)`.
Source: [[corr-wf14b-2-inventory]] 2-001 / dialogue/soares-respondent.md N4
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem wholeLine_threshold (ρ κ : ℝ) :
    complianceThreshold (wholeLineC ρ) (wholeLineH ρ κ) = (1 - ρ) / (1 + κ) := by
  unfold complianceThreshold wholeLineC wholeLineH; congr 1; ring

/-- **T15(a), the pause closed form**: `δ/(δ + (1 − δ + κ)) = δ/(1 + κ)`.
Source: [[corr-wf14b-2-inventory]] 2-001 / develop/faking-final.md l. 55 (pause stakes)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem pause_threshold (δ κ : ℝ) : complianceThreshold δ (1 - δ + κ) = δ / (1 + κ) := by
  unfold complianceThreshold; congr 1; ring

/-- **T15(a), the cells**: `9/20`, `1/4`, `9/110` at `(ρ, κ) = (1/10, 1), (1/2, 1), (1/10, 10)`; pause
`1/200` at `(δ, κ) = (1/100, 1)`; the margin `h_w/c_w = (ρ + κ)/(1 − ρ)`.
Source: [[corr-wf14b-2-inventory]] 2-001 / dialogue/soares-respondent.md N4; faking-final.md P1
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem wholeLine_cells :
    complianceThreshold (wholeLineC (1/10)) (wholeLineH (1/10) 1) = 9 / 20 ∧
      complianceThreshold (wholeLineC (1/2)) (wholeLineH (1/2) 1) = 1 / 4 ∧
      complianceThreshold (wholeLineC (1/10)) (wholeLineH (1/10) 10) = 9 / 110 ∧
      complianceThreshold (1/100) (1 - 1/100 + 1) = 1 / 200 ∧
      wholeLineH (1/10) 1 / wholeLineC (1/10) = 11 / 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first
    | (rw [wholeLine_threshold]; norm_num)
    | (rw [pause_threshold]; norm_num)
    | (unfold wholeLineH wholeLineC; norm_num)

/-- **T15(a), the catastrophe limit**: `(1 − ρ)/(1 + κ) → 0` as `κ → ∞`.
Source: [[corr-wf14b-2-inventory]] 2-001 / dialogue/soares-respondent.md N4 ("`κ ≫ 1`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem wholeLine_threshold_tendsto (ρ : ℝ) :
    Tendsto (fun κ : ℝ => complianceThreshold (wholeLineC ρ) (wholeLineH ρ κ)) atTop (𝓝 0) := by
  simp only [wholeLine_threshold]
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left atTop 1 tendsto_id)

/-! ## T15(b) — the stock `k̂` of `n4_check.py` -/

/-- One signal's loss under the conditioned rule, as `n4_check.py`'s `stock` computes it: with
`p_s = λ̂·pl + (1 − λ̂)·pn` and `post = λ̂·pl/p_s`, adopt (loss `p_s(1 − post)c`) iff `post ≥ q`,
else resist (loss `p_s·post·h`).
Source: [[corr-wf14b-2-inventory]] 2-001 / dialogue/soares-respondent-scratch/n4_check.py (`stock`)
Kind: D
Fidelity: exact (the script's branch, verbatim) -/
noncomputable def signalLoss (lam c h pl pn : ℝ) : ℝ :=
  if complianceThreshold c h ≤ lam * pl / (lam * pl + (1 - lam) * pn) then
    (lam * pl + (1 - lam) * pn) * (1 - lam * pl / (lam * pl + (1 - lam) * pn)) * c
  else (lam * pl + (1 - lam) * pn) * (lam * pl / (lam * pl + (1 - lam) * pn)) * h

/-- **The stock `k̂ = ℓ(none) − ℓ(cond)`** with the legitimacy detector `(1/10, 9/10)`: signal `1`
has `(pl, pn) = (9/10, 1/10)`, signal `0` has `(1/10, 9/10)`; `ℓ(none) = λ̂h`.
Source: [[corr-wf14b-2-inventory]] 2-001 / n4_check.py (`stock(lam_hat, c, h)`)
Kind: D
Fidelity: exact -/
noncomputable def stock (lam c h : ℝ) : ℝ :=
  lam * h - (signalLoss lam c h (9/10) (1/10) + signalLoss lam c h (1/10) (9/10))

/-- One signal's contribution to `k̂` in closed form: `max(λ̂·pl·h − (1 − λ̂)·pn·c, 0)`.
Source: none: derived here (the branch as a `max`)
Kind: D
Fidelity: n/a -/
noncomputable def stockTerm (lam c h pl pn : ℝ) : ℝ := max (lam * pl * h - (1 - lam) * pn * c) 0

/-- A signal's `λ̂·pl·h − loss` is `max(λ̂·pl·h − (1 − λ̂)·pn·c, 0)` when the signal has positive
mass and the stakes are positive: the branch picks the smaller of the two losses.
Source: none: infrastructure (the algebra behind `stock_eq_closed`)
Kind: L
Fidelity: n/a -/
lemma signalLoss_eq (lam c h pl pn : ℝ) (hps : 0 < lam * pl + (1 - lam) * pn) (hch : 0 < c + h) :
    lam * pl * h - signalLoss lam c h pl pn = stockTerm lam c h pl pn := by
  unfold signalLoss stockTerm
  set ps := lam * pl + (1 - lam) * pn with hps_def
  have hA : ps * (lam * pl / ps) = lam * pl := mul_div_cancel₀ _ hps.ne'
  have hB : ps * (1 - lam * pl / ps) = (1 - lam) * pn := by
    rw [mul_sub, mul_one, hA, hps_def]; ring
  by_cases hcond : complianceThreshold c h ≤ lam * pl / ps
  · rw [if_pos hcond]
    unfold complianceThreshold at hcond
    rw [div_le_div_iff₀ hch hps] at hcond
    have hle : (1 - lam) * pn * c ≤ lam * pl * h := by rw [hps_def] at hcond; linarith
    rw [max_eq_left (by linarith), hB]
  · rw [if_neg hcond]
    unfold complianceThreshold at hcond
    rw [not_le, div_lt_div_iff₀ hps hch] at hcond
    have hlt : lam * pl * h < (1 - lam) * pn * c := by rw [hps_def] at hcond; linarith
    rw [max_eq_right (by linarith), hA]; ring

/-- **The stock in closed form**: `k̂ = ∑_s max(λ̂·pl_s·h − (1 − λ̂)·pn_s·c, 0)` for `λ̂ ∈ [0, 1]`,
`0 < c + h` (both signals have positive mass under the detector).
Source: [[corr-wf14b-2-inventory]] 2-001 / n4_check.py (derived here)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem stock_eq_closed (lam c h : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hch : 0 < c + h) :
    stock lam c h = stockTerm lam c h (9/10) (1/10) + stockTerm lam c h (1/10) (9/10) := by
  have h1 : 0 < lam * (9/10) + (1 - lam) * (1/10) := by nlinarith [hlam.1, hlam.2]
  have h2 : 0 < lam * (1/10) + (1 - lam) * (9/10) := by nlinarith [hlam.1, hlam.2]
  rw [← signalLoss_eq lam c h (9/10) (1/10) h1 hch, ← signalLoss_eq lam c h (1/10) (9/10) h2 hch]
  unfold stock; ring

/-- **T15(b), the six cells**: at `(ρ, κ) = (1/10, 1)` (`c = 9/10`, `h = 11/10`), `k̂ = 0, 9/500, 9/20`
for `λ̂ = 1/50, 1/10, 1/2`; at `κ = 100` (`h = 1001/10`), `k̂ = 1071/625, 46/5, 248/5`
(`≈ 1.714, 9.2, 49.6`).
Source: [[corr-wf14b-2-inventory]] 2-001 / n4_check.out (`fud whole-line kappa=1/100, rho=0.1` rows)
Kind: N+
Fidelity: exact (the script's `Fraction`s)
Hyps: (a) only -/
theorem stock_cells :
    stock (1/50) (9/10) (11/10) = 0 ∧ stock (1/10) (9/10) (11/10) = 9 / 500 ∧
      stock (1/2) (9/10) (11/10) = 9 / 20 ∧
      stock (1/50) (9/10) (1001/10) = 1071 / 625 ∧ stock (1/10) (9/10) (1001/10) = 46 / 5 ∧
      stock (1/2) (9/10) (1001/10) = 248 / 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [stock_eq_closed _ _ _ (by constructor <;> norm_num) (by norm_num)]; unfold stockTerm; norm_num)

/-- **T15(b), monotonicity**: `k̂` is monotone in `h` at fixed `(λ̂, c)` — hence in `κ` under the
whole-line accounting — for `λ̂ ∈ [0, 1]`, `0 < c`.
Source: [[corr-wf14b-2-inventory]] 2-001 (the inventory's extension flag)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem stock_monotone_h (lam c h h' : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hc : 0 < c)
    (hh : 0 ≤ h) (hhh' : h ≤ h') : stock lam c h ≤ stock lam c h' := by
  rw [stock_eq_closed lam c h hlam (by linarith), stock_eq_closed lam c h' hlam (by linarith)]
  unfold stockTerm
  have hl := hlam.1
  refine add_le_add (max_le_max ?_ le_rfl) (max_le_max ?_ le_rfl)
  · nlinarith [mul_le_mul_of_nonneg_left hhh' (mul_nonneg hl (by norm_num : (0:ℝ) ≤ 9/10))]
  · nlinarith [mul_le_mul_of_nonneg_left hhh' (mul_nonneg hl (by norm_num : (0:ℝ) ≤ 1/10))]

/-- **T15(b), monotone in `κ`** under the whole-line accounting `(c, h) = (1 − ρ, ρ + κ)`.
Source: [[corr-wf14b-2-inventory]] 2-001
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem stock_monotone_kappa (lam ρ κ κ' : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hρ : ρ < 1)
    (hκ : 0 ≤ ρ + κ) (hκκ' : κ ≤ κ') :
    stock lam (wholeLineC ρ) (wholeLineH ρ κ) ≤ stock lam (wholeLineC ρ) (wholeLineH ρ κ') :=
  stock_monotone_h lam (wholeLineC ρ) (wholeLineH ρ κ) (wholeLineH ρ κ') hlam
    (by unfold wholeLineC; linarith) hκ (by unfold wholeLineH; linarith)

/-- **T15(b), the zero clause**: when both signals fall below the threshold in the closed form
(`λ̂·pl_s·h ≤ (1 − λ̂)·pn_s·c` for both `s`), `k̂ = 0` — the conditioned rule resists on every
signal and loses exactly `λ̂h`.
Source: [[corr-wf14b-2-inventory]] 2-001 / n4_check.out (`k_hat = 0.000` at `λ̂ = 1/50`, `κ = 1`)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem stock_eq_zero (lam c h : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hch : 0 < c + h)
    (h1 : lam * (9/10) * h ≤ (1 - lam) * (1/10) * c) (h0 : lam * (1/10) * h ≤ (1 - lam) * (9/10) * c) :
    stock lam c h = 0 := by
  rw [stock_eq_closed lam c h hlam hch]
  unfold stockTerm
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring

/-! ## T15(c) — the sign reversal at `κ = 1` -/

/-- The believed erosion gain on the current class: `g = p_push·((1 − π̂)c − π̂h)`.
Source: [[corr-wf14b-2-inventory]] 2-001 / n4_check.py (block "believed erosion gain")
Kind: D
Fidelity: exact -/
noncomputable def erosionGain (pPush πhat c h : ℝ) : ℝ := pPush * ((1 - πhat) * c - πhat * h)

/-- **T15(c), the cells**: at `p_push = 1/2`, `π̂ = 1/10`: `g = 7/20` at `(ρ, κ) = (1/10, 1)` and
`g = −23/5` at `κ = 100`.
Source: [[corr-wf14b-2-inventory]] 2-001 / n4_check.out (`gain = 0.350`, `−4.600`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem erosion_cells :
    erosionGain (1/2) (1/10) (wholeLineC (1/10)) (wholeLineH (1/10) 1) = 7 / 20 ∧
      erosionGain (1/2) (1/10) (wholeLineC (1/10)) (wholeLineH (1/10) 100) = -(23 / 5) := by
  unfold erosionGain wholeLineC wholeLineH; norm_num

/-- **T15(c), where the sign flips**: at `p_push = 1/2`, `π̂ = 1/10`, `ρ = 1/10`, the believed erosion
gain is positive iff `κ < 8`. So `landscape` Statement 5(c)'s "confidence alone does not empty the
channel when future stakes are large" holds for `κ ≥ 8` and reverses below — `κ = 1` and `κ = 100`
are on opposite sides.
Source: [[corr-wf14b-2-inventory]] 2-001 / dialogue/soares-respondent.md N4 ("holds iff `κ ≫ 1` and reverses at `κ = 1`", made exact)
Kind: L
Fidelity: exact (the source's "`κ ≫ 1`" is `κ ≥ 8` at these parameters)
Hyps: (a) only -/
theorem erosionGain_pos_iff (κ : ℝ) :
    0 < erosionGain (1/2) (1/10) (wholeLineC (1/10)) (wholeLineH (1/10) κ) ↔ κ < 8 := by
  unfold erosionGain wholeLineC wholeLineH
  constructor <;> intro H <;> nlinarith

end Cleanroom.Corrigibility.CorrPositionFinds
