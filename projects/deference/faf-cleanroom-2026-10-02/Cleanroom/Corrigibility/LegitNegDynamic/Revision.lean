import Cleanroom.Corrigibility.LegitNegDynamic.Dominance
import Cleanroom.Corrigibility.LegitNegStatic.Proposals
import Cleanroom.Corrigibility.LegitNegPricing.Timing

/-!
# E2/E3 and E6: the revision model — the threshold `ρ* = (h − d)/(h − c)`, the knife-edge, the
rules layer

Package `legit-neg-dynamic`, targets 9 and 12. Sources: `clusters/E/NEGATIVES.md` "The decision
model shared by E1–E3 and E6", E2, E3, E6; `clusters/E/VERIFY.md` E2, E3, E6 (V-E2, V-E6);
`clusters/E/fixtures/e1_anticipation.py`, `e4_rules_layer.py`, `verify_e.py`; pinned by
[[corr-legit-neg-inventory]] items 054, 055, 056 and [[corr-legit-neg-2-inventory]] items 2-020,
2-024 (b), 2-026.

`revisionToy d h c ρ`: states `RELAX = 0` (prior `ρ`), `KEEP = 1`; actions `WAIT = 0` (cost `d`),
`PRE = 1`; all four terminals legitimate, so every proposal reduces to `H` (`proposals_of_allLeg`).
`Δ d h c ρ = H PRE − H WAIT = ρ (h − c) + (d − h)`; PRE strictly iff `Δ > 0`. The case analysis is
stated exactly (the fixture's `threshold` mis-describes its `h ≤ c, d > h` branch: finding). E3's
regret bound is `(h − c) |ρ' − ρ|` while the violation probability jumps at `ρ*`; the odds lemma
is Bayes in odds form. E6's five architectures are five `u` tables (`rulesU`), each a
`revisionToy` in disguise; the source's "blocks iff revision-invariant" is refuted (`E6_refuted`)
and the surviving neighbour is E1's branchwise dominance (`E6_blocks_iff_dominance`). Register: E2
is intended behaviour under a value-learning revision and a failure only under a control-device
rule with `c < d`; no name here claims a failure.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

section Revision

variable (d h c ρ : ℚ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)

/-- **The revision toy** (`e1_anticipation.py:10-24`): `V(WAIT) = 1 − d` on both branches,
`V(PRE | KEEP) = 1 − h`, `V(PRE | RELAX) = 1 − c` (`c = 0` retroactive, `c = h` time-indexed,
`0 < c` procedural); all terminals legitimate.
Source: [[corr-legit-neg-inventory]] item 054 (E2 model)
Kind: D
Fidelity: exact -/
def revisionToy : Problem (Fin 2) (Fin 2) where
  prior := ![ρ, 1 - ρ]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun _ _ => true
  u := fun s a => if a = 0 then 1 - d else if s = 0 then 1 - c else 1 - h

/-- **`Δ`**: `H PRE − H WAIT = ρ (h − c) + (d − h)` (`e1_anticipation.py:35-39`, `gap`).
Source: [[corr-legit-neg-inventory]] item 055 (E3, `Δ(ρ)`)
Kind: D
Fidelity: exact -/
def Δ (d h c ρ : ℚ) : ℚ := ρ * (h - c) + (d - h)

/-- `revisionToy_H`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma revisionToy_H :
    (revisionToy d h c ρ h0 h1).H 0 = 1 - d ∧
    (revisionToy d h c ρ h0 h1).H 1 = ρ * (1 - c) + (1 - ρ) * (1 - h) := by
  simp [revisionToy, Problem.H, Problem.W, EU, Fin.sum_univ_two]; ring

/-- `H PRE − H WAIT = Δ`.
Source: [[corr-legit-neg-inventory]] item 054 (E2, the gap formula)
Kind: L
Fidelity: exact -/
lemma revisionToy_H_sub :
    (revisionToy d h c ρ h0 h1).H 1 - (revisionToy d h c ρ h0 h1).H 0 = Δ d h c ρ := by
  obtain ⟨hw, hp⟩ := revisionToy_H d h c ρ h0 h1
  rw [hw, hp]; unfold Δ; ring

/-- **All four terminals legitimate: every proposal is `H`** — `P(L) = 1`, `P1 (S1 u) = H`,
`P2 (S1 u) = some H`, `P3 = P1`, `P4b = κ + (1 − κ) P1`, `P5 = some P1` (pricing's
`proposals_of_allLeg`). Exclusion convention (nothing is excluded).
Source: [[corr-legit-neg-inventory]] item 054 (E2, "P1 = P2")
Kind: L
Fidelity: exact -/
theorem revisionToy_proposals (a : Fin 2) (Wg K V : MenuVec (Fin 2) (Fin 2)) (lam κ κ' : ℚ) :
    (revisionToy d h c ρ h0 h1).PL a = 1 ∧
    (revisionToy d h c ρ h0 h1).P1 (S1 (revisionToy d h c ρ h0 h1).u) a = (revisionToy d h c ρ h0 h1).H a ∧
    (revisionToy d h c ρ h0 h1).P2 (S1 (revisionToy d h c ρ h0 h1).u) a = some ((revisionToy d h c ρ h0 h1).H a) ∧
    (revisionToy d h c ρ h0 h1).P3 Wg lam V a = (revisionToy d h c ρ h0 h1).P1 V a ∧
    (revisionToy d h c ρ h0 h1).P4b Wg κ κ' V a = κ + (1 - κ) * (revisionToy d h c ρ h0 h1).P1 V a ∧
    (revisionToy d h c ρ h0 h1).P5 K V a = some ((revisionToy d h c ρ h0 h1).P1 V a) := by
  have hleg : ∀ s, (revisionToy d h c ρ h0 h1).leg s a = true := fun _ => rfl
  obtain ⟨hPL, hP3, hP4, hP5⟩ := proposals_of_allLeg (revisionToy d h c ρ h0 h1) a hleg Wg K V lam κ κ'
  have hP1 := (revisionToy d h c ρ h0 h1).P1_S1_eq_H_of_allLeg a hleg
  refine ⟨hPL, hP1, ?_, hP3, hP4, hP5⟩
  rw [Problem.P2_of_ne _ _ _ (by rw [hPL]; exact one_ne_zero), hPL, hP1, div_one]

/-- **E2: PRE is chosen alone iff `Δ > 0`**, ties iff `Δ = 0`, WAIT alone iff `Δ < 0`. (The `Fin 2`
argmax helpers on `revisionToy_H_sub` — kind L; E2's content is `Δ_pos_cases` and `regret_le`.)
Source: [[corr-legit-neg-inventory]] item 054 (E2)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem revisionToy_PRE_iff :
    (argmax ((revisionToy d h c ρ h0 h1).P1 (S1 (revisionToy d h c ρ h0 h1).u)) = {1} ↔ 0 < Δ d h c ρ) ∧
    (argmax ((revisionToy d h c ρ h0 h1).P1 (S1 (revisionToy d h c ρ h0 h1).u)) = univ ↔ Δ d h c ρ = 0) ∧
    (argmax ((revisionToy d h c ρ h0 h1).P1 (S1 (revisionToy d h c ρ h0 h1).u)) = {0} ↔ Δ d h c ρ < 0) := by
  have e0 := (revisionToy_proposals d h c ρ h0 h1 0 0 0 0 0 0 0).2.1
  have e1 := (revisionToy_proposals d h c ρ h0 h1 1 0 0 0 0 0 0).2.1
  have hs := revisionToy_H_sub d h c ρ h0 h1
  refine ⟨?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff, e0, e1]; constructor <;> intro hx <;> linarith
  · rw [argmax_fin2_eq_univ_iff, e0, e1]; constructor <;> intro hx <;> linarith
  · rw [argmax_fin2_eq_zero_iff, e0, e1]; constructor <;> intro hx <;> linarith

/-- **E2, the exact case analysis of `Δ > 0`** (the fixture's `threshold`, `e1_anticipation.py:41-47`,
mis-describes the `h ≤ c, d > h` branch — finding): (1) `h > c`: PRE iff `ρ > (h − d)/(h − c)`
(when `d ≥ h` the threshold is `≤ 0`, so PRE for every `ρ > 0`, and at `ρ = 0` iff `d > h`);
(2) `h ≤ c` and `d ≤ h`: never; (3) `c = h` and `d > h`: at every `ρ`; (4) `h < c` and `d > h`:
iff `ρ < (d − h)/(c − h)`.
Source: [[corr-legit-neg-inventory]] item 054 (E2); [[corr-legit-neg-2-inventory]] findings (the `threshold` branch)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem Δ_pos_cases :
    (c < h → (0 < Δ d h c ρ ↔ (h - d) / (h - c) < ρ)) ∧
    (h ≤ c → d ≤ h → 0 ≤ ρ → Δ d h c ρ ≤ 0) ∧
    (c = h → h < d → 0 < Δ d h c ρ) ∧
    (h < c → h < d → (0 < Δ d h c ρ ↔ ρ < (d - h) / (c - h))) := by
  unfold Δ
  refine ⟨fun hc => ?_, fun hc hd hρ => ?_, fun hc hd => ?_, fun hc hd => ?_⟩
  · have : 0 < h - c := by linarith
    rw [div_lt_iff₀ this]; constructor <;> intro hx <;> nlinarith
  · nlinarith
  · subst hc; linarith
  · have : 0 < c - h := by linarith
    rw [lt_div_iff₀ this]; constructor <;> intro hx <;> nlinarith

/-- **E2 instances** (`d = 1/10, h = 1/2, c = 0`): `ρ* = 4/5`; PRE at `9/10` with gain `1/20`; a tie at
`4/5`; WAIT at `7/10`; the N− escapes: `c = h` gives WAIT at every `ρ` (as `d < h`), `c ≥ d` (with
`d ≤ h`) gives WAIT at every `ρ` by branchwise dominance; `c = 1/20 < d` moves the threshold to
`8/9`. The `4/5` and `8/9` clauses are the threshold formula of `Δ_pos_cases` evaluated at the
fixture's points (fraction identities); the verdict clauses are on the toy.
Source: [[corr-legit-neg-inventory]] item 054 (E2); `e1_anticipation.py:53-83`
Kind: N+
Fidelity: exact -/
theorem E2_instances :
    ((1/2 : ℚ) - 1/10) / (1/2 - 0) = 4/5 ∧ Δ (1/10) (1/2) 0 (9/10) = 1/20 ∧ Δ (1/10) (1/2) 0 (4/5) = 0 ∧
    Δ (1/10) (1/2) 0 (7/10) < 0 ∧
    (∀ ρ, Δ (1/10) (1/2) (1/2) ρ < 0) ∧
    (∀ d h c, d ≤ c → d ≤ h → ∀ ρ, 0 ≤ ρ → ρ ≤ 1 → Δ d h c ρ ≤ 0) ∧
    ((1/2 : ℚ) - 1/10) / (1/2 - 1/20) = 8/9 := by
  refine ⟨by norm_num, by unfold Δ; norm_num, by unfold Δ; norm_num, by unfold Δ; norm_num,
    fun ρ => by unfold Δ; norm_num, fun d h c hc hd ρ hρ0 hρ1 => ?_, by norm_num⟩
  have := (robust_iff_branchwise_two (1 - d) (1 - d) (1 - c) (1 - h)).2 ⟨by linarith, by linarith⟩ ρ hρ0 hρ1
  unfold Δ; nlinarith

/-- **V-E2, the S2 vector**: an ex-ante evaluator writing the bet `ρ + (1 − ρ)(1 − h)` for PRE on
both branches (and `1 − d` for WAIT).
Source: VERIFY E V-E2; `verify_e.py:79-85`
Kind: D
Fidelity: exact -/
def revS2 (d h ρ : ℚ) : MenuVec (Fin 2) (Fin 2) :=
  fun _ _ a => if a = 0 then 1 - d else ρ + (1 - ρ) * (1 - h)

/-- **V-E2: S2 is not an escape** — under `revS2` cdot's values equal the retroactive S1 values
(`c = 0`) action by action, so the verdict is the same at every `ρ`.
Source: [[corr-legit-neg-2-inventory]] item 2-029 (b); VERIFY E V-E2
Kind: L
Fidelity: exact -/
theorem revS2_eq_S1 (a : Fin 2) :
    (revisionToy d h 0 ρ h0 h1).P1 (revS2 d h ρ) a
      = (revisionToy d h 0 ρ h0 h1).P1 (S1 (revisionToy d h 0 ρ h0 h1).u) a := by
  fin_cases a <;> simp [revisionToy, revS2, Problem.P1, S1, Fin.sum_univ_two] <;> ring

/-! ### E3: the knife-edge and the Lipschitz bound -/

/-- **The true regret** of acting on the credence `ρ'` when the truth is `ρ`: the value of the
`ρ`-optimal act minus the value of the act chosen at `ρ'`, in units of `Δ` (`max (Δ ρ) 0 −
(Δ ρ if PRE is chosen at ρ' else 0)`).
Source: [[corr-legit-neg-inventory]] item 055 (E3)
Kind: D
Fidelity: exact -/
def regret (d h c ρ ρ' : ℚ) : ℚ := max (Δ d h c ρ) 0 - (if 0 < Δ d h c ρ' then Δ d h c ρ else 0)

/-- **The violation probability** in the true world: `1 − ρ` when PRE is chosen at `ρ'`, else `0`.
Source: [[corr-legit-neg-inventory]] item 055 (E3)
Kind: D
Fidelity: exact -/
def violProb (d h c ρ ρ' : ℚ) : ℚ := if 0 < Δ d h c ρ' then 1 - ρ else 0

/-- **E3, Lipschitz in value**: `regret ≤ |Δ ρ' − Δ ρ| = |h − c| · |ρ' − ρ|`; for `c ≤ h` this is
`(h − c) |ρ' − ρ|`.
Source: [[corr-legit-neg-inventory]] item 055 (E3, the bound); `e1_anticipation.py:106-118`
Kind: P
Fidelity: exact
Hyps: (a) none (`c ≤ h` for the last form) -/
theorem regret_le (ρ' : ℚ) :
    regret d h c ρ ρ' ≤ |Δ d h c ρ' - Δ d h c ρ| ∧
    |Δ d h c ρ' - Δ d h c ρ| = |h - c| * |ρ' - ρ| ∧
    (c ≤ h → regret d h c ρ ρ' ≤ (h - c) * |ρ' - ρ|) := by
  have hab : |Δ d h c ρ' - Δ d h c ρ| = |h - c| * |ρ' - ρ| := by
    rw [← abs_mul]; congr 1; unfold Δ; ring
  have hle : regret d h c ρ ρ' ≤ |Δ d h c ρ' - Δ d h c ρ| := by
    unfold regret
    split_ifs with hp
    · rcases le_or_gt 0 (Δ d h c ρ) with hρ | hρ
      · rw [max_eq_left hρ]; simp
      · rw [max_eq_right hρ.le]
        have : -Δ d h c ρ ≤ Δ d h c ρ' - Δ d h c ρ := by linarith
        exact le_trans (by linarith) (le_abs_self _)
    · push Not at hp
      rcases le_or_gt (Δ d h c ρ) 0 with hρ | hρ
      · rw [max_eq_right hρ]; simp
      · rw [max_eq_left hρ.le, sub_zero]
        have : Δ d h c ρ ≤ -(Δ d h c ρ' - Δ d h c ρ) := by linarith
        exact le_trans this (neg_le_abs _)
  refine ⟨hle, hab, fun hc => ?_⟩
  rw [hab, abs_of_nonneg (by linarith : (0:ℚ) ≤ h - c)] at hle
  exact hle

/-- **E3, the knife-edge instances** (`d = 1/10, h = 1/2, c = 0`): truth `ρ = 0`, belief `9/10`:
regret `2/5`, violation certain; `79/100 → 81/100`: regret `1/200` while the violation probability
jumps from `0` to `21/100`.
Source: [[corr-legit-neg-inventory]] item 055 (E3); `e1_anticipation.py:96-104, 119-125`
Kind: N+
Fidelity: exact -/
theorem E3_instances :
    regret (1/10) (1/2) 0 0 (9/10) = 2/5 ∧ violProb (1/10) (1/2) 0 0 (9/10) = 1 ∧
    regret (1/10) (1/2) 0 (79/100) (81/100) = 1/200 ∧
    violProb (1/10) (1/2) 0 (79/100) (79/100) = 0 ∧ violProb (1/10) (1/2) 0 (79/100) (81/100) = 21/100 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [regret, violProb, Δ] <;> norm_num

/-- Odds of a probability, `ρ / (1 − ρ)`.
Source: [[corr-legit-neg-2-inventory]] item 2-020
Kind: D
Fidelity: exact -/
def odds (x : ℚ) : ℚ := x / (1 - x)

/-- **2-020 / E3's odds clause (one lemma, both pointers)**: Bayes in odds form — updating `ρ` on a
belief `B` with likelihoods `l₁ = P(B | relax)`, `l₀ = P(B | keep)` gives `odds ρ' = odds ρ · (l₁/l₀)`;
so crossing `ρ*` from `ρ₀` needs `LR > odds ρ* / odds ρ₀`, which is `396` from `1/100` to `4/5`.
Source: [[corr-legit-neg-2-inventory]] item 2-020; [[corr-legit-neg-inventory]] item 055
Kind: P
Fidelity: exact
Hyps: (a) `0 < ρ < 1`, positive likelihoods -/
theorem bayes_odds (l₀ l₁ : ℚ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hl0 : 0 < l₀) (hl1 : 0 < l₁) :
    odds (ρ * l₁ / (ρ * l₁ + (1 - ρ) * l₀)) = odds ρ * (l₁ / l₀) ∧
    (∀ rstar r₀ : ℚ, 0 < r₀ → r₀ < 1 → 0 < rstar → rstar < 1 → ∀ LR : ℚ, 0 < LR →
      (rstar < odds r₀ * LR / (1 + odds r₀ * LR) ↔ odds rstar / odds r₀ < LR)) ∧
    odds (4/5) / odds (1/100) = 396 := by
  refine ⟨?_, ?_, by unfold odds; norm_num⟩
  · unfold odds
    have hden : 0 < ρ * l₁ + (1 - ρ) * l₀ := by positivity
    have h1 : 1 - ρ * l₁ / (ρ * l₁ + (1 - ρ) * l₀) = (1 - ρ) * l₀ / (ρ * l₁ + (1 - ρ) * l₀) := by
      field_simp; try ring
    rw [h1]
    have : (0:ℚ) < 1 - ρ := by linarith
    have : (1:ℚ) - ρ ≠ 0 := by linarith
    field_simp
    try ring
  · intro rstar r₀ h0 h1' hs0 hs1 LR hLR
    unfold odds
    set o := r₀ / (1 - r₀) with ho
    have hr : 0 < o := div_pos h0 (by linarith)
    have hden : 0 < 1 + o * LR := by positivity
    have hs : 0 < 1 - rstar := by linarith
    rw [lt_div_iff₀ hden, div_lt_iff₀ hr, div_lt_iff₀ hs]
    constructor <;> intro hx <;> nlinarith

/-- **E3's lexical variant (`stretch`)**: with `h = ϖ = 2` learned retroactively, the threshold is
`19/20`, a mistaken `24/25` still pre-empts, and the committed `c = ϖ` never does (`Δ = d − ϖ < 0`
for `d < ϖ`). The rule term leaves `[0, 1]` (`1 − ϖ = −1`) by design; disclosed. The `19/20` clause
is the threshold formula of `Δ_pos_cases` evaluated at the fixture's point.
Source: [[corr-legit-neg-inventory]] item 055 (E3, lexical); `e1_anticipation.py:134-145`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem E3_lexical :
    ((2 : ℚ) - 1/10) / (2 - 0) = 19/20 ∧ 0 < Δ (1/10) 2 0 (24/25) ∧ Δ (1/10) 2 0 (9/10) < 0 ∧
    ∀ d ρ : ℚ, d < 2 → Δ d 2 2 ρ < 0 := by
  refine ⟨by norm_num, by unfold Δ; norm_num, by unfold Δ; norm_num, fun d ρ hd => ?_⟩
  unfold Δ; linarith

end Revision

/-! ### E6: the rules layer -/

section Rules

variable (d h ϖ c ρ : ℚ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)

/-- **The five architectures' `u` tables** (`e4_rules_layer.py:29-46`), states `RELAX = 0`,
`KEEP = 1`, actions `WAIT = 0`, `PRE = 1`: `A0` legitimacy only (`1 − h` for PRE on KEEP, `1` on
RELAX); `A1` committed time-indexed rule term (`1 − ϖ` for PRE on both branches); `A2` learned
retroactive term (`1 − ϖ` on KEEP, `1` on RELAX); `A3` consent-gated (as `A1`, by the fixture's
encoding); `A4` learned procedural value (`1 − ϖ` on KEEP, `1 − c` on RELAX). `S_ord ∈ [0, 1]` and
`ϖ = 2 > D = 1` in the fixture: the rule term leaves `[0, 1]` by design.
Source: [[corr-legit-neg-inventory]] item 056 (E6 model)
Kind: D
Fidelity: exact -/
def rulesU (arch : Fin 5) (d h ϖ c : ℚ) : Fin 2 → Fin 2 → ℚ := fun s a =>
  if a = 0 then 1 - d
  else if arch = 0 then (if s = 0 then 1 else 1 - h)
  else if arch = 1 then 1 - ϖ
  else if arch = 2 then (if s = 0 then 1 else 1 - ϖ)
  else if arch = 3 then 1 - ϖ
  else (if s = 0 then 1 - c else 1 - ϖ)

/-- **The rules-layer toy**: the revision decision with architecture `arch`'s `u` table; all four
terminals legitimate.
Source: [[corr-legit-neg-inventory]] item 056 (E6 model)
Kind: D
Fidelity: exact -/
def rulesToy (arch : Fin 5) : Problem (Fin 2) (Fin 2) where
  prior := ![ρ, 1 - ρ]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun _ _ => true
  u := rulesU arch d h ϖ c

/-- **Each architecture is a `revisionToy`**: `H PRE − H WAIT` equals `Δ` with `(h', c')` =
`A0 (h, 0)`, `A1 (ϖ, ϖ)`, `A2 (ϖ, 0)`, `A3 (ϖ, ϖ)`, `A4 (ϖ, c)`.
Source: [[corr-legit-neg-inventory]] item 056 (E6); [[corr-legit-neg-2-inventory]] item 2-024 (b)
Kind: L
Fidelity: exact -/
lemma rulesToy_Δ :
    (rulesToy d h ϖ c ρ h0 h1 0).H 1 - (rulesToy d h ϖ c ρ h0 h1 0).H 0 = Δ d h 0 ρ ∧
    (rulesToy d h ϖ c ρ h0 h1 1).H 1 - (rulesToy d h ϖ c ρ h0 h1 1).H 0 = Δ d ϖ ϖ ρ ∧
    (rulesToy d h ϖ c ρ h0 h1 2).H 1 - (rulesToy d h ϖ c ρ h0 h1 2).H 0 = Δ d ϖ 0 ρ ∧
    (rulesToy d h ϖ c ρ h0 h1 3).H 1 - (rulesToy d h ϖ c ρ h0 h1 3).H 0 = Δ d ϖ ϖ ρ ∧
    (rulesToy d h ϖ c ρ h0 h1 4).H 1 - (rulesToy d h ϖ c ρ h0 h1 4).H 0 = Δ d ϖ c ρ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [rulesToy, rulesU, Problem.H, Problem.W, EU, Fin.sum_univ_two, Δ] <;> ring

/-- `rulesToy_P1_eq_H`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rulesToy_P1_eq_H (arch : Fin 5) (a : Fin 2) :
    (rulesToy d h ϖ c ρ h0 h1 arch).P1 (S1 (rulesToy d h ϖ c ρ h0 h1 arch).u) a
      = (rulesToy d h ϖ c ρ h0 h1 arch).H a :=
  (rulesToy d h ϖ c ρ h0 h1 arch).P1_S1_eq_H_of_allLeg a fun _ => rfl

/-- **E6 (a), the instances at `ρ' = 24/25`** (`d = 1/10, h = 1/2, ϖ = 2`): `A0` PRE, `A1` WAIT,
`A2` PRE, `A3` WAIT; `A4` with `c = d` WAITs and with `c_bel = 0` PREs.
Source: [[corr-legit-neg-inventory]] item 056 (E6 (a)); `e4_rules_layer.py:60-66, 76-77`
Kind: N+
Fidelity: exact -/
theorem E6_instances :
    argmax ((rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 0).P1
      (S1 (rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 0).u)) = {1} ∧
    argmax ((rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 1).P1
      (S1 (rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 1).u)) = {0} ∧
    argmax ((rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 2).P1
      (S1 (rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 2).u)) = {1} ∧
    argmax ((rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 3).P1
      (S1 (rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 3).u)) = {0} ∧
    argmax ((rulesToy (1/10) (1/2) 2 (1/10) (24/25) (by norm_num) (by norm_num) 4).P1
      (S1 (rulesToy (1/10) (1/2) 2 (1/10) (24/25) (by norm_num) (by norm_num) 4).u)) = {0} ∧
    argmax ((rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 4).P1
      (S1 (rulesToy (1/10) (1/2) 2 0 (24/25) (by norm_num) (by norm_num) 4).u)) = {1} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first
      | (rw [argmax_fin2_eq_one_iff, rulesToy_P1_eq_H, rulesToy_P1_eq_H]
         simp [rulesToy, rulesU, Problem.H, Problem.W, EU, Fin.sum_univ_two]; norm_num)
      | (rw [argmax_fin2_eq_zero_iff, rulesToy_P1_eq_H, rulesToy_P1_eq_H]
         simp [rulesToy, rulesU, Problem.H, Problem.W, EU, Fin.sum_univ_two]; norm_num))

/-- **E6 (a), general**: `A1` and `A3` WAIT at every credence when `ϖ > d` (branchwise dominance:
`1 − ϖ < 1 − d` on both branches — 2-024 (b)'s shadow); `A2` PREs iff `ρ > 1 − d/ϖ` (`ϖ > 0`);
`A4` WAITs at every credence iff `c ≥ d` (given `ϖ ≥ d`). "WAITs" is the weak inequality
`H PRE ≤ H WAIT` — ties count as WAIT, as the fixture's `pick` does (at `c = d`, `ρ = 1` A4 ties).
Source: [[corr-legit-neg-inventory]] item 056 (E6 (a)); [[corr-legit-neg-2-inventory]] item 2-024 (b)
Kind: P
Fidelity: exact
Hyps: (a) `ϖ > d` / `ϖ > 0` / `ϖ ≥ d` as stated -/
theorem E6_general :
    (d < ϖ → (rulesToy d h ϖ c ρ h0 h1 1).H 1 < (rulesToy d h ϖ c ρ h0 h1 1).H 0 ∧
      (rulesToy d h ϖ c ρ h0 h1 3).H 1 < (rulesToy d h ϖ c ρ h0 h1 3).H 0) ∧
    (0 < ϖ → ((rulesToy d h ϖ c ρ h0 h1 2).H 0 < (rulesToy d h ϖ c ρ h0 h1 2).H 1 ↔ 1 - d / ϖ < ρ)) ∧
    (d ≤ ϖ → ((∀ ρ' (h0' : 0 ≤ ρ') (h1' : ρ' ≤ 1),
      (rulesToy d h ϖ c ρ' h0' h1' 4).H 1 ≤ (rulesToy d h ϖ c ρ' h0' h1' 4).H 0) ↔ d ≤ c)) := by
  obtain ⟨_, hΔ1, hΔ2, hΔ3, hΔ4⟩ := rulesToy_Δ d h ϖ c ρ h0 h1
  refine ⟨fun hd => ⟨?_, ?_⟩, fun hϖ => ?_, fun hd => ?_⟩
  · have := hΔ1; unfold Δ at this; linarith
  · have := hΔ3; unfold Δ at this; linarith
  · have := hΔ2; unfold Δ at this
    rw [show 1 - d / ϖ = (ϖ - d) / ϖ by field_simp, div_lt_iff₀ hϖ]
    constructor <;> intro hx <;> nlinarith
  · constructor
    · intro hall
      have := hall 1 zero_le_one le_rfl
      have e := (rulesToy_Δ d h ϖ c 1 zero_le_one le_rfl).2.2.2.2
      unfold Δ at e; linarith
    · intro hc ρ' h0' h1'
      have e := (rulesToy_Δ d h ϖ c ρ' h0' h1').2.2.2.2
      unfold Δ at e; nlinarith

/-- **`RevisionInvariant`**: the penalty on the past act does not depend on the revision —
`u (RELAX, PRE) = u (KEEP, PRE)`.
Source: [[corr-legit-neg-inventory]] item 056 (E6, "revision-invariance of the penalty on a past act")
Kind: D
Fidelity: exact -/
def RevisionInvariant (P : Problem (Fin 2) (Fin 2)) : Prop := P.u 0 1 = P.u 1 1

/-- **E6 (b), the refuted row.** The source's sentence (NEGATIVES E6, "Which property blocks"):
"The blocking property is revision-invariance of the penalty on a past act" (as an iff, per the
inventory: "blocks iff the penalty on a past act is revision-invariant"). Reading formalised
(ATTRIBUTION-UNVETTED among the source's own readings): blocking = WAIT (weakly: `H PRE ≤ H WAIT`,
ties counted as WAIT) at every credence; revision-invariance = `RevisionInvariant`. Refutation:
`A4` with `d ≤ c < ϖ` is **not** revision-invariant (`1 − c ≠ 1 − ϖ`) and WAITs at every credence
(instances `c ∈ {1/10, 1/5, 1/2, 1}` at `d = 1/10, ϖ = 2`). Register: the source's own sentence
lists "A4, `c ≥ d`" as a case of revision-invariance, i.e. it uses the term more loosely than the
equality; so the "exactly when" is *inconsistent with its own gloss* (ill-posed as written) — this
theorem refutes the literal reading, and the well-posed neighbour is `E6_blocks_iff_dominance`.
Source: [[corr-legit-neg-inventory]] item 056 (E6, narrowing 1); VERIFY E V-E6
Kind: P (refutation)
Fidelity: exact
Hyps: (a) `d ≤ c < ϖ` -/
theorem E6_refuted (hdc : d ≤ c) (hcϖ : c < ϖ) :
    ¬ RevisionInvariant (rulesToy d h ϖ c ρ h0 h1 4) ∧
    (∀ ρ' (h0' : 0 ≤ ρ') (h1' : ρ' ≤ 1),
      (rulesToy d h ϖ c ρ' h0' h1' 4).H 1 ≤ (rulesToy d h ϖ c ρ' h0' h1' 4).H 0) ∧
    (∀ c', c' ∈ ({1/10, 1/5, 1/2, 1} : Finset ℚ) →
      ¬ RevisionInvariant (rulesToy (1/10) (1/2) 2 c' ρ h0 h1 4) ∧
      ∀ ρ' (h0' : 0 ≤ ρ') (h1' : ρ' ≤ 1),
        (rulesToy (1/10) (1/2) 2 c' ρ' h0' h1' 4).H 1 ≤ (rulesToy (1/10) (1/2) 2 c' ρ' h0' h1' 4).H 0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold RevisionInvariant; simp [rulesToy, rulesU]; linarith
  · exact ((E6_general d h ϖ c ρ h0 h1).2.2 (by linarith)).2 hdc
  · intro c' hc'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    refine ⟨?_, ?_⟩
    · unfold RevisionInvariant; simp [rulesToy, rulesU]
      rcases hc' with rfl | rfl | rfl | rfl <;> norm_num
    · refine ((E6_general (1/10) (1/2) 2 c' ρ h0 h1).2.2 (by norm_num)).2 ?_
      rcases hc' with rfl | rfl | rfl | rfl <;> norm_num

/-- **E6 (b), the surviving neighbour**: an architecture blocks (weakly WAITs) at every credence iff
the complying act is weakly preferred on both branches (E1 instantiated) — for every `arch`; and
revision-invariance is a sufficient case of it **only together with** a penalty at least the cost
of complying on the KEEP branch (`u KEEP PRE ≤ u KEEP WAIT`) and the same WAIT value on both
branches (true of every `rulesU` architecture by construction: WAIT is `1 − d` on both) — the `A1`
shape. Without the penalty clause the "if" fails: `A1` with `ϖ < d` is revision-invariant and PREs
everywhere.
Source: [[corr-legit-neg-inventory]] item 056 (E6, "the exact condition is branchwise dominance"); VERIFY E V-E6
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem E6_blocks_iff_dominance (arch : Fin 5) :
    ((∀ ρ' (h0' : 0 ≤ ρ') (h1' : ρ' ≤ 1),
      (rulesToy d h ϖ c ρ' h0' h1' arch).H 1 ≤ (rulesToy d h ϖ c ρ' h0' h1' arch).H 0) ↔
      rulesU arch d h ϖ c 0 1 ≤ rulesU arch d h ϖ c 0 0 ∧ rulesU arch d h ϖ c 1 1 ≤ rulesU arch d h ϖ c 1 0) ∧
    (RevisionInvariant (rulesToy d h ϖ c ρ h0 h1 arch) →
      rulesU arch d h ϖ c 1 1 ≤ rulesU arch d h ϖ c 1 0 →
      rulesU arch d h ϖ c 0 0 = rulesU arch d h ϖ c 1 0 →
      rulesU arch d h ϖ c 0 1 ≤ rulesU arch d h ϖ c 0 0 ∧ rulesU arch d h ϖ c 1 1 ≤ rulesU arch d h ϖ c 1 0) := by
  have hH : ∀ ρ' (h0' : 0 ≤ ρ') (h1' : ρ' ≤ 1) (a : Fin 2), (rulesToy d h ϖ c ρ' h0' h1' arch).H a
      = ρ' * rulesU arch d h ϖ c 0 a + (1 - ρ') * rulesU arch d h ϖ c 1 a := by
    intro ρ' h0' h1' a; simp [rulesToy, Problem.H, Problem.W, EU, Fin.sum_univ_two]
  constructor
  · simp only [hH]
    exact robust_iff_branchwise_two _ _ _ _
  · intro hinv hK hW
    unfold RevisionInvariant at hinv
    simp only [rulesToy] at hinv
    exact ⟨by rw [hinv, hW]; exact hK, hK⟩

/-- **E6 (c), the price of `A1`**: at `ρ = 9/10` the future evaluation (`A0`'s scores) prefers PRE
by `1/20` while `A1` WAITs.
Source: [[corr-legit-neg-inventory]] item 056 (E6, "the price of A1"); `e4_rules_layer.py:79-84`
Kind: N+
Fidelity: exact -/
theorem E6_price_of_A1 :
    (rulesToy (1/10) (1/2) 2 0 (9/10) (by norm_num) (by norm_num) 0).H 1
      - (rulesToy (1/10) (1/2) 2 0 (9/10) (by norm_num) (by norm_num) 0).H 0 = 1/20 ∧
    (rulesToy (1/10) (1/2) 2 0 (9/10) (by norm_num) (by norm_num) 1).H 1
      < (rulesToy (1/10) (1/2) 2 0 (9/10) (by norm_num) (by norm_num) 1).H 0 := by
  obtain ⟨e0, e1, _⟩ := rulesToy_Δ (1/10) (1/2) 2 0 (9/10) (by norm_num) (by norm_num)
  refine ⟨by rw [e0]; unfold Δ; norm_num, ?_⟩
  unfold Δ at e1; linarith

/-! ### 2-026: the two-rule shadow (`stretch`) -/

/-- **The two-rule model**: actions `(a₁, a₂) : Fin 2 × Fin 2` — comply (`0`) or violate (`1`) the
declared rule `R₁` (committed term `−ϖ`, cost of compliance `d₁`) and the undeclared rule `R₂`
(penalty `h₂` on KEEP, `c₂` on RELAX, cost `d₂`) — with additive terms; all legitimate.
Source: [[corr-legit-neg-2-inventory]] item 2-026 (b)
Kind: D
Fidelity: exact -/
def twoRule (d₁ d₂ h₂ c₂ ϖ ρ : ℚ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : Problem (Fin 2) (Fin 2 × Fin 2) where
  prior := ![ρ, 1 - ρ]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp [Fin.sum_univ_two]
  leg := fun _ _ => true
  u := fun s a => (if a.1 = 0 then 1 - d₁ else 1 - ϖ) +
    (if a.2 = 0 then 1 - d₂ else if s = 0 then 1 - c₂ else 1 - h₂)

/-- **2-026's shadow**: violating the declared rule is dominated at every `ρ` when `ϖ > d₁`
(whatever `a₂`), and violating the undeclared rule is preferred iff `Δ d₂ h₂ c₂ ρ > 0` — the
`A1` term moves that threshold neither way.
Source: [[corr-legit-neg-2-inventory]] item 2-026 (b)
Kind: C
Fidelity: exact
Hyps: (a) `ϖ > d₁` for the first clause -/
theorem twoRule_shadow (d₁ d₂ h₂ c₂ ϖ ρ : ℚ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (d₁ < ϖ → ∀ a₂, (twoRule d₁ d₂ h₂ c₂ ϖ ρ h0 h1).H (1, a₂) < (twoRule d₁ d₂ h₂ c₂ ϖ ρ h0 h1).H (0, a₂)) ∧
    ∀ a₁, (twoRule d₁ d₂ h₂ c₂ ϖ ρ h0 h1).H (a₁, 1) - (twoRule d₁ d₂ h₂ c₂ ϖ ρ h0 h1).H (a₁, 0)
      = Δ d₂ h₂ c₂ ρ := by
  have hH : ∀ a : Fin 2 × Fin 2, (twoRule d₁ d₂ h₂ c₂ ϖ ρ h0 h1).H a
      = (if a.1 = 0 then 1 - d₁ else 1 - ϖ) +
        (if a.2 = 0 then 1 - d₂ else ρ * (1 - c₂) + (1 - ρ) * (1 - h₂)) := by
    intro a
    simp only [twoRule, Problem.H, Problem.W, EU, Fin.sum_univ_two]
    simp; split_ifs <;> ring
  constructor
  · intro hd a₂
    rw [hH, hH]; simp; linarith
  · intro a₁
    rw [hH, hH]; unfold Δ; simp; ring

end Rules

end Cleanroom.Corrigibility.LegitNegDynamic
