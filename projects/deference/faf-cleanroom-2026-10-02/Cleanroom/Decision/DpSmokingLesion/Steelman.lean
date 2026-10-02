import Cleanroom.Decision.DpSmokingLesion.Prop13

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# T8, T9, T12: the two-type trees — Propositions 15–16, the steelman's clause-2 failure iff,
referent separation by coverage failure alone

[[dp-smoking-lesion-mandate]] T8 (load-bearing 4), T9 (load-bearing 5), T12.

* **The two-type tree** `twoType n U κ` (kind D): type `t ∼ Bern(n)` (index `0` = `true`, the
  smoke-lover / lesioned type); at type `t` query `d_t` (point `t : Bool`, `O = ⊤`); act `m`;
  chance `k ∼ Bern(κ_t)`; leaf world `(t, m, k)` with payoff `U t m k` — the occupant's own
  utility (encoding (M)). Instances: `robotsHybrid` (E3, `U_ROBOT`, `k` = killed, `κ = (1, 0)`),
  `suicidal` (E4, `U_SUICIDAL`), `fdtSL` (E8, the FDT paper's numbers, `κ = (99/100, 1/100)`).
* **T8(a)** (`twoType_value`, `twoType_tOpt_iff`): `V_B` is bilinear in the two labels
  (`V_B(C) = ∑_t n_t (q_t ū_t(1) + (1 − q_t) ū_t(0))`), so when the smoke-lover prefers smoking
  and the other type refraining (`ū_S(1) > ū_S(0)`, `ū_N(0) > ū_N(1)`, `n ∈ (0,1)`), `T_opt C ↔
  C = (smoke at d_S, refrain at d_N)` — proved from the bilinear form, not by enumeration;
  values `E3: −45`, `E4: 5`, `E8: 500 500` (`robots_tOpt_value` etc.).
* **T8(b)** (`udtValue_eq_pooled`, `fdtSL_udt_masked_prior`): act-event `UDT_{s°,ρ}` with
  `ρ_d(a) = {m = a}` and a Definition-11 prior equals the pooled updateful value; on E8 at the
  masked prior (interior self-model `(½, ½)` at both points) `V(m=1) = 500 499.5 > 500 000 =
  V(m=0)`, so its approved point is "everyone smokes", losing `½` to `T_opt`.
* **T9** (`steelman_clause2_iff`): on the hybrid steelman under (M) with the pooled strictly
  calibrated `P = ν(· ∣ ⊤)` and `V` the type's own utility (`State.ofUtility`), Definition 8's
  clause 2 fails at `d_N` iff `n c_L > 0` and at `d_L` iff `(1 − n) c_N > 0`; corollary
  (`steelman_some_point_fails`): for every procedure with `c_L + c_N > 0` some point fails clause
  2 — and at `(c_L, c_N) = (0, 0)` both clauses hold (the exact boundary S7's "every procedure"
  needs), a finding.
* **T12** (`steelman_r1State_vs_limit`): at `(c_L, c_N) = (1, 0)` under (M) at `d_L`, R1-state
  smokes (`−45 > −50`) while the tremble-limit evidential value (`limitVal`, D4/R3) abstains
  (`−90 < 0`), and coverage fails at `d_L` (the `d_N`-runs realize `m = 0` without consulting
  `d_L`): a referent separation with no simulation node.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-! ## The two-type tree -/

section twoType

variable (n : ℚ) (n0 : 0 ≤ n) (n1 : n ≤ 1) (U : Bool → Bool → Bool → ℚ) (κ : Bool → ℚ)
  (κ0 : ∀ t, 0 ≤ κ t) (κ1 : ∀ t, κ t ≤ 1)

/-- **The two-type tree**: type `t ∼ Bern(n)` (index `0` = `true`), query `d_t` (`O = ⊤`), act
`m`, chance `k ∼ Bern(κ_t)` (index `0` = `k = 1`), leaf `(t, m, k)` with payoff `U t m k`.
Source: `sl_zoo.py` lines 171–190 (`robots`), 264–278 (`fdt_sl`); `sl-defensible-claims.md` S7
(hybrid encoding: "leaf payoff the occupant type's own utility"); mandate §3.7, T8
Kind: D
Fidelity: exact (the script's `typed=True` worlds; `k` is the script's death/cancer coordinate) -/
def twoType : Tree TickleW Bool (fun _ => Bool) ℚ :=
  .chance 2 (FinDistr.coin n n0 n1) fun i =>
    .decision (decide (i = 0)) fun m =>
      .chance 2 (FinDistr.coin (κ (decide (i = 0))) (κ0 _) (κ1 _)) fun j =>
        .leaf (decide (i = 0), m, decide (j = 0)) (U (decide (i = 0)) m (decide (j = 0)))

local notation "TT" => twoType n n0 n1 U κ κ0 κ1

/-- The type rate: `n` for the smoke-lover, `1 − n` for the other. Source: none: infrastructure. Kind: D -/
def typeRate (t : Bool) : ℚ := if t then n else 1 - n

/-- The expected own-utility of act `m` at type `t`: `ū_t(m) = κ_t U(t,m,1) + (1 − κ_t) U(t,m,0)`.
Source: [[decision-problems-v2]] §4 (act values); mandate T8(a)
Kind: D -/
def ubar (t m : Bool) : ℚ := κ t * U t m true + (1 - κ t) * U t m false

/-- A sum over the leaves of the two-type tree. Source: none: infrastructure. Kind: L -/
theorem twoType_sum (f : (TT).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2, f ⟨i, m, j, ()⟩ := by
  unfold twoType at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The leaf masses of the two-type tree: `n_t · C(d_t)(m) · κ_{t,k}`.
Source: Definition 6. Kind: L -/
theorem twoType_leafLaw (C : Proc Bool (fun _ => Bool) ℚ) (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw C TT ⟨i, m, j, ()⟩ =
      typeRate n (decide (i = 0)) * (C (decide (i = 0))).w m *
        (if j = 0 then κ (decide (i = 0)) else 1 - κ (decide (i = 0))) := by
  unfold twoType typeRate
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.coin]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The world and payoff at a leaf. Source: none: infrastructure. Kind: L -/
theorem twoType_world_payoff (i : Fin 2) (m : Bool) (j : Fin 2) :
    world TT ⟨i, m, j, ()⟩ = (decide (i = 0), m, decide (j = 0)) ∧
    payoff TT ⟨i, m, j, ()⟩ = U (decide (i = 0)) m (decide (j = 0)) :=
  ⟨rfl, rfl⟩

variable (C : Proc Bool (fun _ => Bool) ℚ)

/-- **`V_B` on the two-type tree is bilinear in the two labels**:
`V_B(C) = ∑_t n_t ∑_m C(d_t)(m) ū_t(m)`.
Source: [[decision-problems-v2]] §8 (`valueNode_affine`: multilinear in the labels); mandate
T8(a) ("prove the vertex claim from multilinearity")
Kind: P
Fidelity: exact -/
theorem twoType_value :
    value C TT = ∑ t : Bool, typeRate n t * ∑ m : Bool, (C t).w m * ubar U κ t m := by
  unfold value
  rw [twoType_sum]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, twoType_leafLaw, (twoType_world_payoff _ _ _ _ _ _ _ _ _ _).2,
    ubar]
  simp; ring

/-- The two-type tree's `ν` at the act and type events. Source: none: infrastructure. Kind: L -/
theorem twoType_nu_act (a : Bool) :
    nu C TT (evM a) = n * (C true).w a + (1 - n) * (C false).w a ∧
    nu C TT evL = n ∧
    nu C TT (evL ∩ evM a) = n * (C true).w a := by
  have hnu : ∀ X, nu C TT X = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
      if (decide (i = 0), m, decide (j = 0)) ∈ X then leafLaw C TT ⟨i, m, j, ()⟩ else 0 := by
    intro X; rw [nu_eq_sum, twoType_sum]; rfl
  have hw : ∀ t : Bool, (C t).w false = 1 - (C t).w true := by
    intro t; have := (C t).sum_one; rw [Fintype.sum_bool] at this; linarith
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [hnu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, twoType_leafLaw, mem_evM, mem_evL,
      Finset.mem_inter, typeRate]
    cases a <;> simp [hw] <;> ring

/-- The two-type tree's payoff mass at the act events: `paySum(m) = ∑_t n_t C(d_t)(m) ū_t(m)`.
Source: none: infrastructure. Kind: L -/
theorem twoType_paySum_act (a : Bool) :
    paySum C TT (evM a) = n * (C true).w a * ubar U κ true a + (1 - n) * (C false).w a * ubar U κ false a := by
  rw [paySum_eq_sum_ite, twoType_sum]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, twoType_leafLaw, (twoType_world_payoff _ _ _ _ _ _ _ _ _ _).1,
    (twoType_world_payoff _ _ _ _ _ _ _ _ _ _).2, mem_evM, typeRate, ubar]
  cases a <;> simp <;> ring

/-- Every run meets `d_t` once on the `t`-branch and never on the other.
Source: none: infrastructure. Kind: L -/
theorem twoType_count (i : Fin 2) (m : Bool) (j : Fin 2) (t : Bool) :
    count t TT ⟨i, m, j, ()⟩ = if decide (i = 0) = t then 1 else 0 := by
  unfold twoType
  simp only [count_chance, count_decision, count_leaf, add_zero]

/-- **Coverage fails at both points of a two-type tree with `n ∈ (0,1)`**: the other type's
runs satisfy `⊤` and never consult this point.
Source: `sl-synthesis.md` §1.1 ("Two-point robots, hybrid … coverage fails at both points");
mandate T12 ("coverage at `d_L`: the `d_N`-runs realize `evM 0` without consulting `d_L`")
Kind: N− -/
theorem twoType_not_covers (hn0 : 0 < n) (hn1 : n < 1) (t : Bool) : ¬ Covers slObs C TT t := by
  intro h
  cases t
  · obtain ⟨a, ha⟩ := FinDistr.exists_pos_w' (C true)
    rcases (κ0 true).lt_or_eq with hk | hk
    · have hpos : 0 < leafLaw C TT ⟨0, a, 0, ()⟩ := by
        rw [twoType_leafLaw]; simp only [typeRate]; simp
        exact mul_pos (mul_pos hn0 ha) hk
      have := h _ hpos (Finset.mem_univ _)
      rw [twoType_count] at this; simp at this
    · have hpos : 0 < leafLaw C TT ⟨0, a, 1, ()⟩ := by
        rw [twoType_leafLaw]; simp only [typeRate]; simp; rw [← hk]; simp
        exact mul_pos hn0 ha
      have := h _ hpos (Finset.mem_univ _)
      rw [twoType_count] at this; simp at this
  · obtain ⟨a, ha⟩ := FinDistr.exists_pos_w' (C false)
    have hn' : 0 < 1 - n := by linarith
    rcases (κ0 false).lt_or_eq with hk | hk
    · have hpos : 0 < leafLaw C TT ⟨1, a, 0, ()⟩ := by
        rw [twoType_leafLaw]; simp only [typeRate]; simp
        exact mul_pos (mul_pos hn' ha) hk
      have := h _ hpos (Finset.mem_univ _)
      rw [twoType_count] at this; simp at this
    · have hpos : 0 < leafLaw C TT ⟨1, a, 1, ()⟩ := by
        rw [twoType_leafLaw]; simp only [typeRate]; simp; rw [← hk]; simp
        exact mul_pos hn' ha
      have := h _ hpos (Finset.mem_univ _)
      rw [twoType_count] at this; simp at this

end twoType

/-! ## The three instances and `T_opt` -/

section instances

/-- `U_ROBOT`: the smoke-lover `S` (`t = true`) values smoking at `+10` and being killed at
`−100` (`(1,1) ↦ −90`, `(1,0) ↦ 10`, `(0,1) ↦ −100`, `(0,0) ↦ 0`); the other type `N` values
smoking at `−1` (`(1,1) ↦ −101`, `(1,0) ↦ −1`, `(0,1) ↦ −100`, `(0,0) ↦ 0`). `k` = killed.
Source: `sl_zoo.py` line 166 (`U_ROBOT`); P01's table
Kind: D -/
def uRobot (t m k : Bool) : ℚ :=
  (if m then (if t then 10 else -1) else 0) - (if k then 100 else 0)

/-- `U_SUICIDAL` (Treutlein's variant): `S`: `(1,1) ↦ 10`, `(1,0) ↦ −90`, refrain `↦ 0`;
`N`: smoke `↦ −100`, refrain `↦ 0`.
Source: `sl_zoo.py` line 168 (`U_SUICIDAL`)
Kind: D -/
def uSuicidal (t m k : Bool) : ℚ :=
  if m then (if t then (if k then 10 else -90) else -100) else 0

/-- The FDT paper's Smoking Lesion payoffs: the lesioned type values smoking at `+1000`, the
other at `−1`; `+1 000 000` if no cancer.
Source: `sl_zoo.py` lines 264–278 (`fdt_sl`)
Kind: D -/
def uFdt (t m k : Bool) : ℚ :=
  (if m then (if t then 1000 else -1) else 0) + (if k then 0 else 1000000)

/-- The robots' death coin: the hunter kills all and only smoke-lovers. Source: `sl_zoo.py` line 184. Kind: D -/
def κRobot (t : Bool) : ℚ := if t then 1 else 0

/-- `0 ≤ κRobot`. Source: none: infrastructure. Kind: L -/
theorem κRobot_nonneg (t : Bool) : 0 ≤ κRobot t := by unfold κRobot; split_ifs <;> norm_num

/-- `κRobot ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem κRobot_le_one (t : Bool) : κRobot t ≤ 1 := by unfold κRobot; split_ifs <;> norm_num

/-- The FDT lesion's cancer rates. Source: `sl_zoo.py` line 275. Kind: D -/
def κFdt (t : Bool) : ℚ := if t then 99/100 else 1/100

/-- `0 ≤ κFdt`. Source: none: infrastructure. Kind: L -/
theorem κFdt_nonneg (t : Bool) : 0 ≤ κFdt t := by unfold κFdt; split_ifs <;> norm_num

/-- `κFdt ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem κFdt_le_one (t : Bool) : κFdt t ≤ 1 := by unfold κFdt; split_ifs <;> norm_num

/-- **E3, the hybrid robots** at `n = ½`. Source: `sl_zoo.py` `robots()`; mandate T8. Kind: D -/
def robotsHybrid (n : ℚ) (n0 : 0 ≤ n) (n1 : n ≤ 1) : Tree TickleW Bool (fun _ => Bool) ℚ :=
  twoType n n0 n1 uRobot κRobot κRobot_nonneg κRobot_le_one

/-- **E4, Treutlein's suicidal variant** at `n = ½`. Source: `sl_zoo.py` E4. Kind: D -/
def suicidal (n : ℚ) (n0 : 0 ≤ n) (n1 : n ≤ 1) : Tree TickleW Bool (fun _ => Bool) ℚ :=
  twoType n n0 n1 uSuicidal κRobot κRobot_nonneg κRobot_le_one

/-- **E8, the FDT paper's two-point Smoking Lesion**. Source: `sl_zoo.py` `fdt_sl`. Kind: D -/
def fdtSL (n : ℚ) (n0 : 0 ≤ n) (n1 : n ≤ 1) : Tree TickleW Bool (fun _ => Bool) ℚ :=
  twoType n n0 n1 uFdt κFdt κFdt_nonneg κFdt_le_one

/-- The two-point deterministic procedure `(smoke at d_S, refrain at d_N)`.
Source: `sl-defensible-claims.md` S7 ("`T_opt` smokes at the smoke-lover point and refrains at
the other")
Kind: D -/
def procSmokeRefrain : Proc Bool (fun _ => Bool) ℚ := Proc.ofFun fun t => t

/-- The two-point label `(c_L at d_L, c_N at d_N)`. Source: mandate T9. Kind: D -/
def procTwo (cL : ℚ) (l0 : 0 ≤ cL) (l1 : cL ≤ 1) (cN : ℚ) (m0 : 0 ≤ cN) (m1 : cN ≤ 1) :
    Proc Bool (fun _ => Bool) ℚ :=
  fun t => if t then FinDistr.bool cL l0 l1 else FinDistr.bool cN m0 m1

variable (n : ℚ) (n0 : 0 ≤ n) (n1 : n ≤ 1) (U : Bool → Bool → Bool → ℚ) (κ : Bool → ℚ)
  (κ0 : ∀ t, 0 ≤ κ t) (κ1 : ∀ t, κ t ≤ 1)

/-- **Proposition 15 (`T_opt` on a two-type tree)**: when the smoke-lover prefers smoking
(`ū_S(1) > ū_S(0)`), the other type prefers refraining (`ū_N(0) > ū_N(1)`) and both types have
positive mass, `T_opt C ↔ C = (smoke at d_S, refrain at d_N)` — from the bilinear form of `V_B`
in the two labels (no enumeration of profiles).
Source: `sl-synthesis.md` §1.3 bullet 5 ("`T_opt` smokes at the smoke-lover point of every
two-type tree"); `sl-defensible-claims.md` S7; dp-sl-015; mandate T8(a)
Kind: P
Fidelity: exact (the tie set is excluded by the strict preferences)
Hyps: (a) the two strict preferences; (a) `0 < n < 1` -/
theorem twoType_tOpt_iff (hS : ubar U κ true false < ubar U κ true true)
    (hN : ubar U κ false true < ubar U κ false false) (hn0 : 0 < n) (hn1 : n < 1)
    (C : Proc Bool (fun _ => Bool) ℚ) :
    TOpt C (twoType n n0 n1 U κ κ0 κ1) ↔ (C true).w true = 1 ∧ (C false).w true = 0 := by
  have hw : ∀ (C' : Proc Bool (fun _ => Bool) ℚ) (t : Bool), (C' t).w false = 1 - (C' t).w true := by
    intro C' t
    have := (C' t).sum_one; rw [Fintype.sum_bool] at this; linarith
  have hval : ∀ C' : Proc Bool (fun _ => Bool) ℚ, value C' (twoType n n0 n1 U κ κ0 κ1) =
      n * ((C' true).w true * ubar U κ true true + (1 - (C' true).w true) * ubar U κ true false) +
      (1 - n) * ((C' false).w true * ubar U κ false true + (1 - (C' false).w true) * ubar U κ false false) := by
    intro C'
    rw [twoType_value]
    simp only [Fintype.sum_bool, typeRate, hw]
    simp
    try ring
  have hstar : value procSmokeRefrain (twoType n n0 n1 U κ κ0 κ1) =
      n * ubar U κ true true + (1 - n) * ubar U κ false false := by
    rw [hval]; simp [procSmokeRefrain, Proc.ofFun]
  constructor
  · intro hopt
    have h := hopt procSmokeRefrain
    rw [hstar, hval] at h
    have hq1 := (C true).w_le_one true
    have hq0 := (C false).nonneg true
    have hΔS : 0 < ubar U κ true true - ubar U κ true false := sub_pos.mpr hS
    have hΔN : 0 < ubar U κ false false - ubar U κ false true := sub_pos.mpr hN
    -- `n (1 − q_S) Δ_S + (1 − n) q_N Δ_N ≤ 0` with both terms `≥ 0`
    have key : n * (1 - (C true).w true) * (ubar U κ true true - ubar U κ true false) +
        (1 - n) * (C false).w true * (ubar U κ false false - ubar U κ false true) ≤ 0 := by
      linarith
    have h1 : 0 ≤ n * (1 - (C true).w true) * (ubar U κ true true - ubar U κ true false) :=
      mul_nonneg (mul_nonneg hn0.le (by linarith)) hΔS.le
    have h2 : 0 ≤ (1 - n) * (C false).w true * (ubar U κ false false - ubar U κ false true) :=
      mul_nonneg (mul_nonneg (by linarith) hq0) hΔN.le
    have e1 : n * (1 - (C true).w true) * (ubar U κ true true - ubar U κ true false) = 0 := by
      linarith
    have e2 : (1 - n) * (C false).w true * (ubar U κ false false - ubar U κ false true) = 0 := by
      linarith
    constructor
    · rcases mul_eq_zero.mp e1 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hn0.ne'
        · linarith
      · exact absurd h hΔS.ne'
    · rcases mul_eq_zero.mp e2 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (by linarith)
        · exact h'
      · exact absurd h hΔN.ne'
  · rintro ⟨h1, h0⟩ C'
    rw [hval, hval, h1, h0]
    have hq1 := (C' true).w_le_one true
    have hq1' := (C' true).nonneg true
    have hq0 := (C' false).nonneg true
    have hq0' := (C' false).w_le_one true
    nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hq1), mul_nonneg (sub_nonneg.mpr hn1.le) hq0,
      sub_pos.mpr hS, sub_pos.mpr hN]

/-- **`T_opt` values reproduced**: E3 `−45`, E4 `5`, E8 `500 500` at `n = ½`, attained by
`(smoke, refrain)`, and `T_opt` holds exactly there on each tree.
Source: `sl-defensible-claims.md` S7 ("`T_opt` smokes at the smoke-lover point and refrains at
the other (E3 `−45`, E4 `5`, E8 `500 500`)"); mandate T8(a)
Kind: N+ -/
theorem robots_tOpt_value :
    value procSmokeRefrain (robotsHybrid (1/2) (by norm_num) (by norm_num)) = -45 ∧
    value procSmokeRefrain (suicidal (1/2) (by norm_num) (by norm_num)) = 5 ∧
    value procSmokeRefrain (fdtSL (1/2) (by norm_num) (by norm_num)) = 500500 ∧
    (∀ C, TOpt C (robotsHybrid (1/2) (by norm_num) (by norm_num)) ↔
      (C true).w true = 1 ∧ (C false).w true = 0) ∧
    (∀ C, TOpt C (suicidal (1/2) (by norm_num) (by norm_num)) ↔
      (C true).w true = 1 ∧ (C false).w true = 0) ∧
    (∀ C, TOpt C (fdtSL (1/2) (by norm_num) (by norm_num)) ↔
      (C true).w true = 1 ∧ (C false).w true = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold robotsHybrid; rw [twoType_value]
    norm_num [procSmokeRefrain, Proc.ofFun, typeRate, ubar, uRobot, κRobot]
  · unfold suicidal; rw [twoType_value]
    norm_num [procSmokeRefrain, Proc.ofFun, typeRate, ubar, uSuicidal, κRobot]
  · unfold fdtSL; rw [twoType_value]
    norm_num [procSmokeRefrain, Proc.ofFun, typeRate, ubar, uFdt, κFdt]
  · intro C; unfold robotsHybrid
    exact twoType_tOpt_iff _ _ _ _ _ _ _ (by norm_num [ubar, uRobot, κRobot])
      (by norm_num [ubar, uRobot, κRobot]) (by norm_num) (by norm_num) C
  · intro C; unfold suicidal
    exact twoType_tOpt_iff _ _ _ _ _ _ _ (by norm_num [ubar, uSuicidal, κRobot])
      (by norm_num [ubar, uSuicidal, κRobot]) (by norm_num) (by norm_num) C
  · intro C; unfold fdtSL
    exact twoType_tOpt_iff _ _ _ _ _ _ _ (by norm_num [ubar, uFdt, κFdt])
      (by norm_num [ubar, uFdt, κFdt]) (by norm_num) (by norm_num) C

end instances

/-! ## T8(b): act-event UDT at a Definition-11 prior is the pooled updateful value -/

section udt

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- **Act-event `UDT_{s°,ρ}`'s value** with the self-sufficient policy interpretation
`ρ_d(a) := a` (the act event itself): `V_{s°}(ρ_d(a))`.
Source: [[decision-problems-v2]] §4 Definition 17 (`UDT_{s°,ρ}(d) := Unif argmax_{a : P_{s°}(ρ_d(a)) > 0} V_{s°}(ρ_d(a))`), with `ρ_d(a) = a`; mandate T8(b)
Kind: D
Fidelity: variant: `ρ_d(a) = a` (the self-sufficient interpretation Remark 4.2 warns about);
not `dp-calibration`'s (it defined no UDT) -/
def udtValue (s₀ : State Ω ℚ) (actEv : (d : ι) → acts d → Finset Ω) (d : ι) (a : acts d) : ℚ :=
  s₀.V (actEv d a)

/-- **`T_{UDT_{s°,ρ}}` at a point** (Definition 18's advocacy shape for the updateless pair):
if some act event has positive prior probability, `supp C(d)` lies in the argmax of `V_{s°}` over
the prior-possible act events.
Source: [[decision-problems-v2]] §4 Definition 18 ("`T_{UDT_{s°,ρ}}` … analogously, each with
its own act value and maximization domain"); mandate T8(b)
Kind: D
Fidelity: variant: `ρ_d(a) = a` -/
def UdtApprovedAt (s₀ : State Ω ℚ) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts ℚ)
    (d : ι) : Prop :=
  (∃ a, 0 < s₀.pr (actEv d a)) → ∀ a, 0 < (C d).w a →
    0 < s₀.pr (actEv d a) ∧ ∀ b, 0 < s₀.pr (actEv d b) → udtValue s₀ actEv d b ≤ udtValue s₀ actEv d a

/-- **The prior's act value is the pooled updateful value**: at a Definition-11 prior `s°` for
`C` on `B`, `V_{s°}(a) = 𝔼_μ[r ∣ λ ⊨ a] = V_{s_⊤}(a)` at the pooled strictly calibrated state
`s_⊤ = (ν, 𝔼[r ∣ ·])` at `O = ⊤`, for every act event of positive `ν`-mass — across the two
definitions (Definition 11's prior and Definition 8's state at `⊤`).
Source: `sl-synthesis.md` §1.3 bullet 5 ("act-event `UDT_{s°,ρ}` equals the pooled updateful
value"); mandate T8(b)
Kind: L -/
theorem udtValue_eq_pooled (B : Tree Ω ι acts ℚ) (C : Proc ι acts ℚ) (s₀ : State Ω ℚ)
    (hprior : PriorCalibrated C B s₀) (actEv : (d : ι) → acts d → Finset Ω) (d : ι) (a : acts d)
    (hpos : 0 < nu C B (actEv d a)) :
    udtValue s₀ actEv d a = (calibratedState C B Finset.univ (nu_univ_pos C B)).V (actEv d a) := by
  unfold udtValue
  rw [calibratedState_V, Finset.inter_univ, eq_div_iff hpos.ne']
  exact hprior.2 _ hpos

end udt

/-- **Proposition 16 on E8 at the masked prior**: with the interior self-model `(½, ½)` at both
points, the prior calibrated to `C' = (½, ½)` has `V(m=1) = 500 499.5 > 500 000 = V(m=0)`,
both act events prior-possible; so act-event `UDT` approves "everyone smokes"
(`procSmokeSmoke`) and rejects `T_opt`'s `(smoke, refrain)` at the smoke-refrain point `d_N`;
the value loss of "everyone smokes" relative to `T_opt` is exactly `½`.
Source: `sl-defensible-claims.md` S7 ("its approved deterministic point is 'everyone smokes'
(non-vacuously at the masked prior: `V(m=1) = 500 499.5 > 500 000`), losing `½` utilon to
pooling"); dp-sl-015; mandate T8(b)
Kind: N+
Fidelity: variant: `ρ_d(a) = a`; masked prior = the prior calibrated to an interior self-model -/
theorem fdtSL_udt_masked_prior :
    let B := fdtSL (1/2) (by norm_num) (by norm_num)
    let C' : Proc Bool (fun _ => Bool) ℚ := fun _ => FinDistr.bool (1/2) (by norm_num) (by norm_num)
    let s₀ := calibratedState C' B Finset.univ (nu_univ_pos _ _)
    PriorCalibrated C' B s₀ ∧ udtValue s₀ slActEv true true = 500499 + 1/2 ∧
      udtValue s₀ slActEv true false = 500000 ∧
      UdtApprovedAt s₀ slActEv (Proc.ofFun fun _ => true) true ∧
      UdtApprovedAt s₀ slActEv (Proc.ofFun fun _ => true) false ∧
      ¬ UdtApprovedAt s₀ slActEv procSmokeRefrain false ∧
      value procSmokeRefrain B - value (Proc.ofFun fun _ => true) B = 1/2 := by
  intro B C' s₀
  have hν : ∀ a, nu C' B (evM a) = 1/2 := by
    intro a; unfold B fdtSL
    rw [(twoType_nu_act _ _ _ _ _ _ _ C' a).1]
    cases a <;> simp [C'] <;> norm_num
  have hpay : paySum C' B (evM true) = 500499/2 + 1/4 ∧ paySum C' B (evM false) = 250000 := by
    constructor <;>
    · unfold B fdtSL
      rw [twoType_paySum_act]
      simp [C', ubar, uFdt, κFdt]; norm_num
  have hV : ∀ a, udtValue s₀ slActEv true a = paySum C' B (evM a) / nu C' B (evM a) := by
    intro a; simp [udtValue, s₀, calibratedState_V]
  have hVt : udtValue s₀ slActEv true true = 500499 + 1/2 := by
    rw [hV, hpay.1, hν]; norm_num
  have hVf : udtValue s₀ slActEv true false = 500000 := by
    rw [hV, hpay.2, hν]; norm_num
  have hP : ∀ a, 0 < s₀.pr (slActEv true a) := by
    intro a; simp only [s₀, calibratedState_pr, slActEv_apply, Finset.inter_univ, nu_univ, div_one, hν]
    norm_num
  have hV' : ∀ (d : Bool) (a : Bool), udtValue s₀ slActEv d a = udtValue s₀ slActEv true a :=
    fun _ _ => rfl
  refine ⟨priorCalibrated_calibratedState_univ C' B _, hVt, hVf, ?_, ?_, ?_, ?_⟩
  · intro _ a ha
    simp only [Proc.ofFun_w] at ha
    have : a = true := by by_contra h; simp [h] at ha
    subst this
    refine ⟨hP true, fun b _ => ?_⟩
    cases b
    · rw [hV' true false, hV' true true, hVt, hVf]; norm_num
    · exact le_rfl
  · intro _ a ha
    simp only [Proc.ofFun_w] at ha
    have : a = true := by by_contra h; simp [h] at ha
    subst this
    refine ⟨hP true, fun b _ => ?_⟩
    cases b
    · rw [hV' false false, hV' false true, hVt, hVf]; norm_num
    · exact le_rfl
  · intro h
    have := (h ⟨true, hP true⟩ false (by simp [procSmokeRefrain, Proc.ofFun])).2 true (hP true)
    rw [hV' false true, hV' false false, hVt, hVf] at this
    norm_num at this
  · unfold B fdtSL
    rw [twoType_value, twoType_value]
    simp [procSmokeRefrain, Proc.ofFun, typeRate, ubar, uFdt, κFdt]; norm_num

/-! ## T9: the steelman's clause-2 failure iff, under (M) -/

section ownUtility

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **The own-utility state**: `P` given, `V(X) := ∑_{ω ∈ X} P(ω) u(ω) / P(X)` — the
expected own utility on the event (the steelman's stipulated `V`, "reading (a)": `P` pooled,
`V` the robot's own utility on every atom).
Source: `sl-defensible-claims.md` S7 ("`P` = the population conditional, `V` = the type's own
utility"); `sl_zoo.py` `own_U_state`; mandate T9
Kind: D -/
def State.ofUtility (P : FinDistr ℚ Ω) (u : Ω → ℚ) : State Ω ℚ where
  P := P
  V X := (∑ ω ∈ X, P.w ω * u ω) / probOf P X
  avg X Y h hX hY := by
    have hU : 0 < probOf P (X ∪ Y) := by rw [probOf_union P h]; linarith
    rw [probOf_union P h, Finset.sum_union h]
    field_simp

/-- `V` of the own-utility state. Source: none: infrastructure. Kind: L -/
theorem State.ofUtility_V (P : FinDistr ℚ Ω) (u : Ω → ℚ) (X : Finset Ω) :
    (State.ofUtility P u).V X = (∑ ω ∈ X, P.w ω * u ω) / probOf P X := rfl

/-- `P` of the own-utility state. Source: none: infrastructure. Kind: L -/
theorem State.ofUtility_pr (P : FinDistr ℚ Ω) (u : Ω → ℚ) (X : Finset Ω) :
    (State.ofUtility P u).pr X = probOf P X := rfl

end ownUtility

section steelman

variable (n : ℚ) (n0 : 0 ≤ n) (n1 : n ≤ 1) (cL : ℚ) (l0 : 0 ≤ cL) (l1 : cL ≤ 1) (cN : ℚ)
  (m0 : 0 ≤ cN) (m1 : cN ≤ 1)

local notation "RB" => robotsHybrid n n0 n1
local notation "CC" => procTwo cL l0 l1 cN m0 m1

/-- The pooled statistic `ν` on the hybrid robots as a weight vector on worlds.
Source: [[decision-problems-v2]] Definition 8 clause 1 at `O = ⊤` (`P = ν(· ∣ ⊤) = ν`)
Kind: D -/
def pooledDistr : FinDistr ℚ TickleW := nuCondDistr CC RB Finset.univ (nu_univ_pos _ _)

/-- **The hybrid steelman's states under (M)**: at `d_t`, `P` pooled (`= ν`) and `V` the
occupant's own utility `U_ROBOT t`.
Source: `sl-defensible-claims.md` S7 (hybrid encoding); mandate T9
Kind: D
Fidelity: exact (reading (a) of P01: own utility on a pooled `P`) -/
def steelmanState (t : Bool) : State TickleW ℚ :=
  State.ofUtility (pooledDistr n n0 n1 cL l0 l1 cN m0 m1) (fun w => uRobot t w.2.1 w.2.2)

/-- `P` of the steelman state is `ν`. Source: none: infrastructure. Kind: L -/
theorem steelmanState_pr (t : Bool) (X : Finset TickleW) :
    (steelmanState n n0 n1 cL l0 l1 cN m0 m1 t).pr X = nu CC RB X := by
  unfold steelmanState pooledDistr
  rw [State.ofUtility_pr, probOf_nuCondDistr, Finset.inter_univ, nu_univ, div_one]

/-- Clause 1 of Definition 8 holds at both points for the steelman states (`P` is pooled).
Source: `sl-defensible-claims.md` S7 ("calibrated beliefs, miscalibrated stakes")
Kind: L -/
theorem steelmanState_clause1 (t : Bool) :
    StrictClause1At (steelmanState n n0 n1 cL l0 l1 cN m0 m1) slObs CC RB t := by
  intro X
  rw [steelmanState_pr, slObs_apply, nu_univ, mul_one, Finset.inter_univ]

/-- A sum over the leaves of the hybrid robots. Source: none: infrastructure. Kind: L -/
theorem robots_sum (f : (RB).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2, f ⟨i, m, j, ()⟩ :=
  twoType_sum n n0 n1 uRobot κRobot κRobot_nonneg κRobot_le_one f

/-- The leaf masses of the hybrid robots. Source: Definition 6. Kind: L -/
theorem robots_leafLaw (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw CC RB ⟨i, m, j, ()⟩ =
      typeRate n (decide (i = 0)) * (CC (decide (i = 0))).w m *
        (if j = 0 then κRobot (decide (i = 0)) else 1 - κRobot (decide (i = 0))) :=
  twoType_leafLaw n n0 n1 uRobot κRobot κRobot_nonneg κRobot_le_one CC i m j

/-- The worlds and payoffs at the leaves of the hybrid robots. Source: none: infrastructure. Kind: L -/
theorem robots_world_payoff (i : Fin 2) (m : Bool) (j : Fin 2) :
    world RB ⟨i, m, j, ()⟩ = (decide (i = 0), m, decide (j = 0)) ∧
    payoff RB ⟨i, m, j, ()⟩ = uRobot (decide (i = 0)) m (decide (j = 0)) :=
  twoType_world_payoff n n0 n1 uRobot κRobot κRobot_nonneg κRobot_le_one i m j

/-- The pooled masses on the hybrid robots: `ν({(t, m, k)})` at the eight worlds
(the `k`-coordinate is deterministic: `k = t`).
Source: none: infrastructure. Kind: L -/
theorem robots_nu_single (t m k : Bool) :
    nu CC RB {(t, m, k)} =
      if k = t then (if t then n else 1 - n) * ((CC t).w m) else 0 := by
  have hnu : ∀ X, nu CC RB X = ∑ i : Fin 2, ∑ m' : Bool, ∑ j : Fin 2,
      if (decide (i = 0), m', decide (j = 0)) ∈ X then leafLaw CC RB ⟨i, m', j, ()⟩ else 0 := by
    intro X; rw [nu_eq_sum, robots_sum]; rfl
  rw [hnu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool]
  simp only [robots_leafLaw]
  simp only [Finset.mem_singleton, typeRate, κRobot]
  cases t <;> cases m <;> cases k <;> simp

/-- The payoff mass on the hybrid robots as a sum over worlds: `paySum(X) = ∑_{w ∈ X} ν({w}) U_{w.1}(w)`.
Source: none: infrastructure. Kind: L -/
theorem robots_paySum_worlds (X : Finset TickleW) :
    paySum CC RB X = ∑ w : TickleW, if w ∈ X then nu CC RB {w} * uRobot w.1 w.2.1 w.2.2 else 0 := by
  have hsing := robots_nu_single n n0 n1 cL l0 l1 cN m0 m1
  have hpay : ∀ X, paySum CC RB X = ∑ i : Fin 2, ∑ m' : Bool, ∑ j : Fin 2,
      if (decide (i = 0), m', decide (j = 0)) ∈ X then
        leafLaw CC RB ⟨i, m', j, ()⟩ * uRobot (decide (i = 0)) m' (decide (j = 0)) else 0 := by
    intro X; rw [paySum_eq_sum_ite, robots_sum]; rfl
  rw [hpay]
  simp only [Fin.sum_univ_two, Fintype.sum_bool]
  simp only [robots_leafLaw]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hsing, typeRate, κRobot]
  simp
  try ring

/-- The own-utility numerator and the payoff mass on the hybrid robots, on any event `X`:
their difference is `11` times the pooled mass of the cross-type smoking atom in `X`.
Source: mandate T9 ("the `←` direction exhibits the event (`evM 1`) at which `V·ν ≠ paySum`")
Kind: L -/
theorem robots_own_vs_pay (t : Bool) (X : Finset TickleW) :
    paySum CC RB X - ∑ ω ∈ X, (pooledDistr n n0 n1 cL l0 l1 cN m0 m1).w ω * uRobot t ω.2.1 ω.2.2 =
      (if (true, true, true) ∈ X then nu CC RB {(true, true, true)} else 0) *
          (uRobot true true true - uRobot t true true) +
        (if (false, true, false) ∈ X then nu CC RB {(false, true, false)} else 0) *
          (uRobot false true false - uRobot t true false) := by
  have hw : ∀ ω, (pooledDistr n n0 n1 cL l0 l1 cN m0 m1).w ω = nu CC RB {ω} := by
    intro ω
    unfold pooledDistr nuCondDistr
    simp [nu_univ]
  simp only [hw]
  have e : (∑ ω ∈ X, nu CC RB {ω} * uRobot t ω.2.1 ω.2.2) =
      ∑ ω, if ω ∈ X then nu CC RB {ω} * uRobot t ω.2.1 ω.2.2 else 0 := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [robots_paySum_worlds, e, ← Finset.sum_sub_distrib]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, robots_nu_single]
  cases t <;> simp [uRobot] <;> split_ifs <;> ring

/-- **The steelman's clause-2 failure iff (T9)**: on the hybrid robots under (M) with the pooled
`P` and own-utility `V`, Definition 8's clause 2 fails at `d_N` iff `n c_L > 0`, and fails at
`d_L` iff `(1 − n) c_N > 0`. The `←` directions exhibit the event `{m = 1}` at which
`V · ν ≠ paySum` (by `11` times the cross-type smoking mass); the `→` directions show agreement
on every event when the other type never smokes with positive mass (the types' utilities agree
on refraining atoms).
Source: dp-sl-2-001 ("Definition 8 clause 2 fails at the steelman's type points iff the other
type smokes with positive probability"); `sl-defensible-claims.md` S7 ("`d_SL`: `+10` against
the statistic `−1` …; `d_NSL`: `−101` against `−90`"); mandate T9
Kind: P
Fidelity: exact (both directions)
Hyps: none (the utility table is `U_ROBOT`; the identity is computed) -/
theorem steelman_clause2_iff :
    (¬ StrictClause2At (steelmanState n n0 n1 cL l0 l1 cN m0 m1) slObs CC RB false ↔ 0 < n * cL) ∧
    (¬ StrictClause2At (steelmanState n n0 n1 cL l0 l1 cN m0 m1) slObs CC RB true ↔ 0 < (1 - n) * cN) := by
  have hsing : ∀ t m k, nu CC RB {(t, m, k)} = if k = t then (if t then n else 1 - n) * ((CC t).w m) else 0 :=
    robots_nu_single n n0 n1 cL l0 l1 cN m0 m1
  have hV : ∀ t X, (steelmanState n n0 n1 cL l0 l1 cN m0 m1 t).V X =
      (∑ ω ∈ X, (pooledDistr n n0 n1 cL l0 l1 cN m0 m1).w ω * uRobot t ω.2.1 ω.2.2) /
        probOf (pooledDistr n n0 n1 cL l0 l1 cN m0 m1) X := fun _ _ => rfl
  have hprob : ∀ X, probOf (pooledDistr n n0 n1 cL l0 l1 cN m0 m1) X = nu CC RB X := by
    intro X; unfold pooledDistr; rw [probOf_nuCondDistr, Finset.inter_univ, nu_univ, div_one]
  -- clause 2 at `t`, unpacked: for all `X` with positive mass, `V_t(X) ν(X) = paySum(X)`
  have hcl : ∀ t, StrictClause2At (steelmanState n n0 n1 cL l0 l1 cN m0 m1) slObs CC RB t ↔
      ∀ X, 0 < nu CC RB X → paySum CC RB X -
        ∑ ω ∈ X, (pooledDistr n n0 n1 cL l0 l1 cN m0 m1).w ω * uRobot t ω.2.1 ω.2.2 = 0 := by
    intro t
    unfold StrictClause2At
    simp only [slObs_apply, Finset.inter_univ, steelmanState_pr, hV, hprob]
    constructor
    · intro h X hX
      have := h X hX hX
      rw [div_mul_cancel₀ _ hX.ne'] at this
      linarith
    · intro h X hX _
      rw [div_mul_cancel₀ _ hX.ne']
      linarith [h X hX]
  have hLm : nu CC RB {(true, true, true)} = n * cL := by
    rw [hsing]; simp [procTwo]
  have hNm : nu CC RB {(false, true, false)} = (1 - n) * cN := by
    rw [hsing]; simp [procTwo]
  have hdiff := robots_own_vs_pay n n0 n1 cL l0 l1 cN m0 m1
  have hnn : 0 ≤ n * cL := mul_nonneg n0 l0
  have hnn' : 0 ≤ (1 - n) * cN := mul_nonneg (by linarith) m0
  constructor
  · rw [hcl]
    constructor
    · intro h
      by_contra hle
      have hz : n * cL = 0 := le_antisymm (not_lt.mp hle) hnn
      apply h
      intro X _
      rw [hdiff, hLm, hNm]
      simp [uRobot, hz]
    · intro hpos h
      have := h (evM true) (by
        have : nu CC RB {(true, true, true)} ≤ nu CC RB (evM true) :=
          nu_mono CC RB (by intro w; simp only [Finset.mem_singleton, mem_evM]; rintro rfl; rfl)
        linarith)
      rw [hdiff, hLm, hNm] at this
      have h11 : uRobot true true true - uRobot false true true = 11 := by norm_num [uRobot]
      have h0 : uRobot false true false - uRobot false true false = 0 := by ring
      rw [h11, h0, mul_zero, add_zero, if_pos (by simp)] at this
      nlinarith
  · rw [hcl]
    constructor
    · intro h
      by_contra hle
      have hz : (1 - n) * cN = 0 := le_antisymm (not_lt.mp hle) hnn'
      apply h
      intro X _
      rw [hdiff, hLm, hNm]
      simp [uRobot, hz]
    · intro hpos h
      have := h (evM true) (by
        have : nu CC RB {(false, true, false)} ≤ nu CC RB (evM true) :=
          nu_mono CC RB (by intro w; simp only [Finset.mem_singleton, mem_evM]; rintro rfl; rfl)
        linarith)
      rw [hdiff, hLm, hNm] at this
      have h11 : uRobot false true false - uRobot true true false = -11 := by norm_num [uRobot]
      have h0 : uRobot true true true - uRobot true true true = 0 := by ring
      rw [h11, h0, mul_zero, zero_add, if_pos (by simp)] at this
      nlinarith

/-- **Corollary (dp-sl-017's first sentence, with its exact boundary)**: with `n ∈ (0, 1)`, some
point fails clause 2 for every procedure with `c_L + c_N > 0`; at `c_L = c_N = 0` (nobody
smokes) **both** points satisfy clause 2 — so S7's "for every procedure" needs `c_L + c_N > 0`
(a finding: the boundary procedure is honest in both clauses).
Source: dp-sl-017 (S7's first sentence: "clause 2 … is violated at some point for **every**
procedure"); mandate T9 ("state the exact boundary")
Kind: C
Fidelity: exact (the boundary made explicit)
Hyps: (a) `0 < n < 1` -/
theorem steelman_some_point_fails (hn0 : 0 < n) (hn1 : n < 1) :
    (0 < cL + cN → (¬ StrictClause2At (steelmanState n n0 n1 cL l0 l1 cN m0 m1) slObs CC RB false ∨
      ¬ StrictClause2At (steelmanState n n0 n1 cL l0 l1 cN m0 m1) slObs CC RB true)) ∧
    (cL = 0 → cN = 0 → StrictClause2At (steelmanState n n0 n1 cL l0 l1 cN m0 m1) slObs CC RB false ∧
      StrictClause2At (steelmanState n n0 n1 cL l0 l1 cN m0 m1) slObs CC RB true) := by
  obtain ⟨hN, hL⟩ := steelman_clause2_iff n n0 n1 cL l0 l1 cN m0 m1
  constructor
  · intro hsum
    rcases le_or_gt cL 0 with h | h
    · right; exact hL.mpr (mul_pos (by linarith) (by linarith))
    · left; exact hN.mpr (mul_pos hn0 h)
  · intro h0 h1
    constructor
    · by_contra h; rw [hN, h0] at h; simp at h
    · by_contra h; rw [hL, h1] at h; simp at h

/-- **The numbers at P01's table, `n = ½`, `(c_L, c_N) = (1, 1)`** — the atom-level
miscalibration S7 names: at `d_SL` the own-utility state values the atom "`N`-type smokes and
lives" at `+10` while the statistic pays `−1` there; at `d_NSL` the own-utility state values the
atom "`S`-type smokes and is killed" at `−101` while the statistic pays `−90`. (Each atom has
pooled mass `½`.)
Source: `sl-defensible-claims.md` S7 ("`d_SL`: `+10` against the statistic `−1` on (NSL, smoke,
alive); `d_NSL`: `−101` against `−90`"); mandate T9 ("Numbers … at P01's table, `n = ½`")
Kind: N+ -/
theorem steelman_numbers :
    let s := steelmanState (1/2) (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num) 1
      (by norm_num) (by norm_num)
    let C := procTwo 1 (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num)
    let B := robotsHybrid (1/2) (by norm_num) (by norm_num)
    (s true).V {(false, true, false)} = 10 ∧
      paySum C B {(false, true, false)} / nu C B {(false, true, false)} = -1 ∧
      (s false).V {(true, true, true)} = -101 ∧
      paySum C B {(true, true, true)} / nu C B {(true, true, true)} = -90 := by
  intro s C B
  have hsing := robots_nu_single (1/2) (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num) 1
    (by norm_num) (by norm_num)
  have hw : ∀ ω, (pooledDistr (1/2) (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num) 1
      (by norm_num) (by norm_num)).w ω = nu C B {ω} := by
    intro ω
    show (nuCondDistr C B Finset.univ _).w ω = nu C B {ω}
    unfold nuCondDistr
    simp only [Finset.mem_univ, if_true, nu_univ, div_one]
  have hprob : ∀ X, probOf (pooledDistr (1/2) (by norm_num) (by norm_num) 1 (by norm_num) (by norm_num) 1
      (by norm_num) (by norm_num)) X = nu C B X := by
    intro X
    show probOf (nuCondDistr C B Finset.univ _) X = nu C B X
    rw [probOf_nuCondDistr, Finset.inter_univ, nu_univ, div_one]
  have hpay : ∀ w : TickleW, paySum C B {w} = nu C B {w} * uRobot w.1 w.2.1 w.2.2 := by
    intro w
    rw [robots_paySum_worlds]
    simp only [Finset.mem_singleton]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rfl
  have hV : ∀ (t : Bool) (w : TickleW), nu C B {w} ≠ 0 →
      (s t).V {w} = uRobot t w.2.1 w.2.2 := by
    intro t w hne
    show (∑ ω ∈ {w}, (pooledDistr _ _ _ _ _ _ _ _ _).w ω * uRobot t ω.2.1 ω.2.2) /
      probOf (pooledDistr _ _ _ _ _ _ _ _ _) {w} = _
    rw [Finset.sum_singleton, hw, hprob]
    exact mul_div_cancel_left₀ _ hne
  have hNw : nu C B {(false, true, false)} = 1/2 := by rw [hsing]; norm_num [procTwo]
  have hSw : nu C B {(true, true, true)} = 1/2 := by rw [hsing]; norm_num [procTwo]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hV true _ (by rw [hNw]; norm_num)]; norm_num [uRobot]
  · rw [hpay, hNw]; norm_num [uRobot]
  · rw [hV false _ (by rw [hSw]; norm_num)]; norm_num [uRobot]
  · rw [hpay, hSw]; norm_num [uRobot]

end steelman

/-! ## T12: referent separation by coverage failure alone -/

section t12

/-- `paySum` of `⊤` is the value. Source: none: infrastructure. Kind: L -/
theorem paySum_univ_eq_value {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type}
    [∀ d, Fintype (acts d)] (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) :
    paySum C B Finset.univ = value C B := by
  unfold paySum value
  rw [worldEv_univ]

/-- The tremble-limit act value at a realized event is the strict conditional:
`limitVal C B Y = paySum(Y)/ν(Y)` when `ν_C(Y) > 0`.
Source: [[decision-problems-v2]] Lemma 2 (the limiting conditionals are the strict ones at
realized events); `dp-calibration`'s `limitCond_eq_of_pos` pattern
Kind: L -/
theorem limitVal_eq_of_pos {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type}
    [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
    (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (Y : Finset Ω) (h : 0 < nu C B Y) :
    limitVal C B Y = paySum C B Y / nu C B Y := by
  unfold limitVal
  rw [(natTrailingDegree_nuPoly_eq_zero C B Y h).1, coeff_zero_nuPoly, coeff_zero_payPoly]

/-- **Referent separation by coverage failure alone (T12)**: on the hybrid robots at `n = ½`
with the deterministic profile `(c_L, c_N) = (1, 0)` under (M), at `d_L`: the R1-state values
are `(−45, −50)` (smoke), while the tremble-limit evidential values of the pooled point are
`(−90, 0)` (abstain) — both act events are realized (`ν(m=1) = ν(m=0) = ½`), so the limit values
are the strict pooled conditionals; and coverage fails at `d_L` (the `d_N`-runs realize `m = 0`
without consulting `d_L`). No simulation node is involved: Proposition 13's identity
`EV = R1-state` needs recording, and here its coverage clause fails.
Source: dp-sl-2-004(i) ("R1-state smokes at `d_L` while R3 (tremble-limit conditional)
abstains — a split produced by coverage failure with no simulation"); mandate T12
Kind: N+
Fidelity: exact (R3 = `limitVal`, D4; at realized events it is the strict conditional) -/
theorem steelman_r1State_vs_limit :
    let B := robotsHybrid (1/2) (by norm_num) (by norm_num)
    let C := procTwo 1 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    r1StateVal slObs C B true true = -45 ∧ r1StateVal slObs C B true false = -50 ∧
      limitVal C B (slActEv true true ∩ slObs true) = -90 ∧
      limitVal C B (slActEv true false ∩ slObs true) = 0 ∧
      ¬ Covers slObs C B true := by
  intro B C
  have hval : ∀ C' : Proc Bool (fun _ => Bool) ℚ, value C' B =
      (1/2 : ℚ) * ((C' true).w true * (-90) + (C' true).w false * (-100)) +
      (1/2) * ((C' false).w true * (-1) + (C' false).w false * 0) := by
    intro C'; unfold B robotsHybrid; rw [twoType_value]
    simp [typeRate, ubar, uRobot, κRobot]; ring
  have hν : ∀ a, nu C B (evM a) = 1/2 := by
    intro a; unfold B robotsHybrid; rw [(twoType_nu_act _ _ _ _ _ _ _ C a).1]
    cases a <;> simp [C, procTwo] <;> norm_num
  have hpay : paySum C B (evM true) = -45 ∧ paySum C B (evM false) = 0 := by
    constructor <;> · unfold B robotsHybrid; rw [twoType_paySum_act]; norm_num [C, procTwo, ubar, uRobot, κRobot]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold r1StateVal r1StatePay r1StateNu
    simp only [slObs_apply, nu_univ, div_one]
    rw [paySum_univ_eq_value, hval]; simp [C, procTwo, Proc.deviatePure, Proc.deviate]; norm_num
  · unfold r1StateVal r1StatePay r1StateNu
    simp only [slObs_apply, nu_univ, div_one]
    rw [paySum_univ_eq_value, hval]; simp [C, procTwo, Proc.deviatePure, Proc.deviate]; norm_num
  · rw [slActEv_apply, slObs_apply, Finset.inter_univ, limitVal_eq_of_pos C B _ (by rw [hν]; norm_num),
      hpay.1, hν]; norm_num
  · rw [slActEv_apply, slObs_apply, Finset.inter_univ, limitVal_eq_of_pos C B _ (by rw [hν]; norm_num),
      hpay.2, hν]; norm_num
  · unfold B robotsHybrid
    exact twoType_not_covers _ _ _ _ _ _ _ C (by norm_num) (by norm_num) true

end t12

end Cleanroom.Decision.DpSmokingLesion
