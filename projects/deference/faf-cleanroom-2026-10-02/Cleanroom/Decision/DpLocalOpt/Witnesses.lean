import Cleanroom.Decision.DpLocalOpt.ChainRule
import Cleanroom.Decision.DpLocalOpt.Trees
import Cleanroom.Decision.DpLocalOpt.AmdWitness

/-!
# `dp-local-opt`: the `k`-fold mugging (T8(c), T9), draw-keyed Death in Damascus (T8(e)) and
weak node-SSC on the AMD (T15)

* **Dilution (T9).** On `kfold k x y b` with `q := C(d)(pay)`, Theorem 1's difference
  `Φ(pay) − Φ(refuse)` is `½(−x + D_H)` where `D_H` is the simulated branch's difference:
  linear coupling `D_H = y` for every `k`, `q` — no dilution (`kfold_linear_sia_sub`); convex
  coupling at `q = 1`: `D_H = k y` (`kfold_convex_sia_sub_one`); concave coupling at `q = 1`:
  `D_H = y·[k = 1]`, so all-pay is never ratifiable for `k ≥ 2`, `x > 0`
  (`kfold_concave_sia_sub_one`).
* **A Theorem-1 fixed point below the refuse value (T8(c)).** Convex `3`-fold, `y < x < 3y`:
  all-pay satisfies Theorem 1's condition with `V = ½(y − x) < 0 = V(refuse)`
  (`kfold_convex_allPay_thm1_not_optimal`); at `x = 2`, `y = 3/2` it is a strict local maximum
  on `[1/2, 1]`.
* **Death in Damascus (T8(e)).** `deathDamascus 0 1000 1`: `V = −2000q² + 2001q − 1` is concave,
  Theorem 1's interior fixed point `q = 2001/4000` *is* the optimum; the calibrated evidential
  tie `1001/2000` sits `1/8000` below it (`deathDamascus_thm1_optimum`).
* **Weak node-SSC (T15).** On the AMD the two nodes' normalised downtree payoff laws agree iff
  `q = 0` (always continue), where `V = 1 < 4/3` (`amd_nodeSSC_iff`).
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

/-! ### `Φ` on the `k`-fold mugging -/

section kfold

variable (y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-- `Φ` vanishes on the bottom chance node (no decision below).
Source: none: infrastructure
Kind: L -/
theorem kfoldH_zero_siaSum (j : ℕ) (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    siaSum C (kfoldH y b hb 0 j) () a = 0 := by
  simp [kfoldH, siaSum_chance, Fin.sum_univ_two]

/-- `Φ(pay)` one level up the simulated branch.
Source: none: infrastructure
Kind: L -/
theorem kfoldH_succ_siaSum_pay (k j : ℕ) :
    siaSum (procQ q h0 h1) (kfoldH y b hb (k + 1) j) () .a =
      q * siaSum (procQ q h0 h1) (kfoldH y b hb k (j + 1)) () .a +
        (1 - q) * siaSum (procQ q h0 h1) (kfoldH y b hb k j) () .a +
        value (procQ q h0 h1) (kfoldH y b hb k (j + 1)) := by
  simp only [kfoldH, siaSum_decision_self, Act2.sum_univ, procQ, FinDistr.act2_a, FinDistr.act2_b]

/-- `Φ(refuse)` one level up the simulated branch.
Source: none: infrastructure
Kind: L -/
theorem kfoldH_succ_siaSum_refuse (k j : ℕ) :
    siaSum (procQ q h0 h1) (kfoldH y b hb (k + 1) j) () .b =
      q * siaSum (procQ q h0 h1) (kfoldH y b hb k (j + 1)) () .b +
        (1 - q) * siaSum (procQ q h0 h1) (kfoldH y b hb k j) () .b +
        value (procQ q h0 h1) (kfoldH y b hb k j) := by
  simp only [kfoldH, siaSum_decision_self, Act2.sum_univ, procQ, FinDistr.act2_a, FinDistr.act2_b]

/-- The simulated branch's difference `Φ(pay) − Φ(refuse)` satisfies
`D(k+1, j) = q D(k, j+1) + (1−q) D(k, j) + V(k, j+1) − V(k, j)`.
Source: none: infrastructure
Kind: L -/
theorem kfoldH_succ_sia_sub (k j : ℕ) :
    siaSum (procQ q h0 h1) (kfoldH y b hb (k + 1) j) () .a -
      siaSum (procQ q h0 h1) (kfoldH y b hb (k + 1) j) () .b =
      q * (siaSum (procQ q h0 h1) (kfoldH y b hb k (j + 1)) () .a -
          siaSum (procQ q h0 h1) (kfoldH y b hb k (j + 1)) () .b) +
        (1 - q) * (siaSum (procQ q h0 h1) (kfoldH y b hb k j) () .a -
          siaSum (procQ q h0 h1) (kfoldH y b hb k j) () .b) +
        (value (procQ q h0 h1) (kfoldH y b hb k (j + 1)) -
          value (procQ q h0 h1) (kfoldH y b hb k j)) := by
  rw [kfoldH_succ_siaSum_pay, kfoldH_succ_siaSum_refuse]; ring

/-- `Φ` on the whole mugging: `½` the real node's forced value plus `½` the simulated branch's.
Source: none: infrastructure
Kind: L -/
theorem kfold_sia_sub (k : ℕ) (x : ℚ) :
    siaSum (procQ q h0 h1) (kfold k x y b hb) () .a -
      siaSum (procQ q h0 h1) (kfold k x y b hb) () .b =
      (1 / 2) * (-x) + (1 / 2) * (siaSum (procQ q h0 h1) (kfoldH y b hb k 0) () .a -
        siaSum (procQ q h0 h1) (kfoldH y b hb k 0) () .b) := by
  simp [kfold, siaSum_chance, siaSum_decision_self, Fin.sum_univ_two, FinDistr.fair, FinDistr.coin,
    Act2.sum_univ, procQ]
  ring

/-- **Linear coupling: no dilution on the simulated branch** — `D(k', j) = k' y / k` for
`j + k' ≤ k`.
Source: `repair/spectrum.md` SP-23 ("**linear** coupling: `ΔG = −x` at the real node, `y/k` at
each simulation, `∑_q R_q ΔG_q = ½(−x) + k · ½ · y/k = (y−x)/2` — no dilution")
Kind: P -/
theorem kfoldH_linear_sia_sub (k : ℕ) (hk : 0 < k) :
    ∀ k' j, j + k' ≤ k →
      siaSum (procQ q h0 h1) (kfoldH y (linearB k) (linearB_bounds k) k' j) () .a -
        siaSum (procQ q h0 h1) (kfoldH y (linearB k) (linearB_bounds k) k' j) () .b =
        k' * y / k
  | 0, j, _ => by rw [kfoldH_zero_siaSum, kfoldH_zero_siaSum]; simp
  | k' + 1, j, hj => by
      rw [kfoldH_succ_sia_sub, kfoldH_linear_sia_sub k hk k' (j + 1) (by omega),
        kfoldH_linear_sia_sub k hk k' j (by omega),
        kfoldH_linear_value k hk y q h0 h1 k' (j + 1) (by omega),
        kfoldH_linear_value k hk y q h0 h1 k' j (by omega)]
      push_cast
      field_simp
      ring

/-- **T9(a) — linear coupling: `Φ(pay) − Φ(refuse) = (y − x)/2` for every `k ≥ 1` and every `q`**:
SIA's `k`-fold weighting of being a simulation exactly compensates the `1/k` influence of one
draw. No dilution.
Source: [[fable-slop-notes]] "Dilution" ("with linear `b_j = j/k`, … no dilution");
`repair/spectrum.md` SP-23; dp-core-065; dp-cf-2-021; dp-cf-006(c)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem kfold_linear_sia_sub (k : ℕ) (hk : 0 < k) (x : ℚ) :
    siaSum (procQ q h0 h1) (kfold k x y (linearB k) (linearB_bounds k)) () .a -
      siaSum (procQ q h0 h1) (kfold k x y (linearB k) (linearB_bounds k)) () .b = (y - x) / 2 := by
  rw [kfold_sia_sub, kfoldH_linear_sia_sub y q h0 h1 k hk k 0 (by omega)]
  have : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp
  ring

/-- **Convex coupling at `q = 1`**: `D(k', j) = k' y · [j + k' = k]` for `j + k' ≤ k`.
Source: [[fable-slop-notes]] "Dilution" (convex coupling, `∂V/∂q|_{q=1} = ½(ky − x)`)
Kind: P -/
theorem kfoldH_convex_sia_sub_one (k : ℕ) :
    ∀ k' j, j + k' ≤ k →
      siaSum (procQ 1 zero_le_one le_rfl) (kfoldH y (convexB k) (convexB_bounds k) k' j) () .a -
        siaSum (procQ 1 zero_le_one le_rfl) (kfoldH y (convexB k) (convexB_bounds k) k' j) () .b =
        if j + k' = k then k' * y else 0
  | 0, j, _ => by rw [kfoldH_zero_siaSum, kfoldH_zero_siaSum]; simp
  | k' + 1, j, hj => by
      rw [kfoldH_succ_sia_sub, kfoldH_convex_sia_sub_one k k' (j + 1) (by omega),
        kfoldH_convex_value_one, kfoldH_convex_value_one]
      have hlt : ¬ j + k' = k := by omega
      have e1 : j + 1 + k' = j + (k' + 1) := by omega
      rw [e1, if_neg hlt]
      by_cases h : j + (k' + 1) = k
      · simp only [h, if_true]; push_cast; ring
      · simp only [h, if_false]; ring

/-- **T9(c) — convex coupling: at `q = 1`, `Φ(pay) − Φ(refuse) = ½(k y − x)`**: SIA
*over*-incentivises under unanimity coupling.
Source: [[fable-slop-notes]] "Dilution" ("With convex coupling …, `∂V/∂q|_{q=1} = ½(ky − x)`");
SP-23; dp-core-065
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem kfold_convex_sia_sub_one (k : ℕ) (x : ℚ) :
    siaSum (procQ 1 zero_le_one le_rfl) (kfold k x y (convexB k) (convexB_bounds k)) () .a -
      siaSum (procQ 1 zero_le_one le_rfl) (kfold k x y (convexB k) (convexB_bounds k)) () .b =
      (1 / 2) * (k * y - x) := by
  rw [kfold_sia_sub, kfoldH_convex_sia_sub_one y k k 0 (by omega)]
  simp; ring

/-- Concave coupling at `q = 1`: the simulated branch is worth `y` iff at least one draw pays.
Source: none: infrastructure
Kind: L -/
theorem kfoldH_concave_value_one :
    ∀ k' j, value (procQ 1 zero_le_one le_rfl) (kfoldH y concaveB concaveB_bounds k' j) =
      if 1 ≤ j + k' then y else 0
  | 0, j => by
      rw [kfoldH_zero_value]; unfold concaveB
      simp only [add_zero]; split_ifs <;> simp
  | k' + 1, j => by
      rw [kfoldH_succ_value, kfoldH_concave_value_one k' (j + 1), kfoldH_concave_value_one k' j]
      have : (1 ≤ j + 1 + k') ↔ (1 ≤ j + (k' + 1)) := by omega
      simp only [this]; ring

/-- **Concave coupling at `q = 1`**: `D(k', j) = y` iff `j = 0 ∧ k' = 1`, else `0`.
Source: [[fable-slop-notes]] "Dilution" (concave coupling, `∂V/∂q` at `q = 1` is `−x/2`)
Kind: P -/
theorem kfoldH_concave_sia_sub_one :
    ∀ k' j, siaSum (procQ 1 zero_le_one le_rfl) (kfoldH y concaveB concaveB_bounds k' j) () .a -
      siaSum (procQ 1 zero_le_one le_rfl) (kfoldH y concaveB concaveB_bounds k' j) () .b =
      if j = 0 ∧ k' = 1 then y else 0
  | 0, j => by rw [kfoldH_zero_siaSum, kfoldH_zero_siaSum]; simp
  | k' + 1, j => by
      rw [kfoldH_succ_sia_sub, kfoldH_concave_sia_sub_one k' (j + 1),
        kfoldH_concave_sia_sub_one k' j, kfoldH_concave_value_one, kfoldH_concave_value_one]
      have h1 : 1 ≤ j + 1 + k' := by omega
      rw [if_pos h1]
      by_cases hj : j = 0
      · subst hj
        by_cases hk : k' = 0
        · subst hk; simp
        · have h2 : 1 ≤ 0 + k' := by omega
          have h3 : ¬ (0 + 1 = 0 ∧ k' = 1) := by omega
          have h4 : ¬ (0 = 0 ∧ k' + 1 = 1) := by omega
          rw [if_neg h3, if_pos h2, if_neg h4]
          by_cases h5 : 0 = 0 ∧ k' = 1
          · rw [if_pos h5]; ring
          · rw [if_neg h5]; ring
      · have h2 : 1 ≤ j + k' := by omega
        have h3 : ¬ (j + 1 = 0 ∧ k' = 1) := by omega
        have h4 : ¬ (j = 0 ∧ k' = 1) := by omega
        have h5 : ¬ (j = 0 ∧ k' + 1 = 1) := by omega
        rw [if_neg h3, if_neg h4, if_pos h2, if_neg h5]; ring

/-- **T9(b) at the endpoint — concave coupling: at `q = 1`, `Φ(pay) − Φ(refuse) = −x/2` for
`k ≥ 2`**: all-pay is never ratifiable for `x > 0`.
Source: [[fable-slop-notes]] "Dilution" ("With concave coupling …, `∂V/∂q` at `q = 1` is `−x/2`:
the marginal instance's pivotality vanishes as compliance rises"); SE-13
Kind: P
Fidelity: weaker: the `q = 1` endpoint only (the interior stationarity `x = yk(1−q)^{k−1}` is not
shipped)
Hyps: (a) all -/
theorem kfold_concave_sia_sub_one (k : ℕ) (hk : 2 ≤ k) (x : ℚ) :
    siaSum (procQ 1 zero_le_one le_rfl) (kfold k x y concaveB concaveB_bounds) () .a -
      siaSum (procQ 1 zero_le_one le_rfl) (kfold k x y concaveB concaveB_bounds) () .b = -x / 2 := by
  rw [kfold_sia_sub, kfoldH_concave_sia_sub_one]
  have : k ≠ 1 := by omega
  simp [this]; ring

/-- **T8(c) — Theorem 1 can ratify a pay-when-you-shouldn't policy**: on the convex `3`-fold
mugging with `y < x < 3y`, all-pay (`q = 1`) satisfies Theorem 1's condition
(`Φ(pay) − Φ(refuse) = ½(3y − x) ≥ 0`) while `V(1) = ½(y − x) < 0 = V(0)`: not optimal.
Source: [[fable-slop-notes]] "Dilution" ("for `y < x < ky` the all-pay policy is
Theorem-1-ratifiable but not optimal — a pay-when-you-shouldn't equilibrium"); SP-15; dp-core-048;
dp-cf-122
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem kfold_convex_allPay_thm1_not_optimal (x : ℚ) (hyx : y < x) (hx3y : x < 3 * y) :
    Thm1At (procQ 1 zero_le_one le_rfl) (kfold 3 x y (convexB 3) (convexB_bounds 3)) () ∧
    value (procQ 1 zero_le_one le_rfl) (kfold 3 x y (convexB 3) (convexB_bounds 3)) = (y - x) / 2 ∧
    value (procQ 0 le_rfl zero_le_one) (kfold 3 x y (convexB 3) (convexB_bounds 3)) = 0 ∧
    ¬ IsOptimal (procQ 1 zero_le_one le_rfl) (kfold 3 x y (convexB 3) (convexB_bounds 3)) := by
  have hsub := kfold_convex_sia_sub_one y 3 x
  refine ⟨?_, by rw [kfold3_convex_value]; ring, by rw [kfold3_convex_value]; ring, ?_⟩
  · rw [thm1At_procQ_iff]
    refine ⟨fun _ => ?_, fun h => absurd h (by norm_num)⟩
    have : (0 : ℚ) ≤ (1 / 2) * (3 * y - x) := by push_cast at hsub; linarith
    linarith
  · intro h
    have := h (procQ 0 le_rfl zero_le_one)
    rw [kfold3_convex_value, kfold3_convex_value] at this
    linarith

/-- **dp-cf-122's instance**: at `x = 2`, `y = 3/2`, `V(q) = q(3q² − 4)/4` and all-pay is a strict
local maximum: `V(q) < V(1)` for every `q ∈ [1/2, 1)`.
Source: dp-cf-122 ("at `x = 2, y = 3/2`: `V = q(3q² − 4)/4`, `q = 1` a strict local maximum on
`[0,1]`")
Kind: N+ -/
theorem kfold_convex_instance :
    (∀ q (h0 : 0 ≤ q) (h1 : q ≤ 1),
      value (procQ q h0 h1) (kfold 3 2 (3/2) (convexB 3) (convexB_bounds 3)) =
        q * (3 * q ^ 2 - 4) / 4) ∧
    (∀ q (h0 : 1/2 ≤ q) (h1 : q < 1),
      value (procQ q (by linarith) h1.le) (kfold 3 2 (3/2) (convexB 3) (convexB_bounds 3)) <
        value (procQ 1 zero_le_one le_rfl) (kfold 3 2 (3/2) (convexB 3) (convexB_bounds 3))) := by
  refine ⟨fun q h0 h1 => by rw [kfold3_convex_value]; ring, ?_⟩
  intro q h0 h1
  rw [kfold3_convex_value, kfold3_convex_value]
  nlinarith [sq_nonneg q, sq_nonneg (q - 1)]

end kfold

/-! ### Draw-keyed Death in Damascus -/

section deathDamascus

/-- `Φ(stay) − Φ(flee) = 2001 − 4000q` on `deathDamascus 0 1000 1`, computed from the tree through
`siaSum`'s node equations (the two `d`-nodes both contribute).
Source: none: infrastructure
Kind: L -/
theorem deathDamascus_sia_sub (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    siaSum (procQ q h0 h1) (deathDamascus 0 le_rfl zero_le_one 1000 1) () .a -
      siaSum (procQ q h0 h1) (deathDamascus 0 le_rfl zero_le_one 1000 1) () .b =
      2001 - 4000 * q := by
  simp [deathDamascus, siaSum_chance, siaSum_decision_self, value_decision, Fin.sum_univ_two,
    FinDistr.coin, Act2.sum_univ, procQ]
  ring

/-- **T8(e) — on draw-keyed Death in Damascus Theorem 1's interior fixed point is the optimum**:
`V = −2000q² + 2001q − 1` is concave; `Φ(stay) − Φ(flee) = 2001 − 4000q` vanishes at
`q = 2001/4000`, which maximises `V` (`V = 3996001/8000`); the calibrated evidential tie
`q = 1001/2000` has `V = 999/2`, `1/8000` below the optimum. Contrast with Wei Dai's AMD, where
the interior fixed point is the minimum.
Source: `sl-workflow/notes/repair/P03.md` P03-7 ("`V_B(1001/2000) = V_B(1/2) = 999/2`, optimum
`2001/4000` with `V_B = 3996001/8000 = 499.500125`, gap `1/8000`"); dp-sl-2-009 (the
"ratifiable ≠ optimal by `1/8000`" numerals concern the evidential tie, `dp-calibration`'s
object)
Kind: N+
Fidelity: exact (the `p = 0`, `L = 1000`, `c = 1` instance)
Hyps: (a) all -/
theorem deathDamascus_thm1_optimum :
    Thm1At (procQ (2001/4000) (by norm_num) (by norm_num))
      (deathDamascus 0 le_rfl zero_le_one 1000 1) () ∧
    IsOptimal (procQ (2001/4000) (by norm_num) (by norm_num))
      (deathDamascus 0 le_rfl zero_le_one 1000 1) ∧
    value (procQ (2001/4000) (by norm_num) (by norm_num))
      (deathDamascus 0 le_rfl zero_le_one 1000 1) = 3996001/8000 ∧
    value (procQ (1001/2000) (by norm_num) (by norm_num))
      (deathDamascus 0 le_rfl zero_le_one 1000 1) = 999/2 ∧
    (3996001/8000 : ℚ) - 999/2 = 1/8000 := by
  refine ⟨?_, ?_, by rw [deathDamascus_value_instance]; norm_num,
    by rw [deathDamascus_value_instance]; norm_num, by norm_num⟩
  · rw [thm1At_procQ_iff]
    have := deathDamascus_sia_sub (2001/4000) (by norm_num) (by norm_num)
    constructor
    · intro _; linarith
    · intro _; linarith
  · rw [isOptimal_procQ_iff]
    intro r r0 r1
    rw [deathDamascus_value_instance, deathDamascus_value_instance]
    nlinarith [sq_nonneg (r - 2001/4000)]

end deathDamascus

/-! ### Weak node-SSC on the AMD -/

section nodeSSC

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]

/-- The normalised downtree payoff law at a node: `μ_C(r = v ∣ reach q)`, as
`(∑_{ℓ below q, r(ℓ) = v} μ_C(ℓ)) / R_q(C)`. **Junk value:** Lean's `x / 0 = 0` makes it the zero
law at an unreached node (`R_q = 0`), where Claim 1.2's `θ₂` is undefined — on the AMD this is
the second node at `q = 1`; `amd_nodeSSC_iff` is unaffected (its forward direction reads `v = 0`
at the root, where `R = 1`). `dp-fairness-reloc` states the same AMD fact over its `thetaAt`
(`amd_thetaAt_eq_iff`); this is a second definition of record for one law.
Source: [[fable-slop-notes]] Claim 1.2 ("the two nodes' downtree laws")
Kind: D -/
def downLaw (C : Proc ι acts K) (B : Tree Ω ι acts K) (q : B.DecNode) (v : K) : K :=
  (∑ ℓ ∈ leavesBelow B q, if payoff B ℓ = v then leafLaw C B ℓ else 0) / reach C B q

/-- The AMD's second node.
Source: none: infrastructure
Kind: D -/
def amdNode2 : amd.DecNode := some ⟨.b, none⟩

/-- **T15 — weak node-SSC on the AMD holds exactly at `q = 0`**: the two `d`-nodes' normalised
downtree payoff laws (`q δ₀ + (1−q) θ₂` at the root, `θ₂ = q δ₄ + (1−q) δ₁` at the second node)
agree iff `q = C(d)(a) = 0`, the always-continue procedure, whose value `1` is below the optimum
`4/3`: weak node-SSC admits the AMD but selects a dominated procedure on it.
Source: [[fable-slop-notes]] Claim 1.2 ("equal iff `x = 0`. So weak node-SSC *admits* the AMD tree,
but only for the procedure 'always continue', value `1 < 4/3`") | dp-core-062
Kind: N+
Fidelity: exact (laws compared as normalised payoff-value laws)
Hyps: (a) all -/
theorem amd_nodeSSC_iff (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ((∀ v, downLaw (procQ q h0 h1) amd none v = downLaw (procQ q h0 h1) amd amdNode2 v) ↔ q = 0) ∧
    value (procQ 0 le_rfl zero_le_one) amd = 1 ∧
    value (procQ (1/3) (by norm_num) (by norm_num)) amd = 4/3 := by
  refine ⟨?_, by rw [amd_value]; norm_num, by rw [amd_value]; norm_num⟩
  have hroot : ∀ v, downLaw (procQ q h0 h1) amd none v =
      (if (0 : ℚ) = v then q else 0) + ((if (4 : ℚ) = v then (1 - q) * q else 0) +
        (if (1 : ℚ) = v then (1 - q) * (1 - q) else 0)) := by
    intro v
    unfold downLaw leavesBelow amd
    rw [Finset.sum_filter, sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf,
      sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [procQ]
  have hnode : ∀ v, downLaw (procQ q h0 h1) amd amdNode2 v =
      ((if (4 : ℚ) = v then (1 - q) * q else 0) + (if (1 : ℚ) = v then (1 - q) * (1 - q) else 0)) /
        (1 - q) := by
    intro v
    unfold downLaw leavesBelow amd amdNode2
    rw [Finset.sum_filter, sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf,
      sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [procQ]
  constructor
  · intro h
    have := h 0
    rw [hroot, hnode] at this
    norm_num at this
    exact this
  · rintro rfl v
    rw [hroot, hnode]
    norm_num

end nodeSSC

end Cleanroom.Decision.DpLocalOpt
