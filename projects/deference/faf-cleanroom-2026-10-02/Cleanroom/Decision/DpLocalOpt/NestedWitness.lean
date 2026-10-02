import Cleanroom.Decision.DpLocalOpt.Cells
import Cleanroom.Decision.DpLocalOpt.AmdWitness

/-!
# `dp-local-opt`: witnesses on nested trees (T12's cells on the AMD; T6's CA-22′ check)

Added in repair round 1 (audit r1 fidelity B1/B2 and non-blocking 2).

* **T12 (the anthropic 2×2) evaluated.** On v2's AMD with `0 < q < 1` (full support, `d`
  reached, `𝔼[#_d] = 2 − q > 0`, `μ'(occ d) = 1 > 0`):
  (Definition 6, per-occurrence) `ownDraw6Occ = (4(1−q)/(2−q), (2+2q)/(2−q))` — Theorem 1's
  `Φ_d/𝔼[#_d]`; (Definition 6′, per-run) `ownDraw6'Run = (0, 1)` — Theorem 2′'s
  `V'(C[d↦·])` (every run under seed `a` exits at once, under `b` continues twice). At the
  Definition-6 optimum `q = 1/3` the first cell ties (`8/5 = 8/5`) and the second strictly prefers
  `b`: the two diagonal cells are different evaluators (`amd_cells_differ_at_third`). This is
  the N+ instance of both diagonal cells the round-1 audit asked for.
* **T6 on a nested tree with `μ(occ) ∈ (0,1)`** (`ca22`): CA-22′'s own check, a fair coin between
  the AMD gadget and a leaf paying `7`. For every mixed `m`, `ssaValue(m) = 1 + 2m − 3m²` (the
  instance sum over `#_d = 2` on the continue-continue leaf is exercised, not `x/1 = x`),
  `V(C[d↦m]) = −3/2 m² + m + 4`, `μ(occ) = 1/2`, `offOcc = 7/2`, and the evaluator's argmax is
  `V(C[d↦·])`'s (`ca22_ssa_witness`).
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

/-! ### T12: both diagonal cells on the AMD -/

section amdCells

variable (q : ℚ) (h0 : 0 < q) (h1 : q < 1)

/-- **The (Definition 6, per-occurrence) cell on the AMD, `0 < q < 1`**:
`ownDraw6Occ = (4(1−q)/(2−q), (2+2q)/(2−q))`, i.e. Theorem 1's `Φ_d(C,·)/𝔼[#_d]` with
`𝔼[#_d] = 2 − q`.
Source: `repair/seeds.md` SE-11 (the "(Definition 6, SIA)" cell), SE-13 (closed forms); audit r1
fidelity B2's probe `AmdCells.lean`, adopted
Kind: N+
Fidelity: exact (full support at `d`: `0 < q < 1`)
Hyps: (a) all -/
theorem amd_ownDraw6Occ :
    ownDraw6Occ (procQ q h0.le h1.le) amd () .a = 4 * (1 - q) / (2 - q) ∧
    ownDraw6Occ (procQ q h0.le h1.le) amd () .b = (2 + 2 * q) / (2 - q) := by
  have ha : 0 < (procQ q h0.le h1.le ()).w .a := by simpa [procQ] using h0
  have hb : 0 < (procQ q h0.le h1.le ()).w .b := by simp only [procQ, FinDistr.act2_b]; linarith
  have hE : expCount (procQ q h0.le h1.le) amd () = 2 - q := by rw [amd_expCount]; ring
  constructor
  · rw [ownDraw6Occ_eq _ _ _ ha, amd_siaSum_a, hE]
  · rw [ownDraw6Occ_eq _ _ _ hb, amd_siaSum_b, hE]

/-- **The (Definition 6′, per-run) cell on the AMD, `0 < q < 1`**: `ownDraw6'Run = (0, 1)` —
Theorem 2′'s `V'(C[d↦·])`: under a shared seed `a` every run exits at the root (payoff `0`),
under `b` every run continues twice (payoff `1`).
Source: `repair/seeds.md` SE-12′(i), SE-13; audit r1 fidelity B2's probe `AmdCells.lean`, adopted
Kind: N+
Fidelity: exact (full support at `d`; `μ'_C(occ d) = 1`)
Hyps: (a) all -/
theorem amd_ownDraw6'Run :
    ownDraw6'Run (procQ q h0.le h1.le) amd () .a = 0 ∧
    ownDraw6'Run (procQ q h0.le h1.le) amd () .b = 1 := by
  have ha : 0 < (procQ q h0.le h1.le ()).w .a := by simpa [procQ] using h0
  have hb : 0 < (procQ q h0.le h1.le ()).w .b := by simp only [procQ, FinDistr.act2_b]; linarith
  have hden : ∑ ℓ ∈ occ () amd, leafLaw' (procQ q h0.le h1.le) amd ℓ = 1 := by
    rw [amd_occ_eq_univ, sum_leafLaw']
  constructor
  · rw [ownDraw6'Run_eq _ _ _ ha, hden, div_one]
    unfold ssaNum'
    rw [amd_occ_eq_univ, Proc.deviatePure, pure_a_eq_act2, procQ_deviate]
    unfold amd
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [leafLaw', leafLawSeed, procQ, payoff]
  · rw [ownDraw6'Run_eq _ _ _ hb, hden, div_one]
    unfold ssaNum'
    rw [amd_occ_eq_univ, Proc.deviatePure, pure_b_eq_act2, procQ_deviate]
    unfold amd
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [leafLaw', leafLawSeed, procQ, payoff]

/-- **T12's N+ witness — the two diagonal cells are different evaluators.** At the Definition-6
optimum `q = 1/3` the (6, per-occurrence) cell ties (`8/5 = 8/5`, Theorem 1's fixed point) while
the (6′, per-run) cell strictly prefers `b` (`0 < 1`, Theorem 2′'s argmax is the pure optimum
under 6′). Both cells are evaluated with full support, `𝔼[#_d] = 5/3 > 0` and `μ'(occ) = 1 > 0`
on a nested tree.
Source: `repair/seeds.md` SE-11, SE-13 ("`CX1`: the cells differ"); mandate T12 (load-bearing
item 5's witness); audit r1 fidelity B2
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem amd_cells_differ_at_third :
    ownDraw6Occ (procQ (1/3) (by norm_num) (by norm_num)) amd () .a =
      ownDraw6Occ (procQ (1/3) (by norm_num) (by norm_num)) amd () .b ∧
    ownDraw6'Run (procQ (1/3) (by norm_num) (by norm_num)) amd () .a <
      ownDraw6'Run (procQ (1/3) (by norm_num) (by norm_num)) amd () .b := by
  obtain ⟨ha, hb⟩ := amd_ownDraw6Occ (1/3) (by norm_num) (by norm_num)
  obtain ⟨ha', hb'⟩ := amd_ownDraw6'Run (1/3) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [ha, hb]; norm_num
  · rw [ha', hb']; norm_num

end amdCells

/-! ### T6 on a nested tree with `μ(occ) ∈ (0,1)`: CA-22′'s check -/

section ca22

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι]

/-- `μ_C(occ(d))` at a chance node is the `β`-average of the children's.
Source: none: infrastructure
Kind: L -/
theorem mass_occ_chance (C : Proc ι acts K) (d : ι) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) :
    mass C (.chance n β child) (occ d (.chance n β child)) =
      ∑ i, β.w i * mass C (child i) (occ d (child i)) := by
  unfold mass occ
  rw [Finset.sum_filter, sum_leaves_chance]
  simp only [count_chance, leafLaw_chance, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]

/-- `μ_C(occ(d)) = 0` on a leaf.
Source: none: infrastructure
Kind: L -/
theorem mass_occ_leaf (C : Proc ι acts K) (d : ι) (ω : Ω) (r : K) :
    mass C (.leaf ω r) (occ d (.leaf ω r : Tree Ω ι acts K)) = 0 := by
  simp [mass, occ, count_leaf]

/-- `ssaNum` at a chance node is the `β`-average of the children's.
Source: none: infrastructure
Kind: L -/
theorem ssaNum_chance (C : Proc ι acts K) (d : ι) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) (m : FinDistr K (acts d)) :
    ssaNum C (.chance n β child) d m = ∑ i, β.w i * ssaNum C (child i) d m := by
  unfold ssaNum occ
  rw [Finset.sum_filter, sum_leaves_chance]
  simp only [count_chance, leafLaw_chance, payoff_chance, Finset.sum_filter, Finset.mul_sum,
    mul_ite, mul_zero, mul_assoc]

/-- `ssaNum = 0` on a leaf.
Source: none: infrastructure
Kind: L -/
theorem ssaNum_leaf (C : Proc ι acts K) (d : ι) (ω : Ω) (r : K) (m : FinDistr K (acts d)) :
    ssaNum C (.leaf ω r) d m = 0 := by
  simp [ssaNum, occ, count_leaf]

variable [∀ d, DecidableEq (acts d)]

/-- `offOcc` at a chance node is the `β`-average of the children's.
Source: none: infrastructure
Kind: L -/
theorem offOcc_chance (C : Proc ι acts K) (d : ι) {n : ℕ} (β : FinDistr K (Fin n))
    (child : Fin n → Tree Ω ι acts K) :
    offOcc C (.chance n β child) d = ∑ i, β.w i * offOcc C (child i) d := by
  unfold offOcc occ
  rw [Finset.sum_filter, sum_leaves_chance]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, count_chance, leafLaw_chance,
    payoff_chance, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

/-- `offOcc = r` on a leaf paying `r`.
Source: none: infrastructure
Kind: L -/
theorem offOcc_leaf (C : Proc ι acts K) (d : ι) (ω : Ω) (r : K) :
    offOcc C (.leaf ω r) d = r := by
  have h1 : Fintype.card (Tree.leaf ω r : Tree Ω ι acts K).Leaves = 1 := by
    first | rfl | exact Fintype.card_unit
  simp [offOcc, occ, count_leaf, h1]

end ca22

section ca22Amd

/-- **CA-22′'s tree**: a fair coin between the AMD gadget and a leaf paying `7`. Nested at `d`
(the AMD's continue-continue run has `#_d = 2`) with `μ(occ(d)) = 1/2`.
Source: `repair/calibration.md` CA-22′ (line 105: "chance `½ →` AMD gadget, `½ →` leaf `7`");
the same tree and numbers under the unprimed label in `adversary/calibration.md` §9 (CA-21 /
CA-22)
Kind: D -/
def ca22 : Tree AmdW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair ![amd, .leaf .sa 7]

/-- `offOcc = 0` on the AMD (every run occurs).
Source: none: infrastructure
Kind: L -/
theorem amd_offOcc (c : ℚ) (c0 : 0 ≤ c) (c1 : c ≤ 1) : offOcc (procQ c c0 c1) amd () = 0 := by
  simp [offOcc, amd_occ_eq_univ]

/-- `ssaNum` on the AMD for the deviation `(m, 1 − m)`: `(1 − m)(3m + 1)` — the AMD's value
polynomial, since every run occurs.
Source: none: infrastructure
Kind: L -/
theorem amd_ssaNum (c : ℚ) (c0 : 0 ≤ c) (c1 : c ≤ 1) (m : ℚ) (m0 : 0 ≤ m) (m1 : m ≤ 1) :
    ssaNum (procQ c c0 c1) amd () (FinDistr.act2 m m0 m1) = (1 - m) * (3 * m + 1) := by
  unfold ssaNum
  rw [amd_occ_eq_univ, procQ_deviate]
  unfold amd
  rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
    Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
  simp [procQ]
  ring

/-- **T6's nested N+ witness (CA-22′)**: on `ca22` with any `C = (c, 1 − c)` and every mixed
deviation `m` (on a one-point tree `C[d ↦ m]` forgets `C(d)`, so nothing below depends on `c`:
the "any `C`" is decoration, audit r2 adversarial N5; the witness where `C(d)` enters is
`twoPoint_ssa_witness`): `μ_C(occ(d)) = 1/2`, `offOcc = 7/2`, the EDT+SSA evaluator is
`ssaValue(m) = 1 + 2m − 3m²` (CA-22′'s `𝔼[r ∣ occ](m) = −3m² + 2m + 1`) and
`V(C[d ↦ m]) = −3/2 m² + m + 4`, so `ssaValue(m) ≤ ssaValue(m') ↔ V(C[d↦m]) ≤ V(C[d↦m'])` is
exercised with nesting (`#_d = 2` on the continue-continue run), a mixed deviation and a proper
occurrence event at once; `ssaValue_mul_mass`'s instance-sum cancellation is `2·(x/2) = x` there,
not `x/1 = x`.
Source: `repair/calibration.md` CA-22′ (line 105: "`μ(occ) = ½` for every `m`,
`𝔼[r ∣ occ](m) = −3m² + 2m + 1`, `V(C[d↦m]) = −3/2 m² + m + 4`, difference `7/2`";
`adversary/calibration.md` §9 has the same check unprimed); audit r1 fidelity non-blocking 2
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem ca22_ssa_witness (c : ℚ) (c0 : 0 ≤ c) (c1 : c ≤ 1) (m : ℚ) (m0 : 0 ≤ m) (m1 : m ≤ 1) :
    count () ca22 ⟨0, ⟨.b, ⟨.b, ()⟩⟩⟩ = 2 ∧
    mass (procQ c c0 c1) ca22 (occ () ca22) = 1/2 ∧
    offOcc (procQ c c0 c1) ca22 () = 7/2 ∧
    ssaValue (procQ c c0 c1) ca22 () (FinDistr.act2 m m0 m1) = 1 + 2 * m - 3 * m ^ 2 ∧
    value ((procQ c c0 c1).deviate () (FinDistr.act2 m m0 m1)) ca22 = -3/2 * m ^ 2 + m + 4 := by
  have hmass : mass (procQ c c0 c1) ca22 (occ () ca22) = 1/2 := by
    unfold ca22
    rw [mass_occ_chance, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mass_occ_leaf,
      amd_occ_eq_univ, mass_univ, FinDistr.fair, FinDistr.coin]
    norm_num
  refine ⟨rfl, hmass, ?_, ?_, ?_⟩
  · unfold ca22
    rw [offOcc_chance, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, offOcc_leaf,
      amd_offOcc, FinDistr.fair, FinDistr.coin]
    norm_num
  · rw [ssaValue_eq_div, hmass]
    unfold ca22
    rw [ssaNum_chance, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ssaNum_leaf,
      amd_ssaNum, FinDistr.fair, FinDistr.coin]
    ring
  · rw [procQ_deviate]
    unfold ca22
    simp only [value_chance, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      value_leaf, amd_value, FinDistr.fair, FinDistr.coin]
    ring

end ca22Amd

end Cleanroom.Decision.DpLocalOpt
