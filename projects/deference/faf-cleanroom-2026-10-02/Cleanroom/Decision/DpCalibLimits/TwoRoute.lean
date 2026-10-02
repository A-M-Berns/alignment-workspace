import Cleanroom.Decision.DpCalibLimits.Rays
import Mathlib.Algebra.Polynomial.Derivative

/-!
# T2(c),(d) — Ray dependence on the two-route tree; the single-point claim beyond two actions

[[dp-calib-limits-mandate]] T2(c),(d) (dp-sl-2-012, SE-18′(b), dp-sl-029).

* **The two-route tree** `twoRoute` (SE-18′(b), `seeds.md` line 81): a fair coin; left, point
  `e` whose `u`-edge leads to a `d`-copy (`a ↦ 10`, `b ↦ 0`) and whose `v`-edge leads off
  `O_d`; right, point `f` whose `w`-edge leads to a `d`-copy (`a ↦ 0`, `b ↦ 30`) and whose
  `z`-edge leads off `O_d`. Under `C₀` with `C₀(e)(u) = 0 = C₀(f)(w)` (so `O_d` is
  unrealized, `twoRoute_obs_null`), the limiting act values at `d` are `(5, 15)` along the
  uniform ray, `(10, 0)` along `s = ε, t = ε²`, `(0, 30)` along `s = ε², t = ε`
  (`twoRoute_values`): the argmax reverses between rays. N+, the ray-dependence SE-18′(b)
  computes.
* **The single-point claim** (P07-1′ (ii): ray dependence "needs two points"; the survey
  headline dp-sl-029 compresses it to "absent from single-point classes"): **refuted beyond two
  actions** by a one-node, three-action tree with `C = δ_a` and the unrealized observation
  `{b, c}`: the conditional of `{b}` given `{b, c}` is `1` along the ray `(w_b, w_c) = (ε, ε²)`
  and `0` along `(ε², ε)` (`threeAct_ray_dependent`). The two-action version is the surviving
  neighbour, proved in `SinglePoint.lean` (`twoAct_single_point_ray_independent`, repair
  round 1).

Coefficients of the concrete polynomials are read off as `p.eval 0` (order `0`) and
`(derivative p).eval 0` (order `1`), which `simp` evaluates on any expression.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-! ## Limits from the first two coefficients -/

section coeffOne

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `coeff 1 p = (derivative p).eval 0`. Source: none: infrastructure. Kind: L -/
theorem coeff_one_eq_eval_zero_derivative (p : Polynomial K) :
    p.coeff 1 = (Polynomial.derivative p).eval 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  simp

/-- A polynomial with `coeff 0 = 0` and `coeff 1 ≠ 0` has order `1`.
Source: none: infrastructure. Kind: L -/
theorem natTrailingDegree_eq_one_of_coeff {p : Polynomial K} (h0 : p.coeff 0 = 0)
    (h1 : p.coeff 1 ≠ 0) : p.natTrailingDegree = 1 := by
  have hne : p ≠ 0 := fun h => h1 (by rw [h, Polynomial.coeff_zero])
  refine le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero h1) ?_
  apply Polynomial.le_natTrailingDegree hne
  intro m hm
  have : m = 0 := by omega
  rw [this, h0]

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- A limiting act value along a ray whose event polynomial has order `1`.
Source: none: infrastructure. Kind: L -/
theorem limitValRay_of_coeff_one (R : Ray ι acts K) (B : Tree Ω ι acts K) (Y : Finset Ω)
    (h0 : (nuPolyRay R B Y).coeff 0 = 0) (h1 : (nuPolyRay R B Y).coeff 1 ≠ 0) :
    limitValRay R B Y = (payPolyRay R B Y).coeff 1 / (nuPolyRay R B Y).coeff 1 := by
  unfold limitValRay
  rw [natTrailingDegree_eq_one_of_coeff h0 h1]

/-- A limiting conditional along a ray whose condition polynomial has order `1`.
Source: none: infrastructure. Kind: L -/
theorem limitCondRay_of_coeff_one (R : Ray ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω)
    (h0 : (nuPolyRay R B O).coeff 0 = 0) (h1 : (nuPolyRay R B O).coeff 1 ≠ 0) :
    limitCondRay R B X O = (nuPolyRay R B (X ∩ O)).coeff 1 / (nuPolyRay R B O).coeff 1 := by
  unfold limitCondRay
  rw [natTrailingDegree_eq_one_of_coeff h0 h1]

/-- The uniform-ray instance. Source: none: infrastructure. Kind: L -/
theorem limitVal_of_coeff_one (C : Proc ι acts K) (B : Tree Ω ι acts K) (Y : Finset Ω)
    (h0 : (nuPoly C B Y).coeff 0 = 0) (h1 : (nuPoly C B Y).coeff 1 ≠ 0) :
    limitVal C B Y = (payPoly C B Y).coeff 1 / (nuPoly C B Y).coeff 1 := by
  rw [← limitValRay_uniform, limitValRay_of_coeff_one (uniformRay C) B Y
    (by rwa [nuPolyRay_uniform]) (by rwa [nuPolyRay_uniform]), nuPolyRay_uniform,
    payPolyRay_uniform]

end coeffOne

/-- `|Act2| = 2` as a rational. Source: none: infrastructure. Kind: L -/
theorem act2_card_rat : ((Fintype.card Act2 : ℕ) : ℚ) = 2 := by
  rw [show Fintype.card Act2 = 2 from rfl]; norm_num

/-! ## The two-route tree -/

/-- The two-route tree's points: `d` (queried on both routes), `e` (left), `f` (right).
Source: SE-18′(b) (`seeds.md` line 81)
Kind: D -/
inductive TrPt : Type
  | d
  | e
  | f
  deriving DecidableEq, Fintype

instance : Nonempty TrPt := ⟨.d⟩

/-- The two-route tree's worlds: `(route, act)` on the `d`-copies, and one off-`O_d` world
per route.
Source: SE-18′(b)
Kind: D -/
inductive TrW : Type
  | la
  | lb
  | ra
  | rb
  | offL
  | offR
  deriving DecidableEq, Fintype

/-- The route's point: index `0` = left = `e`, index `1` = right = `f`.
Source: SE-18′(b). Kind: D -/
def trPt (i : Fin 2) : TrPt := if i = 0 then .e else .f

/-- The world of the `d`-copy leaf on route `i` after act `x`. Source: SE-18′(b). Kind: D -/
def trWorld (i : Fin 2) (x : Act2) : TrW :=
  if i = 0 then (if x = .a then .la else .lb) else (if x = .a then .ra else .rb)

/-- The payoff of the `d`-copy leaf on route `i` after act `x`: left `a ↦ 10, b ↦ 0`; right
`a ↦ 0, b ↦ 30`. Source: SE-18′(b). Kind: D -/
def trPay (i : Fin 2) (x : Act2) : ℚ :=
  if i = 0 then (if x = .a then 10 else 0) else (if x = .a then 0 else 30)

/-- The off-`O_d` world of route `i`. Source: SE-18′(b). Kind: D -/
def trOff (i : Fin 2) : TrW := if i = 0 then .offL else .offR

/-- **The two-route tree** (SE-18′(b)): a fair coin; on route `i` the point `trPt i` (`e` or
`f`), whose first act (`u`/`w`) leads to a `d`-copy with payoffs `trPay i` and whose second
act (`v`/`z`) leads to an off-`O_d` leaf.
Source: `cf-workflow/phase2-notes/repair/seeds.md` line 81, SE-18′(b) ("the two-route `O_d`
tree"); dp-sl-2-012
Kind: D -/
def twoRoute : Tree TrW TrPt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i =>
    .decision (trPt i) fun
      | .a => .decision .d fun x => .leaf (trWorld i x) (trPay i x)
      | .b => .leaf (trOff i) 0

/-- Observations: `O_d = {route ∈ {L, R}}` (the `d`-copy worlds), `O_e = O_f = ⊤`.
Source: SE-18′(b). Kind: D -/
def trObs : TrPt → Finset TrW
  | .d => {.la, .lb, .ra, .rb}
  | _ => Finset.univ

/-- Action events by the world's act coordinate (for `e`, `f`: which subtree the world lies in).
Source: SE-18′(b). Kind: D -/
def trActEv : (p : TrPt) → Act2 → Finset TrW
  | .d, .a => {.la, .ra}
  | .d, .b => {.lb, .rb}
  | .e, .a => {.la, .lb}
  | .e, .b => {.offL}
  | .f, .a => {.ra, .rb}
  | .f, .b => {.offR}

/-- A sum over the leaves of the two-route tree. Source: none: infrastructure. Kind: L -/
theorem twoRoute_sum {M : Type} [AddCommMonoid M] (f : twoRoute.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ x : Act2, f ⟨i, .a, x, ()⟩) + f ⟨i, .b, ()⟩) := by
  unfold twoRoute at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision, Act2.sum_univ, sum_leaves_decision]
  simp only [Tree.sum_leaves_leaf]

/-- The procedure `C₀`: `e` and `f` play their second act with certainty (so `O_d` is
unrealized), `d` plays `(½, ½)`.
Source: SE-18′(b) ("`s = C(e)(u)`, `t = C(f)(w)`" both `0` at the limit)
Kind: D -/
def trC0 : Proc TrPt (fun _ => Act2) ℚ
  | .d => FinDistr.act2 (1 / 2) (by norm_num) (by norm_num)
  | .e => FinDistr.pure .b
  | .f => FinDistr.pure .b

/-- The `d`-act event `a` within `O_d`. Source: none: infrastructure. Kind: D -/
def trA : Finset TrW := trActEv .d .a ∩ trObs .d

/-- The `d`-act event `b` within `O_d`. Source: none: infrastructure. Kind: D -/
def trB : Finset TrW := trActEv .d .b ∩ trObs .d

/-- A ray on the two-route tree with weights `u` on `e`'s first act, `v` on `f`'s first act,
and `(½, ½)` at `d` — a `Ray` (sums to one at each point, positively trailing).
Source: SE-18′(b) ("along the ray `s = ε, t = ε²` … `s = ε², t = ε`")
Kind: D -/
noncomputable def trRay (u v : Polynomial ℚ) (hu : PosTrail u) (hu' : PosTrail (Polynomial.C 1 - u))
    (hv : PosTrail v) (hv' : PosTrail (Polynomial.C 1 - v)) : Ray TrPt (fun _ => Act2) ℚ where
  w := fun p x => match p, x with
    | .d, _ => Polynomial.C (1 / 2)
    | .e, .a => u
    | .e, .b => Polynomial.C 1 - u
    | .f, .a => v
    | .f, .b => Polynomial.C 1 - v
  sum_one p := by
    cases p
    · rw [Act2.sum_univ]; simp only; rw [← Polynomial.C_add]; norm_num
    · rw [Act2.sum_univ]; simp only; ring
    · rw [Act2.sum_univ]; simp only; ring
  posTrail p x := by
    cases p <;> cases x
    · exact PosTrail.C (by norm_num)
    · exact PosTrail.C (by norm_num)
    · exact hu
    · exact hu'
    · exact hv
    · exact hv'

/-- `C 1 − X^k` has positive constant term. Source: none: infrastructure. Kind: L -/
theorem posTrail_one_sub_X_pow (k : ℕ) (hk : 0 < k) :
    PosTrail (Polynomial.C 1 - Polynomial.X ^ k : Polynomial ℚ) := by
  apply posTrail_of_coeff_zero_pos
  simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, hk.ne]

/-- The ray `s = ε, t = ε²`. Source: SE-18′(b). Kind: D -/
noncomputable def trRayXX2 : Ray TrPt (fun _ => Act2) ℚ :=
  trRay Polynomial.X (Polynomial.X ^ 2) PosTrail.X
    (by simpa using posTrail_one_sub_X_pow 1 one_pos) (PosTrail.pow PosTrail.X 2)
    (posTrail_one_sub_X_pow 2 two_pos)

/-- The ray `s = ε², t = ε`. Source: SE-18′(b). Kind: D -/
noncomputable def trRayX2X : Ray TrPt (fun _ => Act2) ℚ :=
  trRay (Polynomial.X ^ 2) Polynomial.X (PosTrail.pow PosTrail.X 2)
    (posTrail_one_sub_X_pow 2 two_pos) PosTrail.X
    (by simpa using posTrail_one_sub_X_pow 1 one_pos)

/-- The ray `s = ε, t = ε²` starts at `C₀`. Source: SE-18′(b). Kind: L -/
theorem trRayXX2_isRayOf : IsRayOf trRayXX2 trC0 := by
  intro p x
  cases p <;> cases x <;> simp [trRayXX2, trRay, trC0, Polynomial.coeff_sub, Polynomial.coeff_C,
    Polynomial.coeff_X_pow, Polynomial.coeff_X] <;> norm_num

/-- The ray `s = ε², t = ε` starts at `C₀`. Source: SE-18′(b). Kind: L -/
theorem trRayX2X_isRayOf : IsRayOf trRayX2X trC0 := by
  intro p x
  cases p <;> cases x <;> simp [trRayX2X, trRay, trC0, Polynomial.coeff_sub, Polynomial.coeff_C,
    Polynomial.coeff_X_pow, Polynomial.coeff_X] <;> norm_num

/-- `O_d` is unrealized under `C₀` (both routes to `d` have weight `0`).
Source: SE-18′(b) ("`C`-unrealized observation"). Kind: L -/
theorem twoRoute_obs_null : nu trC0 twoRoute (trObs .d) = 0 := by
  rw [nu_eq_sum, twoRoute_sum]
  simp [twoRoute, leafLaw, trWorld, trPt, trOff, trC0, trObs, Fin.sum_univ_two, Act2.sum_univ]

section computations

/-- The simp set that evaluates a leaf sum of the two-route tree to a number. -/
local macro "tr_eval" : tactic =>
  `(tactic| (simp [twoRoute, leafLawPoly, leafLawPolyRay, trembleW, trWorld, trPt, trOff, trPay,
      trC0, trA, trB, trActEv, trObs, trRay, trRayXX2, trRayX2X, Fin.sum_univ_two, Act2.sum_univ,
      FinDistr.fair, FinDistr.coin, act2_card_rat]; try norm_num))

/-- Uniform ray, act `a`: `coeff 0 = 0`, `coeff 1 = ¼`, pay `coeff 1 = 5/4`. Kind: L. Source: SE-18′(b). -/
theorem twoRoute_uniform_a_coeffs :
    (nuPoly trC0 twoRoute trA).coeff 0 = 0 ∧ (nuPoly trC0 twoRoute trA).coeff 1 = 1 / 4 ∧
    (payPoly trC0 twoRoute trA).coeff 1 = 5 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPoly_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPoly_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, payPoly_eq_sum, twoRoute_sum]; tr_eval

/-- Uniform ray, act `b`. Kind: L. Source: SE-18′(b). -/
theorem twoRoute_uniform_b_coeffs :
    (nuPoly trC0 twoRoute trB).coeff 0 = 0 ∧ (nuPoly trC0 twoRoute trB).coeff 1 = 1 / 4 ∧
    (payPoly trC0 twoRoute trB).coeff 1 = 15 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPoly_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPoly_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, payPoly_eq_sum, twoRoute_sum]; tr_eval

/-- Ray `s = ε, t = ε²`, act `a`. Kind: L. Source: SE-18′(b). -/
theorem twoRoute_XX2_a_coeffs :
    (nuPolyRay trRayXX2 twoRoute trA).coeff 0 = 0 ∧ (nuPolyRay trRayXX2 twoRoute trA).coeff 1 = 1 / 4 ∧
    (payPolyRay trRayXX2 twoRoute trA).coeff 1 = 5 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPolyRay_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, payPolyRay_eq_sum, twoRoute_sum]; tr_eval

/-- Ray `s = ε, t = ε²`, act `b`. Kind: L. Source: SE-18′(b). -/
theorem twoRoute_XX2_b_coeffs :
    (nuPolyRay trRayXX2 twoRoute trB).coeff 0 = 0 ∧ (nuPolyRay trRayXX2 twoRoute trB).coeff 1 = 1 / 4 ∧
    (payPolyRay trRayXX2 twoRoute trB).coeff 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPolyRay_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, payPolyRay_eq_sum, twoRoute_sum]; tr_eval

/-- Ray `s = ε², t = ε`, act `a`. Kind: L. Source: SE-18′(b). -/
theorem twoRoute_X2X_a_coeffs :
    (nuPolyRay trRayX2X twoRoute trA).coeff 0 = 0 ∧ (nuPolyRay trRayX2X twoRoute trA).coeff 1 = 1 / 4 ∧
    (payPolyRay trRayX2X twoRoute trA).coeff 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPolyRay_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, payPolyRay_eq_sum, twoRoute_sum]; tr_eval

/-- Ray `s = ε², t = ε`, act `b`. Kind: L. Source: SE-18′(b). -/
theorem twoRoute_X2X_b_coeffs :
    (nuPolyRay trRayX2X twoRoute trB).coeff 0 = 0 ∧ (nuPolyRay trRayX2X twoRoute trB).coeff 1 = 1 / 4 ∧
    (payPolyRay trRayX2X twoRoute trB).coeff 1 = 15 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPolyRay_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, twoRoute_sum]; tr_eval
  · rw [coeff_one_eq_eval_zero_derivative, payPolyRay_eq_sum, twoRoute_sum]; tr_eval

end computations

/-- **Ray dependence at an unrealized observation** (SE-18′(b) made exact): under `C₀` the
limiting act values at `d` are `(5, 15)` along Definition 10's uniform ray, `(10, 0)` along
`s = ε, t = ε²`, and `(0, 30)` along `s = ε², t = ε`. The argmax at `d` reverses between rays;
by `limitValRay_eq_of_pos` this can only happen because `O_d` is `C₀`-null
(`twoRoute_obs_null`). Both custom rays start at `C₀` (`trRayXX2_isRayOf`, `trRayX2X_isRayOf`).
Source: SE-18′(b): "`V(a) = 10s/(s+t)`, `V(b) = 30t/(s+t)` … along Definition 10's ray
`s = t = ε/2` the values are `(5, 15)`, along `s = ε, t = ε²` `(10, 0)`, along `s = ε², t = ε`
`(0, 30)`"; P07 I2′; dp-sl-2-012
Kind: N+
Fidelity: exact
Hyps: none -/
theorem twoRoute_values :
    (limitVal trC0 twoRoute trA = 5 ∧ limitVal trC0 twoRoute trB = 15) ∧
    (limitValRay trRayXX2 twoRoute trA = 10 ∧ limitValRay trRayXX2 twoRoute trB = 0) ∧
    (limitValRay trRayX2X twoRoute trA = 0 ∧ limitValRay trRayX2X twoRoute trB = 30) := by
  obtain ⟨ua0, ua1, uap⟩ := twoRoute_uniform_a_coeffs
  obtain ⟨ub0, ub1, ubp⟩ := twoRoute_uniform_b_coeffs
  obtain ⟨xa0, xa1, xap⟩ := twoRoute_XX2_a_coeffs
  obtain ⟨xb0, xb1, xbp⟩ := twoRoute_XX2_b_coeffs
  obtain ⟨ya0, ya1, yap⟩ := twoRoute_X2X_a_coeffs
  obtain ⟨yb0, yb1, ybp⟩ := twoRoute_X2X_b_coeffs
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [limitVal_of_coeff_one _ _ _ ua0 (by rw [ua1]; norm_num), uap, ua1]; norm_num
  · rw [limitVal_of_coeff_one _ _ _ ub0 (by rw [ub1]; norm_num), ubp, ub1]; norm_num
  · rw [limitValRay_of_coeff_one _ _ _ xa0 (by rw [xa1]; norm_num), xap, xa1]; norm_num
  · rw [limitValRay_of_coeff_one _ _ _ xb0 (by rw [xb1]; norm_num), xbp, xb1]; norm_num
  · rw [limitValRay_of_coeff_one _ _ _ ya0 (by rw [ya1]; norm_num), yap, ya1]; norm_num
  · rw [limitValRay_of_coeff_one _ _ _ yb0 (by rw [yb1]; norm_num), ybp, yb1]; norm_num

/-! ## The single-point claim beyond two actions -/

/-- Three actions. Source: dp-sl-029 (the `|A_d| ≥ 3` test); mandate T2(d). Kind: D -/
inductive Act3 : Type
  | a
  | b
  | c
  deriving DecidableEq, Fintype

instance : Nonempty Act3 := ⟨.a⟩

/-- `univ = {a, b, c}`. Source: none: infrastructure. Kind: L -/
theorem Act3.univ_eq : (Finset.univ : Finset Act3) = {.a, .b, .c} := by
  ext x; cases x <;> simp

/-- Sums over `Act3`. Source: none: infrastructure. Kind: L -/
theorem Act3.sum_univ {M : Type} [AddCommMonoid M] (f : Act3 → M) :
    ∑ x, f x = f .a + f .b + f .c := by
  rw [Act3.univ_eq, Finset.sum_insert (by simp), Finset.sum_pair (by simp), ← add_assoc]

/-- **The one-node three-action tree**: a single `d`-node with acts `a, b, c`, each leading to
a leaf whose world records the act (payoffs `0`).
Source: mandate T2(d) ("three acts at a single point"); dp-sl-029
Kind: D -/
def threeAct : Tree Act3 Unit (fun _ => Act3) ℚ := .decision () fun x => .leaf x 0

/-- The observation `{b, c}`, unrealized under `δ_a`. Source: mandate T2(d). Kind: D -/
def threeObs : Finset Act3 := {.b, .c}

/-- The procedure `δ_a` on the three-action tree. Source: mandate T2(d). Kind: D -/
def procA3 : Proc Unit (fun _ => Act3) ℚ := fun _ => FinDistr.pure .a

/-- A sum over the leaves of the three-action tree. Source: none: infrastructure. Kind: L -/
theorem threeAct_sum {M : Type} [AddCommMonoid M] (f : threeAct.Leaves → M) :
    ∑ ℓ, f ℓ = f ⟨.a, ()⟩ + f ⟨.b, ()⟩ + f ⟨.c, ()⟩ := by
  unfold threeAct at f ⊢
  rw [sum_leaves_decision, Act3.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- A ray on the three-action tree: `w_b = p`, `w_c = q`, `w_a = 1 − p − q`.
Source: mandate T2(d) ("which a ray may set to `1` and `2`")
Kind: D -/
noncomputable def ray3 (p q : Polynomial ℚ) (hp : PosTrail p) (hq : PosTrail q)
    (h : PosTrail (Polynomial.C 1 - p - q)) : Ray Unit (fun _ => Act3) ℚ where
  w := fun _ x => match x with
    | .a => Polynomial.C 1 - p - q
    | .b => p
    | .c => q
  sum_one _ := by rw [Act3.sum_univ]; simp only; ring
  posTrail _ x := by
    cases x
    · exact h
    · exact hp
    · exact hq

/-- `C 1 − X − X²` has positive constant term. Source: none: infrastructure. Kind: L -/
theorem posTrail_one_sub_X_sub_X_sq :
    PosTrail (Polynomial.C 1 - Polynomial.X - Polynomial.X ^ 2 : Polynomial ℚ) := by
  apply posTrail_of_coeff_zero_pos
  simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow]

/-- `C 1 − X² − X` has positive constant term. Source: none: infrastructure. Kind: L -/
theorem posTrail_one_sub_X_sq_sub_X :
    PosTrail (Polynomial.C 1 - Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ) := by
  apply posTrail_of_coeff_zero_pos
  simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow]

/-- The ray `(w_b, w_c) = (ε, ε²)`. Source: mandate T2(d). Kind: D -/
noncomputable def ray3XX2 : Ray Unit (fun _ => Act3) ℚ :=
  ray3 Polynomial.X (Polynomial.X ^ 2) PosTrail.X (PosTrail.pow PosTrail.X 2)
    posTrail_one_sub_X_sub_X_sq

/-- The ray `(w_b, w_c) = (ε², ε)`. Source: mandate T2(d). Kind: D -/
noncomputable def ray3X2X : Ray Unit (fun _ => Act3) ℚ :=
  ray3 (Polynomial.X ^ 2) Polynomial.X (PosTrail.pow PosTrail.X 2) PosTrail.X
    posTrail_one_sub_X_sq_sub_X

section computations3

local macro "ta_eval" : tactic =>
  `(tactic| (simp [threeAct, leafLawPolyRay, threeObs, ray3, ray3XX2, ray3X2X, Act3.sum_univ]; try norm_num))

/-- Coefficients on the three-action tree along `(ε, ε²)`. Source: mandate T2(d). Kind: L -/
theorem threeAct_XX2_coeffs :
    (nuPolyRay ray3XX2 threeAct threeObs).coeff 0 = 0 ∧
    (nuPolyRay ray3XX2 threeAct threeObs).coeff 1 = 1 ∧
    (nuPolyRay ray3XX2 threeAct ({.b} ∩ threeObs)).coeff 1 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPolyRay_eq_sum, threeAct_sum]; ta_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, threeAct_sum]; ta_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, threeAct_sum]; ta_eval

/-- Coefficients on the three-action tree along `(ε², ε)`. Source: mandate T2(d). Kind: L -/
theorem threeAct_X2X_coeffs :
    (nuPolyRay ray3X2X threeAct threeObs).coeff 0 = 0 ∧
    (nuPolyRay ray3X2X threeAct threeObs).coeff 1 = 1 ∧
    (nuPolyRay ray3X2X threeAct ({.b} ∩ threeObs)).coeff 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero, nuPolyRay_eq_sum, threeAct_sum]; ta_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, threeAct_sum]; ta_eval
  · rw [coeff_one_eq_eval_zero_derivative, nuPolyRay_eq_sum, threeAct_sum]; ta_eval

end computations3

/-- **Ray dependence at a single point with three actions**: on the one-node tree with
`C = δ_a`, both rays start at `δ_a`, the observation `{b, c}` is `C`-null, and the limiting
conditional of `{b}` given `{b, c}` is `1` along `(w_b, w_c) = (ε, ε²)` and `0` along `(ε², ε)`.
What this refutes (repair round 1, fidelity N1 / adversarial B2): P07-1′ refinement (ii)'s
"the ray-dependence of SE-18′(b) … needs two *points* trembling at different rates" (P07.md
line 32) — per-act rates at one point suffice. What survives: (1) P07 I2′'s own sentence, "at a
single point with realized `O_d` there is nothing to choose", which is `limitCondRay_eq_of_pos`
(confirmed, not refuted); (2) the class-relative half of line 32 — P07's "#4 class" (every act
tremble-reachable, the observation a parent of the act) forbids act-decided observations, and
`{b, c}` is decided by the act, so within that class there is still no ray to choose; (3) the
two-action case (the off-support act's order is the only free choice and cancels — proved,
`twoAct_single_point_ray_independent` in `SinglePoint.lean`). The survey headline dp-sl-029 ("absent from single-point
classes") is the run's own compression, not a source sentence.
Source: P07-1′ refinement (ii) (`P07.md` line 32: "needs two points trembling at different
rates and an observation the untrembled procedure never realizes" — refuted as stated for
`|A_d| ≥ 3`, ATTRIBUTION-UNVETTED as to the reading); P07 I2′ (confirmed); survey dp-sl-029;
mandate T2(d)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem threeAct_ray_dependent :
    IsRayOf ray3XX2 procA3 ∧ IsRayOf ray3X2X procA3 ∧ nu procA3 threeAct threeObs = 0 ∧
    limitCondRay ray3XX2 threeAct {.b} threeObs = 1 ∧
    limitCondRay ray3X2X threeAct {.b} threeObs = 0 := by
  obtain ⟨x0, x1, xb⟩ := threeAct_XX2_coeffs
  obtain ⟨y0, y1, yb⟩ := threeAct_X2X_coeffs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ x
    cases x <;> simp [ray3XX2, ray3, procA3, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  · intro _ x
    cases x <;> simp [ray3X2X, ray3, procA3, Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  · rw [nu_eq_sum, threeAct_sum]
    simp [threeAct, leafLaw, threeObs, procA3]
  · rw [limitCondRay_of_coeff_one _ _ _ _ x0 (by rw [x1]; norm_num), xb, x1]; norm_num
  · rw [limitCondRay_of_coeff_one _ _ _ _ y0 (by rw [y1]; norm_num), yb, y1]; norm_num

end Cleanroom.Decision.DpCalibLimits
