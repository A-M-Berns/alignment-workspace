import Cleanroom.Uea.UeaSelfGame.Defs

/-!
# The general `T3(n, θ, g)` family: the supremum `δ/(1−δ)` on `δ ≤ 1/2`, and the gap `1` above `1/2`

Repair round 2 of the `uea-self-game` package (faf-cleanroom run, 2026-10-01), continuation. The mandate's
target 6 `stretch` (M) asks for the round-2 script's `T3(n, θ, g)` family as a parametric theorem and for
its limit; the round-2 adversarial audit (B1) showed the limit sentence needs `δ ≤ 1/2` and that above
`1/2` the maximal gap `1` is attained (hand-checked for `δ ∈ (1/2, 2/3)`, proved on `Fin 3` for
`δ ≥ 2/3` in `Regimes.GapOne`). This module proves all of it at symbolic parameters.

**The family** (`T3Family`). Situations `Fin (n + 2)` (the mandate's `n` is the number of situations,
`n + 2` here, so its `n − 1` deviations are `n + 1` and its `(n − 2) w` is `n · w`), actions `Fin 2`
(`0 = a`, `1 = b`). The own policy is `aPol = aⁿ⁺²`; the deviations `ρ_j` (`j ≠ 0`) play `b` at `j`
only; the polluter is `bPol = bⁿ⁺²`. Utilities `U(aPol) = 1 − g`, `U(ρ_j) = 1`, everything else `0`;
`π* = ρ_1`; `Po = w ∑_{j ≠ 0} δ_{ρ_j} + θ δ_{bPol}` with `w = (1 − θ)/(n + 1)`.

* `condDen_diracComb`, `condNum_diracComb`: the conditional's numerator and denominator of a finite
  combination of point masses, as sums over the support (the only sum-over-policies infrastructure the
  family needs; no enumeration of `Fin (n+2) → Fin 2`).
* The eight conditionals of `μ_{aPol}` in closed form (`cond_00`, …, `cond_succ_one`), every action
  available.
* `isPureFP_iff`: `aPol` is a pure fixed point iff `w/(w+θ) ≤ ((1−δ)(1−g) + δ n w)/((1−δ) + δ n w)` — the
  mandate's fixed-point condition at a deviation situation (automatic at `s₀`).
* `TB_zero_iff`: the trust bound at `s₀` iff `g ≤ δ + δ²(1−θ)/(1−δ)` (the mandate's cap, exact).
* `TB_succ_iff`: the trust bound at a deviation situation iff `g ≤ δ + δ² n w/(1−δ)` **or**
  `(1−δ)(w+θ) ≤ w` — the second disjunct (the deviation's own conditional `w/(w+θ)` clears the
  threshold) is one the mandate's cap sentence omits; under the fixed-point condition it is subsumed
  (`TB_succ_of_cap`), which is the case the mandate had in mind.
* `family`: the parametric theorem — under the three conditions, `aPol` is a pure fixed point with the
  trust bound at every situation and gap exactly `g`.
* **`sup_limit`**: for every `δ ∈ (0, 1/2]` and `ε > 0` an instance with gap `≥ δ/(1−δ) − ε`
  (`θ = 1/(N+1)`, `g` at the deviation cap, `N` large). This is the statement that was
  `sup_limit_open` (retired); with `Attainment.theoremC_strict` (`gap < δ/(1−δ)` at every pure fixed
  point with the trust bound somewhere, `δ > 0`) it makes `δ/(1−δ)` the exact, unattained supremum of
  the gap on `δ ≤ 1/2`.
* **`gap_one_attained_above_half`**: for every `δ ∈ (1/2, 1)` an instance with a pure fixed point, the
  trust bound everywhere and gap `1` (`g = 1`, `θ = (1−δ)/(δN)`, `N ≥ (1−δ)/(2δ−1)`); extends
  `Regimes.GapOne.gap_one_attained` from `[2/3, 1)` to all of `(1/2, 1)`.

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30; repair round 2, 2026-10-01).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

/-! ### Finite combinations of point masses and their conditionals -/

section Dirac

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
variable {J : Type*} [Fintype J]

/-- `∑_j c_j δ_{p_j}` as a function on policies: the belief with mass `c_j` on the policy `p_j`.
Source: none: infrastructure (the `T3` family's `Po` is one of these)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def diracComb (c : J → ℝ) (p : J → S → A) : (S → A) → ℝ :=
  fun π' => ∑ j, c j * (if π' = p j then 1 else 0)

omit [DecidableEq S] [Fintype A] in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem diracComb_nonneg {c : J → ℝ} (hc : ∀ j, 0 ≤ c j) (p : J → S → A) (π' : S → A) :
    0 ≤ diracComb c p π' :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (by split_ifs <;> norm_num)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_diracComb (c : J → ℝ) (p : J → S → A) : ∑ π', diracComb c p π' = ∑ j, c j := by
  simp only [diracComb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ (p j), if_pos (Finset.mem_univ _), mul_one]

/-- The denominator of the conditional of a point-mass combination is the sum, over the support, of the
masses of the policies that play `a` at `s`.
Source: none: infrastructure ([[updateless-self-game]] §1's `conditionals`, evaluated on a finite support)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_diracComb (c : J → ℝ) (p : J → S → A) (s : S) (a : A) :
    condDen (diracComb c p) s a = ∑ j, c j * (if p j s = a then 1 else 0) := by
  simp only [condDen, diracComb]
  have key : ∀ π' : S → A, (if π' s = a then ∑ j, c j * (if π' = p j then 1 else 0) else 0) =
      ∑ j, (if π' = p j then c j * (if p j s = a then 1 else 0) else 0) := by
    intro π'
    by_cases h : π' s = a
    · rw [if_pos h]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : π' = p j
      · subst hj; simp [h]
      · simp [hj]
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : π' = p j
      · subst hj; simp [h]
      · simp [hj]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (p j), if_pos (Finset.mem_univ _)]

/-- The numerator of the conditional of a point-mass combination: the same sum weighted by `U`.
Source: none: infrastructure ([[updateless-self-game]] §1's `conditionals`, evaluated on a finite support)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_diracComb (G : Game S A) (c : J → ℝ) (p : J → S → A) (s : S) (a : A) :
    G.condNum (diracComb c p) s a = ∑ j, c j * (if p j s = a then 1 else 0) * G.U (p j) := by
  simp only [Game.condNum, diracComb]
  have key : ∀ π' : S → A,
      (if π' s = a then (∑ j, c j * (if π' = p j then 1 else 0)) * G.U π' else 0) =
      ∑ j, (if π' = p j then c j * (if p j s = a then 1 else 0) * G.U (p j) else 0) := by
    intro π'
    by_cases h : π' s = a
    · rw [if_pos h, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : π' = p j
      · subst hj; simp [h]
      · simp [hj]
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : π' = p j
      · subst hj; simp [h]
      · simp [hj]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (p j), if_pos (Finset.mem_univ _)]

end Dirac

namespace T3Family

/-- The family's parameters: `n` (situations `Fin (n + 2)`, deviations `n + 1`), the polluter's weight
`θ ∈ (0,1)`, the prior `δ ∈ (0,1)`, the own policy's loss `g ∈ [0,1]`.
Source: [[uea-self-game-mandate]] target 6 (`T3(n, θ, g)`: "`S = Fin n`, `π = aⁿ`, `U π = 1−g`, … `Po ρ_i = (1−θ)/(n−1)`; polluter `bⁿ`, `Po = θ`")
Kind: D
Fidelity: exact (the mandate's `n` situations are `n + 2` here)
Hyps: n/a -/
structure Params where
  /-- situations are `Fin (n + 2)` -/
  n : ℕ
  /-- the polluter's weight -/
  θ : ℝ
  /-- the prior on "other" -/
  δ : ℝ
  /-- the own policy's loss -/
  g : ℝ
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  δ_pos : 0 < δ
  δ_lt_one : δ < 1
  g_nonneg : 0 ≤ g
  g_le_one : g ≤ 1

variable (P : Params)

/-- Each deviation's weight `w = (1 − θ)/(n + 1)`.
Source: [[uea-self-game-mandate]] target 6 (`w := (1−θ)/(n−1)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def w : ℝ := (1 - P.θ) / (P.n + 1)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem w_pos : 0 < w P := div_pos (by linarith [P.θ_lt_one]) (by positivity)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem w_mul : (P.n + 1 : ℝ) * w P = 1 - P.θ := by
  unfold w
  field_simp

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem n_mul_w_le : (P.n : ℝ) * w P ≤ 1 - P.θ := by
  have h := w_mul P
  have := w_pos P
  nlinarith

/-- The own policy `aⁿ⁺²`.
Source: [[uea-self-game-mandate]] target 6 (`π = aⁿ`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def aPol : Fin (P.n + 2) → Fin 2 := fun _ => 0

/-- The polluter `bⁿ⁺²`.
Source: [[uea-self-game-mandate]] target 6 ("polluter `bⁿ`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def bPol : Fin (P.n + 2) → Fin 2 := fun _ => 1

/-- The deviation `ρ_j`: `b` at `j`, `a` elsewhere.
Source: [[uea-self-game-mandate]] target 6 (`ρ_i := π` with `b` at `s_i`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def rho (j : Fin (P.n + 2)) : Fin (P.n + 2) → Fin 2 := fun s => if s = j then 1 else 0

/-- The support of `Po`, indexed by `Fin (n + 2)`: index `0` is the polluter, index `j ≠ 0` is `ρ_j`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def supp (j : Fin (P.n + 2)) : Fin (P.n + 2) → Fin 2 := if j = 0 then bPol P else rho P j

/-- The weights of `Po` on the support: `θ` on the polluter, `w` on each deviation.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def wt (j : Fin (P.n + 2)) : ℝ := if j = 0 then P.θ else w P

/-- `Po = w ∑_{j ≠ 0} δ_{ρ_j} + θ δ_{bPol}`.
Source: [[uea-self-game-mandate]] target 6
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Po : (Fin (P.n + 2) → Fin 2) → ℝ := diracComb (wt P) (supp P)

/-- The utility: `1 − g` on `aPol`, `1` on each deviation `ρ_j` (`j ≠ 0`), `0` elsewhere.
Source: [[uea-self-game-mandate]] target 6 (`U π = 1−g`, `U ρ_i = 1`, "all other `U = 0`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def U (π' : Fin (P.n + 2) → Fin 2) : ℝ :=
  if π' = aPol P then 1 - P.g else if ∃ j, j ≠ 0 ∧ π' = rho P j then 1 else 0

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem rho_ne_aPol (j : Fin (P.n + 2)) : rho P j ≠ aPol P := by
  intro h
  have := congrFun h j
  simp [rho, aPol] at this

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bPol_ne_aPol : bPol P ≠ aPol P := by
  intro h
  have := congrFun h 0
  simp [bPol, aPol] at this

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem bPol_ne_rho (j : Fin (P.n + 2)) (hj : j ≠ 0) : bPol P ≠ rho P j := by
  intro h
  have := congrFun h 0
  simp [bPol, rho, hj.symm] at this

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_aPol : U P (aPol P) = 1 - P.g := by
  simp [U]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_rho (j : Fin (P.n + 2)) (hj : j ≠ 0) : U P (rho P j) = 1 := by
  unfold U
  rw [if_neg (rho_ne_aPol P j), if_pos ⟨j, hj, rfl⟩]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_bPol : U P (bPol P) = 0 := by
  unfold U
  rw [if_neg (bPol_ne_aPol P), if_neg]
  rintro ⟨j, hj, h⟩
  exact bPol_ne_rho P j hj h

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_supp (j : Fin (P.n + 2)) : U P (supp P j) = if j = 0 then 0 else 1 := by
  unfold supp
  by_cases h : j = 0
  · rw [if_pos h, if_pos h, U_bPol]
  · rw [if_neg h, if_neg h, U_rho P j h]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_nonneg (π' : Fin (P.n + 2) → Fin 2) : 0 ≤ U P π' := by
  unfold U
  have := P.g_le_one
  split_ifs <;> linarith

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_le_one (π' : Fin (P.n + 2) → Fin 2) : U P π' ≤ 1 := by
  unfold U
  have := P.g_nonneg
  split_ifs <;> linarith

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wt_nonneg (j : Fin (P.n + 2)) : 0 ≤ wt P j := by
  unfold wt
  have := P.θ_pos
  have := w_pos P
  split_ifs <;> linarith

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_wt : ∑ j, wt P j = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [wt, if_true, Fin.succ_ne_zero, if_false, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  linarith [w_mul P]

/-- The instance `T3(n, θ, g)` as a `Game`: `U` above, `π* = ρ_1`, `Po` above, prior `δ`.
Source: [[uea-self-game-mandate]] target 6 (`T3(n, θ, g)`); [[uea-2-inventory]] 2-013
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def game : Game (Fin (P.n + 2)) (Fin 2) where
  U := U P
  U_nonneg := U_nonneg P
  U_le_one := U_le_one P
  piStar := rho P (Fin.succ 0)
  piStar_max := fun π => by rw [U_rho P _ (Fin.succ_ne_zero 0)]; exact U_le_one P π
  Po := Po P
  Po_mem := ⟨fun π' => diracComb_nonneg (wt_nonneg P) _ π', by
    unfold Po; rw [sum_diracComb]; exact sum_wt P⟩
  δ := P.δ
  δ_nonneg := P.δ_pos.le
  δ_lt_one := P.δ_lt_one

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem U_apply (π' : Fin (P.n + 2) → Fin 2) : (game P).U π' = U P π' := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem δ_eq : (game P).δ = P.δ := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Po_eq : (game P).Po = Po P := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ustar_eq : (game P).Ustar = 1 := by
  show U P (rho P (Fin.succ 0)) = 1
  exact U_rho P _ (Fin.succ_ne_zero 0)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem thr_eq : (game P).thr = 1 - P.δ := by
  simp [Game.thr, Ustar_eq, δ_eq]

/-- The gap of the own policy is exactly `g`.
Source: [[uea-self-game-mandate]] target 6 (`U π = 1−g`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem gap : (game P).Ustar - (game P).U (aPol P) = P.g := by
  rw [Ustar_eq, U_apply, U_aPol]; ring

/-! ### The conditionals of `μ_{aPol}` in closed form -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem rho_succ_zero (i : Fin (P.n + 1)) : rho P i.succ 0 = 0 := by
  simp [rho, (Fin.succ_ne_zero i).symm]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem rho_succ_succ (i t : Fin (P.n + 1)) : rho P i.succ t.succ = if t = i then 1 else 0 := by
  simp [rho]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_ind_zero_zero :
    ∑ i : Fin (P.n + 1), (if rho P i.succ 0 = 0 then (1 : ℝ) else 0) = P.n + 1 := by
  simp [rho_succ_zero]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_ind_zero_one :
    ∑ i : Fin (P.n + 1), (if rho P i.succ 0 = 1 then (1 : ℝ) else 0) = 0 := by
  simp [rho_succ_zero]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_ind_succ_one (t : Fin (P.n + 1)) :
    ∑ i : Fin (P.n + 1), (if rho P i.succ t.succ = 1 then (1 : ℝ) else 0) = 1 := by
  have key : ∀ i : Fin (P.n + 1),
      (if rho P i.succ t.succ = 1 then (1 : ℝ) else 0) = if t = i then 1 else 0 := by
    intro i
    rw [rho_succ_succ]
    by_cases h : t = i <;> simp [h]
  simp_rw [key]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_ind_succ_zero (t : Fin (P.n + 1)) :
    ∑ i : Fin (P.n + 1), (if rho P i.succ t.succ = 0 then (1 : ℝ) else 0) = P.n := by
  have key : ∀ i : Fin (P.n + 1),
      (if rho P i.succ t.succ = 0 then (1 : ℝ) else 0) = 1 - if t = i then 1 else 0 := by
    intro i
    rw [rho_succ_succ]
    by_cases h : t = i <;> simp [h]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  simp

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_Po (s : Fin (P.n + 2)) (a : Fin 2) :
    condDen (Po P) s a = P.θ * (if bPol P s = a then 1 else 0) +
      w P * ∑ i : Fin (P.n + 1), (if rho P i.succ s = a then 1 else 0) := by
  unfold Po
  rw [condDen_diracComb, Fin.sum_univ_succ, Finset.mul_sum]
  simp only [wt, supp, if_true, Fin.succ_ne_zero, if_false]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_Po (s : Fin (P.n + 2)) (a : Fin 2) :
    (game P).condNum (Po P) s a =
      w P * ∑ i : Fin (P.n + 1), (if rho P i.succ s = a then 1 else 0) := by
  unfold Po
  rw [condNum_diracComb, Fin.sum_univ_succ, Finset.mul_sum]
  simp only [U_apply, U_supp]
  simp only [wt, supp, if_true, Fin.succ_ne_zero, if_false, mul_zero, mul_one, zero_add]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_eq (s : Fin (P.n + 2)) (a : Fin 2) : (game P).pa s a = condDen (Po P) s a := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_eq (s : Fin (P.n + 2)) (a : Fin 2) :
    (game P).pva s a = (game P).condNum (Po P) s a := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_00 : (game P).pa 0 0 = 1 - P.θ := by
  rw [pa_eq, condDen_Po, sum_ind_zero_zero]
  simp [bPol]
  linarith [w_mul P]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_01 : (game P).pa 0 1 = P.θ := by
  rw [pa_eq, condDen_Po, sum_ind_zero_one]
  simp [bPol]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_succ_zero (t : Fin (P.n + 1)) : (game P).pa t.succ 0 = P.n * w P := by
  rw [pa_eq, condDen_Po, sum_ind_succ_zero]
  simp [bPol, mul_comm]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_succ_one (t : Fin (P.n + 1)) : (game P).pa t.succ 1 = P.θ + w P := by
  rw [pa_eq, condDen_Po, sum_ind_succ_one]
  simp [bPol]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_00 : (game P).pva 0 0 = 1 - P.θ := by
  rw [pva_eq, condNum_Po, sum_ind_zero_zero]
  linarith [w_mul P]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_01 : (game P).pva 0 1 = 0 := by
  rw [pva_eq, condNum_Po, sum_ind_zero_one, mul_zero]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_succ_zero (t : Fin (P.n + 1)) : (game P).pva t.succ 0 = P.n * w P := by
  rw [pva_eq, condNum_Po, sum_ind_succ_zero, mul_comm]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pva_succ_one (t : Fin (P.n + 1)) : (game P).pva t.succ 1 = w P := by
  rw [pva_eq, condNum_Po, sum_ind_succ_one, mul_one]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_mu_00 :
    condDen ((game P).muSelf (aPol P)) 0 0 = (1 - P.δ) + P.δ * (1 - P.θ) := by
  rw [Game.condDen_muSelf, pa_00, δ_eq]; simp [aPol]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_mu_01 : condDen ((game P).muSelf (aPol P)) 0 1 = P.δ * P.θ := by
  rw [Game.condDen_muSelf, pa_01, δ_eq]; simp [aPol]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_mu_succ_zero (t : Fin (P.n + 1)) :
    condDen ((game P).muSelf (aPol P)) t.succ 0 = (1 - P.δ) + P.δ * (P.n * w P) := by
  rw [Game.condDen_muSelf, pa_succ_zero, δ_eq]; simp [aPol]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_mu_succ_one (t : Fin (P.n + 1)) :
    condDen ((game P).muSelf (aPol P)) t.succ 1 = P.δ * (P.θ + w P) := by
  rw [Game.condDen_muSelf, pa_succ_one, δ_eq]; simp [aPol]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_mu_00 : (game P).condNum ((game P).muSelf (aPol P)) 0 0 =
    (1 - P.δ) * (1 - P.g) + P.δ * (1 - P.θ) := by
  rw [Game.condNum_muSelf, pva_00, δ_eq, U_apply, U_aPol]; simp [aPol]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_mu_01 : (game P).condNum ((game P).muSelf (aPol P)) 0 1 = 0 := by
  rw [Game.condNum_muSelf, pva_01, δ_eq, U_apply, U_aPol]; simp [aPol]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_mu_succ_zero (t : Fin (P.n + 1)) :
    (game P).condNum ((game P).muSelf (aPol P)) t.succ 0 =
      (1 - P.δ) * (1 - P.g) + P.δ * (P.n * w P) := by
  rw [Game.condNum_muSelf, pva_succ_zero, δ_eq, U_apply, U_aPol]; simp [aPol]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_mu_succ_one (t : Fin (P.n + 1)) :
    (game P).condNum ((game P).muSelf (aPol P)) t.succ 1 = P.δ * w P := by
  rw [Game.condNum_muSelf, pva_succ_one, δ_eq, U_apply, U_aPol]; simp [aPol]

/-- The own conditional at `s₀`: `((1−δ)(1−g) + δ(1−θ))/((1−δ) + δ(1−θ))`.
Source: [[uea-self-game-mandate]] target 6 (`T3`; the `s₀` conditional)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_00 : (game P).cond ((game P).muSelf (aPol P)) 0 0 =
    ((1 - P.δ) * (1 - P.g) + P.δ * (1 - P.θ)) / ((1 - P.δ) + P.δ * (1 - P.θ)) := by
  unfold Game.cond; rw [condNum_mu_00, condDen_mu_00]

/-- The deviation's conditional at `s₀` is `0` (only the polluter plays `b` there).
Source: [[uea-self-game-mandate]] target 6 ("at `s₀` automatic (`cond b = 0`)")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_01 : (game P).cond ((game P).muSelf (aPol P)) 0 1 = 0 := by
  unfold Game.cond; rw [condNum_mu_01, zero_div]

/-- The own conditional at a deviation situation: `((1−δ)(1−g) + δ n w)/((1−δ) + δ n w)`.
Source: [[uea-self-game-mandate]] target 6 (`T3`; the `s_i` conditional)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_succ_zero (t : Fin (P.n + 1)) : (game P).cond ((game P).muSelf (aPol P)) t.succ 0 =
    ((1 - P.δ) * (1 - P.g) + P.δ * (P.n * w P)) / ((1 - P.δ) + P.δ * (P.n * w P)) := by
  unfold Game.cond; rw [condNum_mu_succ_zero, condDen_mu_succ_zero]

/-- The deviation's conditional at its own situation: `w/(w+θ)` (pollution by `bⁿ⁺²`).
Source: [[uea-self-game-mandate]] target 6 (`T3`; "`w/(w+θ)`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_succ_one (t : Fin (P.n + 1)) :
    (game P).cond ((game P).muSelf (aPol P)) t.succ 1 = w P / (w P + P.θ) := by
  unfold Game.cond
  rw [condNum_mu_succ_one, condDen_mu_succ_one,
    div_eq_div_iff (mul_pos P.δ_pos (add_pos P.θ_pos (w_pos P))).ne' (add_pos (w_pos P) P.θ_pos).ne']
  ring

/-- Every action is available at every situation (the instance is convention-free).
Source: [[uea-self-game-mandate]] target 6
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_all (s : Fin (P.n + 2)) (a : Fin 2) : avail ((game P).muSelf (aPol P)) s a := by
  unfold avail
  have hδ := P.δ_pos
  have hθ := P.θ_pos
  have hw := w_pos P
  have h1 : 0 < 1 - P.δ := by linarith [P.δ_lt_one]
  have hθ1 : 0 < 1 - P.θ := by linarith [P.θ_lt_one]
  have hn : (0 : ℝ) ≤ P.n := Nat.cast_nonneg _
  induction s using Fin.cases with
  | zero =>
    match a with
    | 0 => rw [condDen_mu_00]; positivity
    | 1 => rw [condDen_mu_01]; positivity
  | succ t =>
    match a with
    | 0 => rw [condDen_mu_succ_zero]; positivity
    | 1 => rw [condDen_mu_succ_one]; positivity

/-! ### The exact conditions: fixed point, trust bound at `s₀`, trust bound at a deviation situation -/

/-- **`aPol` is a pure fixed point iff the mandate's fixed-point condition holds** at a deviation
situation: `w/(w+θ) ≤ ((1−δ)(1−g) + δ n w)/((1−δ) + δ n w)`. At `s₀` the fixed point is automatic
(`cond b = 0`); the condition is the same at every deviation situation.
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 6 ("fixed point at `s_i ⟺ w/(w+θ) ≤ ((1−δ)(1−g) + δ(n−2)w)/((1−δ) + δ(n−2)w)`; at `s₀` automatic")
Kind: P
Fidelity: exact (the mandate's `(n−2) w` is `n · w` in this module's indexing)
Hyps: (a) -/
theorem isPureFP_iff : (game P).IsPureFP (aPol P) ↔
    w P / (w P + P.θ) ≤
      ((1 - P.δ) * (1 - P.g) + P.δ * (P.n * w P)) / ((1 - P.δ) + P.δ * (P.n * w P)) := by
  have hδ := P.δ_pos
  have hθ := P.θ_pos
  have h1 : 0 < 1 - P.δ := by linarith [P.δ_lt_one]
  have hθ1 : 0 < 1 - P.θ := by linarith [P.θ_lt_one]
  have hg1 : 0 ≤ 1 - P.g := by linarith [P.g_le_one]
  constructor
  · intro h
    have h1 := (h (Fin.succ 0)).2 1 (avail_all P _ 1)
    change (game P).cond _ (Fin.succ 0) 1 ≤ (game P).cond _ (Fin.succ 0) 0 at h1
    rwa [cond_succ_one, cond_succ_zero] at h1
  · intro h s
    induction s using Fin.cases with
    | zero =>
      refine ⟨avail_all P 0 0, fun b _ => ?_⟩
      match b with
      | 0 => exact le_rfl
      | 1 =>
        change (game P).cond _ 0 1 ≤ (game P).cond _ 0 0
        rw [cond_01, cond_00]
        exact div_nonneg (by positivity) (by positivity)
    | succ t =>
      refine ⟨avail_all P _ 0, fun b _ => ?_⟩
      match b with
      | 0 => exact le_rfl
      | 1 =>
        change (game P).cond _ t.succ 1 ≤ (game P).cond _ t.succ 0
        rw [cond_succ_one, cond_succ_zero]
        exact h

/-- Supporting lemma (no headline claim; see the headline it serves): `a ≤ b + x/c ↔ (a − b) c ≤ x`
for `c > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem le_add_div_iff {a b x c : ℝ} (hc : 0 < c) : a ≤ b + x / c ↔ (a - b) * c ≤ x := by
  constructor
  · intro h
    have := (le_div_iff₀ hc).1 (show a - b ≤ x / c by linarith)
    exact this
  · intro h
    have := (le_div_iff₀ hc).2 h
    linarith

/-- **The trust bound at `s₀` iff `g ≤ δ + δ²(1−θ)/(1−δ)`** — the mandate's cap, exact (the deviation's
conditional at `s₀` is `0 < (1−δ) U*`, so only the own action can clear the threshold).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 6 ("`TB_{s₀} ⟺ g ≤ δ + δ²(1−θ)/(1−δ)`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem TB_zero_iff : (game P).TB ((game P).muSelf (aPol P)) 0 ↔
    P.g ≤ P.δ + P.δ ^ 2 * (1 - P.θ) / (1 - P.δ) := by
  have hδ := P.δ_pos
  have hθ := P.θ_pos
  have h1 : 0 < 1 - P.δ := by linarith [P.δ_lt_one]
  have hθ1 : 0 < 1 - P.θ := by linarith [P.θ_lt_one]
  have hden : 0 < (1 - P.δ) + P.δ * (1 - P.θ) := by positivity
  unfold Game.TB
  rw [thr_eq, le_add_div_iff h1]
  constructor
  · rintro ⟨a, -, ha⟩
    match a with
    | 0 =>
      rw [cond_00, le_div_iff₀ hden] at ha
      nlinarith [ha]
    | 1 =>
      rw [cond_01] at ha
      linarith
  · intro h
    refine ⟨0, avail_all P 0 0, ?_⟩
    rw [cond_00, le_div_iff₀ hden]
    nlinarith [h]

/-- **The trust bound at a deviation situation iff `g ≤ δ + δ² n w/(1−δ)` or `(1−δ)(w+θ) ≤ w`.** The
first disjunct is the mandate's cap (the own action clears the threshold); the second — the deviation's
own conditional `w/(w+θ)` clears it — is one the mandate's "`TB_{s_i} ⟺ g ≤ …`" omits. Under the
fixed-point condition the second is subsumed (`TB_succ_of_cap` is the direction the family uses).
Scope: finite updateless self-game; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 6 ("`TB_{s_i} ⟺ g ≤ δ + δ²(n−2)w/(1−δ)`")
Kind: P
Fidelity: stronger: the exact two-way condition; the mandate's iff holds only when `w/(w+θ) < 1 − δ`
Hyps: (a) -/
theorem TB_succ_iff (t : Fin (P.n + 1)) : (game P).TB ((game P).muSelf (aPol P)) t.succ ↔
    (P.g ≤ P.δ + P.δ ^ 2 * (P.n * w P) / (1 - P.δ) ∨ (1 - P.δ) * (w P + P.θ) ≤ w P) := by
  have hδ := P.δ_pos
  have hθ := P.θ_pos
  have hw := w_pos P
  have h1 : 0 < 1 - P.δ := by linarith [P.δ_lt_one]
  have hn : (0 : ℝ) ≤ P.n := Nat.cast_nonneg _
  have hden : 0 < (1 - P.δ) + P.δ * (P.n * w P) := by positivity
  have hwθ : 0 < w P + P.θ := by positivity
  unfold Game.TB
  rw [thr_eq, le_add_div_iff h1]
  constructor
  · rintro ⟨a, -, ha⟩
    match a with
    | 0 =>
      left
      rw [cond_succ_zero, le_div_iff₀ hden] at ha
      nlinarith [ha]
    | 1 =>
      right
      rw [cond_succ_one, le_div_iff₀ hwθ] at ha
      exact ha
  · rintro (h | h)
    · refine ⟨0, avail_all P _ 0, ?_⟩
      rw [cond_succ_zero, le_div_iff₀ hden]
      nlinarith [h]
    · refine ⟨1, avail_all P _ 1, ?_⟩
      rw [cond_succ_one, le_div_iff₀ hwθ]
      exact h

/-- The trust bound at a deviation situation from the mandate's cap `g ≤ δ + δ² n w/(1−δ)`.
Source: [[uea-self-game-mandate]] target 6
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem TB_succ_of_cap (t : Fin (P.n + 1)) (h : P.g ≤ P.δ + P.δ ^ 2 * (P.n * w P) / (1 - P.δ)) :
    (game P).TB ((game P).muSelf (aPol P)) t.succ :=
  (TB_succ_iff P t).2 (Or.inl h)

/-- **The `T3(n, θ, g)` family as a parametric theorem**: under the mandate's three conditions — the
fixed-point condition at a deviation situation, the cap at `s₀`, the cap at a deviation situation —
`aⁿ⁺²` is a pure fixed point of `game P` with the trust bound at every situation and gap exactly `g`.
Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 6 (`stretch` (M): "the general `T3(n, θ, g)` as a parametric family (`P`: for all `n ≥ 3`, `θ ∈ (0,1)`, `g` satisfying the three conditions, it is a pure fixed point with the stated `TB`s and gap `g`)"); [[uea-2-inventory]] 2-013
Kind: P
Fidelity: exact (every `n ≥ 2` situations; the mandate's `n ≥ 3` is `P.n ≥ 1`)
Hyps: (a) -/
theorem family
    (hFP : w P / (w P + P.θ) ≤
      ((1 - P.δ) * (1 - P.g) + P.δ * (P.n * w P)) / ((1 - P.δ) + P.δ * (P.n * w P)))
    (hTB0 : P.g ≤ P.δ + P.δ ^ 2 * (1 - P.θ) / (1 - P.δ))
    (hTBi : P.g ≤ P.δ + P.δ ^ 2 * (P.n * w P) / (1 - P.δ)) :
    (game P).IsPureFP (aPol P) ∧ (∀ s, (game P).TB ((game P).muSelf (aPol P)) s) ∧
      (game P).Ustar - (game P).U (aPol P) = P.g := by
  refine ⟨(isPureFP_iff P).2 hFP, fun s => ?_, gap P⟩
  induction s using Fin.cases with
  | zero => exact (TB_zero_iff P).2 hTB0
  | succ t => exact TB_succ_of_cap P t hTBi

/-! ### The limit on `δ ≤ 1/2`: the supremum of the gap is `δ/(1−δ)` -/

/-- The limit instance's polluter weight `θ_N = 1/(N+1)` (so `θ → 0` as `N → ∞`).
Source: [[uea-self-game-mandate]] target 6 (the limit: "take `θ → 0`, then `n → ∞`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def limθ (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

/-- The limit instance's deviation weight `w_N = (1 − θ_N)/(N+1) = N/(N+1)²`.
Source: [[uea-self-game-mandate]] target 6
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def limw (N : ℕ) : ℝ := (1 - limθ N) / ((N : ℝ) + 1)

/-- The limit instance's own loss `g_N = δ + δ² N w_N/(1−δ)`: the deviation-situation cap, met with
equality.
Source: [[uea-self-game-mandate]] target 6 ("the `TB_{s_i}` cap `→ δ + δ²(1−θ)/(1−δ) → δ/(1−δ)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def limg (δ : ℝ) (N : ℕ) : ℝ := δ + δ ^ 2 * ((N : ℝ) * limw N) / (1 - δ)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem limθ_pos (N : ℕ) : 0 < limθ N := by
  unfold limθ; positivity

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem limθ_le_one (N : ℕ) : limθ N ≤ 1 := by
  unfold limθ
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) N]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem limθ_lt_one (N : ℕ) (hN : 1 ≤ N) : limθ N < 1 := by
  unfold limθ
  rw [div_lt_one (by positivity)]
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem limw_eq (N : ℕ) : limw N = (N : ℝ) / ((N : ℝ) + 1) ^ 2 := by
  unfold limw limθ
  have h : ((N : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem limw_nonneg (N : ℕ) : 0 ≤ limw N := by
  rw [limw_eq]; positivity

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem limw_le_limθ (N : ℕ) : limw N ≤ limθ N := by
  unfold limw
  calc (1 - limθ N) / ((N : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_right (by linarith [limθ_pos N]) (by positivity)
    _ = limθ N := rfl

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem N_mul_limw_le (N : ℕ) : (N : ℝ) * limw N ≤ 1 - limθ N := by
  unfold limw
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have := limθ_le_one N
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem one_sub_N_mul_limw (N : ℕ) :
    1 - (N : ℝ) * limw N = (2 * (N : ℝ) + 1) / ((N : ℝ) + 1) ^ 2 := by
  rw [limw_eq]
  have h : ((N : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem limg_nonneg (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) (N : ℕ) : 0 ≤ limg δ N := by
  unfold limg
  have h1' : 0 < 1 - δ := by linarith
  have := limw_nonneg N
  positivity

/-- Supporting lemma (no headline claim; see the headline it serves): `g_N ≤ δ/(1−δ) ≤ 1` on `δ ≤ 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem limg_le_one (δ : ℝ) (h0 : 0 < δ) (hhalf : δ ≤ 1 / 2) (N : ℕ) : limg δ N ≤ 1 := by
  unfold limg
  have h1 : 0 < 1 - δ := by linarith
  have hx1 : (N : ℝ) * limw N ≤ 1 := by linarith [N_mul_limw_le N, limθ_pos N]
  have hx0 : 0 ≤ (N : ℝ) * limw N := mul_nonneg (Nat.cast_nonneg _) (limw_nonneg N)
  have key : δ ^ 2 * ((N : ℝ) * limw N) / (1 - δ) ≤ 1 - δ := by
    rw [div_le_iff₀ h1]
    nlinarith [mul_nonneg (sq_nonneg δ) (sub_nonneg.2 hx1)]
  linarith

/-- The limit instance's parameters at `δ ∈ (0, 1/2]`, `N ≥ 1`: `n = N`, `θ = 1/(N+1)`, `g = g_N`.
Source: [[uea-self-game-mandate]] target 6 (the limit)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def limParams (δ : ℝ) (h0 : 0 < δ) (hhalf : δ ≤ 1 / 2) (N : ℕ) (hN : 1 ≤ N) :
    Params where
  n := N
  θ := limθ N
  δ := δ
  g := limg δ N
  θ_pos := limθ_pos N
  θ_lt_one := limθ_lt_one N hN
  δ_pos := h0
  δ_lt_one := by linarith
  g_nonneg := limg_nonneg δ h0 (by linarith) N
  g_le_one := limg_le_one δ h0 hhalf N

/-- **The supremum half of the corrected tightness statement, on `δ ≤ 1/2`** (formerly the OPEN
`sup_limit_open`): for every `δ ∈ (0, 1/2]` and `ε > 0` there is an instance on `Fin n → Fin 2` with a
pure fixed point, the trust bound at every situation, and gap `≥ δ/(1−δ) − ε`. The instance is
`T3(N+2, 1/(N+1), g_N)` with `g_N` the deviation-situation cap, whose gap is
`δ/(1−δ) − δ²(2N+1)/((1−δ)(N+1)²)`; `N ≥ 2δ²/((1−δ)ε)` suffices. With `Attainment.theoremC_strict`
(`U* − δ/(1−δ) < U(π)` at every pure fixed point with the trust bound somewhere, `δ > 0`), `δ/(1−δ)` is
the exact, unattained supremum of the gap over such fixed points on `δ ≤ 1/2`. The hypothesis
`δ ≤ 1/2` is forced: the gap is at most `1` (`Regimes.gap_le_one`), and above `1/2` the supremum is
`1`, attained (`gap_one_attained_above_half`).
Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[uea-self-game-mandate]] target 6 (`stretch`: "for every `ε > 0` there are `n`, `θ`, `g` with `T3(n,θ,g)` a fixed point with `TB` everywhere and `g ≥ δ/(1−δ) − ε`", which omits `δ ≤ 1/2`); [[uea-2-inventory]] 2-013
Kind: P
Fidelity: variant: restricted to `δ ≤ 1/2` (the mandate's sentence is false above `1/2`, `Regimes.sup_limit_previous_form_false_above_half`)
Hyps: (a) -/
theorem sup_limit (δ : ℝ) (h0 : 0 < δ) (hhalf : δ ≤ 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (G : Game (Fin n) (Fin 2)) (π : Fin n → Fin 2), G.δ = δ ∧ G.IsPureFP π ∧
      (∀ s, G.TB (G.muSelf π) s) ∧ δ / (1 - δ) - ε ≤ G.Ustar - G.U π := by
  have h1 : 0 < 1 - δ := by linarith
  have h1' : (1 - δ) ≠ 0 := h1.ne'
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * δ ^ 2 / ((1 - δ) * ε))
  set N : ℕ := N₀ + 1 with hN_def
  have hN : 1 ≤ N := Nat.le_add_left 1 N₀
  have hNcast : (N₀ : ℝ) ≤ (N : ℝ) + 1 := by rw [hN_def]; push_cast; linarith
  have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set P := limParams δ h0 hhalf N hN with hP
  have hwP : w P = limw N := rfl
  have hθP : P.θ = limθ N := rfl
  have hnP : (P.n : ℝ) = N := rfl
  have hgP : P.g = limg δ N := rfl
  have hδP : P.δ = δ := rfl
  -- the three conditions of `family`
  have hθ0 := limθ_pos N
  have hw0 := limw_nonneg N
  have hwθ : 0 < limw N + limθ N := by positivity
  have hNw := N_mul_limw_le N
  have hden : 0 < (1 - δ) + δ * ((N : ℝ) * limw N) := by positivity
  have hg : (1 - δ) * limg δ N = (1 - δ) * δ + δ ^ 2 * ((N : ℝ) * limw N) := by
    unfold limg; field_simp
  have hR : ((1 - δ) * (1 - limg δ N) + δ * ((N : ℝ) * limw N)) /
      ((1 - δ) + δ * ((N : ℝ) * limw N)) = 1 - δ := by
    rw [div_eq_iff hden.ne']
    linear_combination -hg
  have hFP : w P / (w P + P.θ) ≤
      ((1 - P.δ) * (1 - P.g) + P.δ * (P.n * w P)) / ((1 - P.δ) + P.δ * (P.n * w P)) := by
    rw [hwP, hθP, hnP, hgP, hδP, hR, div_le_iff₀ hwθ]
    have hlw := limw_le_limθ N
    nlinarith [mul_le_mul_of_nonneg_left hlw h0.le,
      mul_nonneg hθ0.le (by linarith : (0 : ℝ) ≤ 1 - 2 * δ)]
  have hTBi : P.g ≤ P.δ + P.δ ^ 2 * (P.n * w P) / (1 - P.δ) := by
    rw [hgP, hδP, hnP, hwP]; unfold limg; exact le_rfl
  have hTB0 : P.g ≤ P.δ + P.δ ^ 2 * (1 - P.θ) / (1 - P.δ) := by
    rw [hgP, hθP, hδP]
    unfold limg
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNw (sq_nonneg δ)) h1.le
    linarith
  obtain ⟨hfp, htb, hgap⟩ := family P hFP hTB0 hTBi
  refine ⟨P.n + 2, game P, aPol P, rfl, hfp, htb, ?_⟩
  rw [hgap, hgP]
  -- the gap bound: `δ/(1−δ) − g_N = δ²(2N+1)/((1−δ)(N+1)²) ≤ 2δ²/((1−δ)(N+1)) ≤ ε`
  have hdef : δ / (1 - δ) - limg δ N =
      δ ^ 2 * ((2 * (N : ℝ) + 1) / ((N : ℝ) + 1) ^ 2) / (1 - δ) := by
    unfold limg
    rw [← one_sub_N_mul_limw]
    field_simp
    ring
  have hb1 : (2 * (N : ℝ) + 1) / ((N : ℝ) + 1) ^ 2 ≤ 2 / ((N : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) hM]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hb2 : δ ^ 2 * (2 / ((N : ℝ) + 1)) / (1 - δ) ≤ ε := by
    rw [div_le_iff₀ h1, mul_div_assoc', div_le_iff₀ hM]
    rw [div_le_iff₀ (by positivity)] at hN₀
    have hpos : (0 : ℝ) ≤ (1 - δ) * ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hNcast hpos]
  have hb : δ ^ 2 * ((2 * (N : ℝ) + 1) / ((N : ℝ) + 1) ^ 2) / (1 - δ) ≤
      δ ^ 2 * (2 / ((N : ℝ) + 1)) / (1 - δ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb1 (sq_nonneg δ)) h1.le
  linarith [hdef, hb, hb2]

/-! ### Above `δ = 1/2`: the gap `1` is attained, for every `δ ∈ (1/2, 1)` -/

/-- The `g = 1` instance's polluter weight `θ = (1−δ)/(δN)`: the least weight making the own action an
argmax (a tie) at every deviation situation when `U(aPol) = 0`.
Source: round-2 adversarial audit B1 (the hand calculation for `δ ∈ (1/2, 2/3)`); [[uea-self-game-mandate]] target 6 (the `T3` shape with `g = 1`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def oneθ (δ : ℝ) (N : ℕ) : ℝ := (1 - δ) / (δ * N)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem oneθ_pos (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) (N : ℕ) (hN : 1 ≤ N) : 0 < oneθ δ N := by
  unfold oneθ
  have : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  exact div_pos (by linarith) (by positivity)

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem oneθ_lt_one (δ : ℝ) (hhalf : 1 / 2 < δ) (h1 : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    oneθ δ N < 1 := by
  unfold oneθ
  have h0 : 0 < δ := by linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_lt_one (by positivity)]
  nlinarith [mul_nonneg h0.le (sub_nonneg.2 hN')]

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem oneθ_mul (δ : ℝ) (h0 : 0 < δ) (N : ℕ) (hN : 1 ≤ N) : oneθ δ N * (δ * N) = 1 - δ := by
  unfold oneθ
  have : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hne : (δ * N) ≠ 0 := by positivity
  field_simp

/-- The `g = 1` instance's parameters at `δ ∈ (1/2, 1)`, `N ≥ 1`: `n = N`, `θ = (1−δ)/(δN)`, `g = 1`.
Source: round-2 adversarial audit B1; [[uea-self-game-mandate]] target 6 (the `T3` shape with `g = 1`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def oneParams (δ : ℝ) (hhalf : 1 / 2 < δ) (h1 : δ < 1) (N : ℕ) (hN : 1 ≤ N) :
    Params where
  n := N
  θ := oneθ δ N
  δ := δ
  g := 1
  θ_pos := oneθ_pos δ (by linarith) h1 N hN
  θ_lt_one := oneθ_lt_one δ hhalf h1 N hN
  δ_pos := by linarith
  δ_lt_one := h1
  g_nonneg := zero_le_one
  g_le_one := le_rfl

/-- **Above `δ = 1/2` the maximal gap `1` is attained, for every `δ ∈ (1/2, 1)`**: an instance with a
pure fixed point, the trust bound at every situation, and gap `U* − U(π) = 1`. The instance is
`T3(N+2, (1−δ)/(δN), 1)` with `N ≥ (1−δ)/(2δ−1)` (the auditor's condition `x²(n−1) + x ≤ n − 2`,
`x = (1−δ)/δ`, in this module's indexing): the own action ties the deviation at every deviation
situation (`(1−δ) = θδN`) and the trust bound there reduces to `(1−δ) ≤ N(2δ−1)`. So on `(1/2, 1)` the
supremum of the gap over pure fixed points with the trust bound everywhere is `1`, attained, and Theorem
C's constant `δ/(1−δ) > 1` is not the truth there. Extends `Regimes.GapOne.gap_one_attained`
(`Fin 3`, `δ ∈ [2/3, 1)`) to all of `(1/2, 1)`.
Scope: finite updateless self-game — pointwise EDT conditional on one's own action, self-consistent
belief; not rOSI, not the sequential model of `uea-cole-shadow`.
Source: round-2 adversarial audit B1 ("for `δ ∈ (1/2, 2/3)` an `n`-situation version works once `x²(n−1) + x ≤ n − 2` — hand calculation, not machine-checked"); [[uea-self-game-mandate]] target 6 (the `stretch` limit, corrected)
Kind: P
Fidelity: exact (symbolic `δ ∈ (1/2, 1)`)
Hyps: (a) -/
theorem gap_one_attained_above_half (δ : ℝ) (hhalf : 1 / 2 < δ) (h1 : δ < 1) :
    ∃ (n : ℕ) (G : Game (Fin n) (Fin 2)) (π : Fin n → Fin 2), G.δ = δ ∧ G.IsPureFP π ∧
      (∀ s, G.TB (G.muSelf π) s) ∧ G.Ustar - G.U π = 1 := by
  have h0 : 0 < δ := by linarith
  have h1' : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 * δ - 1 := by linarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((1 - δ) / (2 * δ - 1))
  set N : ℕ := N₀ + 1 with hN_def
  have hN : 1 ≤ N := Nat.le_add_left 1 N₀
  have hNcast : (N₀ : ℝ) ≤ N := by rw [hN_def]; push_cast; linarith
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  set P := oneParams δ hhalf h1 N hN with hP
  have hwP : w P = (1 - oneθ δ N) / ((N : ℝ) + 1) := rfl
  have hθP : P.θ = oneθ δ N := rfl
  have hnP : (P.n : ℝ) = N := rfl
  have hgP : P.g = 1 := rfl
  have hδP : P.δ = δ := rfl
  have hθ0 := oneθ_pos δ h0 h1 N hN
  have hθ1 := oneθ_lt_one δ hhalf h1 N hN
  have hθmul := oneθ_mul δ h0 N hN
  have hw0 : 0 < w P := w_pos P
  -- `(1−δ) ≤ N(2δ−1)` from the choice of `N`
  have hNbound : 1 - δ ≤ (N : ℝ) * (2 * δ - 1) := by
    rw [div_le_iff₀ h2] at hN₀
    nlinarith [mul_le_mul_of_nonneg_right hNcast h2.le]
  -- the core inequality `(1−δ)² ≤ δ² N w`
  have hNw : (N : ℝ) * w P = (N : ℝ) * (1 - oneθ δ N) / ((N : ℝ) + 1) := by
    rw [hwP, mul_div_assoc']
  have hcore : (1 - δ) ^ 2 ≤ δ ^ 2 * ((N : ℝ) * w P) := by
    rw [hNw, mul_div_assoc', le_div_iff₀ (by positivity)]
    have hθ2 : δ ^ 2 * ((N : ℝ) * oneθ δ N) = δ * (1 - δ) := by rw [← hθmul]; ring
    nlinarith [hNbound, hθ2]
  -- the three conditions of `family`
  have hden : 0 < (1 - δ) + δ * ((N : ℝ) * w P) := by positivity
  have hwθ : 0 < w P + oneθ δ N := by positivity
  have hFP : w P / (w P + P.θ) ≤
      ((1 - P.δ) * (1 - P.g) + P.δ * (P.n * w P)) / ((1 - P.δ) + P.δ * (P.n * w P)) := by
    rw [hθP, hδP, hgP, hnP, div_le_div_iff₀ hwθ hden]
    have hθ3 : w P * ((N : ℝ) * oneθ δ N) * δ = w P * (1 - δ) := by rw [← hθmul]; ring
    nlinarith [hθ3]
  have hTBi : P.g ≤ P.δ + P.δ ^ 2 * (P.n * w P) / (1 - P.δ) := by
    rw [hgP, hδP, hnP, le_add_div_iff h1']
    nlinarith [hcore]
  have hTB0 : P.g ≤ P.δ + P.δ ^ 2 * (1 - P.θ) / (1 - P.δ) := by
    rw [hgP, hδP, hθP, le_add_div_iff h1']
    have hle := n_mul_w_le P
    rw [hnP, hθP] at hle
    nlinarith [hcore, mul_le_mul_of_nonneg_left hle (sq_nonneg δ)]
  obtain ⟨hfp, htb, hgap⟩ := family P hFP hTB0 hTBi
  exact ⟨P.n + 2, game P, aPol P, rfl, hfp, htb, by rw [hgap, hgP]⟩

end T3Family

end Cleanroom.Uea.UeaSelfGame
