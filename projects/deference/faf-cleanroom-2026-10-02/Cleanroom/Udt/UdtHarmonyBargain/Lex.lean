import Cleanroom.Udt.UdtHarmonyBargain.Perturbed
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# `udt-harmony-bargain` — the two-player lexicographic criterion (T3(iii))

For a two-player game `G : StrategicGame (Fin 2) ℝ`, the payoff of the pure deviation `s` against
the uniform perturbation `σ^ε_{-i}` of `s*` is `Mᵢ(s) + ε (Tᵢ(s) − K_{-i} Mᵢ(s))`, with
`Mᵢ(s)` the payoff against `s*_{-i}` and `Tᵢ(s)` the total against every pure strategy of the
opponent (dp-cf-003's `M + ε(T − 32M)`). Hence the lexicographic criterion
"`M` strictly worse, or `M` tied and `T` no better" for every alternative of every player makes
`s*` a trembling-hand equilibrium (`uniform_thpe_of_lex`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset StrategicGame

variable {G : StrategicGame (Fin 2) ℝ} [∀ i, Fintype (G.strategy i)] [∀ i, DecidableEq (G.strategy i)]

/-- The profile `(x, y)` of a two-player game.
Source: none: infrastructure
Kind: D -/
def pair (x : G.strategy 0) (y : G.strategy 1) : G.Profile :=
  (piFinTwoEquiv G.strategy).symm (x, y)

@[simp] theorem pair_zero (x : G.strategy 0) (y : G.strategy 1) : pair x y 0 = x := rfl

@[simp] theorem pair_one (x : G.strategy 0) (y : G.strategy 1) : pair x y 1 = y := rfl

theorem pair_eq (σ : G.Profile) : pair (σ 0) (σ 1) = σ :=
  (piFinTwoEquiv G.strategy).symm_apply_apply σ

theorem update_pair_zero (x x' : G.strategy 0) (y : G.strategy 1) :
    Function.update (pair x y) 0 x' = pair x' y := by
  funext i
  fin_cases i <;> simp

theorem update_pair_one (x : G.strategy 0) (y y' : G.strategy 1) :
    Function.update (pair x y) 1 y' = pair x y' := by
  funext i
  fin_cases i <;> simp

/-- Sums over two-player profiles are double sums.
Source: none: infrastructure
Kind: L -/
theorem sum_profile_two (F : G.Profile → ℝ) : ∑ σ, F σ = ∑ x, ∑ y, F (pair x y) := by
  rw [← (piFinTwoEquiv G.strategy).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- `Mᵢ(s)`: the payoff of `s` against `s*_{-i}` (player `0`).
Source: mandate T3(iii)
Kind: D -/
def M0 (sStar : G.Profile) (s : G.strategy 0) : ℝ := G.payoff (pair s (sStar 1)) 0

/-- `Tᵢ(s)`: the total payoff of `s` against every pure strategy of the opponent (player `0`).
Source: mandate T3(iii); dp-cf-003's `T`
Kind: D -/
def T0 (s : G.strategy 0) : ℝ := ∑ t, G.payoff (pair s t) 0

/-- `M` for player `1`. Source: mandate T3(iii). Kind: D -/
def M1 (sStar : G.Profile) (t : G.strategy 1) : ℝ := G.payoff (pair (sStar 0) t) 1

/-- `T` for player `1`. Source: mandate T3(iii). Kind: D -/
def T1 (t : G.strategy 1) : ℝ := ∑ s, G.payoff (pair s t) 1

theorem sum_unifPertVal {N : Type} [Fintype N] [DecidableEq N] {H : StrategicGame N ℝ}
    [∀ i, Fintype (H.strategy i)] [∀ i, DecidableEq (H.strategy i)]
    (ε : ℝ) (sStar : H.Profile) (i : N) : ∑ s, unifPertVal ε sStar i s = 1 := by
  unfold unifPertVal
  have : ∀ s : H.strategy i, (if s = sStar i then 1 - (Fintype.card (H.strategy i) - 1) * ε else ε)
      = ε + (if s = sStar i then 1 - Fintype.card (H.strategy i) * ε else 0) := by
    intro s; split_ifs <;> ring
  simp_rw [this]
  rw [sum_add_distrib, sum_ite_eq', if_pos (mem_univ _), sum_const, card_univ, nsmul_eq_mul]
  ring

/-- `∑_s σ^ε_i(s) f(s) = f(s*ᵢ) + ε (∑_s f(s) − Kᵢ f(s*ᵢ))`: the order-`ε` expansion.
Source: mandate T3(iii) (dp-cf-003's `M + ε(T − 32 M)`)
Kind: P -/
theorem sum_unifPertVal_mul {N : Type} [Fintype N] [DecidableEq N] {H : StrategicGame N ℝ}
    [∀ i, Fintype (H.strategy i)] [∀ i, DecidableEq (H.strategy i)]
    (ε : ℝ) (sStar : H.Profile) (i : N) (f : H.strategy i → ℝ) :
    ∑ s, unifPertVal ε sStar i s * f s =
      f (sStar i) + ε * (∑ s, f s - Fintype.card (H.strategy i) * f (sStar i)) := by
  unfold unifPertVal
  have : ∀ s : H.strategy i,
      (if s = sStar i then 1 - (Fintype.card (H.strategy i) - 1) * ε else ε) * f s
      = ε * f s + (if s = sStar i then (1 - Fintype.card (H.strategy i) * ε) * f s else 0) := by
    intro s; split_ifs <;> ring
  simp_rw [this]
  rw [sum_add_distrib, sum_ite_eq', if_pos (mem_univ _), ← mul_sum]
  ring

/-- Player `0`'s pure-deviation payoff against the uniform perturbation.
Source: mandate T3(iii)
Kind: P -/
theorem pureDevFun_unifPert_zero (ε : ℝ) (sStar : G.Profile) (s : G.strategy 0) :
    pureDevFun G (unifPertVal ε sStar) 0 s =
      M0 sStar s + ε * (T0 s - Fintype.card (G.strategy 1) * M0 sStar s) := by
  unfold pureDevFun
  rw [sum_profile_two]
  simp_rw [Fin.prod_univ_two, pair_zero, pair_one, update_pair_zero]
  have : ∀ x : G.strategy 0, ∑ y, unifPertVal ε sStar 0 x * unifPertVal ε sStar 1 y *
      G.payoff (pair s y) 0 = unifPertVal ε sStar 0 x *
        ∑ y, unifPertVal ε sStar 1 y * G.payoff (pair s y) 0 := by
    intro x; rw [mul_sum]; refine sum_congr rfl fun y _ => ?_; ring
  simp_rw [this]
  rw [← sum_mul, sum_unifPertVal, one_mul, sum_unifPertVal_mul]
  rfl

/-- Player `1`'s pure-deviation payoff against the uniform perturbation.
Source: mandate T3(iii)
Kind: P -/
theorem pureDevFun_unifPert_one (ε : ℝ) (sStar : G.Profile) (t : G.strategy 1) :
    pureDevFun G (unifPertVal ε sStar) 1 t =
      M1 sStar t + ε * (T1 t - Fintype.card (G.strategy 0) * M1 sStar t) := by
  unfold pureDevFun
  rw [sum_profile_two]
  simp_rw [Fin.prod_univ_two, pair_zero, pair_one, update_pair_one]
  have : ∀ x : G.strategy 0, ∑ y, unifPertVal ε sStar 0 x * unifPertVal ε sStar 1 y *
      G.payoff (pair x t) 1 = unifPertVal ε sStar 0 x * G.payoff (pair x t) 1 *
        ∑ y, unifPertVal ε sStar 1 y := by
    intro x; rw [mul_sum]; refine sum_congr rfl fun y _ => ?_; ring
  simp_rw [this]
  rw [sum_unifPertVal]
  simp_rw [mul_one]
  rw [sum_unifPertVal_mul]
  rfl

/-- A positive lower bound for finitely many positive reals.
Source: none: infrastructure
Kind: L -/
theorem exists_pos_le_of_pos {S : Type*} [Fintype S] [Nonempty S] (f : S → ℝ) (hf : ∀ s, 0 < f s) :
    ∃ ε₀, 0 < ε₀ ∧ ∀ s, ε₀ ≤ f s :=
  ⟨univ.inf' univ_nonempty f, (Finset.lt_inf'_iff _).2 fun s _ => hf s,
    fun s => Finset.inf'_le f (mem_univ s)⟩

/-- The margin `ε` may use against one alternative: if the alternative is strictly worse at order
`0` with gap `g`, then `ε ≤ g / (|ΔT| + K g + 1)` keeps it worse at order `ε`.
Source: mandate T3(iii)
Kind: L -/
theorem margin_ok {m mStar tS tStar K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hlt : m < mStar)
    (hmargin : ε ≤ (mStar - m) / (|tS - tStar| + K * (mStar - m) + 1)) :
    m + ε * (tS - K * m) ≤ mStar + ε * (tStar - K * mStar) := by
  set g := mStar - m with hg
  have hgpos : 0 < g := by rw [hg]; linarith
  have hden : 0 < |tS - tStar| + K * g + 1 := by positivity
  have h1 : ε * (|tS - tStar| + K * g + 1) ≤ g := by
    rwa [le_div_iff₀ hden] at hmargin
  have h2 : tS - tStar ≤ |tS - tStar| := le_abs_self _
  have h3 : ε * (tS - tStar) ≤ ε * |tS - tStar| := mul_le_mul_of_nonneg_left h2 hε
  nlinarith

/-- Whether an alternative is strictly worse at order `0`: the admissible margin, positive.
Source: none: infrastructure
Kind: D -/
noncomputable def marginOf (m mStar tS tStar K : ℝ) : ℝ :=
  if m < mStar then (mStar - m) / (|tS - tStar| + K * (mStar - m) + 1) else 1

theorem marginOf_pos {m mStar tS tStar K : ℝ} (hK : 0 ≤ K) : 0 < marginOf m mStar tS tStar K := by
  unfold marginOf
  split_ifs with h
  · have : 0 < mStar - m := by linarith
    positivity
  · exact one_pos

/-- **The two-player lexicographic criterion** (T3(iii)): if for each player every alternative to
`s*ᵢ` is strictly worse against `s*_{-i}`, or tied there and no better in total against every pure
strategy of the opponent, then `s*` is a trembling-hand equilibrium (SC Def. 10.4), via the uniform
perturbation. This is the Selten step dp-cf-003 left as prose.
Source: mandate T3(iii) (`uniform_thpe_of_lex`); dp-cf-003
Kind: P
Fidelity: exact (two players; the `n`-player expansion is T16(i))
Hyps: (a) all -/
theorem uniform_thpe_of_lex (sStar : G.Profile)
    (h0 : ∀ s, M0 sStar s < M0 sStar (sStar 0) ∨
      (M0 sStar s = M0 sStar (sStar 0) ∧ T0 s ≤ T0 (sStar 0)))
    (h1 : ∀ t, M1 sStar t < M1 sStar (sStar 1) ∨
      (M1 sStar t = M1 sStar (sStar 1) ∧ T1 t ≤ T1 (sStar 1))) :
    THPE (pureProfileToMixed sStar) := by
  haveI : Nonempty (G.strategy 0) := ⟨sStar 0⟩
  haveI : Nonempty (G.strategy 1) := ⟨sStar 1⟩
  set K0 : ℝ := (Fintype.card (G.strategy 0) : ℝ) with hK0
  set K1 : ℝ := (Fintype.card (G.strategy 1) : ℝ) with hK1
  have hK0n : 0 ≤ K0 := Nat.cast_nonneg _
  have hK1n : 0 ≤ K1 := Nat.cast_nonneg _
  obtain ⟨e0, he0, he0le⟩ := exists_pos_le_of_pos
    (fun s => marginOf (M0 sStar s) (M0 sStar (sStar 0)) (T0 s) (T0 (sStar 0)) K1)
    (fun s => marginOf_pos hK1n)
  obtain ⟨e1, he1, he1le⟩ := exists_pos_le_of_pos
    (fun t => marginOf (M1 sStar t) (M1 sStar (sStar 1)) (T1 t) (T1 (sStar 1)) K0)
    (fun t => marginOf_pos hK0n)
  set eK : ℝ := 1 / (K0 + K1 + 1) with heK
  have heKpos : 0 < eK := by positivity
  refine thpe_of_unifPert sStar (ε₀ := min (min e0 e1) eK) (lt_min (lt_min he0 he1) heKpos) ?_ ?_
  · intro i
    have hle : min (min e0 e1) eK ≤ eK := min_le_right _ _
    have hnn : 0 ≤ min (min e0 e1) eK := (lt_min (lt_min he0 he1) heKpos).le
    fin_cases i
    · calc (Fintype.card (G.strategy 0) : ℝ) * min (min e0 e1) eK ≤ K0 * eK :=
            mul_le_mul_of_nonneg_left hle hK0n
        _ ≤ 1 := by rw [heK, mul_one_div, div_le_one (by positivity)]; linarith
    · calc (Fintype.card (G.strategy 1) : ℝ) * min (min e0 e1) eK ≤ K1 * eK :=
            mul_le_mul_of_nonneg_left hle hK1n
        _ ≤ 1 := by rw [heK, mul_one_div, div_le_one (by positivity)]; linarith
  · intro ε hε hεle i s
    have hε0 : ε ≤ e0 := le_trans hεle (le_trans (min_le_left _ _) (min_le_left _ _))
    have hε1 : ε ≤ e1 := le_trans hεle (le_trans (min_le_left _ _) (min_le_right _ _))
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [pureDevFun_unifPert_zero, pureDevFun_unifPert_zero]
      rcases h0 s with hlt | ⟨heq, hT⟩
      · have hm := he0le s
        simp only [marginOf, if_pos hlt] at hm
        exact margin_ok hK1n hε.le hlt (le_trans hε0 hm)
      · rw [heq]
        have : ε * (T0 s - K1 * M0 sStar (sStar 0)) ≤ ε * (T0 (sStar 0) - K1 * M0 sStar (sStar 0)) :=
          mul_le_mul_of_nonneg_left (by linarith) hε.le
        linarith
    · simp only [Fin.mk_one, Fin.isValue]
      rw [pureDevFun_unifPert_one, pureDevFun_unifPert_one]
      rcases h1 s with hlt | ⟨heq, hT⟩
      · have hm := he1le s
        simp only [marginOf, if_pos hlt] at hm
        exact margin_ok hK0n hε.le hlt (le_trans hε1 hm)
      · rw [heq]
        have : ε * (T1 s - K0 * M1 sStar (sStar 1)) ≤ ε * (T1 (sStar 1) - K0 * M1 sStar (sStar 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hε.le
        linarith

end Cleanroom.Udt.UdtHarmonyBargain
