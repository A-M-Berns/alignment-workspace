import Cleanroom.Decision.DpCalibLimits.Defs

/-!
# Elementary sequence convergence, and continuity of the run law in the weights

Infrastructure for T4 ([[dp-calib-limits-mandate]] T4(c),(e)): the test-sequence device
speaks of `ε_n → 0` and `C_n → C` elementarily (no topology, as `dp-calibration`'s
`TestSeqTrembleEdtConsistent` does). `SeqTendsTo` is that notion; it is closed under the ring
operations, finite sums and quotients with non-zero limit, weak inequalities pass to the
limit, and a positive limit is eventually positive. The run law `leafLaw`, `ν`, `paySum` and
`condExp` (where `ν > 0`) are continuous in the weights (`leafLaw_tendsTo` …), and the
trembles of a convergent sequence at vanishing `ε_n` converge to the limit procedure
(`tremble_tendsTo`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Elementary convergence of a sequence: `∀ δ > 0, ∃ N, ∀ n ≥ N, |x n − l| < δ`.
Source: none: infrastructure (`dynamic.md` DY-3's "convergence stated elementarily")
Kind: D -/
def SeqTendsTo (x : ℕ → K) (l : K) : Prop := ∀ δ > (0 : K), ∃ N, ∀ n ≥ N, |x n - l| < δ

namespace SeqTendsTo

variable {x y : ℕ → K} {l m : K}

/-- Constant sequences. Source: none: infrastructure. Kind: L -/
theorem const (c : K) : SeqTendsTo (fun _ => c) c :=
  fun δ hδ => ⟨0, fun _ _ => by simp [hδ]⟩

/-- Pointwise-equal sequences. Source: none: infrastructure. Kind: L -/
theorem congr (h : SeqTendsTo x l) (hxy : ∀ n, x n = y n) : SeqTendsTo y l := by
  intro δ hδ
  obtain ⟨N, hN⟩ := h δ hδ
  exact ⟨N, fun n hn => by rw [← hxy]; exact hN n hn⟩

/-- Sums. Source: none: infrastructure. Kind: L -/
theorem add (hx : SeqTendsTo x l) (hy : SeqTendsTo y m) :
    SeqTendsTo (fun n => x n + y n) (l + m) := by
  intro δ hδ
  obtain ⟨N₁, h₁⟩ := hx (δ / 2) (by positivity)
  obtain ⟨N₂, h₂⟩ := hy (δ / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have e : x n + y n - (l + m) = (x n - l) + (y n - m) := by ring
  rw [e]
  calc |x n - l + (y n - m)| ≤ |x n - l| + |y n - m| := abs_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add (h₁ n (le_of_max_le_left hn)) (h₂ n (le_of_max_le_right hn))
    _ = δ := by ring

/-- Negation. Source: none: infrastructure. Kind: L -/
theorem neg (hx : SeqTendsTo x l) : SeqTendsTo (fun n => -x n) (-l) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hx δ hδ
  refine ⟨N, fun n hn => ?_⟩
  rw [show -x n - -l = -(x n - l) by ring, abs_neg]
  exact hN n hn

/-- Differences. Source: none: infrastructure. Kind: L -/
theorem sub (hx : SeqTendsTo x l) (hy : SeqTendsTo y m) :
    SeqTendsTo (fun n => x n - y n) (l - m) := by
  have := hx.add hy.neg
  simpa [sub_eq_add_neg] using this

/-- Products. Source: none: infrastructure. Kind: L -/
theorem mul (hx : SeqTendsTo x l) (hy : SeqTendsTo y m) :
    SeqTendsTo (fun n => x n * y n) (l * m) := by
  intro δ hδ
  obtain ⟨N₀, h₀⟩ := hy 1 one_pos
  have hm1 : (0 : K) < |m| + 1 := by positivity
  have hl1 : (0 : K) < |l| + 1 := by positivity
  obtain ⟨N₁, h₁⟩ := hx (δ / (2 * (|m| + 1))) (by positivity)
  obtain ⟨N₂, h₂⟩ := hy (δ / (2 * (|l| + 1))) (by positivity)
  refine ⟨max N₀ (max N₁ N₂), fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := le_of_max_le_left hn
  have hn1 : N₁ ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hn2 : N₂ ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  have hy_bd : |y n| ≤ |m| + 1 := by
    have := h₀ n hn0
    calc |y n| = |(y n - m) + m| := by ring_nf
      _ ≤ |y n - m| + |m| := abs_add_le _ _
      _ ≤ |m| + 1 := by linarith
  have e : x n * y n - l * m = (x n - l) * y n + l * (y n - m) := by ring
  have hm1' : |m| + 1 ≠ 0 := hm1.ne'
  have hl1' : |l| + 1 ≠ 0 := hl1.ne'
  have hA : |x n - l| * |y n| ≤ δ / 2 := by
    calc |x n - l| * |y n| ≤ (δ / (2 * (|m| + 1))) * (|m| + 1) :=
          mul_le_mul (h₁ n hn1).le hy_bd (abs_nonneg _) (by positivity)
      _ = δ / 2 := by field_simp; try ring
  have hB : |l| * |y n - m| < δ / 2 := by
    calc |l| * |y n - m| ≤ (|l| + 1) * |y n - m| :=
          mul_le_mul_of_nonneg_right (by linarith [abs_nonneg l]) (abs_nonneg _)
      _ < (|l| + 1) * (δ / (2 * (|l| + 1))) := mul_lt_mul_of_pos_left (h₂ n hn2) hl1
      _ = δ / 2 := by field_simp; try ring
  rw [e]
  calc |(x n - l) * y n + l * (y n - m)| ≤ |(x n - l) * y n| + |l * (y n - m)| := abs_add_le _ _
    _ = |x n - l| * |y n| + |l| * |y n - m| := by rw [abs_mul, abs_mul]
    _ < δ / 2 + δ / 2 := add_lt_add_of_le_of_lt hA hB
    _ = δ := by ring

/-- Inverses at a non-zero limit. Source: none: infrastructure. Kind: L -/
theorem inv (hx : SeqTendsTo x l) (hl : l ≠ 0) : SeqTendsTo (fun n => (x n)⁻¹) l⁻¹ := by
  intro δ hδ
  have hlpos : 0 < |l| := abs_pos.mpr hl
  obtain ⟨N₀, h₀⟩ := hx (|l| / 2) (by positivity)
  obtain ⟨N₁, h₁⟩ := hx (δ * |l| ^ 2 / 2) (by positivity)
  refine ⟨max N₀ N₁, fun n hn => ?_⟩
  have hbd : |l| / 2 ≤ |x n| := by
    have h1 := h₀ n (le_of_max_le_left hn)
    have h2 := abs_sub_abs_le_abs_sub l (x n)
    rw [abs_sub_comm] at h2
    linarith
  have hxn : x n ≠ 0 := by
    intro h; rw [h, abs_zero] at hbd; linarith
  rw [show (x n)⁻¹ - l⁻¹ = (l - x n) / (x n * l) by field_simp, abs_div, abs_mul, abs_sub_comm,
    div_lt_iff₀ (mul_pos (abs_pos.mpr hxn) hlpos)]
  calc |x n - l| < δ * |l| ^ 2 / 2 := h₁ n (le_of_max_le_right hn)
    _ = δ * (|l| / 2) * |l| := by ring
    _ ≤ δ * |x n| * |l| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbd hδ.le) (abs_nonneg _)
    _ = δ * (|x n| * |l|) := by ring

/-- Quotients at a non-zero limit denominator. Source: none: infrastructure. Kind: L -/
theorem div (hx : SeqTendsTo x l) (hy : SeqTendsTo y m) (hm : m ≠ 0) :
    SeqTendsTo (fun n => x n / y n) (l / m) := by
  have := hx.mul (hy.inv hm)
  simpa [div_eq_mul_inv] using this

/-- Finite sums. Source: none: infrastructure. Kind: L -/
theorem sum {α : Type} (S : Finset α) (f : α → ℕ → K) (g : α → K)
    (h : ∀ i ∈ S, SeqTendsTo (f i) (g i)) :
    SeqTendsTo (fun n => ∑ i ∈ S, f i n) (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using SeqTendsTo.const (0 : K)
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Weak inequalities pass to the limit. Source: none: infrastructure. Kind: L -/
theorem le_of_eventually_le (hx : SeqTendsTo x l) (hy : SeqTendsTo y m)
    (h : ∃ N, ∀ n ≥ N, x n ≤ y n) : l ≤ m := by
  by_contra hlt
  push Not at hlt
  obtain ⟨N₀, h₀⟩ := h
  obtain ⟨N₁, h₁⟩ := hx ((l - m) / 2) (by linarith)
  obtain ⟨N₂, h₂⟩ := hy ((l - m) / 2) (by linarith)
  have a := h₀ (max N₀ (max N₁ N₂)) (le_max_left _ _)
  have b := h₁ (max N₀ (max N₁ N₂)) (le_of_max_le_left (le_max_right _ _))
  have c := h₂ (max N₀ (max N₁ N₂)) (le_of_max_le_right (le_max_right _ _))
  rw [abs_lt] at b c
  linarith [b.1, c.2]

/-- A positive limit is eventually positive. Source: none: infrastructure. Kind: L -/
theorem eventually_pos (hx : SeqTendsTo x l) (hl : 0 < l) : ∃ N, ∀ n ≥ N, 0 < x n := by
  obtain ⟨N, hN⟩ := hx l hl
  exact ⟨N, fun n hn => by have := (abs_lt.mp (hN n hn)).1; linarith⟩

end SeqTendsTo

/-! ## Continuity of the run law in the weights -/

section tree

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- Pointwise convergence of procedures (every weight converges).
Source: `dynamic.md` DY-3 ("`C_n → C` pointwise in every weight")
Kind: D -/
def ProcTendsTo (Dn : ℕ → Proc ι acts K) (C : Proc ι acts K) : Prop :=
  ∀ d a, SeqTendsTo (fun n => (Dn n d).w a) ((C d).w a)

variable {Dn : ℕ → Proc ι acts K} {C : Proc ι acts K}

/-- The leaf law is continuous in the weights (a product of converging factors).
Source: SE-18′(a) ("leaf probabilities polynomial in `C`"); mandate T4(c)
Kind: L -/
theorem leafLaw_tendsTo (h : ProcTendsTo Dn C) :
    (B : Tree Ω ι acts K) → ∀ ℓ, SeqTendsTo (fun n => leafLaw (Dn n) B ℓ) (leafLaw C B ℓ)
  | .leaf _ _, _ => by simp only [leafLaw_leaf]; exact SeqTendsTo.const 1
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLaw_chance]
      exact (SeqTendsTo.const (β.w i)).mul (leafLaw_tendsTo h (child i) ℓ)
  | .decision d child, ⟨a, ℓ⟩ => by
      simp only [leafLaw_decision]
      exact (h d a).mul (leafLaw_tendsTo h (child a) ℓ)

/-- `ν` is continuous in the weights. Source: mandate T4(c). Kind: L -/
theorem nu_tendsTo (h : ProcTendsTo Dn C) (B : Tree Ω ι acts K) (X : Finset Ω) :
    SeqTendsTo (fun n => nu (Dn n) B X) (nu C B X) := by
  simp only [nu, mass]
  exact SeqTendsTo.sum _ _ _ fun ℓ _ => leafLaw_tendsTo h B ℓ

/-- `paySum` is continuous in the weights. Source: mandate T4(c). Kind: L -/
theorem paySum_tendsTo (h : ProcTendsTo Dn C) (B : Tree Ω ι acts K) (X : Finset Ω) :
    SeqTendsTo (fun n => paySum (Dn n) B X) (paySum C B X) := by
  simp only [paySum]
  exact SeqTendsTo.sum _ _ _ fun ℓ _ => (leafLaw_tendsTo h B ℓ).mul (SeqTendsTo.const _)

/-- `condExp` is continuous in the weights where the limit mass is positive.
Source: SE-18′(a) ("denominators bounded away from `0`"); mandate T4(c)
Kind: L -/
theorem condExp_tendsTo (h : ProcTendsTo Dn C) (B : Tree Ω ι acts K) (X : Finset Ω)
    (hpos : 0 < nu C B X) :
    SeqTendsTo (fun n => condExp (Dn n) B X) (condExp C B X) := by
  simp only [condExp]
  exact (paySum_tendsTo h B X).div (nu_tendsTo h B X) hpos.ne'

/-- The trembles of a convergent sequence at vanishing `ε_n` converge to the limit procedure.
Source: mandate T4(e) ("`C'n` … converges to `C` because `ε n → 0`")
Kind: L -/
theorem tremble_tendsTo (Cn : ℕ → Proc ι acts K) (ε : ℕ → K) (hε : ∀ n, 0 ≤ ε n ∧ ε n ≤ 1)
    (hε0 : SeqTendsTo ε 0) (hCn : ProcTendsTo Cn C) :
    ProcTendsTo (fun n => tremble (Cn n) (ε n) (hε n).1 (hε n).2) C := by
  intro d a
  have := (((SeqTendsTo.const (1 : K)).sub hε0).mul (hCn d a)).add
    (hε0.mul (SeqTendsTo.const ((Fintype.card (acts d) : K)⁻¹)))
  simpa [tremble_w] using this

end tree

end Cleanroom.Decision.DpCalibLimits
