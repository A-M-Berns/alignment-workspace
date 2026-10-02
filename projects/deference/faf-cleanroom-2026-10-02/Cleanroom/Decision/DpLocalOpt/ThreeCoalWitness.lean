import Cleanroom.Decision.DpLocalOpt.Coalition
import Cleanroom.Decision.DpLocalOpt.Trees
import Cleanroom.Decision.DpLocalOpt.AmdWitness

/-!
# `dp-local-opt`: HA-9′'s three-point strictness table on `threeCoal` (T10(c), repair round 1)

Proposition 13(i)'s "strictly, already for three points" clause (A39 / HA-9′): on the
chance-free three-point tree with payoffs `SSS:2, SSH:3, SHS:2, SHH:3, HSS:3, HSH:3, HHS:3,
HHH:4`, the conflict-free pure profiles are `{SSH, HSS, HHH}` for the singleton family,
`{HSS, HHH}` for `{{d₁,d₂},{d₃}}` and `{HHH}` for the grand coalition. What is shipped is the
strictness this table witnesses: `SSH` separates singletons from the intermediate family, `HSS`
separates the intermediate family from the grand coalition (`threeCoal_spectrum_strict`). Mixed
joint revisions are handled through the trilinear closed form `threeCoal_value`, not by a
vertex argument.
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

section proc3

variable (p₁ p₂ p₃ : ℚ) (h₁0 : 0 ≤ p₁) (h₁1 : p₁ ≤ 1) (h₂0 : 0 ≤ p₂) (h₂1 : p₂ ≤ 1)
  (h₃0 : 0 ≤ p₃) (h₃1 : p₃ ≤ 1)

/-- The three-point procedure `C(dᵢ) = (pᵢ, 1 − pᵢ)` (`pᵢ` the weight of `S = a`).
Source: none: infrastructure
Kind: D -/
def proc3 : Proc Pt3 (fun _ => Act2) ℚ
  | .d1 => FinDistr.act2 p₁ h₁0 h₁1
  | .d2 => FinDistr.act2 p₂ h₂0 h₂1
  | .d3 => FinDistr.act2 p₃ h₃0 h₃1

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem proc3_d1 : proc3 p₁ p₂ p₃ h₁0 h₁1 h₂0 h₂1 h₃0 h₃1 .d1 = FinDistr.act2 p₁ h₁0 h₁1 :=
  rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem proc3_d2 : proc3 p₁ p₂ p₃ h₁0 h₁1 h₂0 h₂1 h₃0 h₃1 .d2 = FinDistr.act2 p₂ h₂0 h₂1 :=
  rfl

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem proc3_d3 : proc3 p₁ p₂ p₃ h₁0 h₁1 h₂0 h₂1 h₃0 h₃1 .d3 = FinDistr.act2 p₃ h₃0 h₃1 :=
  rfl

/-- Every three-point procedure on `Act2` is a `proc3`.
Source: none: infrastructure
Kind: L -/
theorem Proc.pt3_eq_proc3 (C : Proc Pt3 (fun _ => Act2) ℚ) :
    C = proc3 ((C .d1).w .a) ((C .d2).w .a) ((C .d3).w .a) ((C .d1).nonneg .a)
      ((C .d1).w_le_one .a) ((C .d2).nonneg .a) ((C .d2).w_le_one .a) ((C .d3).nonneg .a)
      ((C .d3).w_le_one .a) := by
  funext d; cases d
  · exact FinDistr.eq_act2 (C .d1)
  · exact FinDistr.eq_act2 (C .d2)
  · exact FinDistr.eq_act2 (C .d3)

/-- `V_{threeCoal}(p₁, p₂, p₃)`: the trilinear form in the `S`-weights with HA-9′'s payoffs.
Source: `repair/harmony.md` HA-9′
Kind: P -/
theorem threeCoal_value :
    value (proc3 p₁ p₂ p₃ h₁0 h₁1 h₂0 h₂1 h₃0 h₃1) threeCoal =
      p₁ * p₂ * p₃ * 2 + p₁ * p₂ * (1 - p₃) * 3 + p₁ * (1 - p₂) * p₃ * 2 +
        p₁ * (1 - p₂) * (1 - p₃) * 3 + (1 - p₁) * p₂ * p₃ * 3 + (1 - p₁) * p₂ * (1 - p₃) * 3 +
        (1 - p₁) * (1 - p₂) * p₃ * 3 + (1 - p₁) * (1 - p₂) * (1 - p₃) * 4 := by
  simp only [threeCoal, value_decision, value_leaf, Act2.sum_univ, proc3_d1, proc3_d2, proc3_d3,
    FinDistr.act2_a, FinDistr.act2_b, coalPay]
  ring

/-- Deviating `proc3` at `d1`. Source: none: infrastructure. Kind: L -/
theorem proc3_deviate_d1 (r : ℚ) (r0 : 0 ≤ r) (r1 : r ≤ 1) :
    (proc3 p₁ p₂ p₃ h₁0 h₁1 h₂0 h₂1 h₃0 h₃1).deviate .d1 (FinDistr.act2 r r0 r1) =
      proc3 r p₂ p₃ r0 r1 h₂0 h₂1 h₃0 h₃1 := by
  funext d; cases d <;> simp [Proc.deviate, proc3]

/-- Deviating `proc3` at `d2`. Source: none: infrastructure. Kind: L -/
theorem proc3_deviate_d2 (r : ℚ) (r0 : 0 ≤ r) (r1 : r ≤ 1) :
    (proc3 p₁ p₂ p₃ h₁0 h₁1 h₂0 h₂1 h₃0 h₃1).deviate .d2 (FinDistr.act2 r r0 r1) =
      proc3 p₁ r p₃ h₁0 h₁1 r0 r1 h₃0 h₃1 := by
  funext d; cases d <;> simp [Proc.deviate, proc3]

/-- Deviating `proc3` at `d3`. Source: none: infrastructure. Kind: L -/
theorem proc3_deviate_d3 (r : ℚ) (r0 : 0 ≤ r) (r1 : r ≤ 1) :
    (proc3 p₁ p₂ p₃ h₁0 h₁1 h₂0 h₂1 h₃0 h₃1).deviate .d3 (FinDistr.act2 r r0 r1) =
      proc3 p₁ p₂ r h₁0 h₁1 h₂0 h₂1 r0 r1 := by
  funext d; cases d <;> simp [Proc.deviate, proc3]

/-- Every point of `threeCoal` is queried.
Source: none: infrastructure
Kind: L -/
theorem threeCoal_queried : queried threeCoal = Finset.univ := by
  ext d; cases d <;> simp [threeCoal, queried]

end proc3

section table

/-- The singleton family on `threeCoal`.
Source: A39 ("singletons")
Kind: D -/
def singletons3 : Set (Finset Pt3) := (fun d => ({d} : Finset Pt3)) '' (↑(queried threeCoal) : Set Pt3)

/-- The intermediate family `{{d₁,d₂},{d₃}}`.
Source: A39; `repair/harmony.md` HA-9′
Kind: D -/
def mid3 : Set (Finset Pt3) := {{.d1, .d2}, {.d3}}

/-- `SSH` (`proc3 1 1 0`) is mixed-coherent at every point, hence conflict-free for the singleton
family.
Source: `repair/harmony.md` HA-9′ (singletons `{SSH, HSS, HHH}`)
Kind: N+ -/
theorem threeCoal_SSH_singletons :
    ConflictFree (proc3 1 1 0 zero_le_one le_rfl zero_le_one le_rfl le_rfl zero_le_one)
      threeCoal singletons3 := by
  rw [singletons3, conflictFree_singletons_iff]
  intro d _
  unfold CoherentAt
  intro m
  rw [FinDistr.eq_act2 m]
  cases d
  · rw [proc3_deviate_d1, threeCoal_value, threeCoal_value]; nlinarith [m.nonneg .a, m.w_le_one .a]
  · rw [proc3_deviate_d2, threeCoal_value, threeCoal_value]; nlinarith [m.nonneg .a, m.w_le_one .a]
  · rw [proc3_deviate_d3, threeCoal_value, threeCoal_value]; nlinarith [m.nonneg .a, m.w_le_one .a]

/-- `SSH` is not conflict-free for `{{d₁,d₂},{d₃}}`: the joint revision of `d₁, d₂` to `H, H`
gives `HHH = 4 > 3`.
Source: `repair/harmony.md` HA-9′ (`{{d₁,d₂},{d₃}}`: `{HSS, HHH}`)
Kind: N+ -/
theorem threeCoal_SSH_not_mid :
    ¬ ConflictFree (proc3 1 1 0 zero_le_one le_rfl zero_le_one le_rfl le_rfl zero_le_one)
      threeCoal mid3 := by
  rw [conflictFree_iff_coalition_nash']
  intro h
  have := h {.d1, .d2} (by simp [mid3])
    (proc3 0 0 0 le_rfl zero_le_one le_rfl zero_le_one le_rfl zero_le_one)
    (fun d hd => by cases d <;> simp_all [proc3])
  rw [threeCoal_value, threeCoal_value] at this
  norm_num at this

/-- `HSS` (`proc3 0 1 1`) is conflict-free for `{{d₁,d₂},{d₃}}`: with `d₃ = S` every `(d₁,d₂)`
revision is worth `3 − p₁ ≤ 3`, and with `(d₁,d₂) = (H,S)` every `d₃` revision is worth `3`.
Source: `repair/harmony.md` HA-9′
Kind: N+ -/
theorem threeCoal_HSS_mid :
    ConflictFree (proc3 0 1 1 le_rfl zero_le_one zero_le_one le_rfl zero_le_one le_rfl)
      threeCoal mid3 := by
  rw [conflictFree_iff_coalition_nash']
  intro D hD C' hC'
  rw [Proc.pt3_eq_proc3 C', threeCoal_value, threeCoal_value]
  have h10 := (C' .d1).nonneg .a
  have h11 := (C' .d1).w_le_one .a
  have h20 := (C' .d2).nonneg .a
  have h21 := (C' .d2).w_le_one .a
  have h30 := (C' .d3).nonneg .a
  have h31 := (C' .d3).w_le_one .a
  rcases hD with rfl | rfl
  · have e3 : (C' .d3).w .a = 1 := by
      have := hC' .d3 (by decide)
      rw [this]; rfl
    rw [e3]; nlinarith
  · have e1 : (C' .d1).w .a = 0 := by
      have := hC' .d1 (by decide)
      rw [this]; rfl
    have e2 : (C' .d2).w .a = 1 := by
      have := hC' .d2 (by decide)
      rw [this]; rfl
    rw [e1, e2]; nlinarith

/-- `HSS` is not optimal (`HHH = 4 > 3`), so not conflict-free for the grand coalition.
Source: `repair/harmony.md` HA-9′ (grand: `{HHH}`)
Kind: N+ -/
theorem threeCoal_HSS_not_grand :
    ¬ ConflictFree (proc3 0 1 1 le_rfl zero_le_one zero_le_one le_rfl zero_le_one le_rfl)
      threeCoal {queried threeCoal} := by
  rw [conflictFree_trivial_iff']
  intro h
  have := h (proc3 0 0 0 le_rfl zero_le_one le_rfl zero_le_one le_rfl zero_le_one)
  rw [threeCoal_value, threeCoal_value] at this
  norm_num at this

/-- `HHH` is optimal (`V ≤ 4` for every procedure), so conflict-free for every family.
Source: `repair/harmony.md` HA-9′
Kind: N+ -/
theorem threeCoal_HHH_optimal :
    IsOptimal (proc3 0 0 0 le_rfl zero_le_one le_rfl zero_le_one le_rfl zero_le_one) threeCoal := by
  intro C'
  rw [Proc.pt3_eq_proc3 C', threeCoal_value, threeCoal_value]
  have h10 := (C' .d1).nonneg .a
  have h11 := (C' .d1).w_le_one .a
  have h20 := (C' .d2).nonneg .a
  have h21 := (C' .d2).w_le_one .a
  have h30 := (C' .d3).nonneg .a
  have h31 := (C' .d3).w_le_one .a
  have h1' : 0 ≤ 1 - (C' .d1).w .a := by linarith
  have h2' : 0 ≤ 1 - (C' .d2).w .a := by linarith
  have h3' : 0 ≤ 1 - (C' .d3).w .a := by linarith
  nlinarith [mul_nonneg (mul_nonneg h10 h20) h30, mul_nonneg (mul_nonneg h10 h20) h3',
    mul_nonneg (mul_nonneg h10 h2') h30, mul_nonneg (mul_nonneg h10 h2') h3',
    mul_nonneg (mul_nonneg h1' h20) h30, mul_nonneg (mul_nonneg h1' h20) h3',
    mul_nonneg (mul_nonneg h1' h2') h30]

/-- **T10(c) — Proposition 13(i)'s spectrum is strict on three points (HA-9′'s table)**: `SSH` is
conflict-free for the singleton family but not for `{{d₁,d₂},{d₃}}`; `HSS` is conflict-free for
`{{d₁,d₂},{d₃}}` but not for the grand coalition; `HHH` is optimal. So the three families of
`conflictFree_antitone`'s order are pairwise separated.
Source: A39 ("strictly, already for three points"); `repair/harmony.md` HA-9′ (the table
`{SSH, HSS, HHH} ⊋ {HSS, HHH} ⊋ {HHH}`); mandate T10(c)
Kind: N+
Fidelity: exact (the strictness the table witnesses; the full membership iff for the eight
profiles is not stated)
Hyps: (a) all -/
theorem threeCoal_spectrum_strict :
    (ConflictFree (proc3 1 1 0 zero_le_one le_rfl zero_le_one le_rfl le_rfl zero_le_one)
        threeCoal singletons3 ∧
      ¬ ConflictFree (proc3 1 1 0 zero_le_one le_rfl zero_le_one le_rfl le_rfl zero_le_one)
        threeCoal mid3) ∧
    (ConflictFree (proc3 0 1 1 le_rfl zero_le_one zero_le_one le_rfl zero_le_one le_rfl)
        threeCoal mid3 ∧
      ¬ ConflictFree (proc3 0 1 1 le_rfl zero_le_one zero_le_one le_rfl zero_le_one le_rfl)
        threeCoal {queried threeCoal}) ∧
    ConflictFree (proc3 0 0 0 le_rfl zero_le_one le_rfl zero_le_one le_rfl zero_le_one)
      threeCoal {queried threeCoal} :=
  ⟨⟨threeCoal_SSH_singletons, threeCoal_SSH_not_mid⟩,
    ⟨threeCoal_HSS_mid, threeCoal_HSS_not_grand⟩,
    (conflictFree_trivial_iff' _ _).mpr threeCoal_HHH_optimal⟩

end table

end Cleanroom.Decision.DpLocalOpt
