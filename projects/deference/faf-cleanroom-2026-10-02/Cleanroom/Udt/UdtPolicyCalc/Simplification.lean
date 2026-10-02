import Cleanroom.Udt.UdtPolicyCalc.LocalGlobal
import Mathlib.Tactic.FieldSimp

/-!
# The unjustified "simplification" of the UDT rule: T13

[[core-argument-draft]] Step 4: "The UDT formula: `a* = argmax_a E[U | π(s) = a, π is optimal
elsewhere]`. For a coherent agent with a single policy, this simplifies to
`a* = argmax_a E[U | π(s) = a]`."

Objects: a prior `μ` over policies, a policy utility `U`, an optimal `π*`. The two sides:
`lhs U π* s a := U (π*[s ↦ a])` (the only precise reading of "`π(s) = a`, `π` optimal elsewhere"
the source supports; ATTRIBUTION-UNVETTED that this reading was intended) and
`rhs μ U s a := E_μ[U | π(s) = a]` with the C&T junk value `-1`.

* `rhs_argmax_ne_lhs_argmax` — the **refutation**: a two-situation witness where the argmaxes differ.
* `rhs_eq_lhs_of_concentrated` — the **sufficient condition** (the conditional law of `π` given
  `π(s) = a` is concentrated on `π*[s ↦ a]`); `rhs_delta_eq` / `rhs_delta_junk` — the point-mass
  form: equality at `a = π* s` only, junk `-1` everywhere else (T10(b)'s phenomenon again).
* `concentrated_witness` — the N+ witness for the condition.

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

namespace Simplification

open Finset

section General

variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

/-- The left side of Step 4: `E[U | π(s) = a, π optimal elsewhere]` read as `U (π*[s ↦ a])`.
Source: [[core-argument-draft]] lines 86–88 (udt-rep-2-004); reading ATTRIBUTION-UNVETTED
Kind: D
Fidelity: variant: the one precise reading the source supports
Hyps: n/a -/
def lhs (U : Policy S A → ℝ) (π : Policy S A) (s : S) (a : A) : ℝ := U (Function.update π s a)

/-- The right side of Step 4: `E_μ[U | π(s) = a]` under a prior `μ` over policies, junk `-1`.
Source: [[core-argument-draft]] line 90; [[notation]] §3.2 (udt-rep-2-004, 090)
Kind: D
Fidelity: exact
Hyps: n/a -/
def rhs (μ : FinDist (Policy S A)) (U : Policy S A → ℝ) (s : S) (a : A) : ℝ :=
  condExpJunk μ.w U (event fun π => π s = a) (-1)

/-- **T13, the sufficient condition (udt-rep-2-004).** If `μ` restricted to `{π s = a}` is
concentrated on `π*[s ↦ a]` (every other policy with `π s = a` has weight `0`) and that policy
has positive weight, then `rhs μ U s a = lhs U π* s a`.
Source: [[core-argument-draft]] Step 4 (udt-rep-2-004: "the prior is a point mass or the conditional law is concentrated")
Kind: P
Fidelity: exact
Hyps: (a) the concentration and positivity hypotheses (explicit) -/
theorem rhs_eq_lhs_of_concentrated (μ : FinDist (Policy S A)) (U : Policy S A → ℝ)
    (π₀ : Policy S A) (s : S) (a : A)
    (hconc : ∀ π, π s = a → π ≠ Function.update π₀ s a → μ.w π = 0)
    (hpos : 0 < μ.w (Function.update π₀ s a)) : rhs μ U s a = lhs U π₀ s a := by
  have hmem : Function.update π₀ s a ∈ event (fun π : Policy S A => π s = a) := by simp
  have hmass : mass μ.w (event fun π : Policy S A => π s = a) = μ.w (Function.update π₀ s a) := by
    unfold mass
    rw [Finset.sum_eq_single (Function.update π₀ s a)]
    · intro π hπ hne
      rw [mem_event] at hπ
      exact hconc π hπ hne
    · intro h
      exact absurd hmem h
  have hnum : ∑ π ∈ event (fun π : Policy S A => π s = a), μ.w π * U π =
      μ.w (Function.update π₀ s a) * U (Function.update π₀ s a) := by
    rw [Finset.sum_eq_single (Function.update π₀ s a)]
    · intro π hπ hne
      rw [mem_event] at hπ
      rw [hconc π hπ hne, zero_mul]
    · intro h
      exact absurd hmem h
  unfold rhs lhs
  rw [condExpJunk_of_pos (by rw [hmass]; exact hpos), hnum, hmass, mul_comm, mul_div_assoc,
    div_self hpos.ne', mul_one]

/-- **T13, point-mass form, the good case.** Under the point mass at `π*`, `rhs` at `a = π* s`
equals `lhs` (both are `U π*`).
Source: [[core-argument-draft]] Step 4 (udt-rep-2-004)
Kind: L
Fidelity: exact
Hyps: none -/
theorem rhs_delta_eq (U : Policy S A → ℝ) (π₀ : Policy S A) (s : S) :
    rhs (FinDist.delta π₀) U s (π₀ s) = lhs U π₀ s (π₀ s) := by
  apply rhs_eq_lhs_of_concentrated
  · intro π _ hne
    rw [Function.update_eq_self] at hne
    simp [hne]
  · rw [Function.update_eq_self]
    simp

/-- **T13, point-mass form, the junk case.** Under the point mass at `π*`, `rhs` at any `a ≠ π* s`
is the junk value `-1`: the "simplified" rule cannot even compare the alternatives.
Source: [[core-argument-draft]] Step 4 (udt-rep-2-004); [[communication-trust-translated]] line 269 (udt-rep-090)
Kind: P
Fidelity: exact
Hyps: (a) `a ≠ π* s` -/
theorem rhs_delta_junk (U : Policy S A → ℝ) (π₀ : Policy S A) (s : S) (a : A) (ha : a ≠ π₀ s) :
    rhs (FinDist.delta π₀) U s a = -1 := by
  apply condExpJunk_of_mass_eq_zero
  apply mass_eq_zero_of_forall
  intro π hπ
  rw [mem_event] at hπ
  have : π ≠ π₀ := by
    rintro rfl
    exact ha hπ.symm
  simp [this]

end General

/-! ### The refutation witness -/

/-- Supporting lemma `vec2_eq_iff`: equality of two-entry vectors is entrywise.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem vec2_eq_iff {α : Type} {a b c d : α} : (![a, b] : Fin 2 → α) = ![c, d] ↔ a = c ∧ b = d :=
  ⟨fun h => ⟨congrFun h 0, congrFun h 1⟩, by
    rintro ⟨rfl, rfl⟩
    rfl⟩

/-- `U (0,0) = 1`, `U (1,1) = 2`, `U (0,1) = U (1,0) = 0`: the optimal policy is `(1,1)`.
Source: mandate T13 (udt-rep-2-004's witness, made exact)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def U13 : Policy (Fin 2) (Fin 2) → ℝ := tbl 1 0 0 2

/-- The prior `μ (1,0) = 6/10`, `μ (0,0) = 3/10`, `μ (1,1) = μ (0,1) = 1/20`: most mass on
miscoordinating policies with `π 0 = 1`.
Source: mandate T13 (udt-rep-2-004's witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def μ13 : FinDist (Policy (Fin 2) (Fin 2)) where
  w := tbl (3 / 10) (1 / 20) (6 / 10) (1 / 20)
  nonneg := by
    rw [forall_policy2]
    simp only [tbl_00, tbl_01, tbl_10, tbl_11]
    norm_num
  sum_one := by
    rw [policy2_sum]
    simp only [tbl_00, tbl_01, tbl_10, tbl_11]
    norm_num

/-- Supporting lemma `U13_optimal` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem U13_optimal : IsOptimal U13 ![1, 1] := by
  rw [IsOptimal, forall_policy2]
  simp only [U13, tbl_00, tbl_01, tbl_10, tbl_11]
  norm_num

/-- Supporting lemma `lhs13` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem lhs13 : lhs U13 ![1, 1] 0 0 < lhs U13 ![1, 1] 0 1 := by
  simp only [lhs, update_vec2_zero, U13, tbl_01, tbl_11]
  norm_num

/-- Supporting lemma `rhs13_one` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem rhs13_one : rhs μ13 U13 0 1 = 2 / 13 := by
  unfold rhs
  have hpos : 0 < mass μ13.w (event fun π : Policy (Fin 2) (Fin 2) => π 0 = 1) := by
    rw [mass, Finset.sum_filter, policy2_sum]
    norm_num [μ13, tbl_00, tbl_01, tbl_10, tbl_11]
  rw [condExpJunk_of_pos hpos, mass, Finset.sum_filter, Finset.sum_filter, policy2_sum, policy2_sum]
  norm_num [μ13, U13, tbl_00, tbl_01, tbl_10, tbl_11]

/-- Supporting lemma `rhs13_zero` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem rhs13_zero : rhs μ13 U13 0 0 = 6 / 7 := by
  unfold rhs
  have hpos : 0 < mass μ13.w (event fun π : Policy (Fin 2) (Fin 2) => π 0 = 0) := by
    rw [mass, Finset.sum_filter, policy2_sum]
    norm_num [μ13, tbl_00, tbl_01, tbl_10, tbl_11]
  rw [condExpJunk_of_pos hpos, mass, Finset.sum_filter, Finset.sum_filter, policy2_sum, policy2_sum]
  norm_num [μ13, U13, tbl_00, tbl_01, tbl_10, tbl_11]

/-- **T13, the refutation (udt-rep-2-004; load-bearing 4).** "For a coherent agent with a single
policy, this simplifies to `a* = argmax_a E[U | π(s) = a]`" is false in general: with
`U (0,0) = 1`, `U (1,1) = 2`, `U (0,1) = U (1,0) = 0` (so `π* = (1,1)`) and the prior
`μ (1,0) = 6/10`, `μ (0,0) = 3/10`, `μ (1,1) = μ (0,1) = 1/20`, one has
`rhs 0 1 = 2/13 < rhs 0 0 = 6/7` while `lhs 0 1 = 2 > lhs 0 0 = 0`: the argmaxes differ. The
surviving neighbour is `rhs_eq_lhs_of_concentrated`.
Source: [[core-argument-draft]] lines 86–90 (udt-rep-2-004); the same identification in [[presentation-outline]] Part 5 and [[daniel-h-challenge]]
Kind: P
Fidelity: exact (refutation of the literal sentence under the `lhs` reading; ATTRIBUTION-UNVETTED)
Hyps: (a) none -/
theorem rhs_argmax_ne_lhs_argmax :
    IsOptimal U13 ![1, 1] ∧ IsStrictArgmax (lhs U13 ![1, 1] 0) 1 ∧
      IsStrictArgmax (rhs μ13 U13 0) 0 := by
  refine ⟨U13_optimal, ?_, ?_⟩
  · intro a ha
    rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h <;> subst h
    · exact lhs13
    · exact absurd rfl ha
  · intro a ha
    rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h <;> subst h
    · exact absurd rfl ha
    · rw [rhs13_one, rhs13_zero]
      norm_num

/-- **T13, N+ witness for the sufficient condition.** The prior `½δ_{(0,1)} + ½δ_{(1,1)}` is
supported exactly on `{π*[0 ↦ a] | a}` with positive weights, and `rhs = lhs` at `s = 0` for both
actions; two distinct policies, `U` non-constant.
Source: mandate T13 witness
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem concentrated_witness :
    (∀ a, rhs (FinDist.halfHalf ![0, 1] ![1, 1]) U13 0 a = lhs U13 ![1, 1] 0 a) ∧
      U13 ![0, 1] ≠ U13 ![1, 1] := by
  refine ⟨?_, by simp only [U13, tbl_01, tbl_11]; norm_num⟩
  intro a
  apply rhs_eq_lhs_of_concentrated
  · rw [forall_policy2]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h1 h2 <;>
      simp only [Matrix.cons_val_zero] at h1 <;> subst h1 <;>
      simp [FinDist.halfHalf, FinDist.bern_w, vec2_eq_iff] at h2 ⊢
  · rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h <;> subst h <;>
      norm_num [FinDist.halfHalf, FinDist.bern_w, vec2_eq_iff]

end Simplification

end

end Cleanroom.Udt.UdtPolicyCalc
