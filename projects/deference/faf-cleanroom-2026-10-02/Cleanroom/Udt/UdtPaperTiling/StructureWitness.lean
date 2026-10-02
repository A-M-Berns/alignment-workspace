import Cleanroom.Udt.UdtPaperTiling.Structure
import Cleanroom.Udt.UdtPaperTiling.ElimOrder
import Cleanroom.Udt.UdtPaperTiling.Vingean
import Cleanroom.Udt.UdtPaperTiling.Tables

/-!
# `udt-paper-tiling` · StructureWitness: Paul's race conditions, and a fourth (T1(c),
bli-slides-009)

Each of Paul's race conditions violates one hypothesis of `CausalStructure`, and in each the order
in which `elim` runs the self-modifications changes the result — so without the hypothesis the
paper's "limit of repeated `elim`" is not well defined (`main.tex` 97's footnote half-admits this).
A fourth order-dependence (`Chain`, below) survives all three hypotheses.

* **Disagreement** (`Disagree`): two observations of the same rank each carry a self-modification
  that forces the third observation differently (`m₁` forces `x`, `m₂` forces `y`). No causal
  structure exists (`no_disagree` fails), and the two elimination orders give effective policies
  that differ at the forced point.
* **A two-cycle** (`Cycle`): `m₁` at `o` forces `y` at `ō`, `m₂` at `ō` forces `y` at `o`. No rank
  can satisfy `rank_lt` in both directions, and the two orders give `(x, y)` and `(y, x)`.
* **A modification at a null-mass observation** still rewrites: `effCausal_fires_at_null` in
  `Structure.lean` (the general statement: `eff` is a function of the policy alone).
* **A chain** (`Chain`; repair round 2, from the adversarial audit's B1 probe
  `ElimOrderDependent`, with the fidelity audit's N-9 probe `UnsortedOrder` making the same
  point): `m₁ ∈ 𝒜_{X1}` forces a non-modifying action at `X2`, `m₂ ∈ 𝒜_{X2}` forces one at `X3`,
  the rank `X1 < X2 < X3` is a **valid** causal structure (and Limited Self-Modification holds),
  and for `π = (m₁, m₂, a)` the rank-sorted elimination overwrites `m₂` before it can fire
  (`(a, a, a) = effCausal π`) while the reverse elimination lets `m₂` fire first (`(a, a, b)`).
  Both are complete, repeat-free "repeated applications of `elim`" ending at non-modifying
  policies, and they differ. So the three hypotheses make the paper's limit unique only among
  rank-compatible orders (`elimSeq_eq_effCausal`); the paper's "uniquely defined" needs the
  elimination order as a fourth clause, which `effCausal` fixes by definition.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30; repair 2026-10-01).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

namespace Disagree

/-- Actions `x = 0`, `y = 1`, `m₁ = 2`, `m₂ = 3`; `𝒜_{X1} = {x, m₁}`, `𝒜_{X2} = {x, m₂}`,
`𝒜_{X3} = {x, y}`; `m₁` forces `x` at `X3`, `m₂` forces `y` at `X3`.
Source: bli-slides-009 (b) ("simple race conditions: two modifications of the same entry")
Kind: D
Fidelity: n/a -/
def S : PaperStructure threeTables (Fin 4) where
  Aof := fun T => if T = X1 then {0, 2} else if T = X2 then {0, 3} else {0, 1}
  selfMod := {2, 3}
  twin := fun a => if a = 2 ∨ a = 3 then 0 else a
  twin_nonMod := by decide
  twin_typed := by
    intro a T ha
    by_cases h1 : T = X1
    · simp only [h1, if_true] at ha ⊢; fin_cases a <;> simp_all
    · by_cases h2 : T = X2
      · simp only [h1, h2, if_true, if_false] at ha ⊢; fin_cases a <;> simp_all
      · simp only [h1, h2, if_false] at ha ⊢; fin_cases a <;> simp_all
  twin_id := by intro a ha; fin_cases a <;> simp_all
  mod := fun a T => if T = X3 then (if a = 2 then some 0 else if a = 3 then some 1 else none) else none
  mod_nonMod_none := by intro a ha T; fin_cases a <;> simp_all

/-- **No causal structure exists**: `m₁` and `m₂` disagree on `X3`.
Source: bli-slides-009 (b)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem no_causalStructure : ∀ _ : S.CausalStructure, False := by
  intro C
  have := C.no_disagree 2 3 X3 0 1 (by simp [S]) (by simp [S])
  exact absurd this (by decide)

/-- The policy `(m₁, m₂, y)`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def π : Policy threeTables (Fin 4) := fun T => if T = X1 then 2 else if T = X2 then 3 else 1

/-- **The two elimination orders disagree**: eliminating `m₁` then `m₂` leaves `y` at `X3`;
eliminating `m₂` then `m₁` leaves `x`.
Source: bli-slides-009 (b)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem orders_differ :
    S.elim (S.elim π X1 2) X2 3 X3 = 1 ∧ S.elim (S.elim π X2 3) X1 2 X3 = 0 := by
  constructor
  · rw [S.elim_forced _ 3 1 X3_ne_X2 (by simp [S])]
  · rw [S.elim_forced _ 2 0 X3_ne_X1 (by simp [S])]

end Disagree

namespace Cycle

/-- `Rec ≠ Ask`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mRec_ne_mAsk : mRec ≠ mAsk := mAsk_ne_mRec.symm

/-- Actions `x = 0`, `y = 1`, `m₁ = 2`, `m₂ = 3`; `𝒜_o = {x, y, m₁}`, `𝒜_ō = {x, y, m₂}`;
`m₁` (at `o`) forces `y` at `ō`, `m₂` (at `ō`) forces `y` at `o`.
Source: bli-slides-009 (c) ("tangled race conditions"); `main.tex` 97 footnote ("infinite loops")
Kind: D
Fidelity: n/a -/
def S : PaperStructure twoTables (Fin 4) where
  Aof := fun T => if T = T1 then {0, 1, 2} else {0, 1, 3}
  selfMod := {2, 3}
  twin := fun a => if a = 2 ∨ a = 3 then 0 else a
  twin_nonMod := by decide
  twin_typed := by
    intro a T ha
    by_cases h1 : T = T1
    · simp only [h1, if_true] at ha ⊢; fin_cases a <;> simp_all
    · simp only [h1, if_false] at ha ⊢; fin_cases a <;> simp_all
  twin_id := by intro a ha; fin_cases a <;> simp_all
  mod := fun a T => if a = 2 ∧ T = T2 then some 1 else if a = 3 ∧ T = T1 then some 1 else none
  mod_nonMod_none := by intro a ha T; fin_cases a <;> simp_all

/-- **No causal structure exists**: a rank would have to satisfy `rank o < rank ō < rank o`.
Source: bli-slides-009 (c)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem no_causalStructure : ∀ _ : S.CausalStructure, False := by
  intro C
  have h1 := C.rank_lt 2 T1 T2 1 (by simp [S]) (by simp [S, mRec_ne_mAsk])
  have h2 := C.rank_lt 3 T2 T1 1 (by simp [S, mRec_ne_mAsk]) (by simp [S])
  exact lt_irrefl _ (lt_trans h1 h2)

/-- The policy `(m₁, m₂)`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def π : Policy twoTables (Fin 4) := fun T => if T = T1 then 2 else 3

/-- **The two elimination orders disagree**: `m₁` first gives `(x, y)`, `m₂` first gives `(y, x)`
(each eliminated modification overwrites the other's self-modifying point with a non-modifying
action before it can fire).
Source: bli-slides-009 (c)
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem orders_differ :
    (S.elim π T1 2 T1 = 0 ∧ S.elim π T1 2 T2 = 1) ∧ (S.elim π T2 3 T1 = 1 ∧ S.elim π T2 3 T2 = 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [S.elim_self]; simp [S]
  · rw [S.elim_forced _ 2 1 T2_ne_T1 (by simp [S, mRec_ne_mAsk])]
  · rw [S.elim_forced _ 3 1 T1_ne_T2 (by simp [S])]
  · rw [S.elim_self]; simp [S]

end Cycle

namespace Chain

attribute [local simp] mAsk_ne_mRec mRec_ne_mAsk' mAsk_ne_mZero mZero_ne_mAsk mRec_ne_mZero
  mZero_ne_mRec X1_ne_X2 X1_ne_X3 X2_ne_X3 X2_ne_X1 X3_ne_X1 X3_ne_X2

/-- Actions `a = 0`, `b = 1`, `m₁ = 2`, `m₂ = 3`; `𝒜_{X1} = {a, m₁}`, `𝒜_{X2} = {a, m₂}`,
`𝒜_{X3} = {a, b}`; `m₁` forces `a` at `X2`, `m₂` forces `b` at `X3` — a modification whose target
is itself a self-modifying point.
Source: audit r2 adversarial probe `ElimOrderDependent` (B1); `main.tex` 95–97
Kind: D
Fidelity: n/a -/
def S : PaperStructure threeTables (Fin 4) where
  Aof := fun T => if T = X1 then {0, 2} else if T = X2 then {0, 3} else {0, 1}
  selfMod := {2, 3}
  twin := fun a => if a = 2 ∨ a = 3 then 0 else a
  twin_nonMod := by decide
  twin_typed := by
    intro a T ha
    rcases eq_X1_or_X2_or_X3 T with rfl | rfl | rfl <;> fin_cases a <;> simp_all
  twin_id := by intro a ha; fin_cases a <;> simp_all
  mod := fun a T => if a = 2 ∧ T = X2 then some 0 else if a = 3 ∧ T = X3 then some 1 else none
  mod_nonMod_none := by intro a ha T; fin_cases a <;> simp_all

/-- **A valid causal structure on the chain**: rank `X1 = 0`, `X2 = 1`, `X3 = 2`; all three
hypotheses hold (modifications target strictly later observations, no disagreement, forced
actions non-modifying and well-typed).
Source: audit r2 adversarial probe `ElimOrderDependent` (B1)
Kind: D
Fidelity: n/a -/
def C : S.CausalStructure where
  rank := fun T => if T = X1 then 0 else if T = X2 then 1 else 2
  rank_lt := by
    intro a o o' a' ha hm
    rcases eq_X1_or_X2_or_X3 o with rfl | rfl | rfl <;>
      rcases eq_X1_or_X2_or_X3 o' with rfl | rfl | rfl <;>
      fin_cases a <;> simp [S] at ha hm ⊢
  no_disagree := by
    intro a b o' x y hx hy
    rcases eq_X1_or_X2_or_X3 o' with rfl | rfl | rfl <;> fin_cases a <;> fin_cases b <;>
      simp [S] at hx hy <;> omega
  mod_nonMod := by
    intro a o' a' h
    rcases eq_X1_or_X2_or_X3 o' with rfl | rfl | rfl <;> fin_cases a <;> simp [S] at h ⊢ <;> omega
  mod_typed := by
    intro a o' a' h
    rcases eq_X1_or_X2_or_X3 o' with rfl | rfl | rfl <;> fin_cases a <;> simp [S] at h ⊢ <;>
      (rcases h with rfl <;> simp)

/-- The chain also satisfies Limited Self-Modification (`ob m₁ = X2`, `ac m₁ = a`; `ob m₂ = X3`,
`ac m₂ = b`; neither modifies its own point): the order-dependence below survives LSM too.
Source: audit r2 adversarial probe `ElimOrderDependent` (B1); `main.tex` 205–215
Kind: D
Fidelity: n/a -/
def L : LimitedSelfMod S where
  ob := fun a => if a = 2 then X2 else X3
  ac := fun a => if a = 2 then 0 else 1
  mod_eq := by
    intro a ha o
    rcases eq_X1_or_X2_or_X3 o with rfl | rfl | rfl <;> fin_cases a <;> simp_all [S]
  ac_nonMod := by intro a ha; fin_cases a <;> simp_all [S]
  not_self := by intro a ha; fin_cases a <;> simp_all [S]

/-- The policy `(m₁, m₂, a)`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def π : Policy threeTables (Fin 4) := fun T => if T = X1 then 2 else if T = X2 then 3 else 0

/-- `π X1 = m₁`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma π_X1 : π X1 = 2 := by simp [π]
/-- `π X2 = m₂`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma π_X2 : π X2 = 3 := by simp [π]
/-- `π X3 = a`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma π_X3 : π X3 = 0 := by simp [π]

/-- `π` is well-typed. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma π_wellTyped : S.WellTyped π := by
  intro T
  rcases eq_X1_or_X2_or_X3 T with rfl | rfl | rfl <;> simp [S, π]

/-- The result of the rank-sorted elimination: `(a, a, a)`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def σ_sorted : Policy threeTables (Fin 4) := fun _ => 0

/-- The result of the reverse elimination: `(a, a, b)`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def σ_rev : Policy threeTables (Fin 4) := fun T => if T = X3 then 1 else 0

/-- Step 1 of the sorted order: `elim` at `X1` yields `(a, a, a)` (`m₁` fires and overwrites `X2`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma step_X1_π : S.elimStep π X1 = σ_sorted := by
  have h : S.elimStep π X1 = S.elim π X1 2 := by
    unfold PaperStructure.elimStep; rw [π_X1]; simp [S]
  rw [h]
  apply policy_ext
  · rw [S.elim_self]; simp [S, σ_sorted]
  · rw [S.elim_forced _ 2 0 X2_ne_X1 (by simp [S])]; simp [σ_sorted]
  · rw [S.elim_other _ 2 X3_ne_X1 (by simp [S]), π_X3]; simp [σ_sorted]

/-- On the non-modifying `(a, a, a)` every step is a no-op.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma step_noop_sorted (T : ↥threeTables) : S.elimStep σ_sorted T = σ_sorted := by
  unfold PaperStructure.elimStep; simp [S, σ_sorted]

/-- **The rank-sorted elimination** `[X1, X2, X3]` gives `(a, a, a)`, as `elimSeq_eq_effCausal`
says.
Source: audit r2 adversarial probe `ElimOrderDependent` (B1)
Kind: P
Fidelity: n/a -/
theorem sorted_result : S.elimSeq π [X1, X2, X3] = σ_sorted := by
  simp only [PaperStructure.elimSeq, List.foldl_cons, List.foldl_nil]
  rw [step_X1_π, step_noop_sorted, step_noop_sorted]

/-- The intermediate policy after `elim` at `X2` in the reverse order: `(m₁, a, b)`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def σ_mid : Policy threeTables (Fin 4) := fun T => if T = X1 then 2 else if T = X2 then 0 else 1

/-- `elim` at `X3` is a no-op on `π` (`π X3 = a` is non-modifying).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma step_X3_π : S.elimStep π X3 = π := by
  unfold PaperStructure.elimStep; rw [π_X3]; simp [S]

/-- `elim` at `X2` on `π`: `m₂` fires and forces `b` at `X3`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma step_X2_π : S.elimStep π X2 = σ_mid := by
  have h : S.elimStep π X2 = S.elim π X2 3 := by
    unfold PaperStructure.elimStep; rw [π_X2]; simp [S]
  rw [h]
  apply policy_ext
  · rw [S.elim_other _ 3 X1_ne_X2 (by simp [S]), π_X1]; simp [σ_mid]
  · rw [S.elim_self]; simp [S, σ_mid]
  · rw [S.elim_forced _ 3 1 X3_ne_X2 (by simp [S])]; simp [σ_mid]

/-- `elim` at `X1` on `(m₁, a, b)`: `m₁` fires; its overwrite of `X2` cannot undo the
modification `m₂` already made at `X3`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma step_X1_mid : S.elimStep σ_mid X1 = σ_rev := by
  have h : S.elimStep σ_mid X1 = S.elim σ_mid X1 2 := by
    unfold PaperStructure.elimStep; simp [S, σ_mid]
  rw [h]
  apply policy_ext
  · rw [S.elim_self]; simp [S, σ_rev]
  · rw [S.elim_forced _ 2 0 X2_ne_X1 (by simp [S])]; simp [σ_rev]
  · rw [S.elim_other _ 2 X3_ne_X1 (by simp [S])]; simp [σ_mid, σ_rev]

/-- **The reverse elimination** `[X3, X2, X1]` gives `(a, a, b)`: `m₂` fires before `m₁`
overrides it.
Source: audit r2 adversarial probe `ElimOrderDependent` (B1)
Kind: P
Fidelity: n/a -/
theorem reverse_result : S.elimSeq π [X3, X2, X1] = σ_rev := by
  simp only [PaperStructure.elimSeq, List.foldl_cons, List.foldl_nil]
  rw [step_X3_π, step_X2_π, step_X1_mid]

/-- Both enumerations are complete and repeat-free; only the first is rank-sorted.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem both_complete :
    ([X1, X2, X3] : List ↥threeTables).Nodup ∧ (∀ o, o ∈ ([X1, X2, X3] : List ↥threeTables)) ∧
    ([X3, X2, X1] : List ↥threeTables).Nodup ∧ (∀ o, o ∈ ([X3, X2, X1] : List ↥threeTables)) := by
  refine ⟨by simp, fun o => ?_, by simp, fun o => ?_⟩ <;>
  · rcases eq_X1_or_X2_or_X3 o with rfl | rfl | rfl <;> simp

/-- **The paper's unordered limit is not unique under the causal structure** (the fourth race
condition): with a valid causal structure and Limited Self-Modification, two complete
eliminations of the same well-typed policy end at different non-modifying policies (`a` vs `b`
at `X3`); the rank-sorted one is `effCausal π`. So the three hypotheses make the limit unique
only among rank-compatible orders (`elimSeq_eq_effCausal`), and the paper's "uniquely defined"
(`main.tex` 97) needs "elimination follows the causal order" as a fourth clause — which
`effCausal` supplies by definition.
Source: audit r2 adversarial probe `ElimOrderDependent` (B1); `main.tex` 95–97; bli-slides-036;
bli-paper-062
Kind: N−
Fidelity: n/a (a refutation of the three hypotheses' sufficiency for the paper's assumption)
Hyps: (a) none -/
theorem limit_not_unique :
    Nonempty (LimitedSelfMod S) ∧ S.WellTyped π ∧
    S.elimSeq π [X1, X2, X3] X3 = 0 ∧ S.elimSeq π [X3, X2, X1] X3 = 1 ∧
    S.NonMod (S.elimSeq π [X1, X2, X3]) ∧ S.NonMod (S.elimSeq π [X3, X2, X1]) ∧
    S.elimSeq π [X1, X2, X3] = C.effCausal π := by
  refine ⟨⟨L⟩, π_wellTyped, by rw [sorted_result]; rfl, by rw [reverse_result]; simp [σ_rev], ?_, ?_, ?_⟩
  · rw [sorted_result]; intro T; simp [S, σ_sorted]
  · rw [reverse_result]; intro T; simp only [σ_rev, S]; split_ifs <;> decide
  · exact S.elimSeq_eq_effCausal C π π_wellTyped [X1, X2, X3] both_complete.1 both_complete.2.1
      (by simp [C])

end Chain

end Cleanroom.Udt.UdtPaperTiling
