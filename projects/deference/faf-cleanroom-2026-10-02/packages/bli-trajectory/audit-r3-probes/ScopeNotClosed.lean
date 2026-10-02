import Cleanroom.Bli.BliTrajectory.TriState

/-!
# Audit r3 (fidelity) probe: `bli-found`'s faith scope at `(0, 1)` is not Boolean-closed

`Pinning.two_state_pinning_scope` ("two distinct tables are pinned") needs a family `Γ` closed
under `⋏` and `∼`. `bli-found`'s `FaithMarginal`/`E2x` quantify `φ` over `Sminus m m`, a
size-bounded set. At `(n, m) = (0, 1)` the bound is `sizeBound 1 = 4`: `atom 0` and `atom 1`
(token size `3`) are in scope, their conjunction (token size `8`) and negation (token size `6`)
are not. So the pinning theorem does not apply to `bli-found`'s predicates at `(0, 1)`, and
"with two distinct tables the converse holds" is a statement about Boolean-closed scopes.
Not imported by the library.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound

/-- `(natDigits4 5).length = 2` and `(natDigits4 6).length = 2`. -/
lemma natDigits4_five_six :
    (natDigits4 5).length = 2 ∧ (natDigits4 6).length = 2 := by
  constructor
  · rw [length_natDigits4_eq_log (by norm_num)]
    have : Nat.log 4 5 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    omega
  · rw [length_natDigits4_eq_log (by norm_num)]
    have : Nat.log 4 6 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    omega

/-- `sizeBound 1 = 4`. -/
lemma sizeBound_one : sizeBound 1 = 4 := by
  unfold sizeBound; norm_num

/-- `atomDay 1 = 0`. -/
lemma atomDay_one : atomDay 1 = 0 := by
  have h : Nat.unpair 1 = (0, 1) := by decide
  simp [atomDay, atomDayBase, cleanroomBaseTag, h]

/-- `triAtom' = atom 1` is in the scope at `(0, 1)`. -/
theorem triAtom'_mem_Sminus_one : triAtom' ∈ Sminus 1 1 := by
  rw [mem_Sminus]
  refine ⟨?_, fun a ha => ?_⟩
  · unfold SmallOn triAtom'
    rw [tokenSize_atom, sizeBound_one, natDigits4_five_six.2]; omega
  · simp only [triAtom', sentenceAtomCodes_atom, Finset.mem_singleton] at ha
    subst ha
    rw [atomDay_one]; omega

/-- **The scope at `(0, 1)` is not `⋏`-closed**: `cohAtom ⋏ triAtom' ∉ Sminus 1 1` although both
conjuncts are in it (`cohAtom_mem_Sminus`, `triAtom'_mem_Sminus_one`). -/
theorem and_not_mem_Sminus_one : cohAtom ⋏ triAtom' ∉ Sminus 1 1 := by
  rw [mem_Sminus]
  rintro ⟨h, -⟩
  unfold SmallOn at h
  rw [tokenSize_and, sizeBound_one] at h
  unfold cohAtom triAtom' at h
  rw [tokenSize_atom, tokenSize_atom, natDigits4_five_six.1, natDigits4_five_six.2] at h
  omega

/-- **Nor `∼`-closed**: `∼triAtom' ∉ Sminus 1 1`. -/
theorem neg_not_mem_Sminus_one : ∼triAtom' ∉ Sminus 1 1 := by
  rw [mem_Sminus]
  rintro ⟨h, -⟩
  unfold SmallOn at h
  rw [tokenSize_neg, sizeBound_one] at h
  unfold triAtom' at h
  rw [tokenSize_atom, natDigits4_five_six.2] at h
  omega

end Cleanroom.Bli.BliTrajectory
