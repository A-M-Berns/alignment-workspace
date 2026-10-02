import Cleanroom.Decision.DpCalibLimits.TwoRoute

/-!
# T15 — Not every Popper function is a ray limit

[[dp-calib-limits-mandate]] T15 (dp-sl-2-020, P07 Open 3).

`chanceTwin`: a fair coin, then in each branch a `d`-node with acts `a, b`, four leaves
`(H,a), (H,b), (T,a), (T,b)`, `O = ⊤`. For **every** ray `R` the limiting conditional of
`{(H,a)}` given `{(H,a), (T,a)}` is `½` when `w_a ≠ 0` (both leaves have polynomial `½ · w_a`)
and the junk `0` when `w_a = 0`; the Popper reading `popperLimitRay` is therefore `½` or `1`,
never `⅓` (`chanceTwin_popperLimitRay`). The conditional probability of a probability measure
with the `≡ 1` convention is a Popper function (`isPopper_ofMeasure`); the one with
`μ(H,a) = ⅓`, `μ(T,a) = ⅔` gives `p({(H,a)} | {(H,a),(T,a)}) = ⅓` (`twinPopper_third`). So the
universal reading of "every Popper function arises as a ray limit" is **refuted**
(`chanceTwin_refutes`); the surviving neighbour is T16's necessary chance-conditional
invariance (`PopperClass.lean`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Conditional probability of a measure as a Popper function -/

section ofMeasure

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The conditional probability of a probability measure, with the `≡ 1` convention on null
conditions. Source: Hájek 2003 p. 316 (the standard example of a Popper function); mandate T15
Kind: D -/
noncomputable def condOfMeasure (μ : FinDistr K Ω) (A B : Finset Ω) : K :=
  if 0 < probOf μ B then probOf μ (A ∩ B) / probOf μ B else 1

/-- Abnormality for `condOfMeasure` is nullity. Source: none: infrastructure. Kind: L -/
theorem abnormal_condOfMeasure_iff (μ : FinDistr K Ω) (B : Finset Ω) :
    Abnormal (condOfMeasure μ) B ↔ probOf μ B = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < probOf μ B := lt_of_le_of_ne (probOf_nonneg μ B) (Ne.symm hne)
    have := h ∅
    unfold condOfMeasure at this
    rw [if_pos hpos, Finset.empty_inter, probOf_empty, zero_div] at this
    exact zero_ne_one this
  · intro h A
    unfold condOfMeasure
    rw [if_neg (by rw [h]; exact lt_irrefl 0)]

/-- **The conditional probability of a probability measure with the `≡ 1` convention is a
Popper function.** Source: Hájek 2003 p. 316; mandate T15. Kind: P. Fidelity: exact -/
theorem isPopper_ofMeasure (μ : FinDistr K Ω) : IsPopper (condOfMeasure μ) where
  bounds A B := by
    unfold condOfMeasure
    split_ifs with h
    · exact ⟨div_nonneg (probOf_nonneg μ _) (probOf_nonneg μ _),
        div_le_one_of_le₀ (probOf_mono μ Finset.inter_subset_right) (probOf_nonneg μ _)⟩
    · exact ⟨zero_le_one, le_rfl⟩
  refl B := by
    unfold condOfMeasure
    split_ifs with h
    · rw [Finset.inter_self]; exact div_self h.ne'
    · rfl
  add A A' B hn hd := by
    have hpos : 0 < probOf μ B := by
      by_contra hc
      exact hn ((abnormal_condOfMeasure_iff μ B).mpr
        (le_antisymm (not_lt.mp hc) (probOf_nonneg μ B)))
    unfold condOfMeasure
    simp only [if_pos hpos]
    rw [Finset.union_inter_distrib_right, probOf_union μ
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hd)), add_div]
  mul A B C := by
    unfold condOfMeasure
    by_cases hC : 0 < probOf μ C
    · by_cases hBC : 0 < probOf μ (B ∩ C)
      · rw [if_pos hC, if_pos hBC, if_pos hC, Finset.inter_assoc]
        field_simp
      · have hz : probOf μ (B ∩ C) = 0 := le_antisymm (not_lt.mp hBC) (probOf_nonneg μ _)
        have hz' : probOf μ (A ∩ B ∩ C) = 0 := le_antisymm
          (by rw [← hz]; exact probOf_mono μ (by rw [Finset.inter_assoc]; exact Finset.inter_subset_right))
          (probOf_nonneg μ _)
        rw [if_pos hC, if_neg hBC, if_pos hC, hz, hz', zero_div, one_mul]
    · have hz : probOf μ (B ∩ C) = 0 := le_antisymm
        (by rw [← le_antisymm (not_lt.mp hC) (probOf_nonneg μ C)]
            exact probOf_mono μ Finset.inter_subset_right) (probOf_nonneg μ _)
      rw [if_neg hC, if_neg (by rw [hz]; exact lt_irrefl 0), if_neg hC, one_mul]
  nontrivial := by
    refine ⟨∅, Finset.univ, ?_⟩
    unfold condOfMeasure
    rw [if_pos (by rw [probOf_univ]; exact one_pos), Finset.empty_inter, probOf_empty, zero_div]
    exact zero_ne_one

end ofMeasure

/-! ## The Popper reading of a ray limit -/

section rayPopper

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- The Popper reading of the limit along a ray (`popperLimit` for a general ray).
Source: P07 I2′; mandate T15. Kind: D -/
noncomputable def popperLimitRay (R : Ray ι acts K) (B : Tree Ω ι acts K) (A B' : Finset Ω) : K :=
  if nuPolyRay R B B' ≠ 0 then limitCondRay R B A B' else 1

/-- A limiting conditional from a scalar factorisation: if `nuPolyRay (X ∩ O) = C c · nuPolyRay O`
with `nuPolyRay O ≠ 0`, the limit is `c`. Source: none: infrastructure. Kind: L -/
theorem limitCondRay_of_scalar (R : Ray ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω) (c : K)
    (hO : nuPolyRay R B O ≠ 0) (h : nuPolyRay R B (X ∩ O) = Polynomial.C c * nuPolyRay R B O) :
    limitCondRay R B X O = c := by
  unfold limitCondRay
  rw [h, Polynomial.coeff_C_mul]
  have : (nuPolyRay R B O).coeff (nuPolyRay R B O).natTrailingDegree ≠ 0 :=
    (trailingCoeff_nuPolyRay_pos R B O hO).ne'
  field_simp

end rayPopper

/-! ## The chance-twin tree -/

/-- The four worlds `(coin, act)`. Source: mandate T15. Kind: D -/
inductive TwinW : Type
  | ha
  | hb
  | ta
  | tb
  deriving DecidableEq, Fintype

/-- The world on branch `i` after act `x`. Source: mandate T15. Kind: D -/
def twinW (i : Fin 2) (x : Act2) : TwinW :=
  if i = 0 then (if x = .a then .ha else .hb) else (if x = .a then .ta else .tb)

/-- **The chance-twin tree**: a fair coin, then a `d`-node in each branch, payoffs `0`.
Source: mandate T15 (`chanceTwin`); P07 Open 3
Kind: D -/
def chanceTwin : Tree TwinW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => .decision () fun x => .leaf (twinW i x) 0

/-- A sum over the leaves. Source: none: infrastructure. Kind: L -/
theorem chanceTwin_sum (f : chanceTwin.Leaves → Polynomial ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ x : Act2, f ⟨i, x, ()⟩ := by
  unfold chanceTwin at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- Along every ray the event polynomials are `nuPolyRay {ha, ta} = w_a` and
`nuPolyRay {ha} = C ½ · w_a`. Source: mandate T15. Kind: L -/
theorem chanceTwin_nuPolyRay (R : Ray Unit (fun _ => Act2) ℚ) :
    nuPolyRay R chanceTwin {.ha, .ta} = R.w () .a ∧
    nuPolyRay R chanceTwin ({.ha} ∩ {.ha, .ta}) = Polynomial.C (1 / 2) * R.w () .a := by
  constructor
  · rw [nuPolyRay_eq_sum, chanceTwin_sum]
    simp [chanceTwin, leafLawPolyRay, twinW, Fin.sum_univ_two, Act2.sum_univ, FinDistr.fair,
      FinDistr.coin]
    ring
  · rw [nuPolyRay_eq_sum, chanceTwin_sum]
    simp [chanceTwin, leafLawPolyRay, twinW, Fin.sum_univ_two, Act2.sum_univ, FinDistr.fair,
      FinDistr.coin]

/-- **Along every ray the Popper reading of `P({(H,a)} | {(H,a),(T,a)})` is `½` or `1`**: `½` when
`w_a ≠ 0`, the convention's `1` when `w_a = 0` (a trap ray). Never `⅓`.
Source: mandate T15 ("for every ray `R` (of any procedure), `limitCondRay R B {(H,a)}
{(H,a),(T,a)} = ½`"); P07 Open 3
Kind: P
Fidelity: exact
Hyps: none -/
theorem chanceTwin_popperLimitRay (R : Ray Unit (fun _ => Act2) ℚ) :
    popperLimitRay R chanceTwin {.ha} {.ha, .ta} = 1 / 2 ∨
    popperLimitRay R chanceTwin {.ha} {.ha, .ta} = 1 := by
  obtain ⟨h1, h2⟩ := chanceTwin_nuPolyRay R
  unfold popperLimitRay
  by_cases hz : R.w () .a = 0
  · right; rw [if_neg (by rw [h1]; exact not_not.mpr hz)]
  · left
    rw [if_pos (by rw [h1]; exact hz)]
    exact limitCondRay_of_scalar R chanceTwin _ _ (1 / 2) (by rw [h1]; exact hz)
      (by rw [h2, h1])

/-- The measure `μ(H,a) = ⅓`, `μ(T,a) = ⅔`. Source: mandate T15. Kind: D -/
def twinMeasure : FinDistr ℚ TwinW where
  w := fun w => match w with
    | .ha => 1 / 3
    | .ta => 2 / 3
    | _ => 0
  nonneg := fun w => by cases w <;> simp <;> norm_num
  sum_one := by
    rw [show (Finset.univ : Finset TwinW) = {.ha, .hb, .ta, .tb} from by ext x; cases x <;> simp]
    simp [Finset.sum_insert]
    norm_num

/-- **A Popper function with `p({(H,a)} | {(H,a),(T,a)}) = ⅓`** on the chance-twin world algebra.
Source: mandate T15. Kind: N+. Fidelity: exact -/
theorem twinPopper_third :
    IsPopper (condOfMeasure twinMeasure) ∧
    condOfMeasure twinMeasure {.ha} {.ha, .ta} = 1 / 3 := by
  refine ⟨isPopper_ofMeasure twinMeasure, ?_⟩
  unfold condOfMeasure
  rw [if_pos (by simp [probOf, twinMeasure, Finset.sum_pair]; norm_num)]
  simp [probOf, twinMeasure, Finset.sum_pair]
  norm_num

/-- **Not every Popper function is a ray limit on the chance-twin tree**: on `chanceTwin` the
Popper function `condOfMeasure twinMeasure` (value `⅓` at `{(H,a)} | {(H,a),(T,a)}`) equals
`popperLimitRay R chanceTwin` for no ray `R` (whose value there is `½`, or the convention's `1`
on a trap ray with `w_a = 0`, where both event polynomials vanish), in particular for no
uniform ray `popperLimit C chanceTwin` of any procedure. The statement is tree-relative, as
P07 Open 3 is ("the limit of some tremble ray of a procedure on that tree"): on a different
tree over the same worlds (chance `(⅓, ⅔)` then the two `a`-leaves) the same function *is*
`popperLimit C` for every `C`. Refutes the universal reading of "every Popper function arises
as a ray limit" (the SL run's Dead list already forbids the affirmative sentence); the
surviving neighbour is the chance-conditional invariance of `PopperClass.lean`.
Source: dp-sl-2-020; P07 Open 3 ("is every Popper function a limit along some ray?" — the
source expected "no"); `sl-synthesis.md` Dead list
Kind: N+
Fidelity: exact
Hyps: none -/
theorem chanceTwin_refutes :
    (∀ R : Ray Unit (fun _ => Act2) ℚ, popperLimitRay R chanceTwin ≠ condOfMeasure twinMeasure) ∧
    (∀ C : Proc Unit (fun _ => Act2) ℚ, popperLimit C chanceTwin ≠ condOfMeasure twinMeasure) := by
  obtain ⟨-, hthird⟩ := twinPopper_third
  have key : ∀ R : Ray Unit (fun _ => Act2) ℚ, popperLimitRay R chanceTwin ≠ condOfMeasure twinMeasure := by
    intro R h
    have := congrFun (congrFun h {.ha}) {.ha, .ta}
    rw [hthird] at this
    rcases chanceTwin_popperLimitRay R with h' | h' <;> rw [h'] at this <;> norm_num at this
  refine ⟨key, fun C h => key (uniformRay C) ?_⟩
  rw [← h]
  funext A B'
  unfold popperLimitRay popperLimit
  rw [nuPolyRay_uniform, limitCondRay_uniform]

end Cleanroom.Decision.DpCalibLimits
