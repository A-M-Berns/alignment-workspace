import Cleanroom.Decision.DpCalibration.Bridge
import Cleanroom.Udt.UdtSupercondition.Thinning

/-!
# The exact `ℚ → PMF` bridge (decision 1 of [[dp-firstperson-sc-mandate]])

Every statement of this package that mentions a `udt-supercondition` object (a `CondModel`, a
`BoundedDensity`, a `JeffreyOnA`, a `Downstream`) needs the decision area's `FinDistr ℚ α`
(weights in `ℚ`, non-negative, summing to one) as a Mathlib `PMF α` (masses in `ℝ≥0∞`). The
bridge `toPMF` is `x ↦ ENNReal.ofReal (P.w x)`; it is **exact** (no truncation: `0 ≤ P.w x` is a
field of `FinDistr`, so `ENNReal.ofReal` is injective on the weights, `toPMF_injective`), and it
commutes with the three operations the targets use: event mass (`mass_toPMF`), pushforward
along a function (`toPMF_map`, `toPMF_map_world`), and conditioning on a positive event
(`condOn_toPMF`, `condOn_toPMF_jeffrey`). The run-space instance is `runPMF C B` (the run law
`μ_{B,C}` as a `PMF B.Leaves`).

No such bridge existed anywhere in `Cleanroom/` on 2026-10-01 (`corr-reflect-frames` bridges
frames, not `FinDistr`). Nothing here is a definition of record of the sources: `Kind: D`
infrastructure, `Source: none`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree hiding mass mass_mono mass_union mass_univ mass_nonneg
open Cleanroom.Decision.DpCalibration
open Cleanroom.Udt.UdtSupercondition
open scoped ENNReal
open Finset

/-! ## `toPMF` -/

section toPMF

variable {α : Type} [Fintype α]

/-- The exact bridge `FinDistr ℚ α → PMF α`: `x ↦ ENNReal.ofReal (P.w x)`. Sums to one because the
rational weights do and `ENNReal.ofReal` is additive on non-negative reals.
Source: none: infrastructure (mandate decision 1)
Kind: D
Fidelity: n/a (exact: no `ℝ≥0` truncation, `w ≥ 0` is a field of `FinDistr`) -/
noncomputable def toPMF (P : FinDistr ℚ α) : PMF α :=
  PMF.ofFintype (fun x => ENNReal.ofReal (P.w x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => Rat.cast_nonneg.mpr (P.nonneg x))]
    have h : (∑ x, ((P.w x : ℚ) : ℝ)) = 1 := by rw [← Rat.cast_sum, P.sum_one, Rat.cast_one]
    rw [h, ENNReal.ofReal_one])

/-- The mass function of the bridge. Source: none: infrastructure. Kind: L -/
@[simp] theorem toPMF_apply (P : FinDistr ℚ α) (x : α) : toPMF P x = ENNReal.ofReal (P.w x) := rfl

/-- An atom is null under `toPMF P` iff its rational weight is zero (exactness at atoms).
Source: none: infrastructure. Kind: L -/
theorem toPMF_eq_zero_iff (P : FinDistr ℚ α) (x : α) : toPMF P x = 0 ↔ P.w x = 0 := by
  rw [toPMF_apply, ENNReal.ofReal_eq_zero]
  constructor
  · intro h; exact le_antisymm (by exact_mod_cast h) (P.nonneg x)
  · intro h; rw [h]; simp

/-- Event mass under the bridge is the rational probability, exactly.
Source: none: infrastructure. Kind: L -/
theorem mass_toPMF (P : FinDistr ℚ α) (S : Finset α) :
    mass (toPMF P) (↑S : Set α) = ENNReal.ofReal ((probOf P S : ℚ) : ℝ) := by
  classical
  rw [mass, PMF.toOuterMeasure_apply_fintype]
  have hind : ∀ x, (↑S : Set α).indicator (toPMF P) x =
      if x ∈ S then ENNReal.ofReal (P.w x) else 0 := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem (Finset.mem_coe.mpr hx), if_pos hx, toPMF_apply]
    · rw [Set.indicator_of_notMem (fun h => hx (Finset.mem_coe.mp h)), if_neg hx]
  simp only [hind]
  rw [Finset.sum_ite_mem, Finset.univ_inter,
    ← ENNReal.ofReal_sum_of_nonneg (fun x _ => Rat.cast_nonneg.mpr (P.nonneg x)), probOf,
    Rat.cast_sum]

/-- Positivity transfers across the bridge. Source: none: infrastructure. Kind: L -/
theorem mass_toPMF_pos_iff (P : FinDistr ℚ α) (S : Finset α) :
    0 < mass (toPMF P) (↑S : Set α) ↔ 0 < probOf P S := by
  rw [mass_toPMF, ENNReal.ofReal_pos, Rat.cast_pos]

/-- The bridge is injective (exactness as a map). Source: none: infrastructure. Kind: L -/
theorem toPMF_injective : Function.Injective (toPMF (α := α)) := by
  intro P Q h
  apply FinDistr.ext'
  intro x
  have hx := congrArg (fun p : PMF α => p x) h
  simp only [toPMF_apply] at hx
  rw [ENNReal.ofReal_eq_ofReal_iff (Rat.cast_nonneg.mpr (P.nonneg x))
    (Rat.cast_nonneg.mpr (Q.nonneg x))] at hx
  exact_mod_cast hx

/-- `toPMF P = toPMF Q ↔ P = Q`. Source: none: infrastructure. Kind: L -/
theorem toPMF_eq_iff (P Q : FinDistr ℚ α) : toPMF P = toPMF Q ↔ P = Q :=
  ⟨fun h => toPMF_injective h, fun h => h ▸ rfl⟩

/-- Absolute continuity across the bridge, in the atom form `udt-supercondition` uses on finite
carriers (`boundedDensity_iff_of_fintype`, `sameOntology_condModel_iff_of_fintype`).
Source: none: infrastructure. Kind: L -/
theorem toPMF_ac_iff (P Q : FinDistr ℚ α) :
    (∀ x, toPMF P x = 0 → toPMF Q x = 0) ↔ ∀ x, P.w x = 0 → Q.w x = 0 := by
  simp only [toPMF_eq_zero_iff]

/-- Bounded density across the bridge: `BoundedDensity (toPMF Q) (toPMF P) (ofReal b)` is the
rational atom inequality `Q.w x ≤ b · P.w x`, for `0 ≤ b`.
Source: none: infrastructure. Kind: L -/
theorem boundedDensity_toPMF_iff (Q P : FinDistr ℚ α) (b : ℚ) (hb : 0 ≤ b) :
    BoundedDensity (toPMF Q) (toPMF P) (ENNReal.ofReal b) ↔ ∀ x, Q.w x ≤ b * P.w x := by
  unfold BoundedDensity
  refine forall_congr' fun x => ?_
  rw [toPMF_apply, toPMF_apply, ← ENNReal.ofReal_mul (Rat.cast_nonneg.mpr hb),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Rat.cast_nonneg.mpr hb)
      (Rat.cast_nonneg.mpr (P.nonneg x)))]
  exact_mod_cast Iff.rfl

end toPMF

/-! ## Pushforward -/

section pushforward

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]

/-- The pushforward of a rational distribution along `f`: `w y := P(f⁻¹{y})`.
Source: none: infrastructure
Kind: D -/
def pushDistr (P : FinDistr ℚ α) (f : α → β) : FinDistr ℚ β where
  w y := ∑ x ∈ Finset.univ.filter (fun x => f x = y), P.w x
  nonneg y := Finset.sum_nonneg fun x _ => P.nonneg x
  sum_one := by
    rw [Finset.sum_fiberwise Finset.univ f P.w]
    exact P.sum_one

/-- `(toPMF P).map f = toPMF (pushDistr P f)`: the bridge commutes with pushforward.
Source: none: infrastructure. Kind: L -/
theorem toPMF_map (P : FinDistr ℚ α) (f : α → β) :
    (toPMF P).map f = toPMF (pushDistr P f) := by
  refine PMF.ext fun y => ?_
  rw [PMF.map_apply, tsum_fintype, toPMF_apply]
  show _ = ENNReal.ofReal ((∑ x ∈ Finset.univ.filter (fun x => f x = y), P.w x : ℚ) : ℝ)
  rw [Finset.sum_filter, Rat.cast_sum,
    ENNReal.ofReal_sum_of_nonneg (fun x _ => by split_ifs <;> simp [P.nonneg])]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : f x = y
  · simp [h, toPMF_apply]
  · simp [h, Ne.symm h]

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- The pushforward along `world B` is `dp-calibration`'s `pushdownDistr`.
Source: none: infrastructure. Kind: L -/
theorem pushDistr_world (B : Tree Ω ι acts ℚ) (P : FinDistr ℚ B.Leaves) :
    pushDistr P (world B) = pushdownDistr B P := by
  apply FinDistr.ext'
  intro ω
  show (∑ x ∈ Finset.univ.filter (fun x => world B x = ω), P.w x) = probOf P (worldEv B {ω})
  unfold probOf worldEv
  simp only [Finset.mem_singleton]

/-- `(toPMF P).map (world B) = toPMF (pushdownDistr B P)`: the bridge commutes with `λ_*`.
Source: none: infrastructure. Kind: L -/
theorem toPMF_map_world (B : Tree Ω ι acts ℚ) (P : FinDistr ℚ B.Leaves) :
    (toPMF P).map (world B) = toPMF (pushdownDistr B P) := by
  rw [toPMF_map, pushDistr_world]

end pushforward

/-! ## Conditioning -/

section conditioning

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The rational conditional `P(· | E)` for `0 < P(E)`: `w x := [x ∈ E] · P.w x / P(E)`. This is
exactly the `P`-component of `dp-calibration`'s `jeffreyCond` (`condDistr_eq_jeffreyCond_P`).
Source: none: infrastructure (the division sits behind the positivity guard, as in
`dp-calibration`)
Kind: D -/
def condDistr (P : FinDistr ℚ α) (E : Finset α) (h : 0 < probOf P E) : FinDistr ℚ α where
  w x := if x ∈ E then P.w x / probOf P E else 0
  nonneg x := by
    split_ifs
    · exact div_nonneg (P.nonneg x) (probOf_nonneg _ _)
    · exact le_rfl
  sum_one := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_div]
    exact div_self h.ne'

/-- The conditional's weights. Source: none: infrastructure. Kind: L -/
@[simp] theorem condDistr_w (P : FinDistr ℚ α) (E : Finset α) (h : 0 < probOf P E) (x : α) :
    (condDistr P E h).w x = if x ∈ E then P.w x / probOf P E else 0 := rfl

/-- The probability of an event under the conditional. Source: none: infrastructure. Kind: L -/
theorem probOf_condDistr (P : FinDistr ℚ α) (E : Finset α) (h : 0 < probOf P E) (X : Finset α) :
    probOf (condDistr P E h) X = probOf P (X ∩ E) / probOf P E := by
  unfold probOf condDistr
  simp only
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, ← Finset.sum_div]
  rfl

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `jeffreyCond`'s probability component is `condDistr` (definitional).
Source: none: infrastructure. Kind: L -/
theorem jeffreyCond_P_eq_condDistr (s : State α ℚ) (E : Finset α) (h : 0 < s.pr E) :
    (jeffreyCond s E h).P = condDistr s.P E h := rfl

/-- **The bridge commutes with conditioning**: `condOn (toPMF P) ↑E = toPMF (P(· | E))`.
Source: none: infrastructure (SC §0.8's `condOn` against `dp-calibration`'s cross-multiplied
conditional)
Kind: L -/
theorem condOn_toPMF (P : FinDistr ℚ α) (E : Finset α) (h : 0 < probOf P E) :
    condOn (toPMF P) (↑E : Set α) ((mass_toPMF_pos_iff P E).mpr h) = toPMF (condDistr P E h) := by
  refine PMF.ext fun x => ?_
  rw [condOn_apply, mass_toPMF, toPMF_apply, condDistr_w]
  by_cases hx : x ∈ E
  · rw [Set.indicator_of_mem (by exact_mod_cast hx), toPMF_apply, if_pos hx,
      ← ENNReal.ofReal_inv_of_pos (Rat.cast_pos.mpr h),
      ← ENNReal.ofReal_mul (Rat.cast_nonneg.mpr (P.nonneg x))]
    congr 1
    push_cast
    rw [div_eq_mul_inv]
  · rw [Set.indicator_of_notMem (by exact_mod_cast hx), if_neg hx, zero_mul]
    simp

/-- The state form: `condOn (toPMF s.P) ↑E = toPMF (jeffreyCond s E h).P`.
Source: none: infrastructure. Kind: L -/
theorem condOn_toPMF_jeffrey (s : State α ℚ) (E : Finset α) (h : 0 < s.pr E) :
    condOn (toPMF s.P) (↑E : Set α) ((mass_toPMF_pos_iff s.P E).mpr h) =
      toPMF (jeffreyCond s E h).P := by
  rw [jeffreyCond_P_eq_condDistr]; exact condOn_toPMF s.P E h

/-- Conditioning with an arbitrary positivity proof (proof irrelevance packaged for rewriting).
Source: none: infrastructure. Kind: L -/
theorem condOn_toPMF' (P : FinDistr ℚ α) (E : Finset α) (h : 0 < probOf P E)
    (h' : 0 < mass (toPMF P) (↑E : Set α)) :
    condOn (toPMF P) (↑E : Set α) h' = toPMF (condDistr P E h) :=
  condOn_toPMF P E h

end conditioning

/-- Conditioning on equal events (the positivity proof transported).
Source: none: infrastructure. Kind: L -/
theorem condOn_congr {β : Type} (P : PMF β) {s t : Set β} (hst : s = t) (hs : 0 < mass P s) :
    condOn P s hs = condOn P t (hst ▸ hs) := by
  subst hst; rfl

/-! ## The run space -/

section run

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-- The run law `μ_{B,C}` as a rational distribution on the leaves.
Source: [[decision-problems-v2]] §3.1 Definition 6 (`μ_{B,C} ∈ Δ(Leaves(B))`), packaged
Kind: D -/
def leafDistr (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) : FinDistr ℚ B.Leaves where
  w := leafLaw C B
  nonneg := leafLaw_nonneg C B
  sum_one := sum_leafLaw C B

/-- `probOf (leafDistr C B) S = μ_{B,C}(S)` (definitional). Source: none: infrastructure. Kind: L -/
theorem probOf_leafDistr (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (S : Finset B.Leaves) :
    probOf (leafDistr C B) S = Tree.mass C B S := rfl

/-- **The run law as a `PMF`** on `B.Leaves`: SC's enlarged space `L̂` in reading (a) of AN-1.
Source: `anticipation.md` AN-1 (`L̂ = (Leaves, 2^{Leaves}, μ)`); mandate decision 1
Kind: D -/
noncomputable def runPMF (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) : PMF B.Leaves :=
  toPMF (leafDistr C B)

/-- Event mass of the run `PMF` is the rational mass. Source: none: infrastructure. Kind: L -/
theorem mass_runPMF (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (S : Finset B.Leaves) :
    mass (runPMF C B) (↑S : Set B.Leaves) = ENNReal.ofReal ((Tree.mass C B S : ℚ) : ℝ) := by
  rw [runPMF, mass_toPMF, probOf_leafDistr]

/-- Positivity of a leaf set transfers. Source: none: infrastructure. Kind: L -/
theorem mass_runPMF_pos_iff (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (S : Finset B.Leaves) :
    0 < mass (runPMF C B) (↑S : Set B.Leaves) ↔ 0 < Tree.mass C B S := by
  rw [runPMF, mass_toPMF_pos_iff, probOf_leafDistr]

/-- Conditioning the run `PMF` on a leaf set is the rational conditional through the bridge
(`runPMF` is `toPMF (leafDistr C B)` definitionally; stated so that `rw` needs no unfolding).
Source: none: infrastructure. Kind: L -/
theorem condOn_runPMF (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (S : Finset B.Leaves)
    (h : 0 < Tree.mass C B S) (h' : 0 < mass (runPMF C B) (↑S : Set B.Leaves)) :
    condOn (runPMF C B) (↑S : Set B.Leaves) h' = toPMF (condDistr (leafDistr C B) S h) :=
  condOn_toPMF' (leafDistr C B) S h h'

/-- The world marginal of the run `PMF` is `ν_{B,C}` (the prior state's `P`).
Source: `anticipation.md` AN-1 reading (a) (`p_* L = ν`)
Kind: L -/
theorem runPMF_map_world (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) :
    (runPMF C B).map (world B) = toPMF (pushdownDistr B (leafDistr C B)) :=
  toPMF_map_world B (leafDistr C B)

/-- `λ_* μ` has weights `ν({ω})`. Source: none: infrastructure. Kind: L -/
theorem pushdownDistr_leafDistr_w (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (ω : Ω) :
    (pushdownDistr B (leafDistr C B)).w ω = nu C B {ω} := rfl

end run

end Cleanroom.Decision.DpFirstpersonSc
