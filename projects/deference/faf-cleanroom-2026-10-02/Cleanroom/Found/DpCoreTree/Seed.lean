import Cleanroom.Found.DpCoreTree.Agreement

/-!
# SE-1: the shared-seed law is the product mixture of the pure laws; multiaffinity

T2 of [[dp-core-tree-mandate]] (theorem half) and T7(iv). Because Definition 6′ is rendered
operationally (`leafLawSeed`, a memoised walk), the product-mixture form
`μ'_{B,C} = ∑_π (∏_{d ∈ queried B} C(d)(π(d))) μ_{B,π}` (SE-1(a)) is a **theorem** here
(`leafLaw'_eq_product_mixture`), proved from a generalisation over the seed environment.
SE-1(b), multiaffinity `μ'_{B,C} = ∑_a C(d)(a) μ'_{B,C[d↦a]}` at every point (queried or not),
is proved directly (`leafLaw'_deviate_sum`) and lifted to `V'` and `ν'`.

T7(iv): on almost-fair trees `V_B(C) = ∑_π (∏_d C(d)(π(d))) V_B(π)` (`AlmostFair.value_interpolation`),
and in general the *multiplicity term* `V_B(C) − ∑_π (∏_d C(d)(π(d))) V_B(π)` equals
`V_B(C) − V'_B(C)` (`multiplicityTerm_eq_value_sub_value'`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

namespace Tree

/-! ### SE-1(b): multiaffinity of the shared-seed law -/

variable (C : Proc ι acts K)

/-- Procedures agreeing at every unseeded point give the memoised walk the same masses.
Source: none: infrastructure
Kind: L -/
theorem leafLawSeed_congr {C C' : Proc ι acts K} :
    (B : Tree Ω ι acts K) → ∀ env, (∀ d, env d = none → C d = C' d) →
      ∀ ℓ, leafLawSeed C env B ℓ = leafLawSeed C' env B ℓ
  | leaf _ _, _, _, _ => rfl
  | chance _ β child, env, h, ⟨i, ℓ⟩ => by
      simp only [leafLawSeed_chance, leafLawSeed_congr (child i) env h ℓ]
  | decision d child, env, h, ⟨a, ℓ⟩ => by
      rcases hd : env d with _ | a'
      · rw [leafLawSeed_decision_of_none C hd, leafLawSeed_decision_of_none C' hd, h d hd]
        congr 1
        apply leafLawSeed_congr (child a)
        intro d' hd'
        by_cases hdd : d' = d
        · subst hdd; simp at hd'
        · rw [Function.update_of_ne hdd] at hd'; exact h d' hd'
      · rw [leafLawSeed_decision_of_some C hd, leafLawSeed_decision_of_some C' hd]
        split_ifs
        · exact leafLawSeed_congr (child a) env h ℓ
        · rfl

/-- Multiaffinity of the memoised walk at any point, from any seed environment.
Source: `seeds.md` SE-1(b)
Kind: P -/
theorem leafLawSeed_deviate_sum (d : ι) :
    (B : Tree Ω ι acts K) → ∀ env ℓ,
      leafLawSeed C env B ℓ = ∑ a, (C d).w a * leafLawSeed (C.deviatePure d a) env B ℓ
  | leaf _ _, _, _ => by simp [FinDistr.sum_one]
  | chance _ β child, env, ⟨i, ℓ⟩ => by
      simp only [leafLawSeed_chance, leafLawSeed_deviate_sum d (child i) env ℓ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
  | decision d' child, env, ⟨b, ℓ⟩ => by
      rcases hd : env d' with _ | a'
      · simp only [leafLawSeed_decision_of_none _ hd]
        by_cases hdd : d' = d
        · subst hdd
          simp only [Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w]
          rw [Finset.sum_eq_single b]
          · simp only [if_true, one_mul]
            congr 1
            apply leafLawSeed_congr (child b)
            intro d'' hd''
            by_cases h : d'' = d'
            · subst h; simp at hd''
            · rw [Proc.deviate_ne _ _ h]
          · intro a _ ha; simp [Ne.symm ha]
          · intro h; exact absurd (Finset.mem_univ b) h
        · simp only [Proc.deviatePure, Proc.deviate_ne _ _ hdd]
          rw [leafLawSeed_deviate_sum d (child b) _ ℓ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
      · simp only [leafLawSeed_decision_of_some _ hd]
        split_ifs
        · exact leafLawSeed_deviate_sum d (child b) env ℓ
        · simp

/-- **SE-1(b), leaf-law level**: `μ'_{B,C}(ℓ) = ∑_a C(d)(a) μ'_{B,C[d↦a]}(ℓ)` for every point `d`,
on every tree.
Source: `seeds.md` SE-1(b)
Kind: P
Fidelity: exact (stated at every point and at leaf level; at an unqueried point the identity is
trivial, so "every point" is nominal) -/
theorem leafLaw'_deviate_sum (B : Tree Ω ι acts K) (d : ι) (ℓ : B.Leaves) :
    leafLaw' C B ℓ = ∑ a, (C d).w a * leafLaw' (C.deviatePure d a) B ℓ :=
  leafLawSeed_deviate_sum C d B _ ℓ

/-- **SE-1(b)**: `V'_B(C) = ∑_a C(d)(a) V'_B(C[d↦a])` on every tree (multiaffine in `C(d)`).
Source: `seeds.md` SE-1(b)
Kind: C
Fidelity: exact
Hyps: none -/
theorem value'_deviate_sum (B : Tree Ω ι acts K) (d : ι) :
    value' C B = ∑ a, (C d).w a * value' (C.deviatePure d a) B := by
  unfold value'
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ℓ _ => by
    rw [leafLaw'_deviate_sum C B d ℓ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring

/-- `ν'_{B,C}(X) = ∑_a C(d)(a) ν'_{B,C[d↦a]}(X)`.
Source: `seeds.md` SE-1(b)
Kind: C -/
theorem nu'_deviate_sum [DecidableEq Ω] (B : Tree Ω ι acts K) (d : ι) (X : Finset Ω) :
    nu' C B X = ∑ a, (C d).w a * nu' (C.deviatePure d a) B X := by
  unfold nu'
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [leafLaw'_deviate_sum C B d ℓ]

/-! ### SE-1(a): the product mixture -/

/-- The procedure that plays `π` deterministically on the points of `S` and `C` elsewhere.
Source: `seeds.md` SE-1(a) (`μ_{B,π}` for `π ∈ ∏_d A_d`, the product over the queried points)
Kind: D -/
def Proc.pureOn (S : Finset ι) (π : (d : ↥S) → acts d) : Proc ι acts K :=
  fun d => if h : d ∈ S then FinDistr.pure (π ⟨d, h⟩) else C d

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem Proc.pureOn_of_mem (S : Finset ι) (π : (d : ↥S) → acts d) {d : ι} (h : d ∈ S) :
    Proc.pureOn C S π d = FinDistr.pure (π ⟨d, h⟩) := by
  simp [Proc.pureOn, h]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem Proc.pureOn_of_not_mem (S : Finset ι) (π : (d : ↥S) → acts d) {d : ι} (h : d ∉ S) :
    Proc.pureOn C S π d = C d := by
  simp [Proc.pureOn, h]

/-- The seed-conditional weight of a draw: a point mass at the seed if drawn, `C(d)` otherwise.
Source: none: infrastructure
Kind: D -/
def seedW (env : (d : ι) → Option (acts d)) (d : ι) (a : acts d) : K :=
  match env d with
  | some a' => if a' = a then 1 else 0
  | none => (C d).w a

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem seedW_of_some {env : (d : ι) → Option (acts d)} {d : ι} {a' : acts d}
    (h : env d = some a') (a : acts d) : seedW C env d a = if a' = a then 1 else 0 := by
  simp [seedW, h]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
theorem seedW_of_none {env : (d : ι) → Option (acts d)} {d : ι} (h : env d = none) (a : acts d) :
    seedW C env d a = (C d).w a := by
  simp [seedW, h]

/-- Equation lemma: unfolds the definition on a constructor. Source: none: infrastructure. Kind: L -/
@[simp] theorem seedW_none (d : ι) (a : acts d) : seedW C (fun _ => none) d a = (C d).w a := rfl

/-- The seed-conditional weights sum to one.
Source: none: infrastructure
Kind: L -/
theorem sum_seedW (env : (d : ι) → Option (acts d)) (d : ι) : ∑ a, seedW C env d a = 1 := by
  rcases h : env d with _ | a'
  · simp only [seedW_of_none C h]; exact (C d).sum_one
  · simp only [seedW_of_some C h]; simp

/-- Sum-of-products over a dependent product of finite types.
Source: none: infrastructure (`Fintype.prod_sum` reversed)
Kind: L -/
theorem sum_prod_pi {S : Finset ι} (w : (d : ↥S) → acts d → K) :
    ∑ π : (d : ↥S) → acts d, ∏ d : ↥S, w d (π d) = ∏ d : ↥S, ∑ a, w d a :=
  (Fintype.prod_sum w).symm

/-- **SE-1(a), generalised over the seed environment**: from any environment `env`, on any
`S ⊇ queried B`, the memoised walk is the mixture of the pure laws `μ_{B,pureOn C S π}` with
weights `∏_{d ∈ S} seedW env d (π d)`.
Source: `seeds.md` SE-1(a) ("condition on the seed tuple")
Kind: P -/
theorem leafLawSeed_eq_mixture (S : Finset ι) :
    (B : Tree Ω ι acts K) → queried B ⊆ S → ∀ env ℓ,
      leafLawSeed C env B ℓ =
        ∑ π : (d : ↥S) → acts d,
          (∏ d : ↥S, seedW C env d (π d)) * leafLaw (Proc.pureOn C S π) B ℓ
  | leaf _ _, _, env, _ => by
      simp only [leafLawSeed_leaf, leafLaw_leaf, mul_one]
      rw [sum_prod_pi]
      simp [sum_seedW]
  | chance _ β child, hS, env, ⟨i, ℓ⟩ => by
      have hS' : queried (child i) ⊆ S := (queried_child_subset_chance β child i).trans hS
      simp only [leafLawSeed_chance, leafLaw_chance,
        leafLawSeed_eq_mixture S (child i) hS' env ℓ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun π _ => by ring
  | decision d child, hS, env, ⟨b, ℓ⟩ => by
      have hS' : queried (child b) ⊆ S := (queried_child_subset_decision d child b).trans hS
      have hd : d ∈ S := hS (mem_queried_decision d child)
      have hprod : ∀ π : (d : ↥S) → acts d, ∀ env',
          (∏ d : ↥S, seedW C env' d (π d)) =
            seedW C env' d (π ⟨d, hd⟩) *
              ∏ d ∈ Finset.univ.erase (⟨d, hd⟩ : ↥S), seedW C env' d (π d) :=
        fun π env' => (Finset.mul_prod_erase Finset.univ (fun d : ↥S => seedW C env' d (π d))
          (Finset.mem_univ (⟨d, hd⟩ : ↥S))).symm
      have herase : ∀ π : (d : ↥S) → acts d, ∀ env₁ env₂ : (d : ι) → Option (acts d),
          (∀ d', d' ≠ d → env₁ d' = env₂ d') →
          (∏ d ∈ Finset.univ.erase (⟨d, hd⟩ : ↥S), seedW C env₁ d (π d)) =
            ∏ d ∈ Finset.univ.erase (⟨d, hd⟩ : ↥S), seedW C env₂ d (π d) := by
        intro π env₁ env₂ h
        refine Finset.prod_congr rfl fun d' hd' => ?_
        have hne : (d' : ι) ≠ d := by
          intro heq; apply Finset.ne_of_mem_erase hd'; exact Subtype.ext heq
        simp only [seedW, h d' hne]
      simp only [leafLaw_decision, Proc.pureOn_of_mem C S _ hd, FinDistr.pure_w]
      rcases henv : env d with _ | a'
      · rw [leafLawSeed_decision_of_none C henv,
          leafLawSeed_eq_mixture S (child b) hS' _ ℓ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [hprod π env, hprod π, herase π (Function.update env d (some b)) env
          (fun d' h => Function.update_of_ne h _ _)]
        rw [seedW_of_some C (show Function.update env d (some b) d = some b by simp) (π ⟨d, hd⟩),
          seedW_of_none C henv (π ⟨d, hd⟩)]
        by_cases hb : π ⟨d, hd⟩ = b
        · rw [hb]; simp only [eq_self_iff_true, if_true, mul_one, one_mul, mul_assoc]
        · simp [hb, Ne.symm hb]
      · rw [leafLawSeed_decision_of_some C henv]
        split_ifs with hab
        · subst hab
          rw [leafLawSeed_eq_mixture S (child a') hS' env ℓ]
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [hprod π env, seedW_of_some C henv (π ⟨d, hd⟩)]
          by_cases hb : π ⟨d, hd⟩ = a'
          · rw [hb]; simp only [eq_self_iff_true, if_true, mul_one, one_mul, mul_assoc]
          · simp [hb, Ne.symm hb]
        · symm
          apply Finset.sum_eq_zero
          intro π _
          rw [hprod π env, seedW_of_some C henv (π ⟨d, hd⟩)]
          by_cases hb : π ⟨d, hd⟩ = a'
          · rw [hb]; simp [hab, Ne.symm hab]
          · simp [Ne.symm hb]

/-- **SE-1(a), the product-mixture form of Definition 6′**: on every tree,
`μ'_{B,C}(ℓ) = ∑_{π ∈ ∏_{d ∈ queried B} A_d} (∏_{d ∈ queried B} C(d)(π(d))) · μ_{B,π}(ℓ)`, where
`μ_{B,π}` is the law of the deterministic procedure `π` on the queried points (`pureOn`; by
`leafLaw_congr_queried` its values off `queried B` are irrelevant).
Source: `seeds.md` SE-1(a); mandate T2 (route (a): a real theorem, not a definition)
Kind: P
Fidelity: exact (sum and product over `queried B`)
Hyps: none -/
theorem leafLaw'_eq_product_mixture (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    leafLaw' C B ℓ =
      ∑ π : (d : ↥(queried B)) → acts d,
        (∏ d : ↥(queried B), (C d).w (π d)) * leafLaw (Proc.pureOn C (queried B) π) B ℓ := by
  unfold leafLaw'
  rw [leafLawSeed_eq_mixture C (queried B) B (Finset.Subset.refl _) _ ℓ]
  simp only [seedW_none]

/-- `V'_B(C)` as the product mixture of the pure values.
Source: `seeds.md` SE-1(a)
Kind: C -/
theorem value'_eq_product_mixture (B : Tree Ω ι acts K) :
    value' C B =
      ∑ π : (d : ↥(queried B)) → acts d,
        (∏ d : ↥(queried B), (C d).w (π d)) * value (Proc.pureOn C (queried B) π) B := by
  unfold value' value
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ℓ _ => by
    rw [leafLaw'_eq_product_mixture C B ℓ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun π _ => by ring

/-! ### T7(iv): interpolation and the multiplicity term -/

/-- The multiplicity term: `V_B(C)` minus the product-mixture interpolation of the pure values.
Source: `cf-workflow` A24/A23 via dp-cf-2-055 ("the multiplicity term
`V_B(C) − ∑_π ∏_d C(d)(π(d)) V_B(π)`")
Kind: D -/
def multiplicityTerm (B : Tree Ω ι acts K) : K :=
  value C B -
    ∑ π : (d : ↥(queried B)) → acts d,
      (∏ d : ↥(queried B), (C d).w (π d)) * value (Proc.pureOn C (queried B) π) B

/-- **The multiplicity term is the gap between the two semantics**:
`V_B(C) − ∑_π (∏_d C(d)(π(d))) V_B(π) = V_B(C) − V'_B(C)`, on every tree. One rewrite of
SE-1(a) (`value'_eq_product_mixture`) under the definition of `multiplicityTerm`; the content is
SE-1(a)'s.
Source: mandate T7(iv) ("by T2 that term equals `V_B(C) − V'_B(C)`"); `seeds.md` SE-1/SE-2
Kind: L
Fidelity: exact
Hyps: none -/
theorem multiplicityTerm_eq_value_sub_value' (B : Tree Ω ι acts K) :
    multiplicityTerm C B = value C B - value' C B := by
  unfold multiplicityTerm
  rw [value'_eq_product_mixture]

/-- **Interpolation on almost-fair trees**: `V_B(C) = ∑_π (∏_{d ∈ queried B} C(d)(π(d))) V_B(π)`.
Source: `cf-workflow` A24/A23 (dp-cf-2-055), v2 Definition 21 ("multiaffine in the tied
variables" when no path contains two nodes sharing a point)
Kind: C
Fidelity: exact
Hyps: none -/
theorem AlmostFair.value_interpolation {B : Tree Ω ι acts K} (h : AlmostFair B) :
    value C B =
      ∑ π : (d : ↥(queried B)) → acts d,
        (∏ d : ↥(queried B), (C d).w (π d)) * value (Proc.pureOn C (queried B) π) B := by
  rw [h.value_eq_value' C, value'_eq_product_mixture]

/-- On almost-fair trees the multiplicity term vanishes.
Source: dp-cf-2-055
Kind: L -/
theorem AlmostFair.multiplicityTerm_eq_zero {B : Tree Ω ι acts K} (h : AlmostFair B) :
    multiplicityTerm C B = 0 := by
  rw [multiplicityTerm_eq_value_sub_value', h.value_eq_value' C, sub_self]

end Tree

end Cleanroom.Found.DpCoreTree
