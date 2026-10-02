import Cleanroom.Found.DpCoreTree.Seed

/-!
# SE-1(b), second half: the shared-seed optimum is pure

T2 stretch of [[dp-core-tree-mandate]]. Under Definition 6′, `V'_B` is affine in every `C(d)`
(`value'_deviate_sum`), so on every tree a procedure can be made deterministic point by point
on `queried B` without lowering `V'` (`exists_detOn_ge`); deterministic procedures induce the
same law under both semantics (`leafLaw'_ofFun`); hence `max_C V'_B(C) = max_{π pure} V_B(π)`,
attained by a deterministic procedure (`exists_pure_max_value'`). Contrast: under Definition 6
the AMD's optimum is properly mixed (`amd_value`: `V = (1−q)(3q+1)`, maximal at `q = ⅓`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Found.DpCoreTree

open Finset

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] [DecidableEq ι]
  [∀ d, Nonempty (acts d)]

namespace Tree

/-! ### Deterministic procedures agree under both semantics -/

/-- On a list of draws, the memoised walk of a deterministic procedure is the plain draw product,
provided every seed already drawn is the procedure's own action.
Source: `seeds.md` Remark 3.2 ("a shared-seed variant … differs only for stochastic
procedures")
Kind: L -/
theorem seedFold_ofFun (π : (d : ι) → acts d) :
    (L : List (Σ d : ι, acts d)) → ∀ env : (d : ι) → Option (acts d),
      (∀ d a, env d = some a → a = π d) →
      seedFold (Proc.ofFun π) env L = (L.map fun x => ((Proc.ofFun π : Proc ι acts K) x.1).w x.2).prod
  | [], _, _ => by simp
  | ⟨d, a⟩ :: L, env, henv => by
      simp only [List.map_cons, List.prod_cons, Proc.ofFun_w]
      rcases hd : env d with _ | a'
      · rw [seedFold_cons_of_none _ hd]
        by_cases ha : a = π d
        · rw [seedFold_ofFun π L _ (fun d' b hb => by
            by_cases hdd : d' = d
            · subst hdd; simp at hb; rw [← hb]; exact ha
            · rw [Function.update_of_ne hdd] at hb; exact henv d' b hb)]
          simp [ha]
        · simp [ha]
      · rw [seedFold_cons_of_some _ hd]
        have ha' := henv d a' hd
        subst ha'
        rw [seedFold_ofFun π L env henv]
        by_cases ha : a = π d
        · simp [ha]
        · simp [ha, Ne.symm ha]

/-- **Deterministic procedures induce the same law under Definitions 6 and 6′.**
Source: `seeds.md` Remark 3.2; [[decision-problems-v2]] Remark 3.2 ("differs only for
stochastic procedures")
Kind: P -/
theorem leafLaw'_ofFun (π : (d : ι) → acts d) (B : Tree Ω ι acts K) (ℓ : B.Leaves) :
    leafLaw' (Proc.ofFun π) B ℓ = leafLaw (Proc.ofFun π) B ℓ := by
  rw [leafLaw'_eq, leafLaw_eq_chanceWeight_mul_drawsWeight]
  unfold drawsWeight
  rw [seedFold_ofFun π _ _ (fun d a h => by cases h)]

/-- `V'` and `V` agree on deterministic procedures.
Source: `seeds.md` SE-1(b) ("`max_C V'_B(C) = max_{π pure} V_B(π)`")
Kind: L -/
theorem value'_ofFun (π : (d : ι) → acts d) (B : Tree Ω ι acts K) :
    value' (Proc.ofFun π) B = value (Proc.ofFun π) B :=
  Finset.sum_congr rfl fun ℓ _ => by rw [leafLaw'_ofFun]

/-- `ν'` of a deterministic procedure is its `ν`.
Source: [[decision-problems-v2]] Remark 3.2; `seeds.md` (deterministic procedures induce one
law under both semantics)
Kind: L -/
theorem nu'_ofFun [DecidableEq Ω] (π : (d : ι) → acts d) (B : Tree Ω ι acts K) (X : Finset Ω) :
    nu' (Proc.ofFun π) B X = nu (Proc.ofFun π) B X :=
  Finset.sum_congr rfl fun ℓ _ => by rw [leafLaw'_ofFun]

/-- `V'` is a function of `C` on the queried points only.
Source: none: infrastructure
Kind: L -/
theorem value'_congr_queried {C C' : Proc ι acts K} (B : Tree Ω ι acts K)
    (h : ∀ d ∈ queried B, C d = C' d) : value' C B = value' C' B := by
  rw [value'_eq_product_mixture, value'_eq_product_mixture]
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  · exact Finset.prod_congr rfl fun d _ => by rw [h d d.2]
  · apply value_congr_queried
    intro d hd
    simp [Proc.pureOn, hd]

/-! ### Point-by-point purification -/

/-- `C` is deterministic on the points of `S`.
Source: [[decision-problems-v2]] Definition 4 ("deterministic")
Kind: D -/
def Proc.DetOn (C : Proc ι acts K) (S : Finset ι) : Prop := ∀ d ∈ S, ∃ a, C d = FinDistr.pure a

/-- A convex combination is at most its largest term.
Source: none: infrastructure
Kind: L -/
theorem exists_le_of_convex {α : Type} [Fintype α] [Nonempty α] (w : FinDistr K α) (f : α → K) :
    ∃ a, ∑ b, w.w b * f b ≤ f a := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨a, ?_⟩
  calc ∑ b, w.w b * f b ≤ ∑ b, w.w b * f a :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (ha b (Finset.mem_univ b)) (w.nonneg b)
    _ = f a := by rw [← Finset.sum_mul, w.sum_one, one_mul]

/-- **Purification**: on any finite set of points `S`, every procedure can be replaced by one
that is deterministic on `S`, agrees with it off `S`, and has no smaller `V'`.
Source: `seeds.md` SE-1(b) ("attained by a deterministic procedure on every tree")
Kind: P -/
theorem exists_detOn_ge (B : Tree Ω ι acts K) (S : Finset ι) :
    ∀ C : Proc ι acts K, ∃ C' : Proc ι acts K,
      Proc.DetOn C' S ∧ (∀ d, d ∉ S → C' d = C d) ∧ value' C B ≤ value' C' B := by
  induction S using Finset.induction_on with
  | empty => intro C; exact ⟨C, fun d hd => absurd hd (Finset.notMem_empty d), fun _ _ => rfl, le_rfl⟩
  | insert d S hdS ih =>
    intro C
    obtain ⟨C₁, hdet, hoff, hle⟩ := ih C
    obtain ⟨a, ha⟩ := exists_le_of_convex (C₁ d) fun a => value' (C₁.deviatePure d a) B
    refine ⟨C₁.deviatePure d a, ?_, ?_, ?_⟩
    · intro d' hd'
      rw [Finset.mem_insert] at hd'
      rcases hd' with rfl | hd'
      · exact ⟨a, by simp [Proc.deviatePure]⟩
      · have hne : d' ≠ d := fun h => hdS (h ▸ hd')
        rw [Proc.deviatePure, Proc.deviate_ne _ _ hne]
        exact hdet d' hd'
    · intro d' hd'
      rw [Finset.mem_insert, not_or] at hd'
      rw [Proc.deviatePure, Proc.deviate_ne _ _ hd'.1]
      exact hoff d' hd'.2
    · calc value' C B ≤ value' C₁ B := hle
        _ = ∑ b, (C₁ d).w b * value' (C₁.deviatePure d b) B := value'_deviate_sum C₁ B d
        _ ≤ value' (C₁.deviatePure d a) B := ha

/-- Extend a deterministic-on-`queried B` procedure to an assignment.
Source: none: infrastructure
Kind: D -/
noncomputable def Proc.assignOf (C : Proc ι acts K) (S : Finset ι) (h : Proc.DetOn C S) :
    (d : ι) → acts d :=
  fun d => if hd : d ∈ S then Classical.choose (h d hd) else Classical.arbitrary _

/-- A procedure deterministic on `S` agrees on `S` with its assignment.
Source: none: infrastructure
Kind: L -/
theorem Proc.assignOf_spec (C : Proc ι acts K) (S : Finset ι) (h : Proc.DetOn C S) {d : ι}
    (hd : d ∈ S) : C d = FinDistr.pure (Proc.assignOf C S h d) := by
  unfold Proc.assignOf
  rw [dif_pos hd]
  exact Classical.choose_spec (h d hd)

/-- Every procedure is dominated under 6′ by a deterministic one.
Source: `seeds.md` SE-1(b)
Kind: C -/
theorem exists_pure_ge (B : Tree Ω ι acts K) (C : Proc ι acts K) :
    ∃ π : (d : ι) → acts d, value' C B ≤ value (Proc.ofFun π) B := by
  obtain ⟨C', hdet, -, hle⟩ := exists_detOn_ge B (queried B) C
  refine ⟨Proc.assignOf C' (queried B) hdet, ?_⟩
  calc value' C B ≤ value' C' B := hle
    _ = value' (Proc.ofFun (Proc.assignOf C' (queried B) hdet)) B :=
        value'_congr_queried B fun d hd => by
          rw [Proc.assignOf_spec C' (queried B) hdet hd]; rfl
    _ = value (Proc.ofFun (Proc.assignOf C' (queried B) hdet)) B := value'_ofFun _ B

/-- Restrict an assignment to the queried points and extend it back arbitrarily.
Source: none: infrastructure
Kind: D -/
noncomputable def extendAssign (B : Tree Ω ι acts K) (π : (d : ↥(queried B)) → acts d) :
    (d : ι) → acts d :=
  fun d => if hd : d ∈ queried B then π ⟨d, hd⟩ else Classical.arbitrary _

/-- **SE-1(b), second half: `max_C V'_B(C) = max_{π pure} V_B(π)`, attained by a deterministic
procedure.** There is a deterministic procedure `π*` (one action per *point*, `seeds.md`'s
"`π` pure" — not v2 Proposition 5(a)'s *assignment*, which is one action per decision *node*;
on nested trees the two maxima differ, Proposition 5(c)) with `V'_B(C) ≤ V_B(π*)` for every
procedure `C`, `V_B(π) ≤ V_B(π*)` for every deterministic procedure `π`, and
`V'_B(π*) = V_B(π*)`.
Source: `seeds.md` SE-1(b) ("`max_C V'_B(C) = max_{π pure} V_B(π)` is attained by a
deterministic procedure on every tree (AMD: `V'(q) = 1−q`, max `1`, against Definition 6's
`max_mixed = 4/3`)"); mandate T2 (stretch)
Kind: P
Fidelity: exact
Hyps: none -/
theorem exists_pure_max_value' (B : Tree Ω ι acts K) :
    ∃ π : (d : ι) → acts d,
      (∀ C : Proc ι acts K, value' C B ≤ value (Proc.ofFun π) B) ∧
      (∀ π' : (d : ι) → acts d, value (Proc.ofFun π') B ≤ value (Proc.ofFun π) B) ∧
      value' (Proc.ofFun π) B = value (Proc.ofFun π) B := by
  -- maximise `V_B` over the finitely many assignments on `queried B`
  obtain ⟨πm, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ((d : ↥(queried B)) → acts d))
    (fun π => value (Proc.ofFun (extendAssign B π)) B) Finset.univ_nonempty
  have hrestrict : ∀ π' : (d : ι) → acts d,
      value (Proc.ofFun π') B = value (Proc.ofFun (extendAssign B fun d => π' d)) B := by
    intro π'
    apply value_congr_queried
    intro d hd
    simp [Proc.ofFun, extendAssign, hd]
  refine ⟨extendAssign B πm, fun C => ?_, fun π' => ?_, value'_ofFun _ B⟩
  · obtain ⟨π', hπ'⟩ := exists_pure_ge B C
    calc value' C B ≤ value (Proc.ofFun π') B := hπ'
      _ = value (Proc.ofFun (extendAssign B fun d => π' d)) B := hrestrict π'
      _ ≤ value (Proc.ofFun (extendAssign B πm)) B := hmax _ (Finset.mem_univ _)
  · rw [hrestrict π']
    exact hmax _ (Finset.mem_univ _)

end Tree

end Cleanroom.Found.DpCoreTree
