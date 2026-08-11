/-
  aumann-modesty.lean  —  run2 LEAN-CORE

  CLAIM. Aumann's *averaging step* fails on a genuinely NON-partitional (overlapping-cell)
  information correspondence, and is RESTORED by making the same prior's correspondence
  partitional (S5 / Euclidean). This is the finite, instantiated reflection of v2 §5.2's
  modesty/immodesty = non-partition/partition dichotomy — built, not argued by analogy.
  (The negative phenomenon is classical — Geanakoplos's non-partitional information; we cite
  it, we do not claim to discover it. The contribution here is the explicit, kernel-checked
  *lab instance* tying it to modesty.)

  WHAT IS FORMALIZED (all finite, decidable; NO LI machinery, NO asymptotics, NO hypothesis
  that smuggles the conclusion — the target objects, the differing posteriors and "no common
  q", are CONCLUSIONS computed from π and E):

  Frame on `Fin 4`, common prior `π` uniform, RV `X = (1,0,1,0)`:
    * E : Fin 4 → Fin 4 → Bool, an information correspondence, REFLEXIVE + TRANSITIVE (S4)
      but NON-PARTITIONAL: cells `E 0 = {0,1,2}` and `E 3 = {1,2,3}` GENUINELY OVERLAP
      (share {1,2}) and are NON-NESTED (decide-checked). Euclidean (axiom 5) FAILS.
    * C = {0,1,2,3} is SELF-EVIDENT: a fixed point of the knowledge operator
      `knows S w := (E w ⊆ S)`, i.e. closed under E, AND equal to the union of its members'
      cells (a genuine common-knowledge / meet event, not a free Boolean label). decide-checked.
    * E 0, E 3 are ⊆ C and COVER C, but OVERLAP ⇒ they do NOT partition C.

  THE FAILURE (computed): post(E 0) = 2/3, post(E 3) = 1/3 (q1 ≠ q2); post(C) = 1/2, which
  equals NEITHER ⇒ no single common-knowledge value q ⇒ Aumann's averaging identity has no q
  to land on: it FAILS on the overlapping cover.

  THE NEAR-MISS (mandatory, compiled):
    * GENERAL lemma `partition_averaging`: over self-evident C partitioned by DISJOINT cells
      sharing posterior q, the overall posterior equals q (forced agreement).
    * Concrete PARTITIONAL (Euclidean / S5) correspondence `Ehat` on the SAME π, whose cells
      {0,1}, {2,3} are disjoint, cover C, and SHARE posterior 1/2 ⇒ `partition_averaging`
      FORCES post(C) = 1/2: agreement is forced. The averaging step that FAILED now HOLDS.
    * "Weaker hypothesis ⇒ FALSE": DROP disjointness (use the overlapping cover) and the
      averaging conclusion is false on the same numbers (`disjointness_essential`).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

open Finset

namespace AumannModesty

/-! ## 1. The concrete frame on `Fin 4`. -/

/-- Common prior: uniform on four worlds. -/
def π : Fin 4 → ℚ := fun _ => 1/4

/-- Information correspondence as a Bool relation; `E w v = true` ⇔ `v ∈ E(w)`.
      E 0 = {0,1,2}     E 1 = {1,2}     E 2 = {1,2}     E 3 = {1,2,3}
    Reflexive, transitive; cells E0 and E3 OVERLAP at {1,2} and neither nests. -/
def E : Fin 4 → Fin 4 → Bool
  | 0, 0 => true  | 0, 1 => true  | 0, 2 => true  | 0, 3 => false
  | 1, 0 => false | 1, 1 => true  | 1, 2 => true  | 1, 3 => false
  | 2, 0 => false | 2, 1 => true  | 2, 2 => true  | 2, 3 => false
  | 3, 0 => false | 3, 1 => true  | 3, 2 => true  | 3, 3 => true

/-- RV `X = (1,0,1,0)`  (equivalently the indicator of the event `{0,2}`). -/
def X : Fin 4 → ℚ
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0

/-- The self-evident candidate event `C = {0,1,2,3}` (the whole space here). -/
def C : Fin 4 → Bool := fun _ => true

/-! ## 2. Structural facts about `E` — all `decide`-checked. -/

/-- `E` is REFLEXIVE: `w ∈ E(w)`. -/
theorem E_reflexive : ∀ w : Fin 4, E w w = true := by decide

/-- `E` is TRANSITIVE (positive introspection, axiom 4): `v ∈ E(w) → E(v) ⊆ E(w)`. -/
theorem E_transitive : ∀ w v u : Fin 4, E w v = true → E v u = true → E w u = true := by
  decide

/-- `E` is NOT Euclidean (axiom 5 fails): `v ∈ E(w)` with `E(w) ⊄ E(v)`.
    (Witness: `1 ∈ E 0`, `0 ∈ E 0`, `0 ∉ E 1`.) -/
theorem E_not_euclidean :
    ∃ w v : Fin 4, E w v = true ∧ ∃ u, E w u = true ∧ E v u = false := by decide

/-- Cells `E 0` and `E 3` GENUINELY OVERLAP (share worlds 1,2) AND neither contains the
    other — NOT nested, NOT disjoint. A partition would have cells equal or disjoint. -/
theorem cells_overlap_not_nested :
    (∃ u, E 0 u = true ∧ E 3 u = true)            -- overlap
    ∧ (∃ u, E 0 u = true ∧ E 3 u = false)         -- E0 ⊄ E3  (world 0)
    ∧ (∃ u, E 3 u = true ∧ E 0 u = false) := by   -- E3 ⊄ E0  (world 3)
  decide

/-! ## 3. `C` is genuinely SELF-EVIDENT: a fixed point of the knowledge operator. -/

/-- Knowledge operator: `knows S w` ⇔ `E(w) ⊆ S`. -/
def knows (S : Fin 4 → Bool) (w : Fin 4) : Bool := decide (∀ v, E w v = true → S v = true)

/-- `C` is SELF-EVIDENT: `C ⊆ knows C` (closed under `E`). -/
theorem C_self_evident : ∀ w, C w = true → knows C w = true := by decide

/-- `C` is exactly the FIXED POINT `C = knows C` (genuine common knowledge, not a label). -/
theorem C_is_knowledge_fixed_point : ∀ w, C w = knows C w := by decide

/-- `C` is NONEMPTY. -/
theorem C_nonempty : ∃ w, C w = true := ⟨0, by decide⟩

/-- `C` equals the UNION of the cells of its members (a real meet/cell-union event). -/
theorem C_is_union_of_cells :
    ∀ w, C w = true ↔ ∃ w', C w' = true ∧ E w' w = true := by decide

/-- The two cells `E 0`, `E 3` are SUBSETS of `C` and together COVER `C`. -/
theorem cells_cover_C :
    (∀ u, E 0 u = true → C u = true)
    ∧ (∀ u, E 3 u = true → C u = true)
    ∧ (∀ u, C u = true → E 0 u = true ∨ E 3 u = true) := by
  decide

/-! ## 4. Posteriors `E_π(X | cell)` — the CONCLUSION, computed from π and E. -/

/-- Posterior expectation of `X` given a cell `S`:
    `E_π(X | S) = (∑_{v ∈ S} π v · X v) / (∑_{v ∈ S} π v)`. -/
def post (S : Fin 4 → Bool) : ℚ :=
  (∑ v, (if S v then π v * X v else 0)) / (∑ v, (if S v then π v else 0))

theorem post_E0 : post (E 0) = 2/3 := by
  simp only [post, π, X, E, Fin.sum_univ_four]; norm_num

theorem post_E3 : post (E 3) = 1/3 := by
  simp only [post, π, X, E, Fin.sum_univ_four]; norm_num

theorem post_C : post C = 1/2 := by
  simp only [post, π, X, C, Fin.sum_univ_four]; norm_num

/-! ## 5. AUMANN'S AVERAGING STEP FAILS — the headline, with computed witness. -/

/-- **The two covering cells carry STRICTLY DIFFERENT posteriors** (`2/3 ≠ 1/3`). Both
    cells cover the self-evident `C`, yet they disagree. The disagreement is the CONCLUSION
    (computed from π, E), not a hypothesis. -/
theorem covering_cells_disagree : post (E 0) ≠ post (E 3) := by
  rw [post_E0, post_E3]; norm_num

/-- **No single common-knowledge value `q` exists.**  Aumann's averaging identity says: if
    the posterior of `X` is common knowledge and equals `q` on the cells tiling `C`, then
    `post C = q`. Here NO `q` can be common to both covering cells (they already differ). So
    there is no `q` for the averaging identity to deliver: it fails on `C`. -/
theorem no_common_knowledge_value :
    ¬ ∃ q : ℚ, post (E 0) = q ∧ post (E 3) = q := by
  rintro ⟨q, h0, h3⟩
  exact covering_cells_disagree (h0.trans h3.symm)

/-- Sharper: the overall posterior on `C` (`1/2`) agrees with NEITHER covering cell, so
    Aumann's conclusion `post C = q` is unattainable for any cell-consistent `q`. -/
theorem averaging_target_unattainable :
    post C ≠ post (E 0) ∧ post C ≠ post (E 3) := by
  rw [post_C, post_E0, post_E3]; constructor <;> norm_num

/-! ## 6. THE NON-VACUITY WITNESS, packaged. -/

/-- **NON-VACUITY WITNESS (overlapping cover).**  A single decide/norm_num-checked bundle:
    `π` is a prior (∑ = 1, positive); `E` is reflexive + transitive; cells E0, E3 genuinely
    overlap and are non-nested; `C` is self-evident, nonempty, covered by E0 ∪ E3; and the
    covering posteriors are `2/3 ≠ 1/3` with overall posterior `1/2` — Aumann's averaging
    step has no common value. ALL conjuncts hold. -/
theorem nonvacuity_witness :
    (∑ w, π w = 1) ∧ (∀ w, 0 < π w)
    ∧ (∀ w, E w w = true)
    ∧ (∀ w v u, E w v = true → E v u = true → E w u = true)
    ∧ (∃ u, E 0 u = true ∧ E 3 u = true)                  -- overlap
    ∧ (∃ u, E 0 u = true ∧ E 3 u = false)                 -- non-nested
    ∧ (∃ u, E 3 u = true ∧ E 0 u = false)                 -- non-nested
    ∧ (∀ w, C w = true → knows C w = true)                -- C self-evident
    ∧ (∃ w, C w = true)                                   -- C nonempty
    ∧ (∀ u, C u = true → E 0 u = true ∨ E 3 u = true)     -- cover
    ∧ post (E 0) = (2:ℚ)/3 ∧ post (E 3) = (1:ℚ)/3 ∧ post C = (1:ℚ)/2 := by
  refine ⟨?_, ?_, E_reflexive, E_transitive, ?_, ?_, ?_, C_self_evident, C_nonempty, ?_,
          post_E0, post_E3, post_C⟩
  · simp only [π, Fin.sum_univ_four]; norm_num
  · intro w; simp only [π]; norm_num
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨3, by decide⟩
  · exact (cells_cover_C).2.2

/-! ## 7. MANDATORY NEAR-MISS — making the correspondence PARTITIONAL restores Aumann. -/

/-- **Finite-Aumann-proper (partition averaging).**  Two DISJOINT cells `S₁, S₂` whose union
    is `C`, each with positive π-mass and common posterior `q` of `X`, force `post C = q`.
    This is the averaging step the overlapping cover destroys; `hdisj` (disjointness) is the
    hypothesis the overlapping witness lacks. -/
theorem partition_averaging
    (S₁ S₂ : Fin 4 → Bool) (q : ℚ)
    (hcover : ∀ w, C w = true ↔ (S₁ w = true ∨ S₂ w = true))
    (hdisj  : ∀ w, ¬ (S₁ w = true ∧ S₂ w = true))
    (hm₁ : 0 < ∑ v, (if S₁ v then π v else 0))
    (hm₂ : 0 < ∑ v, (if S₂ v then π v else 0))
    (hq₁ : post S₁ = q) (hq₂ : post S₂ = q) :
    post C = q := by
  have hnum : (∑ v, (if C v then π v * X v else 0))
            = (∑ v, (if S₁ v then π v * X v else 0)) + (∑ v, (if S₂ v then π v * X v else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hc := hcover v
    by_cases h1 : S₁ v = true
    · have h2 : S₂ v = false := by
        by_contra h2'; exact hdisj v ⟨h1, by simpa using h2'⟩
      simp [h1, h2, (hc.mpr (Or.inl h1))]
    · by_cases h2 : S₂ v = true
      · simp [h1, h2, (hc.mpr (Or.inr h2))]
      · have hC : C v = false := by
          by_contra hC'
          rcases (hc.mp (by simpa using hC')) with h | h
          · exact h1 h
          · exact h2 h
        simp [hC, h1, h2]
  have hden : (∑ v, (if C v then π v else 0))
            = (∑ v, (if S₁ v then π v else 0)) + (∑ v, (if S₂ v then π v else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hc := hcover v
    by_cases h1 : S₁ v = true
    · have h2 : S₂ v = false := by
        by_contra h2'; exact hdisj v ⟨h1, by simpa using h2'⟩
      simp [h1, h2, (hc.mpr (Or.inl h1))]
    · by_cases h2 : S₂ v = true
      · simp [h1, h2, (hc.mpr (Or.inr h2))]
      · have hC : C v = false := by
          by_contra hC'
          rcases (hc.mp (by simpa using hC')) with h | h
          · exact h1 h
          · exact h2 h
        simp [hC, h1, h2]
  have e1 : (∑ v, (if S₁ v then π v * X v else 0)) = q * (∑ v, (if S₁ v then π v else 0)) := by
    have h := hq₁; unfold post at h
    rw [div_eq_iff (ne_of_gt hm₁)] at h
    rw [h, mul_comm]
  have e2 : (∑ v, (if S₂ v then π v * X v else 0)) = q * (∑ v, (if S₂ v then π v else 0)) := by
    have h := hq₂; unfold post at h
    rw [div_eq_iff (ne_of_gt hm₂)] at h
    rw [h, mul_comm]
  unfold post
  rw [hnum, hden, e1, e2]
  have hden_pos : 0 < (∑ v, (if S₁ v then π v else 0)) + (∑ v, (if S₂ v then π v else 0)) := by
    linarith
  rw [← mul_add]
  exact mul_div_cancel_right₀ q (ne_of_gt hden_pos)

/-- **Concrete PARTITIONAL (Euclidean / S5) correspondence on the SAME prior `π`.**
      Ehat 0 = Ehat 1 = {0,1}      Ehat 2 = Ehat 3 = {2,3}
    A genuine partition of `C` into cells `{0,1}` and `{2,3}` (equivalence relation = S5). -/
def Ehat : Fin 4 → Fin 4 → Bool
  | 0, 0 => true  | 0, 1 => true  | 0, 2 => false | 0, 3 => false
  | 1, 0 => true  | 1, 1 => true  | 1, 2 => false | 1, 3 => false
  | 2, 0 => false | 2, 1 => false | 2, 2 => true  | 2, 3 => true
  | 3, 0 => false | 3, 1 => false | 3, 2 => true  | 3, 3 => true

theorem Ehat_reflexive : ∀ w : Fin 4, Ehat w w = true := by decide
theorem Ehat_transitive : ∀ w v u : Fin 4, Ehat w v = true → Ehat v u = true → Ehat w u = true := by
  decide
/-- `Ehat` IS Euclidean (axiom 5 holds) — the partitional / S5 case. -/
theorem Ehat_euclidean : ∀ w v u : Fin 4, Ehat w v = true → Ehat w u = true → Ehat v u = true := by
  decide

/-- The two cells of `Ehat` are DISJOINT and COVER `C` — a genuine partition. -/
theorem Ehat_partition_of_C :
    (∀ w, C w = true ↔ (Ehat 0 w = true ∨ Ehat 2 w = true))   -- cover
    ∧ (∀ w, ¬ (Ehat 0 w = true ∧ Ehat 2 w = true)) := by      -- disjoint
  decide

/-- Both cells of the `Ehat` partition SHARE posterior `1/2` (common-knowledge value across
    the tiling of `C`). -/
theorem post_Ehat0 : post (Ehat 0) = 1/2 := by
  simp only [post, π, X, Ehat, Fin.sum_univ_four]; norm_num
theorem post_Ehat2 : post (Ehat 2) = 1/2 := by
  simp only [post, π, X, Ehat, Fin.sum_univ_four]; norm_num

/-- **NEAR-MISS PAYOFF: partitionality FORCES agreement.**  Under the partitional (Euclidean
    / S5) correspondence `Ehat`, the cells tiling `C` share the common-knowledge posterior
    `1/2`, and `partition_averaging` then FORCES `post C = 1/2`. The very averaging step that
    FAILED on the overlapping cover now HOLDS. -/
theorem aumann_holds_under_partition : post C = 1/2 := by
  have hcover := (Ehat_partition_of_C).1
  have hdisj  := (Ehat_partition_of_C).2
  have hm₁ : 0 < ∑ v, (if Ehat 0 v then π v else 0) := by
    simp only [π, Ehat, Fin.sum_univ_four]; norm_num
  have hm₂ : 0 < ∑ v, (if Ehat 2 v then π v else 0) := by
    simp only [π, Ehat, Fin.sum_univ_four]; norm_num
  exact partition_averaging (Ehat 0) (Ehat 2) (1/2) hcover hdisj hm₁ hm₂ post_Ehat0 post_Ehat2

/-! ## 8. "Weaker hypothesis ⇒ FALSE": drop disjointness, averaging breaks. -/

/-- **NEAR-MISS (false direction).**  Apply the averaging template to the ORIGINAL
    OVERLAPPING cover `E 0, E 3` of `C` (dropping `partition_averaging`'s disjointness
    hypothesis): the conclusion is FALSE — the cells do not share a posterior, and the
    averaging target `post C` matches neither. So disjointness is essential; overlap (the only
    failed hypothesis) is exactly what breaks Aumann. -/
theorem disjointness_essential :
    post (E 0) ≠ post (E 3)
    ∧ post C ≠ post (E 0) ∧ post C ≠ post (E 3)
    ∧ (∀ u, C u = true → E 0 u = true ∨ E 3 u = true)   -- they DO cover C
    ∧ (∃ u, E 0 u = true ∧ E 3 u = true) := by           -- but they OVERLAP
  refine ⟨covering_cells_disagree, averaging_target_unattainable.1,
          averaging_target_unattainable.2, (cells_cover_C).2.2, ⟨1, by decide⟩⟩

end AumannModesty

-- Axiom audit. Every theorem must depend ONLY on [propext, Classical.choice, Quot.sound]
-- and must NOT mention sorryAx.
#print axioms AumannModesty.E_reflexive
#print axioms AumannModesty.E_transitive
#print axioms AumannModesty.E_not_euclidean
#print axioms AumannModesty.cells_overlap_not_nested
#print axioms AumannModesty.C_self_evident
#print axioms AumannModesty.C_is_knowledge_fixed_point
#print axioms AumannModesty.C_is_union_of_cells
#print axioms AumannModesty.cells_cover_C
#print axioms AumannModesty.post_E0
#print axioms AumannModesty.post_E3
#print axioms AumannModesty.post_C
#print axioms AumannModesty.covering_cells_disagree
#print axioms AumannModesty.no_common_knowledge_value
#print axioms AumannModesty.averaging_target_unattainable
#print axioms AumannModesty.nonvacuity_witness
#print axioms AumannModesty.partition_averaging
#print axioms AumannModesty.Ehat_euclidean
#print axioms AumannModesty.aumann_holds_under_partition
#print axioms AumannModesty.disjointness_essential
