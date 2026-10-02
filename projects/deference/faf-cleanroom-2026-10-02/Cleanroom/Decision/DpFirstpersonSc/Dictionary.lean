import Cleanroom.Found.DpCoreTree.SeedMax
import Cleanroom.Found.DpCoreTree.Shadow

/-!
# Dictionary rows with Lean content: T20 (dossier) and Q11's finite dependence — T11 and T16(a)
of [[dp-firstperson-sc-mandate]]

* **T20** (`value_ofFun_eq_value'`): for a pure procedure `π`, Definition 6's value equals
  Definition 6′'s shared-seed value — `dp-core-tree`'s `value'_ofFun`, read as the dossier's
  exact dictionary row `𝔼_X[u(O,·)] = V_B(O)` with `X := ⊗β_n` the chance profiles and
  `u(O,x) := r(leaf(O,x))`: for a pure `π` the seed walk is deterministic in the actions, so
  `value'` is the chance-profile expectation of the payoff at the leaf `π` and the profile
  determine (`leafLaw'_ofFun`; the product-mixture form over seeds is
  `value'_eq_product_mixture`). Only `value'` is used (DNI-6/T20's "uses only `value'`"); the
  `CartesianFrames` enrichment is out of scope.
* **T16(a), Q11 as a necessary condition** (`shadow_congr_queried`, `FiniteDependence`,
  `not_realizable_of_not_finiteDependence`): the shadow of a finite tree depends on `C` only
  through `C d`, `d ∈ queried B` (`dp-core-tree`'s `leafLaw_congr_queried`); so every
  tree-realizable functional has *finite dependence*, and the infinite-family functional, which
  has none (`infiniteFamily_not_finiteDependence`), is realized by no tree — the restatement of
  dp-core-006 (`not_shadow_of_infinite_family`, whose argument is the same two lines).
  Continuity in the product topology (T16(b)) and the two-point exact image (T16(c)) are stretch
  and not built; Remark 7.3's free-monad reading and the universe caveat are recorded in the
  report.

The remaining rows of T11 — T9 (= T4(a)), T7 (= T6(a)(b)), the ten-word vocabulary and the
do-not-cite list — are prose: `dp-firstperson-sc-report.md` §Vocabulary and §Do-not-cite.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- **T20 (dossier), the pure-procedure identity**: Definition 6's value of a pure procedure is
its shared-seed value — the chance-profile expectation `𝔼_{⊗β}[r(leaf(π, ·))]` of the frame
reading, in `dp-core-tree`'s objects.
Source: `bridge-dossier.md` T20 ("`𝔼_X[u(O,·)] = V_B(O)` for every pure procedure `O` … exact for
pure profiles"); `seeds.md` SE-1(b); [[decision-problems-v2]] Remark 3.2
Kind: L
Fidelity: exact (pure procedures; the identification of leaves consistent with `π` with chance
profiles is `leafLaw'_ofFun`)
Hyps: none -/
theorem value_ofFun_eq_value' (π : (d : ι) → acts d) (B : Tree Ω ι acts K) :
    value (Proc.ofFun π) B = value' (Proc.ofFun π) B :=
  (value'_ofFun π B).symm

/-- The shadow of a tree depends on `C` only through the queried points.
Source: [[decision-problems-v2]] §3.1 ("no run touching finitely many points"); `dp-core-tree`
`leafLaw_congr_queried`
Kind: L -/
theorem shadow_congr_queried {C C' : Proc ι acts K} (B : Tree Ω ι acts K)
    (h : ∀ d ∈ queried B, C d = C' d) : shadow C B = shadow C' B := by
  funext x
  unfold shadow
  exact Finset.sum_congr rfl fun ℓ _ => by rw [leafLaw_congr_queried B h ℓ]

/-- **Finite dependence**: a functional of procedures depends on finitely many coordinates.
Source: [[decision-problems-v2]] Q11; the drafting chat (`2026-07-02…b8914860.md` lines
3011–3027: "dependence on finitely many coordinates")
Kind: D -/
def FiniteDependence (F : Proc ι acts K → (Ω × K → K)) : Prop :=
  ∃ S : Finset ι, ∀ C C' : Proc ι acts K, (∀ d ∈ S, C d = C' d) → F C = F C'

/-- **T16(a), Q11's necessary condition**: a functional realized as the shadow of some finite
tree has finite dependence (on `queried B`); contrapositively, a functional without finite
dependence is tree-realizable by no tree. This is dp-core-006's non-surjectivity restated as a
*necessary condition*.
Source: [[decision-problems-v2]] Q11, §3.1 ("some extensional functionals are realized by no
tree"); the drafting chat lines 3011–3027
Kind: C
Fidelity: exact
Hyps: none -/
theorem not_realizable_of_not_finiteDependence (F : Proc ι acts K → (Ω × K → K))
    (hF : ¬ FiniteDependence F) (B : Tree Ω ι acts K) : ¬ ∀ C, shadow C B = F C := by
  intro hreal
  apply hF
  refine ⟨queried B, fun C C' h => ?_⟩
  rw [← hreal C, ← hreal C', shadow_congr_queried B h]

/-- **The infinite-family functional has no finite dependence**: for any finite `S`, some point
of the family lies outside `S`, and flipping the designated action there changes the value.
Source: [[decision-problems-v2]] §3.1 (the infinite-family counterexample); `dp-core-tree`
`not_shadow_of_infinite_family` (the same two lines inside its proof)
Kind: N+
Fidelity: exact
Hyps: (a) `e` injective, (a) two actions at every family point -/
theorem infiniteFamily_not_finiteDependence [DecidableEq K]
    (e : ℕ → ι) (he : Function.Injective e) (t : (d : ι) → acts d)
    (h2 : ∀ i, 2 ≤ Fintype.card (acts (e i))) (ω : Ω) :
    ¬ FiniteDependence (infiniteFamilyFunctional e t ω : Proc ι acts K → (Ω × K → K)) := by
  rintro ⟨S, hS⟩
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset (S.preimage e he.injOn)
  rw [Finset.mem_preimage] at hj
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by have := h2 j; omega) (t (e j))
  set C₁ : Proc ι acts K := Proc.ofFun t with hC₁
  set C₂ : Proc ι acts K := C₁.deviatePure (e j) b with hC₂
  have hagree : ∀ d ∈ S, C₁ d = C₂ d := by
    intro d hd
    have hne : d ≠ e j := fun h => hj (h ▸ hd)
    simp [hC₂, Proc.deviatePure, Proc.deviate_ne _ _ hne]
  have h1 : infiniteFamilyFunctional e t ω C₁ (ω, 1) = 1 := by
    simp only [infiniteFamilyFunctional]
    rw [if_pos]
    · simp
    · intro i; rfl
  have h2' : infiniteFamilyFunctional e t ω C₂ (ω, 1) = 0 := by
    simp only [infiniteFamilyFunctional]
    rw [if_neg]
    · simp
    · intro hall
      have := hall j
      simp only [hC₂, Proc.deviatePure, Proc.deviate_same] at this
      exact hb (FinDistr.pure_injective this)
  have := congrFun (hS C₁ C₂ hagree) (ω, 1)
  rw [h1, h2'] at this
  exact one_ne_zero this

/-- The infinite-family functional is tree-realizable by no tree, via finite dependence (the
restatement of `not_shadow_of_infinite_family`).
Source: [[decision-problems-v2]] §3.1; Q11
Kind: C -/
theorem infiniteFamily_not_realizable' [DecidableEq K]
    (e : ℕ → ι) (he : Function.Injective e) (t : (d : ι) → acts d)
    (h2 : ∀ i, 2 ≤ Fintype.card (acts (e i))) (ω : Ω) (B : Tree Ω ι acts K) :
    ¬ ∀ C : Proc ι acts K, shadow C B = infiniteFamilyFunctional e t ω C :=
  not_realizable_of_not_finiteDependence _ (infiniteFamily_not_finiteDependence e he t h2 ω) B

end Cleanroom.Decision.DpFirstpersonSc
