import Cleanroom.Found.DpCoreTree.Overwrite
import Cleanroom.Decision.DpCausalConsist.Dags
import Cleanroom.Decision.DpCausalConsist.Mixture

/-!
# `dp-causal-consist`: the overwrite tree's temporal structure — Corollary 3.1(b) at a
non-recorded point, and the non-responsiveness contrast (T4(b), T6; repair round 1)

`dp-core-tree`'s `overwrite` (`ℓ ∼ Bern(½)`; query `d` drawing `m'`; on the lesion branch a coin
with `δ = ½` overwrites `m := 1`; `k ∼ Bern(γ_ℓ)`, `γ = (¼, ¾)`; leaf `(ℓ, m, k)`) is **not**
Definition-7 recorded at `d` (`overwrite_not_recordsFor`, imported: action-veridicality fails on
the overwritten run). Its world law at `C(d) = ½` is `owP` on `Fin 3 → Bool` (`owP_mass`: every
mass is `ν{x}`), which factorizes over the temporal DAG `ℓ → m`, `ℓ → k` (`sOw_isFor`; `pa(m) =
{ℓ}` pre-query, `k` reads `ℓ` only).

* **T4(b)**: the temporal structure's truncated law is **not** the calibrated act-conditional
  (`overwrite_truncate_ne_cond`): `P^{do m}(k) = ½` for both acts (Pearl: `k ∈ nondesc(m)`) while
  `P(k | m = 1) = 11/20`, `P(k | m = 0) = 5/12`. Theorem 3(ii)'s conclusion fails exactly where its
  recording hypothesis fails.
* **T6, the contrast**: `cf^G` of the temporal DAG holds `{ℓ = 1}` fixed (`½` under both
  interventions, Pearl's invariance), while conditioning on the act moves it: `P(ℓ = 1 | m = 1)
  = 3/5 ≠ ½` (`overwrite_contrast`; this is `overwrite_m_not_indep_lesion`'s `3/8 ≠ 5/8 · ½` as a
  conditional). On a recorded point both are non-responsive on `𝓔₀^G ∩ ⟨V₀⟩`
  (`nonResponsive_shared`), so the property separates nothing there; what it separates is the
  choice of `𝓔₀`, visible only off the recorded points.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

/-! ## The temporal DAG `ℓ → m`, `ℓ → k` -/

/-- `ℓ → m`, `ℓ → k` (the temporal DAG of the overwrite and bypass trees: `m` reads `ℓ`, `k`
reads `ℓ`, no `m → k`). Source: mandate T4(b) ("the compatible temporal structure"), T3(C). Kind: D -/
def gLmLk : Digraph (Fin 3) := dag3 fun a b => decide ((a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2))

instance : DecidableRel gLmLk.Adj := inferInstanceAs (DecidableRel (dag3 _).Adj)

/-- `gLmLk` is acyclic (rank `ℓ < k < m`). Source: none: infrastructure. Kind: L -/
theorem gLmLk_rank : ∀ u v, gLmLk.Adj u v → rankLKM u < rankLKM v := by decide

/-- The parents in `gLmLk`. Source: none: infrastructure. Kind: L -/
theorem gLmLk_parents : gLmLk.parents 0 = ∅ ∧ gLmLk.parents 1 = {0} ∧ gLmLk.parents 2 = {0} := by
  decide

/-- `k ∈ nondesc(m)` in `gLmLk`. Source: none: infrastructure. Kind: L -/
theorem gLmLk_k_nondesc : (2 : Fin 3) ∈ nondesc gLmLk 1 :=
  mem_nondesc_of_rank gLmLk rankLKM gLmLk_rank (by decide) (by decide)

/-- `ℓ ∈ nondesc(m)` in `gLmLk`. Source: none: infrastructure. Kind: L -/
theorem gLmLk_l_nondesc : (0 : Fin 3) ∈ nondesc gLmLk 1 :=
  mem_nondesc_of_rank gLmLk rankLKM gLmLk_rank (by decide) (by decide)

/-- A coordinate event `{x_v = 1}` is in the fixed algebra of `m` when `v ∈ nondesc(m)`.
Source: none: infrastructure
Kind: L -/
theorem coord_inFixedAlgebra (G : Digraph (Fin 3)) (v : Fin 3) (hv : v ∈ nondesc G 1) :
    InFixedAlgebra G 1 (Finset.univ.filter fun x : W3 => x v = true) := by
  intro x y hxy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hxy v hv]

/-! ## The overwrite law on `W3` -/

/-- The world masses of the overwrite tree at `C(d) = ½`, as a table: `ν(ℓ, m, k) = ½ · P(m | ℓ) ·
γ_ℓ(k)` with `P(m = 1 | ℓ = 1) = ¾` (the draw `½` or the overwrite), `P(m = 1 | ℓ = 0) = ½`,
`γ = (¼, ¾)`.
Source: dp-core-083 (`overwrite`'s own parameters `½, ½`); mandate T4(b)
Kind: D -/
def owMassQ (ℓ m k : Bool) : ℚ :=
  (1/2) * (if ℓ then (if m then 3/4 else 1/4) else 1/2)
    * (if k then (if ℓ then 3/4 else 1/4) else (if ℓ then 1/4 else 3/4))

/-- `ν{(ℓ, m, k)}` on the overwrite tree is the table. Source: none: infrastructure. Kind: L -/
theorem overwrite_nu_singleton (ℓ m k : Bool) :
    nu owProc overwrite {(ℓ, m, k)} = owMassQ ℓ m k := by
  rw [overwrite_nu]
  simp only [overwrite_leafLaw]
  cases ℓ <;> cases m <;> cases k <;>
    simp [Fin.sum_univ_two, Fintype.sum_bool, owM, owMassQ] <;> norm_num

/-- The overwrite law as a `Distr` on `W3` (coordinates `ℓ, m, k`).
Source: mandate T4(b) (`overwrite` at its own parameters)
Kind: D -/
noncomputable def owP : Distr W3 :=
  distr3 (fun ℓ m k => ((owMassQ ℓ m k : ℚ) : ℝ))
    (fun a b c => by cases a <;> cases b <;> cases c <;> norm_num [owMassQ])
    (by norm_num [owMassQ])

/-- **`owP` is the overwrite tree's world law**: every mass is `ν{x}` (the calibrated state at
`O = ⊤`). Source: mandate §3.3 (the seam); T4(b). Kind: L -/
theorem owP_mass (ℓ m k : Bool) :
    owP.mass (pt3 ℓ m k) = ((nu owProc overwrite {(ℓ, m, k)} : ℚ) : ℝ) := by
  rw [overwrite_nu_singleton]; rfl

/-- The rate table of the overwrite tree's temporal structure. Source: mandate T4(b). Kind: D -/
noncomputable def rOw : Rate3 where
  r v ℓ _ _ := match v with
    | 0 => 1/2
    | 1 => if ℓ then 3/4 else 1/2
    | 2 => if ℓ then 3/4 else 1/4
  nonneg v a b c := by fin_cases v <;> cases a <;> norm_num
  le_one v a b c := by fin_cases v <;> cases a <;> norm_num

/-- **The overwrite tree's temporal structure** `ℓ → m`, `ℓ → k`. Source: mandate T4(b). Kind: D -/
noncomputable def sOw : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gLmLk, isAcyclic_of_rank _ _ gLmLk_rank, cpdOfRate gLmLk rOw⟩

/-- The temporal structure is compatible with the overwrite law. Source: mandate T4(b). Kind: N+ -/
theorem sOw_isFor : sOw.IsFor owP := by
  unfold sOw
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gLmLk_parents.1, gLmLk_parents.2.1, gLmLk_parents.2.2,
    Finset.notMem_empty, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [owP, owMassQ, rOw]

/-- `P(m = b) > 0` under the overwrite law. Source: none: infrastructure. Kind: L -/
theorem owP_m_pos (b : Bool) : 0 < owP.prob {x | x 1 = b} := by
  rw [prob3_eq]; cases b <;> norm_num [owP, owMassQ]

/-- `P(k = 1) = ½`, `P(ℓ = 1) = ½` under the overwrite law. Source: dp-core-083. Kind: N+ -/
theorem owP_k_l : owP.prob {x | x 2 = true} = 1/2 ∧ owP.prob {x | x 0 = true} = 1/2 := by
  constructor <;> (rw [prob3_eq]; norm_num [owP, owMassQ])

/-- `P(k = 1 | m = 1) = 11/20`, `P(k = 1 | m = 0) = 5/12` under the overwrite law.
Source: mandate T4(b) ("exact rationals")
Kind: N+ -/
theorem owP_k_given (b : Bool) :
    owP.condProb {x | x 2 = true} {x | x 1 = b} = if b then 11/20 else 5/12 := by
  unfold Distr.condProb
  have : ({x : W3 | x 2 = true} ∩ {x | x 1 = b}) = {x | x 2 = true ∧ x 1 = b} := by ext x; simp
  rw [this, prob3_eq, prob3_eq]
  cases b <;> norm_num [owP, owMassQ]

/-- `P(ℓ = 1 | m = 1) = 3/5` under the overwrite law (the lesion is evidence of the act — the
cross-multiplied `overwrite_m_not_indep_lesion`, `3/8 ≠ 5/8 · ½`).
Source: dp-core-083; mandate T6 ("conditioning moves `{ℓ = 1}`")
Kind: N+ -/
theorem owP_l_given_m : owP.condProb {x | x 0 = true} {x | x 1 = true} = 3/5 := by
  unfold Distr.condProb
  have : ({x : W3 | x 0 = true} ∩ {x | x 1 = true}) = {x | x 0 = true ∧ x 1 = true} := by
    ext x; simp
  rw [this, prob3_eq, prob3_eq]
  norm_num [owP, owMassQ]

/-- The truncated `k`-rate of the temporal structure is the marginal `½` for both acts (Pearl's
invariance: `k ∈ nondesc(m)`). Source: mandate T4(b). Kind: C -/
theorem sOw_truncate_k (b : Bool) : (sOw.truncate 1 b).prob {x | x 2 = true} = 1/2 := by
  have hset : ({x : W3 | x 2 = true}) = ↑(Finset.univ.filter fun x : W3 => x 2 = true) := by
    ext x; simp
  rw [hset, CausalStructure.truncate,
    truncate_prob_eq_of_inFixedAlgebra sOw.acyclic sOw.φ sOw_isFor 1 b _
      (coord_inFixedAlgebra gLmLk 2 gLmLk_k_nondesc), ← hset, owP_k_l.1]

/-- The truncated `ℓ`-rate of the temporal structure is the marginal `½` for both acts.
Source: mandate T6 ("`cf^G` of the temporal DAG holds it"). Kind: C -/
theorem sOw_truncate_l (b : Bool) : (sOw.truncate 1 b).prob {x | x 0 = true} = 1/2 := by
  have hset : ({x : W3 | x 0 = true}) = ↑(Finset.univ.filter fun x : W3 => x 0 = true) := by
    ext x; simp
  rw [hset, CausalStructure.truncate,
    truncate_prob_eq_of_inFixedAlgebra sOw.acyclic sOw.φ sOw_isFor 1 b _
      (coord_inFixedAlgebra gLmLk 0 gLmLk_l_nondesc), ← hset, owP_k_l.2]

/-- **Corollary 3.1(b) on the overwrite tree**: the point is not Definition-7 recorded (imported),
and the compatible temporal structure's truncated law differs from the calibrated act-conditional
for both acts (`½` against `11/20`, `5/12` on `{k = 1}`).
Source: [[learning-cdt-renderings]] Corollary 3.1(b) ("at a non-recorded point the identity
fails"); mandate T4(b) (`overwrite`, action-veridicality failure)
Kind: N+
Fidelity: exact (`overwrite`'s own parameters `½, ½`; the world law is `ν` by `owP_mass`)
Hyps: (a) `sOw_isFor` -/
theorem overwrite_truncate_ne_cond :
    ¬ RecordsFor owObs owActEv owProc overwrite () ∧
    ∀ b, sOw.truncate 1 b ≠ condDistr owP {x | x 1 = b} (owP_m_pos b) := by
  refine ⟨overwrite_not_recordsFor, fun b h => ?_⟩
  have h1 := sOw_truncate_k b
  rw [h, condDistr_prob, owP_k_given] at h1
  cases b <;> norm_num at h1

/-- **The non-responsiveness contrast on the overwrite tree** (T6): `cf^G` of the temporal DAG
holds `{ℓ = 1}` at `½` under both interventions, while conditioning on the act moves it to `3/5`.
Source: [[learning-cdt-renderings]] "Non-responsiveness: form, not content" (the two coincide on
`𝓔₀^G ∩ ⟨V₀⟩` at recorded points; the overwrite tree is where they come apart); mandate T6
Kind: N+
Fidelity: exact -/
theorem overwrite_contrast :
    (∀ b, (sOw.truncate 1 b).prob {x | x 0 = true} = owP.prob {x | x 0 = true}) ∧
    owP.condProb {x | x 0 = true} {x | x 1 = true} ≠ owP.prob {x | x 0 = true} := by
  refine ⟨fun b => by rw [sOw_truncate_l, owP_k_l.2], ?_⟩
  rw [owP_l_given_m, owP_k_l.2]; norm_num

/-! ## Non-responsiveness is shared at recorded points -/

section shared

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)]
  {ι : Type} [DecidableEq ι] {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (obs : ι → Finset (Pt Val)) (actEv : (d : ι) → acts d → Finset (Pt Val))
  {C : Proc ι acts ℚ} {B : Tree (Pt Val) ι acts ℚ} {d : ι}

/-- **Non-responsiveness is shared on `𝓔₀^G ∩ ⟨V₀⟩` at a recorded point** (T6): for an event `X`
in the fixed algebra of a compatible structure *and* pre-query, both the interventional supposition
(every act) and the evidential conditional (every positive act) leave `P(X)` unchanged — the
property separates nothing there; the content of a CDT is the choice of `𝓔₀` (module docstring).
Source: [[learning-cdt-renderings]] "Non-responsiveness: form, not content" ("Every interventional
supposition is non-responsive on the algebra of the act's non-descendants … so is the evidential
conditional on the pre-query algebra at every recorded point"); mandate T6 (`nonResponsive_shared`)
Kind: L (the conjunction of Pearl's invariance `truncate_prob_eq_of_inFixedAlgebra` and
`edt_nonResponsive_preQuery`, no chaining — audit r2 fid N2 / adv N4)
Fidelity: exact
Hyps: (a) recording; (a) `0 < ν(O_d)`; (a) clause 1; (a) `Γ.IsFor P_{s_d}`; (a) `X ∈ 𝓔₀^G`;
(a) `X` pre-query; (a) `0 < P_{s_d}(b)` -/
theorem nonResponsive_shared (s : ι → State (Pt Val) ℚ) (hrec : RecordsFor obs actEv C B d)
    (hO : 0 < nu C B (obs d)) (h1 : StrictClause1At s obs C B d) (m : V)
    (Γ : CausalStructure Val) (hΓ : Γ.IsFor (State.toDistr (State.castℝ (s d)))) (a : Val m)
    (X : Finset (Pt Val)) (hX1 : InFixedAlgebra Γ.G m X) (hX2 : PreQuery obs C B d X)
    (b : acts d) (hb : 0 < (s d).pr (actEv d b)) :
    (Γ.truncate m a).prob ↑X = (State.toDistr (State.castℝ (s d))).prob ↑X ∧
    (jeffreyCond (s d) (actEv d b) hb).pr X = (s d).pr X :=
  ⟨by rw [CausalStructure.truncate]
      exact truncate_prob_eq_of_inFixedAlgebra Γ.acyclic Γ.φ hΓ m a X hX1,
    edt_nonResponsive_preQuery obs actEv s hrec hO h1 hX2 b hb⟩

end shared

end Cleanroom.Decision.DpCausalConsist
