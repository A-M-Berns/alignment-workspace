import Cleanroom.Corrigibility.CorrLegitGeneral.Eval
import Cleanroom.Corrigibility.CorrLegitGeneral.Compose
import Cleanroom.Found.LitDdbFrames.ExamplesFact21
import Cleanroom.Lit.LitDdbFacts.ExamplesFig5

/-!
# corr-legit-general — witnesses on three worlds: the composition counterexample (T6(c))

`π = (1/2, 1/4, 1/4)`, `φ = {0}`, `Q = {φ, ¬φ}`; `F₂` rows `(3/4, 1/4, 0), (1/2, 1/2, 0),
(1/2, 1/2, 0)`; `F₃` rows `(3/4, 1/4, 0), (1/4, 3/4, 0), (3/4, 0, 1/4)`. Local Total Trust on
`Q` at step one (the cuts at `3/4` and `1/2`), global Total Trust toward `F₃` at every
`F₂`-candidate (Theorem 4.1: `(3/4,1/4,0) = 2/3·δ₀ + 1/3·(1/4,3/4,0)`, `(1/4,3/4,0) = 2/3·δ₁ +
1/3·(3/4,1/4,0)`, `(1/2,1/2,0) = ½(3/4,1/4,0) + ½(1/4,3/4,0)`), and the composite fails local
Total Trust on `Q` at `X = 𝟙_φ`, `s = 3/4` (event `{0, 2}`, product sum `1/8 − 3/16 = −1/16`).
Diagnosis: every `F₂`-row is null at world `2` while `π(2) = 1/4`, so `π` is not a mixture of its
candidates — the hull half fails at step one, and `φ` does not see the `1/2` split that `F₃`'s
confidence is correlated with. `L = Ω` throughout: a fact about Total Trust itself, settling ddb
I15.2 (cross-frame non-transitivity); distinct from `tt-finite-frames`'
`T4.totalTrust_not_transitive` (one prior per agent).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples
  Cleanroom.Lit.LitDdbFacts.Examples

noncomputable section

/-- A convex combination of two points of a set lies in its hull.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_hull_of_comb2 {W : Type} {s : Set (W → ℝ)} {x y z : W → ℝ} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hz : z = a • x + b • y) :
    z ∈ convexHull ℝ s := by
  rw [hz]
  exact (convex_convexHull ℝ s) (subset_convexHull ℝ s hx) (subset_convexHull ℝ s hy) ha hb hab

/-- The informed expert, pointwise (by definition).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem informed_apply {W : Type} [Fintype W] [DecidableEq W] (F : Frame W) (ρ : W → ℝ) (w : W) :
    F.informed ρ w = if F.P w = ρ then ρ w / F.selfMass ρ else 0 := rfl

/-- The step-two frame `F₂`.
Source: [[legitimacy-general-final]] Proofs l. 142 (Statement 9(c))
Kind: D
Fidelity: exact -/
def cF2 : Frame (Fin 3) :=
  mk3 ![3 / 4, 1 / 4, 0] ![1 / 2, 1 / 2, 0] ![1 / 2, 1 / 2, 0]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The step-three frame `F₃`.
Source: [[legitimacy-general-final]] Proofs l. 142 (Statement 9(c))
Kind: D
Fidelity: exact -/
def cF3 : Frame (Fin 3) :=
  mk3 ![3 / 4, 1 / 4, 0] ![1 / 4, 3 / 4, 0] ![3 / 4, 0, 1 / 4]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The deferrer `(1/2, 1/4, 1/4)`.
Source: [[legitimacy-general-final]] Proofs l. 142
Kind: D
Fidelity: exact -/
def πc : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- The proposition `φ = {0}`.
Source: [[legitimacy-general-final]] Proofs l. 142
Kind: D
Fidelity: exact -/
abbrev φc : Finset (Fin 3) := {0}

/-- The rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF_P : (cF2.P 0 = ![3 / 4, 1 / 4, 0] ∧ cF2.P 1 = ![1 / 2, 1 / 2, 0] ∧
      cF2.P 2 = ![1 / 2, 1 / 2, 0]) ∧
    (cF3.P 0 = ![3 / 4, 1 / 4, 0] ∧ cF3.P 1 = ![1 / 4, 3 / 4, 0] ∧ cF3.P 2 = ![3 / 4, 0, 1 / 4]) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- `F₃`'s rows are pairwise distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF3_ne : (![3 / 4, 1 / 4, 0] : Fin 3 → ℝ) ≠ ![1 / 4, 3 / 4, 0] ∧
    (![3 / 4, 1 / 4, 0] : Fin 3 → ℝ) ≠ ![3 / 4, 0, 1 / 4] ∧
    (![1 / 4, 3 / 4, 0] : Fin 3 → ℝ) ≠ ![3 / 4, 0, 1 / 4] := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrFun h 0; norm_num at this
  · have := congrFun h 1; norm_num at this
  · have := congrFun h 0; norm_num at this

/-- `F₃`'s cells are singletons.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF3_cell : cF3.cell ![3 / 4, 1 / 4, 0] = {0} ∧ cF3.cell ![1 / 4, 3 / 4, 0] = {1} ∧
    cF3.cell ![3 / 4, 0, 1 / 4] = {2} := by
  obtain ⟨_, ⟨h0, h1, h2⟩⟩ := cF_P
  obtain ⟨n01, n02, n12⟩ := cF3_ne
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext w
      fin_cases w <;> simp +decide [Frame.mem_cell, h0, h1, h2, n01, n02, n12, n01.symm, n02.symm, n12.symm] <;>
        norm_num

/-- `F₂`'s rows' probabilities of `φ`: `3/4, 1/2, 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF2_mass_φ : mass (cF2.P 0) φc = 3 / 4 ∧ mass (cF2.P 1) φc = 1 / 2 ∧
    mass (cF2.P 2) φc = 1 / 2 := by
  obtain ⟨⟨h0, h1, h2⟩, _⟩ := cF_P
  refine ⟨?_, ?_, ?_⟩ <;> simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, h0, h1, h2, vec3_two] <;>
    norm_num

/-- **Step one: local Total Trust on `{φ, ¬φ}` toward `F₂`** (the cuts at `3/4` and `1/2`:
`π(φ | P(φ) ≥ 3/4) = 1`, `π(φ | P(φ) ≥ 1/2) = 1/2`, `π(φ | P(φ) ≤ 1/2) = 0`,
`π(φ | P(φ) ≤ 3/4) = 1/2`).
Source: [[legitimacy-general-final]] Proofs l. 142 ("Step 1 passes Simple Trust on φ")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem cF2_totalTrustWrt : TotalTrustWrt (questionOf φc) πc cF2 := by
  rw [totalTrustWrt_questionOf_iff (fun w => by fin_cases w <;> norm_num [πc, vec3_two])]
  obtain ⟨m0, m1, m2⟩ := cF2_mass_φ
  constructor
  · intro t
    rw [mass_probEvent_eq, mass_inter_probEvent_eq]
    simp only [Fin.sum_univ_three, m0, m1, m2]
    simp +decide [πc, vec3_two]
    split_ifs <;> (try norm_num) <;> (try linarith)
  · intro t
    rw [mass_probEventLE_eq, mass_inter_probEventLE_eq]
    simp only [Fin.sum_univ_three, m0, m1, m2]
    simp +decide [πc, vec3_two]
    split_ifs <;> (try norm_num) <;> (try linarith)

/-- The candidates of `π` under `F₂`: `{(3/4,1/4,0), (1/2,1/2,0)}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF2_cands : cF2.cands πc = {![3 / 4, 1 / 4, 0], ![1 / 2, 1 / 2, 0]} := by
  obtain ⟨⟨h0, h1, h2⟩, _⟩ := cF_P
  rw [cands_eq_triple cF2 (by norm_num [πc]) (by norm_num [πc]) (by norm_num [πc, vec3_two]),
    h0, h1, h2]
  ext σ; simp

/-- Supports of the two candidates: `{0, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cand_supp : supp (![3 / 4, 1 / 4, 0] : Fin 3 → ℝ) = {0, 1} ∧
    supp (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) = {0, 1} ∧
    supp (![1 / 4, 3 / 4, 0] : Fin 3 → ℝ) = {0, 1} := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext w; fin_cases w <;> simp [supp, vec3_two] <;> norm_num

/-- Candidates of the two candidates under `F₃`: both `{(3/4,1/4,0), (1/4,3/4,0)}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF3_cands : cF3.cands ![3 / 4, 1 / 4, 0] = {![3 / 4, 1 / 4, 0], ![1 / 4, 3 / 4, 0]} ∧
    cF3.cands ![1 / 2, 1 / 2, 0] = {![3 / 4, 1 / 4, 0], ![1 / 4, 3 / 4, 0]} ∧
    cF3.cands ![1 / 4, 3 / 4, 0] = {![3 / 4, 1 / 4, 0], ![1 / 4, 3 / 4, 0]} := by
  obtain ⟨_, ⟨h0, h1, _⟩⟩ := cF_P
  obtain ⟨s0, s1, s2⟩ := cand_supp
  refine ⟨?_, ?_, ?_⟩
  · rw [Frame.cands, s0, image_insert, image_singleton, h0, h1]
  · rw [Frame.cands, s1, image_insert, image_singleton, h0, h1]
  · rw [Frame.cands, s2, image_insert, image_singleton, h0, h1]

/-- Self-masses and informed experts of `F₃`'s first two rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF3_informed : cF3.selfMass ![3 / 4, 1 / 4, 0] = 3 / 4 ∧
    cF3.selfMass ![1 / 4, 3 / 4, 0] = 3 / 4 ∧
    cF3.informed ![3 / 4, 1 / 4, 0] = ![1, 0, 0] ∧ cF3.informed ![1 / 4, 3 / 4, 0] = ![0, 1, 0] := by
  obtain ⟨_, ⟨h0, h1, h2⟩⟩ := cF_P
  obtain ⟨n01, n02, n12⟩ := cF3_ne
  obtain ⟨c0, c1, _⟩ := cF3_cell
  have s0 : cF3.selfMass ![3 / 4, 1 / 4, 0] = 3 / 4 := by
    unfold Frame.selfMass; rw [c0, mass_singleton]; rfl
  have s1 : cF3.selfMass ![1 / 4, 3 / 4, 0] = 3 / 4 := by
    unfold Frame.selfMass; rw [c1, mass_singleton]; rfl
  refine ⟨s0, s1, ?_, ?_⟩
  · funext w
    fin_cases w
    · show cF3.informed ![3 / 4, 1 / 4, 0] 0 = ![1, 0, 0] 0
      rw [informed_apply, if_pos h0, s0]; norm_num
    · show cF3.informed ![3 / 4, 1 / 4, 0] 1 = ![1, 0, 0] 1
      rw [informed_apply, if_neg (by rw [h1]; exact n01.symm)]; simp
    · show cF3.informed ![3 / 4, 1 / 4, 0] 2 = ![1, 0, 0] 2
      rw [informed_apply, if_neg (by rw [h2]; exact n02.symm)]; simp [vec3_two]
  · funext w
    fin_cases w
    · show cF3.informed ![1 / 4, 3 / 4, 0] 0 = ![0, 1, 0] 0
      rw [informed_apply, if_neg (by rw [h0]; exact n01)]; simp
    · show cF3.informed ![1 / 4, 3 / 4, 0] 1 = ![0, 1, 0] 1
      rw [informed_apply, if_pos h1, s1]; norm_num
    · show cF3.informed ![1 / 4, 3 / 4, 0] 2 = ![0, 1, 0] 2
      rw [informed_apply, if_neg (by rw [h2]; exact n12.symm)]; simp [vec3_two]

/-- **`F₃`'s first two rows are modestly informed**: `(3/4,1/4,0) = 2/3·δ₀ + 1/3·(1/4,3/4,0)` and
`(1/4,3/4,0) = 2/3·δ₁ + 1/3·(3/4,1/4,0)`.
Source: [[legitimacy-general-final]] Proofs l. 142 (hull weights)
Kind: L
Fidelity: n/a -/
theorem cF3_modestlyInformed : cF3.ModestlyInformed ![3 / 4, 1 / 4, 0] ∧
    cF3.ModestlyInformed ![1 / 4, 3 / 4, 0] := by
  obtain ⟨s0, s1, i0, i1⟩ := cF3_informed
  obtain ⟨c0, _, c1⟩ := cF3_cands
  obtain ⟨n01, _, _⟩ := cF3_ne
  constructor
  · refine ⟨by rw [s0]; norm_num, ?_⟩
    rw [i0]
    have hcm : cF3.candsMinus ![3 / 4, 1 / 4, 0] = {![1 / 4, 3 / 4, 0]} := by
      rw [Frame.candsMinus, c0]
      exact erase_insert (by rw [mem_singleton]; exact n01)
    rw [hcm]
    exact mem_hull_of_comb2 (x := ![1, 0, 0]) (y := ![1 / 4, 3 / 4, 0])
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [vec3_two])
  · refine ⟨by rw [s1]; norm_num, ?_⟩
    rw [i1]
    have hcm : cF3.candsMinus ![1 / 4, 3 / 4, 0] = {![3 / 4, 1 / 4, 0]} := by
      rw [Frame.candsMinus, c1]
      ext σ
      simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hne, h | h⟩
        · exact h
        · exact absurd h hne
      · rintro rfl; exact ⟨n01, Or.inl rfl⟩
    rw [hcm]
    exact mem_hull_of_comb2 (x := ![0, 1, 0]) (y := ![3 / 4, 1 / 4, 0])
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [vec3_two])

/-- **Step two: every `F₂`-candidate totally trusts `F₃`** (Theorem 4.1 at each candidate:
`(3/4,1/4,0)` is its own candidate, `(1/2,1/2,0) = ½(3/4,1/4,0) + ½(1/4,3/4,0)`, and both
candidates are modestly informed).
Source: [[legitimacy-general-final]] Proofs l. 142 ("each ρ totally trusts the t₃-frame
globally")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem cF2_cands_totalTrust : ∀ ρ ∈ cF2.cands πc, TotalTrust ρ cF3 := by
  obtain ⟨_, ⟨h0, h1, _⟩⟩ := cF_P
  obtain ⟨c0, c1, _⟩ := cF3_cands
  obtain ⟨mi0, mi1⟩ := cF3_modestlyInformed
  have hmi : ∀ ρ ∈ ({![3 / 4, 1 / 4, 0], ![1 / 4, 3 / 4, 0]} : Finset (Fin 3 → ℝ)),
      cF3.ModestlyInformed ρ := by
    intro ρ hρ
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · exact mi0
    · exact mi1
  intro ρ hρ
  rw [cF2_cands] at hρ
  simp only [mem_insert, mem_singleton] at hρ
  rcases hρ with rfl | rfl
  · have hmem : (![3 / 4, 1 / 4, 0] : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) := h0 ▸ cF3.P_mem 0
    refine (totalTrust_iff_hullAndModestlyInformed hmem cF3).2 ⟨?_, by rw [c0]; exact hmi⟩
    rw [c0]
    exact subset_convexHull ℝ _ (by simp)
  · have hmem : (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) :=
      simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine (totalTrust_iff_hullAndModestlyInformed hmem cF3).2 ⟨?_, by rw [c1]; exact hmi⟩
    rw [c1]
    exact mem_hull_of_comb2 (x := ![3 / 4, 1 / 4, 0]) (y := ![1 / 4, 3 / 4, 0])
      (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num) (by ext w; fin_cases w <;> norm_num [vec3_two])

/-- **The composite fails local Total Trust on `{φ, ¬φ}`** at `X = 𝟙_φ`, `s = 3/4`: the event
`[P₃(φ) ≥ 3/4] = {0, 2}` and the product sum is `1/2·(1/4) + 1/4·(−3/4) = −1/16`.
Source: [[legitimacy-general-final]] Proofs l. 142 ("π(φ | {w₀, w₂}) = 2/3 < 3/4")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem cF3_not_totalTrustWrt : ¬ TotalTrustWrt (questionOf φc) πc cF3 := by
  intro h
  obtain ⟨_, ⟨h0, h1, h2⟩⟩ := cF_P
  have := h (ind φc) (measurableWrt_questionOf_ind φc) (3 / 4)
  simp only [Fin.sum_univ_three, E, h0, h1, h2, ind, πc] at this
  simp +decide [vec3_two] at this <;> norm_num at this

/-- **T6(c), packaged**: local trust at step one and global trust at step two, with the
composite failing — `L = Ω`, so this is a fact about Total Trust itself.
Source: [[legitimacy-general-final]] Statement 9(c) l. 67, Proofs l. 142; [[ddb]] I15.2;
corr-wf14b-057
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem compose_counterexample : πc ∈ stdSimplex ℝ (Fin 3) ∧
    TotalTrustWrt (questionOf φc) πc cF2 ∧ (∀ ρ ∈ cF2.cands πc, TotalTrust ρ cF3) ∧
    ¬ TotalTrustWrt (questionOf φc) πc cF3 :=
  ⟨simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), cF2_totalTrustWrt,
    cF2_cands_totalTrust, cF3_not_totalTrustWrt⟩

/-- **Diagnosis**: `π` is not a mixture of its `F₂`-candidates — every candidate is null at
world `2` while `π(2) = 1/4` — so the hull half (`MixtureOfCands`) fails at step one.
Source: [[legitimacy-general-final]] Proofs l. 142 ("every t₂-state puts mass 0 on w₂")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem compose_counterexample_diagnosis : ¬ MixtureOfCands cF2 πc := by
  rintro ⟨lam, _, heq⟩
  have h2 := congrFun heq 2
  rw [cF2_cands] at h2
  simp +decide [Finset.sum_insert, Finset.sum_singleton, πc, vec3_two] at h2 <;> norm_num at h2

/-! ## A non-degenerate positive instance of `compose_global` on the same frames (audit r1
N10 fidelity / N2 adversarial)

With the legitimacy event `L = {0, 1}` — excluding exactly the world at which every `F₂`-row is
null — step one holds *globally* conditional on `L` (Theorem 4.1 at the normalized
`(2/3, 1/3, 0) = ⅔·(3/4,1/4,0) + ⅓·(1/2,1/2,0)`, both `F₂`-rows modestly informed), step two holds
at both legitimate candidates, and `compose_global` yields the new fact that `(1/2, 1/4, 0)`
totally trusts `F₃` — while the same composite fails even locally at `L = Ω`. `F₃` is not the
Dirac frame, `L ≠ Ω`, and `π(L) = 3/4 > 0`: the theorem's hypothesis package is inhabited with
bite, not by `Vacuity.lean`'s degenerate `diracFrame`. -/

open Cleanroom.Corrigibility.CorrReflectFrames

/-- The legitimacy event `{0, 1}` of the positive instance.
Source: audit r1 N10 (fidelity), N2 (adversarial); this package
Kind: D
Fidelity: n/a -/
abbrev Lcomp : Finset (Fin 3) := {0, 1}

/-- `F₂`'s two rows differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF2_ne : (![3 / 4, 1 / 4, 0] : Fin 3 → ℝ) ≠ ![1 / 2, 1 / 2, 0] := by
  intro h; have := congrFun h 0; norm_num at this

/-- `F₂`'s cells: `{0}` at `(3/4,1/4,0)` and `{1, 2}` at `(1/2,1/2,0)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF2_cell : cF2.cell ![3 / 4, 1 / 4, 0] = {0} ∧ cF2.cell ![1 / 2, 1 / 2, 0] = {1, 2} := by
  obtain ⟨⟨h0, h1, h2⟩, _⟩ := cF_P
  have n := cF2_ne
  refine ⟨?_, ?_⟩ <;>
    · ext w
      fin_cases w <;> simp +decide [Frame.mem_cell, h0, h1, h2, n, n.symm] <;> norm_num

/-- Supports of the restricted deferrer `(1/2, 1/4, 0)` and its normalization `(2/3, 1/3, 0)`:
both `{0, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem comp_supp : supp (![1 / 2, 1 / 4, 0] : Fin 3 → ℝ) = {0, 1} ∧
    supp (![2 / 3, 1 / 3, 0] : Fin 3 → ℝ) = {0, 1} := by
  refine ⟨?_, ?_⟩ <;>
    · ext w; fin_cases w <;> simp [supp, vec3_two] <;> norm_num

/-- Candidates under `F₂` of a deferrer supported on `{0, 1}`: `{(3/4,1/4,0), (1/2,1/2,0)}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF2_cands_of_supp {μ : Fin 3 → ℝ} (hs : supp μ = {0, 1}) :
    cF2.cands μ = {![3 / 4, 1 / 4, 0], ![1 / 2, 1 / 2, 0]} := by
  obtain ⟨⟨h0, h1, _⟩, _⟩ := cF_P
  rw [Frame.cands, hs, image_insert, image_singleton, h0, h1]

/-- Self-masses and informed experts of `F₂`'s rows: `3/4` with `δ₀`, `1/2` with `δ₁`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cF2_informed : cF2.selfMass ![3 / 4, 1 / 4, 0] = 3 / 4 ∧
    cF2.selfMass ![1 / 2, 1 / 2, 0] = 1 / 2 ∧
    cF2.informed ![3 / 4, 1 / 4, 0] = ![1, 0, 0] ∧ cF2.informed ![1 / 2, 1 / 2, 0] = ![0, 1, 0] := by
  obtain ⟨⟨h0, h1, h2⟩, _⟩ := cF_P
  have n := cF2_ne
  obtain ⟨c0, c1⟩ := cF2_cell
  have s0 : cF2.selfMass ![3 / 4, 1 / 4, 0] = 3 / 4 := by
    unfold Frame.selfMass; rw [c0, mass_singleton]; rfl
  have s1 : cF2.selfMass ![1 / 2, 1 / 2, 0] = 1 / 2 := by
    unfold Frame.selfMass; rw [c1]
    simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, vec3_two] <;> norm_num
  refine ⟨s0, s1, ?_, ?_⟩
  · funext w
    fin_cases w
    · show cF2.informed ![3 / 4, 1 / 4, 0] 0 = ![1, 0, 0] 0
      rw [informed_apply, if_pos h0, s0]; norm_num
    · show cF2.informed ![3 / 4, 1 / 4, 0] 1 = ![1, 0, 0] 1
      rw [informed_apply, if_neg (by rw [h1]; exact n.symm)]; simp
    · show cF2.informed ![3 / 4, 1 / 4, 0] 2 = ![1, 0, 0] 2
      rw [informed_apply, if_neg (by rw [h2]; exact n.symm)]; simp [vec3_two]
  · funext w
    fin_cases w
    · show cF2.informed ![1 / 2, 1 / 2, 0] 0 = ![0, 1, 0] 0
      rw [informed_apply, if_neg (by rw [h0]; exact n)]; simp
    · show cF2.informed ![1 / 2, 1 / 2, 0] 1 = ![0, 1, 0] 1
      rw [informed_apply, if_pos h1, s1]; norm_num
    · show cF2.informed ![1 / 2, 1 / 2, 0] 2 = ![0, 1, 0] 2
      rw [informed_apply, if_pos h2, s1]; simp [vec3_two]

/-- **`F₂`'s rows are modestly informed**: `(3/4,1/4,0) = ½·δ₀ + ½·(1/2,1/2,0)` and
`(1/2,1/2,0) = ⅓·δ₁ + ⅔·(3/4,1/4,0)`.
Source: this package (Theorem 4.1's second condition for the positive instance)
Kind: L
Fidelity: n/a -/
theorem cF2_modestlyInformed : cF2.ModestlyInformed ![3 / 4, 1 / 4, 0] ∧
    cF2.ModestlyInformed ![1 / 2, 1 / 2, 0] := by
  obtain ⟨s0, s1, i0, i1⟩ := cF2_informed
  have n := cF2_ne
  have ca := cF2_cands_of_supp cand_supp.1
  have cb := cF2_cands_of_supp cand_supp.2.1
  constructor
  · refine ⟨by rw [s0]; norm_num, ?_⟩
    rw [i0]
    have hcm : cF2.candsMinus ![3 / 4, 1 / 4, 0] = {![1 / 2, 1 / 2, 0]} := by
      rw [Frame.candsMinus, ca]
      exact erase_insert (by rw [mem_singleton]; exact n)
    rw [hcm]
    exact mem_hull_of_comb2 (x := ![1, 0, 0]) (y := ![1 / 2, 1 / 2, 0])
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [vec3_two])
  · refine ⟨by rw [s1]; norm_num, ?_⟩
    rw [i1]
    have hcm : cF2.candsMinus ![1 / 2, 1 / 2, 0] = {![3 / 4, 1 / 4, 0]} := by
      rw [Frame.candsMinus, cb]
      ext σ
      simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hne, h | h⟩
        · exact h
        · exact absurd h hne
      · rintro rfl; exact ⟨n, Or.inl rfl⟩
    rw [hcm]
    exact mem_hull_of_comb2 (x := ![0, 1, 0]) (y := ![3 / 4, 1 / 4, 0])
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (by simp))
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [vec3_two])

/-- The restricted deferrer `π_L = (1/2, 1/4, 0)`, its mass `3/4`, and its normalization
`(2/3, 1/3, 0)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem comp_restrict : restrict πc Lcomp = ![1 / 2, 1 / 4, 0] ∧ mass πc Lcomp = 3 / 4 ∧
    (mass πc Lcomp)⁻¹ • restrict πc Lcomp = ![2 / 3, 1 / 3, 0] := by
  have hr : restrict πc Lcomp = ![1 / 2, 1 / 4, 0] := by
    funext w; fin_cases w <;> simp [restrict_apply, Lcomp, πc, vec3_two, fin3_mk_two]
  have hm : mass πc Lcomp = 3 / 4 := by
    simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, Lcomp, πc, vec3_two] <;> norm_num
  refine ⟨hr, hm, ?_⟩
  rw [hr, hm]; funext w; fin_cases w <;> simp [vec3_two, fin3_mk_two] <;> norm_num

/-- **Step one, global**: `π` has `L`-conditioned Total Trust toward `F₂` for `L = {0, 1}` —
Theorem 4.1 at the normalized `(2/3, 1/3, 0) = ⅔·(3/4,1/4,0) + ⅓·(1/2,1/2,0)` with both
candidates modestly informed — unlike at `L = Ω`, where the hull half fails
(`compose_counterexample_diagnosis`).
Source: this package (positive instance for Statement 9(a)); audit r1 N10/N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem cF2_legitimizingTT : LegitimizingTT πc cF2 Lcomp := by
  obtain ⟨_, hm, hn⟩ := comp_restrict
  rw [legitimizingTT_iff_hullAndModestlyInformed (fun w => by fin_cases w <;> norm_num [πc, vec3_two])
    (by rw [hm]; norm_num), hn]
  have hc := cF2_cands_of_supp comp_supp.2
  refine ⟨?_, ?_⟩
  · rw [hc]
    exact mem_hull_of_comb2 (x := ![3 / 4, 1 / 4, 0]) (y := ![1 / 2, 1 / 2, 0]) (by simp) (by simp)
      (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
      (by ext w; fin_cases w <;> norm_num [vec3_two])
  · intro ρ hρ
    rw [hc] at hρ
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · exact cF2_modestlyInformed.1
    · exact cF2_modestlyInformed.2

/-- **Step two**: every legitimate `F₂`-candidate of `π_L` has `L`-conditioned Total Trust
toward `F₃` — each candidate lives on `L`, so this is `cF2_cands_totalTrust`.
Source: this package; [[legitimacy-general-final]] Proofs l. 142
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem cF2_cands_legitimizingTT :
    ∀ ρ ∈ cF2.cands (restrict πc Lcomp), LegitimizingTT ρ cF3 Lcomp := by
  intro ρ hρ
  rw [comp_restrict.1, cF2_cands_of_supp comp_supp.1] at hρ
  have hρ' : ρ ∈ cF2.cands πc := by rw [cF2_cands]; exact hρ
  have ht := cF2_cands_totalTrust ρ hρ'
  have hr : restrict ρ Lcomp = ρ := by
    simp only [mem_insert, mem_singleton] at hρ
    rcases hρ with rfl | rfl <;>
      (funext w; fin_cases w <;> simp [restrict_apply, Lcomp, vec3_two, fin3_mk_two])
  unfold LegitimizingTT
  rw [hr]; exact ht

/-- **A non-degenerate positive instance of `compose_global`** on the counterexample's own
frames: `L = {0, 1} ≠ Ω` with `π(L) = 3/4`, `F₃` not the Dirac frame, step one global and step
two at both legitimate candidates, and the composite `L`-conditioned Total Trust toward `F₃`
(`TotalTrust (1/2, 1/4, 0) F₃`, a fact the theorem produces) — while the same composite fails
even locally at `L = Ω` (`cF3_not_totalTrustWrt`, cited). So the composition theorem has bite
exactly where the counterexample's diagnosis says: the event must exclude the world at which the
hull half fails.
Source: audit r1 N10 (fidelity), N2 (adversarial); [[legitimacy-general-final]] Statement 9(a)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem compose_positive_instance : Lcomp ≠ univ ∧ 0 < mass πc Lcomp ∧
    (∀ w, cF3.P w ≠ ind {w}) ∧ LegitimizingTT πc cF2 Lcomp ∧
    (∀ ρ ∈ cF2.cands (restrict πc Lcomp), LegitimizingTT ρ cF3 Lcomp) ∧
    LegitimizingTT πc cF3 Lcomp ∧ ¬ TotalTrustWrt (questionOf φc) πc cF3 := by
  obtain ⟨_, ⟨h0, h1, h2⟩⟩ := cF_P
  refine ⟨by decide, by rw [comp_restrict.2.1]; norm_num, fun w h => ?_, cF2_legitimizingTT,
    cF2_cands_legitimizingTT, ?_, cF3_not_totalTrustWrt⟩
  · have := congrFun h 0
    fin_cases w <;> simp [h0, h1, h2, ind, fin3_mk_two] at this <;> norm_num at this
  · have := compose_global (fun w => by fin_cases w <;> norm_num [πc, vec3_two])
      (by rw [comp_restrict.2.1]; norm_num) cF2_legitimizingTT cF2_cands_legitimizingTT
    rwa [inter_self] at this

end

end Cleanroom.Corrigibility.CorrLegitGeneral
