import Cleanroom.Decision.DpSmokingLesion.Prop14

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# T10, T11, T13, T14: "Why Ain'cha Rich", per-run SSC does not rescue (S2), the unobserved
parent, the cosmic-ray tree

* **T10 "Why Ain'cha Rich"** (`war_slOne`, `war_instances`): `V_B(δ_smoke) − V_B(δ_refrain) =
  α · (ν_{δ_smoke}(m=1) − ν_{δ_refrain}(m=1))` on the four catalogue trees — a comparison of
  `V_B` across procedures, never of evaluators at a point; `= α` exactly on the recorded
  `slOne` (`1000`), `α π = 500` on counterexample A, `100` on E2a, `500` on E13. The inventory's
  "compulsion `13/20`" is not reproduced by the mandate's parameters (findings).
* **T11** is `Prop14E13.lean`'s `perRunSSCAt_iff_strictOCAt_of_occ_univ` with its E13 instance
  (`e13_perRun_iff_strict`); the contrast is E2a, where `occ(d) ≠ univ` (`e2a_mass_occ_univ = 1/10`)
  and the per-run state differs (`war_e2a_occ`).
* **T13 the unobserved parent** (`not_covers_of_unconsulted_run`, `e2a_unobserved_parent`):
  a positive run whose world satisfies `O_d` and which meets no `d`-node is a coverage failure —
  the one direction the mandate asks for; the converse needs a coordinate in the algebra
  (E2a's `who` is absent from `SLW`, said in the docstring).
* **T14 the cosmic-ray tree** (`ray`, `ray_strict_state`): a chance branch sets `m := 1`
  without consulting `d`; at `δ_refrain` the strict state at `⊤` has `P(m=1) = π > 0` although
  `C(d)(smoke) = 0`, `V(m=1)` is the ray branch's conditional payoff, and coverage fails (the
  ray runs meet no `d`-node) — P02's inference at an unrecorded point.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-! ## T10: Why Ain'cha Rich -/

section war

/-- `paySum` of `⊤` is the value. Source: none: infrastructure. Kind: L -/
theorem paySum_univ_eq_value' (C : Proc Unit (fun _ => Bool) ℚ) (B : Tree TickleW Unit (fun _ => Bool) ℚ) :
    paySum C B Finset.univ = value C B := by
  unfold paySum value
  rw [worldEv_univ]

/-- On a lesion tree the value splits as `α ν(m=1) − β ν(k)`: the payoff is `α m − β k`.
Source: [[decision-problems-v2]] §7.3 (`r = αm − βk`)
Kind: L -/
theorem value_eq_alpha_nu_sub_beta_nu (C : Proc Unit (fun _ => Bool) ℚ)
    (B : Tree TickleW Unit (fun _ => Bool) ℚ) (α β : ℚ)
    (hpay : ∀ ℓ, payoff B ℓ = ticklePay α β (world B ℓ)) :
    value C B = α * nu C B (evM true) - β * nu C B evK := by
  unfold value
  rw [nu_eq_sum, nu_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [hpay ℓ]
  simp only [ticklePay, mem_evM, mem_evK]
  obtain ⟨l, m, k⟩ := world B ℓ
  cases m <;> cases k <;> simp <;> ring

/-- **"Why Ain'cha Rich" on the recorded instantiation**: on `slOne` the `k`-marginal is
label-invariant (`ν(k) = ρ γ₁ + (1−ρ) γ₀` for every `C`, `slOne_nu_k`), so
`V_B(δ_smoke) − V_B(δ_refrain) = α · (ν_{δ_smoke}(m=1) − ν_{δ_refrain}(m=1)) = α` exactly. This
is a comparison of `V_B` across procedures, never of evaluators at a point.
Source: dp-sl-018 ("'Why Ain'cha Rich' sides with the smoker on every (S1) tree computed:
`V_B(smoke) − V_B(refrain) = αΔ > 0` … equal to `α` exactly under recording"); mandate T10
Kind: P
Fidelity: exact on `slOne`
Hyps: none -/
theorem war_slOne (L : Lesion) (α β : ℚ) :
    value procSmoke (slOne L α β) - value procRefrain (slOne L α β) =
      α * (nu procSmoke (slOne L α β) (evM true) - nu procRefrain (slOne L α β) (evM true)) ∧
    value procSmoke (slOne L α β) - value procRefrain (slOne L α β) = α := by
  have hpay : ∀ ℓ, payoff (slOne L α β) ℓ = ticklePay α β (world (slOne L α β) ℓ) := by
    intro ℓ
    unfold slOne kBlock slLeaf at ℓ ⊢
    rcases ℓ with ⟨i, m, j, ⟨⟩⟩
    rfl
  rw [value_eq_alpha_nu_sub_beta_nu _ _ α β hpay, value_eq_alpha_nu_sub_beta_nu _ _ α β hpay,
    slOne_nu_k, slOne_nu_k, slOne_nu_m, slOne_nu_m]
  simp [procSmoke, procRefrain]

/-- **"Why Ain'cha Rich" on the four catalogue trees at the mandate's numbers**: the smoker's
`V_B` exceeds the refrainer's by `1000` on `slOne` (`= α`), `500` on counterexample A (`α π`),
`100` on E2a (`α π`), `500` on E13 (`α(1 − (ρc₁ + (1−ρ)c₀))`).
Source: dp-sl-018 (`1000` recorded, `500` reference class; the inventory's compulsion `13/20`
is not reproduced by the mandate's parameters — findings); mandate T10
Kind: N+ -/
theorem war_instances :
    value procSmoke (slOne Lesion.fdt 1000 1000000) - value procRefrain (slOne Lesion.fdt 1000 1000000) = 1000 ∧
    value procSmoke cexA₀ - value procRefrain cexA₀ = 500 ∧
    value procSmoke e2a₀ - value procRefrain e2a₀ = 100 ∧
    value procSmoke e13₀ - value procRefrain e13₀ = 500 := by
  refine ⟨(war_slOne Lesion.fdt 1000 1000000).2, ?_, ?_, ?_⟩
  · have h : ∀ C, value C cexA₀ = paySum C cexA₀ Finset.univ := fun C => (paySum_univ_eq_value' C _).symm
    rw [h, h, paySum_eq_sum_ite, paySum_eq_sum_ite, cexA_sum, cexA_sum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, cexA_leafLaw_E, cexA_leafLaw_A, Finset.mem_univ,
      if_true]
    have hE : ∀ (C : Proc Unit (fun _ => Bool) ℚ) (m : Bool) (i j : Fin 2), payoff cexA₀ ⟨0, m, i, j, ()⟩ =
        ticklePay 1000 1000000 (decide (i = 0), m, decide (j = 0)) := fun _ _ _ _ => rfl
    have hA : ∀ (i j : Fin 2), payoff cexA₀ ⟨1, i, j, ()⟩ =
        ticklePay 1000 1000000 (decide (i = 0), decide (i = 0), decide (j = 0)) := fun _ _ => rfl
    simp only [hE procSmoke, hE procRefrain, hA, ticklePay, procSmoke, procRefrain, FinDistr.pure_w]
    norm_num
  · have h : ∀ C, value C e2a₀ = paySum C e2a₀ (evM true) + paySum C e2a₀ (evM false) := by
      intro C; rw [← paySum_univ_eq_value', ← evM_union, paySum_union C e2a₀ evM_disjoint]
    rw [h, h, (e2a_paySum_values _).1, (e2a_paySum_values _).2, (e2a_paySum_values _).1,
      (e2a_paySum_values _).2]
    simp [procSmoke, procRefrain]; norm_num
  · have h : ∀ C, value C e13₀ = paySum C e13₀ (evM true) + paySum C e13₀ (evM false) := by
      intro C; rw [← paySum_univ_eq_value', ← evM_union, paySum_union C e13₀ evM_disjoint]
    rw [h, h, (e13_paySum_values _).1, (e13_paySum_values _).2, (e13_paySum_values _).1,
      (e13_paySum_values _).2]
    simp [procSmoke, procRefrain]; norm_num

/-- A sum over the leaves of the general compulsion `e13 L T α β`: per lesion branch, the two
"drew smoke" leaves and the four "drew refrain" leaves (`e13_sum` at the mandate's numbers).
Source: none: infrastructure. Kind: L -/
theorem e13_sum_gen (L : Lesion) (T : Compulsion) (α β : ℚ) (f : (e13 L T α β).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ j : Fin 2, f ⟨i, true, j, ()⟩) +
      ∑ fc : Fin 2, ∑ j : Fin 2, f ⟨i, false, fc, j, ()⟩) := by
  unfold e13 at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision, Fintype.sum_bool]
  have h1 : (∑ ℓ, f ⟨i, true, ℓ⟩) = ∑ j : Fin 2, f ⟨i, true, j, ()⟩ := by
    show (∑ ℓ : (kBlock L α β (decide (i = 0)) true).Leaves, f ⟨i, true, ℓ⟩) = _
    unfold kBlock slLeaf
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  have h2 : (∑ ℓ, f ⟨i, false, ℓ⟩) = ∑ fc : Fin 2, ∑ j : Fin 2, f ⟨i, false, fc, j, ()⟩ := by
    show (∑ ℓ : (Tree.chance 2 (T.coinF (decide (i = 0))) fun j =>
      kBlock L α β (decide (i = 0)) (decide (j = 0)) : Tree TickleW Unit (fun _ => Bool) ℚ).Leaves,
        f ⟨i, false, ℓ⟩) = _
    unfold kBlock slLeaf
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun fc _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  rw [h1, h2]

/-- The "drew smoke" leaf masses of the general compulsion: `ρ_i · C(d)(1) · γ_{i,j}`.
Source: Definition 6 on E13. Kind: L -/
theorem e13_leafLaw_smoke_gen (L : Lesion) (T : Compulsion) (α β : ℚ)
    (C : Proc Unit (fun _ => Bool) ℚ) (i j : Fin 2) :
    leafLaw C (e13 L T α β) ⟨i, true, j, ()⟩ =
      L.coinL.w i * (C ()).w true * (L.coinK (decide (i = 0))).w j := by
  unfold e13
  rw [leafLaw_chance, leafLaw_decision]
  show (L.coinL).w i * ((C ()).w true * leafLaw C (kBlock L α β (decide (i = 0)) true) ⟨j, ()⟩) = _
  unfold kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_leaf]
  ring

/-- The "drew refrain" leaf masses of the general compulsion:
`ρ_i · C(d)(0) · c_{i,fc} · γ_{i,j}`.
Source: Definition 6 on E13. Kind: L -/
theorem e13_leafLaw_refrain_gen (L : Lesion) (T : Compulsion) (α β : ℚ)
    (C : Proc Unit (fun _ => Bool) ℚ) (i fc j : Fin 2) :
    leafLaw C (e13 L T α β) ⟨i, false, fc, j, ()⟩ =
      L.coinL.w i * (C ()).w false * (T.coinF (decide (i = 0))).w fc *
        (L.coinK (decide (i = 0))).w j := by
  unfold e13
  rw [leafLaw_chance, leafLaw_decision]
  show (L.coinL).w i * ((C ()).w false * leafLaw C (Tree.chance 2 (T.coinF (decide (i = 0))) fun j =>
    kBlock L α β (decide (i = 0)) (decide (j = 0))) ⟨fc, j, ()⟩) = _
  unfold kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_leaf]
  ring

/-- **The post-decision compulsion of `repair/L1.md` L1-20′** (`repair_l1_checks.py` §1–2):
lesion `ρ = ½`, `γ = (⅘, ⅕)`, override rates `t = (3/5, 1/10)`, `α = 1`, `β = 5` — the tree
whose "Why Ain'cha Rich" difference the inventory (dp-sl-018) reports as `13/20`.
Source: `sl-workflow/notes/repair/L1.md` L1-20′ / L1-10′ ("`= 1 − 𝔼[t_ℓ]` on the tremble tree
(`13/20`)"); audit r1 fidelity §3.1
Kind: D -/
def e13L1 : Tree TickleW Unit (fun _ => Bool) ℚ :=
  e13 ⟨1/2, 4/5, 1/5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    ⟨3/5, 1/10, by norm_num, by norm_num, by norm_num, by norm_num⟩ 1 5

/-- **The inventory's `13/20` reproduced**: on L1-20′'s compulsion tree
`V_B(δ_smoke) − V_B(δ_refrain) = α(1 − (ρ t₁ + (1−ρ) t₀)) = 1 − (3/10 + 1/20) = 13/20`. The
mandate's E13 parameters (`α = 1000`, `c = (9/10, 1/10)`) give `500` (`war_instances`); the
inventory's number is right for its own tree, and findings F8 bullet 1 is corrected
accordingly.
Source: dp-sl-018 ("`13/20`"); `repair/L1.md` L1-10′; audit r1 fidelity §3.1
Kind: N+ -/
theorem war_e13L1 : value procSmoke e13L1 - value procRefrain e13L1 = 13/20 := by
  have hsum : ∀ f : e13L1.Leaves → ℚ, ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ j : Fin 2, f ⟨i, true, j, ()⟩) +
      ∑ fc : Fin 2, ∑ j : Fin 2, f ⟨i, false, fc, j, ()⟩) := fun f => e13_sum_gen _ _ _ _ f
  have hls : ∀ (C : Proc Unit (fun _ => Bool) ℚ) (i j : Fin 2), leafLaw C e13L1 ⟨i, true, j, ()⟩ =
      1/2 * (C ()).w true * (if i = 0 then (if j = 0 then 4/5 else 1/5) else
        (if j = 0 then 1/5 else 4/5)) := by
    intro C i j
    unfold e13L1
    rw [e13_leafLaw_smoke_gen]
    simp only [Lesion.coinL, Lesion.coinK, FinDistr.coin, tickleGamma]
    fin_cases i <;> fin_cases j <;> simp <;> norm_num
  have hlr : ∀ (C : Proc Unit (fun _ => Bool) ℚ) (i fc j : Fin 2),
      leafLaw C e13L1 ⟨i, false, fc, j, ()⟩ =
      1/2 * (C ()).w false * (if i = 0 then (if fc = 0 then 3/5 else 2/5) else
        (if fc = 0 then 1/10 else 9/10)) *
        (if i = 0 then (if j = 0 then 4/5 else 1/5) else (if j = 0 then 1/5 else 4/5)) := by
    intro C i fc j
    unfold e13L1
    rw [e13_leafLaw_refrain_gen]
    simp only [Lesion.coinL, Lesion.coinK, Compulsion.coinF, FinDistr.coin, tickleGamma]
    fin_cases i <;> fin_cases fc <;> fin_cases j <;> simp <;> norm_num
  have hp1 : ∀ (i j : Fin 2), payoff e13L1 ⟨i, true, j, ()⟩ =
      ticklePay 1 5 (decide (i = 0), true, decide (j = 0)) := fun _ _ => rfl
  have hp2 : ∀ (i fc j : Fin 2), payoff e13L1 ⟨i, false, fc, j, ()⟩ =
      ticklePay 1 5 (decide (i = 0), decide (fc = 0), decide (j = 0)) := fun _ _ _ => rfl
  have h : ∀ C, value C e13L1 = paySum C e13L1 Finset.univ :=
    fun C => (paySum_univ_eq_value' C _).symm
  rw [h, h, paySum_eq_sum_ite, paySum_eq_sum_ite, hsum, hsum]
  simp only [Fin.sum_univ_two, hls, hlr, hp1, hp2, Finset.mem_univ, if_true, ticklePay, procSmoke,
    procRefrain, FinDistr.pure_w]
  norm_num

/-- **T11's contrast**: on E2a `occ(d)` is not every run (`μ(occ(d)) = 1/10`), so the per-run
state is not the strict state at `⊤` — the per-run state screens the reference class
(`prop14_e2a_screened_perRun`) while the strict state does not (`e2a_S2_calibrated`).
Source: dp-sl-2-031 (the contrast); mandate T11
Kind: N+ -/
theorem war_e2a_occ (C : Proc Unit (fun _ => Bool) ℚ) :
    mass C e2a₀ (occ () e2a₀) = 1/10 ∧ occ () e2a₀ ≠ Finset.univ := by
  refine ⟨e2a_mass_occ_univ C, fun h => ?_⟩
  have := e2a_mass_occ_univ C
  rw [h, mass_univ] at this
  norm_num at this

end war

/-! ## T13: the unobserved parent is coverage failure -/

section unobserved

variable {Ω ι : Type} [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)]

/-- **A positive run that satisfies `O_d` and consults no `d`-node is a coverage failure** (the
one direction of dp-sl-2-005: a second point `d'` with the same observation, on a branch of
positive mass separated from `d`'s by an unobserved coordinate, makes `d` uncovered). The
converse — "uncovered ⟹ such a coordinate exists in the algebra" — holds only when the algebra
events the branch (E2a's `who` is absent from `SLW`), and is not stated.
Source: dp-sl-2-005 ("a chance coordinate … that separates queried points sharing an
observation is exactly a Definition 7 coverage failure at those points"), one direction; mandate
T13
Kind: L
Fidelity: weaker: one direction (the converse needs a coordinate in the algebra) -/
theorem not_covers_of_unconsulted_run (obs : ι → Finset Ω) (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ)
    (d : ι) (ℓ : B.Leaves) (hpos : 0 < leafLaw C B ℓ) (hobs : world B ℓ ∈ obs d)
    (hno : count d B ℓ = 0) : ¬ Covers obs C B d := by
  intro h
  have := h ℓ hpos hobs
  rw [hno] at this
  exact lt_irrefl 0 this

end unobserved

/-- **E2a as the unobserved parent**: the "who" coordinate (agent vs reference class) is
absent from `SLW`; the reference-class run `(1, 1, 1)` has positive mass, satisfies `⊤`, and
consults no `d`-node, so `d` is uncovered for every procedure (`e2a_not_covers`, restated
through the one-direction lemma).
Source: dp-sl-2-005 (witness: E2a); mandate T13
Kind: N+ -/
theorem e2a_unobserved_parent (C : Proc Unit (fun _ => Bool) ℚ) : ¬ Covers slObs C e2a₀ () :=
  not_covers_of_unconsulted_run slObs C e2a₀ () ⟨0, 1, 0, 0, ()⟩
    (by rw [e2a_leafLaw_other]; norm_num) (Finset.mem_univ _) (e2a_count.2 0 0 0)

/-! ## T14: the cosmic-ray tree -/

section ray

/-- **The cosmic-ray tree**: with probability `π` (index `0`) a ray sets `m := 1` without
consulting `d` (then `ℓ ∼ Bern(ρ)`, `k ∼ Bern(γ_ℓ)`); otherwise the recorded `slOne` block.
Source: dp-sl-2-007 ("add a chance 'ray' coordinate whose branch sets the act coordinate `m`
without consulting `d`"); mandate T14
Kind: D -/
def ray (π : ℚ) (p0 : 0 ≤ π) (p1 : π ≤ 1) (L : Lesion) (α β : ℚ) : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 (FinDistr.coin π p0 p1)
    ![.chance 2 L.coinL fun i => kBlock L α β (decide (i = 0)) true,
      .chance 2 L.coinL fun i => .decision () fun m => kBlock L α β (decide (i = 0)) m]

/-- The cosmic-ray tree at `π = 1/10`, the FDT lesion, `α = 1000`, `β = 10⁶`. Source: mandate T14. Kind: D -/
def ray₀ : Tree TickleW Unit (fun _ => Bool) ℚ := ray (1/10) (by norm_num) (by norm_num) Lesion.fdt 1000 1000000

/-- A sum over the leaves of `ray₀`: the four ray leaves and the eight `d` leaves.
Source: none: infrastructure. Kind: L -/
theorem ray_sum (f : ray₀.Leaves → ℚ) :
    ∑ ℓ, f ℓ = (∑ i : Fin 2, ∑ j : Fin 2, f ⟨0, i, j, ()⟩) +
      ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2, f ⟨1, i, m, j, ()⟩ := by
  unfold ray₀ ray kBlock slLeaf at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : (Tree.chance 2 Lesion.fdt.coinL fun i =>
      Tree.chance 2 (Lesion.fdt.coinK (decide (i = 0))) fun j =>
        Tree.leaf (decide (i = 0), true, decide (j = 0))
          (ticklePay 1000 1000000 (decide (i = 0), true, decide (j = 0))) :
      Tree TickleW Unit (fun _ => Bool) ℚ).Leaves, f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.chance 2 Lesion.fdt.coinL fun i => Tree.decision () fun m =>
      Tree.chance 2 (Lesion.fdt.coinK (decide (i = 0))) fun j =>
        Tree.leaf (decide (i = 0), m, decide (j = 0))
          (ticklePay 1000 1000000 (decide (i = 0), m, decide (j = 0))) :
      Tree TickleW Unit (fun _ => Bool) ℚ).Leaves, f ⟨1, ℓ⟩) = _
  congr 1
  · rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  · rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_leaves_decision]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _

/-- The ray-leaf masses: `(1/10) · ½ · γ_{ℓ,k}`. Source: Definition 6. Kind: L -/
theorem ray_leafLaw_ray (C : Proc Unit (fun _ => Bool) ℚ) (i j : Fin 2) :
    leafLaw C ray₀ ⟨0, i, j, ()⟩ =
      (1/10 : ℚ) * (1/2) *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100)) := by
  unfold ray₀ ray
  rw [leafLaw_chance]
  show (FinDistr.coin (1/10) _ _).w 0 * leafLaw C (Tree.chance 2 Lesion.fdt.coinL fun i =>
    kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) true) ⟨i, j, ()⟩ = _
  unfold kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_leaf, Lesion.coinL, Lesion.coinK, FinDistr.coin, tickleGamma,
    Lesion.fdt]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- The `d`-leaf masses: `(9/10) · ½ · C(d)(m) · γ_{ℓ,k}`. Source: Definition 6. Kind: L -/
theorem ray_leafLaw_d (C : Proc Unit (fun _ => Bool) ℚ) (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw C ray₀ ⟨1, i, m, j, ()⟩ =
      (9/10 : ℚ) * (1/2) * (C ()).w m *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100)) := by
  unfold ray₀ ray
  rw [leafLaw_chance]
  show (FinDistr.coin (1/10) _ _).w 1 * leafLaw C (Tree.chance 2 Lesion.fdt.coinL fun i =>
    Tree.decision () fun m => kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) m) ⟨i, m, j, ()⟩ = _
  unfold kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, Lesion.coinL, Lesion.coinK,
    FinDistr.coin, tickleGamma, Lesion.fdt]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The worlds at the leaves of `ray₀`. Source: none: infrastructure. Kind: L -/
theorem ray_world :
    (∀ (i j : Fin 2), world ray₀ ⟨0, i, j, ()⟩ = (decide (i = 0), true, decide (j = 0))) ∧
    (∀ (i : Fin 2) (m : Bool) (j : Fin 2), world ray₀ ⟨1, i, m, j, ()⟩ = (decide (i = 0), m, decide (j = 0))) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The payoffs at the leaves of `ray₀`. Source: none: infrastructure. Kind: L -/
theorem ray_payoff :
    (∀ (i j : Fin 2), payoff ray₀ ⟨0, i, j, ()⟩ = ticklePay 1000 1000000 (decide (i = 0), true, decide (j = 0))) ∧
    (∀ (i : Fin 2) (m : Bool) (j : Fin 2), payoff ray₀ ⟨1, i, m, j, ()⟩ =
      ticklePay 1000 1000000 (decide (i = 0), m, decide (j = 0))) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- The ray runs consult no `d`-node; the `d` runs consult it once. Source: none: infrastructure. Kind: L -/
theorem ray_count :
    (∀ (i j : Fin 2), count () ray₀ ⟨0, i, j, ()⟩ = 0) ∧
    (∀ (i : Fin 2) (m : Bool) (j : Fin 2), count () ray₀ ⟨1, i, m, j, ()⟩ = 1) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- **The cosmic-ray tree at `δ_refrain`**: the strictly calibrated state at `⊤` has
`P(m=1) = 1/10 > 0` although `C(d)(smoke) = 0` (clause 1 reads the ray), its value of smoking is
the ray branch's conditional payoff `V(m=1) = 1000 − 10⁶ · ½ = −499 000`, and coverage fails —
the ray leaf `(1, 1, 1)` has mass `99/2000`, satisfies `⊤`, and meets no `d`-node (clause 1 by
coverage, not clause 3: the `d`-runs are veridical). This is P02's inference at an unrecorded
point: the unplayed act is priced by a writer that is not the agent.
Source: dp-sl-2-007 ("strict OC at the pooled `O_d` gives `P_{s_d}(a*) > 0` even for a
deterministic `C` with `C(d) ≠ a*`, and `𝔼[r ∣ a*]` is the ray-branch payoff"); mandate T14
Kind: N+ -/
theorem ray_strict_state :
    let s₀ : Unit → State TickleW ℚ := fun _ => calibratedState procRefrain ray₀ Finset.univ (nu_univ_pos _ _)
    StrictOCAt s₀ slObs procRefrain ray₀ () ∧ (s₀ ()).pr (evM true) = 1/10 ∧
      (procRefrain ()).w true = 0 ∧ (s₀ ()).V (evM true) = -499000 ∧
      ¬ Covers slObs procRefrain ray₀ () := by
  intro s₀
  have hnu : nu procRefrain ray₀ (evM true) = 1/10 := by
    rw [nu_eq_sum, ray_sum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, ray_leafLaw_ray, ray_leafLaw_d, ray_world.1,
      ray_world.2, mem_evM, procRefrain, FinDistr.pure_w]
    simp; norm_num
  have hpay : paySum procRefrain ray₀ (evM true) = -49900 := by
    rw [paySum_eq_sum_ite, ray_sum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, ray_leafLaw_ray, ray_leafLaw_d, ray_world.1,
      ray_world.2, ray_payoff.1, ray_payoff.2, mem_evM, procRefrain, FinDistr.pure_w, ticklePay]
    simp; norm_num
  refine ⟨strictOCAt_calibratedState slObs _ _ s₀ () _ rfl, ?_, by simp [procRefrain], ?_, ?_⟩
  · simp only [s₀, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, hnu]
  · simp only [s₀, calibratedState_V, Finset.inter_univ, hpay, hnu]; norm_num
  · exact not_covers_of_unconsulted_run slObs procRefrain ray₀ () ⟨0, 0, 0, ()⟩
      (by rw [ray_leafLaw_ray]; norm_num) (Finset.mem_univ _) (ray_count.1 0 0)

end ray

end Cleanroom.Decision.DpSmokingLesion
