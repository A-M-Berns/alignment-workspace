import Cleanroom.Decision.DpCausalConsist.Witness3
import Cleanroom.Decision.DpCausalConsist.OverwriteDag

/-!
# `dp-causal-consist`: the bypass tree — Corollary 3.1(b) at a coverage failure (T4(b); T3(C) in
part; repair round 1)

**The bypass tree** (`bypassTree u`, mandate T3(C)/T4(b)): `ℓ ∼ Bern(1/10)`; on the lesion branch
the act is written `m := 1` **without consulting `d`**, then `k ∼ Bern(3/5)`; off it `d` is queried
and `k ∼ Bern(1/20)`; leaf `pt3 ℓ m k`, `O_d = ⊤`. The lesion runs pass through no `d`-node, so the
tree does not cover `d` for any label (`bypass_not_covers`) and is not Definition-7 recorded
(`bypass_not_recordsFor`): the point is a *coverage* failure, as opposed to the overwrite tree's
action-veridicality failure.

Its world law at `C(d) = (q, 1 − q)` is `bypassP q` on `W3` (`bypassTree_toDistr`, the seam), which
factorizes over the temporal DAG `ℓ → m`, `ℓ → k` (`sByp_isFor`; the unique temporal DAG in the
mandate's sense is `stretch`, not proved). Corollary 3.1(b): the temporal structure's truncated
`k`-rate is `21/200` for both acts at every label (`sByp_truncate_k`, Pearl), while the calibrated
conditionals are `P(k | m = 1) = (12 + 9q)/(20(1 + 9q))` and `P(k | m = 0) = 1/20`
(`bypassP_k_given`), so the truncated law differs from the act-conditional for both acts at every
label `q < 1` (`bypass_truncate_ne_cond`).

**Finding (new, T3(C)'s numbers; F13):** at the note's label `q = 1` the identity *holds* for the
realized act — `P(k | m = 1) = 21/200` exactly — and fails only at the null act, whose conditional
is junk (`bypass_cond_eq_truncate_at_one`); the note's `0.105276` for conditioning is not an
untrembled value at `q = 1` (it is the untrembled conditional at `q ≈ 0.9945`, or the `q = 1` row
with the script's tremble `δ = 0.05`: `0.105276 − 0.105 = 0.000276` is the "analytic miss" the
adjacent `lab_cdt_miss.py` paragraph reports). The discrepancy on the realized act is a
mixed-label phenomenon. The bypass tree's source is [[defining-cdt-in-the-learning-setting]]
(Corollary 3.1(b), l. 46; script (C), l. 131), not [[learning-cdt-renderings]], whose "Checks"
paragraph has no bypass tree (audit r2 fid N1 / adv N2 — the pointers below were corrected in
repair round 2).
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

/-- The lesion coin `Bern(1/10)`. Source: mandate T2 witness (`ρ = 1/10`). Kind: D -/
def bypRoot : FinDistr ℚ (Fin 2) := FinDistr.coin (1/10) (by norm_num) (by norm_num)

/-- The cancer coin on the lesion branch `Bern(3/5)`. Source: mandate (`γ₁ = 3/5`). Kind: D -/
def bypK1 : FinDistr ℚ (Fin 2) := FinDistr.coin (3/5) (by norm_num) (by norm_num)

/-- The cancer coin off the lesion branch `Bern(1/20)`. Source: mandate (`γ₀ = 1/20`). Kind: D -/
def bypK0 : FinDistr ℚ (Fin 2) := FinDistr.coin (1/20) (by norm_num) (by norm_num)

section tree

variable (u : W3 → ℚ)

/-- **The bypass tree**: the lesion branch writes `m := 1` without consulting `d`; otherwise `d` is
queried; `k ∼ Bern(γ_ℓ)`; leaf `pt3 ℓ m k`.
Source: [[defining-cdt-in-the-learning-setting]] Corollary 3.1(b), l. 46 ("coverage failure (the
bypass tree at `O_d = ⊤`, S2's reference class)") and l. 131 (script (C): "bypass tree at OC-⊤,
`q = 1` (not recorded)");
mandate T3(C), T4(b) (`bypassTree`: "lesion branch writes `m := 1` without consulting `d`; else
query `d`")
Kind: D
Fidelity: exact -/
def bypassTree : Tree W3 Unit (fun _ => Bool) ℚ :=
  .chance 2 bypRoot
    ![.chance 2 bypK1 fun j =>
        .leaf (pt3 true true (decide (j = 0))) (u (pt3 true true (decide (j = 0)))),
      .decision () fun m =>
        .chance 2 bypK0 fun j =>
          .leaf (pt3 false m (decide (j = 0))) (u (pt3 false m (decide (j = 0))))]

/-- The lesion run with `k = 1` has count `0` at `d`. Source: none: infrastructure. Kind: L -/
theorem bypass_count_lesion : count () (bypassTree u) ⟨0, ⟨0, ()⟩⟩ = 0 := rfl

/-- The lesion run with `k = 1` has positive mass under every procedure.
Source: none: infrastructure
Kind: L -/
theorem bypass_leafLaw_lesion_pos (C : Proc Unit (fun _ => Bool) ℚ) :
    0 < leafLaw C (bypassTree u) ⟨0, ⟨0, ()⟩⟩ := by
  show 0 < bypRoot.w 0 * (bypK1.w 0 * 1)
  simp [bypRoot, bypK1, FinDistr.coin]

/-- **The bypass tree does not cover `d`** for any procedure: the lesion run (`1/10 · 3/5 > 0`)
meets no `d`-node.
Source: [[decision-problems-v2]] Definition 7 ("covers"); mandate T3(C) ("prove `¬ Covers`")
Kind: N+ (every procedure; the refuting run has mass `3/50` under each — the forced write *is* the
coverage failure, not a degeneracy of the witness; audit r2 fid N6 / adv N7)
Fidelity: exact -/
theorem bypass_not_covers (C : Proc Unit (fun _ => Bool) ℚ) :
    ¬ Covers s1Obs C (bypassTree u) () := by
  intro h
  have := h ⟨0, ⟨0, ()⟩⟩ (bypass_leafLaw_lesion_pos u C) (Finset.mem_univ _)
  rw [bypass_count_lesion] at this
  exact lt_irrefl _ this

/-- **The bypass tree is not Definition-7 recorded at `d`** for any procedure (clause (1) fails on
the lesion run). Source: mandate T4(b) ("`bypassTree` (coverage failure)"). Kind: N+ (every
procedure, as `bypass_not_covers`) -/
theorem bypass_not_recordsFor (C : Proc Unit (fun _ => Bool) ℚ) :
    ¬ RecordsFor s1Obs s1ActEv C (bypassTree u) () := by
  intro h
  have := (h ⟨0, ⟨0, ()⟩⟩ (bypass_leafLaw_lesion_pos u C) (Finset.mem_univ _)).1
  rw [bypass_count_lesion] at this
  exact zero_ne_one this

/-- `ν` on the bypass tree. Source: none: infrastructure. Kind: L -/
theorem bypass_nu (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset W3) :
    nu C (bypassTree u) X =
      bypRoot.w 0 * ∑ j : Fin 2, (if pt3 true true (decide (j = 0)) ∈ X then bypK1.w j else 0)
      + bypRoot.w 1 * ∑ m : Bool, (C ()).w m
          * ∑ j : Fin 2, (if pt3 false m (decide (j = 0)) ∈ X then bypK0.w j else 0) := by
  rw [nu_eq_sum]
  unfold bypassTree
  rw [sum_leaves_chance, Fin.sum_univ_two]
  congr 1
  · show ∑ ℓ : (Σ _ : Fin 2, Unit), (if pt3 true true (decide (ℓ.1 = 0)) ∈ X then
      bypRoot.w 0 * (bypK1.w ℓ.1 * 1) else 0) = _
    rw [Fintype.sum_sigma]
    simp only [Fin.sum_univ_two, Fintype.sum_unique, mul_add, mul_ite, mul_zero, mul_one]
  · show ∑ ℓ : (Σ _ : Bool, Σ _ : Fin 2, Unit), (if pt3 false ℓ.1 (decide (ℓ.2.1 = 0)) ∈ X then
      bypRoot.w 1 * ((C ()).w ℓ.1 * (bypK0.w ℓ.2.1 * 1)) else 0) = _
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp

/-- `ν{pt3 ℓ m k}` on the bypass tree. Source: none: infrastructure. Kind: L -/
theorem bypass_nu_singleton (C : Proc Unit (fun _ => Bool) ℚ) (ℓ m k : Bool) :
    nu C (bypassTree u) {pt3 ℓ m k} =
      if ℓ then (if m then (1/10) * (if k then 3/5 else 2/5) else 0)
      else (9/10) * ((C ()).w m * (if k then 1/20 else 19/20)) := by
  rw [bypass_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, Finset.mem_singleton, pt3_inj,
    bypRoot, bypK1, bypK0, FinDistr.coin]
  cases ℓ <;> cases m <;> cases k <;> simp
  all_goals first | ring1 | norm_num

end tree

section law

variable (u : W3 → ℚ) (q : ℚ) (q0 : 0 ≤ q) (q1 : q ≤ 1)

/-- The label `C(d) = (q, 1 − q)` on a one-point boolean tree (`true ↦ q`).
Source: none: infrastructure
Kind: D -/
def procB : Proc Unit (fun _ => Bool) ℚ := fun _ => FinDistr.bool q q0 q1

/-- The strictly calibrated state of the bypass tree at label `q` and `O = ⊤`.
Source: [[decision-problems-v2]] Definition 8; mandate T4(b)
Kind: D -/
def bypassState : State W3 ℚ :=
  calibratedState (procB q q0 q1) (bypassTree u) Finset.univ (nu_univ_pos _ _)

/-- `P_s(x) = ν{x}` at `O = ⊤`. Source: none: infrastructure. Kind: L -/
theorem bypassState_w (x : W3) :
    (bypassState u q q0 q1).P.w x = nu (procB q q0 q1) (bypassTree u) {x} := by
  simp [bypassState, calibratedState, nuCondDistr, nu_univ]

/-- The bypass law's mass table over ℝ. Source: mandate T4(b). Kind: D -/
noncomputable def bypMass (ℓ m k : Bool) : ℝ :=
  if ℓ then (if m then (1/10) * (if k then 3/5 else 2/5) else 0)
  else (9/10) * ((if m then (q : ℝ) else 1 - q) * (if k then 1/20 else 19/20))

/-- **The bypass law** on `W3` at label `q`. Source: mandate T4(b). Kind: D -/
noncomputable def bypassP : Distr W3 :=
  distr3 (bypMass q)
    (fun a b c => by
      have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast q0
      have hq1 : (q : ℝ) ≤ 1 := by exact_mod_cast q1
      cases a <;> cases b <;> cases c <;> norm_num [bypMass] <;> linarith)
    (by norm_num [bypMass]; ring)

/-- **The seam**: the calibrated state of the bypass tree at label `q`, pushed to FAF's `Distr`,
is `bypassP q`. Source: mandate §3.3; T4(b). Kind: L -/
theorem bypassTree_toDistr :
    State.toDistr (State.castℝ (bypassState u q q0 q1)) = bypassP q q0 q1 := by
  apply Distr.ext
  funext x
  rw [eq_pt3 x]
  simp only [State.toDistr_mass, State.castℝ, FinDistr.castℝ, bypassState_w, bypass_nu_singleton,
    bypassP, distr3_mass, bypMass, procB, FinDistr.bool]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> simp <;> ring

/-- The rate table of the bypass tree's temporal structure: `ℓ ∼ Bern(1/10)`, `m | ℓ ∼ Bern(1)` on
the lesion branch and `Bern(q)` off it, `k | ℓ ∼ Bern(γ_ℓ)`.
Source: mandate T4(b)
Kind: D -/
noncomputable def rByp : Rate3 where
  r v ℓ _ _ := match v with
    | 0 => 1/10
    | 1 => if ℓ then 1 else (q : ℝ)
    | 2 => if ℓ then 3/5 else 1/20
  nonneg v a b c := by
    have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast q0
    fin_cases v <;> cases a <;> norm_num <;> linarith
  le_one v a b c := by
    have hq1 : (q : ℝ) ≤ 1 := by exact_mod_cast q1
    fin_cases v <;> cases a <;> norm_num <;> linarith

/-- **The bypass tree's temporal structure** `ℓ → m`, `ℓ → k` at label `q`.
Source: mandate T3(C) ("the unique compatible temporal DAG (`ℓ → m`, `ℓ → k`)"), T4(b)
Kind: D -/
noncomputable def sByp : CausalStructure (fun _ : Fin 3 => Bool) :=
  ⟨gLmLk, isAcyclic_of_rank _ _ gLmLk_rank, cpdOfRate gLmLk (rByp q q0 q1)⟩

/-- The temporal structure is compatible with the bypass law at every label.
Source: mandate T4(b)
Kind: N+ -/
theorem sByp_isFor : (sByp q q0 q1).IsFor (bypassP q q0 q1) := by
  unfold sByp
  rw [isFor_cpdOfRate_iff]
  intro a b c
  simp only [cpdFactor_cpdOfRate, gLmLk_parents.1, gLmLk_parents.2.1, gLmLk_parents.2.2,
    Finset.notMem_empty, Finset.mem_singleton]
  cases a <;> cases b <;> cases c <;> norm_num [bypassP, bypMass, rByp] <;> ring

/-- `P(k = 1) = 21/200` under the bypass law, at every label.
Source: [[defining-cdt-in-the-learning-setting]] l. 131 (script (C): "gives `0.105` for both
acts"); mandate T4(b)
Kind: N+ -/
theorem bypassP_k : (bypassP q q0 q1).prob {x | x 2 = true} = 21/200 := by
  rw [prob3_eq]; norm_num [bypassP, bypMass]; ring

/-- `P(m = 1) = (1 + 9q)/10`, `P(m = 0) = 9(1 − q)/10`. Source: none: infrastructure. Kind: L -/
theorem bypassP_m (b : Bool) :
    (bypassP q q0 q1).prob {x | x 1 = b}
      = if b then (1 + 9 * (q : ℝ)) / 10 else 9 * (1 - (q : ℝ)) / 10 := by
  rw [prob3_eq]; cases b <;> norm_num [bypassP, bypMass] <;> ring

/-- `P(m = b) > 0` for `q < 1`. Source: none: infrastructure. Kind: L -/
theorem bypassP_m_pos (hq1 : q < 1) (b : Bool) : 0 < (bypassP q q0 q1).prob {x | x 1 = b} := by
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast q0
  have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq1
  rw [bypassP_m]; cases b <;> simp <;> linarith

/-- **The calibrated act-conditionals of `k`** on the bypass tree: `P(k | m = 1) =
(12 + 9q)/(20(1 + 9q))`, `P(k | m = 0) = 1/20` (the closed forms the mandate asks for; the note's
`0.105276` is not an untrembled value at `q = 1`, module docstring).
Source: [[defining-cdt-in-the-learning-setting]] l. 131 (script (C): "against conditioning's
`(0.105276, 0.050)`") and l. 46 ("S2's statistics (`0.600` vs `0.0525` at `q = 0`)" — `0.600 =
12/20` matches at `q = 0`, `0.0525` is not this tree's `P(k | m = 0) = 1/20` at any label, F13);
mandate T3(C) ("recompute the exact values from the tree … state the closed form")
Kind: N+
Hyps: (a) `q < 1` (for the `m = 0` conditional to be defined) -/
theorem bypassP_k_given (hq1 : q < 1) (b : Bool) :
    (bypassP q q0 q1).condProb {x | x 2 = true} {x | x 1 = b}
      = if b then (12 + 9 * (q : ℝ)) / (20 * (1 + 9 * (q : ℝ))) else 1/20 := by
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast q0
  have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq1
  have h1 : (1 + 9 * (q : ℝ)) ≠ 0 := by linarith
  have h2 : (1 - (q : ℝ)) ≠ 0 := by linarith
  unfold Distr.condProb
  have : ∀ b, ({x : W3 | x 2 = true} ∩ {x | x 1 = b}) = {x | x 2 = true ∧ x 1 = b} := by
    intro b; ext x; simp
  rw [this, bypassP_m, prob3_eq]
  cases b <;> simp [bypassP, bypMass] <;> field_simp <;> ring

/-- **The truncated `k`-rate of the temporal structure is `21/200` for both acts**, at every label
(Pearl's invariance: `k ∈ nondesc(m)`).
Source: [[defining-cdt-in-the-learning-setting]] l. 131 (script (C): "the temporal structure
`m ← ℓ, k ← ℓ` gives `0.105` for both acts") and l. 46 ("gives the population rate `0.105`");
mandate T3(C), T4(b)
Kind: C
Hyps: (a) `sByp_isFor`; (a) `k ∈ nondesc gLmLk m` -/
theorem sByp_truncate_k (b : Bool) :
    ((sByp q q0 q1).truncate 1 b).prob {x | x 2 = true} = 21/200 := by
  have hset : ({x : W3 | x 2 = true}) = ↑(Finset.univ.filter fun x : W3 => x 2 = true) := by
    ext x; simp
  rw [hset, CausalStructure.truncate,
    truncate_prob_eq_of_inFixedAlgebra (sByp q q0 q1).acyclic (sByp q q0 q1).φ (sByp_isFor q q0 q1)
      1 b _ (coord_inFixedAlgebra gLmLk 2 gLmLk_k_nondesc), ← hset, bypassP_k]

/-- **Corollary 3.1(b) on the bypass tree**: at every label `q < 1` the point is not recorded
(coverage fails) and the temporal structure's truncated law differs from the calibrated
act-conditional for both acts (`21/200` against `(12 + 9q)/(20(1 + 9q))` and `1/20` on `{k = 1}`).
Source: [[learning-cdt-renderings]] Corollary 3.1(b); [[defining-cdt-in-the-learning-setting]]
Corollary 3.1(b), l. 46 (the bypass tree named); mandate T4(b) (`bypassTree`)
Kind: N+
Fidelity: exact (the world law is the calibrated state's by `bypassTree_toDistr`; at `q = 1` the
realized act's identity holds — `bypass_cond_eq_truncate_at_one` — so the mixed label is where
both acts separate)
Hyps: (a) `q < 1` -/
theorem bypass_truncate_ne_cond (hq1 : q < 1) :
    ¬ RecordsFor s1Obs s1ActEv (procB q q0 q1) (bypassTree u) () ∧
    ∀ b, (sByp q q0 q1).truncate 1 b
      ≠ condDistr (State.toDistr (State.castℝ (bypassState u q q0 q1))) {x | x 1 = b}
          (by rw [bypassTree_toDistr]; exact bypassP_m_pos q q0 q1 hq1 b) := by
  refine ⟨bypass_not_recordsFor u _, fun b h => ?_⟩
  have h1 := sByp_truncate_k q q0 q1 b
  rw [h, condDistr_prob] at h1
  have h2 : (State.toDistr (State.castℝ (bypassState u q q0 q1))).condProb {x | x 2 = true}
      {x | x 1 = b} = if b then (12 + 9 * (q : ℝ)) / (20 * (1 + 9 * (q : ℝ))) else 1/20 := by
    rw [bypassTree_toDistr]; exact bypassP_k_given q q0 q1 hq1 b
  rw [h2] at h1
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast q0
  have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq1
  cases b
  · norm_num at h1
  · simp only [if_true] at h1
    have hne : (20 * (1 + 9 * (q : ℝ))) ≠ 0 := by positivity
    rw [div_eq_iff hne] at h1
    linarith

/-- **Finding: at the note's label `q = 1` the identity holds for the realized act** — the
calibrated conditional of `k` given `m = 1` is exactly `21/200`, the truncated rate — and fails
only at the null act, whose conditional is junk. The note's "`0.105276`" is not an untrembled
`q = 1` value (module docstring, F13).
Source: [[defining-cdt-in-the-learning-setting]] l. 131 (script (C), the bypass tree at `q = 1`);
mandate T3(C)
("the note's `0.105276` is `q`-dependent")
Kind: N− (deterministic label; the finding row)
Fidelity: exact -/
theorem bypass_cond_eq_truncate_at_one :
    (bypassP 1 zero_le_one le_rfl).condProb {x | x 2 = true} {x | x 1 = true} = 21/200 ∧
    ((sByp 1 zero_le_one le_rfl).truncate 1 true).prob {x | x 2 = true} = 21/200 := by
  refine ⟨?_, sByp_truncate_k 1 zero_le_one le_rfl true⟩
  unfold Distr.condProb
  have : ({x : W3 | x 2 = true} ∩ {x | x 1 = true}) = {x | x 2 = true ∧ x 1 = true} := by
    ext x; simp
  rw [this, prob3_eq, prob3_eq]
  norm_num [bypassP, bypMass]

end law

end Cleanroom.Decision.DpCausalConsist
