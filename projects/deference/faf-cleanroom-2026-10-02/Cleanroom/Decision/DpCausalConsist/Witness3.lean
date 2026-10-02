import Cleanroom.Found.DpCoreTree.Catalogue
import Cleanroom.Found.DpCoreTree.Tickle
import Cleanroom.Found.DpCoreTree.Occurrence
import Cleanroom.Decision.DpCalibration.Basic
import Cleanroom.Decision.DpCalibration.Recording
import Cleanroom.Decision.DpCausalConsist.Dags

/-!
# `dp-causal-consist`: the (S1)-shaped tree family and Theorem 3's tree-side witnesses

**`s1Fam ρ κ u`**: chance `ℓ ∼ Bern(ρ)` (index `0` = `ℓ = 1`); query `d` drawing `m`; chance
`k ∼ Bern(κ ℓ m)` (index `0` = `k = 1`); leaf `pt3 ℓ m k` with supervenient payoff `u`. `O_d = ⊤`
(`s1Obs`), action events the act coordinate (`s1ActEv`). Every member records at `d` for every
procedure (`s1Fam_recordsFor`), the lesion cells are pre-query (`s1Fam_preQuery_ell`), and the
strictly calibrated state at `O = ⊤` (`s1State`) has `P(x) = ν{x}` (`s1State_w`).

**The direct-effect tree** `directTree u` (`κ ℓ m = γ_ℓ + τ·m` at the mandate's numbers) pushes
forward to `directP` (`directTree_toDistr`, the bridge), so Theorem 3(ii) applies with the
collider structure `sColl` (`pa(m) = ∅`, trivially pre-query): `direct_collapse` is the collapse
derived *through* `thm3_ii` from recording and strict calibration (N+: label `1/2`, chances
`1/10`, `(1/20, 3/5)`, `τ = 1/5`), and `direct_tcdt_iff_tedt` is Theorem 3(iv) instantiated for
every supervenient payoff (the proviso holds automatically at a mixed label).

The (S1) tree without the direct effect (`s1P`, joint independence, T3(A)), the noisy-XOR
refutation of the pairwise reading of (iii), and the N− companion of (iv) are `Witness3B.lean`.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

/-- `O_d = ⊤`. Source: mandate §3.1 (`O_d = ⊤`). Kind: D -/
def s1Obs : Unit → Finset W3 := fun _ => Finset.univ

/-- Action events: the act coordinate's fibers. Source: mandate §3.1 (`actEv d a := {x m = a}`). Kind: D -/
def s1ActEv : Unit → Bool → Finset W3 := fun _ b => actEvCoord 1 b

/-- `s1ActEv` unfolds to `actEvCoord`. Source: none: infrastructure. Kind: L -/
@[simp] theorem s1ActEv_eq (b : Bool) : s1ActEv () b = actEvCoord 1 b := rfl

section fam

variable (ρ : ℚ) (r0 : 0 ≤ ρ) (r1 : ρ ≤ 1) (κ : Bool → Bool → ℚ) (k0 : ∀ ℓ m, 0 ≤ κ ℓ m)
  (k1 : ∀ ℓ m, κ ℓ m ≤ 1) (u : W3 → ℚ)

/-- **The (S1)-shaped family**: `ℓ ∼ Bern(ρ)`, query `d` drawing `m`, `k ∼ Bern(κ ℓ m)`, leaf
`pt3 ℓ m k`, payoff `u (pt3 ℓ m k)`. `κ ℓ m = γ_ℓ` is the (S1) tree, `γ_ℓ + τ m` the direct-effect
tree, a noisy XOR the pairwise-independence counterexample.
Source: [[decision-problems-v2]] §7.3 (S1) ("chance `ℓ`; query `d`; act `m`; chance `k`; leaf
`(ℓ, m, k)`"); mandate T2 witness (`s1Tree ρ γ₀ γ₁`), T3(B) (`s1DirectTree`)
Kind: D
Fidelity: exact (worlds are the coordinate points `Fin 3 → Bool`) -/
def s1Fam : Tree W3 Unit (fun _ => Bool) ℚ :=
  .chance 2 (FinDistr.coin ρ r0 r1) fun i =>
    .decision () fun m =>
      .chance 2 (FinDistr.coin (κ (decide (i = 0)) m) (k0 _ _) (k1 _ _)) fun j =>
        .leaf (pt3 (decide (i = 0)) m (decide (j = 0))) (u (pt3 (decide (i = 0)) m (decide (j = 0))))

/-- The world at a leaf. Source: none: infrastructure. Kind: L -/
theorem s1Fam_world (i : Fin 2) (m : Bool) (j : Fin 2) :
    world (s1Fam ρ r0 r1 κ k0 k1 u) ⟨i, m, j, ()⟩ = pt3 (decide (i = 0)) m (decide (j = 0)) := rfl

/-- The payoff is supervenient. Source: none: infrastructure. Kind: L -/
theorem s1Fam_payoff (ℓ : (s1Fam ρ r0 r1 κ k0 k1 u).Leaves) :
    payoff (s1Fam ρ r0 r1 κ k0 k1 u) ℓ = u (world (s1Fam ρ r0 r1 κ k0 k1 u) ℓ) := by
  rcases ℓ with ⟨i, m, j, _⟩; rfl

/-- The leaf law. Source: none: infrastructure. Kind: L -/
theorem s1Fam_leafLaw (C : Proc Unit (fun _ => Bool) ℚ) (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw C (s1Fam ρ r0 r1 κ k0 k1 u) ⟨i, m, j, ()⟩ =
      (FinDistr.coin ρ r0 r1).w i * ((C ()).w m *
        (FinDistr.coin (κ (decide (i = 0)) m) (k0 _ _) (k1 _ _)).w j) := by
  unfold s1Fam
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, mul_one]

/-- Every run meets `d` exactly once. Source: none: infrastructure. Kind: L -/
theorem s1Fam_count (ℓ : (s1Fam ρ r0 r1 κ k0 k1 u).Leaves) :
    count () (s1Fam ρ r0 r1 κ k0 k1 u) ℓ = 1 := by
  rcases ℓ with ⟨i, m, j, _⟩; rfl

/-- **Every member of the family records at `d` for every procedure** (Definition 7): one
`d`-node per run, `O = ⊤` subtree-veridical, the drawn act is the world's act coordinate.
Source: [[decision-problems-v2]] Definition 7; mandate T2 witness (`s1Tree_recordsFor`)
Kind: P
Fidelity: exact -/
theorem s1Fam_recordsFor (C : Proc Unit (fun _ => Bool) ℚ) :
    RecordsFor s1Obs s1ActEv C (s1Fam ρ r0 r1 κ k0 k1 u) () := by
  intro ℓ _ _
  refine ⟨s1Fam_count ρ r0 r1 κ k0 k1 u ℓ, ?_⟩
  unfold s1Fam at ℓ ⊢
  rcases ℓ with ⟨i, m, j, _⟩
  rintro ⟨i', (_ | ⟨m', ⟨j', e⟩⟩)⟩ _ a ha
  · by_cases hi : i = i'
    · subst hi
      simp only [edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      refine ⟨?_, ?_, ?_⟩
      · intro ℓ' _; simp [s1Obs]
      · simp [s1ActEv]
      · intro a' ha'
        simp [s1ActEv] at ha'
        exact ha'.symm
    · simp [edgeOf_chance, hi] at ha
  · exact e.elim

/-- `ν` on the family as an eight-term sum. Source: none: infrastructure. Kind: L -/
theorem s1Fam_nu (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset W3) :
    nu C (s1Fam ρ r0 r1 κ k0 k1 u) X =
      ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
        if pt3 (decide (i = 0)) m (decide (j = 0)) ∈ X then
          leafLaw C (s1Fam ρ r0 r1 κ k0 k1 u) ⟨i, m, j, ()⟩ else 0 := by
  rw [nu_eq_sum]
  unfold s1Fam
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Tree.sum_leaves_leaf]
  rfl

/-- `ν` of a single world: `ρ_ℓ · C(d)(m) · κ'`. Source: none: infrastructure. Kind: L -/
theorem s1Fam_nu_singleton (C : Proc Unit (fun _ => Bool) ℚ) (ℓ m k : Bool) :
    nu C (s1Fam ρ r0 r1 κ k0 k1 u) {pt3 ℓ m k} =
      (if ℓ then ρ else 1 - ρ) * ((C ()).w m * (if k then κ ℓ m else 1 - κ ℓ m)) := by
  rw [s1Fam_nu]
  simp_rw [s1Fam_leafLaw]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, Finset.mem_singleton, pt3_inj, FinDistr.coin,
    decide_fin2_zero, decide_fin2_one]
  cases ℓ <;> cases m <;> cases k <;> simp

/-- `ν(⊤) = 1`. Source: none: infrastructure. Kind: L -/
theorem s1Fam_nu_univ (C : Proc Unit (fun _ => Bool) ℚ) :
    nu C (s1Fam ρ r0 r1 κ k0 k1 u) Finset.univ = 1 := nu_univ C _

/-- Every `d`-node decides the lesion cell `{ℓ = c}`.
Source: none: infrastructure
Kind: L -/
theorem s1Fam_decidedAt_ell (q : (s1Fam ρ r0 r1 κ k0 k1 u).DecNode) (c : Bool) :
    DecidedAt (s1Fam ρ r0 r1 κ k0 k1 u) q (Finset.univ.filter fun x : W3 => x 0 = c) := by
  unfold s1Fam at q ⊢
  rcases q with ⟨i, (_ | ⟨m', ⟨j', e⟩⟩)⟩
  · by_cases hi : decide (i = 0) = c
    · left
      rintro ⟨i', m, j, _⟩ hj
      rw [mem_leavesBelow] at hj
      by_cases hii : i' = i
      · subst hii; simp [hi]
      · simp [edgeOf_chance, hii] at hj
    · right
      rintro ⟨i', m, j, _⟩ hj
      rw [mem_leavesBelow] at hj
      by_cases hii : i' = i
      · subst hii; simp [hi]
      · simp [edgeOf_chance, hii] at hj
  · exact e.elim

/-- The lesion cells are pre-query for `d`. Source: mandate §3.1. Kind: L -/
theorem s1Fam_preQuery_ell (C : Proc Unit (fun _ => Bool) ℚ) (c : Bool) :
    PreQuery s1Obs C (s1Fam ρ r0 r1 κ k0 k1 u) () (Finset.univ.filter fun x : W3 => x 0 = c) :=
  fun _ _ _ q _ _ => s1Fam_decidedAt_ell ρ r0 r1 κ k0 k1 u q c

/-- **The strictly calibrated state at `O = ⊤`** of a family member.
Source: [[decision-problems-v2]] Definition 8; mandate T2 witness
Kind: D -/
def s1State (C : Proc Unit (fun _ => Bool) ℚ) : State W3 ℚ :=
  calibratedState C (s1Fam ρ r0 r1 κ k0 k1 u) Finset.univ (nu_univ_pos C _)

/-- `P_{s}(x) = ν{x}` at `O = ⊤`. Source: none: infrastructure. Kind: L -/
theorem s1State_w (C : Proc Unit (fun _ => Bool) ℚ) (x : W3) :
    (s1State ρ r0 r1 κ k0 k1 u C).P.w x = nu C (s1Fam ρ r0 r1 κ k0 k1 u) {x} := by
  simp [s1State, calibratedState, nuCondDistr, s1Fam_nu_univ]

/-- The strict clauses hold at `d` for the calibrated state.
Source: `dp-calibration` `strictClausesAt_calibratedState`
Kind: L -/
theorem s1State_strict (C : Proc Unit (fun _ => Bool) ℚ) :
    StrictClausesAt (fun _ => s1State ρ r0 r1 κ k0 k1 u C) s1Obs C (s1Fam ρ r0 r1 κ k0 k1 u) () :=
  strictClausesAt_calibratedState s1Obs C _ (fun _ => s1State ρ r0 r1 κ k0 k1 u C) ()
    (nu_univ_pos C _) rfl

/-- Self-transparency on the family: `P_{s}(m = b) = C(d)(b)`.
Source: `dp-calibration` `selfTransparent_of_recordsFor_strict`
Kind: L -/
theorem s1State_pr_act (C : Proc Unit (fun _ => Bool) ℚ) (b : Bool) :
    (s1State ρ r0 r1 κ k0 k1 u C).pr (actEvCoord 1 b) = (C ()).w b :=
  selfTransparent_of_recordsFor_strict s1Obs s1ActEv C _ (fun _ => s1State ρ r0 r1 κ k0 k1 u C)
    (s1Fam_recordsFor ρ r0 r1 κ k0 k1 u C) (nu_univ_pos C _)
    (fun _ => s1State_strict ρ r0 r1 κ k0 k1 u C) b

end fam

/-! ## Helpers for the parent cells -/

/-- A parent cell is everything when the act has no parents.
Source: none: infrastructure
Kind: L -/
theorem parentCell_eq_univ_of_parents_empty (Γ : CausalStructure (fun _ : Fin 3 => Bool))
    (m : Fin 3) (h : Γ.G.parents m = ∅) (c : ParentVals Γ.G (fun _ : Fin 3 => Bool) m) :
    parentCell Γ m c = Finset.univ := by
  ext x
  simp only [parentCell, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  funext i
  exact absurd i.2 (Finset.eq_empty_iff_forall_notMem.mp h i.1)

/-- `⊤` is pre-query at every point. Source: none: infrastructure. Kind: L -/
theorem preQuery_univ {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
    [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (obs : ι → Finset Ω)
    (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι) : PreQuery obs C B d Finset.univ :=
  fun _ _ _ _ _ _ => Or.inl fun _ _ => Finset.mem_univ _

/-- `∑_{x ∈ X} Q(x) = Q(X)`. Source: none: infrastructure. Kind: L -/
theorem sum_mass_eq_prob {S : Type} [Fintype S] [DecidableEq S] (Q : Distr S) (X : Finset S) :
    ∑ x ∈ X, Q.mass x = Q.prob ↑X := by
  rw [prob_eq_sum_ite, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-! ## The direct-effect tree and the bridge -/

/-- The label `C(d) = (1/2, 1/2)` on a one-point boolean tree. Source: none: infrastructure. Kind: D -/
def procHalf : Proc Unit (fun _ => Bool) ℚ := fun _ => FinDistr.bool (1/2) (by norm_num) (by norm_num)

/-- `κ ℓ m = γ_ℓ + τ·m` at `γ = (1/20, 3/5)`, `τ = 1/5`. Source: mandate T3(B). Kind: D -/
def dRateQ (ℓ m : Bool) : ℚ := (if ℓ then 3/5 else 1/20) + (if m then 1/5 else 0)

/-- `0 ≤ dRateQ`. Source: none: infrastructure. Kind: L -/
theorem dRateQ_nonneg (ℓ m : Bool) : 0 ≤ dRateQ ℓ m := by
  cases ℓ <;> cases m <;> norm_num [dRateQ]

/-- `dRateQ ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem dRateQ_le_one (ℓ m : Bool) : dRateQ ℓ m ≤ 1 := by
  cases ℓ <;> cases m <;> norm_num [dRateQ]

/-- **The direct-effect tree** (`s1DirectTree` at `ρ = 1/10`, `γ = (1/20, 3/5)`, `τ = 1/5`).
Source: [[learning-cdt-renderings]] "Checks" ("With a direct effect `m → k` added (still
recorded)"); mandate T3(B)
Kind: D -/
def directTree (u : W3 → ℚ) : Tree W3 Unit (fun _ => Bool) ℚ :=
  s1Fam (1/10) (by norm_num) (by norm_num) dRateQ dRateQ_nonneg dRateQ_le_one u

/-- The strictly calibrated state of the direct-effect tree at label `1/2`.
Source: mandate T3(B)
Kind: D -/
def directState (u : W3 → ℚ) : State W3 ℚ :=
  s1State (1/10) (by norm_num) (by norm_num) dRateQ dRateQ_nonneg dRateQ_le_one u procHalf

/-- **The bridge**: the calibrated state of the direct-effect tree at label `1/2`, pushed to
FAF's `Distr`, is `directP`.
Source: mandate §3.3 (the seam), T3(B)
Kind: L -/
theorem directTree_toDistr (u : W3 → ℚ) :
    State.toDistr (State.castℝ (directState u)) = directP := by
  apply Distr.ext
  funext x
  rw [eq_pt3 x]
  simp only [State.toDistr_mass, State.castℝ, FinDistr.castℝ, directState, s1State_w,
    s1Fam_nu_singleton, directP, distr3_mass, dMass, dRate, procHalf, FinDistr.bool, dRateQ]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> norm_num

/-- `sColl` is a structure for the direct-effect tree's calibrated state.
Source: mandate T2 witness
Kind: L -/
theorem sColl_isFor_direct (u : W3 → ℚ) :
    sColl.IsFor (State.toDistr (State.castℝ (directState u))) := by
  rw [directTree_toDistr]; exact sColl_isFor

/-- `P_{s}(m = b) > 0` on the direct-effect tree at label `1/2`.
Source: none: infrastructure
Kind: L -/
theorem directState_act_pos (u : W3 → ℚ) (b : Bool) :
    0 < (State.toDistr (State.castℝ (directState u))).prob {x | x 1 = b} := by
  rw [directTree_toDistr]; exact directP_m_pos b

/-- **Theorem 3(ii) instantiated on the direct-effect tree** (N+): at label `1/2`, with the
collider structure `sColl` (`pa(m) = ∅`), the truncated law of each act equals the calibrated
act-conditional — derived through `thm3_ii` from `s1Fam_recordsFor`, `s1State_strict` and the
trivially pre-query parent cell, not by direct computation.
Source: [[learning-cdt-renderings]] Theorem 3(ii); mandate T2 witness
Kind: N+ -/
theorem direct_collapse (u : W3 → ℚ) (b : Bool) :
    sColl.truncate 1 b
      = condDistr (State.toDistr (State.castℝ (directState u))) {x | x 1 = b}
          (directState_act_pos u b) :=
  thm3_ii s1Obs s1ActEv (fun _ => directState u)
    (s1Fam_recordsFor _ _ _ _ _ _ u procHalf) (nu_univ_pos procHalf _)
    (s1State_strict _ _ _ _ _ _ u procHalf) 1 id (fun _ => rfl) sColl (sColl_isFor_direct u)
    (fun c => by
      rw [parentCell_eq_univ_of_parents_empty sColl 1 gColl_parents.2.1 c]
      exact preQuery_univ s1Obs procHalf (directTree u) ()) b (directState_act_pos u b)

/-- The act-conditionals of `k` on the direct-effect tree's calibrated state: `61/200` and
`21/200`, and the truncated `k`-rates coincide with them.
Source: [[learning-cdt-renderings]] "Checks"; mandate T3(B)
Kind: N+ -/
theorem direct_k_rates (u : W3 → ℚ) (b : Bool) :
    (sColl.truncate 1 b).prob {x | x 2 = true} = if b then 61/200 else 21/200 := by
  rw [sColl_collapse, condDistr_prob, directP_k_given]

/-- `A_d^+ = A_d` on the direct-effect tree at label `1/2`.
Source: none: infrastructure
Kind: L -/
theorem directState_aPlus (u : W3 → ℚ) :
    APlus (fun _ => directState u) s1ActEv () = Finset.univ := by
  ext b
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, s1ActEv_eq]
  rw [directState, s1State_pr_act]
  cases b <;> norm_num [procHalf, FinDistr.bool]

/-- **Theorem 3(iv) instantiated on the direct-effect tree** (N+): for every supervenient payoff
`u`, at label `1/2`, `T_CDT` with `cf^{sColl}` and `T_EDT` approve the same labels at `d` — the
proviso holds because `A_d^+ = A_d` at a mixed label and a finite argmax is nonempty.
Source: [[learning-cdt-renderings]] Theorem 3(iv); mandate T2(iv)
Kind: N+ -/
theorem direct_tcdt_iff_tedt (u : W3 → ℚ) :
    TCdtAt (fun _ => directState u) s1ActEv procHalf ()
        (fun a => cfG sColl 1 (fun x => (u x : ℝ)) a)
      ↔ TEdtAt (fun _ => directState u) s1ActEv procHalf () := by
  refine thm3_iv s1Obs s1ActEv (fun _ => directState u)
    (s1Fam_recordsFor _ _ _ _ _ _ u procHalf) (nu_univ_pos procHalf _)
    (s1State_strict _ _ _ _ _ _ u procHalf) 1 id (fun _ => rfl) sColl (sColl_isFor_direct u)
    (fun c => by
      rw [parentCell_eq_univ_of_parents_empty sColl 1 gColl_parents.2.1 c]
      exact preQuery_univ s1Obs procHalf (directTree u) ())
    u (s1Fam_payoff _ _ _ _ _ _ u) ?_
  rw [directState_aPlus, Finset.inter_univ]
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ
    (fun a => (cfG sColl 1 (fun x => (u x : ℝ)) (id a)).V (s1ActEv () a)) Finset.univ_nonempty
  exact ⟨a, (mem_argmaxAll _ a).mpr fun b => ha b (Finset.mem_univ b)⟩

/-! ## The temporal witness `ℓ → m` (repair round 1, audit r1 N1/N2)

`direct_collapse` instantiates Theorem 3(ii) with `sColl`, whose act has no parents, so the
parent-cell hypothesis is discharged by `preQuery_univ`. The instance below uses the temporal
structure `sLMK` (`ℓ → m`, `pa(m) = {ℓ}`): its parent cells are the lesion cells, which
`s1Fam_preQuery_ell` proves pre-query by real `DecidedAt` reasoning — the hypothesis
"`pa_G(m) ⊆ V₀`" is now exercised, not vacuous. -/

/-- `0 ∈ gLMK.parents 1`. Source: none: infrastructure. Kind: L -/
theorem zero_mem_parents_LMK : (0 : Fin 3) ∈ gLMK.parents 1 := by
  rw [gLMK_parents.2.1]; simp

/-- The parent cell of `m` in `sLMK` at configuration `c` is the lesion cell `{x | x 0 = c ⟨0, _⟩}`.
Source: none: infrastructure
Kind: L -/
theorem parentCell_sLMK (c : ParentVals gLMK (fun _ : Fin 3 => Bool) 1) :
    parentCell sLMK 1 c = Finset.univ.filter fun x : W3 => x 0 = c ⟨0, zero_mem_parents_LMK⟩ := by
  ext x
  simp only [parentCell, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact congrFun h ⟨0, zero_mem_parents_LMK⟩
  · intro h
    funext i
    have hi : i.1 = 0 := by
      have hmem : (i.1 : Fin 3) ∈ gLMK.parents 1 := i.2
      rw [gLMK_parents.2.1, Finset.mem_singleton] at hmem
      exact hmem
    have hi' : i = ⟨0, zero_mem_parents_LMK⟩ := Subtype.ext hi
    rw [hi']
    exact h

/-- **Theorem 3(ii) on the direct-effect tree with the temporal structure `ℓ → m`** (N+, the
witness of record for (ii)): the parent-cell hypothesis is the real `s1Fam_preQuery_ell`, not
`preQuery_univ`; label `1/2`, `ρ = 1/10`, `γ = (1/20, 3/5)`, `τ = 1/5`.
Source: [[learning-cdt-renderings]] Theorem 3(ii) ("holds whenever `pa_G(m) ⊆ V₀`"); mandate T2
witness ("the temporal DAG")
Kind: N+ -/
theorem direct_collapse_LMK (u : W3 → ℚ) (b : Bool) :
    sLMK.truncate 1 b
      = condDistr (State.toDistr (State.castℝ (directState u))) {x | x 1 = b}
          (directState_act_pos u b) :=
  thm3_ii s1Obs s1ActEv (fun _ => directState u)
    (s1Fam_recordsFor _ _ _ _ _ _ u procHalf) (nu_univ_pos procHalf _)
    (s1State_strict _ _ _ _ _ _ u procHalf) 1 id (fun _ => rfl) sLMK
    (by rw [directTree_toDistr]; exact sLMK_isFor)
    (fun c => by
      rw [parentCell_sLMK c]
      exact s1Fam_preQuery_ell _ _ _ _ _ _ u procHalf _) b (directState_act_pos u b)

/-- **Theorem 3(iv) on the direct-effect tree with the temporal structure `ℓ → m`** (N+): for
every supervenient payoff, `T_CDT` with `cf^{sLMK}` and `T_EDT` approve the same labels at `d`,
with the parent-cell hypothesis exercised.
Source: [[learning-cdt-renderings]] Theorem 3(iv); mandate T2(iv)
Kind: N+ -/
theorem direct_tcdt_iff_tedt_LMK (u : W3 → ℚ) :
    TCdtAt (fun _ => directState u) s1ActEv procHalf ()
        (fun a => cfG sLMK 1 (fun x => (u x : ℝ)) a)
      ↔ TEdtAt (fun _ => directState u) s1ActEv procHalf () := by
  refine thm3_iv s1Obs s1ActEv (fun _ => directState u)
    (s1Fam_recordsFor _ _ _ _ _ _ u procHalf) (nu_univ_pos procHalf _)
    (s1State_strict _ _ _ _ _ _ u procHalf) 1 id (fun _ => rfl) sLMK
    (by rw [directTree_toDistr]; exact sLMK_isFor)
    (fun c => by
      rw [parentCell_sLMK c]
      exact s1Fam_preQuery_ell _ _ _ _ _ _ u procHalf _)
    u (s1Fam_payoff _ _ _ _ _ _ u) ?_
  rw [directState_aPlus, Finset.inter_univ]
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ
    (fun a => (cfG sLMK 1 (fun x => (u x : ℝ)) (id a)).V (s1ActEv () a)) Finset.univ_nonempty
  exact ⟨a, (mem_argmaxAll _ a).mpr fun b => ha b (Finset.mem_univ b)⟩

end Cleanroom.Decision.DpCausalConsist
