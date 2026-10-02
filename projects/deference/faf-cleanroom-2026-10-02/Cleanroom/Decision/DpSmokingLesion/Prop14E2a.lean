import Cleanroom.Decision.DpSmokingLesion.Prop13

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# T4(b): the reference class E2a — coverage failure, honest at the OC grades, screened at SSC

[[dp-smoking-lesion-mandate]] T4(b), on `e2a₀` (`Prop11.lean`, S3's numbers).

* Coverage fails for every procedure (`e2a_not_covers`: the reference-class leaf `(ℓ=1, m=1, k=1)`
  has mass `2673/8000`, satisfies `⊤`, meets no `d`-node), hence recording fails
  (`e2a_not_recordsFor`); the strictly calibrated state satisfies (S2) for every `C`
  (`Prop11.lean`, `e2a_S2_calibrated`).
* Verdicts: at `δ_refrain` both acts are subjectively possible (the reference class realizes
  `m = 1`), `V(smoke) = −891 000 < −1 972 000/11 = V(refrain)`, so `δ_refrain` is
  `T_EDT`-approved **non-vacuously** (`e2a_refrain_approved`); at `δ_smoke`,
  `V(smoke) = −9 017 000/11 < −108 000 = V(refrain)`, so `δ_smoke` is rejected
  (`e2a_smoke_rejected`); R1-state `(−499 450, −499 550)` smokes for every label
  (`e2a_r1State`); R2-SIA at `C(d) = ½`: `(−49 900, −50 000)` over `∑_q R_q = 1/10`, i.e.
  `(−499 000, −500 000)`, smokes (`e2a_r2Sia`), and both readings of R2-real coincide with it
  (both `d`-nodes are veridical and active, `e2a_realFiber`).
* **Screened at both SSC grades** (`prop14_e2a_screened_perRun`, `prop14_e2a_screened_perOcc`):
  `occ(d)` is the "me" branch, within which the tree records, so the per-run state's
  act-conditionals of cancer are flat and (S2) fails — for every procedure and every state.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

section e2aBattery

/-- Every leaf of `e2a₀` is a "me" leaf `⟨i, 0, m, j, ()⟩` or an "other" leaf `⟨i, 1, j, k, ()⟩`.
Source: none: infrastructure. Kind: L -/
theorem e2a_leaves (ℓ : e2a₀.Leaves) :
    (∃ (i : Fin 2) (m : Bool) (j : Fin 2), ℓ = ⟨i, 0, m, j, ()⟩) ∨
    (∃ (i j k : Fin 2), ℓ = ⟨i, 1, j, k, ()⟩) := by
  unfold e2a₀ at ℓ
  rcases ℓ with ⟨i, t, ℓ⟩
  fin_cases t
  · unfold e2aMe kBlock slLeaf at ℓ
    rcases ℓ with ⟨m, j, ⟨⟩⟩
    exact Or.inl ⟨i, m, j, rfl⟩
  · unfold e2aOther kBlock slLeaf at ℓ
    rcases ℓ with ⟨j, k, ⟨⟩⟩
    exact Or.inr ⟨i, j, k, rfl⟩

/-- The "me" runs meet `d` once; the "other" runs never.
Source: `sl_zoo.py` line 130 ("the agent is a share `π` of the runs")
Kind: L -/
theorem e2a_count :
    (∀ (i : Fin 2) (m : Bool) (j : Fin 2), count () e2a₀ ⟨i, 0, m, j, ()⟩ = 1) ∧
    (∀ (i j k : Fin 2), count () e2a₀ ⟨i, 1, j, k, ()⟩ = 0) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- E2a is almost fair. Source: none: infrastructure. Kind: L -/
theorem e2a_almostFair : AlmostFair e2a₀ := by
  intro d ℓ; cases d
  rcases e2a_leaves ℓ with ⟨i, m, j, rfl⟩ | ⟨i, j, k, rfl⟩
  · exact (e2a_count.1 i m j).le
  · rw [e2a_count.2]; exact zero_le_one

/-- **Coverage fails on E2a for every procedure**: the reference-class leaf `(1, 1, 1)` has mass
`½ · 9/10 · 9/10 · 99/100 = 2673/8000 > 0`, its world satisfies `⊤`, and it meets no `d`-node.
Source: `sl-defensible-claims.md` S2 (R-a: "other agents … write the act coordinate on runs
that never consult `d`"); mandate T4(b)
Kind: N− -/
theorem e2a_not_covers (C : Proc Unit (fun _ => Bool) ℚ) : ¬ Covers slObs C e2a₀ () := by
  intro h
  have hpos : 0 < leafLaw C e2a₀ ⟨0, 1, 0, 0, ()⟩ := by rw [e2a_leafLaw_other]; norm_num
  have := h ⟨0, 1, 0, 0, ()⟩ hpos (Finset.mem_univ _)
  rw [e2a_count.2] at this
  exact lt_irrefl 0 this

/-- E2a is not Definition-7 recorded at `d` for any procedure (clause 1 fails by coverage).
Source: mandate T4(b)
Kind: N− -/
theorem e2a_not_recordsFor (C : Proc Unit (fun _ => Bool) ℚ) :
    ¬ RecordsFor slObs slActEv C e2a₀ () :=
  fun h => e2a_not_covers C (h.covers slObs slActEv)

/-- The two payoff masses on E2a as closed forms in the label `q`:
`paySum(m=1) = −49 900q − 400 950`, `paySum(m=0) = 50 000q − 98 600`.
Source: mandate T4(b), T17 (recomputed)
Kind: L -/
theorem e2a_paySum_values (C : Proc Unit (fun _ => Bool) ℚ) :
    paySum C e2a₀ (evM true) = -49900 * (C ()).w true - 400950 ∧
    paySum C e2a₀ (evM false) = 50000 * (C ()).w true - 98600 := by
  have hw := w_false_eq_one_sub C
  constructor <;>
  · rw [e2a_paySum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, e2a_leafLaw_me, e2a_leafLaw_other, mem_evM,
      ticklePay]
    simp [hw]; ring

/-- **`δ_refrain` is strictly calibrated and `T_EDT`-approved on E2a, non-vacuously**: at its
strictly calibrated state both acts are subjectively possible (`P(m=1) = 9/20`, written by the
reference class) and `V(smoke) = −891 000 < −1 972 000/11 = V(refrain)`, so refrain is the
evidential argmax and smoke is not. (The mandate's "refrain is the unique element of `A_d^+`
— vacuous" is wrong here: coverage failure puts the unplayed act into `A_d^+`; findings.)
Source: `sl-defensible-claims.md` S2 (R-a: "`C = refrain` is strictly calibrated *and*
`T_EDT`-approved"); mandate T4(b)
Kind: N+ -/
theorem e2a_refrain_approved :
    let s₀ : Unit → State TickleW ℚ :=
      fun _ => calibratedState procRefrain e2a₀ Finset.univ (nu_univ_pos _ _)
    StrictOCAt s₀ slObs procRefrain e2a₀ () ∧ true ∈ APlus s₀ slActEv () ∧
      false ∈ APlus s₀ slActEv () ∧ (s₀ ()).V (evM true) = -891000 ∧
      (s₀ ()).V (evM false) = -1972000/11 ∧ false ∈ argmaxPlus s₀ slActEv () ∧
      true ∉ argmaxPlus s₀ slActEv () ∧ TEdtAt s₀ slActEv procRefrain () := by
  intro s₀
  obtain ⟨hn1, -, hn3, -⟩ := e2a_nu_values procRefrain
  obtain ⟨hp1, hp3⟩ := e2a_paySum_values procRefrain
  have hA : ∀ m, (s₀ ()).pr (evM m) = nu procRefrain e2a₀ (evM m) := by
    intro m; simp [s₀, calibratedState_pr, nu_univ]
  have hV : ∀ m, (s₀ ()).V (evM m) = paySum procRefrain e2a₀ (evM m) / nu procRefrain e2a₀ (evM m) := by
    intro m; simp [s₀, calibratedState_V]
  have ht : true ∈ APlus s₀ slActEv () := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, slActEv_apply, hA, hn1]
    norm_num [procRefrain]
  have hf : false ∈ APlus s₀ slActEv () := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, slActEv_apply, hA, hn3]
    norm_num [procRefrain]
  have hVt : (s₀ ()).V (evM true) = -891000 := by
    rw [hV, hp1, hn1]; norm_num [procRefrain]
  have hVf : (s₀ ()).V (evM false) = -1972000/11 := by
    rw [hV, hp3, hn3]; norm_num [procRefrain]
  have hAplus : APlus s₀ slActEv () = Finset.univ := by
    ext a; cases a <;> simp [hf, ht]
  have hfmax : false ∈ argmaxPlus s₀ slActEv () := by
    rw [mem_argmaxPlus, hAplus]
    refine ⟨Finset.mem_univ _, fun b _ => ?_⟩
    cases b <;> simp only [slActEv_apply, hVt, hVf] <;> norm_num
  have htmax : true ∉ argmaxPlus s₀ slActEv () := by
    rw [mem_argmaxPlus, hAplus]
    rintro ⟨-, h⟩
    have := h false (Finset.mem_univ _)
    simp only [slActEv_apply, hVt, hVf] at this
    norm_num at this
  refine ⟨strictOCAt_calibratedState slObs _ _ s₀ () _ rfl, ht, hf, hVt, hVf, hfmax, htmax, ?_⟩
  intro _ a ha
  cases a
  · exact hfmax
  · simp [procRefrain] at ha

/-- **`δ_smoke` is strictly calibrated on E2a but `T_EDT` rejects it**: `V(smoke) = −9 017 000/11 <
−108 000 = V(refrain)` at its calibrated state, and `C(d)(smoke) = 1 > 0`.
Source: `sl-defensible-claims.md` S2 (R-a: "strict-OC EDT at `C = smoke` has
`V(smoke) ≈ −819 727 < −108 000 = V(refrain)` and refrains"); mandate T4(b)
Kind: N+ -/
theorem e2a_smoke_rejected :
    let s₀ : Unit → State TickleW ℚ :=
      fun _ => calibratedState procSmoke e2a₀ Finset.univ (nu_univ_pos _ _)
    StrictOCAt s₀ slObs procSmoke e2a₀ () ∧ (s₀ ()).V (evM true) = -9017000/11 ∧
      (s₀ ()).V (evM false) = -108000 ∧ ¬ TEdtAt s₀ slActEv procSmoke () := by
  intro s₀
  obtain ⟨hn1, -, hn3, -⟩ := e2a_nu_values procSmoke
  obtain ⟨hp1, hp3⟩ := e2a_paySum_values procSmoke
  have hA : ∀ m, (s₀ ()).pr (evM m) = nu procSmoke e2a₀ (evM m) := by
    intro m; simp [s₀, calibratedState_pr, nu_univ]
  have hV : ∀ m, (s₀ ()).V (evM m) = paySum procSmoke e2a₀ (evM m) / nu procSmoke e2a₀ (evM m) := by
    intro m; simp [s₀, calibratedState_V]
  have hVt : (s₀ ()).V (evM true) = -9017000/11 := by
    rw [hV, hp1, hn1]; norm_num [procSmoke]
  have hVf : (s₀ ()).V (evM false) = -108000 := by
    rw [hV, hp3, hn3]; norm_num [procSmoke]
  have hf : false ∈ APlus s₀ slActEv () := by
    simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and, slActEv_apply, hA, hn3]
    norm_num [procSmoke]
  refine ⟨strictOCAt_calibratedState slObs _ _ s₀ () _ rfl, hVt, hVf, ?_⟩
  intro h
  have := h ⟨false, hf⟩ true (by simp [procSmoke])
  rw [mem_argmaxPlus] at this
  have h2 := this.2 false hf
  simp only [slActEv_apply, hVt, hVf] at h2
  norm_num at h2

/-- **R1-state on E2a is `(−499 450, −499 550)` for every label** (label-free: the all-instance
deviations `δ_smoke`, `δ_refrain` at `O = ⊤`): it smokes.
Source: `sl-synthesis.md` §1.1 (Reference class: "R1-state `(−499 450, −499 550)`"); mandate
T4(b)
Kind: N+ -/
theorem e2a_r1State (C : Proc Unit (fun _ => Bool) ℚ) :
    r1StateVal slObs C e2a₀ () true = -499450 ∧ r1StateVal slObs C e2a₀ () false = -499550 := by
  have key : ∀ (C' : Proc Unit (fun _ => Bool) ℚ), paySum C' e2a₀ Finset.univ =
      paySum C' e2a₀ (evM true) + paySum C' e2a₀ (evM false) := by
    intro C'
    rw [← evM_union, paySum_union C' e2a₀ evM_disjoint]
  constructor
  · unfold r1StateVal r1StatePay r1StateNu
    simp only [slObs_apply, nu_univ, div_one]
    rw [key, (e2a_paySum_values _).1, (e2a_paySum_values _).2]
    simp [Proc.deviatePure, Proc.deviate_same]; norm_num
  · unfold r1StateVal r1StatePay r1StateNu
    simp only [slObs_apply, nu_univ, div_one]
    rw [key, (e2a_paySum_values _).1, (e2a_paySum_values _).2]
    simp [Proc.deviatePure, Proc.deviate_same]; norm_num

/-! ### R2-SIA and R2-real at `C(d) = ½` -/

/-- The label `C(d) = ½` on E2a. Source: mandate T4(b). Kind: D -/
abbrev e2aHalf : Proc Unit (fun _ => Bool) ℚ := procBool (1/2) (by norm_num) (by norm_num)

/-- The `d`-node of lesion branch `i` (on the "me" sub-branch). Source: none: infrastructure. Kind: D -/
def e2aNode (i : Fin 2) : e2a₀.DecNode := ⟨i, 0, none⟩

/-- Every decision node of E2a is one of the two `d`-nodes. Source: none: infrastructure. Kind: L -/
theorem e2a_nodes_cases (q : e2a₀.DecNode) : ∃ i : Fin 2, q = e2aNode i := by
  unfold e2a₀ at q
  rcases q with ⟨i, t, q⟩
  fin_cases t
  · unfold e2aMe kBlock slLeaf at q
    rcases q with (_ | ⟨m, ⟨j, e⟩⟩)
    · exact ⟨i, rfl⟩
    · exact e.elim
  · unfold e2aOther kBlock slLeaf at q
    rcases q with ⟨j, ⟨k, e⟩⟩
    exact e.elim

/-- The edges at the `d`-node of branch `i`: a "me" leaf of the same branch takes its act's
edge, every other leaf is off the node.
Source: none: infrastructure. Kind: L -/
theorem e2a_edgeOf :
    (∀ (i i' : Fin 2) (m : Bool) (j : Fin 2), edgeOf e2a₀ (e2aNode i) ⟨i', 0, m, j, ()⟩ =
      if i' = i then some m else none) ∧
    (∀ (i i' j k : Fin 2), edgeOf e2a₀ (e2aNode i) ⟨i', 1, j, k, ()⟩ = none) := by
  constructor
  · intro i i' m j
    unfold e2aNode e2a₀
    by_cases h : i' = i
    · subst h; simp [edgeOf_chance, e2aMe, edgeOf_decision_none]
    · simp [edgeOf_chance, h]
  · intro i i' j k
    unfold e2aNode e2a₀
    by_cases h : i' = i
    · subst h; simp [edgeOf_chance]
    · simp [edgeOf_chance, h]

/-- **Cancer is post-query independent of the draw on E2a, for every procedure**: at each
`d`-node (on the "me" branch) the `k`-mass below either action edge is `γ_ℓ` times the edge
mass. So `prop14_only_if` applies to E2a.
Source: mandate T4(a) (`PostQueryIndep evK` on the failing trees); audit r1 adversarial N7,
fidelity §3.7
Kind: N+ -/
theorem e2a_postQueryIndep (C : Proc Unit (fun _ => Bool) ℚ) : PostQueryIndep C e2a₀ () evK := by
  intro q _ a b
  obtain ⟨i, rfl⟩ := e2a_nodes_cases q
  have hin : ∀ a : Bool, edgeMassIn C e2a₀ evK (e2aNode i) a =
      1/20 * (C ()).w a * (if i = 0 then 99/100 else 1/100) := by
    intro a
    unfold edgeMassIn
    rw [e2a_sum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, e2a_edgeOf.1, e2a_edgeOf.2, e2a_leafLaw_me,
      e2a_leafLaw_other, e2a_world.1, e2a_world.2, mem_evK]
    fin_cases i <;> cases a <;> simp <;> norm_num
  have hm : ∀ a : Bool, edgeMass C e2a₀ (e2aNode i) a = 1/20 * (C ()).w a := by
    intro a
    unfold edgeMass
    rw [e2a_sum]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, e2a_edgeOf.1, e2a_edgeOf.2, e2a_leafLaw_me,
      e2a_leafLaw_other]
    fin_cases i <;> cases a <;> simp <;> ring
  rw [hin, hin, hm, hm]; ring

/-- The fiber of `d` on E2a is every decision node. Source: none: infrastructure. Kind: L -/
theorem e2a_fiber : fiber e2a₀ () = Finset.univ := by
  ext q; simp [fiber]

/-- A sum over the decision nodes of E2a. Source: none: infrastructure. Kind: L -/
theorem e2a_sum_decNode (f : e2a₀.DecNode → ℚ) : ∑ q, f q = f (e2aNode 0) + f (e2aNode 1) := by
  unfold e2aNode
  unfold e2a₀ at f ⊢
  rw [sum_decNode_chance, Fin.sum_univ_two]
  have hbranch : ∀ i : Fin 2, (∑ q, f ⟨i, q⟩) = f ⟨i, 0, none⟩ := by
    intro i
    rw [sum_decNode_chance, Fin.sum_univ_two]
    have h0 : (∑ q, f ⟨i, 0, q⟩) = f ⟨i, 0, none⟩ := by
      show (∑ q : (e2aMe i).DecNode, f ⟨i, 0, q⟩) = _
      unfold e2aMe kBlock slLeaf
      rw [sum_decNode_decision]
      rw [Finset.sum_eq_zero (fun m _ => Finset.sum_eq_zero (fun q _ => by
        rcases q with ⟨j, e⟩; exact e.elim)), add_zero]
    have h1 : (∑ q, f ⟨i, 1, q⟩) = 0 := by
      show (∑ q : (e2aOther i).DecNode, f ⟨i, 1, q⟩) = _
      unfold e2aOther kBlock slLeaf
      exact Finset.sum_eq_zero (fun q _ => by rcases q with ⟨j, k, e⟩; exact e.elim)
    rw [h0, h1, add_zero]
  rw [hbranch 0, hbranch 1]

/-- The edge payoff masses at the `d`-node of branch `i` under `C(d) = ½`:
`(1/40)(1000·[a] − 10⁶ γ_ℓ)`.
Source: none: infrastructure. Kind: L -/
theorem e2a_edgePay (i : Fin 2) (a : Bool) :
    (∑ ℓ, if edgeOf e2a₀ (e2aNode i) ℓ = some a then leafLaw e2aHalf e2a₀ ℓ * payoff e2a₀ ℓ
      else 0) = 1/40 * ((if a then 1000 else 0) - 1000000 * (if i = 0 then 99/100 else 1/100)) := by
  rw [e2a_sum]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, e2a_edgeOf.1, e2a_edgeOf.2, e2a_leafLaw_me,
    e2a_leafLaw_other, procBool, FinDistr.bool_true, FinDistr.bool_false]
  have hpay : ∀ (i' : Fin 2) (m : Bool) (j : Fin 2), payoff e2a₀ ⟨i', 0, m, j, ()⟩ =
      ticklePay 1000 1000000 (decide (i' = 0), m, decide (j = 0)) := fun _ _ _ => rfl
  simp only [hpay, ticklePay]
  fin_cases i <;> cases a <;> simp <;> norm_num

/-- The forcing masses on E2a at `C(d) = ½`: `forcedBelow_{q_ℓ}(a) = (1/20)(1000·[a] − 10⁶ γ_ℓ)`.
Source: [[decision-problems-v2]] §8 (`R_q G_q`); mandate T4(b)
Kind: L -/
theorem e2a_forcedBelow (i : Fin 2) (a : Bool) :
    forcedBelow e2a₀ (NodePolicy.ofProc e2aHalf e2a₀) (e2aNode i) a =
      1/20 * ((if a then 1000 else 0) - 1000000 * (if i = 0 then 99/100 else 1/100)) := by
  have h := edge_paySum_eq_mul_forcedBelow e2aHalf e2a₀ (e2aNode i) a
  rw [e2a_edgePay] at h
  have hw : (e2aHalf (pt e2a₀ (e2aNode i))).w a = 1/2 := by cases a <;> norm_num [procBool]
  rw [hw] at h
  linarith

/-- `R_{q_ℓ} = 1/20` on E2a (`ρ_ℓ · π = ½ · 1/10`). Source: none: infrastructure. Kind: L -/
theorem e2a_reach (i : Fin 2) : reach e2aHalf e2a₀ (e2aNode i) = 1/20 := by
  unfold e2aNode e2a₀ e2aMe
  simp only [reach_chance, Lesion.coinL, Lesion.fdt, FinDistr.coin]
  fin_cases i <;> simp <;> norm_num

/-- **R2-SIA on E2a at `C(d) = ½`**: `r2Sia = (−49 900, −50 000)` over `∑_q R_q = 1/10`, i.e.
`(−499 000, −500 000)`: it smokes.
Source: `sl-synthesis.md` §1.1 (Reference class: "R2-SIA all smoke"; "R2-real
`(−499 000, −500 000)`"); mandate T4(b)
Kind: N+ -/
theorem e2a_r2Sia :
    r2Sia e2aHalf e2a₀ () true = -49900 ∧ r2Sia e2aHalf e2a₀ () false = -50000 ∧
    fiberMass e2aHalf e2a₀ () = 1/10 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold r2Sia
    rw [e2a_fiber, e2a_sum_decNode]
    simp only [dite_true, transport_const, e2a_forcedBelow]
    norm_num
  · unfold r2Sia
    rw [e2a_fiber, e2a_sum_decNode]
    simp only [dite_true, transport_const, e2a_forcedBelow]
    norm_num
  · unfold fiberMass
    rw [e2a_fiber, e2a_sum_decNode, e2a_reach, e2a_reach]; norm_num

/-- Both `d`-nodes of E2a are a.s. node-action-veridical and active at `C(d) = ½`, so both
readings of R2-real average the whole fiber: R2-real = R2-SIA here.
Source: `sl-synthesis.md` §1.1; mandate T4(b) ("R2-real reading 2: `(−499 000, −500 000)`")
Kind: L -/
theorem e2a_realFiber :
    realFiber slObs slActEv e2aHalf e2a₀ () = Finset.univ ∧
    realFiberAll slActEv e2aHalf e2a₀ () = Finset.univ := by
  have hnav : ∀ i, NodeActionVeridicalAS slActEv e2aHalf e2a₀ (e2aNode i) := by
    intro i ℓ a _ ha
    rcases e2a_leaves ℓ with ⟨i', m, j, rfl⟩ | ⟨i', j, k, rfl⟩
    · rw [e2a_edgeOf.1] at ha
      by_cases h : i' = i
      · subst h
        simp only [if_true, Option.some.injEq] at ha
        subst ha
        rw [e2a_world.1]; simp [slActEv, evM]
      · simp [h] at ha
    · rw [e2a_edgeOf.2] at ha; exact absurd ha (by simp)
  have hact : ∀ i, ActiveNode slObs e2aHalf e2a₀ () (e2aNode i) := by
    intro i
    refine ⟨⟨i, 0, true, 0, ()⟩, ?_, Finset.mem_univ _, by rw [e2a_edgeOf.1]; simp⟩
    rw [e2a_leafLaw_me]; fin_cases i <;> norm_num [procBool]
  constructor
  · ext q
    rw [mem_realFiber]
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    obtain ⟨i, rfl⟩ := e2a_nodes_cases q
    exact ⟨rfl, hnav i, hact i⟩
  · ext q
    rw [mem_realFiberAll]
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    obtain ⟨i, rfl⟩ := e2a_nodes_cases q
    exact ⟨rfl, hnav i⟩

/-! ### The SSC grades screen the reference class -/

/-- `μ({λ ⊨ X} ∩ occ(d))` on E2a is the "me"-leaf mass of `X`.
Source: `sl-defensible-claims.md` S2 ("occurrence-conditioning … the unconsulted writers drop out")
Kind: L -/
theorem e2a_mass_occ (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset TickleW) :
    mass C e2a₀ (worldEv e2a₀ X ∩ occ () e2a₀) =
      ∑ i : Fin 2, ∑ m : Bool, ∑ j : Fin 2,
        if (decide (i = 0), m, decide (j = 0)) ∈ X then leafLaw C e2a₀ ⟨i, 0, m, j, ()⟩ else 0 := by
  have e : worldEv e2a₀ X ∩ occ () e2a₀ =
      Finset.univ.filter fun ℓ => world e2a₀ ℓ ∈ X ∧ 0 < count () e2a₀ ℓ := by
    ext ℓ; simp [worldEv, occ]
  rw [e, mass_filter, e2a_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : (∑ j : Fin 2, ∑ k : Fin 2,
      if world e2a₀ ⟨i, 1, j, k, ()⟩ ∈ X ∧ 0 < count () e2a₀ ⟨i, 1, j, k, ()⟩ then
        leafLaw C e2a₀ ⟨i, 1, j, k, ()⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero; intro j _; apply Finset.sum_eq_zero; intro k _
    rw [if_neg]; rintro ⟨-, h⟩; rw [e2a_count.2] at h; exact lt_irrefl 0 h
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
  rw [e2a_count.1, e2a_world.1]
  simp

/-- `μ(occ(d)) = 1/10` on E2a for every procedure. Source: none: infrastructure. Kind: L -/
theorem e2a_mass_occ_univ (C : Proc Unit (fun _ => Bool) ℚ) : mass C e2a₀ (occ () e2a₀) = 1/10 := by
  have := e2a_mass_occ C Finset.univ
  rw [worldEv_univ, Finset.univ_inter] at this
  rw [this]
  have hw := w_false_eq_one_sub C
  simp only [Fin.sum_univ_two, Fintype.sum_bool, e2a_leafLaw_me, Finset.mem_univ, if_true]
  simp [hw]; ring

/-- The four occurrence-restricted masses on E2a: `μ(m=1 ∩ occ) = q/10`, `μ(k ∧ m=1 ∩ occ) = q/20`,
`μ(m=0 ∩ occ) = (1−q)/10`, `μ(k ∧ m=0 ∩ occ) = (1−q)/20` — flat within `occ(d)`.
Source: `sl-defensible-claims.md` S2 (R-a: "within `occ(d)` the tree records"); mandate T4(b)
Kind: L -/
theorem e2a_mass_occ_values (C : Proc Unit (fun _ => Bool) ℚ) :
    mass C e2a₀ (worldEv e2a₀ (evM true) ∩ occ () e2a₀) = (C ()).w true / 10 ∧
    mass C e2a₀ (worldEv e2a₀ (evK ∩ evM true) ∩ occ () e2a₀) = (C ()).w true / 20 ∧
    mass C e2a₀ (worldEv e2a₀ (evM false) ∩ occ () e2a₀) = (1 - (C ()).w true) / 10 ∧
    mass C e2a₀ (worldEv e2a₀ (evK ∩ evM false) ∩ occ () e2a₀) = (1 - (C ()).w true) / 20 := by
  have hw := w_false_eq_one_sub C
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [e2a_mass_occ]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, e2a_leafLaw_me, Finset.mem_inter, mem_evM, mem_evK]
    simp [hw]; ring

/-- **Proposition 14: coverage failure is screened at the per-run SSC grade**: on E2a, for every
procedure and every state per-run calibrated at `d`, (S2) fails — `occ(d)` is the "me" branch,
within which the act-conditionals of cancer are flat.
Source: `sl-defensible-claims.md` S2 (R-a: "occurrence-conditioning (per-run / per-occurrence
SSC) **screens R-a**"); dp-sl-012; mandate T4(b)
Kind: C
Fidelity: exact
Hyps: (a) `PerRunSSCAt` -/
theorem prop14_e2a_screened_perRun (C : Proc Unit (fun _ => Bool) ℚ) (s : Unit → State TickleW ℚ)
    (hs : PerRunSSCAt s C e2a₀ ()) : ¬ S2 (s ()) := by
  have hocc := e2a_mass_occ_univ C
  have hcl := hs (by rw [hocc]; norm_num)
  obtain ⟨h1, h2, h3, h4⟩ := e2a_mass_occ_values C
  have hp : ∀ X, (s ()).pr X = 10 * mass C e2a₀ (worldEv e2a₀ X ∩ occ () e2a₀) := by
    intro X
    have := hcl.1 X
    rw [hocc] at this
    linarith
  rintro ⟨-, -, hlt⟩
  rw [hp, hp, hp, hp, h1, h2, h3, h4] at hlt
  nlinarith

/-- **Coverage failure is screened at the per-occurrence SSC grade** as well (E2a is almost fair).
Source: `sl-defensible-claims.md` S2 (R-a); mandate T4(b)
Kind: C
Fidelity: exact
Hyps: (a) `PerOccSSCAt` -/
theorem prop14_e2a_screened_perOcc (C : Proc Unit (fun _ => Bool) ℚ) (s : Unit → State TickleW ℚ)
    (hs : PerOccSSCAt s C e2a₀ ()) : ¬ S2 (s ()) :=
  prop14_e2a_screened_perRun C s
    ((perOccSSCAt_iff_perRunSSCAt_of_count_le_one_ae C e2a₀ () s (fun ℓ _ => e2a_almostFair () ℓ)).mp hs)

end e2aBattery

end Cleanroom.Decision.DpSmokingLesion
