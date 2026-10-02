import Cleanroom.Decision.DpReferentsCdt.C2A
import Cleanroom.Found.DpCoreTree.Witnesses
import Cleanroom.Found.DpCoreTree.Agreement

/-!
# Opaque Newcomb: the referents in closed form

`dp-core-tree`'s `opaqueNewcomb p h0 h1 L S` (a predictor `d`-node upstream samples `C(d)`, the box
is filled according to the sample with probability `p`, then the live `d`-node is queried;
`O_d = ⊤`) is the separator of the type axis (FA-18's last row, FA-19′, C2-2′(a)). This file gives
every referent of §3 on it in closed form in the label `q := C(d)(one)`, the reliability `p` and
the payoffs `L`, `S`, for **every** procedure `C`, under Definition 6 and under the shared seed:

* `opaque_value`, `opaque_nu_actEv`, `opaque_paySum_actEv` — the run law;
* `opaque_realFiber` — the real fiber is the four live nodes; `opaque_realReach = 1`,
  `opaque_realForced`, hence `opaque_refR2Real a = L·P(fill) + S·[a = two]` (label-dependent through
  `P(fill) = qp + (1−q)(1−p)`, act-independent in the fill term: the prediction is held fixed);
* `opaque_refR1Prior`, `opaque_refR1State` — the deviation referents `(pL + S·0, (1−p)L + S)`:
  label-free and act-correlated (the deviation moves the simulation);
* `opaque_refR2Sia` — Theorem 1's SIA sum adds the simulation's forcing;
* `opaque_refR3 = opaque_refR2Real` by Lemma C2-L3 (F3′ structural holds for every `C`);
* `opaque_nu'_actEv`, `opaque_paySum'_actEv` — the shared-seed conditionals `(pL, (1−p)L + S)`.

The numeric rows (T1(c), T3, T4, T10, T11, T12(a), T14, T15) are in `OpaqueRows.lean`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

/-- The second weight of a two-action distribution. Source: none: infrastructure. Kind: L -/
theorem Act2.w_b_eq (m : FinDistr ℚ Act2) : m.w .b = 1 - m.w .a := by
  have := m.sum_one
  rw [Act2.sum_univ] at this
  linarith

section opaqueNewcombForms

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (C : Proc Unit (fun _ => Act2) ℚ)

/-- Sums over the leaves of opaque Newcomb as a triple sum (sample, chance index, live draw).
Source: none: infrastructure
Kind: L -/
theorem opaque_sum_leaves (f : (opaqueNewcomb p h0 h1 L S).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ s, ∑ i, ∑ l, f ⟨s, ⟨i, ⟨l, ()⟩⟩⟩ := by
  unfold opaqueNewcomb at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The Definition 6 leaf law of opaque Newcomb: `C(d)(s) · coin(i) · C(d)(l)`.
Source: `sl-synthesis.md` line 120
Kind: L -/
theorem opaque_leafLaw (s : Act2) (i : Fin 2) (l : Act2) :
    leafLaw C (opaqueNewcomb p h0 h1 L S) ⟨s, ⟨i, ⟨l, ()⟩⟩⟩ =
      (C ()).w s * (FinDistr.coin p h0 h1).w i * (C ()).w l := by
  simp [opaqueNewcomb, leafLaw, mul_assoc]

/-- The world and payoff of a leaf. Source: none: infrastructure. Kind: L -/
theorem opaque_world (s : Act2) (i : Fin 2) (l : Act2) :
    world (opaqueNewcomb p h0 h1 L S) ⟨s, ⟨i, ⟨l, ()⟩⟩⟩ = (opaqueFill s i, l) := rfl

/-- The payoff of a leaf. Source: none: infrastructure. Kind: L -/
theorem opaque_payoff (s : Act2) (i : Fin 2) (l : Act2) :
    payoff (opaqueNewcomb p h0 h1 L S) ⟨s, ⟨i, ⟨l, ()⟩⟩⟩ = opaquePay L S (opaqueFill s i, l) := rfl

/-- The fill probability `P(fill) = qp + (1−q)(1−p)`. Source: `C2.md` C2-2′(b). Kind: D -/
def opaqueFillProb (q : ℚ) : ℚ := q * p + (1 - q) * (1 - p)

/-- **`V(C) = L·P(fill) + S·(1−q)`** on opaque Newcomb, `q := C(d)(one)`, every `C`.
Source: `sl-synthesis.md` line 120; `C2.md` C2-2′(b)
Kind: P
Fidelity: exact -/
theorem opaque_value :
    value C (opaqueNewcomb p h0 h1 L S) =
      L * opaqueFillProb p ((C ()).w .a) + S * (1 - (C ()).w .a) := by
  unfold value
  rw [opaque_sum_leaves]
  simp [opaqueNewcomb, leafLaw, payoff, Act2.sum_univ, Fin.sum_univ_two, opaqueFill, opaquePay,
    FinDistr.coin, opaqueFillProb, Act2.w_b_eq]
  ring

/-- `ν_C(act = a) = C(d)(a)` (the live draw). Source: none: infrastructure. Kind: L -/
theorem opaque_nu_actEv (a : Act2) :
    nu C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () a) = (C ()).w a := by
  rw [nu_eq_sum, opaque_sum_leaves]
  cases a <;> simp [opaqueNewcomb, leafLaw, world, opaqueActEv, Act2.sum_univ, Fin.sum_univ_two,
    FinDistr.coin, Act2.w_b_eq] <;> ring

/-- `∑_{act = a} μ_C r = C(d)(a) · (L·P(fill) + S·[a = two])`: conditioning on the live act
holds the prediction at its `C`-statistics.
Source: `faithful.md` FA-19′ ("holds the prediction at its `C`-statistics"); `C2.md` C2-2′(a)
Kind: P
Fidelity: exact -/
theorem opaque_paySum_actEv (a : Act2) :
    paySum C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () a) =
      (C ()).w a * (L * opaqueFillProb p ((C ()).w .a) + if a = .b then S else 0) := by
  rw [paySum_eq_sum_ite, opaque_sum_leaves]
  cases a <;> simp [opaqueNewcomb, leafLaw, world, payoff, opaqueActEv, Act2.sum_univ,
    Fin.sum_univ_two, FinDistr.coin, opaqueFill, opaquePay, opaqueFillProb, Act2.w_b_eq] <;> ring

/-- `O_d = ⊤` realizes. Source: none: infrastructure. Kind: L -/
theorem opaque_nu_obs : nu C (opaqueNewcomb p h0 h1 L S) (opaqueObs ()) = 1 := by
  unfold opaqueObs; exact nu_univ C _

/-- The action events are disjoint (Definition 3). Source: none: infrastructure. Kind: L -/
theorem opaque_actEvDisjoint : ActEvDisjoint opaqueActEv () := by
  intro a b hab
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [opaqueActEv, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact hab (hw.symm.trans hw')

/-- Opaque Newcomb is F3′-structural (`dp-core-tree`'s `opaqueNewcomb_actRecording` for every `C`).
Source: `faithful.md` Definition F3′ classification ("opaque Newcomb's real node — F3′")
Kind: L -/
theorem opaque_actRecordingStructural :
    ActRecordingStructural opaqueObs opaqueActEv (opaqueNewcomb p h0 h1 L S) () :=
  fun C _ => opaqueNewcomb_actRecording p h0 h1 L S C

/-- The live node below sample `s` and chance index `i`. Source: none: infrastructure. Kind: D -/
def opaqueLive (s : Act2) (i : Fin 2) : (opaqueNewcomb p h0 h1 L S).DecNode :=
  some ⟨s, ⟨i, none⟩⟩

/-- The live nodes are node-action-veridical. Source: `faithful.md` F3′. Kind: L -/
theorem opaque_live_nav (s : Act2) (i : Fin 2) :
    NodeActionVeridical opaqueActEv (opaqueNewcomb p h0 h1 L S) (opaqueLive p h0 h1 L S s i) := by
  intro ℓ a ha
  rcases ℓ with ⟨s', i', l', _⟩
  unfold opaqueLive at ha
  by_cases hs : s' = s
  · subst hs
    by_cases hi : i' = i
    · subst hi
      simp only [opaqueNewcomb, edgeOf_decision_some, dite_true, edgeOf_chance,
        edgeOf_decision_none, Option.some.injEq] at ha
      subst ha
      simp [opaqueActEv, opaqueNewcomb, world]
    · simp [opaqueNewcomb, edgeOf_decision_some, edgeOf_chance, hi] at ha
  · simp [opaqueNewcomb, edgeOf_decision_some, hs] at ha

/-- The simulation node is not node-action-veridical. Source: `faithful.md` F3′. Kind: L -/
theorem opaque_sim_not_nav :
    ¬ NodeActionVeridical opaqueActEv (opaqueNewcomb p h0 h1 L S) none := by
  intro h
  have := h ⟨.a, ⟨0, ⟨.b, ()⟩⟩⟩ .a (by simp [opaqueNewcomb, edgeOf_decision_none])
  simp [opaqueActEv, opaqueNewcomb, world] at this

/-- **The real fiber of opaque Newcomb is the set of live nodes.**
Source: `faithful.md` Definition F2 (R2-real "averaged over the node-action-veridical instances")
Kind: L -/
theorem opaque_realFiber :
    realFiber opaqueActEv (opaqueNewcomb p h0 h1 L S) () =
      (Finset.univ : Finset (Act2 × Fin 2)).image fun x => opaqueLive p h0 h1 L S x.1 x.2 := by
  ext q
  rw [mem_realFiber, Finset.mem_image]
  constructor
  · rintro ⟨-, hnav⟩
    rcases q with _ | ⟨s, i, _ | ⟨l, e⟩⟩
    · exact absurd hnav (opaque_sim_not_nav p h0 h1 L S)
    · exact ⟨(s, i), Finset.mem_univ _, rfl⟩
    · exact e.elim
  · rintro ⟨⟨s, i⟩, -, rfl⟩
    exact ⟨rfl, opaque_live_nav p h0 h1 L S s i⟩

/-- The live-node map is injective. Source: none: infrastructure. Kind: L -/
theorem opaqueLive_injective : Function.Injective fun x : Act2 × Fin 2 =>
    opaqueLive p h0 h1 L S x.1 x.2 := by
  rintro ⟨s, i⟩ ⟨s', i'⟩ h
  have h' := Option.some.inj h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h'
  have h3 := eq_of_heq h2
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp h3
  rfl

/-- `R_{live(s,i)}(C) = C(d)(s) · coin(i)`. Source: none: infrastructure. Kind: L -/
theorem opaque_reach_live (s : Act2) (i : Fin 2) :
    reach C (opaqueNewcomb p h0 h1 L S) (opaqueLive p h0 h1 L S s i) =
      (C ()).w s * (FinDistr.coin p h0 h1).w i := by
  simp [opaqueLive, opaqueNewcomb, reach]

/-- The value of a leaf tree under any node policy. Source: none: infrastructure. Kind: L -/
theorem valueNode_leaf' {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] (ω : Ω) (r : ℚ)
    (pol : NodePolicy (leaf ω r : Tree Ω ι acts ℚ)) : valueNode (leaf ω r) pol = r := by
  unfold valueNode
  rw [Tree.sum_leaves_leaf]
  simp

/-- `forcedBelow` at a live node: `C(d)(s) · coin(i) · r(fill s i, a)`.
Source: none: infrastructure
Kind: L -/
theorem opaque_forcedBelow_live (s : Act2) (i : Fin 2) (a : Act2) :
    forcedBelow (opaqueNewcomb p h0 h1 L S) (NodePolicy.ofProc C _) (opaqueLive p h0 h1 L S s i) a =
      (C ()).w s * (FinDistr.coin p h0 h1).w i * opaquePay L S (opaqueFill s i, a) := by
  unfold opaqueLive opaqueNewcomb
  rw [forcedBelow_decision_some, NodePolicy.ofProc_none, NodePolicy.ofProc_restrictDecision,
    forcedBelow_chance, NodePolicy.ofProc_restrictChance, forcedBelow_decision_none,
    NodePolicy.ofProc_restrictDecision, valueNode_leaf']
  ring

/-- **`∑_{q ∈ realFiber} R_q(C) = 1`** on opaque Newcomb (`O_d = ⊤`).
Source: none: infrastructure
Kind: L -/
theorem opaque_realReach : realReach opaqueActEv C (opaqueNewcomb p h0 h1 L S) () = 1 := by
  rw [← opaque_nu_obs p h0 h1 L S C, nu_obs_eq_realReach opaqueObs opaqueActEv C _
    (opaqueNewcomb_actRecording p h0 h1 L S C)]

/-- On a `Unit`-point tree the transport in `realForced` is trivial.
Source: none: infrastructure
Kind: L -/
theorem realForced_unit {Ω : Type} [Fintype Ω] [DecidableEq Ω] {acts : Unit → Type}
    [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    (actEv : (d : Unit) → acts d → Finset Ω) (C : Proc Unit acts ℚ) (B : Tree Ω Unit acts ℚ)
    (a : acts ()) :
    realForced actEv C B () a =
      ∑ q ∈ realFiber actEv B (), forcedBelow B (NodePolicy.ofProc C B) q a := by
  unfold realForced
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [dif_pos rfl]

/-- **`∑_{q ∈ realFiber} R_q G_q(C, a) = L·P(fill) + S·[a = two]`**: forcing at the live node holds
the prediction at its `C`-statistics.
Source: `faithful.md` FA-19′ (`G_real(one) = 𝔼_C[fill]·L`, `G_real(two) = 𝔼_C[fill]·L + S`)
Kind: P
Fidelity: exact -/
theorem opaque_realForced (a : Act2) :
    realForced opaqueActEv C (opaqueNewcomb p h0 h1 L S) () a =
      L * opaqueFillProb p ((C ()).w .a) + if a = .b then S else 0 := by
  rw [realForced_unit, opaque_realFiber,
    Finset.sum_image (fun x _ y _ h => opaqueLive_injective p h0 h1 L S h),
    Fintype.sum_prod_type]
  simp only [opaque_forcedBelow_live]
  cases a <;> simp [Act2.sum_univ, Fin.sum_univ_two, FinDistr.coin, opaqueFill, opaquePay,
    opaqueFillProb, Act2.w_b_eq] <;> ring

/-- **R2-real on opaque Newcomb**: `refR2Real a = L·P(fill) + S·[a = two]` for every label — the
fill term is act-independent (the prediction held fixed), so R2-real two-boxes whenever `S > 0`.
Source: `faithful.md` FA-18 (Newcomb row, R2-real `(3, 4)` two), FA-19′; `C2.md` C2-2′(a)
Kind: P
Fidelity: exact -/
theorem opaque_refR2Real (a : Act2) :
    refR2Real opaqueActEv C (opaqueNewcomb p h0 h1 L S) () a =
      L * opaqueFillProb p ((C ()).w .a) + if a = .b then S else 0 := by
  unfold refR2Real
  rw [opaque_realReach, opaque_realForced, div_one]

/-- **R3 on opaque Newcomb equals R2-real** (Lemma C2-L3: F3′ structural for every `C`).
Source: `faithful.md` FA-18 (Newcomb row, R3 `(3, 4)`), FA-21′ ("R3 siding with classical CDT under
Definition 6 in the act-recording algebra")
Kind: C
Fidelity: exact -/
theorem opaque_refR3 (a : Act2) :
    refR3 opaqueObs opaqueActEv C (opaqueNewcomb p h0 h1 L S) () a =
      L * opaqueFillProb p ((C ()).w .a) + if a = .b then S else 0 := by
  rw [refR3_eq_refR2Real_of_structural opaqueObs opaqueActEv C _
    (opaque_actRecordingStructural p h0 h1 L S) (opaque_actEvDisjoint)
    (by rw [opaque_nu_obs]; exact one_pos), opaque_refR2Real]

/-- **R1-prior on opaque Newcomb**: `V(C[d ↦ one]) = pL`, `V(C[d ↦ two]) = (1−p)L + S` — the
deviation moves the simulation.
Source: `faithful.md` FA-18 (Newcomb row, R1-prior `(3, 2)`)
Kind: P
Fidelity: exact -/
theorem opaque_refR1Prior (a : Act2) :
    refR1Prior C (opaqueNewcomb p h0 h1 L S) () a =
      L * (if a = .a then p else 1 - p) + if a = .b then S else 0 := by
  unfold refR1Prior
  rw [opaque_value]
  simp only [Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w, opaqueFillProb]
  cases a <;> simp <;> ring

/-- **R1-state on opaque Newcomb** is R1-prior (`O_d = ⊤`).
Source: `faithful.md` FA-18 (Newcomb row, R1-state `(3, 2)`)
Kind: P
Fidelity: exact -/
theorem opaque_refR1State (a : Act2) :
    refR1State opaqueObs C (opaqueNewcomb p h0 h1 L S) () a =
      L * (if a = .a then p else 1 - p) + if a = .b then S else 0 := by
  unfold refR1State condExp
  have hν1 : nu (C.deviatePure () a) (opaqueNewcomb p h0 h1 L S) (opaqueObs ()) = 1 :=
    opaque_nu_obs p h0 h1 L S _
  have hp2 : paySum (C.deviatePure () a) (opaqueNewcomb p h0 h1 L S) (opaqueObs ()) =
      value (C.deviatePure () a) (opaqueNewcomb p h0 h1 L S) := by
    unfold paySum value opaqueObs
    rw [worldEv_univ]
  rw [hν1, hp2, div_one, ← refR1Prior, opaque_refR1Prior]

/-- **R2-SIA on opaque Newcomb**: Theorem 1's sum adds the simulation's forcing to the live one:
`siaSum one = L·P(fill) + pL + S(1−q)`, `siaSum two = L·P(fill) + S + (1−p)L + S(1−q)`.
Source: `faithful.md` FA-18 (Newcomb row, R2-SIA `(6, 5)`), FA-19′ ("Theorem 1's SIA weight on the
simulation adds `½(2p−1)L`")
Kind: P
Fidelity: exact -/
theorem opaque_refR2Sia (a : Act2) :
    refR2Sia C (opaqueNewcomb p h0 h1 L S) () a =
      L * opaqueFillProb p ((C ()).w .a) + (if a = .b then S else 0) +
        (L * (if a = .a then p else 1 - p) + S * (1 - (C ()).w .a)) := by
  unfold refR2Sia opaqueNewcomb
  rw [siaSum_decision_self]
  simp only [siaSum_chance, siaSum_decision_self, siaSum_leaf, mul_zero, Finset.sum_const_zero,
    zero_add, value_leaf, value_chance, value_decision, opaqueFillProb]
  cases a <;> simp [Act2.sum_univ, Fin.sum_univ_two, FinDistr.coin, opaqueFill, opaquePay,
    Act2.w_b_eq] <;> ring

/-! ### Definition 6′: the shared seed -/

/-- The shared-seed leaf law of opaque Newcomb: `C(d)(s) · coin(i) · [l = s]`.
Source: `seeds.md` Definition 6′; `C2.md` C2-3″
Kind: L -/
theorem opaque_leafLaw' (s : Act2) (i : Fin 2) (l : Act2) :
    leafLaw' C (opaqueNewcomb p h0 h1 L S) ⟨s, ⟨i, ⟨l, ()⟩⟩⟩ =
      (C ()).w s * (FinDistr.coin p h0 h1).w i * if l = s then 1 else 0 := by
  rw [leafLaw'_eq]
  simp only [opaqueNewcomb, chanceWeight, draws]
  rw [seedFold_cons_of_none C rfl, seedFold_cons_of_some C (a' := s) (by simp)]
  simp only [seedFold_nil]
  split_ifs with h h' h'
  · ring
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · ring

/-- `ν'_C(act = a) = C(d)(a)`. Source: none: infrastructure. Kind: L -/
theorem opaque_nu'_actEv (a : Act2) :
    nu' C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () a) = (C ()).w a := by
  unfold nu' worldEv
  rw [Finset.sum_filter, opaque_sum_leaves]
  simp only [opaque_leafLaw', opaque_world]
  cases a <;> simp [opaqueActEv, Act2.sum_univ, Fin.sum_univ_two, FinDistr.coin] <;> ring

/-- `∑_{act = a} μ'_C r = C(d)(a) · (L·[a = one]p + L·[a = two](1−p) + S·[a = two])`: under the
shared seed the conditional on the live act reads the prediction.
Source: `C2.md` C2-3″ ("opaque Newcomb `(3,2)` one-box"); P13-4′
Kind: P
Fidelity: exact -/
theorem opaque_paySum'_actEv (a : Act2) :
    paySum' C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () a) =
      (C ()).w a * (L * (if a = .a then p else 1 - p) + if a = .b then S else 0) := by
  unfold paySum' worldEv
  rw [Finset.sum_filter, opaque_sum_leaves]
  simp only [opaque_leafLaw', opaque_world, opaque_payoff]
  cases a <;> simp [opaqueActEv, Act2.sum_univ, Fin.sum_univ_two, FinDistr.coin, opaqueFill,
    opaquePay] <;> ring

/-- **The shared-seed act conditional on opaque Newcomb**: for `C(d)(a) > 0`,
`𝔼'_C[r ∣ act = a] = L·[a = one]p + L·[a = two](1−p) + S·[a = two]` — R1-state's numbers, at every
label.
Source: `C2.md` C2-3″ ("EV′ = R3′ = R1-state′"); `faithful.md` line 113
Kind: P
Fidelity: exact -/
theorem opaque_condExp'_actEv (a : Act2) (ha : 0 < (C ()).w a) :
    condExp' C (opaqueNewcomb p h0 h1 L S) (opaqueActEv () a) =
      L * (if a = .a then p else 1 - p) + if a = .b then S else 0 := by
  unfold condExp'
  rw [opaque_paySum'_actEv, opaque_nu'_actEv]
  field_simp

/-- `ν'_C(⊤) = 1`. Source: none: infrastructure. Kind: L -/
theorem opaque_nu'_obs : nu' C (opaqueNewcomb p h0 h1 L S) (opaqueObs ()) = 1 := by
  unfold nu' opaqueObs
  rw [worldEv_univ]
  exact sum_leafLaw' C _

end opaqueNewcombForms

end Cleanroom.Decision.DpReferentsCdt
