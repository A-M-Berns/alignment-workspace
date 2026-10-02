import Cleanroom.Decision.DpReferentsCdt.Rows
import Cleanroom.Decision.DpCalibration.Mugging
import Cleanroom.Decision.DpCalibration.ToldYouSo
import Cleanroom.Decision.DpCalibration.Miniature
import Cleanroom.Found.DpCoreTree.Agreement

/-!
# FA-18's rows: the mugging, Told-You-So, and the shared-seed rows

* **T1(c), the mugging `B₁(1, 3)`** at `d` (Definition-7-recorded, `O_d = {coin = T}`): R1-prior
  `(1, 0)` pay, R1-state `(−1, 0)` refuse, R2-SIA `(1, 0)` pay, R2-real `(−1, 0)` refuse, R3 `(−1, 0)`
  refuse — the weighting axis (β): the prior-level referents pay, the `O_d`-conditioned ones refuse,
  at a recorded point. At `δ_pay` the nulled act `refuse` is priced `0` by R3 (dp-sl-2-022).
* **T1(c)/T4, Told-You-So** under `C₀ = (five, ten)`: at `d₁₀`, `ν(O₁₀) = 0`, the strict value is
  undefined and `refR2Real`'s guard fails (`realReach = 0`), while R3 is still `(5, 10)` (FA-17′(c));
  at `d₅` the root is a selection node: the real fiber is empty (`realReach = 0`) and R1-prior is
  `(5, 10)`.
* **T7, the shared seed**: on the miniature `EV′ = (0, 0) = R1-state′` while `refR2Real = (2(1−q), q)`
  keeps Remark 4.3's Definition-6 numbers. (The Death-in-Damascus seed row is not shipped: the
  tree's worlds are `Unit` and its `![…]` chance children resist the leaf-sum lemmas; report T7.)
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

/-! ## The mugging row -/

section mugging

/-- FA-18's mugging `B₁(1, 3)`. Source: `faithful.md` FA-18 (mugging row). Kind: D -/
def mugTree : Tree MugW Unit (fun _ => Act2) ℚ := mug1 1 3

/-- The `T`-branch node of the mugging is node-action-veridical. Source: none: infrastructure. Kind: L -/
theorem mug_T_nav : NodeActionVeridical mugActEv mugTree ⟨0, none⟩ := by
  intro ℓ a ha
  rcases ℓ with ⟨i, act, _⟩
  by_cases hi : i = 0
  · subst hi
    simp only [mugTree, mug1, edgeOf_chance, dite_true, edgeOf_decision_none, Option.some.injEq]
      at ha
    subst ha
    cases act <;> simp [mugActEv, mugTree, mug1, world, mugWorld1]
  · simp [mugTree, mug1, edgeOf_chance, hi] at ha

/-- The real fiber of the mugging is the `T`-branch node (the `H`-branch's worlds lie in no action
event). Source: none: infrastructure. Kind: L -/
theorem mug_mem_realFiber (q : mugTree.DecNode) :
    q ∈ realFiber mugActEv mugTree () ↔ q = ⟨0, none⟩ := by
  rw [mem_realFiber]
  constructor
  · rintro ⟨-, hnav⟩
    rcases q with ⟨i, q⟩
    by_cases hi : i = 0
    · subst hi
      rcases q with _ | ⟨act, e⟩
      · rfl
      · exact e.elim
    · have hi1 : i = 1 := by omega
      subst hi1
      rcases q with _ | ⟨act, e⟩
      · exfalso
        have := hnav ⟨1, .a, ()⟩ .a (by simp [mugTree, mug1, edgeOf_chance, edgeOf_decision_none])
        simp [mugActEv, mugTree, mug1, world, mugWorld1] at this
      · exact e.elim
  · rintro rfl
    exact ⟨rfl, mug_T_nav⟩

/-- The mugging is F3′-structural. Source: `faithful.md` line 40 ("mugging `B₁` — F3′ and
Definition 7"). Kind: L -/
theorem mug_actRecordingStructural : ActRecordingStructural mugObs mugActEv mugTree () := by
  intro C _
  refine ⟨?_, ?_⟩
  · intro q hq hnav ℓ hℓ
    have hq' : q = ⟨0, none⟩ := (mug_mem_realFiber q).mp ((mem_realFiber _ _ _ q).mpr ⟨hq, hnav⟩)
    subst hq'
    rcases ℓ with ⟨i, act, _⟩
    by_cases hi : i = 0
    · subst hi
      cases act <;> simp [mugObs, mugTree, mug1, world, mugWorld1]
    · rw [mem_leavesBelow] at hℓ
      simp [mugTree, mug1, edgeOf_chance, hi] at hℓ
  · intro ℓ _ hobs
    rcases ℓ with ⟨i, act, _⟩
    by_cases hi : i = 0
    · subst hi
      refine ⟨⟨0, none⟩, ⟨?_, mug_T_nav⟩, ?_⟩
      · rw [mem_dNodesOn]
        exact ⟨rfl, by simp [mugTree, mug1, edgeOf_chance, edgeOf_decision_none]⟩
      · rintro q ⟨-, hnav⟩
        exact (mug_mem_realFiber q).mp ((mem_realFiber _ _ _ q).mpr ⟨rfl, hnav⟩)
    · exfalso
      have hi1 : i = 1 := by omega
      subst hi1
      cases act <;> simp [mugObs, mugTree, mug1, world, mugWorld1] at hobs

/-- The mugging's action events are disjoint. Source: none: infrastructure. Kind: L -/
theorem mug_actEvDisjoint : ActEvDisjoint mugActEv () := by
  intro a b hab
  cases a <;> cases b <;> simp [mugActEv] at hab ⊢

/-- **FA-18, mugging row**: R1-prior `(1, 0)` (pay), R1-state `(−1, 0)` (refuse), R2-SIA `(1, 0)`
(pay), R2-real `(−1, 0)` (refuse), R3 `(−1, 0)` (refuse) at every label — the weighting axis at a
recorded point: prior-level referents pay, `O_d`-conditioned ones refuse.
Source: `faithful.md` FA-18 (mugging row), FA-21′ ("this split is present even at recorded points
(mugging: pay vs refuse)"); mandate T1(c)
Kind: N+ -/
theorem mug_row (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    refR1Prior (procQ q h0 h1) mugTree () .a = 1 ∧ refR1Prior (procQ q h0 h1) mugTree () .b = 0 ∧
    refR1State mugObs (procQ q h0 h1) mugTree () .a = -1 ∧
      refR1State mugObs (procQ q h0 h1) mugTree () .b = 0 ∧
    refR2Sia (procQ q h0 h1) mugTree () .a = 1 ∧ refR2Sia (procQ q h0 h1) mugTree () .b = 0 ∧
    refR2Real mugActEv (procQ q h0 h1) mugTree () .a = -1 ∧
      refR2Real mugActEv (procQ q h0 h1) mugTree () .b = 0 ∧
    refR3 mugObs mugActEv (procQ q h0 h1) mugTree () .a = -1 ∧
      refR3 mugObs mugActEv (procQ q h0 h1) mugTree () .b = 0 := by
  have hpos : 0 < nu (procQ q h0 h1) mugTree (mugObs ()) := by
    unfold mugTree; rw [mug1_nu_obs]; norm_num
  have hR2 : ∀ a, refR2Real mugActEv (procQ q h0 h1) mugTree () a = if a = .a then -1 else 0 := by
    intro a
    rw [refR2Real_eq_of_unique mugActEv (procQ q h0 h1) mugTree _ mug_mem_realFiber]
    unfold mugTree mug1
    rw [forcedBelow_chance, NodePolicy.ofProc_restrictChance, forcedBelow_decision_none,
      NodePolicy.ofProc_restrictDecision, reach_chance, reach_decision_none]
    unfold valueNode
    rw [Tree.sum_leaves_leaf]
    cases a <;> simp [leafLawNode, mugWorld1, mugPay, FinDistr.fair, FinDistr.coin] <;> norm_num
  have hR3 : ∀ a, refR3 mugObs mugActEv (procQ q h0 h1) mugTree () a = if a = .a then -1 else 0 := by
    intro a
    rw [refR3_eq_refR2Real_of_structural mugObs mugActEv _ _ mug_actRecordingStructural
      mug_actEvDisjoint hpos, hR2]
  have hR1 : ∀ a, refR1Prior (procQ q h0 h1) mugTree () a = if a = .a then 1 else 0 := by
    intro a
    unfold refR1Prior mugTree
    rw [mug1_value]
    cases a <;> simp [Proc.deviatePure, Proc.deviate_same] <;> norm_num
  have hS : ∀ a, refR1State mugObs (procQ q h0 h1) mugTree () a = if a = .a then -1 else 0 := by
    intro a
    unfold refR1State condExp mugTree
    rw [mug1_nu_obs, paySum_eq_sum_ite, mug1_sum]
    cases a <;> simp [Fin.sum_univ_two, Act2.sum_univ, mug1, mugWorld1, mugPay, mugObs,
      FinDistr.fair, FinDistr.coin, Proc.deviatePure, Proc.deviate_same] <;> norm_num
  have hSia : ∀ a, refR2Sia (procQ q h0 h1) mugTree () a = if a = .a then 1 else 0 := by
    intro a
    unfold refR2Sia mugTree mug1
    rw [siaSum_chance]
    cases a <;> simp [siaSum_decision_self, siaSum_leaf, value_leaf, Fin.sum_univ_two,
      mugWorld1, mugPay, FinDistr.fair, FinDistr.coin] <;> norm_num
  exact ⟨by rw [hR1]; simp, by rw [hR1]; simp, by rw [hS]; simp, by rw [hS]; simp,
    by rw [hSia]; simp, by rw [hSia]; simp, by rw [hR2]; simp, by rw [hR2]; simp,
    by rw [hR3]; simp, by rw [hR3]; simp⟩

end mugging

/-! ## Told-You-So -/

section tys

/-- **Told-You-So at `d₁₀` under `C₀`: R3 is `(5, 10)` although `ν(O₁₀) = 0`** (FA-17′(c)): the tremble
limit prices the nulled observation, where the strict value is undefined.
Source: `faithful.md` FA-17′(c) ("Told-You-So `d₁₀` under `C₀`: R3 `= (5,10)`"), FA-18 (TYS `d₁₀` row);
dp-sl-2-022(a); mandate T1(c), T4
Kind: N+ -/
theorem tys_refR3_ten_C0 :
    refR3 tysObs tysActEv procFiveTen toldYouSo .ten .five = 5 ∧
      refR3 tysObs tysActEv procFiveTen toldYouSo .ten .ten = 10 := by
  have hX5 : tysActEv .ten .five ∩ tysObs .ten = {(Five10.ten, Five10.five)} := by
    ext w; rcases w with ⟨a, b⟩; cases a <;> cases b <;> simp [tysActEv, tysObs]
  have hX10 : tysActEv .ten .ten ∩ tysObs .ten = {(Five10.ten, Five10.ten)} := by
    ext w; rcases w with ⟨a, b⟩; cases a <;> cases b <;> simp [tysActEv, tysObs]
  have hne : ∀ a b : Five10, trembleW procFiveTen a b ≠ 0 := fun a b => trembleW_ne_zero _ _ _
  constructor
  · unfold refR3
    rw [hX5, limitVal_eq_of_factor procFiveTen toldYouSo _
      (trembleW procFiveTen .five .ten * trembleW procFiveTen .ten .five) 1 (Polynomial.C 5)
      (by rw [tys_nuPoly]; simp) (by rw [tys_payPoly]; simp) (mul_ne_zero (hne _ _) (hne _ _))
      (by simp)]
    simp
  · unfold refR3
    rw [hX10, limitVal_eq_of_factor procFiveTen toldYouSo _
      (trembleW procFiveTen .five .ten * trembleW procFiveTen .ten .ten) 1 (Polynomial.C 10)
      (by rw [tys_nuPoly]; simp) (by rw [tys_payPoly]; simp) (mul_ne_zero (hne _ _) (hne _ _))
      (by simp)]
    simp

/-- **Told-You-So at `d₁₀` under `C₀`: `refR2Real`'s guard fails** — the real fiber is the `d₁₀`
node, unreached (`R = C₀(d₅)(ten) = 0`), so `refR2Real` is junk `0` there and the identity
`refR3 = refR2Real` is *false* at this point (`5 ≠ 0`): the mandate's `nuPoly (O_d) ≠ 0` hypothesis
for C2-L3 is not enough (findings F2).
Source: `faithful.md` FA-18 (TYS `d₁₀` row: R2-real "undef"); mandate §7 trap 4, T4
Kind: N+ -/
theorem tys_realReach_ten_C0 :
    realReach tysActEv procFiveTen toldYouSo .ten = 0 ∧
      refR2Real tysActEv procFiveTen toldYouSo .ten .five = 0 ∧
      nuPoly procFiveTen toldYouSo (tysObs .ten) ≠ 0 := by
  have hfib : ∀ q : toldYouSo.DecNode,
      q ∈ realFiber tysActEv toldYouSo .ten ↔ q = some ⟨.ten, none⟩ := by
    intro q
    rw [mem_realFiber]
    constructor
    · rintro ⟨hpt, -⟩
      rcases q with _ | ⟨_ | _, q⟩
      · simp [toldYouSo] at hpt
      · exact q.elim
      · rcases q with _ | ⟨_ | _, q⟩
        · rfl
        · exact q.elim
        · exact q.elim
    · rintro rfl
      refine ⟨rfl, fun ℓ a ha => ?_⟩
      rcases ℓ with ⟨_ | _, ℓ⟩
      · simp [toldYouSo, edgeOf_decision_some] at ha
      · rcases ℓ with ⟨_ | _, _⟩ <;>
          simp only [toldYouSo, edgeOf_decision_some, dite_true, edgeOf_decision_none,
            Option.some.injEq] at ha <;> subst ha <;> simp [tysActEv, toldYouSo, world]
  have hreach : realReach tysActEv procFiveTen toldYouSo .ten = 0 := by
    unfold realReach
    apply Finset.sum_eq_zero
    intro q hq
    rw [(hfib q).mp hq]
    simp [toldYouSo, reach, procFiveTen, Proc.ofFun]
  refine ⟨hreach, ?_, ?_⟩
  · unfold refR2Real; rw [hreach, div_zero]
  · rw [nuPoly_ne_zero_iff]
    exact ⟨⟨.ten, .ten, ()⟩, by simp [tysObs, toldYouSo, world], by simp [toldYouSo, chanceWeight]⟩

/-- **Told-You-So at `d₅`: the root is a selection node**, the real fiber is empty, `refR2Real`'s
guard fails, and R1-prior is `(5, 10)`.
Source: `faithful.md` FA-18 (TYS `d₅` row: R2-real "undef", R1-prior `(5, 10)`), FA-25′(5);
mandate T1(c), T4
Kind: N+ -/
theorem tys_five_selection :
    realReach tysActEv procFiveTen toldYouSo .five = 0 ∧
      refR1Prior procFiveTen toldYouSo .five .five = 5 ∧
      refR1Prior procFiveTen toldYouSo .five .ten = 10 := by
  have hfib : realFiber tysActEv toldYouSo .five = ∅ := by
    ext q
    rw [mem_realFiber]
    simp only [Finset.notMem_empty, iff_false, not_and]
    intro hpt hnav
    rcases q with _ | ⟨_ | _, q⟩
    · have := hnav ⟨.ten, .five, ()⟩ .ten (by simp [toldYouSo, edgeOf_decision_none])
      simp [tysActEv, toldYouSo, world] at this
    · exact q.elim
    · rcases q with _ | ⟨_ | _, q⟩
      · simp [toldYouSo] at hpt
      · exact q.elim
      · exact q.elim
  refine ⟨by unfold realReach; rw [hfib, Finset.sum_empty], ?_, ?_⟩ <;>
  · unfold refR1Prior value
    rw [tys_sum]
    simp [toldYouSo, leafLaw, payoff, procFiveTen, Proc.ofFun, Proc.deviatePure, Proc.deviate_same,
      Proc.deviate_ne]

end tys

/-! ## The shared-seed rows (T7) -/

section seed

/-- The shared-seed leaf law of the miniature: `C(d)(s) · [l = s]`.
Source: `seeds.md` Definition 6′; `C2.md` C2-3″ ("miniature EV′ = (0,0)")
Kind: L -/
theorem miniature_leafLaw' (C : Proc Unit (fun _ => Act2) ℚ) (s l : Act2) :
    leafLaw' C miniature ⟨s, ⟨l, ()⟩⟩ = (C ()).w s * if l = s then 1 else 0 := by
  rw [leafLaw'_eq]
  simp only [miniature, chanceWeight, draws]
  rw [seedFold_cons_of_none C rfl, seedFold_cons_of_some C (a' := s) (by simp)]
  simp only [seedFold_nil]
  split_ifs with h h' h'
  · ring
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · ring

/-- The miniature is F3′-structural: the live nodes record the act, the sample node does not, and
every run passes exactly one live node.
Source: [[decision-problems-v2]] Remark 4.3; `C2.md` C2-2′(a) (miniature row); mandate T7
Kind: L -/
theorem miniature_actRecordingStructural :
    ActRecordingStructural miniObs miniActEv miniature () := by
  intro C _
  refine ⟨fun q _ _ ℓ _ => by simp [miniObs], ?_⟩
  intro ℓ _ _
  rcases ℓ with ⟨s, l, _⟩
  refine ⟨some ⟨s, none⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_dNodesOn]
    exact ⟨rfl, by simp [miniature, edgeOf_decision_some, edgeOf_decision_none]⟩
  · intro ℓ' a ha
    rcases ℓ' with ⟨s', l', _⟩
    by_cases hs : s' = s
    · subst hs
      simp only [miniature, edgeOf_decision_some, dite_true, edgeOf_decision_none,
        Option.some.injEq] at ha
      subst ha
      simp [miniActEv, miniature, world]
    · simp [miniature, edgeOf_decision_some, hs] at ha
  · rintro (_ | ⟨s', _ | ⟨l', e⟩⟩) ⟨hmem, hnav⟩
    · exfalso
      have := hnav ⟨.a, ⟨.b, ()⟩⟩ .a (by simp [miniature, edgeOf_decision_none])
      simp [miniActEv, miniature, world] at this
    · rw [mem_dNodesOn] at hmem
      by_cases hs : s = s'
      · subst hs; rfl
      · simp [miniature, edgeOf_decision_some, hs] at hmem
    · exact e.elim

/-- The miniature's action events are disjoint. Source: none: infrastructure. Kind: L -/
theorem miniature_actEvDisjoint : ActEvDisjoint miniActEv () := by
  intro a b hab
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [miniActEv, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact hab (hw.symm.trans hw')

/-- **C2-3″ on the miniature: `EV′ = (0, 0) = R1-state′`** at every label, while `refR2Real =
(2(1−q), q)` keeps Remark 4.3's Definition-6 numbers (at labels with both acts positive, where it is
the strict act conditional by C2-L2).
Source: `C2.md` C2-3″ ("miniature EV′ = (0,0)"; "R2-real′ … keeps the Definition-6 values");
[[decision-problems-v2]] Remark 4.3 (`V(a) = 2(1−q)`, `V(b) = q`); dp-sl-031; mandate T7
Kind: N+ -/
theorem miniature_seed_row (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    condExp' (procQ q h0.le h1.le) miniature (miniActEv () .a) = 0 ∧
    condExp' (procQ q h0.le h1.le) miniature (miniActEv () .b) = 0 ∧
    refR1State' (procQ q h0.le h1.le) miniature miniObs () .a = 0 ∧
    refR1State' (procQ q h0.le h1.le) miniature miniObs () .b = 0 ∧
    refR2Real miniActEv (procQ q h0.le h1.le) miniature () .a = 2 * (1 - q) ∧
    refR2Real miniActEv (procQ q h0.le h1.le) miniature () .b = q := by
  have hpay' : ∀ C : Proc Unit (fun _ => Act2) ℚ, ∀ X, paySum' C miniature X = 0 := by
    intro C X
    unfold paySum' worldEv
    rw [Finset.sum_filter, miniature_sum]
    simp only [miniature_leafLaw']
    simp [miniature, payoff, miniPay, Act2.sum_univ]
  have hpos : 0 < nu (procQ q h0.le h1.le) miniature (miniObs ()) := by
    unfold miniObs; rw [nu_univ]; exact one_pos
  have hR2 : ∀ a, 0 < (procQ q h0.le h1.le ()).w a →
      refR2Real miniActEv (procQ q h0.le h1.le) miniature () a =
        condExp (procQ q h0.le h1.le) miniature (miniActEv () a ∩ miniObs ()) := by
    intro a ha
    exact (condExp_actEv_inter_obs_eq_refR2Real miniObs miniActEv _ _
      (miniature_actRecordingStructural.actRecording _) miniature_actEvDisjoint ha hpos).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold condExp'; rw [hpay', zero_div]
  · unfold condExp'; rw [hpay', zero_div]
  · unfold refR1State' condExp'; rw [hpay', zero_div]
  · unfold refR1State' condExp'; rw [hpay', zero_div]
  · rw [hR2 _ (by simp [procQ, h0])]
    unfold condExp miniObs
    rw [Finset.inter_univ, miniature_nu_live, miniature_paySum_live_a,
      mul_div_cancel_right₀ _ (by simp [procQ, h0.ne'] : (procQ q h0.le h1.le ()).w .a ≠ 0)]
    simp [procQ]
  · rw [hR2 _ (by simp [procQ]; linarith)]
    unfold condExp miniObs
    rw [Finset.inter_univ, miniature_nu_live, miniature_paySum_live_b,
      mul_div_cancel_right₀ _ (by simp [procQ]; linarith : (procQ q h0.le h1.le ()).w .b ≠ 0)]
    simp [procQ]

end seed

end Cleanroom.Decision.DpReferentsCdt
