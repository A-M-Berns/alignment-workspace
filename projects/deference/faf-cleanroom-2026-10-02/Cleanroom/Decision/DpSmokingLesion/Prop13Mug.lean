import Cleanroom.Decision.DpSmokingLesion.Prop13
import Cleanroom.Decision.DpCalibration.Mugging
import Cleanroom.Found.DpCoreTree.ScreeningWitness

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# T3(e): the mugging refutes Proposition 13's R2-SIA / R2-real / SSC clauses under
Definition-7 recording alone

On Counterfactual Mugging `B₁` (`dp-core-tree`'s `mug1 x y`) at `C(d) = ½`, Definition 7
recording at `d` holds for `O_T` (`mug1_recordsFor`) but `H*` fails (`mug1_not_hStar`: the
hypothetical `H`-branch `d`-node sits on a positive non-`O_T` run). There:

* EV(pay) `= paySum(pay ∧ O_T)/ν(pay ∧ O_T) = (−x/4)/(1/4) = −x` (`mug1_ev_pay`);
* R2-SIA(pay) `= ∑_q forcedBelow_q(pay) / ∑_q R_q = ((y − x)/2)/1` (`mug1_r2Sia`,
  `mug1_fiberMass`) — the simulation node contributes `y/2`;
* R2-real(pay), reading 2 (veridical `d`-nodes on positive `O_T`-runs), `= (−x/2)/(1/2) = −x`
  (`mug1_r2Real`): it agrees with EV at the recorded point, as dp-sl-2-058 says reading 2
  should; under the mugging's own action events (`mugActEv pay = {tPay}`) the `H`-node is not
  node-action-veridical, so reading 1 gives the same value (`mug1_realFiberAll`) — the mandate's
  "reading 1 = 1" presupposes an algebra in which the hypothetical node's leaves satisfy the act
  events; `mugRec` below is that algebra and separates the readings (`mugRec_readings_differ`);
* the R2-SIA clause of Proposition 13 fails at `x = 1`, `y = 3`: `paySum(pay ∧ O_T)·fiberMass =
  −1/4 ≠ 1/4 = r2Sia(pay)·ν(pay ∧ O_T)` (`prop13_r2Sia_refuted_recordsFor_alone`);
* EV = R1-state **does** hold (an instance of `prop13_ev_eq_r1State`, N+: `mug1_r1State_instance`);
* the SSC clause fails: `dp-core-tree`'s `mug1_ssc_refuted` and `dp-calibration`'s
  `mug1_perRun_not_strict` (cited, not reproved).
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

section mugging

variable (x y : ℚ)

/-- The label `C(d)(pay) = ½` on the mugging.
Source: [[decision-problems-v2]] Proposition 6 (`q₀ = ½`); mandate T3(e)
Kind: D -/
abbrev mugHalf : Proc Unit (fun _ => Act2) ℚ := procQ (1/2) (by norm_num) (by norm_num)

/-- The `d`-node of branch `i` of `B₁` (`0` = `T`, the real query; `1` = `H`, the simulation).
Source: [[decision-problems-v2]] Proposition 6
Kind: D -/
def mug1Node (i : Fin 2) : (mug1 x y).DecNode := ⟨i, none⟩

/-- Every leaf of `B₁` is `⟨i, act, ()⟩`. Source: none: infrastructure. Kind: L -/
theorem mug1_leaves (ℓ : (mug1 x y).Leaves) : ∃ (i : Fin 2) (act : Act2), ℓ = ⟨i, act, ()⟩ := by
  unfold mug1 at ℓ
  rcases ℓ with ⟨i, act, ⟨⟩⟩
  exact ⟨i, act, rfl⟩

/-- Every decision node of `B₁` is one of the two `d`-nodes. Source: none: infrastructure. Kind: L -/
theorem mug1_nodes_cases (q : (mug1 x y).DecNode) : ∃ i : Fin 2, q = mug1Node x y i := by
  unfold mug1 at q
  rcases q with ⟨i, (_ | ⟨act, e⟩)⟩
  · exact ⟨i, rfl⟩
  · exact e.elim

/-- Every leaf of `B₁` has mass `¼` at `C(d) = ½`. Source: Definition 6. Kind: L -/
theorem mug1_leafLaw_half (i : Fin 2) (act : Act2) :
    leafLaw mugHalf (mug1 x y) ⟨i, act, ()⟩ = 1/4 := by
  unfold mug1
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.fair, FinDistr.coin, procQ]
  fin_cases i <;> cases act <;> simp <;> norm_num

/-- The world at a leaf of `B₁`. Source: none: infrastructure. Kind: L -/
theorem mug1_world (i : Fin 2) (act : Act2) : world (mug1 x y) ⟨i, act, ()⟩ = mugWorld1 i act := rfl

/-- The payoff at a leaf of `B₁`. Source: none: infrastructure. Kind: L -/
theorem mug1_payoff (i : Fin 2) (act : Act2) :
    payoff (mug1 x y) ⟨i, act, ()⟩ = mugPay x y (mugWorld1 i act) := rfl

/-- The edge a leaf takes at the `d`-node of branch `i`. Source: none: infrastructure. Kind: L -/
theorem mug1_edgeOf (i j : Fin 2) (act : Act2) :
    edgeOf (mug1 x y) (mug1Node x y i) ⟨j, act, ()⟩ = if j = i then some act else none := by
  unfold mug1Node mug1
  by_cases h : j = i
  · subst h; simp [edgeOf_chance, edgeOf_decision_none]
  · simp [edgeOf_chance, h]

/-- Every run of `B₁` meets `d` once. Source: none: infrastructure. Kind: L -/
theorem mug1_count (i : Fin 2) (act : Act2) : count () (mug1 x y) ⟨i, act, ()⟩ = 1 := by
  unfold mug1; rfl

/-- **`H*` fails on `B₁` at `C(d) = ½`**: the `H`-branch leaf `(H, pay)` has mass `¼`, meets
the hypothetical `d`-node, and its world `(H, ⊥, 1)` is not in `O_T`.
Source: `sl-defensible-claims.md` S1 ("simulation nodes tolerated off `O_d`-runs, as in the
mugging"); mandate T3(e)
Kind: N− -/
theorem mug1_not_hStar : ¬ HStar mugObs mugActEv mugHalf (mug1 x y) () := by
  rintro ⟨-, h2⟩
  have hpos : 0 < leafLaw mugHalf (mug1 x y) ⟨1, .a, ()⟩ := by
    rw [mug1_leafLaw_half]; norm_num
  have hc : 0 < count () (mug1 x y) ⟨1, .a, ()⟩ := by rw [mug1_count]; exact one_pos
  have := h2 ⟨1, .a, ()⟩ hpos hc
  rw [mug1_world] at this
  simp [mugObs, mugWorld1] at this

/-- **EV(pay) on `B₁`**: `paySum(pay ∧ O_T) = −x/4` and `ν(pay ∧ O_T) = ¼`, so the evidential
value of paying is `−x`.
Source: [[decision-problems-v2]] Proposition 6 (`V_{s_d}(pay) = −x` at the tails state);
mandate T3(e)
Kind: N+ -/
theorem mug1_ev_pay :
    paySum mugHalf (mug1 x y) (mugActEv () .a ∩ mugObs ()) = -x/4 ∧
    nu mugHalf (mug1 x y) (mugActEv () .a ∩ mugObs ()) = 1/4 := by
  constructor
  · rw [paySum_eq_sum_ite, mug1_sum]
    simp only [Fin.sum_univ_two, Act2.sum_univ, mug1_leafLaw_half, mug1_world, mug1_payoff]
    simp [mugWorld1, mugPay, mugActEv, mugObs]; ring
  · rw [mug1_nu]
    simp [mugActEv, mugObs, procQ]; norm_num

/-- The fiber of `d` on `B₁` is every decision node. Source: none: infrastructure. Kind: L -/
theorem mug1_fiber : fiber (mug1 x y) () = Finset.univ := by
  ext q; simp [fiber]

/-- A sum over the decision nodes of `B₁`: the two `d`-nodes.
Source: none: infrastructure. Kind: L -/
theorem mug1_sum_decNode (f : (mug1 x y).DecNode → ℚ) :
    ∑ q, f q = f (mug1Node x y 0) + f (mug1Node x y 1) := by
  unfold mug1Node
  unfold mug1 at f ⊢
  rw [sum_decNode_chance, Fin.sum_univ_two, sum_decNode_decision, sum_decNode_decision]
  have e : ∀ (i : Fin 2) (a : Act2), (∑ q, f ⟨i, some ⟨a, q⟩⟩) = 0 :=
    fun i a => Finset.sum_eq_zero (fun q _ => q.elim)
  simp only [e, Finset.sum_const_zero, add_zero]

/-- The `act`-edge payoff mass at the `d`-node of branch `i`: `¼ · r(i, act)`.
Source: none: infrastructure. Kind: L -/
theorem mug1_edgePay (i : Fin 2) (act : Act2) :
    (∑ ℓ, if edgeOf (mug1 x y) (mug1Node x y i) ℓ = some act then
      leafLaw mugHalf (mug1 x y) ℓ * payoff (mug1 x y) ℓ else 0) =
      1/4 * mugPay x y (mugWorld1 i act) := by
  rw [mug1_sum]
  simp only [Fin.sum_univ_two, Act2.sum_univ, mug1_edgeOf, mug1_leafLaw_half, mug1_payoff]
  fin_cases i <;> cases act <;> simp

/-- **The forcing masses on `B₁`**: `forcedBelow_{q_i}(act) = ½ · r(i, act)` — at the `T`-node
`(−x/2, 0)`, at the `H`-node `(y/2, 0)` — from `edge_paySum_eq_mul_forcedBelow` at `C(d) = ½`.
Source: [[decision-problems-v2]] §8 (`R_q G_q`); mandate T3(e)
Kind: L -/
theorem mug1_forcedBelow (i : Fin 2) (act : Act2) :
    forcedBelow (mug1 x y) (NodePolicy.ofProc mugHalf (mug1 x y)) (mug1Node x y i) act =
      1/2 * mugPay x y (mugWorld1 i act) := by
  have h := edge_paySum_eq_mul_forcedBelow mugHalf (mug1 x y) (mug1Node x y i) act
  rw [mug1_edgePay] at h
  have hw : (mugHalf (pt (mug1 x y) (mug1Node x y i))).w act = 1/2 := by
    cases act <;> norm_num [procQ]
  rw [hw] at h
  linarith

/-- `R_{q_i} = ½` on `B₁` at `C(d) = ½`. Source: none: infrastructure. Kind: L -/
theorem mug1_reach (i : Fin 2) : reach mugHalf (mug1 x y) (mug1Node x y i) = 1/2 := by
  unfold mug1Node mug1
  simp only [reach_chance, reach_decision_none, FinDistr.fair, FinDistr.coin]
  fin_cases i <;> simp <;> norm_num

/-- **R2-SIA on `B₁`**: `r2Sia(pay) = (y − x)/2` (the `T`-node's `−x/2` plus the simulation
node's `y/2`) and `r2Sia(refuse) = 0`.
Source: `sl-defensible-claims.md` S1 ("`∑_q R_q G_q = (1, 0)` pays"); mandate T3(e)
Kind: N+ -/
theorem mug1_r2Sia :
    r2Sia mugHalf (mug1 x y) () .a = (y - x) / 2 ∧ r2Sia mugHalf (mug1 x y) () .b = 0 := by
  constructor <;>
  · unfold r2Sia
    rw [mug1_fiber, mug1_sum_decNode]
    simp only [dite_true, transport_const, mug1_forcedBelow, mugWorld1, mugPay]
    simp; try ring

/-- `∑_q R_q = 1` on `B₁` (both `d`-nodes are reached with probability `½`).
Source: mandate T3(e)
Kind: L -/
theorem mug1_fiberMass : fiberMass mugHalf (mug1 x y) () = 1 := by
  unfold fiberMass
  rw [mug1_fiber, mug1_sum_decNode, mug1_reach, mug1_reach]; norm_num

/-- The `T`-node is a.s. node-action-veridical and active; the `H`-node is neither
(its leaves' worlds are off `O_T` and off every action event).
Source: [[decision-problems-v2]] Proposition 6 (the hypothetical query); mandate T3(e)
Kind: L -/
theorem mug1_nodes :
    (NodeActionVeridicalAS mugActEv mugHalf (mug1 x y) (mug1Node x y 0) ∧
      ActiveNode mugObs mugHalf (mug1 x y) () (mug1Node x y 0)) ∧
    ¬ ActiveNode mugObs mugHalf (mug1 x y) () (mug1Node x y 1) ∧
    ¬ NodeActionVeridicalAS mugActEv mugHalf (mug1 x y) (mug1Node x y 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro ℓ a _ ha
    obtain ⟨j, act, rfl⟩ := mug1_leaves x y ℓ
    rw [mug1_edgeOf] at ha
    by_cases hj : j = 0
    · subst hj
      simp only [if_true, Option.some.injEq] at ha
      subst ha
      rw [mug1_world]
      cases act <;> simp [mugActEv, mugWorld1]
    · simp [hj] at ha
  · refine ⟨⟨0, .a, ()⟩, by rw [mug1_leafLaw_half]; norm_num, ?_, by rw [mug1_edgeOf]; simp⟩
    rw [mug1_world]; simp [mugWorld1, mugObs]
  · rintro ⟨ℓ, -, hobs, he⟩
    obtain ⟨j, act, rfl⟩ := mug1_leaves x y ℓ
    rw [mug1_edgeOf] at he
    by_cases hj : j = 1
    · subst hj
      rw [mug1_world] at hobs
      cases act <;> simp [mugWorld1, mugObs] at hobs
    · simp [hj] at he
  · intro h
    have := h ⟨1, .a, ()⟩ .a (by rw [mug1_leafLaw_half]; norm_num) (by rw [mug1_edgeOf]; simp)
    rw [mug1_world] at this
    simp [mugWorld1, mugActEv] at this

/-- The two `d`-nodes are distinct. Source: none: infrastructure. Kind: L -/
theorem mug1Node_one_ne_zero : mug1Node x y 1 ≠ mug1Node x y 0 := by
  intro h; have h1 := congrArg Sigma.fst h; simp [mug1Node] at h1

/-- **Reading 2's averaging set on `B₁` is the `T`-node alone.**
Source: dp-sl-2-058 reading 2; mandate T3(e)
Kind: L -/
theorem mug1_realFiber : realFiber mugObs mugActEv mugHalf (mug1 x y) () = {mug1Node x y 0} := by
  obtain ⟨⟨hnav0, hact0⟩, hact1, -⟩ := mug1_nodes x y
  ext q
  rw [mem_realFiber, Finset.mem_singleton]
  obtain ⟨i, rfl⟩ := mug1_nodes_cases x y q
  fin_cases i
  · exact ⟨fun _ => rfl, fun _ => ⟨rfl, hnav0, hact0⟩⟩
  · exact ⟨fun ⟨_, _, h⟩ => absurd h hact1, fun h => absurd h (mug1Node_one_ne_zero x y)⟩

/-- **Reading 1's averaging set on `B₁` is also the `T`-node alone**: under `mugActEv`
(`pay ↦ {tPay}`) the `H`-node's leaves lie in no action event, so it is not
node-action-veridical. The two readings coincide on `B₁`; they come apart on `mugRec` below.
Source: dp-sl-2-058 reading 1; mandate T3(e) (whose "reading 1 = 1" presupposes the act
recorded on the `H`-branch — a finding)
Kind: L -/
theorem mug1_realFiberAll : realFiberAll mugActEv mugHalf (mug1 x y) () = {mug1Node x y 0} := by
  obtain ⟨⟨hnav0, -⟩, -, hnav1⟩ := mug1_nodes x y
  ext q
  rw [mem_realFiberAll, Finset.mem_singleton]
  obtain ⟨i, rfl⟩ := mug1_nodes_cases x y q
  fin_cases i
  · exact ⟨fun _ => rfl, fun _ => ⟨rfl, hnav0⟩⟩
  · exact ⟨fun ⟨_, h⟩ => absurd h hnav1, fun h => absurd h (mug1Node_one_ne_zero x y)⟩

/-- **R2-real (reading 2) on `B₁`**: `r2RealPay(pay) = −x/2`, `r2RealMass = ½`, so
R2-real(pay) `= −x` — it agrees with EV at the recorded point (and reading 1 gives the same
numbers here).
Source: dp-sl-2-058 ("under reading 2 … collapses into `H*`"); mandate T3(e)
Kind: N+ -/
theorem mug1_r2Real :
    r2RealPay mugObs mugActEv mugHalf (mug1 x y) () .a = -x/2 ∧
    r2RealMass mugObs mugActEv mugHalf (mug1 x y) () = 1/2 ∧
    r2RealAllPay mugActEv mugHalf (mug1 x y) () .a = -x/2 ∧
    r2RealAllMass mugActEv mugHalf (mug1 x y) () = 1/2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold r2RealPay
    rw [mug1_realFiber, Finset.sum_singleton]
    simp only [dite_true, transport_const, mug1_forcedBelow, mugWorld1, mugPay]
    simp; try ring
  · unfold r2RealMass
    rw [mug1_realFiber, Finset.sum_singleton, mug1_reach]
  · unfold r2RealAllPay
    rw [mug1_realFiberAll, Finset.sum_singleton]
    simp only [dite_true, transport_const, mug1_forcedBelow, mugWorld1, mugPay]
    simp; try ring
  · unfold r2RealAllMass
    rw [mug1_realFiberAll, Finset.sum_singleton, mug1_reach]

/-- **Proposition 13's R2-SIA clause is refuted under `RecordsFor` alone** (the mugging at
`x = 1`, `y = 3`, `C(d) = ½`): recording holds, `H*` fails, and
`paySum(pay ∧ O_T) · fiberMass = −¼ ≠ ¼ = r2Sia(pay) · ν(pay ∧ O_T)` — the conclusion of
`prop13_ev_eq_r2Sia` with `RecordsFor` in place of `H*`. In values: EV(pay) `= −1` (refuses),
R2-SIA(pay) `= 1` (pays), R2-real(pay) `= −1` (reading 2, as the pair
`r2RealPay = −1 · r2RealMass`, `r2RealMass = ½`; agrees with EV). This **confirms** the source's
R2-SIA clause and **refutes** its R2-real clause on `B₁`: under `mugActEv` the `H`-node is not
node-action-veridical, so *both* readings average the `T`-node only and give `−1 = EV`
(`mug1_r2Real`, all four values); the readings separate only on the act-recording `mugRec`,
where reading 1 gives `(y − x)/2` (`mugRec_readings_differ`). In general, reading-2 R2-real
equals EV under recording alone (`prop13_ev_eq_r2Real_of_recordsFor`).
Source: `sl-defensible-claims.md` S1 ("Under Definition-7 recording **alone** … the R2-SIA,
R2-real and SSC clauses fail (mugging `B₁`: strict-OC EDT `(−1, 0)` refuses while
`∑_q R_q G_q = (1, 0)` pays)"); dp-sl-2-058; mandate T3(e)
Kind: N−
Fidelity: exact for the R2-SIA clause (the refuted statement is `prop13_ev_eq_r2Sia`'s
conclusion under `RecordsFor`); the source's R2-real sub-clause is false on `B₁` under either
reading as formalized (`mug1_r2Real`), and false in general under reading 2
(`prop13_ev_eq_r2Real_of_recordsFor`); it is true under reading 1 only on an act-recording
tree such as `mugRec` -/
theorem prop13_r2Sia_refuted_recordsFor_alone :
    RecordsFor mugObs mugActEv mugHalf (mug1 1 3) () ∧
    ¬ HStar mugObs mugActEv mugHalf (mug1 1 3) () ∧
    paySum mugHalf (mug1 1 3) (mugActEv () .a ∩ mugObs ()) * fiberMass mugHalf (mug1 1 3) () ≠
      r2Sia mugHalf (mug1 1 3) () .a * nu mugHalf (mug1 1 3) (mugActEv () .a ∩ mugObs ()) ∧
    r2Sia mugHalf (mug1 1 3) () .a = 1 ∧
    r2RealPay mugObs mugActEv mugHalf (mug1 1 3) () .a =
      -1 * r2RealMass mugObs mugActEv mugHalf (mug1 1 3) () ∧
    r2RealMass mugObs mugActEv mugHalf (mug1 1 3) () = 1/2 := by
  obtain ⟨hp, hn⟩ := mug1_ev_pay 1 3
  obtain ⟨hs, -⟩ := mug1_r2Sia 1 3
  obtain ⟨hr1, hr2, -, -⟩ := mug1_r2Real 1 3
  refine ⟨mug1_recordsFor 1 3, mug1_not_hStar 1 3, ?_, ?_, ?_, hr2⟩
  · rw [hp, hn, hs, mug1_fiberMass]; norm_num
  · rw [hs]; norm_num
  · rw [hr1, hr2]; norm_num

/-- **EV = R2-real (reading 2) holds on `B₁` under recording alone** (Proposition 13(b′)
instantiated at a point without `H*`, N+): `r2RealPay(pay) = −x/2`, `r2RealMass = ½`, and the
cross-multiplied identity of `prop13_ev_eq_r2Real_of_recordsFor` reads
`(−x/4) · ½ = (−x/2) · ¼`. Beside `mug1_r1State_instance`: both `RecordsFor`-only clauses of
Proposition 13 hold on the mugging, only the R2-SIA clause fails.
Source: `sl-defensible-claims.md` S1 (the R2-real clause); dp-sl-2-061 (i); mandate T3(e)
Kind: N+ -/
theorem mug1_r2Real_instance :
    paySum mugHalf (mug1 x y) (mugActEv () .a ∩ mugObs ()) *
        r2RealMass mugObs mugActEv mugHalf (mug1 x y) () =
      r2RealPay mugObs mugActEv mugHalf (mug1 x y) () .a *
        nu mugHalf (mug1 x y) (mugActEv () .a ∩ mugObs ()) ∧
    paySum mugHalf (mug1 x y) (mugActEv () .a ∩ mugObs ()) = -x/4 ∧
    nu mugHalf (mug1 x y) (mugActEv () .a ∩ mugObs ()) = 1/4 ∧
    r2RealPay mugObs mugActEv mugHalf (mug1 x y) () .a = -x/2 ∧
    r2RealMass mugObs mugActEv mugHalf (mug1 x y) () = 1/2 := by
  obtain ⟨hp, hn⟩ := mug1_ev_pay x y
  obtain ⟨hr1, hr2, -, -⟩ := mug1_r2Real x y
  exact ⟨prop13_ev_eq_r2Real_of_recordsFor mugObs mugActEv mugHalf (mug1 x y) ()
    (mug1_recordsFor x y) .a, hp, hn, hr1, hr2⟩

/-- **EV = R1-state holds on `B₁` under recording alone** (Proposition 13(a) instantiated, N+):
`r1StatePay(pay) = −x/2`, `r1StateNu(pay) = ½` (the deviation `C[d ↦ pay]` pays on the
`T`-branch with probability `½`), and the cross-multiplied identity reads
`(−x/4) · ½ = (−x/2) · ¼`.
Source: `sl-defensible-claims.md` S1 ("only 'EDT = R1-state on `A_d^+`' survives"); mandate T3(e)
Kind: N+ -/
theorem mug1_r1State_instance :
    r1StatePay mugObs mugHalf (mug1 x y) () .a = -x/2 ∧
    r1StateNu mugObs mugHalf (mug1 x y) () .a = 1/2 ∧
    paySum mugHalf (mug1 x y) (mugActEv () .a ∩ mugObs ()) *
        r1StateNu mugObs mugHalf (mug1 x y) () .a =
      r1StatePay mugObs mugHalf (mug1 x y) () .a *
        nu mugHalf (mug1 x y) (mugActEv () .a ∩ mugObs ()) := by
  have hdev : (mugHalf.deviatePure () .a) = fun _ => FinDistr.pure .a := by
    rw [Proc.deviatePure, deviate_unit]
  refine ⟨?_, ?_, prop13_ev_eq_r1State mugObs mugActEv mugHalf (mug1 x y) ()
    (mug1_recordsFor x y) .a⟩
  · unfold r1StatePay
    rw [hdev, paySum_eq_sum_ite, mug1_sum]
    simp only [Fin.sum_univ_two, Act2.sum_univ, mug1_world, mug1_payoff]
    unfold mug1
    simp [mugWorld1, mugPay, mugObs, FinDistr.fair, FinDistr.coin]; ring
  · unfold r1StateNu
    rw [hdev, mug1_nu]
    simp [mugObs]

end mugging

/-! ## The act-recording mugging: the two readings of R2-real come apart -/

section mugRec

variable (x y : ℚ)

/-- The payoff of the act-recording mugging: `(T, pay) ↦ −x`, `(H, pay) ↦ y`, refuse `↦ 0`.
Source: [[decision-problems-v2]] Proposition 6 (`r = −x·1[pay] + y·1[transfer]`), with the act
written on the `H`-branch leaves
Kind: D -/
def mugRecPay (c : Bool) (act : Act2) : ℚ :=
  match c, act with
  | true, .a => -x
  | false, .a => y
  | _, .b => 0

/-- **The act-recording mugging**: `B₁`'s shape (fair coin, index `0` = `T`; a `d`-node on each
branch) over the worlds `(coin, act)` of `dp-core-tree`'s `coinQuery`, with `B₁`'s payoffs. The
`H`-branch leaves now record the draw, so the hypothetical node is node-action-veridical
though still off every `O_T`-run: reading 1 of R2-real averages it in, reading 2 does not.
Source: dp-sl-2-058 (witness design; the mugging in the act-recording algebra, FA-19′)
Kind: D -/
def mugRec : Tree CoinQueryW Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => .decision () fun act =>
    .leaf (decide (i = 0), act) (mugRecPay x y (decide (i = 0)) act)

/-- `O_T = {coin = T}` on the act-recording mugging. Source: dp-sl-2-058. Kind: D -/
def mugRecObs : Unit → Finset CoinQueryW := fun _ => cqCoin

/-- The `d`-node of branch `i` of `mugRec`. Source: dp-sl-2-058. Kind: D -/
def mugRecNode (i : Fin 2) : (mugRec x y).DecNode := ⟨i, none⟩

/-- Every leaf of `mugRec` is `⟨i, act, ()⟩`. Source: none: infrastructure. Kind: L -/
theorem mugRec_leaves (ℓ : (mugRec x y).Leaves) : ∃ (i : Fin 2) (act : Act2), ℓ = ⟨i, act, ()⟩ := by
  unfold mugRec at ℓ
  rcases ℓ with ⟨i, act, ⟨⟩⟩
  exact ⟨i, act, rfl⟩

/-- Every decision node of `mugRec` is one of the two `d`-nodes. Source: none: infrastructure. Kind: L -/
theorem mugRec_nodes_cases (q : (mugRec x y).DecNode) : ∃ i : Fin 2, q = mugRecNode x y i := by
  unfold mugRec at q
  rcases q with ⟨i, (_ | ⟨act, e⟩)⟩
  · exact ⟨i, rfl⟩
  · exact e.elim

/-- Every leaf of `mugRec` has mass `¼` at `C(d) = ½`. Source: Definition 6. Kind: L -/
theorem mugRec_leafLaw_half (i : Fin 2) (act : Act2) :
    leafLaw mugHalf (mugRec x y) ⟨i, act, ()⟩ = 1/4 := by
  unfold mugRec
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.fair, FinDistr.coin, procQ]
  fin_cases i <;> cases act <;> simp <;> norm_num

/-- The edge a leaf takes at the `d`-node of branch `i`. Source: none: infrastructure. Kind: L -/
theorem mugRec_edgeOf (i j : Fin 2) (act : Act2) :
    edgeOf (mugRec x y) (mugRecNode x y i) ⟨j, act, ()⟩ = if j = i then some act else none := by
  unfold mugRecNode mugRec
  by_cases h : j = i
  · subst h; simp [edgeOf_chance, edgeOf_decision_none]
  · simp [edgeOf_chance, h]

/-- The world at a leaf of `mugRec`. Source: none: infrastructure. Kind: L -/
theorem mugRec_world (i : Fin 2) (act : Act2) :
    world (mugRec x y) ⟨i, act, ()⟩ = (decide (i = 0), act) := rfl

/-- The payoff at a leaf of `mugRec`. Source: none: infrastructure. Kind: L -/
theorem mugRec_payoff (i : Fin 2) (act : Act2) :
    payoff (mugRec x y) ⟨i, act, ()⟩ = mugRecPay x y (decide (i = 0)) act := rfl

/-- Every run of `mugRec` meets `d` once. Source: none: infrastructure. Kind: L -/
theorem mugRec_count (i : Fin 2) (act : Act2) : count () (mugRec x y) ⟨i, act, ()⟩ = 1 := by
  unfold mugRec; rfl

/-- A sum over the leaves of `mugRec`. Source: none: infrastructure. Kind: L -/
theorem mugRec_sum (f : (mugRec x y).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold mugRec at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- A sum over the decision nodes of `mugRec`. Source: none: infrastructure. Kind: L -/
theorem mugRec_sum_decNode (f : (mugRec x y).DecNode → ℚ) :
    ∑ q, f q = f (mugRecNode x y 0) + f (mugRecNode x y 1) := by
  unfold mugRecNode
  unfold mugRec at f ⊢
  rw [sum_decNode_chance, Fin.sum_univ_two, sum_decNode_decision, sum_decNode_decision]
  have e : ∀ (i : Fin 2) (a : Act2), (∑ q, f ⟨i, some ⟨a, q⟩⟩) = 0 :=
    fun i a => Finset.sum_eq_zero (fun q _ => q.elim)
  simp only [e, Finset.sum_const_zero, add_zero]

/-- The forcing masses on `mugRec`: `½ · r(i, act)`. Source: none: infrastructure. Kind: L -/
theorem mugRec_forcedBelow (i : Fin 2) (act : Act2) :
    forcedBelow (mugRec x y) (NodePolicy.ofProc mugHalf (mugRec x y)) (mugRecNode x y i) act =
      1/2 * mugRecPay x y (decide (i = 0)) act := by
  have h := edge_paySum_eq_mul_forcedBelow mugHalf (mugRec x y) (mugRecNode x y i) act
  have hedge : (∑ ℓ, if edgeOf (mugRec x y) (mugRecNode x y i) ℓ = some act then
      leafLaw mugHalf (mugRec x y) ℓ * payoff (mugRec x y) ℓ else 0) =
      1/4 * mugRecPay x y (decide (i = 0)) act := by
    rw [mugRec_sum]
    simp only [Fin.sum_univ_two, Act2.sum_univ, mugRec_edgeOf, mugRec_leafLaw_half, mugRec_payoff]
    fin_cases i <;> cases act <;> simp
  rw [hedge] at h
  have hw : (mugHalf (pt (mugRec x y) (mugRecNode x y i))).w act = 1/2 := by
    cases act <;> norm_num [procQ]
  rw [hw] at h
  linarith

/-- `R_{q_i} = ½` on `mugRec`. Source: none: infrastructure. Kind: L -/
theorem mugRec_reach (i : Fin 2) : reach mugHalf (mugRec x y) (mugRecNode x y i) = 1/2 := by
  unfold mugRecNode mugRec
  simp only [reach_chance, reach_decision_none, FinDistr.fair, FinDistr.coin]
  fin_cases i <;> simp <;> norm_num

/-- Both `d`-nodes of `mugRec` are a.s. node-action-veridical (the leaves record the act); the
`T`-node is active and the `H`-node is not.
Source: dp-sl-2-058
Kind: L -/
theorem mugRec_nodes :
    (∀ i : Fin 2, NodeActionVeridicalAS cqActEv mugHalf (mugRec x y) (mugRecNode x y i)) ∧
    ActiveNode mugRecObs mugHalf (mugRec x y) () (mugRecNode x y 0) ∧
    ¬ ActiveNode mugRecObs mugHalf (mugRec x y) () (mugRecNode x y 1) := by
  refine ⟨fun i ℓ a _ ha => ?_, ?_, ?_⟩
  · obtain ⟨j, act, rfl⟩ := mugRec_leaves x y ℓ
    rw [mugRec_edgeOf] at ha
    by_cases hj : j = i
    · subst hj
      simp only [if_true, Option.some.injEq] at ha
      subst ha
      rw [mugRec_world]; simp [cqActEv]
    · simp [hj] at ha
  · refine ⟨⟨0, .a, ()⟩, by rw [mugRec_leafLaw_half]; norm_num, ?_, by rw [mugRec_edgeOf]; simp⟩
    rw [mugRec_world]; simp [mugRecObs, cqCoin]
  · rintro ⟨ℓ, -, hobs, he⟩
    obtain ⟨j, act, rfl⟩ := mugRec_leaves x y ℓ
    rw [mugRec_edgeOf] at he
    by_cases hj : j = 1
    · subst hj
      rw [mugRec_world] at hobs
      simp [mugRecObs, cqCoin] at hobs
    · simp [hj] at he

/-- The two `d`-nodes of `mugRec` are distinct. Source: none: infrastructure. Kind: L -/
theorem mugRecNode_one_ne_zero : mugRecNode x y 1 ≠ mugRecNode x y 0 := by
  intro h; have h1 := congrArg Sigma.fst h; simp [mugRecNode] at h1

/-- Reading 2's set on `mugRec` is the `T`-node; reading 1's set is both nodes.
Source: dp-sl-2-058
Kind: L -/
theorem mugRec_fibers :
    realFiber mugRecObs cqActEv mugHalf (mugRec x y) () = {mugRecNode x y 0} ∧
    realFiberAll cqActEv mugHalf (mugRec x y) () = Finset.univ := by
  obtain ⟨hnav, hact0, hact1⟩ := mugRec_nodes x y
  constructor
  · ext q
    rw [mem_realFiber, Finset.mem_singleton]
    obtain ⟨i, rfl⟩ := mugRec_nodes_cases x y q
    fin_cases i
    · exact ⟨fun _ => rfl, fun _ => ⟨rfl, hnav 0, hact0⟩⟩
    · exact ⟨fun ⟨_, _, h⟩ => absurd h hact1, fun h => absurd h (mugRecNode_one_ne_zero x y)⟩
  · ext q
    rw [mem_realFiberAll]
    refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
    obtain ⟨i, rfl⟩ := mugRec_nodes_cases x y q
    exact ⟨rfl, hnav i⟩

/-- **The two readings of R2-real come apart on the act-recording mugging** (N+ for
dp-sl-2-058): at `C(d) = ½`, reading 2 gives `(−x/2)/(½) = −x` (EV's verdict) and reading 1
gives `((y − x)/2)/1 = (y − x)/2` (R2-SIA's verdict); at `x = 1`, `y = 3` these are `−1` and
`1`. Recording at `O_T` holds on `mugRec` for `C(d) = ½` and `H*` fails, exactly as on `B₁`.
Source: dp-sl-2-058 ("the two readings agree at Definition-7-recorded points and differ
elsewhere" — sharpened: they agree under `H*`, `r2RealAll_eq_r2Sia_of_hStar`, and differ at a
recorded point without `H*`); mandate T3(e), §3.4
Kind: N+
Fidelity: exact -/
theorem mugRec_readings_differ :
    r2RealPay mugRecObs cqActEv mugHalf (mugRec x y) () .a = -x/2 ∧
    r2RealMass mugRecObs cqActEv mugHalf (mugRec x y) () = 1/2 ∧
    r2RealAllPay cqActEv mugHalf (mugRec x y) () .a = (y - x)/2 ∧
    r2RealAllMass cqActEv mugHalf (mugRec x y) () = 1 := by
  obtain ⟨hf2, hf1⟩ := mugRec_fibers x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold r2RealPay
    rw [hf2, Finset.sum_singleton]
    simp only [dite_true, transport_const, mugRec_forcedBelow]
    simp [mugRecPay]; ring
  · unfold r2RealMass
    rw [hf2, Finset.sum_singleton, mugRec_reach]
  · unfold r2RealAllPay
    rw [hf1, mugRec_sum_decNode]
    simp only [dite_true, transport_const, mugRec_forcedBelow]
    simp [mugRecPay]; ring
  · unfold r2RealAllMass
    rw [hf1, mugRec_sum_decNode, mugRec_reach, mugRec_reach]; norm_num

/-- `mugRec` records at `d` for `C(d) = ½` at `O_T` (the `T`-node is the unique `d`-node on
`O_T`-runs, subtree-veridical, the act recorded) and fails `H*`.
Source: dp-sl-2-058
Kind: N+ -/
theorem mugRec_recordsFor_not_hStar :
    RecordsFor mugRecObs cqActEv mugHalf (mugRec x y) () ∧
    ¬ HStar mugRecObs cqActEv mugHalf (mugRec x y) () := by
  constructor
  · intro ℓ _ hobs
    obtain ⟨i, act, rfl⟩ := mugRec_leaves x y ℓ
    refine ⟨mugRec_count x y i act, ?_⟩
    intro q hq a ha
    obtain ⟨i', rfl⟩ := mugRec_nodes_cases x y q
    rw [mugRec_edgeOf] at ha
    by_cases hi : i = i'
    · subst hi
      simp only [if_true, Option.some.injEq] at ha
      subst ha
      rw [mugRec_world] at hobs
      refine ⟨?_, ?_, ?_⟩
      · intro ℓ' hℓ'
        rw [mem_leavesBelow] at hℓ'
        obtain ⟨j, b, rfl⟩ := mugRec_leaves x y ℓ'
        rw [mugRec_edgeOf] at hℓ'
        by_cases hj : j = i
        · subst hj; rw [mugRec_world]; simpa [mugRecObs, cqCoin] using hobs
        · simp [hj] at hℓ'
      · rw [mugRec_world]; simp [cqActEv]
      · intro a' ha'; rw [mugRec_world] at ha'; simp [cqActEv] at ha'; exact ha'.symm
    · simp [hi] at ha
  · rintro ⟨-, h2⟩
    have hpos : 0 < leafLaw mugHalf (mugRec x y) ⟨1, .a, ()⟩ := by
      rw [mugRec_leafLaw_half]; norm_num
    have hc : 0 < count () (mugRec x y) ⟨1, .a, ()⟩ := by rw [mugRec_count]; exact one_pos
    have := h2 ⟨1, .a, ()⟩ hpos hc
    rw [mugRec_world] at this
    simp [mugRecObs, cqCoin] at this

end mugRec

end Cleanroom.Decision.DpSmokingLesion
