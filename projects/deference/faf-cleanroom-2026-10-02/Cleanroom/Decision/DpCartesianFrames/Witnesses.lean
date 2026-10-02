import Cleanroom.Decision.DpCartesianFrames.Hon
import Cleanroom.Decision.DpCartesianFrames.Straddle
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Witnesses and refutations on catalogue and hand trees

Package `dp-cartesian-frames`, file 8. Every frame here is `Fr`/`Loc` of a `dp-core-tree`
tree (catalogue or built here); no hand-transcribed matrix is a headline. Lazy seeding.

* **T1(c), the AMD's proper commit** (`amd_payoff4_mem_frNode_image`,
  `amd_payoff4_not_mem_fr_image`): the payoff-4 leaf is in `Image(Fr^nd amd)` and not in
  `Image(Fr amd)` — self-succession is visible only through the evaluation map.
* **T3's converses.** (ii)∧¬(i): the inert simulation `inertTree` (a coin; on tails a real
  `d`-node with distinct `O_d`-leaves, on heads a `d`-node off `O_d` whose edges lead to the
  same leaf): `Loc d` powerless outside `S_{O_d}` (so observable) while the heads node is not
  subtree-veridical. (iii)∧¬(ii): the umbrella-mugging `umbTree` (post 11's `C₀` as a tree:
  `A_d = {u, n, u↔r, u↔s}`, coin rain/sun, both nodes consult `d`): `{rain, sun}` observable
  at `Loc d`, not powerless, sun node not subtree-veridical. Both through ZO-8's criterion.
* **T9(d)'s N+ witness**, the heads-honest policy-menu mugging `menuTree`: observable at
  `Loc d`, `Loc d ≃ᵇ Hon d`, not powerless, heads node not subtree-veridical.
* **T11(a) / dp-core-061 / CF-15**: `mug1 x y` *is* a two-branch tree (`mug1_eq_twoBranch`,
  `rfl`); the coin is column-determined at `Loc d` and **not observable** — for every `x`, `y`
  (the world labels record the choice; positivity of `x`, `y` is not needed); powerlessness
  fails exactly at the heads node, which is the one node that is not subtree-veridical;
  the decoupled mugging is powerless, hence observable.
* **T4(c) / CF-13**, look-decide: `O_d` is not observable in the global frame (membership is
  row-dependent), and observable at `Loc d` (by the Local Theorem).
* **T5(a), the β-pair** (headline 3's refutation row): `Fr (pairTree β₁) = Fr (pairTree β₂)`
  literally for all inner weights, `pairTree fair` strongly fair, `pairTree (coin ⅓)` not —
  so no predicate of the frame is strong fairness (`no_frame_predicate_is_stronglyFair`).
-/

namespace Cleanroom.Decision.DpCartesianFrames

open CartesianFrames
open scoped CartesianFrames.Frame
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpFairnessReloc

/-! ### T1(c): the AMD's commit is proper -/

/-- **The payoff-4 leaf is realized by a node assignment** (continue at the first node, exit at
the second).
Source: cf-correspondence CF-4 (line 19: "AMD's payoff-4 leaf … is in `Image(Fr^nd)`")
Kind: N+
Fidelity: exact -/
theorem amd_payoff4_mem_frNode_image :
    ((AmdW.sba, (4 : ℚ)) : AmdW × ℚ) ∈ (FrNode amd).image :=
  ⟨fun q => match q with | none => Act2.b | some _ => Act2.a,
    (chanceProfileNonempty amd).some, rfl⟩

/-- **The payoff-4 leaf is realized by no policy**: one answer per point sends `a` to the
payoff-0 leaf and `b` to the payoff-1 leaf.
Source: cf-correspondence CF-4 (line 19: "… but not `Image(Fr)`")
Kind: N+
Fidelity: exact -/
theorem amd_payoff4_not_mem_fr_image :
    ((AmdW.sba, (4 : ℚ)) : AmdW × ℚ) ∉ (Fr amd).image := by
  rintro ⟨π, ε, h⟩
  have hπ : π = fun _ => π () := funext fun u => by cases u; rfl
  rw [hπ] at h
  generalize π () = act at h
  cases act
  · have : (Fr amd).outcome (fun _ => Act2.a) ε = (AmdW.sa, 0) := rfl
    rw [this] at h
    exact absurd h (by decide)
  · have : (Fr amd).outcome (fun _ => Act2.b) ε = (AmdW.sbb, 1) := rfl
    rw [this] at h
    exact absurd h (by decide)

/-! ### Two-branch trees over `ℚ` -/

/-- Branch `0` is tails/rain (`true`), branch `1` heads/sun (`false`).
Source: none: infrastructure
Kind: D -/
def coinOf : Fin 2 → Bool := ![true, false]

/-- The observation "the coin shows `true`" at the single point.
Source: none: infrastructure
Kind: D -/
def trueObs : Unit → Finset Bool := fun _ => {true}

/-! ### T3 (ii)∧¬(i): the inert simulation -/

/-- Leaf maps of the inert simulation: tails → real `d`-node with distinct leaves in `O_d`;
heads → a `d`-node off `O_d` whose two edges lead to one and the same leaf.
Source: cf-correspondence CF-11(a) (line 49: "an inert simulation — a `d`-node off `O_d`
whose answer-edges lead to identical subtrees")
Kind: D -/
def inertφ : Fin 2 → Act2 → Bool × ℚ :=
  ![fun act => (true, if act = .a then 1 else 0), fun _ => (false, 0)]

/-- The inert-simulation tree.
Source: cf-correspondence CF-11(a) (line 49)
Kind: D -/
def inertTree : Tree Bool Unit (fun _ => Act2) ℚ := twoBranch FinDistr.fair inertφ

/-- **(ii) without (i)**: `Loc d` of the inert simulation is powerless outside `S_{O_d}` (the
heads row is constant), hence observable, while the heads `d`-node is not subtree-veridical.
The point `d` is consulted on both branches and its tails answers differ (N+).
Source: cf-correspondence CF-11(a) (line 49); mandate T3
Kind: N+
Fidelity: exact -/
theorem inert_powerless_not_veridical :
    PowerlessOutside (Loc () inertTree) (SO trueObs ()) ∧
    Observable2 (Loc () inertTree) (SO trueObs ()) ∧
    ¬ SubtreeVeridical trueObs inertTree ⟨1, none⟩ ∧
    (Loc () inertTree).outcome .a (noOther, (0, fun _ _ => ())) ≠
      (Loc () inertTree).outcome .b (noOther, (0, fun _ _ => ())) := by
  have hT : ∀ act, inertφ 0 act ∈ SO trueObs () := by decide
  have hH : ∀ act, inertφ 1 act ∉ SO trueObs () := by decide
  have hpow : PowerlessOutside (Loc () inertTree) (SO trueObs ()) :=
    (powerlessOutside_loc_twoBranch_iff FinDistr.fair inertφ _ hT hH).mpr fun _ _ => rfl
  refine ⟨hpow, hpow.observable2, ?_, ?_⟩
  · intro h
    have := h ⟨1, ⟨.a, ()⟩⟩ (by decide)
    exact absurd this (by decide)
  · show (Loc () (twoBranch FinDistr.fair inertφ)).outcome .a (noOther, (0, fun _ _ => ())) ≠
      (Loc () (twoBranch FinDistr.fair inertφ)).outcome .b (noOther, (0, fun _ _ => ()))
    rw [loc_twoBranch_outcome, loc_twoBranch_outcome]
    decide

/-! ### T3 (iii)∧¬(ii) and T2(c): the umbrella-mugging -/

/-- Umbrella policies `u, n, u↔r, u↔s` (indices `0..3`): whether the umbrella is taken given the
weather.
Source: post 11 §1.1 (the frame `C₀`); cf-correspondence CF-11(b) (line 49)
Kind: D -/
def umbAt (a : Fin 4) (rain : Bool) : Bool := ![true, false, rain, !rain] a

/-- Leaf maps of the umbrella-mugging: world `(umbrella?, rain?)`, payoff `0`; branch `0`
rain, branch `1` sun, and on both branches the node consults `d`.
Source: cf-correspondence CF-11(b) (line 49: "the `r`-node consults `d` (edges to
`ur, nr, ur, nr`), the `s`-node consults `d` too … (edges to `us, ns, ns, us`)")
Kind: D -/
def umbφ : Fin 2 → Fin 4 → (Bool × Bool) × ℚ :=
  fun i a => ((umbAt a (coinOf i), coinOf i), 0)

/-- The rain observation.
Source: cf-correspondence CF-11(b) (line 49: "`O_d = {rain worlds}`")
Kind: D -/
def rainObs : Unit → Finset (Bool × Bool) := fun _ => {(true, true), (false, true)}

/-- The umbrella-mugging tree.
Source: cf-correspondence CF-11(b) (line 49)
Kind: D -/
def umbTree : Tree (Bool × Bool) Unit (fun _ => Fin 4) ℚ := twoBranch FinDistr.fair umbφ

/-- **(iii) without (ii), and CF-9's converse refuted on a tree**: at `Loc d` of the
umbrella-mugging, `{rain, sun}` is observable (the action set contains the conditional
plans) but the agent is not powerless outside the rain worlds (`u ⋆ sun ≠ n ⋆ sun`), and the
sun node is not subtree-veridical. `Loc d umbTree` is post 11's `C₀` up to the trivial
column factor.
Source: cf-correspondence CF-11(b) (line 49); post 11 §1.1; mandate T2(c), T3
Kind: N+
Fidelity: exact -/
theorem umbrella_observable_not_powerless :
    Observable2 (Loc () umbTree) (SO rainObs ()) ∧
    ¬ PowerlessOutside (Loc () umbTree) (SO rainObs ()) ∧
    ¬ SubtreeVeridical rainObs umbTree ⟨1, none⟩ := by
  have hT : ∀ a, umbφ 0 a ∈ SO rainObs () := by decide
  have hH : ∀ a, umbφ 1 a ∉ SO rainObs () := by decide
  refine ⟨(observable2_loc_twoBranch_iff FinDistr.fair umbφ _ hT hH).mpr (by decide), ?_, ?_⟩
  · intro h
    have := (powerlessOutside_loc_twoBranch_iff FinDistr.fair umbφ _ hT hH).mp h 0 1
    exact absurd this (by decide)
  · intro h
    have := h ⟨1, ⟨0, ()⟩⟩ (by decide)
    exact absurd this (by decide)

/-! ### T9(d): the heads-honest policy-menu mugging -/

/-- Leaf maps of the policy-menu mugging: actions `P, R, P↔T, P↔H` (indices `0..3`); tails
pays `-1, 0, -1, 0`, heads rewards the heads clause `1, 0, 0, 1`.
Source: zoo ZO-8 (line 89: "Rows `(T,H)`: `P(−1,+1)`, `R(0,0)`, `P↔T(−1,0)`, `P↔H(0,+1)`")
Kind: D -/
def menuφ : Fin 2 → Fin 4 → Bool × ℚ :=
  ![fun a => (true, ![-1, 0, -1, 0] a), fun a => (false, ![1, 0, 0, 1] a)]

/-- The policy-menu mugging tree.
Source: zoo ZO-8 (line 89)
Kind: D -/
def menuTree : Tree Bool Unit (fun _ => Fin 4) ℚ := twoBranch FinDistr.fair menuφ

/-- **ZO-8's witness (N+)**: the coin is observable at `Loc d` of the policy-menu mugging,
`Loc d ≃ᵇ Hon d`, the agent is not powerless outside the tails worlds, and the heads node is
not subtree-veridical — the residue (iii) without (ii) and (i), with a genuinely
outcome-relevant simulation.
Source: zoo ZO-8 (line 89); mandate T9(d)
Kind: N+
Fidelity: exact -/
theorem menu_observable_hon_not_powerless :
    Observable2 (Loc () menuTree) (SO trueObs ()) ∧
    (Loc () menuTree ≃ᵇ HonLoc trueObs () menuTree) ∧
    ¬ PowerlessOutside (Loc () menuTree) (SO trueObs ()) ∧
    ¬ SubtreeVeridical trueObs menuTree ⟨1, none⟩ := by
  have hT : ∀ a, menuφ 0 a ∈ SO trueObs () := by decide
  have hH : ∀ a, menuφ 1 a ∉ SO trueObs () := by decide
  have hobs : Observable2 (Loc () menuTree) (SO trueObs ()) :=
    (observable2_loc_twoBranch_iff FinDistr.fair menuφ _ hT hH).mpr (by decide)
  refine ⟨hobs, (observable2_loc_iff_biextEquiv_honLoc trueObs () menuTree
    hobs.columnDetermined).mp hobs, ?_, ?_⟩
  · intro h
    have := (powerlessOutside_loc_twoBranch_iff FinDistr.fair menuφ _ hT hH).mp h 0 1
    exact absurd this (by decide)
  · intro h
    have := h ⟨1, ⟨0, ()⟩⟩ (by decide)
    exact absurd this (by decide)

/-! ### T11(a): Counterfactual Mugging -/

/-- The mugging's leaf maps: `mugWorld1 i a` with payoff `mugPay x y`.
Source: [[decision-problems-v2]] Proposition 6, via `dp-core-tree`'s `mug1`
Kind: D -/
def mugφ (x y : ℚ) : Fin 2 → Act2 → MugW × ℚ :=
  fun i act => (mugWorld1 i act, mugPay x y (mugWorld1 i act))

/-- The catalogue's `mug1 x y` is the two-branch tree of `mugφ x y`, on the nose.
Source: none: infrastructure
Kind: L -/
theorem mug1_eq_twoBranch (x y : ℚ) : mug1 x y = twoBranch FinDistr.fair (mugφ x y) := rfl

theorem mugφ_zero_mem (x y : ℚ) (act : Act2) : mugφ x y 0 act ∈ SO mugObs () := by
  show mugWorld1 0 act ∈ mugObs ()
  cases act <;> decide

theorem mugφ_one_not_mem (x y : ℚ) (act : Act2) : mugφ x y 1 act ∉ SO mugObs () := by
  show mugWorld1 1 act ∉ mugObs ()
  cases act <;> decide

/-- **CF-15 / dp-core-061 / slop Claim 2.1**: at `Loc d` of the mugging `B₁` the coin is
column-determined but **not observable**, for every `x`, `y` — the conditional policy "pay on
tails, refuse on heads" needs a row equal to pay's on tails and refuse's on heads, and the
worlds `(H, ⊥, 1) ≠ (H, ⊥, 0)` already separate them (no positivity of `x`, `y` is needed).
Source: cf-correspondence CF-15 (line 75); fable-slop-notes Claim 2.1 (line 39); mandate
T11(a)
Kind: N+
Fidelity: exact for CF-15 (its worlds record the choice, so its claim holds for all `x`, `y`;
the "`x, y > 0`" was the mandate's wording, not the source's); stronger than Claim 2.1's frame,
whose worlds record only `(coin, payoff)` and whose argument silently needs `x ≠ 0`, `y ≠ 0`
(findings F7) -/
theorem mug1_columnDetermined_not_observable (x y : ℚ) :
    ColumnDetermined (Loc () (mug1 x y)) (SO mugObs ()) ∧
    ¬ Observable2 (Loc () (mug1 x y)) (SO mugObs ()) := by
  constructor
  · show ColumnDetermined (Loc () (twoBranch FinDistr.fair (mugφ x y))) (SO mugObs ())
    intro p a₀ a₁
    obtain ⟨_, ⟨i, _⟩⟩ := p
    rw [loc_twoBranch_outcome, loc_twoBranch_outcome]
    dsimp only
    fin_cases i
    · exact iff_of_true (mugφ_zero_mem x y a₀) (mugφ_zero_mem x y a₁)
    · exact iff_of_false (mugφ_one_not_mem x y a₀) (mugφ_one_not_mem x y a₁)
  · show ¬ Observable2 (Loc () (twoBranch FinDistr.fair (mugφ x y))) (SO mugObs ())
    rw [observable2_loc_twoBranch_iff FinDistr.fair (mugφ x y) _ (mugφ_zero_mem x y)
      (mugφ_one_not_mem x y)]
    intro h
    obtain ⟨act, h0, h1⟩ := h .a .b
    cases act
    · exact absurd (show mugWorld1 1 Act2.a = mugWorld1 1 Act2.b from congrArg Prod.fst h1)
        (by decide)
    · exact absurd (show mugWorld1 0 Act2.b = mugWorld1 0 Act2.a from congrArg Prod.fst h0)
        (by decide)

/-- **The failure is at the simulation node**: `Loc d` of the mugging is not powerless outside
the tails worlds, and the node that is not subtree-veridical is the heads node — the tails
node is.
Source: cf-correspondence CF-15 (line 75: "powerlessness outside `S` fails at the
`H`-column, i.e. exactly at the simulation node")
Kind: N+
Fidelity: exact -/
theorem mug1_not_powerless_heads_not_veridical (x y : ℚ) :
    ¬ PowerlessOutside (Loc () (mug1 x y)) (SO mugObs ()) ∧
    ¬ SubtreeVeridical mugObs (mug1 x y) ⟨1, none⟩ ∧
    SubtreeVeridical mugObs (mug1 x y) ⟨0, none⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · show ¬ PowerlessOutside (Loc () (twoBranch FinDistr.fair (mugφ x y))) (SO mugObs ())
    rw [powerlessOutside_loc_twoBranch_iff FinDistr.fair (mugφ x y) _ (mugφ_zero_mem x y)
      (mugφ_one_not_mem x y)]
    intro h
    exact absurd (show mugWorld1 1 Act2.a = mugWorld1 1 Act2.b from congrArg Prod.fst (h .a .b))
      (by decide)
  · intro h
    have := h ⟨1, ⟨.a, ()⟩⟩ (by
      rw [mem_leavesBelow]
      exact rfl)
    exact absurd (show mugWorld1 1 Act2.a ∈ mugObs () from this) (by decide)
  · rintro ⟨⟨n, hn⟩, act, ⟨⟩⟩ hmem
    rcases n with _ | _ | n
    · show mugWorld1 0 act ∈ mugObs ()
      cases act <;> decide
    · exfalso
      rw [mem_leavesBelow] at hmem
      have : edgeOf (mug1 x y) ⟨0, none⟩ ⟨⟨1, hn⟩, ⟨act, ()⟩⟩ = none := rfl
      rw [this] at hmem
      exact Bool.false_ne_true hmem
    · omega

/-- The decoupled mugging: pay's heads entry replaced by `(H, ⊥, 0)`, so the heads row is
constant.
Source: cf-correspondence CF-15 (line 75: "Deleting Omega's coupling (pay's `H`-entry →
`((H,⊥,0),0)`)")
Kind: D -/
def mugDecφ (x y : ℚ) : Fin 2 → Act2 → MugW × ℚ :=
  ![fun act => mugφ x y 0 act, fun _ => (.hZero, 0)]

/-- **The decoupled mugging is powerless outside the tails worlds, hence observable**: deleting
Omega's coupling inerts the simulation.
Source: cf-correspondence CF-15 (line 75: "makes the rows agree off `S`: powerless outside
`S`, observable")
Kind: N+
Fidelity: exact -/
theorem mugDec_powerless_observable (x y : ℚ) :
    PowerlessOutside (Loc () (twoBranch FinDistr.fair (mugDecφ x y))) (SO mugObs ()) ∧
    Observable2 (Loc () (twoBranch FinDistr.fair (mugDecφ x y))) (SO mugObs ()) := by
  have hpow : PowerlessOutside (Loc () (twoBranch FinDistr.fair (mugDecφ x y))) (SO mugObs ()) :=
    (powerlessOutside_loc_twoBranch_iff FinDistr.fair (mugDecφ x y) _
      (fun act => mugφ_zero_mem x y act) (fun _ => by show MugW.hZero ∉ mugObs (); decide)).mpr
      fun _ _ => rfl
  exact ⟨hpow, hpow.observable2⟩

/-! ### T4(c): look-decide -/

/-- The look-decide tree: root point `true` (look = `a` / leave = `b`); look → a node of point
`false` with `p = a → (opened, 1)`, `q = b → (opened, 0)`; leave → `(closed, 0)`.
Source: cf-correspondence CF-13 (line 59)
Kind: D -/
def lookDecide : Tree Bool Bool (fun _ => Act2) ℚ :=
  .decision true fun
    | .a => .decision false fun
      | .a => .leaf true 1
      | .b => .leaf true 0
    | .b => .leaf false 0

/-- Observations of look-decide: `O_{d'} = ⊤`, `O_d = {opened}`.
Source: cf-correspondence CF-13 (line 59)
Kind: D -/
def lookObs : Bool → Finset Bool := fun p => if p then {true, false} else {true}

/-- **CF-13**: in the global frame `O_d` is not observable (membership is row-dependent: the
leave row lands off `O_d`, the look rows on it), while at `Loc d` it is — by the Local
Theorem, since the unique `d`-node is subtree-veridical. The global frame is the wrong locus
for a mid-tree point.
Source: cf-correspondence CF-13 (line 59); mandate T4(c)
Kind: N+
Fidelity: exact -/
theorem lookDecide_global_not_observable_local_observable :
    ¬ Observable2 (Fr lookDecide) (SO lookObs false) ∧
    Observable2 (Loc false lookDecide) (SO lookObs false) := by
  constructor
  · intro h
    have hcd := h.columnDetermined (chanceProfileNonempty lookDecide).some
      (fun _ => Act2.a) (fun _ => Act2.b)
    have h1 : readout lookDecide
        (runLeaf (fun _ => Act2.a) lookDecide (chanceProfileNonempty lookDecide).some) ∈
          SO lookObs false := by
      show (true : Bool) ∈ lookObs false
      decide
    have h2 := hcd.mp h1
    exact absurd (show (false : Bool) ∈ lookObs false from h2) (by decide)
  · refine observable2_loc_of_subtreeVeridical lookObs lookDecide false ?_
    intro q hq
    rcases q with _ | ⟨a', q'⟩
    · rw [mem_fiber] at hq
      exact absurd hq (by decide)
    · cases a'
      · rcases q' with _ | ⟨c, e⟩
        · rintro ⟨a'', ℓ⟩ hmem
          cases a''
          · obtain ⟨bb, snd⟩ := ℓ
            cases bb
            · obtain ⟨⟩ := snd
              show (true : Bool) ∈ lookObs false
              decide
            · obtain ⟨⟩ := snd
              show (true : Bool) ∈ lookObs false
              decide
          · obtain ⟨⟩ := ℓ
            rw [mem_leavesBelow] at hmem
            exact absurd hmem (by decide)
        · cases c <;> exact e.elim
      · exact q'.elim

/-! ### T5(a): the β-pair -/

/-- The subtree carried by both members of the fiber: the point `d`, then a coin of weight `β`
recorded in the world, payoff `1` after `a` and `0` after `b`.
Source: cf-correspondence CF-14(a) (line 65: "identical subtrees except one interior chance
label")
Kind: D -/
def pairSub (β : FinDistr ℚ (Fin 2)) : Tree Bool Unit (fun _ => Act2) ℚ :=
  .decision () fun act => .chance 2 β fun j => .leaf (coinOf j) (if act = .a then 1 else 0)

/-- The β-pair's shape: a fair root coin routing to two `d`-nodes, the first with an inner
fair coin, the second with inner coin `β₁`.
Source: cf-correspondence CF-14(a) (line 65)
Kind: D -/
def pairTree (β₁ : FinDistr ℚ (Fin 2)) : Tree Bool Unit (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => pairSub (![FinDistr.fair, β₁] i)

/-- **The frame forgets the chance weights**: `Fr (pairTree β₁) = Fr (pairTree β₂)` literally,
for all inner weights (`ChanceProfile` and `runLeaf` never read `β`).
Source: cf-correspondence CF-14(a) (line 65: "`Fr(P) = Fr(P')` identically — the functor
forgets `β`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem fr_pairTree_eq (β₁ β₂ : FinDistr ℚ (Fin 2)) : Fr (pairTree β₁) = Fr (pairTree β₂) := rfl

/-- A coin of weight `1/3`.
Source: cf-correspondence CF-14(a) (line 65: "`β = ½` vs `⅓`")
Kind: D -/
def coinThird : FinDistr ℚ (Fin 2) := FinDistr.coin (1/3) (by norm_num) (by norm_num)

/-- **`P` (both inner coins fair) is strongly fair**: the fiber's two subtrees are equal.
Source: cf-correspondence CF-14(a) (line 65: "`P` fair")
Kind: N+
Fidelity: exact -/
theorem pairTree_fair_stronglyFair : StronglyFair (pairTree FinDistr.fair) := by
  intro d q hq q' hq'
  rcases q with ⟨i, _ | ⟨_, _, e⟩⟩
  · rcases q' with ⟨i', _ | ⟨_, _, e'⟩⟩
    · show LabIso (pairSub (![FinDistr.fair, FinDistr.fair] i))
        (pairSub (![FinDistr.fair, FinDistr.fair] i'))
      fin_cases i <;> fin_cases i' <;> exact LabIso.refl _
    · exact e'.elim
  · exact e.elim

/-- **`P'` (inner coin `⅓` on the second branch) is not strongly fair**: a labelled
isomorphism of the two members would carry the fair inner coin to the `⅓` coin, but no
permutation of `Fin 2` matches the weight `½` with `⅓` or `⅔`.
Source: cf-correspondence CF-14(a) (line 65: "`P'` unfair")
Kind: N+
Fidelity: exact -/
theorem pairTree_third_not_stronglyFair : ¬ StronglyFair (pairTree coinThird) := by
  intro h
  have hiso := h () ⟨0, none⟩ ((mem_fiber _ _ _).mpr rfl) ⟨1, none⟩ ((mem_fiber _ _ _).mpr rfl)
  change LabIso (pairSub FinDistr.fair) (pairSub coinThird) at hiso
  unfold pairSub at hiso
  cases hiso with
  | decision _ _ _ hchild =>
    have h2 := hchild .a
    cases h2 with
    | chance _ _ _ _ σ hβ _ =>
      have h0 := hβ 0
      revert h0
      generalize σ 0 = k
      fin_cases k <;> norm_num [coinThird, FinDistr.coin, FinDistr.fair]

/-- **Fairness is not a function of the frame** (dp-core-063's biconditional refuted in every
reading, headline 3): no predicate `Φ` of frames over `Bool × ℚ` satisfies
`StronglyFair B ↔ Φ (Fr B)` for all trees `B` of the β-pair's signature — `P` and `P'` have
one frame and different fairness.
Source: cf-correspondence CF-14(a) (line 65: "No frame property, observability included, can
be equivalent to strong fairness"); fable-slop-notes Claim 2.2 (line 47, "[guess]"); mandate
T5(a)
Kind: N+
Fidelity: exact (over the fixed signature `Ω = Bool`, `ι = Unit`, `A = Act2`, `K = ℚ`) -/
theorem no_frame_predicate_is_stronglyFair :
    ¬ ∃ Φ : CartesianFrames.Frame (Bool × ℚ) → Prop,
      ∀ B : Tree Bool Unit (fun _ => Act2) ℚ, StronglyFair B ↔ Φ (Fr B) := by
  rintro ⟨Φ, hΦ⟩
  have h1 := (hΦ (pairTree FinDistr.fair)).mp pairTree_fair_stronglyFair
  rw [fr_pairTree_eq FinDistr.fair coinThird] at h1
  exact pairTree_third_not_stronglyFair ((hΦ _).mpr h1)

end Cleanroom.Decision.DpCartesianFrames
