import Cleanroom.Decision.DpDutchBook.MsrValues
import Cleanroom.Found.DpCoreTree.Catalogue

/-!
# T7(f): Arntzenius's Yankees–Red Sox tree — the standing hypothesis fails and no procedure is MSR

**The tree** (S19, dp-sl-033; Ahmed–Price Table 1 as restated by the SL run): the game's
winner `g ∈ {Y : 9/10, R : 1/10}`; the perfect announcer is realised by two hypothetical
queries `r_w ∼ C(d_win)`, `r_l ∼ C(d_lose)` and a truth-seeking rule — announce "win" if `r_w`
wins at `g`, else "lose" if `r_l` loses at `g`, else (no truthful option) "win" anyway, the
contrarian convention (equivalently: "win" iff either probe wins at `g`); then the real query
at the announced point, a fresh draw `a ∼ C(d_ann)`. Payoffs: BR (`.a`, bet Red Sox) pays `+2`
on `R`, `−1` on `Y`; BY (`.b`) pays `−2` on `R`, `+1` on `Y`. Worlds `(g, ann, a)`;
`O_d = {ann = d}`; action events read the live bet at the announced point. All over `ℚ`.
`p := C(d_win)(BY)`, `q := C(d_lose)(BY)`.

* **F3′ holds structurally at both points** (`yankees_actRecordingStruct`): the two hypothetical
  nodes are not node-action-veridical, the real node is.
* **The standing hypothesis of C2-7 fails at `d_lose`** (`yankees_hStand_fails_lose`):
  `ν_{C[d_lose ↦ BR]}(O_lose) = 0` whenever the win-point plays BY (S19(iii)); it holds at
  `d_win` for every procedure (`yankees_hStand_win`).
* **The tie curves** (`yankees_tie_win_iff`, `yankees_tie_lose_iff`): `q = (9p−2)/(7p−9)` at
  `d_win`, `q = 9(p−1)/(7p−9)` at `d_lose`; they never meet (`yankees_ties_never_meet`): the
  two signed margins sum to `−7/10` identically.
* **No procedure is D4-approved at both points** (`yankees_no_msrAtD4`, the refutation of
  "MSR always exists" with `msrAtD4_exists` as the surviving neighbour): the closed-form
  tremble-pinned values where the standing hypothesis holds, and at the one profile where it
  fails at `d_lose` — `(BY, BR)`, "lose" never announced — the tremble limit computed from the
  polynomials (`yankees_limitVal_lose_BYBR`: Definition 10 pins the lose-point to BY).
* The constant profiles' values `V(BR, BR) = −7/10`, `V(BY, BY) = 7/10` (`yankees_value_const`).

Not done: the 6′ clause of S19(iii) ("(BR,BR) limit-consistent at `−7/10`"), Told-You-So `d₅`
and matching pennies as further hypothesis-failure examples, T7(g)'s ε-calibration.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- The two decision points of the Yankees tree: the announced-win point and the announced-lose
point. Source: S19 (`d_win`, `d_lose`). Kind: D -/
inductive YPt : Type
  | win
  | lose
  deriving DecidableEq, Fintype

instance : Nonempty YPt := ⟨YPt.win⟩

/-- Worlds `(g, ann, a)`: the winner (`true` = Yankees), the announcement, the live bet.
Source: S19 ("leaf world `(g, ann, a, truthful)`"; truthfulness is a function of the three).
Kind: D -/
abbrev YW : Type := Bool × YPt × Act2

/-- The winner at chance index `i`: index `0` = Yankees (w.p. `9/10`). Source: S19. Kind: D -/
def yG (i : Fin 2) : Bool := if i = 0 then true else false

/-- The bet `b` wins at `g`: BR (`.a`) iff the Red Sox win, BY (`.b`) iff the Yankees win.
Source: S19 (Ahmed–Price Table 1). Kind: D -/
def yWins : Act2 → Bool → Bool
  | .a, g => !g
  | .b, g => g

/-- The announcement: "win" iff either probe wins at `g` — the truth-seeking rule with the
contrarian convention ("win" if `r_w` wins; else "lose" if `r_l` loses; else "win").
Source: S19 ("Told-You-So's contrarian convention"); `threads/L5-scratch/yankees.py`. Kind: D -/
def yAnn (g : Bool) (rw rl : Act2) : YPt :=
  if (yWins rw g || yWins rl g) = true then .win else .lose

/-- Payoffs: BR pays `+2` on `R`, `−1` on `Y`; BY pays `−2` on `R`, `+1` on `Y`.
Source: S19 (Table 1). Kind: D -/
def yPay : Act2 → Bool → ℚ
  | .a, true => -1
  | .a, false => 2
  | .b, true => 1
  | .b, false => -2

/-- **Arntzenius's Yankees–Red Sox tree**: the winner, the two probes, the announcement, the
real query at the announced point.
Source: S19; dp-sl-033; mandate T7(f)
Kind: D
Fidelity: exact (Definition 6, independent redraws; the "truthful" world coordinate is omitted
because it is a function of `(g, ann, a)`) -/
def yankees : Tree YW YPt (fun _ => Act2) ℚ :=
  .chance 2 (FinDistr.coin (9/10) (by norm_num) (by norm_num)) fun i =>
    .decision .win fun rw =>
      .decision .lose fun rl =>
        .decision (yAnn (yG i) rw rl) fun a =>
          .leaf (yG i, yAnn (yG i) rw rl, a) (yPay a (yG i))

/-- `O_d = {ann = d}`. Source: S19. Kind: D -/
def yObs : YPt → Finset YW := fun d => Finset.univ.filter fun w => w.2.1 = d

/-- Action events: the live bet at the announced point. Source: S19. Kind: D -/
def yActEv : (d : YPt) → Act2 → Finset YW := fun d a =>
  Finset.univ.filter fun w => w.2.1 = d ∧ w.2.2 = a

/-- Sums over the sixteen leaves. Source: none: infrastructure. Kind: L -/
theorem yankees_sum {M : Type} [AddCommMonoid M] (f : yankees.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ rw : Act2, ∑ rl : Act2, ∑ a : Act2,
      f ⟨i, ⟨rw, ⟨rl, ⟨a, ()⟩⟩⟩⟩ := by
  unfold yankees at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun rw _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun rl _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `R_win(p, q) := ν(O_win) = (9/10)(p + q − pq) + (1/10)(1 − pq)`. Source: S19 (derived here).
Kind: D -/
def yRwin (p q : ℚ) : ℚ := 9/10 * (p + q - p * q) + 1/10 * (1 - p * q)

/-- `R_lose(p, q) := ν(O_lose) = (9/10)(1 − p)(1 − q) + (1/10)pq`. Source: S19 (derived here).
Kind: D -/
def yRlose (p q : ℚ) : ℚ := 9/10 * ((1 - p) * (1 - q)) + 1/10 * (p * q)

/-- The signed BR-margin at `d_win`: `Q_BR = −(9/10)(p + q − pq) + (2/10)(1 − pq)`; `Q_BY = −Q_BR`.
Source: S19 (derived here). Kind: D -/
def yQwin (p q : ℚ) : ℚ := -(9/10 * (p + q - p * q)) + 2/10 * (1 - p * q)

/-- The signed BR-margin at `d_lose`: `Q_BR = −(9/10)(1 − p)(1 − q) + (2/10)pq`; `Q_BY = −Q_BR`.
Source: S19 (derived here). Kind: D -/
def yQlose (p q : ℚ) : ℚ := -(9/10 * ((1 - p) * (1 - q))) + 2/10 * (p * q)

/-- **The two margins sum to `−7/10` identically** — the algebraic reason the tie curves never
meet. Source: none: derived here (S19's "never meet", explained). Kind: L -/
theorem yQwin_add_yQlose (p q : ℚ) : yQwin p q + yQlose p q = -7/10 := by
  unfold yQwin yQlose; ring

section tree

variable (C : Proc YPt (fun _ => Act2) ℚ)

/-- `ν(O_win) = R_win(p, q)`. Source: S19 (derived). Kind: L -/
theorem yankees_nu_win :
    nu C yankees (yObs .win) = yRwin ((C .win).w .b) ((C .lose).w .b) := by
  rw [nu_eq_sum, yankees_sum]
  have hw := (C .win).sum_one
  rw [Act2.sum_univ] at hw
  have hl := (C .lose).sum_one
  rw [Act2.sum_univ] at hl
  have hwa : (C .win).w .a = 1 - (C .win).w .b := by linarith
  have hla : (C .lose).w .a = 1 - (C .lose).w .b := by linarith
  simp [Act2.sum_univ, yankees, yG, yWins, yAnn, yPay, Fin.sum_univ_two, yObs, FinDistr.coin]
  unfold yRwin; rw [hwa, hla]; ring

/-- `ν(O_lose) = R_lose(p, q)`. Source: S19 (derived). Kind: L -/
theorem yankees_nu_lose :
    nu C yankees (yObs .lose) = yRlose ((C .win).w .b) ((C .lose).w .b) := by
  rw [nu_eq_sum, yankees_sum]
  have hw := (C .win).sum_one
  rw [Act2.sum_univ] at hw
  have hl := (C .lose).sum_one
  rw [Act2.sum_univ] at hl
  have hwa : (C .win).w .a = 1 - (C .win).w .b := by linarith
  have hla : (C .lose).w .a = 1 - (C .lose).w .b := by linarith
  simp [Act2.sum_univ, yankees, yG, yWins, yAnn, yPay, Fin.sum_univ_two, yObs, FinDistr.coin]
  unfold yRlose; rw [hwa, hla]; ring

/-- **The constant profiles' values**: `V(BR, BR) = −7/10`, `V(BY, BY) = 7/10`.
Source: S19(i); dp-sl-033 (i)
Kind: N+
Fidelity: exact -/
theorem yankees_value_const :
    value (Proc.ofFun fun _ => Act2.a) yankees = -7/10 ∧
      value (Proc.ofFun fun _ => Act2.b) yankees = 7/10 := by
  constructor <;>
  · unfold value
    rw [yankees_sum]
    simp [yankees, yG, yWins, yAnn, yPay, Fin.sum_univ_two, FinDistr.coin, Proc.ofFun]
    norm_num

/-- `R_win(p, q) > 0` on the square: the standing hypothesis holds at `d_win` for every label.
Source: S19 (derived). Kind: L -/
theorem yRwin_pos {p q : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 < yRwin p q := by
  unfold yRwin
  have h1 : 0 ≤ p + q - p * q := by nlinarith
  have h2 : 0 ≤ 1 - p * q := by nlinarith
  rcases lt_or_eq_of_le h2 with h2 | h2
  · linarith
  · have hpq : p * q = 1 := by linarith
    have hp : p = 1 := by nlinarith
    have hq : q = 1 := by nlinarith
    subst hp; subst hq; norm_num

/-- **The standing hypothesis holds at `d_win` for every procedure and every deviation**
(`ν_{C[d_win ↦ m]}(O_win) > 0`): Kakutani's hypothesis package of `msrAtD4_exists` is inhabited
at the win-point alone. Source: C2-7's standing hypothesis; S19(iii). Kind: L -/
theorem yankees_hStand_win (m : FinDistr ℚ Act2) :
    0 < nu (C.deviate .win m) yankees (yObs .win) := by
  rw [yankees_nu_win]
  simp only [Proc.deviate_same, Proc.deviate_ne C m (show YPt.lose ≠ YPt.win by decide)]
  have hs := m.sum_one
  rw [Act2.sum_univ] at hs
  have hs' := (C .lose).sum_one
  rw [Act2.sum_univ] at hs'
  exact yRwin_pos (m.nonneg .b) (by linarith [m.nonneg .a]) ((C .lose).nonneg .b)
    (by linarith [(C .lose).nonneg .a])

/-- **The standing hypothesis fails at `d_lose`** (S19(iii), dp-sl-033 (iii)): when the win-point
plays BY, the deviation to BR at the lose-point never hears "lose" —
`ν_{C[d_lose ↦ BR]}(O_lose) = 0`. So Arntzenius's tree lies outside C2-7's hypothesis.
Source: S19(iii) ("`ν_{C[d ↦ δ_BR]}(O_lose) = 0` when the win-point plays BY"); mandate T7(f)
Kind: P
Fidelity: exact
Hyps: (a) `C(d_win)(BY) = 1` -/
theorem yankees_hStand_fails_lose (hp : (C .win).w .b = 1) :
    nu (C.deviate .lose (FinDistr.pure .a)) yankees (yObs .lose) = 0 := by
  rw [yankees_nu_lose]
  simp only [Proc.deviate_same, Proc.deviate_ne C _ (show YPt.win ≠ YPt.lose by decide),
    FinDistr.pure_w]
  unfold yRlose
  simp [hp]

/-- Action events at each point are disjoint. Source: none: infrastructure. Kind: L -/
theorem yankees_disjointActEv (d : YPt) : DisjointActEv yActEv d := by
  intro x y hxy
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [yActEv, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact hxy (hw.2.symm.trans hw'.2)

/-- **F3′ holds structurally at both points**: the real node (below both probes) is
node-action-veridical and subtree-veridical for its announcement; neither hypothetical node is
node-action-veridical (its edge is a probe, the world records the live bet); every leaf whose
announcement is `d` passes exactly one node-action-veridical `d`-node.
Source: S19 (the announcer as two hypothetical queries; F3′ at the real node); mandate T7(f)
Kind: P
Fidelity: exact -/
theorem yankees_actRecordingStruct (d : YPt) : ActRecordingStruct yObs yActEv yankees d := by
  refine ⟨?_, ?_⟩
  · rintro ⟨i, q⟩ hpt hnav
    rcases q with _ | ⟨rw, q'⟩
    · -- the hypothetical win node: leaf `(rw = BR, rl = BY, a = BY)` has edge BR, live BY
      exfalso
      have := hnav ⟨i, .a, .b, .b, ()⟩ .a (by simp [yankees, edgeOf])
      simp [yankees, yActEv] at this
    · rcases q' with _ | ⟨rl, q''⟩
      · -- the hypothetical lose node: leaf `(rl = BR, a = BY)` has edge BR, live BY
        exfalso
        have := hnav ⟨i, rw, .a, .b, ()⟩ .a (by simp [yankees, edgeOf])
        simp [yankees, yActEv] at this
      · rcases q'' with _ | ⟨x, q'''⟩
        · -- the real node: every leaf below carries the node's announcement
          rintro ⟨j, rw', rl', a', ⟨⟩⟩ hℓ
          rw [mem_leavesBelow] at hℓ
          by_cases hj : j = i
          · subst hj
            by_cases hw : rw' = rw
            · subst hw
              by_cases hl : rl' = rl
              · subst hl
                simp [yankees, pt] at hpt
                simp [yankees, yObs, hpt]
              · simp [yankees, edgeOf, hl] at hℓ
            · simp [yankees, edgeOf, hw] at hℓ
          · simp [yankees, hj] at hℓ
        · exact q'''.elim
  · rintro ⟨i, rw, rl, a, ⟨⟩⟩ - hO
    have hann : yAnn (yG i) rw rl = d := by
      simpa [yankees, yObs] using hO
    refine ⟨⟨i, some ⟨rw, some ⟨rl, none⟩⟩⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_dNodesOn]
      exact ⟨by simp [yankees, pt, hann], by simp [yankees, edgeOf]⟩
    · rintro ⟨j, rw', rl', a', ⟨⟩⟩ a'' he
      by_cases hj : j = i
      · subst hj
        by_cases hw : rw' = rw
        · subst hw
          by_cases hl : rl' = rl
          · subst hl
            simp [yankees, edgeOf] at he
            subst he
            simp [yankees, yActEv, pt]
          · simp [yankees, edgeOf, hl] at he
        · simp [yankees, edgeOf, hw] at he
      · simp [yankees, hj] at he
    · rintro ⟨j, q'⟩ ⟨hq, hnav⟩
      rw [mem_dNodesOn] at hq
      obtain ⟨-, hsome⟩ := hq
      rcases q' with _ | ⟨rw', q''⟩
      · exfalso
        have := hnav ⟨j, .a, .b, .b, ()⟩ .a (by simp [yankees, edgeOf])
        simp [yankees, yActEv] at this
      · rcases q'' with _ | ⟨rl', q'''⟩
        · exfalso
          have := hnav ⟨j, rw', .a, .b, ()⟩ .a (by simp [yankees, edgeOf])
          simp [yankees, yActEv] at this
        · rcases q''' with _ | ⟨x', q''''⟩
          · by_cases hj : i = j
            · subst hj
              by_cases hw : rw = rw'
              · subst hw
                by_cases hl : rl = rl'
                · subst hl; rfl
                · simp [yankees, edgeOf, hl] at hsome
              · simp [yankees, edgeOf, hw] at hsome
            · simp [yankees, hj] at hsome
          · exact q''''.elim

/-! ### The tremble-pinned values where the standing hypothesis holds -/

/-- `Q_a(C)` at `d_win`: the one-draw-erased leaf sum over `a ∧ O_win` is `±Q_BR(p, q)`.
Source: S19 (derived here). Kind: L -/
theorem yankees_qSum_win (a : Act2) :
    qSum C .win a yankees (yActEv .win a ∩ yObs .win) =
      if a = .a then yQwin ((C .win).w .b) ((C .lose).w .b)
        else -yQwin ((C .win).w .b) ((C .lose).w .b) := by
  have hw := (C .win).sum_one
  rw [Act2.sum_univ] at hw
  have hl := (C .lose).sum_one
  rw [Act2.sum_univ] at hl
  have hwa : (C .win).w .a = 1 - (C .win).w .b := by linarith
  have hla : (C .lose).w .a = 1 - (C .lose).w .b := by linarith
  unfold qSum reducedWeight worldEv
  rw [Finset.sum_filter, yankees_sum]
  cases a <;>
    simp [Act2.sum_univ, yankees, yG, yWins, yAnn, yPay, Fin.sum_univ_two, yActEv, yObs,
      FinDistr.coin, List.erase_cons] <;>
    unfold yQwin <;> rw [hwa, hla] <;> ring

/-- `Q_a(C)` at `d_lose`: `±Q_BR(p, q)` of the lose-point. Source: S19 (derived here). Kind: L -/
theorem yankees_qSum_lose (a : Act2) :
    qSum C .lose a yankees (yActEv .lose a ∩ yObs .lose) =
      if a = .a then yQlose ((C .win).w .b) ((C .lose).w .b)
        else -yQlose ((C .win).w .b) ((C .lose).w .b) := by
  have hw := (C .win).sum_one
  rw [Act2.sum_univ] at hw
  have hl := (C .lose).sum_one
  rw [Act2.sum_univ] at hl
  have hwa : (C .win).w .a = 1 - (C .win).w .b := by linarith
  have hla : (C .lose).w .a = 1 - (C .lose).w .b := by linarith
  unfold qSum reducedWeight worldEv
  rw [Finset.sum_filter, yankees_sum]
  cases a <;>
    simp [Act2.sum_univ, yankees, yG, yWins, yAnn, yPay, Fin.sum_univ_two, yActEv, yObs,
      FinDistr.coin, List.erase_cons] <;>
    unfold yQlose <;> rw [hwa, hla] <;> ring

/-- **The tremble-pinned act values at `d_win`** at every label `m` (the standing hypothesis holds
there unconditionally): `r3Val m = (±Q_BR(m(BY), q)) / R_win(m(BY), q)`.
Source: S19(iii); mandate T7(f)
Kind: P
Fidelity: exact
Hyps: (a) none (every label `m`, every procedure `C`) -/
theorem yankees_r3Val_win (m : FinDistr ℚ Act2) (a : Act2) :
    r3Val yObs yActEv C yankees .win m a =
      (if a = .a then yQwin (m.w .b) ((C .lose).w .b) else -yQwin (m.w .b) ((C .lose).w .b)) /
        yRwin (m.w .b) ((C .lose).w .b) := by
  rw [r3Val_eq_qSum_div yObs yActEv (yankees_actRecordingStruct .win) (yankees_disjointActEv .win)
    C m a (yankees_hStand_win C m), yankees_qSum_win, yankees_nu_win]
  simp only [Proc.deviate_same, Proc.deviate_ne C m (show YPt.lose ≠ YPt.win by decide)]

/-- **The tremble-pinned act values at `d_lose`** at a label `m` where the standing hypothesis
holds (`R_lose(p, m(BY)) > 0`): `r3Val m = (±Q_BR(p, m(BY))) / R_lose(p, m(BY))`.
Source: S19(iii); mandate T7(f)
Kind: P
Fidelity: exact
Hyps: (a) `0 < R_lose` at `m` -/
theorem yankees_r3Val_lose (m : FinDistr ℚ Act2) (a : Act2)
    (hR : 0 < yRlose ((C .win).w .b) (m.w .b)) :
    r3Val yObs yActEv C yankees .lose m a =
      (if a = .a then yQlose ((C .win).w .b) (m.w .b) else -yQlose ((C .win).w .b) (m.w .b)) /
        yRlose ((C .win).w .b) (m.w .b) := by
  have hR' : 0 < nu (C.deviate .lose m) yankees (yObs .lose) := by
    rw [yankees_nu_lose]
    simpa only [Proc.deviate_same, Proc.deviate_ne C m (show YPt.win ≠ YPt.lose by decide)] using hR
  rw [r3Val_eq_qSum_div yObs yActEv (yankees_actRecordingStruct .lose) (yankees_disjointActEv .lose)
    C m a hR', yankees_qSum_lose, yankees_nu_lose]
  simp only [Proc.deviate_same, Proc.deviate_ne C m (show YPt.win ≠ YPt.lose by decide)]

/-- **D4 at `d_win`, in closed form**: `C(d_win)` is a best response to itself iff
`Q_BR(p, q) ≤ 0` whenever BY is supported and `Q_BR(p, q) ≥ 0` whenever BR is.
Source: S19(iii); mandate T7(f)
Kind: P
Fidelity: exact -/
theorem yankees_msrAtD4_win_iff :
    MsrAtD4 yObs yActEv C yankees .win ↔
      ((0 < (C .win).w .b → yQwin ((C .win).w .b) ((C .lose).w .b) ≤ 0) ∧
        (0 < (C .win).w .a → 0 ≤ yQwin ((C .win).w .b) ((C .lose).w .b))) := by
  have hw := (C .win).sum_one
  rw [Act2.sum_univ] at hw
  have hl := (C .lose).sum_one
  rw [Act2.sum_univ] at hl
  have hR : 0 < yRwin ((C .win).w .b) ((C .lose).w .b) :=
    yRwin_pos ((C .win).nonneg .b) (by linarith [(C .win).nonneg .a]) ((C .lose).nonneg .b)
      (by linarith [(C .lose).nonneg .a])
  unfold MsrAtD4 brSet
  simp only [Set.mem_setOf_eq, yankees_r3Val_win]
  constructor
  · intro h
    refine ⟨fun hb => ?_, fun ha => ?_⟩
    · have := h .b hb .a
      simp only [reduceCtorEq, if_true, if_false] at this
      rw [div_le_div_iff_of_pos_right hR] at this
      linarith
    · have := h .a ha .b
      simp only [reduceCtorEq, if_true, if_false] at this
      rw [div_le_div_iff_of_pos_right hR] at this
      linarith
  · rintro ⟨hb, ha⟩ x hx y
    cases x <;> cases y <;> simp only [reduceCtorEq, if_true, if_false]
    all_goals first
      | exact le_rfl
      | (rw [div_le_div_iff_of_pos_right hR]; linarith [ha hx])
      | (rw [div_le_div_iff_of_pos_right hR]; linarith [hb hx])

/-- **D4 at `d_lose`, in closed form, where the standing hypothesis holds** (`R_lose(p, q) > 0`):
`C(d_lose)` is a best response to itself iff `Q_BR(p, q) ≤ 0` whenever BY is supported and
`Q_BR(p, q) ≥ 0` whenever BR is.
Source: S19(iii); mandate T7(f)
Kind: P
Fidelity: exact
Hyps: (a) `0 < R_lose(p, q)` -/
theorem yankees_msrAtD4_lose_iff (hR : 0 < yRlose ((C .win).w .b) ((C .lose).w .b)) :
    MsrAtD4 yObs yActEv C yankees .lose ↔
      ((0 < (C .lose).w .b → yQlose ((C .win).w .b) ((C .lose).w .b) ≤ 0) ∧
        (0 < (C .lose).w .a → 0 ≤ yQlose ((C .win).w .b) ((C .lose).w .b))) := by
  unfold MsrAtD4 brSet
  simp only [Set.mem_setOf_eq, yankees_r3Val_lose C (C .lose) _ hR]
  constructor
  · intro h
    refine ⟨fun hb => ?_, fun ha => ?_⟩
    · have := h .b hb .a
      simp only [reduceCtorEq, if_true, if_false] at this
      rw [div_le_div_iff_of_pos_right hR] at this
      linarith
    · have := h .a ha .b
      simp only [reduceCtorEq, if_true, if_false] at this
      rw [div_le_div_iff_of_pos_right hR] at this
      linarith
  · rintro ⟨hb, ha⟩ x hx y
    cases x <;> cases y <;> simp only [reduceCtorEq, if_true, if_false]
    all_goals first
      | exact le_rfl
      | (rw [div_le_div_iff_of_pos_right hR]; linarith [ha hx])
      | (rw [div_le_div_iff_of_pos_right hR]; linarith [hb hx])

/-! ### The tie curves -/

/-- **The `d_win` tie curve**: `Q_BR(p, q) = 0 ↔ q = (9p − 2)/(7p − 9)` for `p ≤ 1`.
Source: S19(iii) ("`q = (9p−2)/(7p−9)`"); dp-sl-033; mandate T7(f)
Kind: P
Fidelity: exact -/
theorem yankees_tie_win_iff {p q : ℚ} (hp1 : p ≤ 1) :
    yQwin p q = 0 ↔ q = (9 * p - 2) / (7 * p - 9) := by
  have hne : 7 * p - 9 ≠ 0 := ne_of_lt (by linarith)
  rw [eq_div_iff hne]
  unfold yQwin
  constructor
  · intro h; linear_combination 10 * h
  · intro h; linear_combination (1/10 : ℚ) * h

/-- **The `d_lose` tie curve**: `Q_BR(p, q) = 0 ↔ q = 9(p − 1)/(7p − 9)` for `p ≤ 1`.
Source: S19(iii) ("`q = 9(p−1)/(7p−9)`"); dp-sl-033; mandate T7(f)
Kind: P
Fidelity: exact -/
theorem yankees_tie_lose_iff {p q : ℚ} (hp1 : p ≤ 1) :
    yQlose p q = 0 ↔ q = 9 * (p - 1) / (7 * p - 9) := by
  have hne : 7 * p - 9 ≠ 0 := ne_of_lt (by linarith)
  rw [eq_div_iff hne]
  unfold yQlose
  constructor
  · intro h; linear_combination (-10 : ℚ) * h
  · intro h; linear_combination (-1/10 : ℚ) * h

/-- **The two tie curves never meet** (for any `(p, q)` whatsoever): the margins sum to `−7/10`.
Source: S19(iii) ("the two tie curves … never meet"); dp-sl-033; mandate T7(f)
Kind: P
Fidelity: stronger: on all of `ℚ²`, not only `[0,1]²` -/
theorem yankees_ties_never_meet (p q : ℚ) : ¬ (yQwin p q = 0 ∧ yQlose p q = 0) := by
  rintro ⟨h1, h2⟩
  have := yQwin_add_yQlose p q
  linarith

/-! ### The degenerate profile `(BY, BR)`: "lose" is never announced -/

/-- `limitVal = c` when `payPoly = C c · nuPoly` as polynomials and `nuPoly ≠ 0`.
Source: none: infrastructure. Kind: L -/
theorem limitVal_eq_of_payPoly_eq_C_mul {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
    [∀ d, Nonempty (acts d)] {C : Proc ι acts K} {B : Tree Ω ι acts K} {Y : Finset Ω}
    (hne : nuPoly C B Y ≠ 0) (c : K) (h : payPoly C B Y = Polynomial.C c * nuPoly C B Y) :
    limitVal C B Y = c := by
  unfold limitVal
  rw [h, Polynomial.coeff_C_mul]
  have htc : (nuPoly C B Y).coeff (nuPoly C B Y).natTrailingDegree ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hne
  field_simp

/-- **The tremble limit at `d_lose` for the profile `(BY, BR)`**, where "lose" is never announced
(the standing hypothesis fails, `yankees_hStand_fails_lose`): Definition 10's limit values are
`(−7/10, 7/10)` — the trembled announcer hears "lose" only through the trembles, where the
Yankees still win w.p. `9/10`, so the lose-point is pinned to BY while the profile plays BR.
Source: S19(iii) ("(BY,BR) passes strictly only because 'lose' is never announced, which
Definition 10 pins to BY"); `yankees.py` §3; mandate T7(f)
Kind: P
Fidelity: exact (algebraic `limitVal`)
Hyps: (a) `C(d_win)(BY) = 1`, `C(d_lose)(BY) = 0` -/
theorem yankees_limitVal_lose_BYBR (hp : (C .win).w .b = 1) (hq : (C .lose).w .b = 0) :
    limitVal C yankees (yActEv .lose .a ∩ yObs .lose) = -7/10 ∧
      limitVal C yankees (yActEv .lose .b ∩ yObs .lose) = 7/10 := by
  have hw := (C .win).sum_one
  rw [Act2.sum_univ] at hw
  have hl := (C .lose).sum_one
  rw [Act2.sum_univ] at hl
  have hwa : (C .win).w .a = 0 := by linarith
  have hla : (C .lose).w .a = 1 := by linarith
  have hne : ∀ x : Act2, nuPoly C yankees (yActEv .lose x ∩ yObs .lose) ≠ 0 := by
    intro x
    rw [nuPoly_ne_zero_iff]
    refine ⟨⟨0, .a, .a, x, ()⟩, ?_, ?_⟩
    · change (yG 0, yAnn (yG 0) .a .a, x) ∈ yActEv .lose x ∩ yObs .lose
      simp [yActEv, yObs, yG, yAnn, yWins]
    · change 0 < (FinDistr.coin (9/10) (by norm_num) (by norm_num)).w 0 * 1
      simp [FinDistr.coin]
  constructor
  · refine limitVal_eq_of_payPoly_eq_C_mul (hne .a) _ ?_
    unfold payPoly nuPoly worldEv
    rw [Finset.sum_filter, Finset.sum_filter, yankees_sum, yankees_sum]
    apply Polynomial.funext
    intro r
    simp [Act2.sum_univ, Fin.sum_univ_two, yankees, yG, yWins, yAnn, yPay, yActEv, yObs,
      FinDistr.coin, leafLawPoly, trembleW, hp, hq, hwa, hla]
    ring
  · refine limitVal_eq_of_payPoly_eq_C_mul (hne .b) _ ?_
    unfold payPoly nuPoly worldEv
    rw [Finset.sum_filter, Finset.sum_filter, yankees_sum, yankees_sum]
    apply Polynomial.funext
    intro r
    simp [Act2.sum_univ, Fin.sum_univ_two, yankees, yG, yWins, yAnn, yPay, yActEv, yObs,
      FinDistr.coin, leafLawPoly, trembleW, hp, hq, hwa, hla]
    ring

/-! ### The headline -/

/-- The arithmetic core: the two closed-form D4 conditions (the lose-point's where its standing
hypothesis holds) are jointly satisfiable only at `(p, q) = (1, 0)`.
Source: S19(iii) (derived here). Kind: L -/
theorem yankees_core {p q : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hwin : (0 < p → yQwin p q ≤ 0) ∧ (0 < 1 - p → 0 ≤ yQwin p q))
    (hlose : 0 < yRlose p q → (0 < q → yQlose p q ≤ 0) ∧ (0 < 1 - q → 0 ≤ yQlose p q)) :
    p = 1 ∧ q = 0 := by
  have hsum := yQwin_add_yQlose p q
  rcases lt_or_eq_of_le hp1 with hplt | hpeq
  · exfalso
    have hQw : 0 ≤ yQwin p q := hwin.2 (by linarith)
    rcases lt_or_eq_of_le hq1 with hqlt | hqeq
    · have hR : 0 < yRlose p q := by
        unfold yRlose
        have h1 := mul_pos (sub_pos.2 hplt) (sub_pos.2 hqlt)
        have h2 := mul_nonneg hp0 hq0
        linarith
      have := (hlose hR).2 (by linarith)
      linarith
    · subst hqeq
      unfold yQwin at hQw
      linarith
  · subst hpeq
    rcases lt_or_eq_of_le hq0 with hqpos | hqzero
    · exfalso
      have hR : 0 < yRlose 1 q := by unfold yRlose; linarith
      have := (hlose hR).1 hqpos
      unfold yQlose at this
      linarith
    · exact ⟨rfl, hqzero.symm⟩

/-- **No procedure is D4-approved at both points of Arntzenius's Yankees tree** — the MSR set is
empty, pure or mixed, under Definition 6: where the standing hypothesis holds the two closed-form
conditions force `(p, q) = (1, 0)` (the tie curves never meet, and every other corner fails at
one point), and at `(BY, BR)` — the one profile where the hypothesis fails at `d_lose` — the
tremble limit pins the lose-point to BY while it plays BR. The naive reading "MSR always exists"
is refuted; the surviving neighbour is `msrAtD4_exists` (existence at a point under the standing
hypothesis), which does apply at `d_win` (`yankees_hStand_win`).
Source: S19(iii) ("the MSR set is empty, pure or mixed"); dp-sl-033 (iii); C2-7's standing
hypothesis; mandate T7(f)
Kind: P
Fidelity: exact (D4 at each point, `MsrAtD4`; the limit grade's calibration clauses beyond the
act values are not modelled — `dp-calib-limits` owns `MSRAt`) -/
theorem yankees_no_msrAtD4 :
    ¬ (MsrAtD4 yObs yActEv C yankees .win ∧ MsrAtD4 yObs yActEv C yankees .lose) := by
  rintro ⟨hwin, hlose⟩
  have hw := (C .win).sum_one
  rw [Act2.sum_univ] at hw
  have hl := (C .lose).sum_one
  rw [Act2.sum_univ] at hl
  have hwa : (C .win).w .a = 1 - (C .win).w .b := by linarith
  have hla : (C .lose).w .a = 1 - (C .lose).w .b := by linarith
  rw [yankees_msrAtD4_win_iff, hwa] at hwin
  obtain ⟨hp1, hq0⟩ := yankees_core ((C .win).nonneg .b) (by linarith [(C .win).nonneg .a])
    ((C .lose).nonneg .b) (by linarith [(C .lose).nonneg .a]) hwin
    (fun hR => by rw [yankees_msrAtD4_lose_iff C hR, hla] at hlose; exact hlose)
  obtain ⟨h1, h2⟩ := yankees_limitVal_lose_BYBR C hp1 hq0
  unfold MsrAtD4 brSet at hlose
  simp only [Set.mem_setOf_eq, r3Val, Proc.deviate_self] at hlose
  have := hlose .a (by rw [hla, hq0]; norm_num) .b
  rw [h1, h2] at this
  norm_num at this

/-- **No deterministic profile is D4-approved at both points** (the four profiles of S19(iii)):
the instance of `yankees_no_msrAtD4` at `ofFun π`.
Source: S19(iii) ("under Definition 6 no deterministic profile is consistent"); mandate T7(f)
Kind: L -/
theorem yankees_det_not_msrAtD4 (π : YPt → Act2) :
    ¬ (MsrAtD4 yObs yActEv (Proc.ofFun π) yankees .win ∧
        MsrAtD4 yObs yActEv (Proc.ofFun π) yankees .lose) :=
  yankees_no_msrAtD4 _

end tree

end Cleanroom.Decision.DpDutchBook
