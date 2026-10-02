import Cleanroom.Decision.DpDutchBook.Damascus
import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpCalibration.Basic

/-!
# T5(a): Death in Damascus, the hypothetical-node encoding, and the Definition-15 inconsistency
of a stipulated predictor accuracy about a mixing agent

`didHyp p L c` (the *hypothetical-node* encoding): Death's location is a `d`-node sampled
upstream (a simulation query, answer `s`), Death goes to `s`'s city with skill `p` and to the
other city otherwise (`didLoc s i`), then the live query (`a`); payoff as `didRouted`. Under
Definition 6 the simulation's draw and the live draw are independent draws from the label, so
**Death is right about the live act w.p. `p(q² + (1−q)²) + (1−p)·2q(1−q)`** (`didHyp_accuracy`),
exactly `½` at `q = ½` for every skill, and the two conditional accuracies
`P(loc = stay ∣ stay) = pq + (1−p)(1−q)` and `P(loc = flee ∣ flee) = p(1−q) + (1−p)q` sum to `1`.

**The Definition-15 inconsistency** (`didHyp_makesInconsistent`): the abstract problem
`didAccurateProblem B` — the instantiations on `B` whose state says "Death predicts the live act
with conditional accuracy `> ½` for both acts" — is `MakesInconsistent` (Definition 16, strict
sense, `⊤` at `0`) for every properly mixed label on `didHyp`: no strictly calibrated state can
assert both accuracies, since strict calibration pins them at the tree's values, which sum to
`1`. **The encoding axis** (`didRouted_consistent`): the same problem is `Consistent` on
`didRouted` (routing on the act = draw-keyed) for every `p > ½` at every properly mixed label —
the strictly calibrated state there has `P(loc = a ∣ a) = p + (1−p)·C(d)(a) > ½`.

Not done: the 6′ clause (`Consistent` under `nu'`) — `dp-calibration`'s Definition 15 is a
Definition-6 object and no 6′ calibration predicate exists to state it against.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- Death's city given the simulation's draw `s` and the skill index `i` (`0` = right, `1` = the
other city). Source: dp-sl-2-027; mandate T5(a). Kind: D -/
def didLoc (s : Act2) (i : Fin 2) : Act2 :=
  if i = 0 then s else (match s with | .a => .b | .b => .a)

/-- **Death in Damascus, hypothetical-node encoding**: the simulation query, the skill coin, then
the live query.
Source: dp-sl-2-027 ("Death's location a `d`-node sampled upstream, skill `p`; live query");
mandate T5(a) (`didHyp`)
Kind: D -/
def didHyp (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L c : ℚ) : Tree DidW Unit (fun _ => Act2) ℚ :=
  .decision () fun s =>
    .chance 2 (FinDistr.coin p h0 h1) fun i =>
      .decision () fun a => .leaf (a, didLoc s i) (didPay L c (a, didLoc s i))

/-- The event "Death is at the agent's city". Source: dp-sl-2-027. Kind: D -/
def didRight : Finset DidW := Finset.univ.filter fun w => w.2 = w.1

/-- **The abstract problem "Death predicts the live act with conditional accuracy `> ½`"** on a
tree `B`: the instantiations on `B` whose state at the point satisfies
`½ · P(a) < P(loc = a ∧ a)` for both acts.
Source: dp-sl-2-027 ("the abstract problem 'Death predicts the live act with conditional accuracy
`> ½`'"); [[decision-problems-v2]] §3.2 Definition 14; mandate T5(a)
Kind: D
Fidelity: exact (the accuracy clauses cross-multiplied) -/
def didAccurateProblem (B : Tree DidW Unit (fun _ => Act2) ℚ) :
    AbstractProblem DidW Unit (fun _ => Act2) ℚ :=
  {I | I.B = B ∧ ∀ a : Act2,
    (1 / 2 : ℚ) * (I.s ()).pr (didActEv () a) < (I.s ()).pr (didRight ∩ didActEv () a)}

section hyp

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L c : ℚ) (C : Proc Unit (fun _ => Act2) ℚ)

/-- Sums over the eight leaves of `didHyp`. Source: none: infrastructure. Kind: L -/
theorem didHyp_sum {M : Type} [AddCommMonoid M] (f : (didHyp p h0 h1 L c).Leaves → M) :
    ∑ ℓ, f ℓ = ∑ s : Act2, ∑ i : Fin 2, ∑ a : Act2, f ⟨s, ⟨i, ⟨a, ()⟩⟩⟩ := by
  unfold didHyp at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- `()` is queried on `didHyp`. Source: none: infrastructure. Kind: L -/
theorem didHyp_queried : () ∈ queried (didHyp p h0 h1 L c) := by
  unfold didHyp; simp [queried_decision]

/-- `()` is queried on `didRouted`. Source: none: infrastructure. Kind: L -/
theorem didRouted_queried : () ∈ queried (didRouted p h0 h1 L c) := by
  unfold didRouted; simp [queried_decision]

/-- `ν(act = a) = C(d)(a)` on `didHyp`. Source: none: infrastructure. Kind: L -/
theorem didHyp_nu_act (a : Act2) :
    nu C (didHyp p h0 h1 L c) (didActEv () a) = (C ()).w a := by
  rw [nu_eq_sum, didHyp_sum]
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  have hb : (C ()).w .b = 1 - (C ()).w .a := by linarith
  cases a <;>
    simp [Act2.sum_univ, Fin.sum_univ_two, didHyp, didActEv, didLoc, FinDistr.coin] <;>
    rw [hb] <;> ring

/-- `ν(loc = stay ∧ stay) = q·(pq + (1−p)(1−q))` and `ν(loc = flee ∧ flee) = (1−q)·(p(1−q) + (1−p)q)`
on `didHyp`: the live draw is independent of Death's city.
Source: dp-sl-2-027; mandate T5(a)
Kind: L -/
theorem didHyp_nu_right_act :
    nu C (didHyp p h0 h1 L c) (didRight ∩ didActEv () .a) =
        (C ()).w .a * (p * (C ()).w .a + (1 - p) * (C ()).w .b) ∧
      nu C (didHyp p h0 h1 L c) (didRight ∩ didActEv () .b) =
        (C ()).w .b * (p * (C ()).w .b + (1 - p) * (C ()).w .a) := by
  constructor <;>
  · rw [nu_eq_sum, didHyp_sum]
    simp [Act2.sum_univ, Fin.sum_univ_two, didHyp, didActEv, didRight, didLoc, FinDistr.coin]
    ring

/-- **Death's accuracy about the live act on `didHyp` is `p(q² + (1−q)²) + (1−p)·2q(1−q)`** —
exactly `½` at `q = ½` for every skill.
Source: dp-sl-2-027 ("prove the accuracy identity `p(q² + (1−q)²) + (1−p)·2q(1−q)` on this tree
yourself"); mandate T5(a)
Kind: P
Fidelity: exact -/
theorem didHyp_accuracy :
    nu C (didHyp p h0 h1 L c) didRight =
      p * ((C ()).w .a ^ 2 + (C ()).w .b ^ 2) + (1 - p) * (2 * (C ()).w .a * (C ()).w .b) := by
  rw [nu_eq_sum, didHyp_sum]
  simp [Act2.sum_univ, Fin.sum_univ_two, didHyp, didRight, didLoc, FinDistr.coin]
  ring

/-- At `q = ½` the accuracy is `½` for every skill. Source: dp-sl-2-027. Kind: N+ -/
theorem didHyp_accuracy_half :
    nu (procQ (1/2) (by norm_num) (by norm_num)) (didHyp p h0 h1 L c) didRight = 1 / 2 := by
  rw [didHyp_accuracy]; simp [procQ]; ring

/-- Under strict calibration at `()` with `O = ⊤`, the state's probabilities are the tree's
`ν`. Source: [[decision-problems-v2]] Definition 8 clause 1; none: infrastructure. Kind: L -/
theorem pr_eq_nu_of_strictOC {B : Tree DidW Unit (fun _ => Act2) ℚ} {s : Unit → State DidW ℚ}
    (hcal : StrictOC s didObs C B) (hq : () ∈ queried B) (X : Finset DidW) :
    (s ()).pr X = nu C B X := by
  have h1 : 0 < nu C B (didObs ()) := by rw [didObs, nu_univ]; exact one_pos
  have := (hcal () hq h1).1 X
  rw [didObs, nu_univ, mul_one, Finset.inter_univ] at this
  exact this

/-- **T5(a), the Definition-15 inconsistency**: on `didHyp` the abstract problem "Death predicts
the live act with conditional accuracy `> ½` for both acts" is made inconsistent (Definition 16,
strict sense, `⊤` at `0`) by every properly mixed label — strict calibration pins the two
conditional accuracies at `pq + (1−p)(1−q)` and `p(1−q) + (1−p)q`, which sum to `1`.
Source: dp-sl-2-027 (the headline); mandate T5(a) ("`MakesInconsistent` for every properly mixed
`C` on `didHyp` under Definition 6")
Kind: P
Fidelity: exact (`dp-calibration`'s `MakesInconsistent` at `X = ⊤`, `δ = 0`: no calibrated
instantiation of the problem exists)
Hyps: (a) `0 < q < 1` -/
theorem didHyp_makesInconsistent (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) :
    MakesInconsistent .strict didObs (didAccurateProblem (didHyp p h0 h1 L c)) C Finset.univ 0 := by
  intro I hI hcal
  obtain ⟨hB, hacc⟩ := hI
  exfalso
  rcases I with ⟨B, s⟩
  simp only at hB hacc
  subst hB
  have hcal' : StrictOC s didObs C (didHyp p h0 h1 L c) := hcal
  have hpr := pr_eq_nu_of_strictOC C hcal' (didHyp_queried p h0 h1 L c)
  have ha := hacc .a
  have hb := hacc .b
  rw [hpr, hpr, didHyp_nu_act, (didHyp_nu_right_act p h0 h1 L c C).1] at ha
  rw [hpr, hpr, didHyp_nu_act, (didHyp_nu_right_act p h0 h1 L c C).2] at hb
  have hs := (C ()).sum_one
  rw [Act2.sum_univ] at hs
  -- divide out the positive weights: `½ < pq + (1−p)(1−q)` and `½ < p(1−q) + (1−p)q`, summing to `1`
  have ha' : 1 / 2 < p * (C ()).w .a + (1 - p) * (C ()).w .b := by
    by_contra h
    push_neg at h
    nlinarith
  have hb' : 1 / 2 < p * (C ()).w .b + (1 - p) * (C ()).w .a := by
    by_contra h
    push_neg at h
    nlinarith
  nlinarith

/-- `ν(loc = a ∧ a) = C(d)(a)·(p + (1−p)·C(d)(a))` on `didRouted`.
Source: dp-sl-034; mandate T5(a). Kind: L -/
theorem didRouted_nu_right_act (a : Act2) :
    nu C (didRouted p h0 h1 L c) (didRight ∩ didActEv () a) =
      (C ()).w a * (p + (1 - p) * (C ()).w a) := by
  rw [nu_eq_sum, didRouted_sum]
  cases a <;>
    simp [Act2.sum_univ, didRouted, didChild_zero, didChild_one, didActEv, didRight,
      FinDistr.coin] <;>
    ring

/-- **The encoding axis: the same problem is `Consistent` on `didRouted` for `p > ½`** at every
properly mixed label — the strictly calibrated state has `P(loc = a ∣ a) = p + (1−p)·C(d)(a) > ½`.
Source: dp-sl-2-027 ("`Consistent` on `didRouted` under Definition 6 — the encoding axis");
mandate T5(a)
Kind: P / N+
Fidelity: exact (`dp-calibration`'s `Consistent`, strict sense; the witness instantiation is the
calibrated state)
Hyps: (a) `½ < p`, `0 < q < 1` -/
theorem didRouted_consistent (hp : 1 / 2 < p) (hqa : 0 < (C ()).w .a) (hqb : 0 < (C ()).w .b) :
    Consistent .strict didObs (didAccurateProblem (didRouted p h0 h1 L c)) C := by
  have hO : 0 < nu C (didRouted p h0 h1 L c) (didObs ()) := by rw [didObs, nu_univ]; exact one_pos
  refine ⟨⟨didRouted p h0 h1 L c, fun _ => calibratedState C (didRouted p h0 h1 L c) (didObs ()) hO⟩,
    ⟨rfl, ?_⟩, ?_⟩
  · intro a
    simp only [calibratedState_pr, didObs, nu_univ, Finset.inter_univ, div_one]
    rw [didRouted_nu_right_act, did_nu_act]
    have h1p : 0 ≤ 1 - p := by linarith
    cases a
    · nlinarith [mul_nonneg h1p hqa.le]
    · nlinarith [mul_nonneg h1p hqb.le]
  · show StrictOC _ didObs C (didRouted p h0 h1 L c)
    intro d _
    cases d
    exact strictOCAt_calibratedState didObs C (didRouted p h0 h1 L c) _ () hO rfl

end hyp

end Cleanroom.Decision.DpDutchBook
