import Cleanroom.Corrigibility.LegitNegStatic.Proposals

/-!
# Readouts R2/R3, ratifiability, and the R2-S1 lemma

Package `legit-neg-static`, target 4. Sources: `clusters/B/fixtures/model.py:163-196`
(`R2_scores`, `R2_ratifiable`, `R2_ref`), `clusters/C/fixtures/model.py:105-136` (`r2`,
`ratifiable`), pinned by [[corr-legit-neg-2-inventory]] item 2-004 and
[[corr-legit-neg-inventory]] item 003.

R2 (realized-terminal readout): the realized action `a*` fixes the terminal and every option
`c` is scored there. As a choice rule R2 is circular; its completion is **ratifiability**: `a*`
is admissible iff it maximises the score vector its own selection produces. The ratifiable set
is a `Finset` that may be empty or plural — existence is never assumed (item 2-013 exhibits
empty, plural and mixed cases downstream).
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- R2 menu scores seen from the realized action `a*`, P1 form:
`∑ s, π s · [leg s a*] · V s a* c` (`model.py:163-175`).
Source: [[corr-legit-neg-2-inventory]] item 2-004
Kind: D
Fidelity: exact -/
def R2scores (V : MenuVec S A) (astar c : A) : ℚ :=
  ∑ s, P.prior s * ind (P.leg s astar) * V s astar c

/-- R2 menu scores, P2 form: divided by `P(L | a*)`, `none` at `0` (exclusion convention).
Source: [[corr-legit-neg-2-inventory]] item 2-004
Kind: D
Fidelity: exact -/
def R2scoresP2 (V : MenuVec S A) (astar c : A) : Option ℚ :=
  if P.PL astar = 0 then none else some (P.R2scores V astar c / P.PL astar)

/-- R2 menu scores, P3 form (C `model.py:112-113`): the legitimate part plus `λ` times the void
part `∑ s, π s · [¬leg s a*] · W s a* c`.
Source: [[corr-legit-neg-2-inventory]] item 2-004
Kind: D
Fidelity: exact -/
def R2scoresP3 (Wg : MenuVec S A) (lam : ℚ) (V : MenuVec S A) (astar c : A) : ℚ :=
  P.R2scores V astar c + lam * ∑ s, P.prior s * ind (!P.leg s astar) * Wg s astar c

/-- R2 menu scores, P4b form (C `model.py:116-118`).
Source: [[corr-legit-neg-2-inventory]] item 2-004
Kind: D
Fidelity: exact -/
def R2scoresP4b (Wg : MenuVec S A) (κ κ' : ℚ) (V : MenuVec S A) (astar c : A) : ℚ :=
  κ * P.PL astar + (1 - κ) * P.R2scores V astar c
    + κ' * ∑ s, P.prior s * ind (!P.leg s astar) * Wg s astar c

/-- R2 menu scores, P5 form (C `model.py:119-125`): `none` at `P(L | a*) = 0`.
Source: [[corr-legit-neg-2-inventory]] item 2-004
Kind: D
Fidelity: exact -/
def R2scoresP5 (K V : MenuVec S A) (astar c : A) : Option ℚ :=
  if P.PL astar = 0 then none
  else some (P.R2scores V astar c
    + (1 - P.PL astar) * (∑ s, P.prior s * ind (P.leg s astar) * K s astar c) / P.PL astar)

open Classical in
/-- The R2-ratifiable set under P1: `{a | a ∈ argmax (R2scores V a)}` — a fixed-point
condition, not a selection rule; may be empty or plural (`model.py:178-190`).
Source: [[corr-legit-neg-2-inventory]] item 2-004; [[corr-legit-neg-inventory]] item 026
Kind: D
Fidelity: exact -/
noncomputable def ratifiable (V : MenuVec S A) : Finset A :=
  univ.filter fun a => a ∈ argmax (P.R2scores V a)

/-- `mem_ratifiable`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mem_ratifiable {V : MenuVec S A} {a : A} :
    a ∈ P.ratifiable V ↔ ∀ b, P.R2scores V a b ≤ P.R2scores V a a := by
  simp [ratifiable, mem_argmax]

open Classical in
/-- The R2-ratifiable set under P2 (exclusion convention: an action with `P(L | a) = 0` has no
defined menu scores and is not ratifiable; B reports it in a separate `undefined` set).
Source: [[corr-legit-neg-2-inventory]] item 2-004
Kind: D
Fidelity: exact -/
noncomputable def ratifiableP2 (V : MenuVec S A) : Finset A :=
  univ.filter fun a => a ∈ argmaxOpt (P.R2scoresP2 V a)

/-- R2-ref: the menu ranking read from a fixed reference terminal `aref` (a counterfactual
evaluator when `aref` is not the action taken; `model.py:193-196`).
Source: [[corr-legit-neg-2-inventory]] item 2-004
Kind: D
Fidelity: exact -/
def R2ref (V : MenuVec S A) (aref : A) : A → ℚ := P.R2scores V aref

/-- `SelectionBlind P V`: sealed legitimacy *and* a selection-independent vector (the
workspace's A2 in finite shadow; item 2-030). Strictly stronger than `Sealed`: R1 = R2 needs
both, not just `Sealed` (item 003's "trivially under R3" needs this predicate).
Source: [[corr-legit-neg-2-inventory]] item 2-030
Kind: D
Fidelity: exact -/
def SelectionBlind (V : MenuVec S A) : Prop := P.Sealed ∧ ∀ s a a' c, V s a c = V s a' c

/-- The diagonal of R2 is R1: `R2scores V a a = P1 V a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma R2scores_diag (V : MenuVec S A) (a : A) : P.R2scores V a a = P.P1 V a := rfl

/-- **Lemma (i)** (item 2-030's selection-blindness lemma): under `SelectionBlind`, every
option's R2 score from any realized action is its R1 score `P1 V c` — R1, R2 and R3 coincide.
Source: [[corr-legit-neg-2-inventory]] item 2-030; NEGATIVES A §0 ("with A2, R1 and R2 coincide")
Kind: L
Fidelity: exact -/
theorem R2scores_eq_P1_of_SelectionBlind {V : MenuVec S A} (h : P.SelectionBlind V)
    (astar c : A) : P.R2scores V astar c = P.P1 V c := by
  unfold R2scores P1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [h.1 s astar c, h.2 s astar c c]

/-- Under `SelectionBlind` the ratifiable set is `argmax P1`: selection-free, and non-empty
when the menu is.
Source: [[corr-legit-neg-2-inventory]] item 2-030
Kind: L
Fidelity: exact -/
theorem ratifiable_eq_argmax_of_SelectionBlind {V : MenuVec S A} (h : P.SelectionBlind V) :
    P.ratifiable V = argmax (P.P1 V) := by
  ext a
  simp only [mem_ratifiable, mem_argmax, P.R2scores_eq_P1_of_SelectionBlind h]

/-- `ratifiable_nonempty_of_SelectionBlind`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ratifiable_nonempty_of_SelectionBlind [Nonempty A] {V : MenuVec S A}
    (h : P.SelectionBlind V) : (P.ratifiable V).Nonempty := by
  rw [P.ratifiable_eq_argmax_of_SelectionBlind h]; exact argmax_nonempty _

/-- **Lemma (ii), the load-bearing R2-S1 lemma.** If `a*` is legitimate in every state, then
under S1 with *sighted evaluators* (S1 prices void terminals off-diagonal, `Scorings.lean`),
the R2 scores from `a*` are the standard `H` on the whole menu.
Source: [[corr-legit-neg-2-inventory]] item 2-004 (from B14/B17)
Kind: L
Fidelity: exact; true *because* S1 prices void terminals (finding 1); fails under `blindImpute`
and when `a*` voids somewhere (`ToyWitnesses.lean`) -/
theorem R2scores_S1_eq_H_of_allLeg (astar : A) (h : ∀ s, P.leg s astar = true) (c : A) :
    P.R2scores (S1 P.u) astar c = P.H c := by
  unfold R2scores H W EU
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [h s]

/-- A fully legitimate action is R2-S1-ratifiable iff it is `H`-optimal (sighted evaluators).
Source: [[corr-legit-neg-2-inventory]] item 2-004
Kind: L
Fidelity: exact (see `R2scores_S1_eq_H_of_allLeg`) -/
theorem mem_ratifiable_S1_iff_of_allLeg (astar : A) (h : ∀ s, P.leg s astar = true) :
    astar ∈ P.ratifiable (S1 P.u) ↔ astar ∈ argmax P.H := by
  simp only [mem_ratifiable, mem_argmax, P.R2scores_S1_eq_H_of_allLeg astar h]

/-- R2-ref from a fully legitimate reference action *is* `H` (B17's "R2-ref from `a₀` = H").
Source: [[corr-legit-neg-2-inventory]] item 2-004
Kind: L
Fidelity: exact (sighted evaluators) -/
theorem R2ref_S1_eq_H_of_allLeg (aref : A) (h : ∀ s, P.leg s aref = true) :
    P.R2ref (S1 P.u) aref = P.H :=
  funext fun c => P.R2scores_S1_eq_H_of_allLeg aref h c

end Problem

end Cleanroom.Corrigibility.LegitNegStatic
