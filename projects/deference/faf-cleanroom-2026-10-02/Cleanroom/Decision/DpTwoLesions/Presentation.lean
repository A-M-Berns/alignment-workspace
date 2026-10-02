import Cleanroom.Decision.DpTwoLesions.Defs

/-!
# T2 — Definition 1 and "the basic argument proves too much"

Abstract, no tree: a *presentation* is a distribution over `(act, outcome)` pairs with a
utility; a *situation* assigns to each agent the distribution its conduct produces; a
presentation is *calibrated* for an agent when its distribution is the situation's. The
theorem-let: if the situation is degenerate on one act (the agent never takes the others) and
the presentation gives every act positive mass, with at least two acts, the presentation is
not calibrated — so under the unamended requirement every problem whose presentation offers a
forgone act is illegitimate (Newcomb, XOR Blackmail, Troll Bridge included). Kind P but
trivial, as the mandate says: the point is scope. A duplicate of v2 Remark 3.6 (dp-core-011).
Serves [[dp-two-lesions-mandate]] T2 (dp-core-071).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Definition 1 (presentation)**: a distribution over act–outcome pairs and a utility.
Source: [[two-lesions-doc-2026-09-18]] §2 Definition 1
Kind: D
Fidelity: exact (finite acts and outcomes) -/
structure Presentation (acts out : Type) [Fintype acts] [Fintype out]
    (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The distribution `D` over `(act, outcome)`. -/
  D : FinDistr K (acts × out)
  /-- The utility. -/
  u : acts → out → K

/-- **A situation**: the distribution over `(act, outcome)` that each agent's conduct produces.
Source: [[two-lesions-doc-2026-09-18]] §2 ("the situation `S`")
Kind: D -/
def Situation (agent acts out : Type) [Fintype acts] [Fintype out] (K : Type) [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] : Type :=
  agent → FinDistr K (acts × out)

/-- **Calibration**: the presentation's distribution is the one the agent's conduct produces.
Source: [[two-lesions-doc-2026-09-18]] §2 ("calibrated for `α`")
Kind: D
Fidelity: exact -/
def Calibrated {agent acts out : Type} [Fintype acts] [Fintype out]
    (D : FinDistr K (acts × out)) (S : Situation agent acts out K) (a : agent) : Prop :=
  D = S a

/-- The marginal mass of an act. Source: none: infrastructure. Kind: D -/
def actMass {acts out : Type} [Fintype acts] [Fintype out] (D : FinDistr K (acts × out))
    (b : acts) : K :=
  ∑ o, D.w (b, o)

/-- **"The basic argument proves too much"**: if the agent's conduct is degenerate on one act
`a*` and the presentation gives every act positive mass, with at least two acts, the
presentation is not calibrated — the agent's record contains no instance of a forgone act.
Source: [[two-lesions-doc-2026-09-18]] §2 ("the basic argument proves too much"); v2 Remark 3.6
(dp-core-011)
Kind: P (trivial; the point is scope)
Fidelity: exact
Hyps: none -/
theorem not_calibrated_of_degenerate {agent acts out : Type} [Fintype acts] [Fintype out]
    [DecidableEq acts] (D : FinDistr K (acts × out)) (S : Situation agent acts out K)
    (a : agent) (aStar : acts) (hdeg : ∀ p : acts × out, p.1 ≠ aStar → (S a).w p = 0)
    (hD : ∀ b, 0 < actMass D b) (hcard : 2 ≤ Fintype.card acts) :
    ¬ Calibrated D S a := by
  intro hcal
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega) aStar
  have h1 := hD b
  have h2 : actMass (S a) b = 0 := by
    unfold actMass
    exact Finset.sum_eq_zero fun o _ => hdeg (b, o) hb
  unfold Calibrated at hcal
  rw [hcal] at h1
  linarith

/-- Scope witness (N−, as the mandate grades it): two acts, an agent that always takes the
first, a presentation that gives both acts mass `½`.
Source: [[two-lesions-doc-2026-09-18]] §2
Kind: N− -/
theorem not_calibrated_act2 :
    ∃ (D : FinDistr ℚ (Bool × Unit)) (S : Situation Unit Bool Unit ℚ),
      ¬ Calibrated D S () := by
  let D : FinDistr ℚ (Bool × Unit) :=
    ⟨fun _ => 1/2, fun _ => by norm_num,
      by simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_unique]; norm_num⟩
  let S : Situation Unit Bool Unit ℚ := fun _ =>
    ⟨fun p => if p.1 = true then 1 else 0, fun p => by split_ifs <;> norm_num,
      by simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_unique]; norm_num⟩
  refine ⟨D, S, not_calibrated_of_degenerate D S () true ?_ ?_ ?_⟩
  · intro p hp
    show (if p.1 = true then (1 : ℚ) else 0) = 0
    rw [if_neg hp]
  · intro b
    show 0 < ∑ _o : Unit, (1/2 : ℚ)
    norm_num [Fintype.sum_unique]
  · simp

end Cleanroom.Decision.DpTwoLesions
