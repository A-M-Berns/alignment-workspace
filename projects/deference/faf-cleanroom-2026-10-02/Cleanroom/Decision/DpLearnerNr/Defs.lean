import Cleanroom.Decision.DpCalibration.Defs
import Cleanroom.Found.DpCoreTree.Catalogue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# `dp-learner-nr`: definitions of record — the act-level marginal formula (D2)

The marginal formula `cf(a) = ∑_w P(w) E(a, w)` of [[non-responsiveness]] (NR1) and
[[marginal-formula-learner]], over a `FinDistr` marginal on a finite exogenous type `W` and a
response table `E`. The pushforward of a distribution along a coordinate (`pushDistr`), the
Bernoulli marginal on `Bool` (`boolDistr`), and the troll's stated response table
(`trollE`: `−10` on `(cross, incon)`, `10` on `(cross, ¬incon)`, `0` on `stay`), with the
closed form `cf(cross) = 10 − 20·P(incon)`.

Mandate: [[dp-learner-nr-mandate]] D2, target 1(b).
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Cleanroom.Decision.DpCalibration Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **D2 — the act-level marginal formula** `cf(a) := ∑_w P(w) · E(a, w)`: a function of the
marginal `P` over the designated exogenous coordinates `w` and of the response table `E`, never
of act-conditionals `P(· | a)`.
Source: [[non-responsiveness]] "NR1 (formula-level)" (`cf(a) = Σ_w P(w) E(a, w)`);
[[marginal-formula-learner]] "The act-level agent"; [[dp-learner-nr-mandate]] D2
Kind: D
Fidelity: exact (the response function `E` is a table of values, i.e. the mean payoff per cell;
the note's `E` is a law per cell — disclosed in D4) -/
def cfMarginal {W A : Type} [Fintype W] (P : FinDistr K W) (E : A → W → K) (a : A) : K :=
  ∑ w, P.w w * E a w

/-- The pushforward of a distribution along a map `f : Ω → E` (the marginal of `P` on the
coordinate `f`).
Source: none: infrastructure
Kind: D -/
def pushDistr {Ω E : Type} [Fintype Ω] [Fintype E] [DecidableEq E] (P : FinDistr K Ω)
    (f : Ω → E) : FinDistr K E where
  w e := ∑ ω ∈ univ.filter (fun ω => f ω = e), P.w ω
  nonneg _ := sum_nonneg fun ω _ => P.nonneg ω
  sum_one := by rw [Finset.sum_fiberwise]; exact P.sum_one

/-- The weight of the pushforward is the probability of the fiber.
Source: none: infrastructure
Kind: L -/
theorem pushDistr_w {Ω E : Type} [Fintype Ω] [Fintype E] [DecidableEq E] (P : FinDistr K Ω)
    (f : Ω → E) (e : E) : (pushDistr P f).w e = probOf P (univ.filter fun ω => f ω = e) := rfl

/-- The Bernoulli marginal on `Bool` with `P(true) = θ`.
Source: none: infrastructure (the one-coordinate exogenous marginal `P₀(□⊥) = θ`)
Kind: D -/
def boolDistr (θ : K) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : FinDistr K Bool where
  w b := if b then θ else 1 - θ
  nonneg b := by cases b <;> simp <;> linarith
  sum_one := by rw [Fintype.sum_bool]; simp

/-- Weights of the Bernoulli marginal. Source: none: infrastructure. Kind: L -/
@[simp] theorem boolDistr_w (θ : K) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (b : Bool) :
    (boolDistr θ h0 h1).w b = if b then θ else 1 - θ := rfl

/-- **The troll's stated response table** over the exogenous coordinate `incon : Bool`:
`E(cross, incon) = −10`, `E(cross, ¬incon) = 10`, `E(stay, ·) = 0` (`Act2.a` = cross,
`Act2.b` = stay).
Source: [[two-lesions-doc-2026-09-18]] §7 Proposition 10 ("crosses iff `10 − 20·P₀(□⊥) > 0`");
[[dp-learner-nr-mandate]] target 1(b)
Kind: D -/
def trollE : Act2 → Bool → K
  | .a, true => -10
  | .a, false => 10
  | .b, _ => 0

/-- `cf(cross) = 10 − 20·P(incon)` under the troll's table, for every marginal on `Bool`.
Source: [[two-lesions-doc-2026-09-18]] §7 Proposition 10; [[dp-learner-nr-mandate]] target 1(b)
Kind: L -/
theorem cfMarginal_trollE_cross (P : FinDistr K Bool) :
    cfMarginal P trollE Act2.a = 10 - 20 * P.w true := by
  have h := P.sum_one
  rw [Fintype.sum_bool] at h
  simp only [cfMarginal, Fintype.sum_bool, trollE]
  linear_combination (10 : K) * h

/-- `cf(stay) = 0` under the troll's table. Source: none: infrastructure. Kind: L -/
theorem cfMarginal_trollE_stay (P : FinDistr K Bool) : cfMarginal P trollE Act2.b = 0 := by
  simp [cfMarginal, trollE]

/-- **The NR1 rule in closed form**: the marginal formula prefers crossing iff `P(incon) < ½`.
Source: [[two-lesions-doc-2026-09-18]] §7 Proposition 10 ("crosses iff `10 − 20·P₀(□⊥) > 0`");
[[dp-learner-nr-mandate]] target 1(b) ("prove this equivalence first")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem cfMarginal_trollE_cross_pos_iff (P : FinDistr K Bool) :
    cfMarginal P trollE Act2.b < cfMarginal P trollE Act2.a ↔ P.w true < 1 / 2 := by
  rw [cfMarginal_trollE_cross, cfMarginal_trollE_stay]
  constructor <;> intro h <;> linarith

/-- The fallible-troll value: with the troll firing on crossing with probability `ζ` (an
exogenous coordinate), `cf(cross) = 10(1 − 2ζ)`.
Source: [[policy-level-fdt-learner]] §2.6 ("`E(cross) → 10(1 − 2ζ)`"); [[dp-learner-nr-mandate]] target 5(d)
Kind: L -/
theorem cfMarginal_trollE_bool (ζ : K) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) :
    cfMarginal (boolDistr ζ h0 h1) trollE Act2.a = 10 * (1 - 2 * ζ) := by
  rw [cfMarginal_trollE_cross]; simp; ring

end Cleanroom.Decision.DpLearnerNr
