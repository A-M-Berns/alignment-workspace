import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# T10 — The self-counterfactual witness: Value's inequality true, its reading false

Package `def-lattice-arrows`, file 12. v2 §8's *Witness* paragraph (root-deference-2-012), in
a finite two-action model: an option's payoff may depend on the *route* by which it is
reached (committed to directly, or reached by deferral). The theorem `Value` compares
expectations on the road taken (`defer`); the gloss "`E(O^i)` is the value of committing to
`O^i`" reads them as commit payoffs. The two agree exactly when the payoffs are
act-independent (`ActIndependent`); the witness menu violates it, satisfies Value's inequality
on the taken route, and has the committed payoff strictly larger.

ATTRIBUTION: the paragraph paraphrased is v2's own (`deference-in-logical-induction-v2.md`
ll. 506–518); it models the self-reference with "a predictor who guessed earlier", as here —
the route is data, not a within-step fixed point. Corollaries (costless deferral, no
Newcomblike payoffs) are report text.
-/

namespace Cleanroom.Deference.DefLatticeArrows.Counterfactual

noncomputable section

/-- The two routes by which an option can be reached.
Source: v2 §8 (root-deference-2-012)
Kind: D
Fidelity: exact (the earlier-predictor model) -/
inductive Route
  | commit
  | defer
  deriving DecidableEq

/-- **Act-independence**: an option's payoff does not depend on the route.
Source: v2 §8 ("the option values are treated as fixed with respect to the choice");
root-deference-2-012
Kind: D
Fidelity: exact -/
def ActIndependent {J : Type*} (O : J → Route → ℝ) : Prop :=
  ∀ j r r', O j r = O j r'

/-- **Under act-independence the reading is sound**: the payoff on the taken route (`defer`)
is the commit payoff.
Source: v2 §8 ("This is exactly right when payoffs are choice-independent")
Kind: L
Fidelity: exact
Hyps: (a) `ActIndependent` -/
theorem reading_sound_of_actIndependent {J : Type*} (O : J → Route → ℝ)
    (h : ActIndependent O) (j : J) : O j Route.defer = O j Route.commit :=
  h j Route.defer Route.commit

/-- The witness options: `A` pays `1` if committed to directly, `0` if reached by deferral;
`B` pays `2/5` either way.
Source: v2 §8 *Witness* (root-deference-2-012), paraphrased
Kind: D
Fidelity: exact (the earlier-predictor model) -/
def witnessMenu : Fin 2 → Route → ℝ
  | 0, Route.commit => 1
  | 0, Route.defer => 0
  | 1, _ => 2 / 5

/-- The witness menu is not act-independent (`A` pays `1` committed, `0` deferred).
Source: v2 §8
Kind: N+
Fidelity: exact -/
theorem witnessMenu_not_actIndependent : ¬ ActIndependent witnessMenu := by
  intro h
  have := h 0 Route.commit Route.defer
  simp [witnessMenu] at this

/-- On the taken route (`defer`), the expert's pick is `B` (`0 < 2/5`), and Value's inequality
`Ŝ ≥ E(A)` holds: `2/5 ≥ 0`.
Source: v2 §8 ("the future self takes `B`, and `Ŝ_n ≈ 0.4`; the theorem reports `0.4 ≳ 0`")
Kind: N+
Fidelity: exact -/
theorem witness_value_inequality :
    witnessMenu 0 Route.defer < witnessMenu 1 Route.defer ∧
      witnessMenu 0 Route.defer ≤ witnessMenu 1 Route.defer := by
  simp [witnessMenu]; norm_num

/-- **The reading fails**: committing to `A` pays `1 > 2/5` — more than the followed strategy.
Source: v2 §8 ("committing to `A` actually pays `1 > 0.4`, so deference is the worse choice")
Kind: N+
Fidelity: exact -/
theorem witness_reading_fails : witnessMenu 1 Route.defer < witnessMenu 0 Route.commit := by
  simp [witnessMenu]; norm_num

/-- **The witness, assembled**: not act-independent; Value's inequality holds on the road
taken; the committed payoff beats the followed strategy.
Source: v2 §8 *Witness*; root-deference-2-012
Kind: N+
Fidelity: exact -/
theorem witness :
    ¬ ActIndependent witnessMenu ∧
      witnessMenu 0 Route.defer ≤ witnessMenu 1 Route.defer ∧
        witnessMenu 1 Route.defer < witnessMenu 0 Route.commit :=
  ⟨witnessMenu_not_actIndependent, witness_value_inequality.2, witness_reading_fails⟩

end

end Cleanroom.Deference.DefLatticeArrows.Counterfactual
