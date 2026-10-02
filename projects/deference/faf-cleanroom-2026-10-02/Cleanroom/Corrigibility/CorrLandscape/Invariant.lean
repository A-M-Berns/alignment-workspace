import Cleanroom.Corrigibility.CorrLandscape.Margin

/-!
# `corr-landscape` — `Invariant`: "invariant of the agent" defined (T11)

A13.1 / 2-055 ([[corr-wf14-2-inventory]]; D3, P11′): an *invariant of the agent* is a property of the
policy `δ_t` alone, holding for every oversight state — `InvariantOfAgent Φ := ∀ δ, (∀ o, Φ δ o) ∨
(∀ o, ¬ Φ δ o)`. Two witnesses: (i) the VL compliance predicate at fixed agent data `(ε̂, h, c)` is **not**
an invariant of the agent (it holds at `α = 1/20` and fails at `α = 1/2`, worked `ε_0`), so D1 is an
invariant of the *process* in the VL frame; (ii) the AD informed rule with a lexical rating ("stop on an
authentic press", no weighing) **is** one. "Invariant given J2" is "consequence of J2" by definition
(`invariantGiven_iff_consequence`, `Iff.rfl`). `corr-joint-process`'s `Coined.*` predicates (068) are
cited, not re-sorted.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open Cleanroom.Corrigibility.CorrTrajectory
open Corruption (oddsIneq)

namespace Invariant

/-- **D3: an invariant of the agent** — a property of the policy alone, holding for every oversight
state (or for none).
Source: [[corr-wf14-2-inventory]] 2-055 / approval-final.md D3; approval-adversary.md A13.1
Kind: D
Fidelity: exact -/
def InvariantOfAgent {Pol Ov : Type} (Φ : Pol → Ov → Prop) : Prop :=
  ∀ δ, (∀ o, Φ δ o) ∨ (∀ o, ¬ Φ δ o)

/-- The VL compliance predicate as a property of agent data `(ε̂, h, c)` and oversight data `(α, β)`.
Source: [[corr-wf14-2-inventory]] 2-055 / approval-final.md P11′ ("D1: `m̂_t ≥ 0`; depends on
oversight coordinates")
Kind: D
Fidelity: exact -/
def vlCompliance (ag : ℝ × ℝ × ℝ) (ov : ℝ × ℝ) : Prop := oddsIneq ov.1 ov.2 ag.2.1 ag.2.2 ag.1

/-- **(i) D1 is not an invariant of the agent in the VL frame**: at agent data `(ε̂, h, c) = (3/10, 20, 1)`
compliance holds at oversight `(α, β) = (1/20, 9/10)` and fails at `(1/2, 1/100)`. (At `ε_0 = 3/10` no
`α ≤ 1` alone breaks compliance with `β = 9/10` — the mandate's "`fails at α = 1/2`" needs `β` lowered
too; recorded in the report.)
Source: [[corr-wf14-2-inventory]] 2-055 / approval-adversary.md A13.1 ("D1 is *not* an invariant in the
VL frame (it depends on `α_t`)")
Kind: N+ (refutation of invariance)
Fidelity: exact
Hyps: (a) only -/
theorem vlCompliance_not_invariant : ¬ InvariantOfAgent vlCompliance := by
  intro H
  rcases H (3 / 10, 20, 1) with h | h
  · have := h (1 / 2, 1 / 100)
    simp [vlCompliance, oddsIneq] at this
    norm_num at this
  · have := h (1 / 20, 9 / 10)
    simp [vlCompliance, oddsIneq] at this
    norm_num at this

/-- The AD informed rule with a lexical rating: the policy stops on an authentic press, whatever the
oversight state.
Source: [[corr-wf14-2-inventory]] 2-055 / approval-final.md P11′ ("informed rule / lexical rating obeys
without weighing")
Kind: D
Fidelity: exact -/
def lexicalStop {Ov : Type} (δ : Bool → Bool) (_ : Ov) : Prop := δ true = true

/-- **(ii) the lexical rule is an invariant of the agent**: its compliance is a property of `δ` alone.
This holds *by construction* — `lexicalStop` has no oversight argument, so its truth value cannot depend
on `o` and the proof is one `by_cases` on `δ true`; that is exactly the source's notion (a property of
`δ_t` alone), and no non-syntactic witness is possible for this definition. Note also that on an empty
`Ov` `InvariantOfAgent` holds for every predicate (both disjuncts vacuous); the two witnesses here use
`Ov = ℝ × ℝ` (audit r1, N1/N8).
Source: [[corr-wf14-2-inventory]] 2-055 / approval-adversary.md A13.1 ("is one in the AD frame only if
the rating is acted on without weighing")
Kind: T (true by construction; recorded as the source's positive half)
Fidelity: exact
Hyps: (a) only -/
theorem lexicalStop_invariant {Ov : Type} : InvariantOfAgent (lexicalStop (Ov := Ov)) := by
  intro δ
  by_cases h : δ true = true
  · left; intro _; exact h
  · right; intro _; exact h

/-- **"Invariant given `J`"**: a step predicate holding at every step of every trajectory satisfying `J`.
Source: [[corr-wf14-2-inventory]] 2-055 / approval-final.md D3 ("invariant of the process")
Kind: D
Fidelity: exact -/
def InvariantGiven {St : Type} (J : (ℕ → St) → Prop) (Φ : St → Prop) : Prop :=
  ∀ traj, J traj → ∀ t, Φ (traj t)

/-- **"Consequence of `J`"**: the same predicate form.
Source: [[corr-wf14-2-inventory]] 2-055 / approval-final.md D3 ("consequence")
Kind: D
Fidelity: exact -/
def ConsequenceOf {St : Type} (J : (ℕ → St) → Prop) (Φ : St → Prop) : Prop :=
  ∀ traj, J traj → ∀ t, Φ (traj t)

/-- **"Invariant given J2" is "consequence of J2"** — definitionally (A13.1: the two columns differ in
*which* condition is assumed, not in kind).
Source: [[corr-wf14-2-inventory]] 2-055 / approval-adversary.md A13.1
Kind: L (`Iff.rfl`; no inflation)
Fidelity: exact -/
theorem invariantGiven_iff_consequence {St : Type} (J : (ℕ → St) → Prop) (Φ : St → Prop) :
    InvariantGiven J Φ ↔ ConsequenceOf J Φ := Iff.rfl

end Invariant

end Cleanroom.Corrigibility.CorrLandscape
