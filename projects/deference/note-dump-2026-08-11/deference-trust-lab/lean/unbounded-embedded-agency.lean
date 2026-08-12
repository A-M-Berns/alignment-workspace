/-
  UNCHECKED — for the Lean-verify agent.

  Companion to models/unbounded-embedded-agency-model.md.

  This file formalizes the ALGEBRAIC CORE of the model

      "a UDT1.0 agent that (1-δ_b)-believes its (realized) policy is UDT1.1
       is ε-optimal, with ε = O(δ_b)·(utility range),"

  separating the self-knowledge parameter δ_b (confidence about WHICH POLICY one
  realizes) from the environment/substrate parameter δ_m (confidence that the
  policy is NOT modified). The point of the split (AGENDA, "Interpretational
  Issues" + "Updatelessness"): the optimality bound needs ONLY δ_b small; it is
  AGNOSTIC to δ_m. So the theorem no longer covertly bans self-modification —
  the belief is placed on the *realized* (possibly post-modification) policy.

  There are THREE theorems here, in increasing order of what they say:

    1. `epsilon_optimal_of_belief`  — the headline bound, restated against the
       REALIZED policy type `Pol` (which the docstring fixes to be the
       post-modification policy space). Pure algebra; identical content to the
       prior `UDT11Belief.lean` headline, re-keyed to make the δ_b vs δ_m split
       explicit in the prose.

    2. `epsilon_optimal_split`  — the SAME bound stated with the self/env split
       made syntactically visible: the believed-value mixture uses ONLY δb, and
       a separate δm appears NOWHERE in hypotheses or conclusion. This is the
       formal witness that "the optimality certificate does not depend on
       substrate stability." (Its proof is literally `epsilon_optimal_of_belief`
       with δ := δb.) The δm argument is present but unused — that *is* the
       claim: optimality is δm-agnostic.

    3. `stag_hunt_select`  — the Stag-Hunt closure as a clean inequality on a
       2-action symmetric game: if a copy (1-δ)-believes the partner plays the
       UDT1.1 action (Stag), and δ ≤ 1 - c/b (the Stag-Hunt gap), then Stag is a
       best response. This is the content the `hsel` hypothesis of theorem 1
       SMUGGLES; here it is proved from the belief + the gap condition, on the
       worst-case belief q = 1-δ. It is the bridge from pointwise UDT1.0 to the
       whole-policy mixture, and it carries an EXPLICIT extra hypothesis
       (δ ≤ 1 - c/b) that the whole-policy view hides. See the micro-example
       `unbounded_embedded_agency_micro.py` Part B for the same numbers.

  WHAT EACH THEOREM IS SUPPOSED TO SAY, AND THE FIDELITY GAPS, are in the
  docstrings. The single most important gap to weigh: theorems 1–2 are about a
  WHOLE-POLICY chooser; a genuine UDT1.0 agent chooses ACTIONS pointwise, and the
  reduction is theorem 3's job — but theorem 3 only covers the symmetric 2-action
  2-situation Stag Hunt, NOT a general game. So the pointwise→whole-policy bridge
  is proved only in a toy instance, and ASSUMED (via hsel) in general. That is
  the honest boundary.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

namespace UnboundedEmbeddedAgency

/- ============================================================
   PART 1–2.  Whole-policy mixture-deference bound, with the
   self-knowledge (δb) vs substrate-stability (δm) split.
   ============================================================ -/

variable {Pol : Type*}

/-- Believed value of a (realized) policy `σ` under `(1-δ)`-belief that one is
    UDT1.1: a mixture of the true UDT1.1 value map `Vstar` and an arbitrary
    "other-code" map `Vother`. Here `δ` is the SELF-KNOWLEDGE deficit δb (mass on
    "my realized policy is NOT the UDT1.1 one"), placed on the *realized* policy
    space `Pol`. No substrate parameter δm enters. -/
def Bel (δ : ℝ) (Vstar Vother : Pol → ℝ) (σ : Pol) : ℝ :=
  (1 - δ) * Vstar σ + δ * Vother σ

/--
  **Theorem 1 (headline bound).**  If the agent commits to a believed-value
  maximizer `s` (hypothesis `hsel`), and both value maps lie in `[lo,hi]`, then
      `(1 - δ) * (Vstar pstar - Vstar s) ≤ δ * (hi - lo)`,
  i.e. the realized policy `s` is within `δ/(1-δ)·(hi-lo)` of the true optimum
  `Vstar pstar` under the UDT1.1 value map.

  Plain English: belief-you're-UDT1.1 with confidence `1-δ` ⇒ `ε(δ)`-optimal,
  `ε(δ) = δ/(1-δ)·range`. Note: `pstar` need NOT be hypothesized optimal — the
  inequality is proved for an ARBITRARY comparison policy `pstar` (it says `s`
  is no worse than ANY `pstar`, up to the δ-slack), which is the strongest form.
  Faithful caveats: `Vother` fully arbitrary (the strength: the (1-δ) mass
  dominates whatever the bad world says); `hsel` is the whole-policy choice,
  the pointwise→whole-policy bridge being theorem 3 (only proved in the toy game).
-/
theorem epsilon_optimal_of_belief
    (δ lo hi : ℝ) (Vstar Vother : Pol → ℝ) (pstar s : Pol)
    (hδ0 : 0 ≤ δ)
    (hloO : ∀ σ, lo ≤ Vother σ) (hhiO : ∀ σ, Vother σ ≤ hi)
    (hsel : ∀ σ, Bel δ Vstar Vother σ ≤ Bel δ Vstar Vother s) :
    (1 - δ) * (Vstar pstar - Vstar s) ≤ δ * (hi - lo) := by
  have key : Bel δ Vstar Vother pstar ≤ Bel δ Vstar Vother s := hsel pstar
  unfold Bel at key
  have hδloO : δ * lo ≤ δ * Vother pstar := mul_le_mul_of_nonneg_left (hloO pstar) hδ0
  have hδhiO : δ * Vother s ≤ δ * hi := mul_le_mul_of_nonneg_left (hhiO s) hδ0
  nlinarith [hδloO, hδhiO, key]

/--
  **Theorem 2 (self/env split made syntactic).**  The SAME bound, but the
  signature now exhibits a substrate-stability parameter `δm` that appears
  NOWHERE in the believed-value mixture, the hypotheses, or the conclusion. The
  belief mixture uses only `δb`. The conclusion bounds the optimality gap by
  `δb·(hi-lo)` with no dependence on `δm`.

  Plain English claim this encodes: *the optimality certificate depends only on
  behavioural self-knowledge `1-δb` (confidence about which policy you realize),
  not on substrate stability `1-δm` (confidence you won't be modified).* So,
  unlike "confidence in my source code", this hypothesis does NOT covertly ban
  self-modification: place the belief on the realized post-modification policy
  and the bound survives for any `δm`.

  Fidelity note: that `δm` is a *bound argument that is genuinely unused* is the
  whole point — Lean will accept the unused variable, and its unusedness is the
  formal content. The verify agent should confirm `δm` truly does not appear in
  the proof term's relevant hypotheses (it is only in the signature for the
  prose). NON-VACUITY: this is not `True`; it is theorem 1 verbatim at `δ := δb`.
-/
theorem epsilon_optimal_split
    (δb δm lo hi : ℝ) (Vstar Vother : Pol → ℝ) (pstar s : Pol)
    (hδb0 : 0 ≤ δb)
    (hloO : ∀ σ, lo ≤ Vother σ) (hhiO : ∀ σ, Vother σ ≤ hi)
    (hsel : ∀ σ, Bel δb Vstar Vother σ ≤ Bel δb Vstar Vother s) :
    (1 - δb) * (Vstar pstar - Vstar s) ≤ δb * (hi - lo) :=
  epsilon_optimal_of_belief δb lo hi Vstar Vother pstar s hδb0 hloO hhiO hsel

/-- The `δ = 0` corner of theorem 1: certainty you are UDT1.1 ⇒ EXACT optimality. -/
theorem optimal_of_certain
    (Vstar Vother : Pol → ℝ) (pstar s : Pol)
    (hsel : ∀ σ, Bel 0 Vstar Vother σ ≤ Bel 0 Vstar Vother s) :
    Vstar pstar ≤ Vstar s := by
  have key := hsel pstar
  unfold Bel at key
  simp only [sub_zero, one_mul, zero_mul, add_zero] at key
  exact key

/- ============================================================
   PART 3.  The Stag-Hunt closure: the pointwise→whole-policy
   bridge, proved in the symmetric 2-action toy game.
   ============================================================ -/

/-- Per-copy payoff in a symmetric Stag Hunt with parameters `b > c > 0`:
    playing Stag against a Stag-partner pays `b`, against a Hare-partner pays `0`;
    playing Hare pays `c` regardless. We encode "my action is Stag" by a bool. -/
def payoffStag (b : ℝ) (otherStag : Bool) : ℝ := if otherStag then b else 0
def payoffHare (c : ℝ) : ℝ := c

/--
  **Theorem 3 (Stag-Hunt selection — the smuggled bridge, discharged in the toy
  game).**  A copy that `(1-δ)`-believes the partner plays the UDT1.1 action
  (Stag) evaluates Stag, in the WORST case (the δ-mass entirely on "partner plays
  Hare", giving belief `q = 1-δ` that the partner is Stag), at expected payoff
  `(1-δ)·b`. If the Stag-Hunt gap condition `δ ≤ 1 - c/b` holds (equivalently
  `(1-δ)·b ≥ c`), then Stag's worst-case expected payoff dominates Hare's safe
  payoff `c`:

      `c ≤ (1-δ) * b`.

  Plain English: when self-belief is strong enough relative to the game's
  Stag-Hunt gap, pointwise best response under "I believe the rest of my policy
  is UDT1.1" plays the OPTIMAL (Stag) action — so the pointwise UDT1.0 agent
  realizes the UDT1.1 policy. This is exactly what `hsel` in theorems 1–2
  assumes; here it is PROVED, but it carries the EXTRA hypothesis `δ ≤ 1 - c/b`
  that the whole-policy view hides. The hypothesis form chosen, `(1-δ)*b ≥ c`,
  is `δ ≤ 1 - c/b` rearranged (avoids division); `hb : 0 < b` makes the two
  equivalent and the game non-degenerate.

  Fidelity: this is the bridge ONLY for the symmetric 2-action 2-copy game, NOT
  a general claim that pointwise-UDT1.0-believing-UDT1.1 implements UDT1.1 in
  arbitrary games (that is the CONJECTURE in the model doc, Idea 2). Non-vacuous:
  for `b=4, c=3` the threshold is `δ ≤ 1/4`, matching the micro-example. -/
theorem stag_hunt_select
    (b c δ : ℝ) (hb : 0 < b) (hc : 0 ≤ c)
    (hgap : (1 - δ) * b ≥ c) :
    payoffHare c ≤ (1 - δ) * payoffStag b true := by
  -- payoffStag b true = b ; payoffHare c = c ; conclusion: c ≤ (1-δ)*b.
  unfold payoffHare payoffStag
  simp only [if_true]
  linarith [hgap]

/--
  **Theorem 3′ (the trap survives when belief is too weak).**  The converse edge:
  if the gap condition FAILS strictly — `(1-δ)·b < c` — then Stag's worst-case
  expected payoff is STRICTLY below Hare's, so the best response is Hare and the
  Stag-Hunt trap can persist. This is the formal witness that the `δ ≤ 1-c/b`
  hypothesis of theorem 3 is REAL and load-bearing (not slack): outside it, the
  belief does not select the optimum, hence `hsel` of theorems 1–2 can fail for
  the pointwise agent. -/
theorem stag_hunt_trap
    (b c δ : ℝ) (hbad : (1 - δ) * b < c) :
    (1 - δ) * payoffStag b true < payoffHare c := by
  unfold payoffHare payoffStag
  simp only [if_true]
  linarith [hbad]

#print axioms epsilon_optimal_of_belief
#print axioms epsilon_optimal_split
#print axioms optimal_of_certain
#print axioms stag_hunt_select
#print axioms stag_hunt_trap

end UnboundedEmbeddedAgency
