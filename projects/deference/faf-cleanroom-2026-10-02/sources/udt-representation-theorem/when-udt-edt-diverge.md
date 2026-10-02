# When Do UDT and EDT Diverge?

> **Corrected 2026-08-05** (see [cleanup-audit-2026-08-05](cleanup-audit-2026-08-05.md)): the original version claimed EDT two-boxes in standard Newcomb. That is CDT/dominance reasoning — EDT conditions on the action, treats it as evidence about the prediction, and **one-boxes**. The Newcomb example, the divergence analysis, and the summary table have been corrected; standard Newcomb separates CDT from EDT/UDT, while EDT/UDT separation requires cases where *updating on the local observation* discards policy-level correlation (transparent Newcomb, counterfactual mugging). `notation.md` §3.3 has the correct three-way conditioning table. The same error was present in `lean/UDT/EDTvsUDT.lean` (relabeled to CDT) and the archived `parsimony-argument.md`.

## The Question

UDT and EDT are often presented as different decision theories with different recommendations. But when exactly do they give different answers?

This document characterizes the precise condition.

## The Setup

An agent faces a multi-situation decision problem:
- Set of situations S the agent might face
- At each situation s, available actions A
- Utility function U(s, a, context) where "context" may include actions at other situations
- Probability distribution P over which situation obtains

## EDT's Recommendation

At situation s, EDT computes:

a*_EDT = argmax_a E[U | I am at s and I take action a]

This conditions on being-at-s as a fact about the world, then asks what action maximizes expected utility given this fact.

## UDT's Recommendation

At situation s, UDT computes:

a*_UDT = argmax_a E[U | my policy maps s to a]

This conditions on having-a-policy-that-says-a-for-s, which is a constraint on the global policy.

## When Are They the Same?

**Theorem.** EDT and UDT agree when there is **no cross-situation dependence**.

**Definition.** A problem has **no cross-situation dependence** if:

For all s, s' ∈ S with s ≠ s', the utility at s does not depend on the action at s'.

Formally: U(s, a, context) = U(s, a) for some function U: S × A → ℝ.

**Proof sketch:**

If U(s, a) depends only on s and a:
- EDT: E[U | s, a] = U(s, a)
- UDT: evaluates the modified policy — V(π[s↦a]) = P(s)·U(s, a) + Σ_{s'≠s} P(s')·U(s', π(s')) — in which only the first term varies with a
  *(the original draft wrote the UDT objective as Σ_{s'} P(s')·U(s', π(s')), a quantity not containing the choice variable a; fixed 2026-08-05)*

For the specific situation s:
- EDT optimizes a → U(s, a)
- UDT optimizes π, which includes choosing π(s)

Since U at s depends only on the action at s, UDT's global optimization decomposes:
- max_π Σ_{s'} P(s') · U(s', π(s')) = Σ_{s'} P(s') · max_a U(s', a)

Each local optimization (max_a U(s, a)) can be done independently. UDT and EDT agree.

## When Do They Diverge?

**Theorem.** EDT and UDT can diverge when there IS **cross-situation dependence**.

**Definition.** A problem has **cross-situation dependence** if:

There exist situations s ≠ s' and actions a such that U(s, a, context) depends on the action taken at s'.

**Example: Newcomb's Problem (standard, opaque box)**

- Situations: {predicting-phase, decision-phase}
- At predicting-phase: predictor forms belief about your policy
- At decision-phase: you choose one-box or two-box
- Utility: depends on predictor's choice, which depends on what you WOULD do

Cross-situation dependence: the predictor's belief at predicting-phase depends on your policy, and affects your utility.

- **CDT** at decision-phase: holds the (already-made) prediction fixed and reasons by dominance → **two-boxes**.
- **EDT** at decision-phase: conditions on the action; one-boxing is strong evidence the prediction was "one-boxer" → **one-boxes**.
- **UDT**: chooses the policy; the one-boxing policy gets the million → **one-boxes**.

**Result:** standard Newcomb separates **CDT** from EDT/UDT. It does *not* separate EDT from UDT.

**Example: Transparent Newcomb (where EDT and UDT actually diverge)**

Both boxes are transparent; the predictor filled the big box iff it predicted you one-box *even upon seeing it full* (and you are facing an empty big box only if it predicted two-boxing). Seeing the empty box, EDT — having **updated on the observation** — computes that one-boxing now yields nothing and two-boxes ("I wish I could be a one-boxer, but the empty box proves I'm not";). UDT evaluates the policy from the prior, without updating on the observation, and one-boxes even facing the empty box — which is what makes the box full for agents with that policy.

**The general pattern:** EDT and UDT diverge when the *local observation* carries information that, once conditioned on, discards the policy-level correlation — i.e., when the observation is downstream of the environment's response to your policy. Cross-situation dependence alone separates CDT from the other two; EDT/UDT separation additionally requires updating-on-observation to change the answer (transparent Newcomb, counterfactual mugging, Parfit's hitchhiker after rescue).

## Characterizing Cross-Situation Dependence

Cross-situation dependence arises from:

### 1. Prediction
The environment predicts your behavior and responds to the prediction.
- Newcomb: Predictor responds to predicted policy
- Transparent Newcomb: You see the result of the prediction

### 2. Correlation
Your behavior correlates with others' behavior (not through causal influence).
- Twin Prisoner's Dilemma: Your twin does what you do
- Symmetry arguments: Identical agents make identical choices

### 3. Commitment
Your current behavior affects how future situations treat you.
- Reputation: Others trust you if you've been trustworthy
- Self-trust: Your future self follows advice if past self was reliable

### 4. Coordination
Multiple instances of you must coordinate without communication.
- Coordinated Buttons: Your copies must press the same button
- Third Button: Coordination with risk of exploitation

## The Common Structure

All cases of cross-situation dependence have the same structure:

**Utility in situation s depends on a counterfactual about another situation s':**
"What would this agent do if it faced s' instead?"

If the counterfactual is part of the utility calculation, then:
- CDT ignores it (holds the environment's state fixed and reasons by dominance)
- EDT tracks it only *evidentially through the current action, after updating on the local observation* — which fails exactly when the observation screens off or contradicts the policy-level correlation
- UDT accounts for it directly (conditions on the policy, which answers the counterfactual, without updating on the local observation)

## The Policy-Dependence Test

**Test:** Does the environment's response to you at s depend on your policy π, beyond just π(s)?

If yes: cross-situation dependence. EDT and UDT may diverge.
If no: no cross-situation dependence. EDT and UDT agree.

**Formally:** Let R(s, π) be the environment's response at s given policy π.

- If R(s, π) = R(s, π') whenever π(s) = π'(s): no cross-situation dependence.
- If R(s, π) ≠ R(s, π') for some π, π' with π(s) = π'(s): cross-situation dependence.

## Why UDT is Correct Under Cross-Situation Dependence

When cross-situation dependence exists:

1. The environment responds to your **policy**, not just your local action
2. Your utility depends on this response
3. To maximize utility, you must account for how your policy affects the response
4. EDT doesn't account for this; UDT does

**The argument:** If the environment checks "what would this agent do in situation s'?" then your answer to that question matters. UDT gives the right answer because it conditions on the policy. EDT gives the wrong answer because it conditions only on the local situation.

## The "Fairness" Connection

**Decision-determination** (fairness) says: the environment responds to policy, not to mechanism.

Combined with cross-situation dependence:
- The environment cares about your policy (which situations you'd handle which way)
- But not about HOW you arrive at that policy (your internal algorithm)

This is exactly the regime where UDT is correct:
- Account for the policy (UDT conditioning)
- Don't worry about mechanism (decision-determined)

## Summary

| Condition | CDT | EDT | UDT |
|-----------|-----|-----|-----|
| No cross-situation dependence | ✓ | ✓ | ✓ (all agree) |
| Cross-situation dependence, observation not downstream of policy-response (standard Newcomb) | ✗ two-boxes | ✓ one-boxes | ✓ one-boxes |
| Cross-situation dependence + observation downstream of policy-response (transparent Newcomb, counterfactual mugging) | ✗ | ✗ updates itself out of the correlation | ✓ |

**The representation theorem says:** unified agents in cross-situation-dependent problems reason updatelessly. Against CDT the divergence appears as soon as there is cross-situation dependence; against EDT it appears only where updating on the local observation breaks the policy correlation — which is exactly the case an EDT advocate would contest.
