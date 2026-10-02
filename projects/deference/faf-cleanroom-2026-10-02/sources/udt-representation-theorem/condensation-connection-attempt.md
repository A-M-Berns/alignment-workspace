# The Condensation Connection: Attempt at Rigor

## The Core Insight: Policy as Latent

The key reframing: **the policy Π is a random variable, not just a function**.

Given observations O and actions A:
- In general, H(A | O) > 0 — knowing the observation doesn't determine the action
- The policy Π is the "missing information" such that H(A | Π, O) = 0
- Different worlds have different policies: Π(ω) = the function used in world ω

This connects directly to condensation's treatment of latent variables.

---

## What Condensation Actually Says

### The Setup (from Sam's work)

**Observable model:** M = (Ω, (X_i)_{i∈I})
- Ω is a probability space
- X_i are random variables (the observables)

**Latent variable model:** L = ((Λ, (Y_j)_{j∈J}), π_map, ▷)
- Λ is a probability space (latent space)
- Y_j are random variables on Λ (the latents)
- π_map : Λ → Ω is a map
- ▷ is a contribution relation: j ▷ S means latent j contributes to observables S

### The Condensation Conditions (informal)

**Perfect condensation** (roughly):
1. **Determination:** The latents determine the observables: H(X_i | relevant Y_j) = 0
2. **Parsimony:** The latents are minimal (no redundancy among latents)
3. **Contribution structure:** Each latent contributes to specific observables

### The Correspondence Theorem

**If L₁ and L₂ are both perfect condensations of M:**
Then their latents correspond (up to bijection and isomorphism).

**Interpretation:** "Doing it right" forces agreement on what the latents are.

---

## Applying This to Agency

### The Observable Model for Agency

**Observables:** For each situation i, we observe (O_i, A_i) ∈ Obs × Act

So M = (Ω, (X_i)_{i∈I}) where X_i = (O_i, A_i).

### The Policy as Latent

**The policy Π is a random variable such that:**
```
H(A_i | Π, O_i) = 0  for all i
```

This says: the policy, together with the observation, determines the action.

**The contribution structure:**
- Π ▷ I (the policy contributes to ALL situations)
- This is the "unity" condition — one latent explains all behavior

### The Condensation Conditions for Agency

**Condition 1: Determination**
```
H(A_i | Π, O_i) = 0
```
The policy + observation determines action. ✓ (by definition of policy)

**Condition 2: Recoverability**
```
H(Π | (X_i)_{i∈I}) ≈ 0
```
The policy can be recovered from behavior.

**Issue:** This depends on the observation distribution.
- If O is always the same o*, we can only learn Π(o*)
- If O has full support, we can learn all of Π

So recoverability requires diverse observations.

**Condition 3: Unity**
Single Π contributes to all situations.

---

## What Would a "Correspondence Theorem for Agency" Say?

**Hypothetical theorem:**
If L₁ and L₂ are both good agency attributions for the same behavior M,
then the attributed policies Π₁ and Π₂ are the same (or isomorphic).

**Is this true?**

Under the right conditions:
1. Both models have determination: H(A_i | Π_k, O_i) = 0
2. Observations have sufficient coverage
3. Both policies are recoverable

Then Π₁ = Π₂ — they must agree on the policy.

**This is intersubjectivity:** different observers agreeing on what the policy IS.

---

## The Gap: Correspondence vs Optimality

The condensation correspondence theorem is about:
**Multiple observers agreeing on what the latents ARE.**

The representation theorem needs to be about:
**What the latent SHOULD BE (optimal policy).**

These are different questions!

### Bridging the Gap

The connection comes through **decision-determination**:

1. **Condensation** says: if agency is well-attributed, observers agree on Π
2. **Decision-determination** says: the environment responds to Π, not mechanism D
3. **Therefore:** the environment's "model" of the agent (if optimal) must be Π
4. **Therefore:** utility depends on Π
5. **Therefore:** optimizing utility means optimizing over Π
6. **Therefore:** UDT formula follows

The key insight: **optimal predictors extract good condensations**.

If the environment is trying to predict the agent, and does so optimally, it will extract Π (the policy latent). Then decision-determination holds, and UDT follows.

---

## A More Precise Statement

**Theorem (sketch):**

Let M be a behavior model. Let L be an agency attribution with policy latent Π.

If:
1. **Determination:** H(A_i | Π, O_i) = 0 for all i
2. **Recoverability:** H(Π | behavior) ≈ 0
3. **Decision-determination:** I(E ; D | Π) = 0 (environment responds to policy)
4. **Rationality:** agent maximizes E[U]

Then:
1. Optimal Π satisfies: Π(o) = argmax_a E[U | Π(o) = a]

**The content is in conditions 1-3.** The derivation (condition 4 → UDT formula) is straightforward once we have policy-based utility.

---

## What This Means

### What Condensation Contributes

1. **Conceptual framing:** Agency attribution as latent variable modeling
2. **The policy as latent:** Π is the "missing information" with H(A | Π, O) = 0
3. **Intersubjectivity:** If agency is well-attributed, observers agree on Π
4. **Optimal prediction insight:** Good predictors extract the policy latent

### What Condensation Doesn't Contribute (Directly)

1. **Optimality:** Nothing about what Π SHOULD be (that comes from rationality)
2. **Decision-determination:** This is a separate assumption about the environment

### The Theorem Structure

```
Condensation conditions (determination, recoverability, unity)
    → Policy Π is well-defined
    → Intersubjectivity (observers agree on Π)
    → Optimal predictors extract Π
    → Decision-determination holds for optimal predictors
    → Utility is function of Π
    → Rationality gives UDT formula
```

---

## Open Questions

1. **Formalize "optimal predictor extracts Π"** — this needs information-theoretic precision
2. **When does decision-determination fail?** — non-optimal predictors, mechanism-dependent environments
3. **Connection to endorsement** — how does Meaning & Agency's framing fit?
4. **Computational aspects** — how does this connect to UDT1.01?

---

## Summary

The condensation connection is now more precise:

1. **Policy as latent:** Π is the random variable with H(A | Π, O) = 0
2. **Agency conditions:** determination + recoverability + unity
3. **Bridge to UDT:** optimal prediction → decision-determination → policy-based utility → UDT formula

The real content is:
- Defining the policy as a latent (not just a function)
- Understanding when decision-determination holds (optimal prediction)
- The UDT derivation follows from these
