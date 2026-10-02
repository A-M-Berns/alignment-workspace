# Agency as Condensation: Formalizing the Connection

## Goal

Make precise the claim that agency attribution is a special case of latent variable modeling, and that the UDT representation theorem is analogous to condensation's correspondence theorem.

---

## The Core Insight: Policy as Latent Variable

**Key reframing:** The policy isn't just a function π : O → A that we optimize over. It's a **random variable Π** — a latent that captures which function relates observations to actions.

### Information-Theoretic Characterization

Given random variables A (actions) and B (observations):

- **H(A | B)** — what remains uncertain about A given B
- **H(B | A)** — what remains uncertain about B given A
- **I(A; B)** — mutual information, what's shared

The **policy Π** is the random variable such that:

```
H(A | Π, B) = 0
```

That is: once we know both the policy Π and the observation B, the action A is completely determined.

But in general:
```
H(A | B) > 0
```

The policy is the "missing information" — what you need to know, beyond the observation, to predict the action.

### Different Worlds, Different Policies

Different worlds ω ∈ Ω might have different policies:
- In world ω₁, Π(ω₁) = π₁ (cooperate strategy)
- In world ω₂, Π(ω₂) = π₂ (defect strategy)

The random variable Π assigns each world its policy.

---

## Review: Condensation Setup

### Random Variable Models

A **random variable model** M = (Ω, (X_i)_{i∈I}) consists of:
- A probability space Ω
- A finite family of observable random variables X_i

### Latent Variable Models

A **latent variable model** L for M consists of:
- An expanded probability space Λ with map π: Λ → Ω
- Latent random variables (Y_j)_{j∈J} on Λ
- A **contribution relation** ▷ ⊆ J × 𝒫(I)

**Condition:** Each X_i is (almost everywhere) a function of the Y_j that contribute to it.

### The Correspondence Theorem

**Perfect condensation** (roughly): The latent variables efficiently summarize the observables.

**Theorem (informal):** If L₁ and L₂ are both perfect condensations of M, then their latent variables correspond.

---

## Agency as Latent Variable Model

### The Observable Variables

When attributing agency to system S:

Let I = {situations the system might face}

For each i ∈ I, let X_i = (O_i, A_i) where:
- O_i = observation in situation i
- A_i = action in situation i

The **random variable model** M = (Ω, (X_i)_{i∈I}) represents all possible behaviors of S across situations.

### The Policy as Central Latent

**The policy Π is a random variable such that:**

For all situations i:
```
H(A_i | Π, O_i) = 0
```

This says: given the policy and the observation, the action is determined.

**Key structural property:** Π contributes to ALL situations — it's a single latent explaining all behavior.

### The Agency Latent Variable Model

**L_agency consists of:**
- Policy random variable Π (values are functions O → A)
- Contribution: Π ▷ I (policy contributes to all situations)
- Determination: H(A_i | Π, O_i) = 0 for all i

**This is the "single latent explains many observables" structure** that condensation identifies as special.

---

## Condensation Conditions for Agency

### Condition 1: Determination

**The policy + observation determines the action.**

```
H(A_i | Π, O_i) = 0
```

For deterministic policies, this is automatic: if Π = π means "use function π," then A_i = π(O_i).

### Condition 2: Recoverability (Redundancy)

**The policy is recoverable from behavior.**

```
H(Π | (O_i, A_i)_{i∈I}) ≈ 0
```

Or with redundancy: for any i₀,
```
H(Π | (O_i, A_i)_{i ≠ i₀}) ≈ 0
```

**Meaning:** The policy isn't hidden — it's manifest in behavior. If we observe enough situations, we can reconstruct which policy is in use.

### Condition 3: Unity

**There is ONE policy across all situations.**

Not: separate policies Π_i for each situation
But: a single Π that determines behavior everywhere

This is the claim that there's a unified agent, not just coincidentally correlated behaviors.

### Condition 4: Decision-Determination

**The environment responds to the policy, not the mechanism.**

Let D be the "dynamics" or "mechanism" — the internal implementation details.

Decision-determination:
```
I(E ; D | Π) = 0
```

The environment E is independent of the mechanism D given the policy Π.

---

## The Representation Theorem

### Setup

- Unified agency: single policy Π with H(A_i | Π, O_i) = 0 for all i
- Recoverability: H(Π | behavior) ≈ 0
- Decision-determination: I(E ; D | Π) = 0
- Rationality: agent maximizes E[U]

### Conclusion

The optimal policy satisfies the UDT formula:

```
π(o) = argmax_a E[U | Π(o) = a]
```

### Why This Follows

1. **Unity** means there's ONE Π determining all actions
2. **Decision-determination** means U depends on Π (via E), not on D
3. **Rationality** means we maximize E[U] over policies
4. **The formula** is just: at each o, choose the action that makes Π globally optimal

The condensation structure (single latent contributing to all observables) plus rationality forces updateless reasoning.

---

## Connection to Communication & Trust Framework

In the IBE framework from Communication & Trust:

- **D_B** (boundary dynamic) is a random variable encoding the decision mechanism
- **Π** (policy) is a coarsening of D_B — it forgets implementation details
- **Π†** (effective policy) is what actually gets implemented
- **Π*** (chosen policy) is what would be implemented without modification

**The relationship:**
- D_B is like "full state"
- Π is the latent we extract
- H(A | Π, O) = 0 is the determination condition
- Decision-determination says E responds to Π, not to D_B

---

## Cross-Situation Dependence

### Why It Matters

When policy Π determines actions in multiple situations:
- Changes in Π affect actions everywhere
- You can't optimize situation i in isolation
- The policy structure induces correlations across situations

**Cross-situation dependence = the condensation structure applied to agency.**

### The Key Insight

Updateless reasoning follows because Π is a SINGLE latent contributing to ALL situations.

Optimizing A_i at observation o_i in isolation ignores that A_i is determined by Π, which also determines A_j at o_j, which affects U.

To optimize properly, you must optimize Π as a whole.

---

## The Information-Theoretic Formulation

### Agency Condensation Conditions

1. **Determination:** H(A_i | Π, O_i) = 0 for all i
2. **Recoverability:** H(Π | (O_i, A_i)_{i∈I}) ≈ 0
3. **Unity:** Single Π contributes to all situations
4. **Decision-determination:** I(U ; D | Π) = 0

### The Theorem

**Given** conditions 1-4 and rationality (maximize E[U]):

**Then** optimal Π satisfies: Π(o) = argmax_a E[U | Π(o) = a]

---

## Open Questions

### Technical

1. What's the exact relationship between condensation's correspondence theorem and the agency representation theorem?
2. How do approximate versions work?
3. Can we state this purely information-theoretically without assuming deterministic policies?

### Conceptual

1. How does the "endorsement" framing from Meaning & Agency connect to these condensation conditions?
2. Is recoverability actually necessary, or just determination + unity + decision-determination?
3. What happens when condensation conditions fail partially?

### For the Full Stack

1. How does Diffractor's plannable/unplanned distinction map onto this?
2. Can UDT1.01's optimality be stated as a condensation result?
3. What are the conditions for multi-agent settings?

---

## Summary

**Agency attribution = introducing a latent variable Π with specific structure:**
- Π is the "missing information" such that H(A | Π, O) = 0
- Π contributes to all situations (unity)
- Π is recoverable from behavior

**The representation theorem = condensation applied to agency:**
- The structure constrains the content
- Optimizing over Π (not local actions) is forced by the structure
- This IS updateless reasoning
