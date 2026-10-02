# Policy as Latent Variable

## The Core Insight

When we have two random variables A (actions) and B (observations), the "policy" isn't just a function π : B → A. It's a **random variable Π** that captures *which* function relates them.

## Information-Theoretic Decomposition

Given random variables A and B:

- **I(A; B)** — mutual information, what's shared
- **H(A | B)** — conditional entropy, what remains uncertain about A given B
- **H(B | A)** — conditional entropy, what remains uncertain about B given A

Condensation theory says we can reify these as random variables:
- **A ∨ B** — the common information (finest variable that's a function of both)
- The "conditional parts" — what's left over

## The Deterministic Case

If **H(A | B) = 0**, then A is a deterministic function of B. Knowing B determines A completely.

But in general, **H(A | B) > 0** — there's uncertainty about A even knowing B.

## The Policy as "Missing Information"

The policy Π is the random variable such that:

```
H(A | Π, B) = 0
```

That is: once we know both the policy Π and the observation B, the action A is determined.

But:
```
H(A | B) > 0  (in general)
```

The policy is exactly the information that's "missing" — what you'd need to know, in addition to B, to predict A.

## Different Worlds, Different Policies

This framing makes clear: different worlds ω ∈ Ω might have different policies.

- In world ω₁, the policy might be π₁ (always cooperate)
- In world ω₂, the policy might be π₂ (always defect)

The random variable Π assigns to each world its policy: Π(ω) = the function that world uses to map observations to actions.

## Connection to the IBE Framework

In the Communication & Trust framework:

- **D_B** (boundary dynamic) is a random variable encoding the full decision mechanism
- **Π** (policy) is a *coarsening* of D_B — the equivalence class that forgets implementation details
- **Π†** (effective policy) is what actually gets implemented
- **Π*** (chosen policy) is what would be implemented without modification

The policy Π is the latent that:
1. Is a subvariable of the mechanism D_B
2. Together with observations O, determines actions A
3. Is what the environment responds to (decision-determination)

## Why This Matters for the Representation Theorem

The question "what does it mean to recognize an agent?" becomes:

> Finding a latent variable Π such that H(A | Π, B) = 0

This is a **condensation condition** — we're finding the minimal latent that explains the action-observation relationship.

The representation theorem should say: if you find such a Π, and the environment only responds to Π (decision-determination), then optimizing over Π gives the UDT formula.

## Contrast with "Policy as Function"

**Old framing (policy as function):**
- A policy is π : Obs → Act
- We optimize over the space of functions
- The theorem says: optimal π satisfies UDT formula

**New framing (policy as latent):**
- A policy is a random variable Π
- Π is characterized by: H(A | Π, O) = 0
- The theorem should derive: if Π is a good condensation, and environment responds only to Π, then UDT

The new framing connects to condensation theory and makes the information-theoretic content explicit.
