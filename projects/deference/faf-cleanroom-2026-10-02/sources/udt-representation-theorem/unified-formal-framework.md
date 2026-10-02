# Toward a Unified Formal Framework

## Goal

Integrate:
1. **Condensation:** Latent variables, contribution relations, correspondence
2. **Communication & Trust:** I/B/E decomposition, internal/external observations
3. **Diffractor:** Plannable/unplanned, epistemic states, UDT1.01

Into a single formal framework that grounds the representation theorem.

---

## Layer 1: The Observable Level

### The Random Variable Model

**Observables:** The system's behavior across situations.

Let I be a set of situations (decision points the system might face).

For each i ∈ I, define:
- O_i ∈ Obs : the observation in situation i
- A_i ∈ Act : the action in situation i
- X_i = (O_i, A_i) : the full behavior in situation i

**The random variable model:** M = (Ω, (X_i)_{i∈I})

This is what we can observe: for each situation, what observation arose and what action was taken.

### Observable Factorization

The situations I can be factored:
- **By time:** I = {t₁, t₂, ...} (sequential decisions)
- **By observation:** I partitioned by external observation Ö (C&T instances)
- **By world:** I = possible worlds (Newcomb-style)

Different factorizations correspond to different granularities of analysis.

---

## Layer 2: The Latent Level (Agency Attribution)

### The Core Latents

When attributing agency, we introduce:

**π : Obs → Act** - The policy (central latent)
- π determines behavior: A_i = π(O_i)
- π contributes to ALL situations: π ▷ i for all i

**U : Ω → ℝ** - The utility function
- What the agent is optimizing
- May depend on the full history/world

**D** - The dynamics (C&T's D_B, D_I, D_E)
- How the agent computes the policy
- The "mechanism" behind the behavior

### The Latent Variable Model

**L_agency = ((Λ, (Y_j)_{j∈J}), π_map, ▷)**

Where:
- Λ = space of (policy, utility, dynamics) triples
- Y_π = policy, Y_U = utility, Y_D = dynamics
- π_map : Λ → Ω connects latent to observable
- ▷ specifies contributions (π ▷ all i)

### The Condensation Structure

**Key property:** π is a SINGLE latent that contributes to ALL observables.

In condensation notation:
- Y_I = π (the latent contributing to full set I)
- This is the "unified agency" structure

---

## Layer 3: The Epistemic Level (Handling Uncertainty)

### The C&T Decomposition

**Internal vs External:**
- Ö (external observation): From environment E
- Ȯ (internal observation): From interior I
- Full observation: O = (Ȯ, Ö)

**Semantic vs Side Channel:**
- Ô (semantic): Legitimate information
- Ǒ (side channel): Procedure modification

### The Diffractor Decomposition

**Plannable vs Unplanned:**
- h (plannable): Can write lookup-table policy
- S (unplanned): Epistemic state, computation output

**Trees:**
- Contracted tree: Just h (the formal policy domain)
- Expanded tree: (h, S) pairs (the actual decision space)

### Synthesizing the Decompositions

| C&T | Diffractor | Role |
|-----|-----------|------|
| Ö (external) | h (plannable) | Public situation |
| Ô (semantic internal) | S (epistemic) | Legitimate private info |
| Ǒ (side channel) | — | Illegitimate modification |
| Policy π: O → A | Broad policy on (h, S) | Behavioral specification |
| External policy π̈ | Narrow policy h → a | What coordination uses |

**The mapping:**
- C&T's "instances" (factored by Ö) = Diffractor's "plannable locations" h
- C&T's internal observation Ȯ includes Diffractor's epistemic state S
- The side channel Ǒ has no Diffractor analog (manipulation is implicit)

### Uncertainty Decomposition

**Empirical uncertainty:** About which situation i obtains
- Resolved by external observation Ö/h

**Epistemic uncertainty:** About beliefs, computations
- Captured by internal observation Ȯ/epistemic state S

**Logical uncertainty:** About own policy/algorithm
- Uncertainty in D_B (C&T) or in "what S implies" (Diffractor)

---

## Layer 4: The Condensation Conditions

### For the Policy Latent

**Condition 1: Determination**
H(A_i | π, O_i) = 0

The policy plus observation determines the action.
(Automatic for deterministic policies)

**Condition 2: Redundancy**
H(π | (X_i)_{i∈I-{i₀}}) ≈ 0 for any i₀

The policy is recoverable from almost-all behavior.
(The policy is manifest, not hidden)

**Condition 3: Relevance**
I(π ; X_i) > 0 for all i

The policy is relevant to every situation.
(Unified agency, not independent situations)

### For the Utility Latent

**Condition 4: Utility depends on policy**
I(U ; π) > 0

The utility function cares about the policy.
(Cross-situation dependence)

**Condition 5: Decision-determination**
I(U ; D | π) = 0

Utility depends on policy, not on mechanism.
(Fair problems)

### For the Dynamics Latent

**Condition 6: Dynamics determine policy**
H(π | D) = 0

The dynamics (mechanism) fully specifies the policy.
(The policy isn't additional - it's entailed by D)

---

## Layer 5: The Representation Theorem

### Statement (Condensation-Informed)

**Given:**
- Agency latent variable model L_agency for behavior M
- Conditions 1-6 hold
- The agent is rational: π maximizes E[U | π]

**Then:**
For each observation o:
$$\pi(o) = \arg\max_a \mathbb{E}[U \mid \pi(o) = a]$$

### Proof Sketch

1. By Condition 6, π is determined by D (mechanism)
2. By Conditions 1-3, π is a well-defined unified latent
3. By Condition 4, U depends on π
4. By Condition 5, U depends ONLY on π (not other aspects of D)
5. By rationality, π maximizes E[U]
6. At each o, π(o) must be optimal given the rest of π
7. This is the UDT formula: choose a that maximizes E[U | π(o) = a]

### The Correspondence Version

**If L₁ and L₂ are both good agency attributions for M:**
- Both have policies π₁, π₂ satisfying Conditions 1-5
- Both are rational

**Then:** π₁ ≈ π₂ (they agree on the policy)

**This is intersubjectivity:** Different observers attribute the same agency.

---

## Layer 6: Computational Realization

### The Problem

The theorem assumes we can:
- Evaluate E[U | π(o) = a]
- Search over policies to find optimal π
- Know our own policy

Under logical uncertainty, none of these are trivial.

### Diffractor's Solution: UDT1.01

**Setup:**
- Plannable observations h (the formal policy domain)
- Unplanned observations S_h (epistemic state at h)
- Algorithm A that uses S_h to compute action at h

**UDT1.01:**
```
At plannable h with epistemic state S̄_h:
  a* = argmax_a f⁰_{h,S̄_h}(a)
```

Where f⁰ encapsulates:
- Expected utility contribution
- Retrocausal effects (how action affects probabilities)
- Acausal effects (how action correlates with other situations)

### Why UDT1.01 Is Correct

**Theorem (Diffractor):** For any metapolicy and plannable h:
- "Current policy + ε more UDT1.01" ≥ "Current policy + ε more A"
- For any algorithm A

**Interpretation:** UDT1.01 is the universally locally optimal algorithm.

### Connection to the Representation Theorem

The representation theorem says: Given unified agency, π(o) = argmax_a E[U | π(o) = a]

UDT1.01 approximates this:
- Uses S̄_h to estimate E[U | ...]
- The f⁰ function captures the conditioning correctly
- Computational tractability through gradient ascent in policy space

---

## Layer 7: The Multi-Agent Interpretation

### Instances as Separate Minds

Under logical uncertainty:
- Instance (h, S) has plannable location h and epistemic state S
- Different S = different beliefs = different "minds"

**The multi-agent view:** Instances are genuinely separate agents who must coordinate.

### The Contract

**The "prior" as social contract:**
- All instances agree to act as if prior P is correct
- Even if local beliefs differ
- This is the arbitration mechanism

**The "algorithm" as shared commitment:**
- All instances agree to run UDT1.01
- This ensures coordination despite epistemic divergence

### Non-Interference

**Respect for epistemic autonomy:**
- Instance (h, S) doesn't override (h', S')
- Each instance uses its own S
- Coordination through shared algorithm, not through control

**This is the self-trust condition:** Unified agents don't prefer to modify themselves.

### Radical Probabilism

**Updates as changes of mind:**
- S can change in ways not forced by evidence
- This is OK - the contract handles it
- You follow UDT1.01 regardless of how your beliefs change

**Stability:** The algorithm is stable under radical updating.

---

## Putting It Together

### The Full Stack

```
Observable: Behavior X_i = (O_i, A_i) across situations i
    ↓ [introduce latent structure]
Latent: Policy π, Utility U, Dynamics D
    ↓ [check condensation conditions]
Condensation: Conditions 1-6 hold
    ↓ [apply representation theorem]
Theorem: π(o) = argmax_a E[U | π(o) = a]
    ↓ [handle computational limits]
Algorithm: UDT1.01 approximates this
    ↓ [handle logical uncertainty]
Multi-Agent: Instances coordinate through shared algorithm
```

### What Each Layer Contributes

**Condensation:** When are latent variables "real"? What makes agency attribution appropriate?

**C&T Framework:** The structure of agent/environment decomposition. Internal vs external, semantic vs side channel.

**Diffractor:** How to compute updatelessly under uncertainty. Plannable vs unplanned, the UDT1.01 algorithm.

**Radical Probabilism:** How to handle epistemic changes. The contract interpretation, multi-agent coordination.

### The Unified Insight

**Updateless reasoning isn't a choice.** It's forced by:
1. The latent structure of unified agency (condensation)
2. The rationality constraint (maximize E[U])
3. The decision-determination condition (U depends on π)

**UDT1.01 isn't arbitrary.** It's the computable approximation to the forced structure.

**The multi-agent view isn't metaphorical.** Under logical uncertainty, instances ARE separate minds, and UDT1.01 is what makes them coordinate.

---

## Open Problems

### Formal

1. Make the condensation conditions for agency fully precise
2. Prove the correspondence theorem for agency (different attributions agree)
3. Show UDT1.01 satisfies the condensation conditions approximately

### Conceptual

1. When exactly does agency attribution fail?
2. What's the status of the utility latent?
3. How do approximate condensation conditions propagate through the stack?

### Technical

1. Integrate the C&T side channel with Diffractor's framework
2. Handle dynamic observation spaces (changing actions/observations)
3. Connect to InfraBayes / non-Bayesian settings

---

## Summary

**The unified framework:**

1. **Observables:** Behavior across situations
2. **Latents:** Policy, utility, dynamics (agency attribution)
3. **Conditions:** Condensation conditions for agency
4. **Theorem:** Conditions + rationality → updateless reasoning
5. **Computation:** UDT1.01 approximates the theorem
6. **Uncertainty:** Multi-agent view with contract coordination

**The key insight:** Each layer constrains the next. The structure of good agency attribution forces updateless reasoning, just as condensation forces correspondence.
