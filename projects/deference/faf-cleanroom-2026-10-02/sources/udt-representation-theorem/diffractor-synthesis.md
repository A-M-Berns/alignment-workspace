# Synthesizing Diffractor's UDT1.01 with the Multi-Agent Framework

## The Key Insight from Diffractor

Diffractor distinguishes:
- **Plannable observations:** Environmental observations you can write a lookup-table policy for
- **Unplanned observations:** Epistemic states, computation outputs, beliefs - things that affect your action but can't be pre-planned

**The fundamental point:** You can't plan for everything. Even computing a good policy requires observing things (like computation outputs) that you didn't plan for.

**The consequence:** Any realistic agent has a "contracted tree" (just plannable observations, what the policy formally covers) and an "expanded tree" (including epistemic states, the actual decision landscape).

## Connection to Radical Probabilism

### Unplanned Observations = Radical Updates

In Diffractor's framework:
- Your epistemic state S_h at plannable location h isn't determined by prior planning
- Different computation paths could give different S_h
- From your past self's view, your epistemic state looks like uncertainty

In radical probabilism:
- Your probability function can change for reasons other than evidence
- You can "change your mind" through reflection, deliberation, computation
- From your past self's view, your current beliefs look like uncertainty

**The connection:** Unplanned observations in UDT1.01 ARE radical probabilist updates. When you observe the output of a long computation, you're not conditionalizing on evidence - you're discovering what you think.

### The Expanded Tree = The Multi-Agent Space

**Diffractor's expanded tree:** All paths (h₁, S₁, h₂, S₂, ...) of interleaved plannable observations and epistemic states.

**Multi-agent view:** Each node (h, S) is an "instance" - an agent with:
- Plannable location h (what environmental situation it's in)
- Epistemic state S (what beliefs/computations it has)

Different instances (h, S) and (h, S') at the same plannable location h but different epistemic states are genuinely different minds that need to coordinate.

### The Contracted Tree = The Contract

**Diffractor's contracted tree:** Just plannable observations h. Policies π: H → A map histories to actions.

**Multi-agent view:** The contracted tree is the "contract" - the specification of behavior that all instances agree to, regardless of their epistemic states.

**The gap:** The contract (contracted tree policy) doesn't fully determine behavior because it doesn't specify how to handle unplanned observations. Instances must use some algorithm to turn their epistemic states into actions.

## UDT1.01 as the Optimal Coordination Algorithm

### Diffractor's Result

For any:
- Metapolicy π (way of assigning algorithms to plannable situations)
- Plannable event h
- Algorithm A (way of using unplanned information)

"π(h) + a little UDT1.01" ≥ "π(h) + a little A"

**Meaning:** No matter your current policy, no matter the situation, you'd always prefer to add more UDT1.01 rather than more of any other algorithm.

### Multi-Agent Interpretation

If all instances agree to run UDT1.01, then:
- Each instance, given its epistemic state, computes the locally optimal action
- "Locally optimal" accounts for retrocausal and acausal effects
- No instance would prefer to deviate to a different algorithm

**This is a coordination equilibrium:** UDT1.01 is the unique algorithm where all instances agree to use it.

### Why UDT1.01 Respects Instance Autonomy

UDT1.01 doesn't require instances to override each other. Instead:
- Each instance uses its own epistemic state
- Each instance computes its own action
- Coordination emerges from all instances using the same algorithm

**The "contract" is to run UDT1.01**, not to output specific actions. This is exactly the "principles over outputs" idea from the earlier documents.

## The "Conservation of Expected Gain" as Non-Interference

### Diffractor's Conservation Principle

UDT1.01 incorporates "conservation of expected gain" - the insight that:
- Your action's expected gain should be evaluated from the prior perspective
- Not from your current epistemic state (which might be biased by selection effects)

### Multi-Agent Reading

"Conservation of expected gain" means:
- Instance (h, S) doesn't just optimize for its current beliefs
- It optimizes for the expected utility across all epistemic states at h
- This respects other instances (h, S') who might have different beliefs

**Non-interference:** Instance (h, S) doesn't try to hijack the policy for its own epistemic state. It acts in a way that's good for all instances at h, weighted by prior probability.

### The Prior as Arbitration

The prior P (over epistemic states, over instances) serves as:
- The weighting for whose interests count
- The "veil of ignorance" perspective
- The arbitration mechanism between instances with different beliefs

**This is the social contract interpretation:** The prior is what all instances agreed to use for arbitration, before they knew what epistemic state they'd have.

## Dynamic Consistency and Radical Updates

### The Problem

With radical probabilist updates:
- Instance-now might disagree with instance-future about what's optimal
- If updates aren't constrained by evidence, anything goes
- How can there be coordination?

### Diffractor's Solution

UDT1.01 incorporates dynamic consistency:
- Your current action should be what your past self would have wanted
- "What your past self would have wanted" = expected utility from prior perspective
- This holds even if your current beliefs differ radically from the prior

### Multi-Agent Reading

Dynamic consistency = respecting the contract:
- Even if you've changed your mind (radical update)
- Even if your current beliefs suggest a different action
- You still act according to the agreed-upon principles

**This is commitment without rigidity:** You're committed to the algorithm (UDT1.01), not to specific outputs. The algorithm can adapt to your epistemic state while still respecting the contract.

## The Plannable/Unplanned Split as Communication Boundary

### Communication via Plannable Observations

Instances at the same plannable location h can "coordinate" because:
- They share h (same environmental situation)
- The policy for h is common knowledge

This is communication through the contracted tree - the formal policy specification.

### Divergence via Unplanned Observations

Instances at the same h but different epistemic states S, S' diverge because:
- Their unplanned observations differ
- They might make different computation-dependent decisions
- From each other's view, the other's decision is uncertain

This is the multi-agent aspect - genuinely different minds.

### UDT1.01 Bridges the Gap

UDT1.01 provides:
- A common algorithm all instances run
- Coordination despite epistemic divergence
- Each instance acts on its own information while respecting the contract

**This is coordination without communication at the unplanned level.** Instances don't need to share their epistemic states - they just need to all run UDT1.01.

## Synthesis: The Complete Picture

### The Multi-Agent Structure

1. **Instances:** Points (h, S) in the expanded tree - plannable location + epistemic state
2. **Different minds:** Instances at same h but different S are genuinely different agents
3. **Shared contract:** Agreement to run UDT1.01 on whatever epistemic state obtains

### The Coordination Mechanism

1. **Prior as arbitration:** The prior P weights different epistemic states
2. **Conservation of expected gain:** Each instance optimizes for the prior-weighted expectation
3. **Dynamic consistency:** Current action = what past-self would have wanted

### The Non-Interference Property

1. **No override:** Instance (h, S) doesn't try to modify other instances
2. **Respect for epistemic autonomy:** Each instance uses its own S
3. **Coordination through algorithm:** Agreement on UDT1.01, not on specific outputs

### The Radical Probabilist Aspect

1. **Epistemic states as radical updates:** S isn't determined by conditionalizing the prior
2. **Changes of mind are OK:** The algorithm handles arbitrary epistemic states
3. **Commitment despite change:** Following UDT1.01 even when your beliefs suggest otherwise

## Implications for the Representation Theorem

### Updated Theorem Statement

**Axioms:**
1. **Multi-situation structure:** Agent faces plannable observations h
2. **Epistemic uncertainty:** Agent has epistemic states S (unplanned observations)
3. **Common algorithm:** All instances (h, S) agree to run the same algorithm A
4. **Decision-determination:** Environment responds to the contracted-tree policy
5. **Gradient optimality:** A is the universally locally optimal algorithm

**Theorem:** Under these axioms, A = UDT1.01, and the agent's behavior satisfies:
- Dynamic consistency with the prior
- Conservation of expected gain
- No preference for self-modification

### What This Adds

The original representation theorem said: "Single coherent agent → updateless reasoning"

Diffractor's framework adds:
- **How** updateless reasoning works under computational limits (UDT1.01)
- **Why** it's optimal (gradient ascent in algorithm space)
- **What** the commitment structure is (contract on algorithm, not outputs)

### The Radical Probabilist Contribution

The radical probabilist framing adds:
- **Understanding** of epistemic divergence (instances have different minds)
- **Justification** for the prior (social contract, arbitration mechanism)
- **Interpretation** of non-interference (respecting epistemic autonomy)

## Open Questions

1. **What if instances don't all run UDT1.01?** Mixed populations, approximate agreement?

2. **How does learning work?** Diffractor notes UDT1.01 needs strong assumptions. Can they be relaxed?

3. **What about UDT1.1 considerations?** Diffractor lists "coordinating your policy with yourself" as an open problem. How does this fit?

4. **Connection to logical induction:** Diffractor couldn't directly plug in a logical inductor. Why? What's needed?

5. **The InfraBayes generalization:** Diffractor mentions Vanessa's InfraBayes setting. How does this fit the multi-agent picture?

## Summary

**Diffractor's UDT1.01** provides the computational content:
- The plannable/unplanned distinction
- The gradient-ascent derivation
- The specific algorithm and its optimality properties

**The radical probabilist multi-agent framework** provides the conceptual content:
- Instances as different minds
- The contract as coordination mechanism
- Non-interference as respect for epistemic autonomy

**Together:** A picture of agency as a cluster of minds, coordinating through shared principles (the UDT1.01 algorithm), respecting each other's epistemic autonomy, while still achieving updateless behavior.

This is not one agent with one policy, but many agents with shared principles - and the two descriptions are equivalent when the principles are UDT1.01.
