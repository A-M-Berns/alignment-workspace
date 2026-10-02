# Observations, Policies, and the Structure of Agency

## The Question

The formal-single-agent.md document treated "situations" abstractly. But in the original paper, situations are defined by **observations** - what the agent perceives.

How does observation structure fit into the representation theorem?

## From Situations to Observations

**Definition.** An **observation-structured problem** is a tuple (Ω, P, O, A, U) where:
- Ω is a set of possible worlds
- P is a probability distribution on Ω
- O: Ω → Obs is an observation function (what the agent sees)
- A is the set of available actions
- U: Ω → ℝ is utility

The agent observes O(ω) and must choose an action. Different worlds may yield the same observation (imperfect information).

## Policies in Observation-Structured Problems

**Definition.** A **policy** is a function π: Obs → A.

**Key point:** The policy specifies what to do for *each observation*, not each world. Multiple worlds map to the same observation, so the agent can't distinguish them.

## Why Observation Structure Matters

**Claim:** Observation structure is what makes "instances" natural.

An **instance** is "the agent facing observation o." Multiple worlds realize the same instance (those with O(ω) = o).

The agent's policy must give the same action for all worlds with the same observation - that's what having a policy *means* for an informationally-constrained agent.

## The UDT Formula with Observations

For an observation-structured problem, the UDT formula is:

π*(o) = argmax_a E[U | π(o) = a]

where the conditional means: expected utility given that the policy maps observation o to action a.

**Unpacking the conditional:**

E[U | π(o) = a] = Σ_ω P(ω | π(O(ω)) = A(ω)) · U(ω)

where A(ω) is the action taken in world ω, which equals π(O(ω)) by the policy.

Wait, this is getting circular. Let me be more careful.

## Careful Treatment of the Conditional

**Setup:** The agent will choose a policy π. The action in world ω is π(O(ω)).

**The evaluation:** E_π[U] = Σ_ω P(ω) · U(ω, π(O(ω)))

where U(ω, a) is utility in world ω when action a is taken.

**The UDT claim:** For a single coherent agent, the optimal policy satisfies:

For each o: π(o) = argmax_a [E_π[U | O = o] where we fix π(o) = a and optimize π elsewhere]

If the policy is globally optimal, then each component is locally optimal given the rest.

## Cross-Observation Dependence

**Definition.** A problem has **cross-observation dependence** if utility in some worlds depends on actions taken under different observations.

Formally: There exist observations o, o', worlds ω with O(ω) = o, and actions a, a' such that:

U(ω, a) depends on what action would be taken if O(ω) = o'

This happens in:
- **Newcomb problems:** Predictor responds to your policy
- **Coordination problems:** Your copy in another situation responds to your shared algorithm
- **Commitment problems:** Your future self responds to your current credibility

## The Observation-Based Representation Theorem

**Theorem.** In an observation-structured problem with cross-observation dependence:

If the agent:
1. Is unified (same algorithm/policy across all observations)
2. Maximizes expected utility
3. Recognizes the cross-observation dependence

Then the agent's choice at observation o is:

a* = argmax_a E[U | π(o) = a, π optimal elsewhere]

For a coherent agent with a single optimal policy, this equals:

a* = argmax_a E[U | π(o) = a]

This is the UDT formula.

## Connection to Instances in the Original Paper

The paper defines "instances" as the agent facing different observations. Two instances can communicate if they share a common past.

**Reinterpretation:** Instances aren't ontologically separate entities. They're applications of the *same* agency model to different observational contexts.

When we say "instance o and instance o' can communicate," we mean: the agent's policy for o and o' share a common origin - they're both outputs of the same decision procedure.

**Functional identity:** All instances run the same algorithm. So "what instance o does" and "what instance o' does" are logically connected - they're outputs of the same function.

## Why Observations Define Instances

**Claim:** Observations are the natural grain for instances because policies are observation-dependent.

A policy π: Obs → A assigns an action to each observation. The agent can't make finer distinctions (it doesn't know which ω, only which O(ω)).

So "instance at o" = "the application of the agent's policy to observation o."

This is why observation-based factoring is appropriate for agency modeling, not because it's the only possibility, but because it's the finest grain at which the agent can condition.

## Finer and Coarser Grains

**Finer grain (world-level):** We could imagine an agent that conditions on the full world ω, not just O(ω). But this agent has more information than our agent.

**Coarser grain (situation-level):** We could imagine grouping observations into "situations" and only conditioning on situations. But this throws away information the agent has.

**The observation level is natural:** It's the finest grain at which the agent can distinguish circumstances, and therefore the finest grain at which its policy can vary.

## Imperfect Self-Knowledge

What if the agent doesn't know its own observation?

**Example:** Transparent Newcomb. The agent observes whether the big box is empty. But in some versions, the agent might be uncertain about what it observes (confusion, unreliable perception).

**Complication:** If the agent doesn't know its observation, it can't directly implement a policy π: Obs → A. It must reason about what it might be observing.

**Resolution:** The agent reasons: "I'm implementing some algorithm F. Whatever observation I have, I'll do F(o). So my action depends on my observation, even if I'm uncertain about it."

This is still policy-based reasoning - the agent reasons about what policy it's implementing, not about what action to take in isolation.

## The Logical Uncertainty Connection

**Observation:** The agent might not know what its policy IS (even though it implements one).

This is the "logical uncertainty" problem. The agent is uncertain about facts that are, in principle, computable from its own algorithm.

**How UDT handles this:** The agent conditions on "my policy maps o to a" even without knowing what its policy is. It reasons: "If my policy maps o to a, then the expected utility is X. If my policy maps o to a', the expected utility is Y. I should implement whichever policy is better."

The agent doesn't need to know its policy to reason about what it *should* be. It can evaluate hypothetical policies and implement the best one.

## Summary: Observations and the Representation Theorem

1. **Observation structure** defines what the agent can condition on
2. **Policies** are functions from observations to actions
3. **Instances** are applications of the policy to specific observations
4. **Cross-observation dependence** means utility depends on the whole policy
5. **Unified agents** (single policy) in such problems reason updatelessly
6. **The observation level** is natural because it's the agent's finest distinguishable grain

The representation theorem says: at the observation level, unified agents optimize policies, which means conditioning on "my policy maps o to a" rather than on "I'm at o and I take a."

---

## Remaining Questions

1. **Sub-observation structure:** What if there's relevant structure finer than observations (e.g., the agent's internal state)?

2. **Observation-dependent utility:** What if the utility function depends on the observation directly (not just through the world)?

3. **Dynamic observations:** What if the agent receives a sequence of observations and updates its policy over time?

4. **Communication between instances:** How does the paper's communication structure fit with this framework?
