# The Decision-Determination Argument for Updateless Reasoning

## Core Idea

If a problem is "decision-determined" (the environment only cares about your external policy, not your internal constitution), then **policies** are the natural unit of analysis, not individual actions. And if policies are the natural unit, you should evaluate them as wholes, which leads to updateless reasoning.

## Setup

**Decision-Determination (from the paper):**
1. Utility depends only on the external environment E
2. E is conditionally independent of the agent's internal state given the external policy

In other words: the universe doesn't care *how* you compute your policy, only *what* it is.

## The Argument

### Step 1: Policies are the "natural" unit

In a decision-determined problem, two agents with the same external policy get the same outcomes (in distribution). The environment can't distinguish them.

This means: from the perspective of predicting outcomes, a policy is a complete description of "what the agent does." Individual actions matter only insofar as they're part of a policy.

### Step 2: Evaluating policies requires considering all instances

A policy pi: O -> A specifies what to do at *every* possible observation. When I ask "how good is policy pi?", I'm asking about its performance across all situations where it might be applied.

This is naturally updateless: I'm not asking "how good is pi given that I'm at observation o?" I'm asking "how good is pi overall?"

### Step 3: The decision at each observation should reflect whole-policy evaluation

If the natural unit is the policy, then when I'm at observation o deciding what to do, I should ask: "What policy do I want to have? And what does that policy say at o?"

This is exactly updateless reasoning.

## Comparison: What does updateful reasoning look like?

An updateful agent at observation o asks: "Given that I'm at o, what action maximizes expected utility?"

The conditioning on "I'm at o" implicitly treats the current observation as special. But in a decision-determined problem, there's nothing special about any particular observation - the policy is what matters.

Updateful reasoning breaks the symmetry between observations that decision-determination establishes.

## Formalization Attempt

### Definition: Policy-Centric Agency

An agency attribution is **policy-centric** if the agent's decision at each observation o can be described as:
1. Evaluating policies pi on the basis of E[U | external-policy = pi]
2. Selecting an optimal policy pi*
3. Outputting pi*(o)

### Theorem (Desired)

In decision-determined problems, policy-centric agency is equivalent to UDT.

### Proof Sketch

UDT: pi(o) = argmax_a E[U | pi(o) = a]

This conditions on "my policy maps o to a" rather than "I take action a at observation o."

If we're evaluating whole policies, the expected utility of policy pi is:
E[U | external-policy = proj(pi)]

where proj(pi) is the projection of pi to external actions.

The policy that maximizes this is the UDT policy, because UDT at each observation o selects the action that would be part of the best whole policy.

## The Remaining Gap: Why be policy-centric?

This argument shows: IF you evaluate policies as wholes, THEN you reason updatelessly.

But why should you evaluate policies as wholes?

**Answer 1 (from decision-determination):** Because in fair problems, policies are the only thing that matter. Individual actions have no causal power except through their contribution to the policy.

**Answer 2 (from reflective stability):** If you evaluate actions locally, you can end up with a policy that no part of you endorses as a whole. This is a form of incoherence.

**Answer 3 (from agency attribution):** When we attribute a single agency across situations, we're committing to a unified policy. The unity of the agent implies unity of policy evaluation.

## Implications for the Representation Theorem

The axioms might look like:

1. **Agency Attribution:** A system X is attributed utility U, boundary B, observations O, actions A

2. **Decision-Determination:** The environment E is conditionally independent of X's internals given the external policy

3. **Unified Agency:** The attribution treats X across all observations as a single agent (not independent agents who happen to share goals)

4. **Optimization:** X's policy maximizes expected utility

Then: X must reason updatelessly.

The key is axiom 3: what does "unified agency" mean formally?

## Unified Agency: First Attempt

**Definition:** An agency attribution has **unified agency** if there exists a single policy pi such that the agent's action at each observation is pi(o).

This is too weak - it's just saying the agent is deterministic given the observation.

**Definition (Attempt 2):** An agency attribution has **unified agency** if the agent evaluates the quality of its action at each observation by evaluating the quality of the whole policy that action is part of.

This is closer but circular - it just says the agent is policy-centric.

**Definition (Attempt 3):** An agency attribution has **unified agency** if changing the agent's behavior at one observation is modeled as changing a parameter that also affects behavior at other observations.

This captures: "instances" are not independent. They share something (the policy, the algorithm, the type).

## Connection to the Paper's "Instances"

The paper factors by external observation: each value of Ö defines an instance.

In the unified agency framing, this factorization is justified by decision-determination: the environment's response to observation-o is determined by the action at observation-o.

But the instances are connected by sharing a policy (or algorithm, or decision procedure).

The key tension: instances are independent in what they observe and do, but connected in how they decide.

UDT respects this structure: it evaluates policies while allowing each instance to condition on its local observation.

## Next Steps

1. Formalize "unified agency" properly
2. Show that optimization + decision-determination + unified agency implies updateless reasoning
3. Address the prior: where does P come from?
4. Address logical uncertainty: how does the agent reason about its own algorithm?
