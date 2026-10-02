# The Burden of Proof Argument

## The Question

The question: [scrubbed]

The implicit assumption is that the default is to treat each decision point separately, and grouping requires justification.

**Thesis:** This gets the burden of proof backwards. The default model of an agent is a single optimizer. Splitting into separate decision points is the move that requires justification.

## The Argument

### Step 1: Agency Attribution Comes First

When we recognize something as an agent, we first recognize the WHOLE - an entity with goals, acting in the world.

We don't first see a collection of decision points and then ask "should we group these?" We see an agent and then analyze its behavior at different times.

The agent is conceptually prior to the decision moments.

### Step 2: The Default Model is a Single Optimizer

Given that we've identified an agent with utility U, the simplest model is:

> The agent maximizes E[U].

This is one optimization. The agent takes all its actions to maximize expected utility.

### Step 3: Splitting Requires Structure

To split this into separate optimizations (one per decision point), we need additional structure:

- What defines the boundary between decision points?
- How are the separate optimizations related?
- Why do they have the same utility function?
- How do they handle coordination?

The updateful model requires answers to all these questions. The updateless model doesn't.

### Step 4: Therefore, the Burden is on the Splitter

The person who wants to analyze decisions separately bears the burden of:
1. Justifying the split
2. Providing the additional structure
3. Explaining why this is better than the default single-optimizer model

## Why This Matters

The opposing model: decision points are primitive, grouping is a choice.

The counter-model: agents are primitive, splitting is a choice.

If we accept the counter-model, then the question "why group?" is backwards. The right question is "why would you split?"

And the answer to "why split?" seems to be: you wouldn't, unless forced to for computational reasons.

## The EDT Response

EDT might respond: "But we ARE considering individual decisions. That's what decision theory is about."

**Counter:** What makes something a "decision" in the first place?

A decision is a choice made by an agent. The agent-nature of the decision is built into the concept. You can't have a "decision" without a decider.

And if the decider is an agent spanning multiple times, then the decision is part of that agent's policy. It's not a separate thing.

## The "Space Cadet" Response

Academic DT might respond: "We want to advise on THIS decision, right now, for any possible agent."

**Counter 1:** Advice-following should be equivalent to self-choosing. If Omega can predict advice-following, then the advice is part of the decision procedure, not external to it.

**Counter 2:** Even for "non-normative" agents, we can still model them as agents. The question is what a good agent would do, which requires the agent structure.

**Counter 3:** If we really want to advise arbitrary space cadets with no agent structure, then decision theory as traditionally understood doesn't apply. We're in the "piece of paper" regime where type signatures break down.

## The Epistemic State Response

Sophisticated EDT might respond: "We start with an epistemic state. From the epistemic state, we derive what to do."

**Counter 1:** An epistemic state underspecifies a decision problem. You need counterfactual structure, algorithmic structure, etc.

**Counter 2:** Where does the epistemic state come from? From the agent's experience. The agent is prior.

**Counter 3:** The "epistemic state" framing treats beliefs as external to agency. But an agent's beliefs are part of its agency - they're how it represents the world in order to act.

## Connection to Representation Theorems

Traditional representation theorems (VNM, Savage, Jeffrey-Bolker) take preferences as input and derive utility/probability as output.

A representation theorem for UDT should take AGENCY as input and derive updateless reasoning as output.

**Input:** X is a single agent with utility U, facing multiple situations.

**Output:** X reasons updatelessly: at each situation, X chooses the action that is part of the globally optimal policy.

The key is that "single agent" is doing the work. If you deny that X is a single agent, then the theorem doesn't apply. But then you're not doing decision theory for X - you're doing decision theory for the separate pieces.

## The Formal Version

**Axiom (Single Agent):** We model X as a single optimizer with utility U.

**Axiom (Multiple Situations):** X appears in situations s1, s2, ... with observations o1, o2, ...

**Axiom (Same Agent):** It's the same X in each situation - same utility, same decision procedure.

**Claim:** These axioms, properly formalized, imply updateless reasoning.

**Proof Sketch:**
- X is a single optimizer (Axiom 1)
- X's actions in all situations are outputs of this single optimization (Axiom 3)
- Therefore, X optimizes the whole policy, not individual actions
- This is updateless reasoning.

The key step is: "single optimizer" means ONE optimization, not many optimizations that happen to share a utility function.

## Why This Should Satisfy the Demand for a Justification

[scrubbed] This argument says: grouping is the default when you're modeling an agent. Splitting is the thing that requires justification.

If one accepts that decision theory is about agents (not about floating decisions), then one should accept that the agent structure is prior to the decision structure.

And if the agent structure is prior, then the agent's optimization is a single optimization spanning all its situations. That's updateless reasoning.

## Remaining Questions

1. **What exactly is the "agent structure"?** The I/B/E decomposition? Functional identity? Something else?

2. **Can we formalize "single optimizer" precisely?** The informal argument is clear, but the formal version needs work.

3. **What if the agent doesn't know it's the same agent in all situations?** (Imperfect self-knowledge)

4. **What if we're modeling an agent that really IS split?** (Multiple personality, etc.)

These are important but don't undermine the main argument: for unified agents, updateless reasoning is the default.
