# Formalizing "Single Agent": The Mathematical Core

## The Challenge

The core argument says: if you model X as a *single agent*, updateless reasoning follows.

But what exactly does "single agent" mean mathematically? We need a definition that:
1. Is independently motivated (not circular with UDT)
2. Captures the intuitive concept of unified agency
3. Has determinate formal consequences (implies UDT)

## Starting Point: Situations and Behaviors

**Definition.** A **multi-situation decision problem** is a tuple (S, P, A, U) where:
- S is a finite set of **situations** (decision points the agent might face)
- P is a probability distribution over S (which situation obtains)
- A is a finite set of **actions** available at each situation
- U: S × A → ℝ is a **utility function**

Note: We're being deliberately agnostic about what "situations" are. They could be:
- Different times
- Different possible worlds
- Different copies of the agent
- Different observations

The key is that an agent might face *any* of these situations and must choose an action.

## Approach 1: Split Model (Multiple Optimizers)

**Definition.** A **split decision procedure** is a family of functions {D_s : s ∈ S} where each D_s chooses an action for situation s.

Under the split model:
- Each D_s optimizes independently
- D_s chooses a_s = argmax_a E[U(s, a) | s obtains]
- The D_s's might share a utility function, but they optimize separately

**Key property:** D_s's choice depends only on what's optimal *given s obtains*. It ignores other situations.

## Approach 2: Unified Model (Single Optimizer)

**Definition.** A **unified decision procedure** is a single function D: S → A choosing an action for each situation.

Under the unified model:
- There's ONE optimization
- D is chosen to maximize E[U(s, D(s))] = Σ_s P(s) · U(s, D(s))
- Each D(s) is part of a globally optimal *policy*

**Key property:** D(s) is chosen considering how the choice affects total expected utility, not just utility in situation s.

## Why These Are Different

In many problems, the split and unified approaches give the same answer. But they diverge when:

**Condition C:** The environment's response to the agent depends on the *pattern* of actions across situations, not just the action in the current situation.

Under Condition C:
- U(s, a) might depend on what the agent does in other situations
- The split approach ignores these dependencies
- The unified approach accounts for them

## Formalizing "Pattern Dependence"

**Definition.** A problem has **cross-situation dependence** if there exist situations s ≠ s' and actions a, a' such that:

U(s, a) depends on the action chosen at s'

More precisely: there exists a policy π with π(s) = a and π(s') = a₁, and another policy π' with π'(s) = a and π'(s') = a₂, such that:

E[U | π] ≠ E[U | π'] despite agreeing on action at s

This happens when "what you do elsewhere" affects "what happens here."

## The Core Theorem

**Theorem (Single Agent = Updateless).**
Let D be a decision problem with cross-situation dependence. If an agent:
1. Treats all situations as "itself" (unity)
2. Aims to maximize expected utility (rationality)
3. Recognizes the cross-situation dependence (awareness)

Then the agent reasons updatelessly: for each s, it chooses the action that is part of the globally optimal policy.

**Proof sketch:**
- By (1), the agent views S as situations it might face as a single entity
- By (2), it wants to maximize E[U]
- By (3), it recognizes that U depends on the full policy, not just local actions
- Therefore, it chooses a policy π maximizing E[U(s, π(s))]
- At each s, it implements π(s)

## Why the Split Model Violates Unity

If an agent uses the split model, it's implicitly treating each D_s as a separate decision-maker.

**Argument:** D_s, optimizing independently, asks: "What should *I* do, given that situation s obtains?"

This question treats s as primitive and separate. It doesn't ask: "What should *the agent* do across all situations?"

If the agent is truly unified, there's no "I" at situation s separate from the agent as a whole. The question "what should I do at s?" is really "what should the agent's policy say for s?"

## The Burden of Proof (Formalized)

**Claim:** The unified model is the *default* when attributing agency. The split model requires additional structure.

**Formal version:** Given a utility function U over situations and actions, the simplest model is a single optimization:

max_π E[U(s, π(s))]

The split model requires specifying:
- What defines the boundaries between D_s's
- How the D_s's are related
- Why they share a utility function but not an optimization

These are additional modeling choices beyond the basic agency attribution.

## Connection to Functional Identity

**Functional identity** provides one way to justify unity formally:

**Definition.** An agent has **functional identity** if all instances (situations) are outputs of the same algorithm F: O → A, where O is the observation space.

**If functional identity holds:** When the agent asks "what should I do at observation o?", the answer is F(o). Since F is fixed, this answer is part of a complete policy. Changing F(o) means changing F, which changes all outputs.

**Consequence:** An agent with functional identity cannot coherently ask "what should I do at o?" in isolation. Its action at o is part of its global algorithm F.

## The Conditioning Interpretation

The split vs. unified distinction maps to conditioning:

**Split (EDT-style):** E[U | s obtains and I take action a]

**Unified (UDT-style):** E[U | my policy maps s to a]

The difference:
- Split conditions on being-in-situation-s as a separate fact
- Unified conditions on having-a-policy-that-says-a-for-s

For a unified agent, "being in situation s" isn't separate from "having a policy." The agent's policy IS its global behavior, of which the current situation is one instance.

## When Do Split and Unified Agree?

**Theorem.** Split and unified reasoning agree when there's no cross-situation dependence.

**Proof:** If U(s, a) depends only on s and a (not on actions at other situations), then:

max_π Σ_s P(s) · U(s, π(s)) = Σ_s P(s) · max_a U(s, a)

The global optimization decomposes into independent local optimizations.

**Interpretation:** When situations are truly independent, treating them separately is fine. The split model is a special case of the unified model when cross-situation dependence is absent.

## Decision-Determination Revisited

**Decision-determination** is the condition that makes cross-situation dependence "fair":

**Definition.** A problem is **decision-determined** if:
1. The environment responds to policies (which actions are taken in each situation)
2. Not to the internal mechanism (how the policy is computed)

Under decision-determination, cross-situation dependence arises from how the environment responds to behavior, not from discrimination based on internals.

**Claim:** In decision-determined problems, unified reasoning is unambiguously correct for unified agents.

## Summary: The Formal Core

1. **Multi-situation problems** involve an agent facing multiple situations
2. **Split model:** Optimize each situation independently → EDT-style reasoning
3. **Unified model:** Optimize the whole policy → UDT-style reasoning
4. **The models differ** when there's cross-situation dependence
5. **Unity (being a single agent)** = treating situations as parts of one entity's behavior
6. **Unified agents in problems with cross-situation dependence** must reason updatelessly
7. **This is the representation theorem:** single agent + cross-situation structure → UDT

## What's Non-Trivial

The representation theorem is:
- **Trivial** if we define "single agent" as "unified optimizer" (circular)
- **Non-trivial** if we motivate "single agent" independently and derive unification

The independent motivation comes from:
- Agency as modeling (the agent is ONE entity we're predicting)
- Functional identity (same algorithm across instances)
- Parsimony (simpler model than split)
- Burden of proof (splitting requires justification)

These motivations are *prior* to the decision theory debate. We'd accept them even before considering Newcomb problems.

---

## Open Questions

1. **Observations vs situations:** How does observation structure (imperfect information) fit in?

2. **Ties:** What if multiple policies are equally optimal?

3. **Logical uncertainty:** What if the agent doesn't know its own policy?

4. **Approximate unity:** What if the agent is "mostly" unified but not perfectly?

5. **Causal structure:** How does this relate to causal vs. evidential decision theory debates?
