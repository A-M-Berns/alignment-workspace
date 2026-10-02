# The Core Argument: From Agency to Updateless Reasoning

## Abstract

This note presents the core argument for a representation theorem for Updateless Decision Theory (UDT). The argument proceeds in four steps:

1. **Agency as modeling:** When we attribute agency to a system X with utility U, we are making a modeling choice - predicting X's behavior via "X optimizes U" rather than via mechanism.

2. **Unity of agency:** If we attribute the SAME agency across multiple situations, we are modeling X as a SINGLE optimizer, not as multiple independent optimizers.

3. **Single optimization implies policy thinking:** A single optimization over multiple situations naturally evaluates policies (complete specifications of what to do in each situation), not individual actions in isolation.

4. **Policy thinking is updateless reasoning:** Evaluating policies as wholes leads to the UDT decision formula: at each situation, choose the action that is part of the globally optimal policy.

The key claim is that steps 1-3 are just unpacking what "single agent with utility U" means. UDT is not an additional assumption; it's what coherent agency attribution implies.

---

## Step 1: Agency as Modeling

To say "X is an agent with utility U" is to make a modeling choice.

**Mechanistic model:** Given X's physical constitution, predict what X will do.

**Teleological model:** Given X's goals (utility U), predict what X will do - namely, whatever maximizes U.

Agency attribution = commitment to the teleological model being appropriate for X.

This doesn't require X to "really" have goals in some metaphysical sense. It requires that the teleological model predicts X's behavior well.

**Key point:** The I/B/E decomposition (Interior/Boundary/Environment) is not a property of X itself. It's a property of how we're modeling X. We draw the boundary where the teleological model applies.

---

## Step 2: Unity of Agency

Suppose we attribute the same utility U to X in situations s1 and s2.

**Question:** Are we modeling one agent, or two?

**One agent:** X-in-s1 and X-in-s2 are the same optimizer, appearing in different circumstances.

**Two agents:** X-in-s1 and X-in-s2 are separate optimizers who happen to share a utility function.

If we say "one agent," then we're committed to a SINGLE optimization spanning both situations.

If we say "two agents," then we need to explain:
- What makes them "the same" in any sense?
- How do they relate to each other?
- Why do they have the same utility function?

The "one agent" model is simpler. It requires no additional structure beyond "X optimizes U."

The "two agents" model requires extra machinery to connect the agents. This is additional complexity that needs justification.

**Thesis:** The default, when attributing agency across situations, is "one agent." Splitting into multiple agents requires justification.

---

## Step 3: Single Optimization Implies Policy Thinking

If X is a single optimizer appearing in multiple situations, what is X optimizing?

**Option A: Individual actions.** X optimizes "what to do in s1", then separately optimizes "what to do in s2."

**Option B: The policy.** X optimizes "what to do in each situation" - a complete plan covering all situations.

Option A is the "two agents" model in disguise. If X-in-s1 and X-in-s2 optimize separately, they are separate optimizers.

Option B is what "single optimizer" means. One optimization produces one answer - a policy.

**The policy is the natural unit of analysis for a single agent spanning multiple situations.**

This doesn't mean the agent computes the entire policy at once. It means: when evaluating an action in situation s, the relevant question is "what policy should I have, and what does that policy say for s?"

---

## Step 4: Policy Thinking is Updateless Reasoning

If the agent evaluates policies, how does it evaluate them?

**Standard answer:** Expected utility. Policy pi is evaluated by E[U | policy = pi].

**At each situation:** The agent chooses the action a that is part of the optimal policy.

**The UDT formula:** a* = argmax_a E[U | pi(s) = a, pi is optimal elsewhere]

For a coherent agent with a single policy, this simplifies to:

a* = argmax_a E[U | pi(s) = a]

This is the UDT decision rule: condition on "my policy maps this situation to action a," not on "I take action a in this particular situation."

---

## The Contrast with Updateful Reasoning

Updateful reasoning (EDT, CDT) conditions on "I am in situation s and I take action a."

This is appropriate if:
- s is a primitive, separate from other situations
- The action in s is independent of actions in other situations

But if X is a single agent, then:
- s is one appearance of X among many
- X's action in s is part of X's policy, which also determines actions elsewhere

Conditioning on "I am in s and I take a" ignores the policy structure. It treats s as if it were separate from other situations.

For a unified agent, this is the wrong level of analysis.

---

## Why This Isn't Circular

**Worry:** We defined "single agent" to mean "policy optimizer," then derived that single agents optimize policies. Isn't this circular?

**Response:** The claim is that "single agent" and "policy optimizer" mean the same thing - that's the representation theorem.

The non-trivial content is:
1. There's a natural concept (single agent with utility U)
2. This concept has determinate implications (updateless reasoning)
3. Other decision theories (EDT, CDT) implicitly deny the unity

The theorem doesn't CREATE the connection between agency and updatelessness. It REVEALS the connection that was always there.

---

## Decision-Determination as Scope Restriction

The above argument applies when the environment responds to policies, not to internal mechanisms.

**Decision-determination:** U depends only on the environment E, and E depends only on the agent's policy pi, not on how pi is computed.

This is a "fairness" condition. In unfair problems (where the environment discriminates based on mechanism, not behavior), any decision theory can be punished.

The claim is: in fair (decision-determined) problems, unified agents reason updatelessly.

This is the appropriate scope for the representation theorem.

---

## Implications

**For reflective stability:** Unified agents in fair problems don't prefer to self-modify. They're already choosing the optimal policy; any modification would be to a suboptimal policy.

**For coordination:** Unified agents with functional identity (same algorithm in multiple instances) automatically coordinate. Their actions are outputs of the same policy, so they're correlated by necessity.

**For decision theory:** UDT is not a competitor to EDT/CDT at the same level. UDT is what happens when you take the concept of "single agent" seriously. EDT/CDT arise when you DON'T take this concept seriously - when you treat decision points as primitive and separate.

---

## Remaining Work

1. **Formalize "single agent"** - what exactly does this mean mathematically?

2. **Formalize "policy"** - connect to the observation/action structure

3. **Prove the theorem** - show that the axioms imply the UDT formula

4. **Handle edge cases** - ties, probability-zero actions, etc.

5. **Connect to the I/B/E framework** - how does the paper's machinery relate to this argument?

---

## Summary

The core argument:

1. Agency attribution models X as an optimizer
2. Same agency across situations = one optimizer = one policy
3. One policy means evaluate policies, not isolated actions
4. Evaluating policies gives updateless reasoning

**UDT is not an additional assumption. It's what "single coherent agent" means.**
