# Formal Representation Theorem Attempt

## Inspiration from Classical Representation Theorems

**Von Neumann-Morgenstern:** Axioms on preferences over lotteries -> EU maximization
**Savage:** Axioms on preferences over acts -> SEU with subjective probabilities
**Jeffrey-Bolker:** Axioms on preferences over propositions -> Expected desirability

**Desired (UDT):** Axioms on ??? -> Updateless expected utility maximization

## What are we axiomatizing?

Options:
1. Preferences over policies (rather than actions)
2. Preferences over actions, plus structural constraints
3. Beliefs about self, plus rationality constraints
4. Properties of the decision problem, plus optimization

I'll try option 4: start with a decision problem satisfying certain properties, then show that an optimizer in such a problem must reason updatelessly.

---

## The Formal Setup

### Decision Problems

**Definition.** A **decision problem** is a tuple D = (Omega, P, O, A, U) where:
- Omega is a set of world-states (possible worlds)
- P is a probability distribution on Omega
- O: Omega -> O is an observation function (what the agent observes)
- A: Omega -> A is an action function (what the agent does)
- U: Omega -> [0,1] is a utility function

We interpret this as: the agent is situated in a world omega. It observes O(omega). It takes action A(omega). Its utility is U(omega).

### Policies

**Definition.** A **policy** is a function pi: O -> A.

### Policy-Compatibility

**Definition.** A decision problem D is **policy-compatible** if for each policy pi, there exists a probability distribution P_pi on Omega such that:
1. P_pi(O = o, A = a) > 0 iff pi(o) = a
2. P_pi marginalizes correctly: for all o, P_pi(O = o) = P(O = o)

Interpretation: P_pi is "what the world looks like if the agent follows policy pi."

Condition 1 says the policy is implemented. Condition 2 says observations don't depend on the policy.

### Decision-Determination

**Definition.** A decision problem D is **decision-determined** if:
1. The environment's response depends only on the policy: for any two policies pi, pi' with the same external actions, P_pi(E | O) = P_pi'(E | O).
2. Utility depends only on the environment: U is a function of E.

(Here E is the "environment" random variable, defined as everything outside the agent.)

### Agent's Problem

Given a decision-determined, policy-compatible problem D, the agent wants to choose a policy pi maximizing E_P_pi[U].

**Key observation:** This is updateless reasoning. The agent chooses a whole policy, not individual actions.

---

## The Representation Theorem

### What we want to show

If an agent:
1. Faces a decision-determined, policy-compatible problem
2. Is coherent (doesn't have contradictory preferences)
3. Treats itself as a single agent (unity)

Then the agent's behavior can be represented as: for each observation o, choose the action that is part of the globally optimal policy.

### Axioms

**Axiom 1 (Coherence).** For each observation o, the agent has a preference ordering >=_o over actions in A. This ordering is complete and transitive.

**Axiom 2 (Policy Preference).** The agent also has a preference ordering >= over policies in O -> A. This ordering is complete and transitive.

**Axiom 3 (Unity).** For all o and all a, a' in A:
   a >=_o a' iff (for any policy pi' with pi'(o) = a', there exists a policy pi with pi(o) = a such that pi >= pi')

Interpretation: action a is preferred at o iff it's part of some policy that's at least as good as any policy using a'.

**Axiom 4 (Optimization).** Policy preference is determined by expected utility:
   pi >= pi' iff E_P_pi[U] >= E_P_pi'[U]

**Theorem.** Under Axioms 1-4, the agent's local preferences are determined by:
   a >=_o a' iff E_P[U | pi(o) = a] >= E_P[U | pi(o) = a']

where the conditional is understood as: the expected utility given that the policy maps o to a.

### Proof sketch

By Axiom 4, pi >= pi' iff E_P_pi[U] >= E_P_pi'[U].

By Axiom 3, a >=_o a' iff there's a best-possible policy containing a that's at least as good as any policy containing a'.

Consider the best policy containing a, call it pi_a. And the best policy containing a', call it pi_a'.

If pi_a >= pi_a', then a >=_o a'.
This happens iff E_P_{pi_a}[U] >= E_P_{pi_a'}[U].
By policy-compatibility and decision-determination, this equals E[U | best policy containing a] vs E[U | best policy containing a'].

This is approximately the UDT formula, but we need to be more careful...

**Issue:** The proof is getting complicated because we're comparing "best policy containing a" vs "best policy containing a'", rather than directly computing E[U | pi(o) = a].

---

## Alternative: More Direct Approach

### Axiom 1' (Single Policy).**
There exists a policy pi such that for all o, the agent chooses pi(o).

### Axiom 2' (Optimality).**
The policy pi maximizes E_P_pi[U] over all policies.

### Axiom 3' (Local Consistency).**
For each o, pi(o) = argmax_a E_P[U | policy pi maps o to a, and pi is optimal elsewhere].

**Theorem.** Under Axioms 1'-3', we have:
   pi(o) = argmax_a E_P[U | pi(o) = a]

### Proof

By Axiom 2', pi is optimal. This means: for any alternative policy pi', E_P_pi[U] >= E_P_pi'[U].

Consider pi' that differs from pi only at o, with pi'(o) = a' ≠ pi(o).

By optimality, E_P_pi[U] >= E_P_{pi'}[U].

This is equivalent to: E[U | pi(o) = pi(o)] >= E[U | pi(o) = a'], using the policy-compatibility condition.

So pi(o) maximizes E[U | pi(o) = a] over all a.

This is the UDT formula. QED.

---

## Is This Trivial?

The "theorem" above feels almost tautological. We assumed the agent chooses an optimal policy, and derived that each action maximizes expected utility conditional on the policy.

But maybe that's the point? The claim is: "coherent single agent" MEANS "updateless reasoner."

The theorem makes this equivalence precise.

### What's non-trivial

The non-trivial part is in the setup:
- Decision-determination (fairness)
- Policy-compatibility (the structure of how actions affect the world)
- The interpretation of "E[U | pi(o) = a]" as conditioning on algorithmic/policy properties, not local facts

These structural assumptions are doing the work. Given them, updateless reasoning follows naturally.

---

## Connection to Reflective Stability

The original goal was to connect this to self-trust (reflective stability).

**Claim:** An agent satisfying the above axioms is reflectively stable in decision-determined problems.

**Argument:** The agent chooses pi optimal. If given the chance to modify itself to choose a different policy pi', the agent prefers pi (by optimality). So no self-modification.

**But wait:** Self-modification opportunities might not be "decision-determined." The environment might treat a self-modifying agent differently from a non-self-modifying one.

This is where the paper's more careful treatment is needed. The paper defines:
- Internal vs external actions
- Communication as a substitute for self-modification
- Conditions under which self-modification is never strictly preferred

---

## Next Steps

1. Clean up the theorem statement to make the non-trivial content clearer
2. Explicitly state what "E[U | pi(o) = a]" means (the conditioning is the key)
3. Show how the theorem implies reflective stability under appropriate conditions
4. Reconnect to the I/B/E framework and instances/communication structure
5. Address the examples (Coordinated Buttons, Third Button)

---

## Reflection on Progress

The representation theorem is taking shape, but the current version feels too simple - it essentially defines a single-agent optimizer as an updateless reasoner.

The more interesting question is: why should we model things this way? What justifies:
- Policy-compatibility
- Decision-determination
- The "single policy" assumption

The arguments from earlier (parsimony, functional identity, agency-as-modeling) are supposed to justify these choices. The formal theorem then just makes the definitions precise.

So the full picture is:
1. Arguments for why agency attribution should have certain properties (conceptual/philosophical)
2. Formal axioms capturing those properties
3. Theorem: axioms imply updateless reasoning
4. Corollary: agents satisfying axioms are reflectively stable

The novelty is in (1) and how it connects to (2), not in (3) alone.
