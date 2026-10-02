# Critical Analysis: What Actually Works?

## The Goal

Ruthlessly examine the claims made so far. For each claim:
1. State it precisely
2. Identify problems/gaps
3. Attempt to prove or find counterexamples
4. Be honest about what we know

---

## Claim 1: Agency Attribution is a Latent Variable Model

### The Claim (Informal)
"When we attribute agency, we introduce latent variables: policy π, utility U, etc."

### Attempt at Precise Statement

**Setup:**
- Let Obs be a finite set of observations
- Let Act be a finite set of actions
- Let I be a set of "situations" (indices)
- For each i ∈ I, we observe (O_i, A_i) ∈ Obs × Act

**The Random Variable Model:**
- Ω = (Obs × Act)^I (space of all possible behavior patterns)
- P is a probability distribution on Ω
- X_i : Ω → Obs × Act is the projection onto situation i

**The Latent Variable Model:**
- Λ = (Obs → Act) (space of all policies)
- Q is a probability distribution on Λ (the "prior over policies")
- Y_π : Λ → (Obs → Act) is the identity (the policy random variable)
- Need a map π_map : Λ → Ω connecting policies to behaviors

### Problem 1: What is the map π_map?

A policy π ∈ Λ = (Obs → Act) determines actions GIVEN observations. But it doesn't determine which observations occur!

To get a distribution on Ω from a distribution on Λ, we need:
- A distribution over observations P(O_i)
- Then A_i = π(O_i) deterministically

**So the full model is:**
- P(O_i) : distribution over observations (from environment/situation structure)
- Q(π) : distribution over policies (the latent)
- A_i = π(O_i) : deterministic given policy and observation

**This means:** The latent variable model is really (Λ × Obs^I, Q × P_O), where:
- Λ contributes the policy
- Obs^I contributes the observations
- Actions are determined: A_i = π(O_i)

### Problem 2: What does "situation i" mean?

I've been vague about what I indexes. Options:
1. **Time:** i = timestep t. Then O_i, A_i are the observation/action at time t.
2. **Possible worlds:** i = world ω. Then O_i, A_i are what happens in world ω.
3. **Copies/instances:** i = instance. Then O_i, A_i are what that instance sees/does.

**For the representation theorem, we need:** Situations where the SAME policy applies.

If different situations have different policies, we have multiple agents, not one.

**Definition attempt:** The situations I are the set of observation-contexts where we're applying the same agency model.

### Problem 3: This only makes sense for deterministic policies

If the policy is stochastic (π : Obs → Δ(Act)), then:
- A_i is not determined by (π, O_i)
- We need: A_i ~ π(O_i)

This changes the information-theoretic conditions:
- H(A_i | π, O_i) = H(π(O_i)) (the entropy of the stochastic policy at O_i)
- Not zero unless policy is deterministic

**Resolution:** Focus on deterministic policies first. This is what UDT typically assumes anyway.

### Assessment

The claim "agency attribution is a latent variable model" is **partially valid** but requires:
1. Specifying the observation distribution separately
2. Clarifying what "situations" are
3. Assuming deterministic policies (or being careful about stochastic ones)

---

## Claim 2: The Condensation Conditions Imply Updateless Reasoning

### The Claim (Informal)
"If the agency latent model satisfies condensation conditions, updateless reasoning follows."

### What Are the Condensation Conditions?

From Sam's paper, **perfect condensation** (roughly) means:
- The latent variables "efficiently summarize" the observables
- Formally: certain entropy/information conditions hold

**For agency, I claimed:**
1. H(A_i | π, O_i) = 0 (determination)
2. H(π | (X_i)_{i∈I-{i₀}}) ≈ 0 (redundancy)

### Problem 4: These conditions don't imply updateless reasoning!

Let me check. Suppose:
- There's a prior Q over policies
- Each policy π determines behavior via A_i = π(O_i)
- The conditions hold

**Does it follow that the "rational" π satisfies π(o) = argmax_a E[U | π(o) = a]?**

**No!** The conditions are about information theory, not about optimality.

The conditions tell us:
- The policy determines behavior (condition 1)
- The policy is identifiable from behavior (condition 2)

But they don't say anything about:
- What makes a policy "rational"
- What the utility function is
- How the utility depends on the policy

### Problem 5: What's the actual theorem?

Let me try to state what should be true:

**Claim (revised):** If:
1. The agent has a single policy π (unity)
2. The utility U depends on the policy (cross-situation dependence)
3. The environment responds to the policy, not mechanism (decision-determination)
4. The agent maximizes E[U | π] (rationality)

Then: For each o, π(o) = argmax_a E[U | π(o) = a]

**Is this even non-trivial?**

If π maximizes E[U | π], and we can vary π(o) independently of π(o') for o' ≠ o, then:
- π(o) should be chosen to maximize contribution to E[U | π]
- This is just calculus: ∂/∂π(o) E[U | π] = 0 at optimum

**The question is:** Does this equal argmax_a E[U | π(o) = a]?

### Let's Actually Compute

**Setup:**
- Situations I, observations Obs, actions Act
- Prior P over (situations × observations): P(i, o)
- Policy π : Obs → Act
- Utility U : I × Obs × Act → ℝ (depends on situation, observation, action)

**Expected utility of a policy:**
E[U | π] = Σ_{i,o} P(i, o) · U(i, o, π(o))

**The derivative with respect to π(o₀):**

This is tricky because π(o₀) is discrete. Let's think of it as: what's the difference if we change π(o₀) from a to a'?

E[U | π with π(o₀)=a'] - E[U | π with π(o₀)=a]
= Σ_i P(i, o₀) · [U(i, o₀, a') - U(i, o₀, a)]

**Optimal π(o₀):**
π(o₀) = argmax_a Σ_i P(i, o₀) · U(i, o₀, a)
       = argmax_a E[U(i, o₀, a) | O = o₀]

### This Is NOT the UDT Formula!

The formula I derived is:
π(o) = argmax_a E[U | O = o, A = a]

But the UDT formula is:
π(o) = argmax_a E[U | π(o) = a]

**These are different!**

- E[U | O = o, A = a] conditions on the observation being o
- E[U | π(o) = a] conditions on the policy mapping o to a

### When Do They Differ?

**Case 1: No cross-situation dependence**

If U(i, o, a) depends only on the local (o, a), not on what happens elsewhere, then:
- E[U | π(o) = a] = E[U | O = o, A = a] (they're the same)
- UDT and EDT agree

**Case 2: Cross-situation dependence**

If U depends on the whole policy (e.g., through a predictor), then:
- E[U | π(o) = a] ≠ E[U | O = o, A = a] in general
- They condition on different things

### The Actual Content of UDT

**UDT says:** Condition on the policy fact π(o) = a, not on the local fact (O = o, A = a).

**When does this matter?** When the utility depends on the policy beyond just the local action.

**The representation theorem should say:**
If utility depends on the policy (cross-situation dependence), then the correct expected utility maximization is E[U | π], which gives the UDT formula.

### But Wait - This Is Almost Tautological!

If we define "rational" as "maximizes E[U | π]", then of course we get the UDT formula. We assumed it!

**The real question is:** Why should we maximize E[U | π] rather than E[U | O = o, A = a]?

This is where the "unity" and "latent structure" arguments come in.

---

## Claim 3: Unity Implies Policy-Centric Evaluation

### The Claim (Informal)
"If you model a SINGLE agent, you should evaluate policies, not individual actions."

### Attempt at Precise Statement

**Definition:** An agency model is **unified** if there's a single policy π that applies to all situations.

**Claim:** For unified agency, the correct evaluation is E[U | π], not E[U | O = o, A = a].

### Why Should This Be True?

**Argument 1: Consistency**

If we have a single π, then the actions at different observations are not independent choices - they're all determined by π.

So when we ask "what action should I take at o?", we're really asking "what should π(o) be?", which is a question about the policy.

**Argument 2: The Environment Responds to the Policy**

Under decision-determination, the environment responds to π, not to individual actions.

So the utility U(π) is really a function of the whole policy.

To maximize U(π), we need to optimize π, which means optimizing each π(o) as part of the whole.

**Argument 3: Information-Theoretic**

When I observe that I'm at observation o, what do I learn?
- I learn O = o (I'm in this situation)
- But I DON'T change my policy π

So conditioning should be: E[U | π, O = o] = E[U | π] (since π already determines what I do at o)

No wait, that's not quite right either...

### Actually, Let's Be Careful

**What does "conditioning on π(o) = a" mean?**

Option 1: I'm uncertain about my policy. Conditioning updates my beliefs about π.

Option 2: I'm choosing my policy. Conditioning is "what if I set π(o) = a".

**For UDT, it's Option 2:** We're choosing the policy, not learning about it.

So E[U | π(o) = a] means: "Expected utility if I commit to doing a at o."

**Compared to E[U | O = o, A = a]:**
This means: "Expected utility given that I observe o and do a."

**The difference:**
- UDT: The commitment to do a at o is known to the environment (via prediction)
- EDT: The environment may not "know" you'll do a at o; you're just calculating given that you end up doing a

### The Key Assumption: Decision-Determination

**Decision-determination:** The environment responds to your policy π, not to your mechanism.

**This means:** The environment "knows" your policy (via prediction or correlation).

**So:** When you commit to π(o) = a, the environment responds to this commitment.

**Therefore:** The correct calculation is E[U | π(o) = a], which accounts for how the environment responds to your commitment.

### The Theorem (More Precise)

**Setup:**
- Situations I, observations Obs, actions Act
- Policy space Π = Obs → Act
- Environment response: E(π) (depends on policy)
- Utility: U(E(π), π) (depends on environment and policy)

**Decision-determination:** U depends on π only through E(π), and E depends only on π (not on how π is computed).

**Rationality:** Choose π to maximize E[U | π] = U(E(π), π).

**Theorem:** The optimal policy satisfies:
For each o, π(o) = argmax_a [U(E(π'), π') where π'(o) = a and π'(o') = π(o') for o' ≠ o]

**If E is "smooth" in π (small changes in π cause small changes in E):**
Then this simplifies to: π(o) = argmax_a E[U | π(o) = a, π optimal elsewhere]

**For a coherent agent:** "π optimal elsewhere" is just π, so:
π(o) = argmax_a E[U | π(o) = a]

---

## Claim 4: This Is Analogous to Condensation Correspondence

### The Claim (Informal)
"The representation theorem is like condensation's correspondence theorem."

### Is This Analogy Precise?

**Condensation correspondence:** If L₁ and L₂ are both perfect condensations of M, their latents correspond.

**Agency "correspondence":** If we attribute unified agency correctly, we get UDT.

**The analogy:**
- Condensation: Structure → latents must correspond
- Agency: Structure → must evaluate policies

### Problem 6: This Isn't Really Correspondence

Condensation correspondence is about **different models agreeing**.

The representation theorem is about **what a single model implies**.

They're not the same structure!

**A better analogy might be:**
- Condensation: Given observables, what latents are appropriate?
- Agency: Given behavior, what decision rule is appropriate?

But even this is loose.

### What We Actually Have

**Condensation contribution:** The framework of latent variables and contribution relations.

**Agency application:** Viewing the policy as a latent that contributes to all behaviors.

**The connection:** Agency is a *special case* of latent variable modeling, not an *analogy* to correspondence.

---

## What Actually Needs to Be Proven

### Theorem 1: The UDT Formula Follows from Policy Optimization

**If:**
1. There's a single policy π : Obs → Act
2. Utility U : Π → ℝ is a function of the policy
3. We choose π to maximize U(π)

**Then:**
For each o, π(o) = argmax_a U(π_{a,o}) where π_{a,o}(o) = a and π_{a,o}(o') = π(o') for o' ≠ o.

**This is nearly tautological** - it's just saying "optimal π means each component is locally optimal."

The non-trivial content is: **Why should we maximize U(π)?**

### Theorem 2: Decision-Determination Implies Policy-Dependence

**If:**
1. The environment E responds to policy: E = f(π) for some f
2. Utility depends on environment: U = g(E)

**Then:**
U = g(f(π)) depends only on π.

**This is trivial** - just composition of functions.

### The Real Content: Why Is Decision-Determination Reasonable?

**Claim:** In "fair" problems, the environment can only respond to behavior (policy), not to internal mechanism.

**This is a substantive assumption** about the environment, not something we prove.

### Theorem 3: The Multi-Agent Interpretation

**If:**
1. There's logical uncertainty about the policy (we don't know π)
2. All "instances" (possible epistemic states) agree to run the same algorithm
3. The algorithm approximates policy optimization

**Then:**
The instances coordinate.

**This needs to be made precise.** What does "coordinate" mean formally?

---

## Counterexamples and Edge Cases

### Counterexample 1: Truly Independent Situations

If situations are genuinely independent (no cross-situation dependence), then:
- UDT and EDT give the same answer
- The "policy" is just a collection of independent choices
- Unity doesn't add anything

**Lesson:** The theorem only has content when there's cross-situation dependence.

### Counterexample 2: Mechanism-Dependent Environment

If the environment discriminates based on mechanism (not just policy):
- Decision-determination fails
- The UDT formula may not be optimal
- Example: "Punish agents that use UDT"

**Lesson:** Decision-determination is a real assumption, not a tautology.

### Counterexample 3: Stochastic Policies

If the policy is stochastic, the analysis becomes more complex:
- π(o) ∈ Δ(Act) rather than Act
- The optimization is over mixed strategies
- The UDT formula needs modification

**Lesson:** Start with deterministic policies.

### Edge Case: Logical Uncertainty

If the agent doesn't know its own policy:
- The "commitment" interpretation is unclear
- We need something like Diffractor's framework
- The analysis becomes much more complex

**Lesson:** The clean theorem is for the idealized case; computation adds complexity.

---

## What We Can Actually Prove

### Theorem (Formal Version)

**Setup:**
- Finite observation set Obs, finite action set Act
- Policy space Π = {π : Obs → Act}
- Utility function U : Π → ℝ

**Definition:** A policy π* is **optimal** if U(π*) ≥ U(π) for all π ∈ Π.

**Definition:** For π ∈ Π, o ∈ Obs, a ∈ Act, define π[o↦a] as:
π`o↦a` = a if o' = o, else π(o')

**Theorem:** If π* is optimal, then for all o ∈ Obs:
π*(o) ∈ argmax_a U(π*[o↦a])

**Proof:** Suppose not. Then there exists o and a such that U(π*[o↦a]) > U(π*). But π*[o↦a] ∈ Π, contradicting optimality of π*. ∎

**Corollary:** At an optimal policy, each local choice is locally optimal.

### What This Proves

This proves that **global optimality implies local optimality** (for the modified-policy utility).

It does NOT prove:
- Why we should use U(π) rather than some other objective
- Why the UDT conditioning is correct
- Anything about condensation

---

## Conclusion

### What's Actually True
1. If you optimize over policies, the UDT formula follows (nearly tautological)
2. Decision-determination is a substantive assumption about environments
3. The "condensation analogy" is suggestive but not precise

### What's Not Proven
1. Why optimize over policies rather than individual actions
2. The connection to condensation correspondence
3. The computational realization (UDT1.01)

### What We Need
1. A precise argument for why unified agency implies policy optimization
2. A real theorem connecting to condensation (not just analogy)
3. Formalization of the computational aspects

### Next Steps
1. Try to formalize the "unity implies policy optimization" argument
2. Look for precise connections to condensation
3. Write Lean proofs of the parts that can be proven
