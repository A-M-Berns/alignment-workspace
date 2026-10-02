# Decision-Determination

Decision-determination (DD) is the formalization of Yudkowsky's notion of "fairness" for decision problems: a problem is fair if all agents making the same *external* decision receive the same payoff, regardless of their internal constitution. In the C&T framework, DD requires (1) that utility depends only on the environment, and (2) that the environment depends on the agent only through the external policy $\ddot{\Pi}$. Under DD, expected utility is a function of the external policy, making updateless evaluation natural and enabling the self-trust results.

---

## Formal Definition

**Definition (Decision-Determination).** An abstract decision structure is **decision-determined** if:

1. $U$ is a function of $E$.
2. $E$ is conditionally independent of $D_{I,B}$ given $\ddot{\Pi}$:

$$\Pr(E = e \mid D_{I,B} = d_{I,B}) = \Pr(E = e \mid \ddot{\Pi} = `d_{I,B}`_{\ddot{\Pi}})$$

**In words:** The external policy is the only agent-intrinsic quantity that impacts the external environment, and utility depends only on the external environment.

Condition (1) says that the agent's reward comes entirely from the state of the world, not from anything internal. Condition (2) says that two agents with different internal dynamics $(D_I, D_B)$ but the same external policy $\ddot{\Pi}$ face exactly the same environment distribution.

## Origin: Yudkowsky's Fairness

The concept originates in Yudkowsky's discussion of which decision problems constitute "fair" tests of rationality:

> An expected utility maximizer can succeed even on problems designed for the convenience of alphabetizers, if the expected utility maximizer knows enough to calculate that the alphabetically first decision has maximum expected utility, *and if the problem structure is such that all agents who make the same decision receive the same payoff regardless of which algorithm produced the decision*. This last requirement is the critical one; I will call it *decision-determination*.

Yudkowsky argues that decision-determination (in some form) is needed to make reflective consistency a meaningful criterion: without restricting to "fair" problems, any agent can be made reflectively inconsistent by an adversary who punishes that agent's decision algorithm specifically.

## The Internal/External Distinction

A conceptual flaw in naive decision-determination: **self-modification is itself a decision**, so a fairness condition that only tracks external choices cannot rule out problems that directly incentivize self-modification.

The C&T formalization resolves this by distinguishing internal from external. The condition is stated in terms of $\ddot{\Pi}$ (the *external* policy) rather than the full policy $\Pi^\dagger$ or $\Pi^*$. This means:

- The environment does not care about the agent's internal state ($D_I$), internal actions ($\dot{A}$), or boundary implementation ($D_B$ beyond what it contributes to $\ddot{\Pi}$).
- The environment *does* respond to external actions ($\ddot{A}$), as mediated through the external policy.
- Internal decisions — including whether to self-modify — are not constrained by DD to be payoff-irrelevant. Instead, they are payoff-irrelevant *only insofar as* they do not change the external policy.

This is the key insight: a "fair problem" is one where the universe doesn't care about the agent's internal makeup except through the agent's external choices.

## Consequences for Expected Utility

Under decision-determination, expected utility simplifies to a function of the external policy.

Since $U$ is a function of $E$, and $E$ depends on $D_{I,B}$ only through $\ddot{\Pi}$:

$$\mathbb{E}(U \mid D_{I,B} = d_{I,B}) = \mathbb{E}(U \mid \ddot{\Pi} = `d_{I,B}`_{\ddot{\Pi}})$$

This means:

1. **Policy-level evaluation is well-defined.** Expected utility depends on which external policy is in effect, not on implementation details.
2. **Updateless reasoning is natural.** The UDT decision rule evaluates $\mathbb{E}(U \mid \Pi^*(o) = a)$, which under DD decomposes over external policies:

$$\mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \sum_{\ddot{\pi}} \mathbb{E}(U \mid \ddot{\Pi} = \ddot{\pi}) \cdot \Pr(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}})$$

3. **Self-trust becomes provable.** The decomposition above is the starting point for the Communicative Expectation Lemma and the Self-Trust Theorem.

## Policy-Centrism Under DD

The formal consequences above have an informal but important upshot: DD makes *policies* the atomic unit of analysis, not individual actions. Two agents with the same $\ddot{\Pi}$ face the same environment distribution (condition 2), so from the environment's perspective, an agent *is* its external policy. Individual actions at particular observations have no significance except through their contribution to $\ddot{\Pi}$ — the environment cannot "see" a single action in isolation, only the whole mapping from observations to actions.

This contrasts sharply with updateful reasoning. EDT and CDT condition on "I am at observation $\ddot{o}$ and I take action $\ddot{a}$," which treats the current observation as privileged. But DD establishes a symmetry between observations: the environment responds to the policy as a whole, so no particular $\ddot{o}$ is special. Updateful conditioning breaks this symmetry by anchoring evaluation to the agent's current epistemic position.

The argument, then, is: if the natural unit is the policy, then at any observation $\ddot{o}$ the agent should ask "what policy do I want to have?" and output what that policy prescribes at $\ddot{o}$. This is exactly the UDT decision rule $\pi(o) \in \arg\max_a \mathbb{E}(U \mid \pi(o) = a)$. The gap remaining — *why* an agent should adopt policy-centric evaluation rather than observation-anchored evaluation — is addressed by the broader core argument (see the parsimony, functional identity, and burden-of-proof arguments in `decision-determination-argument.md`).

## Relationship to the Verified Chain

The formal chain from decision-determination to UDT is machine-verified in Lean 4:

```
Decision-Determination       [lean/UDT/Substantive.lean]
       ↓
Policy Utility Function      [lean/UDT/BasicSimple.lean]
       ↓
UDT: π(o) ∈ argmax_a U(π[o↦a])
```

The Lean proofs verify that under DD, the UDT decision rule follows from the policy-level structure. The key lemma is that expected utility factors through the external policy, which is exactly condition (2) of DD.

## What DD Does Not Cover

Decision-determination is necessary but not sufficient for self-trust:

- DD ensures utility is policy-determined, but does not address **coordination problems** between instances. The Coordinated Buttons problem shows that self-trust can fail under DD without additional communication assumptions.
- DD does not guarantee the existence of **communicative alternatives** — the ability to achieve any external policy through communication rather than modification.
- DD does not guarantee **advice-following** — that instances will actually obey recommendations they receive.

These additional conditions (communicative alternatives, $\Pr(\ddot{\Pi} = R) = 1$, stable recommendations) are needed alongside DD for the self-trust and advice-following theorems.

## Connection to Other Frameworks

- **Causal Decision Theory**: CDT's "intervention" can be seen as a strong form of decision-determination where the environment is causally independent of the agent's decision. DD is weaker — it allows evidential correlations as long as they flow through $\ddot{\Pi}$.
- **Cartesian Frames**: In Garrabrant's framework, $W = A \times E$ imposes a product structure that implies something like DD. The I/B/E decomposition refines this by distinguishing internal and external aspects of the agent.
- **Newcomb-like problems**: DD holds in standard Newcomb's problem (the predictor responds to the agent's *policy*, which is an external quantity). DD fails in problems where the predictor responds to implementation details rather than external behavior.

## Condensation-Theoretic Interpretation

Decision-determination has a clean reading in terms of Eisenstat's condensation theory. Recall that $D_E$ is the condensation variable for $H(E \mid \ddot{A})$: the environment factors as $E = \epsilon_{D_E}(\ddot{A})$. The agent dynamics $D_{I,B}$ determine the external policy $\ddot{\Pi}$, which in turn determines the external action $\ddot{A}$ given $\ddot{O}$.

DD condition (2) says that $E$ is conditionally independent of $D_{I,B}$ given $\ddot{\Pi}$. In condensation-theoretic terms: **$\ddot{\Pi}$ is a perfect condensation variable for the agent's influence on the environment**. The environment's conditional distribution given the agent's internal constitution factors *entirely* through $\ddot{\Pi}$ — no residual information in $D_{I,B}$ beyond $\ddot{\Pi}$ is relevant. Equivalently, if we view the agent-environment interaction as a latent variable model where $D_{I,B}$ is latent and $(E, \ddot{O})$ is observed, then $\ddot{\Pi}$ captures all of $D_{I,B}$'s contribution to $E$.

This parallels Eisenstat's coin-bias example (Example 3.1): just as the bias $L$ is the unique latent variable needed to explain the conditional dependence among coin flips $(X_i)_{i \in I}$, the external policy $\ddot{\Pi}$ is the unique agent-intrinsic quantity needed to explain the environment's response. De Finetti's theorem says that $L$ is the only way to decompose the joint distribution into conditionally independent components; DD says that $\ddot{\Pi}$ is the only aspect of the agent that the environment "sees."

### Amalgamation and Policy Uniqueness

Eisenstat's amalgamation construction (Lemma 5.1) shows that two latent variable models for the same observational data can be combined on a common probability space while preserving each model's latent structure. Applied to DD: if two agents with different internal dynamics $D_{I,B}$ and $D'_{I,B}$ share the same external policy $\ddot{\Pi} = \ddot{\Pi}'$, then DD guarantees they face the same environment distribution $\Pr(E \mid \ddot{\Pi})$. The amalgamation result ensures these two "decompositions" of the agent-environment system are consistent — they agree on the policy-level structure, and can coexist on a shared probability space. Different implementations of the same external behavior are interchangeable from the environment's perspective.

### Recovery from Observations

The correspondence theorem's interpretation (Eisenstat, §4.3) connects to DD through the principle that latent variables are determined by their observational signatures. The terms $H(Y_{\supseteq A} \mid X_B)$ in the correspondence theorem measure how well latent variables can be recovered from observations. Under DD, the relevant agent property — the external policy $\ddot{\Pi}$ — is fully recoverable from the external action profile $(\ddot{A}_{\ddot{o}})_{\ddot{o} \in \mathcal{R}\ddot{O}}$, since $\ddot{\Pi}$ is defined as the function mapping observations to actions. This means the correspondence theorem's recovery terms vanish for $\ddot{\Pi}$: the "latent" policy is perfectly identified by its "observed" actions. Agent properties that do *not* affect the environment (everything in $D_{I,B}$ beyond $\ddot{\Pi}$) are precisely those that *cannot* be recovered from the environment's behavior — they are the condensation theory analogue of "gauge degrees of freedom."

## UDT1.01's Assumptions as DD Variants

Diffractor's UDT1.01 derivation (Post 6) rests on three assumptions that, read through C&T notation, decompose decision-determination into regularity, consequence, and core content.

**Assumption 1 (Influence limits exist).** For every algorithm $A$ and history $h$, the limits $\lim_{\varepsilon \to 0} \frac{1}{\varepsilon}(\mathbb{E}[U \mid A \text{ is } \varepsilon\text{-played at } h] - \mathbb{E}[U])$ and analogous probability-influence limits exist. This is a regularity/continuity condition: it ensures the agent's influence on the environment is well-defined and differentiable. DD presupposes this by requiring that $E$ depends smoothly on $\ddot{\Pi}$ -- the conditional distribution $\Pr(E = e \mid \ddot{\Pi} = \ddot{\pi})$ must be a well-behaved function of the policy. Assumption 1 makes explicit the analytic structure that DD takes for granted.

**Assumption 2 (Expected utility decomposition).** Expected utility decomposes as a sum over observations: $\mathbb{E}[U \mid A \text{ is } \varepsilon\text{-played}] = \sum_o \Pr(o \mid \varepsilon) \cdot \mathbb{E}[U \mid o \wedge \varepsilon]$. In C&T terms, this is a *consequence* of DD: once $U$ depends only on $E$ and $E$ depends only on $\ddot{\Pi}$, expected utility naturally decomposes over the external policy's observation-action pairs $(\ddot{o}, \ddot{a})$. The Lean-verified policy utility function (BasicSimple.lean) formalizes exactly this decomposition.

**Assumption 3 (Only average behavior matters).** The environment responds to the agent's policy as a whole -- to $\bar{A}_{h,n}$ (the average behavior) -- not to the specific algorithm producing that behavior. In C&T language, this *is* decision-determination: the environment sees $\ddot{\Pi}$, not $D_{I,B}$. Two algorithms with identical external policies $\ddot{\Pi}$ have identical influence on the environment. The escape clause ($o = h_{n+1}$) corresponds to the distinction between external and internal influence -- along the agent's own branch, future unplannable observations can matter, reflecting how $D_B$ can exceed $\ddot{\Pi}$ in information content.

**Summary.** UDT1.01's three assumptions are a computationally-oriented restatement of DD, decomposed into: regularity of the agent-environment interface (Assumption 1), the structural consequence for expected utility (Assumption 2), and the core content that the environment sees policies, not implementations (Assumption 3).

---

## Endorsement-Based Perspective

abramdemski's control endorsement provides an alternative framing of DD from the observer's perspective. Control endorsement states:

$$C^1_{U_2, P_1}(A \mid C^2_{U_2, P_2}(A) = a) = a$$

Agent 1 would copy Agent 2's answer if it knew it -- Agent 2's choice is at least as well-informed as Agent 1's, from Agent 1's perspective.

**DD enables inter-instance endorsement.** In the self-trust setting, consider two instances at observations $\ddot{o}_1$ and $\ddot{o}_2$. Under DD, the environment depends only on $\ddot{\Pi}$, so what matters is the policy as a whole. The instance at $\ddot{o}_1$ endorses the decision at $\ddot{o}_2$ because both contribute to the same external policy, and DD guarantees that each instance's contribution is evaluated through the same policy-level utility function $\mathbb{E}(U \mid \ddot{\Pi})$. Each instance optimizes its component of $\ddot{\Pi}$ toward the same objective.

**DD as a precondition for endorsement.** Without DD, the environment could respond differently to two implementations of the same policy -- $\Pr(E \mid D_{I,B})$ would not factor through $\ddot{\Pi}$. This would break endorsement: instance $\ddot{o}_1$ could not rationally trust $\ddot{o}_2$'s decision, because the payoff consequences of the same external action might differ depending on implementation details invisible to the policy. DD guarantees "same policy, same outcome," which is the precondition for any instance to endorse another's decision.

**Evaluation from the prior.** Endorsement is evaluated from $P_1$ (the observer's beliefs), and abramdemski notes that updatelessness boosts agency under endorsement -- any optimization is judged by how well it optimizes the expectations of $P_1$. This parallels UDT's prior-based evaluation: DD's structural condition (environment depends on $\ddot{\Pi}$) pairs with the epistemic condition (evaluate from the prior) to yield updateless reasoning. The connection is that DD makes the policy the natural unit of evaluation, and endorsement from the prior is the natural mode of evaluation for policies.

---

## See Also

- [Policy Types](policy-types.md) — the external policy $\ddot{\Pi}$ and its relationship to $D_{I,B}$
- [Self-Trust](self-trust.md) — the main theorem that builds on DD
- [Dynamics and Condensation](dynamics-and-condensation.md) — the agent dynamics $D_{I,B}$ that DD conditions on
- `Instances and Communication` — communicative alternatives that complement DD
- `Condensation Basics` — formal definitions of condensation variables and the correspondence theorem
- [Optimal Prediction](optimal-prediction.md) — how condensation connects to optimal prediction and DD
