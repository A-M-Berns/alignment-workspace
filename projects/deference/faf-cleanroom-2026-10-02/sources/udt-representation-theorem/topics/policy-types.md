# Policy Types

The C&T framework distinguishes several notions of "policy," reflecting the difference between what an agent *would* do absent interference, what it *actually* does, and what the environment *sees* it doing. These distinctions — chosen policy $\Pi^*$, effective policy $\Pi^\dagger$, and external policy $\ddot{\Pi}$ — are essential for stating decision-determination and the self-trust theorem. The framework also introduces instance policies that factor the full policy by external observation.

---

## Full Policy

**Definition.** A **full policy** is a deterministic function $\pi : \mathcal{R}O \to \mathcal{R}A$.

A full policy specifies, for every possible observation (both internal and external), what action the agent takes. Since $O = (\dot{O}, \ddot{O})$ and $A = (\dot{A}, \ddot{A})$, a full policy determines both internal and external actions given both internal and external observations.

## Effective Policy $\Pi^\dagger$

**Definition.** The **effective policy** is the random variable $\Pi^\dagger = `\beta_{D_B}`_A$, which maps observations to actions.

Here $\beta_{d_B} : \mathcal{R}O \to \mathcal{R}B$ is the function associated with the boundary dynamic value $d_B$, and $`\cdot`_A$ projects from $B$ to $A$ (extracting just the action component). The effective policy is the policy *actually implemented* by the agent.

**Relationship to $D_B$.** $\Pi^\dagger$ is a coarsening (subvariable) of $D_B$: knowing $D_B$ determines $\Pi^\dagger$, but not conversely. Multiple values of $D_B$ may correspond to the same policy — they represent different *implementations* of the same input-output behavior. For example, two decision algorithms might produce identical observation-to-action mappings while differing in their internal processing or memory usage.

## Chosen Policy $\Pi^*$

**Definition.** The **chosen policy** $\Pi^*$ is the random variable representing the full policy that *would be* implemented if the agent's decision procedure were never modified.

The distinction between $\Pi^*$ and $\Pi^\dagger$ captures the possibility of **modification**: an agent instance may be forced (via the side channel $\check{O}$) to act differently from what its decision procedure would normally dictate. When no modification occurs, $\Pi^\dagger = \Pi^*$. When modification does occur, $\Pi^\dagger$ may differ from $\Pi^*$ at the modified instances.

For UDT, the chosen policy is defined by the decision rule:

$$\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = \arg\max_{a_{\ddot{o}} \in \mathcal{R}A_{\ddot{o}}} \mathbb{E}[U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}]$$

The expectation is taken under the agent's prior (before any updating), and the conditioning is on the *policy output at the current observation* — not on the action directly. This is what makes UDT "updateless."

## External Policy $\ddot{\Pi}$

**Definition.** The **external policy** $\ddot{\Pi}$ is defined by:

$$\ddot{\pi}(\ddot{o}) = `\rho_{d_{I,B}}(\ddot{o})`_{\ddot{A}}$$

where $\rho_{d_{I,B}} : \mathcal{R}\ddot{O} \to \mathcal{R}(I, B)$ is the function from the agent dynamic constraint.

The external policy maps external observations to external actions. It is a subvariable of $D_{I,B} = (D_I, D_B)$: the joint agent dynamics determine the external policy, but the external policy forgets all internal details (internal actions, interior state) and retains only the externally visible behavior.

**Why the external policy matters.** Decision-determination is stated in terms of $\ddot{\Pi}$: the environment depends on the agent only through $\ddot{\Pi}$. This makes the external policy the natural unit for evaluating expected utility in UDT, and it is the quantity over which the self-trust results are proved.

## Instance Policies

When the boundary $B$ is factored by external observation (see `Instances and Communication`), policies decompose correspondingly.

**Definition.** An **instance policy** is a function $\pi_{\ddot{o}} : \mathcal{R}\dot{O}_{\ddot{o}} \to \mathcal{R}A_{\ddot{o}}$ for a specific external observation $\ddot{o} \in \mathcal{R}\ddot{O}$.

An instance policy determines what action to take at instance $\ddot{o}$ given only the internal observation at that instance. The full policy decomposes into a family of instance policies:

$$\pi = (\pi_{\ddot{o}})_{\ddot{o} \in \mathcal{R}\ddot{O}}$$

Similarly, both $\Pi^*$ and $\Pi^\dagger$ factor by $\ddot{o}$:
- $\Pi^*$ factors as $(\Pi^*_{\ddot{o}})_{\ddot{o} \in \mathcal{R}\ddot{O}}$
- $\Pi^\dagger$ factors as $(\Pi^\dagger_{\ddot{o}})_{\ddot{o} \in \mathcal{R}\ddot{O}}$

## Cross-Observation Dependence

Whole-policy evaluation is necessary precisely when actions at different observations jointly affect utility. This structural property is what forces reasoning at the policy level rather than the per-observation level.

**Definition.** A problem has **cross-observation dependence** if there exist observations $\ddot{o}, \ddot{o}' \in \mathcal{R}\ddot{O}$ with $\ddot{o} \neq \ddot{o}'$ and an event $\overline{e} \in \overline{E}$ with $\mathbf{P}(\overline{e}) > 0$ such that $U(\overline{e})$ depends on both $\ddot{A}_{\ddot{o}}$ and $\ddot{A}_{\ddot{o}'}$.

In other words, the utility in some positive-probability worlds is affected by what the agent does at two distinct external observations. This makes it impossible to optimize each observation independently — the agent must evaluate *whole policies*.

**Examples:**
- **Newcomb problems:** The predictor's behavior (part of $E$) responds to the agent's full external policy $\ddot{\Pi}$, so the utility at the one-box observation depends on the action at the two-box observation and vice versa.
- **Coordination problems:** A copy of the agent faces a different observation but runs the same algorithm, so both copies' actions jointly determine utility.
- **Commitment problems:** The agent's future self (at observation $\ddot{o}'$) responds to the credibility established by the current self (at observation $\ddot{o}$), coupling their contributions to utility.

Cross-observation dependence is the structural reason that decision-determination elevates the external policy $\ddot{\Pi}$ to the natural unit of evaluation: when the environment responds to the whole policy rather than individual actions, optimizing action-by-action fails to account for these cross-observation effects.

## Observation Grain

External observations $\ddot{O}$ define the natural grain for policies because they mark the finest level at which the agent can distinguish its circumstances.

**Finer grain (world-level):** An agent that conditions on the full world $\omega$ rather than $\ddot{O}(\omega)$ would need more information than it actually has — the agent cannot distinguish worlds that yield the same external observation.

**Coarser grain (situation-level):** Grouping observations into coarser "situations" and conditioning only on those discards information the agent possesses. A policy at a coarser grain cannot exploit distinctions the agent can actually make.

**The observation level is thus canonical:** it is the finest grain at which the agent's policy can vary, matching the agent's actual informational position. The instance factorization $\pi = (\pi_{\ddot{o}})_{\ddot{o} \in \mathcal{R}\ddot{O}}$ decomposes the policy exactly at this grain — one instance policy per distinguishable circumstance, no finer, no coarser.

## The Abstract Decision Structure

These policy types, together with the I/B/E variables, dynamics, and semantic/side-channel decomposition, form the **abstract decision structure**:

$$(I, B, E, \dot{O}, \ddot{O}, \dot{A}, \ddot{A}, D_I, D_E, D_B, \hat{O}, \check{O}, \Pi^*, U)$$

This is the minimal structure needed to state decision-determination and the UDT decision rule. The **concrete decision structure** adds instance factorization and communication structure (see `Instances and Communication`).

## Summary of Relationships

```
D_B  ──→  Π†  (coarsening: forget implementation details)
          │
     Π† = Π* when no modification occurs
          │
D_{I,B} ──→  Π̈   (coarsening: forget internal details)
```

| Symbol | Name | What it captures | Type |
|--------|------|-----------------|------|
| $\pi$ | Full policy | A specific observation-to-action function | Deterministic function |
| $\Pi^\dagger$ | Effective policy | The policy actually implemented | Random variable, coarsening of $D_B$ |
| $\Pi^*$ | Chosen policy | The policy implemented absent modification | Random variable |
| $\ddot{\Pi}$ | External policy | Externally visible behavior only | Random variable, subvariable of $D_{I,B}$ |
| $\pi_{\ddot{o}}$ | Instance policy | Single-instance decision rule | Function $\mathcal{R}\dot{O}_{\ddot{o}} \to \mathcal{R}A_{\ddot{o}}$ |

## UDT1.01 Policy Decomposition

Diffractor's UDT1.01 sequence provides an independent formalization of updateless policies that maps cleanly onto the C&T framework. The translation illuminates what UDT's policy structure is really doing.

**UDT1.01's formal setup.** Diffractor defines a finite observation set $\mathcal{O}$, a finite action set $\mathcal{A}$, and policies $\pi : \mathcal{O}^{<n} \to \mathcal{A}$ mapping observation histories to actions. The environment is a function $e : \Pi \times \mathcal{O}^{<n} \to \Delta\mathcal{O}$ that takes the agent's *full policy* and the current history, and returns a distribution over the next observation. In standard notation (per [Notation Standard](../notation.md) §5.3): $\mathcal{O}$ corresponds to $\ddot{O}$ (external observations), $\mathcal{A}$ corresponds to $\ddot{A}$ (external actions), $\Pi$ corresponds to $\ddot{\Pi}$ (external policies), and the agent's "source code" $S$ maps to $D_{I,B}$ — the agent's computational identity that determines the policy.

**Mapping to C&T framework.** UDT1.01's setup is essentially the external-only projection of the full I/B/E structure. The UDT1.01 environment function $e(\pi, h)$ depends on the full policy, not just the action at the current history — this is precisely the C&T environment dynamic $D_E$ responding to $\ddot{\Pi}$ rather than to an individual $\ddot{A}_{\ddot{o}}$. UDT1.01 omits the internal structure ($I$, $\dot{O}$, $\dot{A}$) and the semantic/side-channel decomposition ($\hat{O}$, $\check{O}$), working entirely at the level of externally visible behavior.

**Key structural difference from EDT.** The policy-dependence of $e$ is what distinguishes UDT from EDT. EDT conditions on the action: $\arg\max_a \mathbb{E}[U \mid a]$. UDT conditions on the policy-at-observation: $\arg\max_a \mathbb{E}[U \mid \pi(o) = a]$. In C&T terms, this is the decision-determination condition — the environment $E$ is conditionally independent of $D_{I,B}$ given $\ddot{\Pi}$, so the environment responds to the external policy, not to individual actions. UDT1.01's environment function $e(\pi, h)$ embodies this directly: the distribution over future observations depends on the entire policy $\pi$, not just the action selected at $h$.

**Plannable vs. unplannable observations.** UDT1.01 distinguishes *plannable* observations (the history $h \in \mathcal{O}^{<n}$, over which the agent selects a policy) from *unplannable* observations (epistemic states $\mathbb{S}_{h_{1:n}}$ that arrive during deliberation and cannot be pre-committed over). In C&T terms, plannable observations correspond to $\ddot{O}$ — the external observations that index instances and over which the external policy $\ddot{\Pi}$ is defined. Unplannable observations correspond to $\dot{O}$ (or more precisely, the semantic observation $\hat{O}$) — internal information that refines the agent's beliefs but does not factor the policy space. The instance factorization $\pi = (\pi_{\ddot{o}})_{\ddot{o} \in \mathcal{R}\ddot{O}}$ thus decomposes the policy exactly over the plannable observations, while unplannable observations are handled within each instance by the "rich policy" or algorithm $A$ that processes epistemic states at runtime.

---

## See Also

- `I/B/E Decomposition` — the structural context for observations and actions
- [Dynamics and Condensation](dynamics-and-condensation.md) — how $D_B$ gives rise to policies
- [Decision-Determination](decision-determination.md) — the fairness condition using $\ddot{\Pi}$
- [Self-Trust](self-trust.md) — the main theorem involving $\Pi^*$, $\Pi^\dagger$, and $\ddot{\Pi}$
- `Instances and Communication` — instance policies and their role in communication
