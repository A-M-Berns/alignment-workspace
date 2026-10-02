# Dynamics and Condensation

The input-output behavior of each component in the I/B/E decomposition is captured by **condensation variables** $D_I$, $D_B$, $D_E$ — minimal random variables that encode the "missing information" needed to determine an output from an input. These dynamics formalize how the interior responds to actions, how the environment responds to actions, and how the boundary maps observations to actions. The agent dynamic constraint ties these together, establishing that the full agent state $(I, B)$ is determined by the external observation and the agent's intrinsic dynamics.

---

## Condensation Variables

**Definition.** Given random variables $X$ and $Y$, a random variable $V$ is a **condensation variable** for $H(X \mid Y)$ if:

1. **Determination**: $H(X \mid Y, V) = 0$ — knowing both $Y$ and $V$ determines $X$.
2. **Support independence**: $V$ is independent of $Y$ in support — all combinations of values in $\mathcal{R}V \times \mathcal{R}Y$ are possible.
3. **Minimality**: $H(V) = H(X \mid Y)$ — $V$ contains exactly the missing information, no more.

**Intuition.** If $Y$ is an input and $X$ is an output, then $V$ captures the "program" or "rule" that computes $X$ from $Y$. Different values of $V$ correspond to different functions from $\mathcal{R}Y$ to $\mathcal{R}X$. The factorization $X = f(Y, V)$ makes the input-output relationship explicit. Support independence ensures that every program is compatible with every input; minimality ensures that no two distinct values of $V$ implement the same function.

**Connection to Eisenstat.** The condensation variable concept is the central construction in Eisenstat's condensation theory. In that framework, the condensation of $X$ given $Y$ provides a canonical decomposition of conditional entropy into a random variable that is orthogonal to the conditioning variable. The C&T paper adopts this concept directly, applying it to the agent-environment interface.

## The Three Dynamics

Each component of the I/B/E decomposition has a characteristic dynamic:

### Interior Dynamic $D_I$

$D_I$ is the condensation variable for $H(I \mid \dot{A})$.

- **Factorization**: $I$ factors as $(\dot{A}, D_I)$.
- **Function notation**: For each $d_I \in \mathcal{R}D_I$, there is a function $\iota_{d_I} : \mathcal{R}\dot{A} \to \mathcal{R}I$.

$D_I$ represents the residual information needed to determine the interior state $I$ given the internal action $\dot{A}$. Informally, $D_I$ is the interior's "constitution" — given a specific $d_I$, the interior's response to any internal action is fully determined.

Since $\dot{O}$ is a subvariable of $I$, each $d_I$ also determines a function $`\iota_{d_I}`_{\dot{O}} : \mathcal{R}\dot{A} \to \mathcal{R}\dot{O}$ giving the internal observations that result from each internal action.

### Environment Dynamic $D_E$

$D_E$ is the condensation variable for $H(E \mid \ddot{A})$.

- **Factorization**: $E$ factors as $(\ddot{A}, D_E)$.
- **Function notation**: For each $d_E \in \mathcal{R}D_E$, there is a function $\epsilon_{d_E} : \mathcal{R}\ddot{A} \to \mathcal{R}E$.

$D_E$ captures the environment's "laws" — everything about the environment except what the agent's external actions contribute. Given $d_E$, the environment's state is fully determined by the agent's external action.

### Boundary Dynamic $D_B$

$D_B$ is the condensation variable for $H(A \mid O)$ (equivalently $H(B \mid O)$, since $B$ factors as $(O, A)$).

- **Factorization**: $B$ factors as $(O, D_B)$.
- **Function notation**: For each $d_B \in \mathcal{R}D_B$, there is a function $\beta_{d_B} : \mathcal{R}O \to \mathcal{R}B$.

$D_B$ is the boundary's "decision algorithm" — it determines how observations are mapped to actions. Different values of $D_B$ represent different implementations of the decision procedure.

**Summary table:**

| Variable | Dynamic for | Factorization | Function notation |
|----------|-------------|---------------|-------------------|
| $D_I$ | $H(I \mid \dot{A})$ | $I$ factors as $(\dot{A}, D_I)$ | $\iota_{d_I} : \mathcal{R}\dot{A} \to \mathcal{R}I$ |
| $D_E$ | $H(E \mid \ddot{A})$ | $E$ factors as $(\ddot{A}, D_E)$ | $\epsilon_{d_E} : \mathcal{R}\ddot{A} \to \mathcal{R}E$ |
| $D_B$ | $H(A \mid O)$ | $B$ factors as $(O, D_B)$ | $\beta_{d_B} : \mathcal{R}O \to \mathcal{R}B$ |

## The Agent Dynamic Constraint

**Assumption.** $(I, B)$ factors as $(\ddot{O}, D_{I,B})$, where $D_{I,B} = (D_I, D_B)$.

This states that the combined agent state is fully determined by the external observation and the joint agent dynamics. The resulting function is:

$$\rho_{d_{I,B}} : \mathcal{R}\ddot{O} \to \mathcal{R}(I, B)$$

For each value $d_{I,B} = (d_I, d_B)$ of the joint dynamics and each external observation $\ddot{o}$, the full agent state $(I, B)$ is determined.

**Why this matters.** The agent dynamic constraint says that the agent's "nature" ($D_{I,B}$) together with the environment's input ($\ddot{O}$) suffice to determine everything about the agent. There is no additional source of randomness inside the agent beyond what is captured by $D_I$ and $D_B$. This is what makes it possible to define the external policy $\ddot{\Pi}$ as a subvariable of $D_{I,B}$.

## Properties of Condensation Variables

Several properties follow from the definition:

1. **Uniqueness up to isomorphism.** If $V$ and $V'$ are both condensation variables for $H(X \mid Y)$, then $V$ is a function of $V'$ and vice versa (they encode the same information).

2. **Entropy equality.** $H(V) = H(X \mid Y)$ ensures a tight correspondence between the conditional entropy and the entropy of the condensation variable.

3. **Factorization.** Since $H(X \mid Y, V) = 0$ and $V$ is support-independent of $Y$, we get that $X$ factors as $(Y, V)$. This is the canonical factorization: $X = f(Y, V)$ where $f$ is a surjective function.

4. **Function space interpretation.** The values of $V$ can be identified with functions $\mathcal{R}Y \to \mathcal{R}X$ (those that appear in the factorization). Two values $v, v'$ are distinct iff they induce different functions.

## Ordered Markov Condition

Eisenstat's condensation theory defines a structural property that governs how latent variables at different levels of a hierarchy relate to one another.

**Definition.** Let $I$ be a finite index set and $(Y_A)_{A \in \mathcal{P}^+ I}$ a family of random variables indexed by nonempty subsets of $I$. The family satisfies the **ordered Markov condition** if for every $A \in \mathcal{P}^+ I$, letting $\mathcal{F}$ be the collection of all $B \in \mathcal{P}^+ I$ incomparable to $A$ in the inclusion order (neither $B \subseteq A$ nor $B \supseteq A$):

$$Y_A \perp\!\!\!\perp Y_{\mathcal{F}} \;\mid\; Y_{\supsetneq A}$$

That is, $Y_A$ is conditionally independent of all variables at incomparable positions given the variables at strictly higher positions (strict supersets of $A$).

**Equivalent global form.** The ordered Markov condition is equivalent to: for any two upward-closed sets $\mathcal{F}, \mathcal{G} \subseteq \mathcal{P}^+ I$, the variables $Y_{\mathcal{F}}$ and $Y_{\mathcal{G}}$ are conditionally independent given $Y_{\mathcal{F} \cap \mathcal{G}}$.

## Characterization of Perfect Condensation

The ordered Markov condition characterizes when a latent variable model constitutes a *perfect* condensation — one where the latent variables capture all the entropy of the observed variables with no slack.

**Theorem (Eisenstat, Thm 5.1, Part B).** Let $\mathcal{M} = (\Omega, (X_i)_{i \in I})$ be a random variable model and $\mathcal{L} = ((\Lambda, (Y_A)_{A \in \mathcal{P}^+ I}), \pi)$ an associated latent variable model. Then $\mathcal{L}$ is a **perfect condensation** of $\mathcal{M}$ if and only if:

1. **Function property**: For all $i \in I$ and $A \in \mathcal{P}^+ I$ with $i \in A$, the latent variable $Y_A$ is a function of $X_i$ (a.e.).
2. **Ordered Markov condition**: The family $(Y_A)_{A \in \mathcal{P}^+ I}$ satisfies the ordered Markov condition.

**Significance for agent dynamics.** Applied to the I/B/E decomposition with index set $I = \{I, B, E\}$, the condensation variables $D_I$, $D_B$, $D_E$ correspond to latent variables at singleton subsets: $Y_{\{I\}} = D_I$, $Y_{\{B\}} = D_B$, $Y_{\{E\}} = D_E$. The agent dynamic constraint — that $(I, B)$ factors as $(\ddot{O}, D_{I,B})$ — reflects the function property for these variables. When the full agent-environment system constitutes a perfect condensation, the ordered Markov condition additionally requires that $D_I$, $D_B$, and $D_E$ satisfy conditional independence relations governed by the subset lattice. In the simplest (simple-perfect) case, the dynamics are jointly independent.

## Connection to General Condensation Theory

The condensation variables $D_I$, $D_B$, $D_E$ defined above are instances of Eisenstat's general construction specialized to the agent-environment setting. In the general theory, given any collection of random variables $(X_i)_{i \in I}$, one constructs a hierarchy of latent variables $(Y_A)_{A \in \mathcal{P}^+ I}$ capturing the shared and residual information at each level of the subset lattice. The agent-specific definitions in this file fix $I = \{I, B, E\}$ and restrict attention to the singleton condensation variables ($D_I$, $D_B$, $D_E$) and the pairwise variable $D_{I,B}$, which are the ones relevant to policy and decision-determination.

For the general theory — including the full lattice of condensation variables, the score function, and the definitions of perfect and simple-perfect condensation — see `Condensation Basics`.

## See Also

- `I/B/E Decomposition` — the structural context in which dynamics are defined
- [Policy Types](policy-types.md) — how $D_B$ gives rise to the effective policy $\Pi^\dagger$ and external policy $\ddot{\Pi}$
- [Decision-Determination](decision-determination.md) — the fairness condition phrased in terms of $D_{I,B}$ and $\ddot{\Pi}$
- `Condensation Basics` — general condensation theory: definitions, score functions, perfect condensation
- [Notation Standard](../notation.md) — formal notation for condensation variables and factorization
