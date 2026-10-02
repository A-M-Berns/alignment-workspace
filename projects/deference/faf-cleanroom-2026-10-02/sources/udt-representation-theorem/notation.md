# Notation Standard

This document defines the notation conventions for all topic files in this project. It is based on the conventions of `superconditioning-mismatched-ontologies.md` (§0), extended with agent-structural notation adapted from the Communication & Trust paper and decision-theoretic notation from Part II of the superconditioning document.

**Standing assumptions.** Unless otherwise stated, probability spaces are **countable and discrete** with **finite entropy**: sigma-algebras are atomic with countably many atoms, all sums over atoms converge, and conditioning on atoms is well-defined.

---

## 1. Core Measure-Theoretic Notation

### 1.1 The Naming Scheme

| Symbol | Meaning |
|--------|---------|
| $P$ | A set (sample space) |
| $p$ | An element of $P$ |
| $\overline{P}$ | The canonical sigma-algebra on $P$ |
| $\overline{p}$ | An event in $\overline{P}$ |
| $\hat{P}$ | The measurable space $(P, \overline{P})$ |
| $\mathbf{P}$ | The canonical probability measure on $\hat{P}$ |
| $\hat{\mathbf{P}}$ | The full probability space $(P, \overline{P}, \mathbf{P})$ |

Other named spaces follow the same scheme: $Q, \overline{Q}, \hat{Q}, \mathbf{Q}, \hat{\mathbf{Q}}$; and $L, W, C, X$, etc.

**Additional.** $\mathcal{P}^+ S = \mathcal{P}S \setminus \{\emptyset\}$ — the nonempty subsets of $S$.

### 1.2 Random Variables

A **random variable** on $\hat{P}$ valued in $\hat{Q}$ is a sigma-algebra homomorphism $\mathbf{q}\colon \overline{Q} \to \overline{P}$, denoted:

$$\mathbf{q}\colon \hat{P} \to \hat{Q}$$

We write random variables in **bold lowercase** matching their range. In the discrete setting, every such homomorphism corresponds to a measurable function $q\colon P \to Q$ via $\mathbf{q}(\overline{q}) = q^{-1}(\overline{q})$.

**Key conventions:**

| Notation | Meaning |
|----------|---------|
| $f(\mathbf{q})$ | Function application: $f(\mathbf{q})(\overline{s}) = \mathbf{q}(f^{-1}(\overline{s}))$ |
| $(\mathbf{q}, \mathbf{r})$ | Pairing/product: $(\mathbf{q}, \mathbf{r})(\overline{q} \times \overline{r}) = \mathbf{q}(\overline{q}) \cap \mathbf{r}(\overline{r})$ |
| $\pi_Q(\mathbf{v})$ | Projection from a product-valued variable |
| $\mathcal{R}\mathbf{q}$ | Range (codomain): $\mathcal{R}\mathbf{q} = \hat{Q}$ |
| $\mathbf{q}(\overline{Q})$ | Image sub-sigma-algebra in $\overline{P}$ |
| $\{\mathbf{q} \in A\}$ | Event $\mathbf{q}(\overline{A}) \in \overline{P}$ |

**"Is a function of."** $\mathbf{r}$ is a function of $\mathbf{q}$ when $\mathbf{r}(\overline{R}) \subseteq \mathbf{q}(\overline{Q})$. Equivalently: $H(\mathbf{r} \mid \mathbf{q}) = 0$. Also called: $\mathbf{r}$ is a **coarsening** of $\mathbf{q}$, or $\mathbf{q}$ is a **refinement** of $\mathbf{r}$.

### 1.3 Pushforward, Pullback, Conditioning

| Notation | Meaning |
|----------|---------|
| $\mathbf{q}_* \mathbf{P}$ | **Pushforward**: $(\mathbf{q}_* \mathbf{P})(\overline{q}) = \mathbf{P}(\mathbf{q}(\overline{q}))$ |
| $\boldsymbol{\pi}^* \mathbf{r}$ | **Pullback**: composite $\boldsymbol{\pi} \circ \mathbf{r}$ (on algebras) |
| $\mathbf{P}(\overline{p}' \mid \overline{p})$ | **Conditioning**: $\mathbf{P}(\overline{p}' \cap \overline{p}) / \mathbf{P}(\overline{p})$ |
| $\mathbf{Q} \ll \mathbf{P}$ | **Absolute continuity** |
| $d\mathbf{Q}/d\mathbf{P}$ | **Density** (Radon-Nikodym derivative) |

**Probability-preserving**: $\mathbf{q}$ is probability-preserving when $\mathbf{q}_* \mathbf{P} = \mathbf{Q}$.

### 1.4 Subspaces and Common Information

$\hat{P}$ is a **subspace** (coarsening) of $\hat{Q}$ when $\overline{P} \subseteq \overline{Q}$.

Given $\mathbf{q}\colon \hat{P} \to \hat{Q}$ and $\mathbf{r}\colon \hat{P} \to \hat{R}$, their **common information** is:

$$\overline{Q} \wedge_{\mathbf{q}, \mathbf{r}} \overline{R} = \mathbf{q}(\overline{Q}) \cap \mathbf{r}(\overline{R}) \subseteq \overline{P}$$

### 1.5 Atoms

An **atom** of $(\overline{P}, \mathbf{P})$ is a minimal event of positive measure. Under standing assumptions, atoms partition the total event. Sums over atoms: $\mathbf{P}(\overline{p}_0) = \sum_{\overline{p} \subseteq \overline{p}_0} \mathbf{P}(\overline{p})$.

### 1.6 Information-Theoretic Quantities

All take random variables as arguments. Commas denote products.

| Notation | Meaning |
|----------|---------|
| $H(\mathbf{q})$ | Entropy |
| $H(\mathbf{q} \mid \mathbf{r})$ | Conditional entropy |
| $I(\mathbf{q};\mathbf{r})$ | Mutual information |
| $I(\mathbf{q};\mathbf{r} \mid \mathbf{s})$ | Conditional mutual information |
| $I(\mathbf{q}; \mathbf{r}; \mathbf{s})$ | Interaction information: $I(\mathbf{q};\mathbf{r}) - I(\mathbf{q};\mathbf{r} \mid \mathbf{s})$ |
| $\mathbb{E}[\mathbf{q}]$ | Expectation (when range is a vector space) |

---

## 2. Agent-Structural Notation

Adapted from the Communication & Trust (C&T) paper. C&T uses point-set random variables on a shared $\Omega$; we translate to the point-free style of §1 where helpful but retain the point-set notation where it is more natural (especially for policy types and instance structure).

### 2.1 The I/B/E Decomposition

Three random variables partition the world:

| Variable | Name | Description |
|----------|------|-------------|
| $I$ | **Interior** | Persistent agent state (memories, cognition) |
| $B$ | **Boundary** | Decision procedure (input-output interface) |
| $E$ | **Environment** | Everything external to the agent |

### 2.2 Information Flows

Four random variables mediate information between $I$, $B$, and $E$:

| Variable | Name | Direction | Subvariable of |
|----------|------|-----------|---------------|
| $\dot{O}$ | Internal observation | $I \to B$ | $I$ and $B$ |
| $\ddot{O}$ | External observation | $E \to B$ | $E$ and $B$ |
| $\dot{A}$ | Internal action | $B \to I$ | $I$ and $B$ |
| $\ddot{A}$ | External action | $B \to E$ | $E$ and $B$ |

**Composites:**
- $O = (\dot{O}, \ddot{O})$: full observation (all inputs to $B$)
- $A = (\dot{A}, \ddot{A})$: full action (all outputs from $B$)

**Exhaustiveness constraints:**
- Common information $I \vee B = (\dot{O}, \dot{A})$
- Common information $B \vee E = (\ddot{O}, \ddot{A})$

**Internal observation decomposition:**
- $\hat{O}$: **semantic observation** — information the agent is supposed to receive normally
- $\check{O}$: **side channel** — aspects that may modify agent behavior off-policy

Note: $\hat{O}$ and $\check{O}$ need not factor $\dot{O}$; they are subvariables but may overlap.

### 2.3 Dynamics (Condensation Variables)

A **condensation variable** $V$ for $H(X|Y)$ satisfies:
1. $H(X \mid Y, V) = 0$ (knowing $Y$ and $V$ determines $X$)
2. $V$ is independent of $Y$ in support
3. $H(V) = H(X \mid Y)$ (minimality)

The agent structure has three dynamics:

| Variable | Dynamic for | Factorization | Function notation |
|----------|-------------|---------------|-------------------|
| $D_I$ | $H(I \mid \dot{A})$ | $I$ factors as $(\dot{A}, D_I)$ | $\iota_{d_I} : \mathcal{R}\dot{A} \to \mathcal{R}I$ |
| $D_E$ | $H(E \mid \ddot{A})$ | $E$ factors as $(\ddot{A}, D_E)$ | $\epsilon_{d_E} : \mathcal{R}\ddot{A} \to \mathcal{R}E$ |
| $D_B$ | $H(A \mid O)$ | $B$ factors as $(O, D_B)$ | $\beta_{d_B} : \mathcal{R}O \to \mathcal{R}B$ |

**Agent dynamic constraint.** $(I, B)$ factors as $(\ddot{O}, D_{I,B})$ where $D_{I,B} = (D_I, D_B)$, with function $\rho_{d_{I,B}} : \mathcal{R}\ddot{O} \to \mathcal{R}(I, B)$.

### 2.4 Policy Types

| Symbol | Name | Definition | Type |
|--------|------|------------|------|
| $\pi$ | Full policy | A function $\mathcal{R}O \to \mathcal{R}A$ | Deterministic |
| $\Pi^\dagger$ | Effective policy | $`\beta_{D_B}`_A$ — the policy actually implemented | Random variable |
| $\Pi^*$ | Chosen policy | The policy implemented absent modification | Random variable |
| $\ddot{\Pi}$ | External policy | $\ddot{\pi}(\ddot{o}) = `\rho_{d_{I,B}}(\ddot{o})`_{\ddot{A}}$ | Subvariable of $D_{I,B}$ |

### 2.5 Instance Factorization

$B$ factors by external observation: $B$ factors as $(B_{\ddot{o}})_{\ddot{o} \in \mathcal{R}\ddot{O}}$. Each $B_{\ddot{o}}$ is the decision-making for observation $\ddot{o}$.

Correspondingly, all agent variables factor by $\ddot{o}$:
- Actions: $A_{\ddot{o}} = (\dot{A}_{\ddot{o}}, \ddot{A}_{\ddot{o}})$
- Internal observations: $\dot{O}_{\ddot{o}}$, with subvariables $\hat{O}_{\ddot{o}}$ (semantic) and $\check{O}_{\ddot{o}}$ (side-channel)
- Policies: $\pi_{\ddot{o}} : \mathcal{R}\dot{O}_{\ddot{o}} \to \mathcal{R}A_{\ddot{o}}$ (instance policies)

### 2.6 Communication Structure

| Symbol | Name | Definition |
|--------|------|------------|
| $s_{\ddot{o}}$ | Message semantics | Partial function $\mathcal{R}\hat{O}_{\ddot{o}} \rightharpoonup \mathcal{R}\ddot{A}$; recommends an external action or stays silent |
| $R$ | Recommendation | Random variable valued in partial functions $\mathcal{R}\ddot{O} \rightharpoonup \mathcal{R}\ddot{A}$; subvariable of $\dot{O}$ |
| $p_{\ddot{o}}$ | Side-channel impact | Partial function $\mathcal{R}\check{O}_{\ddot{o}} \rightharpoonup \mathcal{R}\ddot{A}$; forced action from side channel |
| $P$ | Forced external policy | Random variable valued in partial functions; subvariable of $\dot{O}$ |

**Modification** occurs when $\text{dom}(P) \neq \emptyset$. Modification probability: $m(e) = \Pr(\text{dom}(P) \neq \emptyset \mid e)$.

### 2.7 Decision-Determination

An abstract decision structure is **decision-determined** if:
1. $U$ is a function of $E$
2. $E$ is conditionally independent of $D_{I,B}$ given $\ddot{\Pi}$:
$$\Pr(E = e \mid D_{I,B} = d_{I,B}) = \Pr(E = e \mid \ddot{\Pi} = `d_{I,B}`_{\ddot{\Pi}})$$

In words: the external policy is the only agent-intrinsic quantity that impacts the environment, and utility depends only on the environment.

---

## 3. Decision-Theoretic Notation (Heterogeneous UDT)

From Part II of the superconditioning document.

### 3.1 Decision-Points

A **decision-point** is $d_i = (\hat{\mathbf{X}}_i, A_i, u_i)$ where:
- $\hat{\mathbf{X}}_i$: probability space (world-model)
- $A_i$: finite set of basic actions
- $u_i : A \times X_i \to \mathbb{R}$: utility function, where $A = \prod_j A_j$

Expected utility: $U_i(O) = \mathbb{E}_{\mathbf{X}_i}[u_i(O, \cdot)]$ for outcome $O \in A$.

### 3.2 UDT Decision Rule

$$\pi(o) = \arg\max_{a \in A}\; \mathbb{E}(U \mid \pi(o) = a)$$

The expectation is taken under the agent's **prior** (before any updating).

### 3.3 Conditioning Types

| Type | Formula | Interpretation |
|------|---------|----------------|
| **EDT** | $\arg\max_a \mathbb{E}[U \mid a]$ | Condition on action (evidential) |
| **CDT** | $\arg\max_a \mathbb{E}[U \mid \text{do}(a)]$ | Intervene on action (causal) |
| **UDT** | $\arg\max_a \mathbb{E}[U \mid \pi(o) = a]$ | Condition on policy-at-observation (updateless) |

UDT conditions on the **policy output at the current observation**, not on the action directly.

### 3.4 Harmony and Bargaining

**Subjective Pareto dominance**: $O^*$ dominates $O$ if $U_i(O^*) \geq U_i(O)$ for all $i$ with strict inequality for some $i$.

**Bargaining game**: Each $d_i$ chooses a batna $b_i \in A_i$ and acceptable set $\mathcal{A}_i \subseteq A$. Outcome is $\text{sel}(\bigcap_i \mathcal{A}_i)$ if nonempty, else $b = (b_1, \ldots, b_n)$.

**Harmony** = trembling-hand equilibrium of the bargaining game.

---

## 4. Superconditioning-Specific Notation

Used in the formal superconditioning results.

| Symbol | Meaning |
|--------|---------|
| $(\hat{\mathbf{L}}, \mathbf{p}, \mathbf{p}', \overline{l})$ | Conditioning model for $(\hat{\mathbf{P}}, \hat{\mathbf{P}}')$ |
| $\overline{l}$ | Evidence event in $\overline{L}$ |
| $(\hat{C}, \mathbf{c}, \mathbf{c}')$ | Common information structure |
| $(\overline{A}, \kappa)$ | Anticipation structure; $\kappa_{\overline{a}}$ = intended kernel at atom $\overline{a}$ |
| $\mathbf{Q}_0$ | Prior-predictive measure: $\sum_{\overline{a}} \kappa_{\overline{a}} \cdot \mathbf{P}(\overline{a})$ |
| $\overline{D}$ | Two-atom Boolean algebra (for enrichment constructions) |
| $\nu_{\overline{a}}$ | Bridge-conditional: pushforward of prior conditional to $\overline{C}$ |

---

## 5. Translation Tables

### 5.1 C&T Paper → Standard

| C&T (LaTeX) | Standard (this project) | Notes |
|-------------|------------------------|-------|
| $X : \Omega \to \mathcal{R}X$ | $\mathbf{x} : \hat{\Omega} \to \hat{X}$ | Point-set → point-free |
| $\Prob$ | $\mathbf{P}$ (or $\boldsymbol{\Omega}$) | Probability measure |
| $H(Y \mid X) = 0$ | Same | "Is a function of" |
| $X \vee Y$ | $\overline{X} \wedge \overline{Y}$ | Common information |
| $(X, Y)$ | $(\mathbf{x}, \mathbf{y})$ | Product/pairing |
| $`x`_Y$ | Projection from $\mathbf{x}$ to $\mathbf{y}$ | Coarsening map |
| $I, B, E$ | Same | Interior, Boundary, Environment |
| $\dot{O}, \ddot{O}, \dot{A}, \ddot{A}$ | Same | Information flows |
| $\hat{O}, \check{O}$ | Same | Semantic observation, side channel |
| $D_I, D_B, D_E$ | Same | Dynamics/condensation variables |
| $\Pi^*, \Pi^\dagger, \ddot{\Pi}$ | Same | Policy types |
| $R, P$ | Same | Recommendation, forced policy |

The C&T agent-structural notation is already adopted as-is (§2). The main translation is that C&T uses point-set random variables while the superconditioning paper uses point-free style; both are equivalent in the discrete setting.

### 5.2 Condensation Theory (Eisenstat) → Standard

| Eisenstat | Standard | Notes |
|-----------|----------|-------|
| Measurable functions $f : X \to Y$ | $\mathbf{y} : \hat{X} \to \hat{Y}$ | Equivalent in discrete setting |
| Condensation: $(V, f)$ s.t. $X = f(Y, V)$ | $V$ condensation variable for $H(X \mid Y)$ | Same concept, different framing |
| Full conditional independence | $I(\mathbf{q}; \mathbf{r} \mid \mathbf{s}) = 0$ | Standard |
| Optimal predictor | $\mathbf{v}$ such that $H(\mathbf{x} \mid \mathbf{y}, \mathbf{v}) = 0$ with $I(\mathbf{v}; \mathbf{y}) = 0$ | Maps to condensation variable |

### 5.3 Diffractor's UDT1.01 → Standard

| UDT1.01 | Standard | Notes |
|---------|----------|-------|
| World-program $W$ | $\hat{\mathbf{X}}$ | Probability space |
| Source code $S$ | Part of $D_{I,B}$ | Agent's computational identity |
| $\text{output}(S, o)$ | $\pi(o)$ or $\Pi^*(o)$ | Policy evaluation |
| Logical counterfactual | Conditioning on $\Pi^*(o) = a$ | UDT conditioning type |
| Logical prior | $\mathbf{X}$ (prior measure) | Before any updating |

### 5.4 Cartesian Frames → Standard

| Cartesian Frames | Standard | Notes |
|------------------|----------|-------|
| Agent $A$ | $B$ (boundary) or $(I, B)$ | Agent's controllable part |
| Environment $E$ | $E$ | Same concept |
| World $W = A \times E$ | $(I, B, E)$ with factorization | Product structure |
| Ensurable set | Events achievable by policy choice | Related to $\ddot{\Pi}$-controllable events |
| Biextensional equivalence | Equivalent up to policy-irrelevant distinctions | Related to condensation |

### 5.5 Finite Factored Sets → Standard

| FFS | Standard | Notes |
|-----|----------|-------|
| Factored set $(S, F)$ | Product sigma-algebra structure | Algebraic factorization |
| Factor $f \in F$ | Component random variable | One factor in product |
| Orthogonality $f \perp g$ | Support independence | $\mathcal{R}f \times \mathcal{R}g$ fully realized |
| Conditional orthogonality | Conditional support independence given shared factors | |
| Time from orthogonality | Not directly used | FFS temporal ordering not adopted here |

---

## Usage Notes

1. **Default to point-free style** in formal statements; use point-set notation for intuitive explanations or when discussing agent structure.
2. **Bold lowercase** for random variables ($\mathbf{q}$), **overline** for sigma-algebras ($\overline{Q}$), **hat** for measurable spaces ($\hat{Q}$), **bold uppercase** for measures ($\mathbf{Q}$).
3. **Dotted notation** for internal/external: $\dot{O}$ (internal), $\ddot{O}$ (external). Hat/check for semantic/side-channel: $\hat{O}$ (semantic), $\check{O}$ (side channel).
4. **Policy superscripts**: $\Pi^*$ (chosen), $\Pi^\dagger$ (effective), $\ddot{\Pi}$ (external).
5. When discussing specific references, use the translation tables above rather than adopting the reference's native notation.
