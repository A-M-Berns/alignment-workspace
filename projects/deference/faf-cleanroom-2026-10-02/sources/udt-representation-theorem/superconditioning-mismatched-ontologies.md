# Superconditioning with Mismatched Ontologies

## 0. Definitions and Conventions

We adopt a pointless (point-free) style of presentation, drawing on Eisenstat's conventions. The primary objects are sigma-algebras and measures, not sets and elements. However, we do not totally banish the point-set. Where possible, related symbols denote related objects.

### 0.1 Spaces, Elements, and Notation

| Symbol | Meaning |
|---|---|
| $P$ | A set of interest |
| $p$ | An element of $P$ |
| $\overline{P}$ | The canonical (or most situationally relevant) sigma-algebra on $P$ |
| $\overline{p}$ | An event in $\overline{P}$ |
| $\hat{P}$ | The measurable space $(P, \overline{P})$ |
| $\mathbf{P}$ | The canonical (or most situationally relevant) probability measure on $\hat{P}$ |
| $\hat{\mathbf{P}}$ | The full probability space $(P, \overline{P}, \mathbf{P})$ |

Other named spaces follow the same scheme: $Q, q, \overline{Q}, \overline{q}, \hat{Q}, \mathbf{Q}, \hat{\mathbf{Q}}$; and similarly for $L, W, C$, etc.

**Additional notation.** $\mathcal{P}^+ S = \mathcal{P}S \setminus \{\emptyset\}$ — the nonempty subsets of $S$.

### 0.2 Random Variables

A **random variable** on $\hat{P}$ valued in $\hat{Q}$ is a sigma-algebra homomorphism from $\overline{Q}$ to $\overline{P}$:

$\mathbf{q}\colon \hat{P} \to \hat{Q}$

means a function $\mathbf{q}\colon \overline{Q} \to \overline{P}$ preserving $\bot$, complements, and countable joins. We denote random variables with bold lowercase matching their range.

**Correspondence with measurable functions.** A measurable function $q\colon P \to Q$ (in the point-set sense) induces a sigma-algebra homomorphism $\overline{q} \mapsto q^{-1}(\overline{q})$. Conversely, in countable discrete spaces, every sigma-algebra homomorphism arises this way. Eisenstat's paper works with measurable functions directly; the definitions below are equivalent in the discrete setting.

**Image sub-sigma-algebra.** Given $\mathbf{q}\colon \hat{P} \to \hat{Q}$, the image $\mathbf{q}(\overline{Q}) = \{\mathbf{q}(\overline{q}) : \overline{q} \in \overline{Q}\}$ is a sub-sigma-algebra of $\overline{P}$. This is the information that $\mathbf{q}$ makes available.

**Range.** $\mathcal{R}\mathbf{q}$ denotes the codomain: $\mathcal{R}\mathbf{q} = \hat{Q}$ (or just $Q$ when only the underlying set is needed).

### 0.3 Treating Random Variables as Elements of Their Range

The point of treating a sigma-algebra homomorphism $\mathbf{q}$ as a random variable is to treat it as though it names a stochastic element $q \in Q$. This licenses the following conventions.

**Function application.** If $\mathbf{q}\colon \hat{P} \to \hat{Q}$ and $f\colon \hat{Q} \to \hat{S}$ is a measurable map (point-set: a function $Q \to S$ whose preimage map sends $\overline{S}$-events to $\overline{Q}$-events), then $f(\mathbf{q})\colon \hat{P} \to \hat{S}$ is the random variable $f(\mathbf{q})(\overline{s}) = \mathbf{q}(f^{-1}(\overline{s}))$. In the point-set picture, this is $f \circ q$.

**Pairing / product.** Given $\mathbf{q}\colon \hat{P} \to \hat{Q}$ and $\mathbf{r}\colon \hat{P} \to \hat{R}$, their **pair** $(\mathbf{q}, \mathbf{r})\colon \hat{P} \to \widehat{Q \times R}$ is defined on product-measurable rectangles by $(\mathbf{q}, \mathbf{r})(\overline{q} \times \overline{r}) = \mathbf{q}(\overline{q}) \cap \mathbf{r}(\overline{r})$, extended to the product sigma-algebra. In the point-set picture, $p \mapsto (q(p), r(p))$.

**Tuple-builder notation.** Given a family $(\mathbf{q}_i)_{i \in I}$ of random variables on $\hat{P}$ and a predicate $\phi$, write $(\mathbf{q}_i : i \in I,\, \phi(i))$ or $(\mathbf{q}_i : \phi(i))$ for the product random variable over those $\mathbf{q}_i$ satisfying $\phi(i)$. Its range is the product of their ranges.

**Projection / coordinate extraction.** If $\mathbf{v}\colon \hat{P} \to \widehat{Q \times R}$ is product-valued, then $\pi_Q(\mathbf{v})$ and $\pi_R(\mathbf{v})$ give random variables valued in $\hat{Q}$ and $\hat{R}$, via function application. If $\mathbf{v} = (\mathbf{q}, \mathbf{r})$, then $\pi_Q(\mathbf{v}) = \mathbf{q}$.

**"Is a function of."** $\mathbf{r}$ **is a function of** $\mathbf{q}$ when there exists measurable $f$ with $\mathbf{r} = f(\mathbf{q})$. Equivalently (pointlessly): $\mathbf{r}(\overline{R}) \subseteq \mathbf{q}(\overline{Q})$, i.e., the information in $\mathbf{r}$ is contained in that of $\mathbf{q}$. Similarly **almost everywhere**: $H(\mathbf{r} \mid \mathbf{q}) = 0$ in the discrete finite-entropy setting (Eisenstat, Prop 2.4).

**Equality and equality almost everywhere.** $\mathbf{q}_1 = \mathbf{q}_2$ (with the same codomain) when they agree as sigma-algebra homomorphisms: $\mathbf{q}_1(\overline{s}) = \mathbf{q}_2(\overline{s})$ for all $\overline{s}$. **Almost everywhere**: $\mathbf{P}(\mathbf{q}_1(\overline{s})\, \triangle\, \mathbf{q}_2(\overline{s})) = 0$ for all $\overline{s}$.

**Events and set membership.** For $A \subseteq Q$ measurable, the expression $\{\mathbf{q} \in A\}$ or just "$\mathbf{q} \in A$" denotes the event $\mathbf{q}(\overline{A}) \in \overline{P}$. In the point-set picture, this is $q^{-1}(A)$.

**Algebraic and order operations.** When $Q$ carries algebraic structure (e.g., $Q \subseteq V$ for a vector space, or $Q = \mathbb{R}$), operations lift to random variables via function application. For instance, $\mathbf{q} + \mathbf{r}$ is shorthand for $\mathrm{add}(\mathbf{q}, \mathbf{r})$. Similarly, $\mathbf{q} \leq \mathbf{r}$ is an event when $Q$ is ordered.

**Expectation.** When $\mathcal{R}\mathbf{q} \subseteq V$ for a vector space $V$, the **expectation** $\mathbb{E}[\mathbf{q}]$ is the integral of $\mathbf{q}$ with respect to $\mathbf{P}$.

**Information-theoretic quantities.** Entropy $H(\mathbf{q})$, conditional entropy $H(\mathbf{q} \mid \mathbf{r})$, mutual information $I(\mathbf{q};\mathbf{r} \mid \mathbf{s})$, etc., all take random variables as arguments. Commas within these expressions denote products: $H(\mathbf{q}, \mathbf{r}) = H((\mathbf{q}, \mathbf{r}))$. **Interaction information:** $I(\mathbf{q}; \mathbf{r}; \mathbf{s}) = I(\mathbf{q}; \mathbf{r}) - I(\mathbf{q}; \mathbf{r} \mid \mathbf{s})$, symmetric in its arguments.

**Conditional distributions.** Expressions like $\mathbf{P}(\cdot \mid \mathbf{q} = q)$ treat $q$ as a specific value the stochastic element might take, defining a conditional probability measure for each $q$ in the support.

### 0.4 Pushforward, Probability-Preservation, and Pullback

**Pushforward.** Given $\mathbf{q}\colon \hat{P} \to \hat{Q}$ and a measure $\mathbf{P}$ on $\hat{P}$, the **pushforward** $\mathbf{q}_* \mathbf{P}$ is the measure on $\hat{Q}$ defined by $(\mathbf{q}_* \mathbf{P})(\overline{q}) = \mathbf{P}(\mathbf{q}(\overline{q}))$. This is $\mathbf{P}$'s opinion about which $q \in Q$ obtains. When the meaning is clear, we write $\mathbf{P}(\overline{q})$ as abbreviation for $\mathbf{P}(\mathbf{q}(\overline{q}))$.

**Probability-preserving.** $\mathbf{q}$ is **probability-preserving** when $\mathbf{P}(\overline{q}) = \mathbf{Q}(\overline{q})$ for all $\overline{q} \in \overline{Q}$, i.e., $\mathbf{q}_* \mathbf{P} = \mathbf{Q}$.

**Pullback.** If $\boldsymbol{\pi}\colon \hat{P} \to \hat{Q}$ is a (probability-preserving) map and $\mathbf{r}\colon \hat{Q} \to \hat{S}$ is a random variable, then the **pullback** $\boldsymbol{\pi}^* \mathbf{r}\colon \hat{P} \to \hat{S}$ is the composite. As sigma-algebra homomorphisms: $\overline{S} \xrightarrow{\mathbf{r}} \overline{Q} \xrightarrow{\boldsymbol{\pi}} \overline{P}$, so $\boldsymbol{\pi}^* \mathbf{r} = \boldsymbol{\pi} \circ \mathbf{r}$. Probabilistic quantities are preserved: $I(\mathbf{q}; \mathbf{r}) = I(\boldsymbol{\pi}^* \mathbf{q}; \boldsymbol{\pi}^* \mathbf{r})$. When unambiguous, pullbacks may be left implicit, writing just $\mathbf{r}$ for $\boldsymbol{\pi}^*\mathbf{r}$.

**Composition.** Given $\mathbf{q}\colon \hat{P} \to \hat{Q}$ and $\mathbf{r}\colon \hat{Q} \to \hat{R}$, the composition $\mathbf{r} \circ \mathbf{q}\colon \hat{P} \to \hat{R}$ has underlying map $\overline{R} \xrightarrow{\mathbf{r}} \overline{Q} \xrightarrow{\mathbf{q}} \overline{P}$ (applying $\mathbf{r}$ then $\mathbf{q}$ on algebras, giving the "forward" composition on random variables). This is the same as the pullback $\mathbf{q}^* \mathbf{r}$.

### 0.5 Subspaces, Refinements, and Common Information

$\hat{P}$ is a **(strict) subspace** or **coarsening** of $\hat{Q}$ — and $\hat{Q}$ is a **superspace** or **refinement** of $\hat{P}$ — iff $\overline{P}$ is a sub-sigma-algebra of $\overline{Q}$, equivalently, there exists a sigma-algebra homomorphism $\mathbf{p}\colon \hat{Q} \to \hat{P}$ (i.e., an inclusion $\overline{P} \hookrightarrow \overline{Q}$). Typically a distinguished such $\mathbf{p}$ tells us how to canonically interpret $\overline{P}$-events as $\overline{Q}$-events. If $\mathbf{p}$ is also probability-preserving, then $\hat{\mathbf{P}}$ is a coarsening of $\hat{\mathbf{Q}}$, and $\hat{\mathbf{Q}}$ a refinement of $\hat{\mathbf{P}}$.

**Common information.** Given two random variables $\mathbf{q}\colon \hat{P} \to \hat{Q}$ and $\mathbf{r}\colon \hat{P} \to \hat{R}$, their **common information** is the sub-sigma-algebra

$\overline{Q} \wedge_{\mathbf{q}, \mathbf{r}} \overline{R} = \mathbf{q}(\overline{Q}) \cap \mathbf{r}(\overline{R}) \subseteq \overline{P}.$

This consists of events expressible both in terms of $\mathbf{q}$ and of $\mathbf{r}$.

### 0.6 Product Algebras

Given sigma-algebras $\overline{P}$ and $\overline{Q}$, their **product** $\overline{P} \otimes \overline{Q}$ is the sigma-algebra generated by measurable rectangles $\overline{p} \times \overline{q}$ (in the discrete setting, its atoms are formal pairs of atoms). It comes with canonical embeddings $\mathbf{p}\colon \widehat{P \times Q} \to \hat{P}$ and $\mathbf{q}\colon \widehat{P \times Q} \to \hat{Q}$, the projection random variables.

We write $\overline{D}$ for the **two-atom Boolean algebra** with atoms $\overline{d}$ and $\overline{d}^c$. This is used throughout for the enrichment construction in superconditioning proofs.

### 0.7 Atoms

An **atom** of $(\overline{P}, \mathbf{P})$ is a minimal event of positive measure: $\overline{p} \in \overline{P}$ with $\mathbf{P}(\overline{p}) > 0$ such that for any $\overline{p}' \subseteq \overline{p}$, either $\mathbf{P}(\overline{p}') = 0$ or $\overline{p}' = \overline{p}$.

Under our standing assumptions (§0.10), atoms partition the total event (up to null sets). Atoms play the role of "worlds." In proofs, we freely index sums over atoms: $\mathbf{P}(\overline{p}_0) = \sum_{\overline{p} \subseteq \overline{p}_0} \mathbf{P}(\overline{p})$ where the sum ranges over atoms contained in $\overline{p}_0$.

### 0.8 Conditioning

For $\overline{p} \in \overline{P}$ with $\mathbf{P}(\overline{p}) > 0$:

$\mathbf{P}(\overline{p}' \mid \overline{p}) = \frac{\mathbf{P}(\overline{p}' \cap \overline{p})}{\mathbf{P}(\overline{p})} \quad \text{for } \overline{p}' \in \overline{P}.$

### 0.9 Measure-Theoretic Notation

**Absolute continuity.** $\mathbf{Q} \ll \mathbf{P}$ (for measures on the same algebra): $\mathbf{P}(\overline{p}) = 0 \implies \mathbf{Q}(\overline{p}) = 0$.

**Density.** When $\mathbf{Q} \ll \mathbf{P}$, the density $\frac{d\mathbf{Q}}{d\mathbf{P}}$ is defined on atoms by $\frac{d\mathbf{Q}}{d\mathbf{P}}(\overline{p}) = \mathbf{Q}(\overline{p})/\mathbf{P}(\overline{p})$.

**Essential supremum.** $\left\|\frac{d\mathbf{Q}}{d\mathbf{P}}\right\|_\infty = \sup_{\overline{p}:\, \mathbf{P}(\overline{p}) > 0} \frac{\mathbf{Q}(\overline{p})}{\mathbf{P}(\overline{p})}$, the sup over atoms.

### 0.10 Standing Assumptions

Unless otherwise stated, probability spaces are **countable and discrete** with **finite entropy**. Equivalently: sigma-algebras are atomic with countably many atoms, and $H(\mathbf{P}) < \infty$. All sums over atoms converge. Conditioning on atoms is well-defined. We note where results extend beyond these assumptions.

---

## 1. Conditioning Models

### 1.1 Motivation

Consider an agent's beliefs at an earlier time, $\hat{\mathbf{P}}$, and at a later time, $\hat{\mathbf{P}}'$. These may use different ontologies — $\overline{P}$ and $\overline{P}'$ need not have any relationship. The change in belief need not come from Bayesian conditioning; it can be an arbitrary shift. Our goal is to analyze it as a Bayesian update in a superspace of $\hat{P}$.

This seems sensible since a probability space is always an interpretation we layer over an agent; to understand something as an agent is (arguably) to interpret it as having beliefs (and goals); probabilities are simply the most popular way to formalize this.

### 1.2 Definition

**Definition 1.1.** A **conditioning model** for $(\hat{\mathbf{P}}, \hat{\mathbf{P}}')$ is a tuple $(\hat{\mathbf{L}}, \mathbf{p}, \mathbf{p}', \overline{l})$ satisfying:

- $\mathbf{p}\colon \hat{L} \to \hat{P}$ is probability-preserving w.r.t. $\mathbf{L}$ and $\mathbf{P}$: this interprets $\hat{P}$ as a coarsening of $\hat{L}$, and makes $\hat{\mathbf{L}}$ a refinement of $\hat{\mathbf{P}}$.
- $\overline{l} \in \overline{L}$ with $\mathbf{L}(\overline{l}) > 0$: the evidence event.
- $\mathbf{p}'\colon \hat{L} \to \hat{P}'$ is probability-preserving w.r.t. $\mathbf{L}'$ and $\mathbf{P}'$, where $\mathbf{L}'$ is the conditional:

$\mathbf{L}'(\overline{l}') = \mathbf{L}(\overline{l}' \mid \overline{l}) = \frac{\mathbf{L}(\overline{l} \cap \overline{l}')}{\mathbf{L}(\overline{l})}.$

That is: $\mathbf{P}'$ matches the result of updating $\mathbf{L}$ on $\overline{l}$ and projecting to $\hat{P}'$.

### 1.3 Unconstrained Existence

**Theorem 1.2.** *A conditioning model for $(\hat{\mathbf{P}}, \hat{\mathbf{P}}')$ always exists.*

*Proof.* Take $\overline{L} = \overline{P} \otimes \overline{P}'$, $\mathbf{L} = \mathbf{P} \otimes \mathbf{P}'$, $\overline{l} = \top$. Then $\mathbf{p}_* \mathbf{L} = \mathbf{P}$, $\mathbf{L}' = \mathbf{L}$, and $\mathbf{p}'_* \mathbf{L} = \mathbf{P}'$. $\square$

**Remark 1.3.** The bridge between $\hat{P}$ and $\hat{P}'$ is part of the construction, so there is nothing to prove. The product measure makes $P$ and $P'$ independent — a degenerate bridge asserting no relationship between the ontologies. The non-trivial content arises from constraints on this bridge.

---

## 2. Common Information

### 2.1 Motivation

When we say an agent changed their beliefs from $\hat{\mathbf{P}}$ to $\hat{\mathbf{P}}'$, we usually presuppose some common ground: there are propositions that both ontologies can express, and the agent's beliefs about those propositions evolved in a coherent way. This is what makes the belief change meaningful rather than just two unrelated probability spaces.

### 2.2 Definition

**Definition 2.1.** A **common information structure** for $(\hat{P}, \hat{P}')$ is a triple $(\hat{C}, \mathbf{c}, \mathbf{c}')$:

- $\hat{C}$: a measurable space (the **common information**),
- $\mathbf{c}\colon \hat{P} \to \hat{C}$: a homomorphism (interpreting $C$-events in $P$),
- $\mathbf{c}'\colon \hat{P}' \to \hat{C}$: a homomorphism (interpreting $C$-events in $P'$).

We write $\mathbf{C} = \mathbf{c}_* \mathbf{P}$ and $\mathbf{C}' = \mathbf{c}'_* \mathbf{P}'$ for the induced measures.

**Reading.** $\hat{C}$ is the shared language. An event $\overline{c} \in \overline{C}$ is a proposition expressible in both ontologies: $\mathbf{c}(\overline{c}) \in \overline{P}$ is its interpretation in $P$, and $\mathbf{c}'(\overline{c}) \in \overline{P}'$ is its interpretation in $P'$. The common information structure does not require $\overline{C}$ to be fine; if the ontologies share very little, $\overline{C}$ may have few atoms.

**Remark 2.2** (Extremes). If $\overline{C} = \{\bot, \top\}$ (trivial common information), we are back to the unconstrained case of §1. If $P' = P$ and $\mathbf{c} = \mathbf{c}' = \mathrm{id}$, the common information is the entire ontology.

### 2.3 Compatible Conditioning Models

**Definition 2.3.** A conditioning model $(\hat{\mathbf{L}}, \mathbf{p}, \mathbf{p}', \overline{l})$ is **$\hat{C}$-compatible** if:

$\mathbf{c} \circ \mathbf{p} = \mathbf{c}' \circ \mathbf{p}' \quad \text{as random variables } \hat{L} \to \hat{C}. \tag{Compat}$

That is: the two paths from $L$ to $C$ agree. Every $C$-event is interpreted consistently whether we go through $P$ or $P'$.

Write $\mathbf{c}_L = \mathbf{c} \circ \mathbf{p} = \mathbf{c}' \circ \mathbf{p}'$ for the common random variable in $\hat{L}$.

### 2.4 Consequences of Compatibility

From $\mathbf{p}_* \mathbf{L} = \mathbf{P}$ and $\mathbf{c} \circ \mathbf{p} = \mathbf{c}_L$:

$(\mathbf{c}_L)_* \mathbf{L} = \mathbf{c}_* \mathbf{P} = \mathbf{C}.$

From $\mathbf{p}'_* \mathbf{L}' = \mathbf{P}'$ and $\mathbf{c}' \circ \mathbf{p}' = \mathbf{c}_L$:

$(\mathbf{c}_L)_* \mathbf{L}' = \mathbf{c}'_* \mathbf{P}' = \mathbf{C}'.$

So $\mathbf{L}$ projects to $\mathbf{C}$ on $\hat{C}$, and $\mathbf{L}' = \mathbf{L}(\cdot \mid \overline{l})$ projects to $\mathbf{C}'$ on $\hat{C}$. This is exactly a same-ontology superconditioning problem on $\overline{C}$: starting from $\mathbf{C}$, conditioning on $\overline{l}$ (viewed via $\mathbf{c}_L$), and arriving at $\mathbf{C}'$.

### 2.5 The Common-Information Diaconis–Zabell Theorem

**Theorem 2.4.** *A $\hat{C}$-compatible conditioning model for $(\hat{\mathbf{P}}, \hat{\mathbf{P}}')$ exists if and only if $\mathbf{C}' \ll \mathbf{C}$ and $\left\|\frac{d\mathbf{C}'}{d\mathbf{C}}\right\|_\infty < \infty$.*

*Proof.* $(\Rightarrow)$ For any $\overline{c} \in \overline{C}$:

$\mathbf{C}'(\overline{c}) = \mathbf{L}(\mathbf{c}_L(\overline{c}) \mid \overline{l}) \leq \frac{\mathbf{L}(\mathbf{c}_L(\overline{c}))}{\mathbf{L}(\overline{l})} = \frac{\mathbf{C}(\overline{c})}{\mathbf{L}(\overline{l})}.$

So $\mathbf{C}' \ll \mathbf{C}$ with $d\mathbf{C}'/d\mathbf{C} \leq 1/\mathbf{L}(\overline{l})$.

$(\Leftarrow)$ Let $B = \|d\mathbf{C}'/d\mathbf{C}\|_\infty$. Define residual measure $\mathbf{C}''$ on $\overline{C}$ by:

$\mathbf{C}''(\overline{c}) = \frac{B \cdot \mathbf{C}(\overline{c}) - \mathbf{C}'(\overline{c})}{B - 1}$

on atoms $\overline{c}$ of $\overline{C}$, so that $\mathbf{C} = \frac{1}{B}\mathbf{C}' + \frac{B-1}{B}\mathbf{C}''$.

Construct $\overline{L} = \overline{P} \otimes \overline{P}' \otimes \overline{D}$ (where $\overline{D}$ has atoms $\overline{d}, \overline{d}^c$). We need $\mathbf{L}$ to satisfy:

- $\mathbf{p}_* \mathbf{L} = \mathbf{P}$,
- $\mathbf{c} \circ \mathbf{p} = \mathbf{c}' \circ \mathbf{p}'$ (compatibility),
- Conditioning on $\overline{l} = \mathbf{d}(\overline{d})$ and projecting via $\mathbf{p}'$ gives $\mathbf{P}'$.

The compatibility constraint forces $\mathbf{L}$ to be supported on atoms $(\overline{p}, \overline{p}', \delta)$ where $\mathbf{c}(\overline{p})$ and $\mathbf{c}'(\overline{p}')$ are compatible — i.e., they map to the same atom $\overline{c}$ of $\overline{C}$. Within each $\overline{C}$-fiber, we make $P$ and $P'$ conditionally independent:

$\mathbf{L}(\overline{p}, \overline{p}', \overline{d}) = \frac{1}{B} \cdot \frac{\mathbf{C}'(\overline{c})}{\mathbf{C}(\overline{c})} \cdot \mathbf{P}(\overline{p} \mid \mathbf{c} = \overline{c}) \cdot \mathbf{P}'(\overline{p}' \mid \mathbf{c}' = \overline{c}) \cdot \mathbf{C}(\overline{c})$

$\mathbf{L}(\overline{p}, \overline{p}', \overline{d}^c) = \frac{B-1}{B} \cdot \frac{\mathbf{C}''(\overline{c})}{\mathbf{C}(\overline{c})} \cdot \mathbf{P}(\overline{p} \mid \mathbf{c} = \overline{c}) \cdot \mathbf{P}'(\overline{p}' \mid \mathbf{c}' = \overline{c}) \cdot \mathbf{C}(\overline{c})$

where $\overline{c}$ is the common $\overline{C}$-atom of $\overline{p}$ and $\overline{p}'$ (the measure is zero when these disagree). Here $\mathbf{P}(\overline{p} \mid \mathbf{c} = \overline{c})$ denotes $\mathbf{P}(\overline{p} \mid \mathbf{c}(\overline{c}))$ and similarly for $\mathbf{P}'$.

**Verification.**

*Measure-preservation on $\overline{P}$:*

$\mathbf{p}_* \mathbf{L}(\overline{p}) = \sum_{\overline{p}',\, \delta} \mathbf{L}(\overline{p}, \overline{p}', \delta).$

Let $\overline{c}_0$ be the $\overline{C}$-atom containing $\overline{p}$. The sum over $\overline{p}'$ ranges over atoms of $\overline{P}'$ in the fiber $\mathbf{c}' = \overline{c}_0$. The sum over $\delta$ collapses the $\overline{D}$-factor (since $\frac{1}{B}\frac{\mathbf{C}'}{\mathbf{C}} + \frac{B-1}{B}\frac{\mathbf{C}''}{\mathbf{C}} = 1$). The sum over $\overline{p}'$ gives $\sum_{\overline{p}'} \mathbf{P}'(\overline{p}' \mid \mathbf{c}' = \overline{c}_0) = 1$. So:

$\mathbf{p}_* \mathbf{L}(\overline{p}) = \mathbf{P}(\overline{p} \mid \mathbf{c} = \overline{c}_0) \cdot \mathbf{C}(\overline{c}_0) = \mathbf{P}(\overline{p}). \quad\checkmark$

*Compatibility:* By construction, $\mathbf{L}$ is supported on pairs $(\overline{p}, \overline{p}')$ with $\mathbf{c}(\overline{p}) = \mathbf{c}'(\overline{p}')$, so $\mathbf{c} \circ \mathbf{p} = \mathbf{c}' \circ \mathbf{p}'$. ✓

*Evidence:*

$\mathbf{L}(\overline{l}) = \sum_{\overline{p},\, \overline{p}'} \mathbf{L}(\overline{p}, \overline{p}', \overline{d}) = \frac{1}{B} \sum_{\overline{c}} \frac{\mathbf{C}'(\overline{c})}{\mathbf{C}(\overline{c})} \cdot \mathbf{C}(\overline{c}) = \frac{1}{B}. \quad\checkmark$

*Posterior on $\overline{P}'$:*

$\mathbf{p}'_* \mathbf{L}'(\overline{p}') = \frac{1}{\mathbf{L}(\overline{l})} \sum_{\overline{p}} \mathbf{L}(\overline{p}, \overline{p}', \overline{d}).$

Let $\overline{c}_0$ be the $\overline{C}$-atom of $\overline{p}'$. The sum over $\overline{p}$ collapses: $\sum_{\overline{p}} \mathbf{P}(\overline{p} \mid \mathbf{c} = \overline{c}_0) = 1$. So:

$\mathbf{p}'_* \mathbf{L}'(\overline{p}') = B \cdot \frac{1}{B} \cdot \frac{\mathbf{C}'(\overline{c}_0)}{\mathbf{C}(\overline{c}_0)} \cdot \mathbf{P}'(\overline{p}' \mid \mathbf{c}' = \overline{c}_0) \cdot \mathbf{C}(\overline{c}_0) = \mathbf{C}'(\overline{c}_0) \cdot \mathbf{P}'(\overline{p}' \mid \mathbf{c}' = \overline{c}_0) = \mathbf{P}'(\overline{p}'). \quad\checkmark\quad\square$

### 2.6 Remarks

**Remark 2.5** (Same-ontology recovery). With $P' = P$, $\mathbf{c} = \mathbf{c}' = \mathrm{id}_P$ (so $C = P$, $\mathbf{C} = \mathbf{P}$, $\mathbf{C}' = \mathbf{P}'$), the conditions reduce to $\mathbf{P}' \ll \mathbf{P}$ with bounded density: the classical Diaconis–Zabell theorem (1982).

**Remark 2.6** (Trivial common information). With $\overline{C} = \{\bot, \top\}$: $\mathbf{C} = \mathbf{C}'$ is the trivial measure, absolute continuity is automatic, and a compatible conditioning model always exists. We recover Theorem 1.2.

**Remark 2.7** (The conditions are about shared ground only). $\hat{C}$-compatibility constrains how $\mathbf{P}$ and $\mathbf{P}'$ relate on propositions expressible in both ontologies. It says nothing about propositions private to one ontology. The agent can completely restructure their beliefs about $P$-private or $P'$-private matters; only the shared propositions must satisfy absolute continuity and bounded density.

**Remark 2.8** (The mixture decomposition on $\overline{C}$). The proof produces:

$\mathbf{C} = \frac{1}{B}\mathbf{C}' + \frac{B-1}{B}\mathbf{C}''. \tag{$\star_C$}$

This has the algebraic form of the reflection principle restricted to common information: $\mathbf{C}$ is a weighted average of two measures on $\overline{C}$. As in the same-ontology case, this is not yet a genuine reflection — that requires additional structure relating $(\star_C)$ to the agent's anticipation (§§3–4).

---

## 3. Anticipation Structures

### 3.1 Motivation

Theorem 2.4 constrains the conditioning model based on commonalities between $\hat{P}$ and $\hat{P}'$ — what they agree about structurally. We now ask: can we get sharper constraints by accounting for what $\mathbf{P}$ *thinks* about $\mathbf{P}'$? The agent may have beliefs about their own future beliefs, and a conditioning model that "respects" these beliefs should be more constrained than one that merely preserves common information.

### 3.2 Definition

**Definition 3.1.** An **anticipation structure** on $\hat{\mathbf{P}}$ targeting $\hat{Q}$ consists of:

- A sub-algebra $\overline{A} \subseteq \overline{P}$ (the **anticipation sub-algebra**),
- An **intended kernel** $\kappa$: for each atom $\overline{a}$ of $(\overline{A}, \mathbf{P}|_{\overline{A}})$, a probability measure $\kappa_{\overline{a}}$ on $\hat{Q}$.

**Reading.** $\overline{A}$ consists of events about the agent's possible future belief states. Each atom $\overline{a}$ is an anticipation state: a distinguishable class of future beliefs. $\kappa_{\overline{a}}$ is the probability measure the agent intends $\overline{a}$ to represent: "in anticipation state $\overline{a}$, I expect to hold beliefs $\kappa_{\overline{a}}$ about $\hat{Q}$."

**Remark 3.2** (Why not a function to $\Delta(\hat{Q})$?). A point-set function $s\colon P \to \Delta(\hat{Q})$ assigns each world a specific anticipated future belief. But worlds within the same atom of $\overline{A}$ are indistinguishable with respect to future beliefs, so the per-world assignment carries spurious information. The sub-algebra-plus-kernel formulation avoids this: atoms of $\overline{A}$ are the bearers of anticipation content.

**Remark 3.3** (Targeting $P'$). When the anticipation targets $\hat{P}'$ specifically, each $\kappa_{\overline{a}}$ is a measure on $\overline{P}'$. We use $\hat{Q}$ in the definition to allow the target to differ from $\hat{P}'$; in the same-ontology case, $Q = P$.

### 3.3 Prior-Predictive Measure

The **prior-predictive measure** on $\hat{Q}$ is:

$\mathbf{Q}_0(\overline{q}) = \sum_{\overline{a}} \kappa_{\overline{a}}(\overline{q}) \cdot \mathbf{P}(\overline{a}).$

This is the $\mathbf{P}$-weighted average of the anticipated future beliefs: the agent's current best guess at their future $\hat{Q}$-distribution, marginalizing over anticipation states.

### 3.4 Calibration and Reflection (Same-Ontology)

**Observation 3.4** (Total probability). For any sub-algebra $\overline{A} \subseteq \overline{P}$:

$\mathbf{P}(\overline{p}) = \sum_{\overline{a}} \mathbf{P}(\overline{p} \mid \overline{a}) \cdot \mathbf{P}(\overline{a}). \tag{TP}$

This holds for any sub-algebra and is a theorem of probability, not a rationality constraint.

**Definition 3.5** (Calibration; same-ontology). When $Q = P$, the anticipation structure $(\overline{A}, \kappa)$ is **calibrated** if:

$\mathbf{P}(\cdot \mid \overline{a}) = \kappa_{\overline{a}}(\cdot) \quad \text{for all atoms } \overline{a} \text{ with } \mathbf{P}(\overline{a}) > 0. \tag{Cal}$

Conditional on anticipation state $\overline{a}$, the agent's current beliefs equal the intended future beliefs $\kappa_{\overline{a}}$.

**Remark 3.6** (Cross-ontology). When $Q \neq P$, $\mathbf{P}(\cdot \mid \overline{a})$ is a measure on $\overline{P}$ while $\kappa_{\overline{a}}$ is on $\overline{Q}$. They cannot be directly equated. Cross-ontology calibration requires a bridge (§5).

**Definition 3.7** (Reflection; same-ontology). When $Q = P$, the anticipation structure satisfies the **reflection principle** if:

$\mathbf{P}(\overline{p}) = \sum_{\overline{a}} \kappa_{\overline{a}}(\overline{p}) \cdot \mathbf{P}(\overline{a}) \quad \text{for all } \overline{p} \in \overline{P}. \tag{R}$

Equivalently: the prior-predictive equals the prior, $\mathbf{Q}_0 = \mathbf{P}$.

**Proposition 3.8.** *Calibration implies reflection. Reflection does not imply calibration.*

*Proof.* Calibration substitutes $\kappa_{\overline{a}}$ for $\mathbf{P}(\cdot \mid \overline{a})$ in (TP).

For the converse: let $\overline{P}$ have atoms $\overline{p}_1, \ldots, \overline{p}_4$ with $\mathbf{P}$ uniform, $\overline{A}$ have atoms $\overline{a}_1 = \overline{p}_1 \cup \overline{p}_3$, $\overline{a}_2 = \overline{p}_2 \cup \overline{p}_4$, and $\kappa_{\overline{a}_1} = (1/2, 0, 1/4, 1/4)$, $\kappa_{\overline{a}_2} = (0, 1/2, 1/4, 1/4)$. Reflection holds: $\frac{1}{2}\kappa_{\overline{a}_1} + \frac{1}{2}\kappa_{\overline{a}_2} = \mathbf{P}$. But $\mathbf{P}(\cdot \mid \overline{a}_1) = (1/2, 0, 1/2, 0) \neq \kappa_{\overline{a}_1}$. $\square$

---

## 4. Calibrated Conditioning Models

### 4.1 Motivation

We seek conditioning models that respect the agent's anticipation — models whose enlarged algebra is a reasonable extrapolation of the agent's beliefs, not an arbitrary construction. We constrain the conditioning model, not the evidence.

### 4.2 Definition

**Definition 4.1.** Let $\hat{\mathbf{P}}$ have an anticipation structure $(\overline{A}, \kappa)$ targeting $\hat{Q}$. A conditioning model $(\hat{\mathbf{L}}, \mathbf{p}, \mathbf{q}, \overline{l})$ for $(\hat{\mathbf{P}}, \hat{\mathbf{Q}})$ is **calibrated** if:

$\mathbf{L}(\mathbf{q}(\overline{q}) \mid \mathbf{p}(\overline{a})) = \kappa_{\overline{a}}(\overline{q}) \quad \text{for all atoms } \overline{a} \text{ of } \overline{A},\ \overline{q} \in \overline{Q}. \tag{CM-Cal}$

In the enlarged algebra, conditional on anticipation state $\overline{a}$, the distribution over $\hat{Q}$ (via $\mathbf{q}$) equals the intended future belief $\kappa_{\overline{a}}$.

### 4.3 Same-Ontology: Calibration is Automatic

**Proposition 4.2.** *If $Q = P$, $\mathbf{q} = \mathbf{p}$, and $(\overline{A}, \kappa)$ is calibrated (Def 3.5), then (CM-Cal) holds automatically for any conditioning model.*

*Proof.* Since $\mathbf{q} = \mathbf{p}$ and $\overline{A} \subseteq \overline{P}$:

$\mathbf{L}(\mathbf{p}(\overline{p}) \mid \mathbf{p}(\overline{a})) = \frac{\mathbf{L}(\mathbf{p}(\overline{p} \cap \overline{a}))}{\mathbf{L}(\mathbf{p}(\overline{a}))} = \frac{\mathbf{P}(\overline{p} \cap \overline{a})}{\mathbf{P}(\overline{a})} = \mathbf{P}(\overline{p} \mid \overline{a}) = \kappa_{\overline{a}}(\overline{p}). \quad\square$

**Corollary 4.3.** *In the same-ontology case, calibration of the conditioning model imposes no constraint beyond calibration of the original anticipation.*

### 4.4 Cross-Ontology: A Genuine Constraint

**Remark 4.4.** When $Q \neq P$, (CM-Cal) is NOT automatic. The joint of $(\mathbf{p}(\overline{A}), \mathbf{q}(\overline{Q}))$ in $\overline{L}$ is not determined by $\mathbf{p}_* \mathbf{L} = \mathbf{P}$ alone.

**Theorem 4.5** (Calibration does not restrict posteriors). *Let $\hat{\mathbf{P}}$ have anticipation structure $(\overline{A}, \kappa)$ targeting $\hat{Q}$, with prior-predictive $\mathbf{Q}_0$. Then for any $\mathbf{Q}$ with $\mathbf{Q} \ll \mathbf{Q}_0$ and $\|d\mathbf{Q}/d\mathbf{Q}_0\|_\infty < \infty$, there exists a calibrated conditioning model for $(\hat{\mathbf{P}}, \hat{\mathbf{Q}})$.*

*Proof.* Let $B = \|d\mathbf{Q}/d\mathbf{Q}_0\|_\infty$. Construct $\overline{L} = \overline{P} \otimes \overline{Q} \otimes \overline{D}$ with:

$\mathbf{L}(\overline{p}, \overline{q}, \overline{d}) = \frac{1}{B} \cdot \frac{\mathbf{Q}(\overline{q})}{\mathbf{Q}_0(\overline{q})} \cdot \mathbf{P}(\overline{p}) \cdot \kappa_{\overline{a}(\overline{p})}(\overline{q})$

$\mathbf{L}(\overline{p}, \overline{q}, \overline{d}^c) = \left(1 - \frac{1}{B} \cdot \frac{\mathbf{Q}(\overline{q})}{\mathbf{Q}_0(\overline{q})}\right) \cdot \mathbf{P}(\overline{p}) \cdot \kappa_{\overline{a}(\overline{p})}(\overline{q})$

on atoms, where $\overline{a}(\overline{p})$ is the $\overline{A}$-atom containing $\overline{p}$. Let $\mathbf{p}, \mathbf{q}$ be canonical embeddings, $\overline{l} = \mathbf{d}(\overline{d})$.

**Measure-preservation:**

$\mathbf{p}_* \mathbf{L}(\overline{p}) = \sum_{\overline{q},\, \delta} \mathbf{L}(\overline{p}, \overline{q}, \delta) = \mathbf{P}(\overline{p}) \sum_{\overline{q}} \kappa_{\overline{a}(\overline{p})}(\overline{q}) = \mathbf{P}(\overline{p}). \quad\checkmark$

(The density factor $\mathbf{Q}/\mathbf{Q}_0$ cancels in the sum over $\overline{D}$.)

**Calibration:** For atom $\overline{a}$ of $\overline{A}$:

$\mathbf{L}(\mathbf{q}(\overline{q}) \cap \mathbf{p}(\overline{a})) = \sum_{\overline{p} \subseteq \overline{a},\, \delta} \mathbf{L}(\overline{p}, \overline{q}, \delta) = \kappa_{\overline{a}}(\overline{q}) \sum_{\overline{p} \subseteq \overline{a}} \mathbf{P}(\overline{p}) = \mathbf{P}(\overline{a}) \cdot \kappa_{\overline{a}}(\overline{q}).$

So $\mathbf{L}(\mathbf{q}(\overline{q}) \mid \mathbf{p}(\overline{a})) = \kappa_{\overline{a}}(\overline{q})$. ✓

**Posterior:**

$\mathbf{L}(\overline{l}) = \frac{1}{B} \sum_{\overline{p},\, \overline{q}} \frac{\mathbf{Q}(\overline{q})}{\mathbf{Q}_0(\overline{q})} \cdot \mathbf{P}(\overline{p}) \cdot \kappa_{\overline{a}(\overline{p})}(\overline{q}) = \frac{1}{B} \sum_{\overline{q}} \frac{\mathbf{Q}(\overline{q})}{\mathbf{Q}_0(\overline{q})} \cdot \mathbf{Q}_0(\overline{q}) = \frac{1}{B}.$

$\mathbf{L}(\mathbf{q}(\overline{q}) \cap \overline{l}) = \frac{\mathbf{Q}(\overline{q})}{B}, \qquad \mathbf{L}(\mathbf{q}(\overline{q}) \mid \overline{l}) = \mathbf{Q}(\overline{q}). \quad\checkmark\quad\square$

**Remark 4.6** (Why calibration is not restrictive). The density $\mathbf{Q}(\overline{q})/\mathbf{Q}_0(\overline{q})$ depends on $\overline{q}$ but not on $\overline{a}$: selection is uniform across anticipation states. This preserves calibration while steering the $\overline{Q}$-marginal to $\mathbf{Q}$.

Calibration constrains the unconditional joint of (anticipation, future world). The conditioning event can correlate with $\overline{Q}$ *within* each anticipation fiber without violating this. The event "learns" something about $Q$ that is orthogonal to the anticipation structure.

### 4.5 Calibration Plus Common Information

One might hope that combining calibration (§4) with common-information compatibility (§2) gives a stronger constraint. Specifically: given a common information structure $(\hat{C}, \mathbf{c}, \mathbf{c}')$ and an anticipation structure $(\overline{A}, \kappa)$ targeting $\hat{P}'$, require the conditioning model to be both $\hat{C}$-compatible and calibrated.

**Proposition 4.7.** *The combined constraint still does not restrict achievable posteriors beyond $\mathbf{C}' \ll \mathbf{C}$ with bounded density (the common-information D-Z condition) and $\mathbf{P}' \ll \mathbf{Q}_0$ with bounded density (the calibration D-Z condition).*

*Proof sketch.* The proof of Theorem 4.5 constructs $\overline{L} = \overline{P} \otimes \overline{P}' \otimes \overline{D}$. By supporting $\mathbf{L}$ on the "diagonal" $\{\mathbf{c}(\overline{p}) = \mathbf{c}'(\overline{p}')\}$ (as in Theorem 2.4) while using the anticipation-calibrated conditionals (as in Theorem 4.5), both constraints are satisfied simultaneously. The D-Z condition on $\overline{C}$ and the D-Z condition relative to $\mathbf{Q}_0$ are both necessary; the tighter of the two determines the achievable set. $\square$

### 4.6 Comparison: $\overline{A}$-Compatible Conditioning

A much more restrictive approach requires $\overline{l} \in \mathbf{p}(\overline{A})$: the evidence is expressible in terms of the anticipation. Then if $\overline{l} = \mathbf{p}(\bigcup_{\overline{a} \in T} \overline{a})$ for a set $T$ of anticipation atoms, the posterior (same-ontology case) is:

$\mathbf{P}'(\overline{p}) = \mathbf{P}(\overline{p} \mid \bigcup T) = \sum_{\overline{a} \in T} \mathbf{P}(\overline{p} \mid \overline{a}) \cdot \frac{\mathbf{P}(\overline{a})}{\mathbf{P}(\bigcup T)}.$

Under calibration, this is a Jeffrey conditioning update on $\overline{A}$: a restricted mixture of the $\kappa_{\overline{a}}$.

$\overline{A}$-compatibility constrains $\overline{l}$ rather than the model.

---

## 5. Cross-Ontology Calibration via Bridges

### 5.1 Motivation

Cross-ontology calibration (Def 3.5) requires equating $\mathbf{P}(\cdot \mid \overline{a})$ (on $\overline{P}$) with $\kappa_{\overline{a}}$ (on $\overline{Q}$). The common information structure $(\hat{C}, \mathbf{c}, \mathbf{c}')$ provides a translation.

### 5.2 Bridge-Calibration

Given $(\overline{A}, \kappa)$ targeting $\hat{P}'$ and a common information structure $(\hat{C}, \mathbf{c}, \mathbf{c}')$, the **bridge-conditional** for atom $\overline{a}$ is the pushforward of the prior conditional to $\overline{C}$:

$\nu_{\overline{a}}(\overline{c}) = \mathbf{P}(\mathbf{c}(\overline{c}) \mid \overline{a}) = \frac{\mathbf{P}(\mathbf{c}(\overline{c}) \cap \overline{a})}{\mathbf{P}(\overline{a})} \quad \text{for } \overline{c} \in \overline{C}.$

The intended kernel also pushes forward: $\kappa_{\overline{a}}^C(\overline{c}) = \kappa_{\overline{a}}(\mathbf{c}'(\overline{c}))$.

**Definition 5.1.** The anticipation is **$\hat{C}$-calibrated** if $\nu_{\overline{a}} = \kappa_{\overline{a}}^C$ for all atoms $\overline{a}$. That is: for shared propositions, the prior conditional given $\overline{a}$ matches the intended kernel's opinion.

This is weaker than full calibration (which would equate the measures on all of $\overline{P}$) but is the strongest condition that can be stated without a full semantic bridge between $\hat{P}$ and $\hat{P}'$.

---

## 6. Candidates for Sharper Constraints

Calibration does not restrict posteriors. $\overline{A}$-compatibility restricts them to Jeffrey on $\overline{A}$. Are there intermediate constraints that are semantically motivated?

### 6.1 Candidate A: Canonical $\overline{L}$

**Idea.** Forbid enrichment: use $\overline{L} = \overline{P} \otimes \overline{Q}$ (cross-ontology) or $\overline{L} = \overline{A} \otimes \overline{P}$ (same-ontology) with measure determined by calibration. The evidence $\overline{l}$ is unrestricted, but $\overline{L}$ has no extra structure.

In the same-ontology canonical case with $\overline{L} = \overline{A} \otimes \overline{P}$, $\mathbf{L}(\overline{a}, \overline{p}) = \mathbf{P}(\overline{a}) \cdot \kappa_{\overline{a}}(\overline{p})$. For evidence $\overline{l} \subseteq \overline{L}$, each $\overline{P}$-atom $\overline{p}$ selects a subset $\overline{l}_{\overline{p}} \subseteq \{\text{atoms of } \overline{A}\}$:

$\mathbf{P}'(\overline{p}) \propto \sum_{\overline{a} \in \overline{l}_{\overline{p}}} \mathbf{P}(\overline{a}) \cdot \kappa_{\overline{a}}(\overline{p}).$

**Proposition 6.1.** *Canonical-$\overline{L}$ posteriors strictly include the Jeffrey posteriors and are strictly included in unconstrained posteriors.*

*Proof sketch.* Possible unnormalized values per atom: at most $2^{|\overline{A}|}$ (one per subset of anticipation atoms). Unconstrained allows a continuum. Adding $\overline{D}$ recovers unconstrained (Theorem 4.5). $\square$

**Assessment.** A genuine intermediate. But "no enrichment" does not have a clear semantic motivation — it is a structural restriction on the conditioning model's complexity, not on its agreement with the agent's beliefs.

### 6.2 Candidate B: Conditional Independence

**Idea.** Require $\overline{l}$ to be conditionally independent of $\mathbf{p}(\overline{P})$ given $\mathbf{p}(\overline{A})$. This forces selection to depend only on the anticipation state, giving exactly Jeffrey conditioning on $\overline{A}$.

**Assessment.** Constrains $\overline{l}$ rather than the model.

### 6.3 Candidate C: Calibrated Refinement

**Idea.** The conditioning model extends the anticipation to a finer one, and the evidence is expressed in terms of the refinement.

**Definition 6.2.** A **calibrated refinement model** for $(\hat{\mathbf{P}}, \hat{\mathbf{P}}')$ relative to $(\overline{A}, \kappa)$ (same-ontology, $P' = P$) consists of:

- A finer sub-algebra $\overline{A}^+ \supseteq \overline{A}$ (with $\overline{A}^+ \subseteq \overline{P}$),
- A refined kernel $\kappa^+$: for each atom $\overline{a}^+$ of $\overline{A}^+$, a measure $\kappa^+_{\overline{a}^+}$ on $\overline{P}$,
- Calibration: $\mathbf{P}(\cdot \mid \overline{a}^+) = \kappa^+_{\overline{a}^+}$ for all atoms $\overline{a}^+$,
- An event $\overline{a}_0 \in \overline{A}^+$ with $\mathbf{P}(\overline{a}_0) > 0$ such that $\mathbf{P}' = \mathbf{P}(\cdot \mid \overline{a}_0)$.

**Proposition 6.3** (Coherence). *For any atom $\overline{a}$ of $\overline{A}$, the refined kernel averages back:*

$\kappa_{\overline{a}} = \sum_{\overline{a}^+ \subseteq \overline{a}} \kappa^+_{\overline{a}^+} \cdot \frac{\mathbf{P}(\overline{a}^+)}{\mathbf{P}(\overline{a})}.$

*Proof.* Total probability with calibration at both levels:

$\kappa_{\overline{a}}(\overline{p}) = \mathbf{P}(\overline{p} \mid \overline{a}) = \sum_{\overline{a}^+ \subseteq \overline{a}} \mathbf{P}(\overline{p} \mid \overline{a}^+) \cdot \frac{\mathbf{P}(\overline{a}^+)}{\mathbf{P}(\overline{a})} = \sum_{\overline{a}^+ \subseteq \overline{a}} \kappa^+_{\overline{a}^+}(\overline{p}) \cdot \frac{\mathbf{P}(\overline{a}^+)}{\mathbf{P}(\overline{a})}. \quad\square$

**Proposition 6.4** (Trivial limit). *If $\overline{A}^+ = \overline{P}$, calibrated refinement recovers unconstrained same-ontology superconditioning. The kernel is $\kappa^+_{\overline{p}} = \delta_{\overline{p}}$, trivially calibrated.*

**Assessment.** Calibrated refinement is the most semantically motivated candidate. The agent learns finer-grained things than their current anticipation accounts for, but the learning extends the anticipation coherently (Prop 6.3) rather than contradicting it. The degree of refinement measures "surprise." In the trivial limit (maximal refinement), it recovers unconstrained superconditioning.

---

## 7. Variable Future Ontology

### 7.1 Setup

Different anticipation states may correspond to different future ontologies.

**Definition 7.1.** An **anticipation structure with variable ontology** consists of:

- $\hat{\mathbf{P}}$ with anticipation sub-algebra $\overline{A} \subseteq \overline{P}$,
- For each atom $\overline{a}$ of $\overline{A}$, a measurable space $\hat{Q}_{\overline{a}}$,
- For each atom $\overline{a}$, a probability measure $\kappa_{\overline{a}}$ on $\hat{Q}_{\overline{a}}$.

### 7.2 Common Information Across Variable Ontologies

With variable ontologies, the common information between $\hat{P}$ and the possible future $\hat{Q}_{\overline{a}}$ may itself depend on $\overline{a}$. Formally, for each $\overline{a}$, we may have a different common information structure $(\hat{C}_{\overline{a}}, \mathbf{c}_{\overline{a}}, \mathbf{c}'_{\overline{a}})$, where $\mathbf{c}_{\overline{a}}\colon \hat{P} \to \hat{C}_{\overline{a}}$ and $\mathbf{c}'_{\overline{a}}\colon \hat{Q}_{\overline{a}} \to \hat{C}_{\overline{a}}$.

An event is **universally shared** if it lies in $\overline{C}_{\overline{a}}$ (via $\mathbf{c}_{\overline{a}}$) for all atoms $\overline{a}$ simultaneously. More precisely, define:

$\overline{U} = \bigcap_{\overline{a}} \mathbf{c}_{\overline{a}}(\overline{C}_{\overline{a}}) \subseteq \overline{P}$

the sub-algebra of $\overline{P}$ expressible in all possible future ontologies. As the number of possible future ontologies grows and as they diverge, $\overline{U}$ shrinks.

---

## 8. Discussion

### 8.1 The Hierarchy of Constraints

| Level | Constraint | Conditions on posteriors |
|---|---|---|
| 0 | None (§1) | Always exists |
| 1 | Fix common info $(\hat{C}, \mathbf{c}, \mathbf{c}')$ (§2) | D-Z on $\overline{C}$: $\mathbf{C}' \ll \mathbf{C}$, bounded density |
| 2 | + Calibration w.r.t. anticipation (§4) | No further restriction (Thm 4.5) |
| 2' | + Calibration + common info (§4.5) | Tighter of the two D-Z conditions |
| 3 | Same ontology: $P' = P$, $\mathbf{p}' = \mathbf{p}$ (§2.5) | Classical D-Z |

The transition from Level 0 to Level 1 is the first non-trivial step: fixing common information recovers the D-Z conditions. The surprise is at Level 2: adding calibration (the agent's conditioning model must agree with their own anticipation about future beliefs) does not further restrict the achievable posteriors. The conditioning event can exploit structure orthogonal to the anticipation.

### 8.2 What Calibration Does and Does Not Do

**Does:** Constrains the conditioning model — the enlarged algebra must agree with the anticipation about the future-world distribution conditional on each anticipation state.

**Does not:** Constrain the achievable posteriors — the conditioning event can correlate with $\overline{Q}$ within each anticipation fiber (Remark 4.6).

The underlying reason: calibration is a constraint on the *unconditional* joint of (anticipation, future world). It says nothing about how the evidence event $\overline{l}$ interacts with this joint. The evidence can "select" future worlds in a way that depends on the future world but not on the anticipation state, preserving calibration while achieving any desired posterior.

### 8.3 Reappraising Huttegger

Huttegger (2024) argues that superconditioning connects to the reflection principle.

**Weaker than claimed:** The mixture decomposition $(\star_C)$ has only the algebraic form of reflection. Making it genuinely reflective requires calibration — a condition Huttegger does not articulate.

**Stronger than expected:** Every achievable posterior CAN be represented in a calibrated conditioning model (Theorem 4.5). A genuine reflection interpretation is always available. But the update may go beyond what the anticipation accounts for.

### 8.4 The Landscape of Evidence Constraints

| Constraint on $\overline{l}$ | Effect |
|---|---|
| Unrestricted | Full superconditioning |
| $\overline{l} \in \mathbf{p}(\overline{A})$ ($\overline{A}$-compatible) | Jeffrey conditioning on $\overline{A}$ |
| $\overline{l} \in \mathbf{p}(\overline{A}^+)$ (calibrated refinement) | Jeffrey on $\overline{A}^+$; interpolates |
| $\overline{l} \perp \mathbf{p}(\overline{P}) \mid \mathbf{p}(\overline{A})$ (conditional independence) | Jeffrey on $\overline{A}$ |
| Canonical $\overline{L}$ (no enrichment) | Combinatorial intermediate |

### 8.5 Open Questions

1. **Quantifying refinement.** How much refinement does a given $\mathbf{P}'$ require relative to $\overline{A}$? The conditional entropy of $d\mathbf{P}'/d\mathbf{P}$ given $\overline{A}$ — measuring density variation within anticipation fibers — is a natural candidate.

2. **Relationship to logical induction.** How does calibrated refinement relate to Eisenstat's Bayesian logical induction, where the anticipation structure is generated by the agent's deductive process?

3. **Self-reference.** With $Q = P$, calibration ($\mathbf{P}(\cdot \mid \overline{a}) = \kappa_{\overline{a}}$) is a fixed-point condition: the agent's probability space encodes measures over itself. Manageable when $\overline{A}$ has finitely many atoms; foundationally subtle in the limit (cf. Harsanyi's universal type space).

4. **Approximate common information.** Relaxing exact homomorphisms $\mathbf{c}, \mathbf{c}'$ to approximate ones, modeling imperfect ontology translation.

5. **Sharper semantic constraints?** Is there a principled constraint — between calibration (non-restrictive) and $\overline{A}$-compatibility (severely restrictive) — that restricts posteriors non-trivially by leveraging what $\mathbf{P}$ thinks about $\mathbf{P}'$? The negative result of Theorem 4.5 suggests that the answer, if it exists, must constrain how $\overline{l}$ interacts with the anticipation-future joint, not merely the joint itself.

---

# Part II: Toward a Heterogeneous UDT

The following sections develop a generalization of Updateless Decision Theory (UDT) to heterogeneous decision-points — computational instances that may carry different probability spaces, different sigma-algebras, and different utility assessments. The superconditioning framework of Part I is used to relate such instances when their beliefs are epistemically connected.

---

## 9. Heterogeneous Decision-Points

### 9.1 Motivation

Classical UDT posits a single agent with a single prior $\mathbf{X}$ and a policy $\pi$ mapping observation histories to actions. The principle is that $\pi$ should be evaluated and selected from the prior, *before* any updating, so that all decision-relevant instances are coordinated by the same probability measure.

This coordination mechanism breaks down in several practically important cases:

- **Logical uncertainty.** The agent may be uncertain about its own logical structure, and cannot form a coherent prior over all instances of itself.
- **Ontological shifts.** The agent at time $t'$ may have a different world-model (different $\overline{X}$, different propositions) than at time $t$.
- **Multi-agent coordination.** Distinct agents must coordinate without being able to appeal to a common prior.

We therefore drop the shared-prior requirement and work with a collection of *decision-points*, each carrying its own epistemic and evaluative structure.

### 9.2 Decision-Points

**Definition 9.1 (Decision-Point).** A *decision-point* is a tuple $d_i = (\hat{\mathbf{X}}_i, A_i, u_i)$ where:

- $\hat{\mathbf{X}}_i = (X_i, \overline{X}_i, \mathbf{X}_i)$ is a probability space (the *world-model* of $d_i$);
- $A_i$ is a finite set of *basic actions* available to $d_i$;
- $u_i\colon A \times X_i \to \mathbb{R}$ is a utility function, where $A = \prod_j A_j$ is the joint action space.

The *expected utility* of an outcome $O \in A$ for decision-point $i$ is:

$U_i(O) = \mathbb{E}_{\mathbf{X}_i}[u_i(O, \cdot)] = \int_{X_i} u_i(O, x)\, \mathbf{X}_i(dx).$

Utility depends on the joint outcome $O \in A$, not just $d_i$'s own action; each decision-point cares about what others do. The evaluation uses $\mathbf{X}_i$, so distinct decision-points may rank outcomes differently when they hold different beliefs.

**Definition 9.2 (Subjective Pareto Dominance).** Outcome $O^*$ *subjectively Pareto-dominates* $O$ (with respect to a collection $\{d_i\}$) if $U_i(O^*) \geq U_i(O)$ for all $i$, with strict inequality for some $i$.

This is standard Pareto dominance applied to the subjective expected utilities $U_i$. No common beliefs are required; each $U_i$ is computed under $\mathbf{X}_i$.

---

## 10. The Harmony Condition and the Bargaining Game

### 10.1 Motivation

Classical UDT's policy-before-updating criterion enforces coordination across decision instances: no instance wishes it had acted differently, given what others did. We generalize this by asking that no decision-point wishes to *modify the computation* of any other.

**Definition 10.1 (Harmony).** A strategy profile $\sigma = (\sigma_i)_i$ is *harmonious* if no decision-point has a profitable unilateral deviation that modifies the computation of any other decision-point's action. Modifications that leave all input-output relationships unchanged are considered trivially equivalent.

### 10.2 The Bargaining Game

To formalize harmony, we model it as a game-theoretic equilibrium condition. Each decision-point can either execute its current strategy or *bargain*: propose an alternative joint outcome and agree to cooperate with any mutually acceptable proposal.

**Definition 10.2 (Bargaining Game).** The *bargaining game* $\mathcal{G}$ for a collection $\{d_i\}$ has:

- *Strategies*: a strategy for $d_i$ is a pair $(b_i, \mathcal{A}_i)$ where $b_i \in A_i$ is a *batna* (basic action taken if no deal is reached) and $\mathcal{A}_i \subseteq A$ is a finite set of *acceptable outcomes*;
- *Outcome rule*: let $b = (b_1, \ldots, b_n) \in A$ be the batna profile. The realized outcome is:

$O(\sigma) = \begin{cases} \mathrm{sel}\!\left(\bigcap_i \mathcal{A}_i\right) & \text{if } \bigcap_i \mathcal{A}_i \neq \emptyset, \\ b & \text{otherwise};\end{cases}$

- *Selection rule*: $\mathrm{sel}(S)$ selects an outcome from a nonempty finite set $S \subseteq A$.

### 10.3 Welfare Selection

**Definition 10.3 (Welfare Selection Rule).** A selection rule $\mathrm{sel}$ is a *welfare selection rule* if there exists a function $W\colon A \to \mathbb{R}$ satisfying:

1. *Pareto-consistency*: if $O^*$ subjectively Pareto-dominates $O$ then $W(O^*) > W(O)$;
2. *Selection*: $\mathrm{sel}(S) = \arg\max_{O \in S} W(O)$ (breaking ties arbitrarily but consistently).

One natural choice is $W(O) = \sum_i \tilde{U}_i(O)$ where $\tilde{U}_i$ normalizes $U_i$ to $[0,1]$, but any Pareto-consistent aggregation suffices. The existence of a Pareto-consistent $W$ follows from a standard argument whenever $A$ is finite and each $U_i$ is real-valued.

### 10.4 Equilibrium Concept

**Definition 10.4 (Trembling-Hand Equilibrium).** A strategy profile $\sigma^*$ is a *trembling-hand equilibrium* of $\mathcal{G}$ if there exists a sequence of perturbed games $\mathcal{G}^\epsilon$ (in which every strategy is played with probability at least $\epsilon > 0$) and corresponding Nash equilibria $\sigma^\epsilon$ of $\mathcal{G}^\epsilon$ such that $\sigma^\epsilon \to \sigma^*$ as $\epsilon \to 0$.

Harmony is identified with the trembling-hand equilibrium condition: a strategy profile is harmonious iff it is a trembling-hand equilibrium of $\mathcal{G}$.

---

## 11. The Pareto Result

**Theorem 11.1.** *In the bargaining game $\mathcal{G}$ with a welfare selection rule, any trembling-hand equilibrium outcome is not subjectively Pareto-dominated.*

*Proof.* Suppose $\sigma^*$ is a trembling-hand equilibrium with outcome $O = O(\sigma^*)$, and suppose $O^*$ subjectively Pareto-dominates $O$. Let $j$ be a decision-point with $U_j(O^*) > U_j(O)$.

Since $\sigma^*$ is a trembling-hand equilibrium, it is the limit of Nash equilibria $\sigma^\epsilon$ of perturbed games $\mathcal{G}^\epsilon$ where every strategy is played with probability at least $\epsilon$. In particular, for each $i \neq j$, the strategy $(b_i^*, \{O^*\})$ is played by $d_i$ with probability at least $\epsilon$.

Consider $d_j$ deviating from $\sigma^*_j = (b_j, \mathcal{A}_j)$ to $\hat{\sigma}_j = (b_j, \mathcal{A}_j \cup \{O^*\})$ in $\mathcal{G}^\epsilon$.

The event $E_\epsilon$ that every $d_i$ ($i \neq j$) plays $(b_i^*, \{O^*\})$ has probability at least $\epsilon^{n-1} > 0$. Conditional on $E_\epsilon$, the intersection becomes $\{O^*\} \cap (\mathcal{A}_j \cup \{O^*\}) = \{O^*\}$, so $\mathrm{sel}(\{O^*\}) = O^*$. The expected utility gain includes:

$\epsilon^{n-1} \cdot [U_j(O^*) - U_j(O)] > 0.$

Additional terms from other profiles are bounded and $O(\epsilon)$; for small enough $\epsilon$, the above dominates. The deviation is strictly profitable in $\mathcal{G}^\epsilon$, contradicting that $\sigma^\epsilon$ is a Nash equilibrium. $\square$

**Remark 11.2** (On the selection rule). The proof only uses that $\mathrm{sel}(\{O^*\}) = O^*$ — any selection rule returning the unique element of a singleton works. The welfare assumption matters for determining *which* Pareto-optimal outcome is selected at equilibrium, not for the Pareto result itself.

**Remark 11.3** (Heterogeneous beliefs). Since different $d_i$ may assign different probabilities to the same events, the $U_i$ are genuinely distinct. Subjective Pareto dominance asks that every decision-point, reasoning from its own world-model, weakly prefers $O^*$. No common prior is required.

**Remark 11.4** (What harmony does not guarantee). Theorem 11.1 shows harmonious profiles are Pareto-optimal. It does not show that all Pareto-optimal profiles are harmonious, nor that there is a unique harmonious profile. Multiple harmonious profiles may coexist; selection among them requires additional principles (e.g., a bargaining solution applied to the $U_i$).

---

## 12. Epistemic Coherence Across Decision-Points

The bargaining game treats decision-points as arbitrary agents with distinct beliefs. Theorem 11.1 holds in full generality. But for decision-points intended to be *instances of the same computational procedure* — e.g., the same agent at different times, or logically related branches of a reasoning process — we expect additional epistemic coherence.

### 12.1 Same-Ontology Coherence

When two decision-points share the same world-model space $\hat{X}$ (i.e., $\hat{X}_i = \hat{X}_j = \hat{X}$, differing only in their measures $\mathbf{X}_i \neq \mathbf{X}_j$), the superconditioning framework of §§1–4 applies directly. The pair $(\hat{\mathbf{X}}_i, \hat{\mathbf{X}}_j)$ is a prior-posterior pair, and we can ask whether a conditioning model exists.

By the classical Diaconis–Zabell theorem (Theorem 2.4 with $\hat{C} = \hat{X}$, $\mathbf{c} = \mathbf{c}' = \mathrm{id}$), a conditioning model exists iff $\mathbf{X}_j \ll \mathbf{X}_i$ and $\|d\mathbf{X}_j / d\mathbf{X}_i\|_\infty < \infty$.

But mere existence of a conditioning model says little — any bounded belief shift admits one (§1.3). The interesting structure comes from the anticipation.

**Definition 12.1 (Epistemically Coherent Pair).** Two decision-points $d_i$ and $d_j$ with $\hat{X}_i = \hat{X}_j = \hat{X}$ are *epistemically coherent* if there exists a calibrated anticipation structure $(\overline{A}, \kappa)$ on $\hat{\mathbf{X}}_i$ (targeting $\hat{X}$, in the sense of Definition 3.1) such that $\mathbf{X}_j = \mathbf{X}_i(\cdot \mid \overline{a}_0)$ for some atom $\overline{a}_0$ of $\overline{A}$.

That is: $d_j$'s beliefs arise from conditioning $d_i$'s beliefs on an anticipation state — a scenario that $d_i$ already expected as a possible future. The calibration condition (Definition 3.5) ensures $\mathbf{X}_i(\cdot \mid \overline{a}) = \kappa_{\overline{a}}$ for all atoms $\overline{a}$, so $d_i$'s conditional beliefs in each anticipated state match what $d_i$ intends those states to represent.

This is a calibrated refinement model (Definition 6.2) with $\overline{A}^+ = \overline{A}$ (no additional refinement needed): the evidence is $\overline{a}_0 \in \overline{A}$ itself.

### 12.2 Cross-Ontology Coherence

When the world-models differ ($\hat{X}_i \neq \hat{X}_j$), epistemic coherence requires the cross-ontology framework. A common information structure $(\hat{C}, \mathbf{c}_i, \mathbf{c}_j)$ (Definition 2.1) relates the ontologies:

- $\mathbf{c}_i\colon \hat{X}_i \to \hat{C}$: interpreting shared propositions in $\hat{X}_i$,
- $\mathbf{c}_j\colon \hat{X}_j \to \hat{C}$: interpreting shared propositions in $\hat{X}_j$.

Two events $\overline{x}_i \in \overline{X}_i$ and $\overline{x}_j \in \overline{X}_j$ represent the same proposition when $\mathbf{c}_i(\overline{x}_i) = \mathbf{c}_j(\overline{x}_j)$ in $\overline{C}$ (i.e., they have the same image in the shared language).

**Definition 12.2 (Cross-Ontology Epistemic Coherence).** Decision-points $d_i$ and $d_j$ with different world-models are *epistemically coherent* (relative to a common information structure $(\hat{C}, \mathbf{c}_i, \mathbf{c}_j)$) if:

1. The $\hat{C}$-compatible conditioning model for $(\hat{\mathbf{X}}_i, \hat{\mathbf{X}}_j)$ exists: $\mathbf{C}_j \ll \mathbf{C}_i$ with bounded density (Theorem 2.4), where $\mathbf{C}_k = (\mathbf{c}_k)_* \mathbf{X}_k$;
2. There exists a cross-ontology anticipation structure $(\overline{A}, \kappa)$ on $\hat{\mathbf{X}}_i$ targeting $\hat{X}_j$ (Definition 3.1), $\hat{C}$-calibrated in the sense of Definition 5.1.

Condition (1) ensures the belief shift is legitimate on shared ground. Condition (2) ensures $d_i$ anticipated $d_j$'s beliefs.

Full treatment of cross-ontology coherence also requires specifying how the utility functions $u_i$ and $u_j$ relate across different $\hat{X}_i$; this involves additional structure on the common information (requiring $u_i$ and $u_j$ to agree on shared propositions) and will not be fully developed here.

### 12.3 Coherence Constrains the Bargaining Outcome

When decision-points are epistemically coherent, the bargaining game acquires additional structure. A decision-point $d_j$ whose beliefs $\mathbf{X}_j$ are a calibrated update of $d_i$'s beliefs $\mathbf{X}_i$ has — under calibration — beliefs that $d_i$ already anticipated.

**Claim 12.3.** *If $d_j$ is an epistemically coherent update of $d_i$ (same-ontology, Definition 12.1), then the optimal batna and acceptable set for $d_j$ in the bargaining game are endorsed by $d_i$: $d_i$'s anticipation structure assigns positive probability to the scenario in which $\mathbf{X}_j$ is realized, and $d_i$'s conditional expected utility under that scenario agrees with $d_j$'s unconditional expected utility.*

More precisely: under calibration, $\mathbf{X}_i(\cdot \mid \overline{a}_0) = \kappa_{\overline{a}_0} = \mathbf{X}_j$, so for any outcome $O$:

$\mathbb{E}_{\mathbf{X}_i}[u_i(O, \cdot) \mid \overline{a}_0] = \mathbb{E}_{\mathbf{X}_j}[u_j(O, \cdot)]$

provided $u_i = u_j$ (the utility function is the same across the coherent pair). This means $d_i$, conditional on anticipation state $\overline{a}_0$, agrees with $d_j$ about the value of every outcome.

This claim is not yet a theorem in the sense that it does not determine the *equilibrium selection* — but it establishes that epistemically coherent decision-points do not merely achieve a Pareto-optimal outcome via bargaining; they achieve an outcome *consistent with what the prior decision-point planned for*.

---

## 13. Classical UDT as a Special Case

### 13.1 Recovery

**Theorem 13.1.** *Suppose all decision-points $\{d_i\}$ carry the same prior $\mathbf{X}$ on $\hat{X}$ (i.e., $\mathbf{X}_i = \mathbf{X}$ for all $i$) and the same utility function $u$. Then:*

1. *$U_i(O) = U_j(O)$ for all $i, j$, and subjective Pareto dominance collapses to: $O^*$ dominates $O$ iff $\mathbb{E}_{\mathbf{X}}[u(O^*, \cdot)] > \mathbb{E}_{\mathbf{X}}[u(O, \cdot)]$.*
2. *The unique outcome surviving Theorem 11.1 is $O^* = \arg\max_O \mathbb{E}_{\mathbf{X}}[u(O, \cdot)]$, the classical UDT optimum.*

*Proof.* For (1), all $U_i$ are the same function of $O$, so Pareto dominance collapses to strict inequality. For (2), any $O$ with $\mathbb{E}_\mathbf{X}[u(O, \cdot)] < \max_{O'} \mathbb{E}_\mathbf{X}[u(O', \cdot)]$ is subjectively Pareto-dominated by $O^*$, hence not harmonious by Theorem 11.1. $O^*$ is itself harmonious (no profitable deviation exists when all agree it is optimal). $\square$

### 13.2 Why Updatelessness

**Remark 13.2.** Classical UDT arises from $\mathbf{X}_i = \mathbf{X}$, *not* from conditionalized priors $\mathbf{X}_i = \mathbf{X}(\cdot \mid \overline{e}_i)$ for observation events $\overline{e}_i$. If instances update to their conditionalized beliefs, they disagree about which outcome is best (an instance observing $\overline{e}_i$ evaluates outcomes as $\mathbb{E}_\mathbf{X}[u(\cdot) \mid \overline{e}_i]$, which differs across $i$). This disagreement allows Pareto-suboptimal outcomes to survive as equilibria.

The UDT prescription — do not update before acting — is precisely the prescription to maintain $\mathbf{X}_i = \mathbf{X}$, ensuring unanimous agreement on the globally optimal outcome and hence a unique harmonious profile.

This gives a decision-theoretic *justification* for the UDT prescription via harmony. The policy-before-updating rule is not an assumption; it is what all instances would agree to adopt *before* any of them receives their observation, because maintaining $\mathbf{X}_i = \mathbf{X}$ (rather than updating) is the unique strategy profile ensuring a harmonious outcome. Updating breaks harmony by introducing disagreement.

### 13.3 The Heterogeneous Case

In the heterogeneous case (genuinely different $\mathbf{X}_i$, not arising from a common prior by conditioning), there is no single "correct" prior from which to evaluate policies. Harmony still applies and guarantees Pareto-optimality (Theorem 11.1), but there may be multiple Pareto-optimal outcomes. Selection among these is the role of a bargaining solution concept.

This is the genuinely new territory of heterogeneous UDT: the framework does not collapse to expected utility maximization under a single measure, but instead identifies the Pareto frontier and asks agents to coordinate on a point of it.

---

## 14. The Notion of "Same Decision-Point"

What determines whether two computational instances count as *the same* decision-point (and hence should be coordinated), versus *different* decision-points (and hence should coordinate via bargaining)?

In classical UDT, this is answered by logical equivalence: instances of the same source code, running on identical inputs, are the same decision-point; instances on different inputs may differ but are coordinated by the shared prior. In the heterogeneous setting, the analogous criterion is epistemic coherence (Definition 12.1): two instances are "the same procedure at different informational states" iff one's beliefs are a calibrated update of the other's, within the other's own anticipation structure.

This gives a partial order on decision-points: $d_j$ is *downstream* of $d_i$ iff $\mathbf{X}_j = \mathbf{X}_i(\cdot \mid \overline{a}_0)$ for some anticipation atom $\overline{a}_0$ in a calibrated anticipation structure on $\hat{\mathbf{X}}_i$. A set of decision-points forming a chain in this order can be coordinated via a single "prior" decision-point's anticipation structure (this is calibrated refinement, §6.3). A set not forming such a chain — e.g., agents with genuinely incompatible ontologies — must coordinate purely via bargaining.

The full picture is a *mixed* theory: within epistemically coherent clusters, UDT-style policy coordination applies; across clusters, bargaining equilibria are the relevant solution concept. The connection between the two levels — exactly how the within-cluster structure constrains the between-cluster bargaining — remains to be worked out.

---

## 15. Open Questions

### Part I (Superconditioning)

1. **Quantifying refinement.** How much refinement does a given $\mathbf{P}'$ require relative to $\overline{A}$? The conditional entropy of $d\mathbf{P}'/d\mathbf{P}$ given $\overline{A}$ — measuring density variation within anticipation fibers — is a natural candidate.

2. **Relationship to logical induction.** How does calibrated refinement relate to Eisenstat's Bayesian logical induction, where the anticipation structure is generated by the agent's deductive process?

3. **Self-reference.** With $Q = P$, calibration ($\mathbf{P}(\cdot \mid \overline{a}) = \kappa_{\overline{a}}$) is a fixed-point condition: the agent's probability space encodes measures over itself. Manageable when $\overline{A}$ has finitely many atoms; foundationally subtle in the limit (cf. Harsanyi's universal type space).

4. **Approximate common information.** Relaxing exact homomorphisms $\mathbf{c}, \mathbf{c}'$ to approximate ones, modeling imperfect ontology translation.

5. **Sharper semantic constraints?** Is there a principled constraint — between calibration (non-restrictive) and $\overline{A}$-compatibility (severely restrictive) — that restricts posteriors non-trivially by leveraging what $\mathbf{P}$ thinks about $\mathbf{P}'$? The negative result of Theorem 4.5 suggests that the answer, if it exists, must constrain how $\overline{l}$ interacts with the anticipation-future joint, not merely the joint itself.

### Part II (Heterogeneous UDT)

6. **Formal endorsement theorem.** Claim 12.3 needs a precise formulation connecting the anticipation structure's conditional expectations to the downstream decision-point's expected utilities, and a proof that endorsement constrains the equilibrium selection.

7. **Cross-ontology utility.** When $\hat{X}_i \neq \hat{X}_j$, saying $u_i$ and $u_j$ "agree" requires semantic grounding via the common information structure (§12.2). How should the utility function transform under ontological shifts? One approach: require $u_i(O, x_i) = u_j(O, x_j)$ whenever $\mathbf{c}_i(x_i) = \mathbf{c}_j(x_j)$ — utility agrees on shared propositions. This may be too strong or too weak depending on the application.

8. **Unique harmonious outcome.** Theorem 11.1 establishes Pareto-optimality but not uniqueness. Uniqueness likely requires a specific bargaining solution (Nash, Kalai-Smorodinsky, etc.) applied to the $U_i$. The right choice under heterogeneous beliefs is open.

9. **Logical uncertainty.** The framework assumes each $d_i$ has a well-defined probability space $\hat{\mathbf{X}}_i$. Under logical uncertainty, this fails: the agent may be uncertain about which computation it is. Extending the framework to handle logical uncertainty in the world-model itself is the central remaining challenge for a fully general heterogeneous UDT.

10. **Infinite decision-point collections.** Theorem 11.1 is stated for finite collections. For countably or uncountably many decision-points (as in problems involving all logical copies of an agent), the bargaining game and the trembling-hand notion require measure-theoretic generalization.

---

## References

**Diaconis, P. and Zabell, S. L. (1982).** "Updating Subjective Probability." *JASA* 77(380), 822–830.

**Huttegger, S. M. (2024).** "Superconditioning." *Philosophical Studies* 181, 811–833.

**Selten, R. (1975).** "Reexamination of the Perfectness Concept for Equilibrium Points in Extensive Games." *International Journal of Game Theory* 4(1), 25–55.

**Soares, N. and Fallenstein, B. (2014).** "Toward Idealized Decision Theory." *MIRI Technical Report.*
