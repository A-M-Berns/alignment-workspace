# Optimal Prediction

Eisenstat's condensation theory establishes that latent variable decompositions of a joint distribution, when they achieve perfect or near-perfect condensation, are essentially unique. This uniqueness -- formalized in the exact and approximate correspondence theorems -- is the mathematical backbone of the claim that an agent's external policy $\ddot{\Pi}$ is the *canonical* latent variable mediating between agent and environment. The bridge from general condensation theory to the agent-specific setting runs through the concept of **optimal prediction**: a latent variable that best predicts the observables from the fewest degrees of freedom. This file covers the correspondence and uniqueness results from Eisenstat's theory and their intended application to the agent setting. For the general definitions of condensation, scores, and perfect condensation, see `Condensation Basics`.

---

## Natural Latents and Mediation

Wentworth and Lorell's natural latent framework identifies conditions under which a latent variable mediating between observables is essentially unique. Given observables $(\mathbf{x}_i)_{i \in I}$ and a latent $\mathbf{y}_I$, the two conditions are:

1. **Mediation**: The $\mathbf{x}_i$ are conditionally independent given $\mathbf{y}_I$.
2. **Redundancy**: For each $i_0 \in I$, the variable $\mathbf{x}_{i_0}$ is approximately conditionally independent of $\mathbf{y}_I$ given the remaining observables $(\mathbf{x}_i : i \neq i_0)$.

If two latent variables $\mathbf{y}_I$ and $\mathbf{z}_I$ both satisfy mediation and redundancy, then each is approximately conditionally independent of the observables given the other -- they carry equivalent information. Redundancy holds in many natural settings: when the number of observables is large, $\mathbf{y}_I$ can typically be recovered from any large subset, just as a coin's bias can be estimated from many flips.

Eisenstat's correspondence theorems generalize this beyond the top-level mediator $\mathbf{y}_I$ to the full hierarchy of contribution-indexed latent variables $(\mathbf{y}_A)_{A \in \mathcal{P}^+ I}$. The two error terms in the approximate correspondence theorem map directly onto these two conditions: recovery error generalizes redundancy, and redundancy violation generalizes mediation failure. The symmetric conclusion -- approximate mutual recoverability -- arises only when both conditions hold for both LVMs.

## Amalgamation

Comparing two LVMs $\mathcal{L}_1$ and $\mathcal{L}_2$ for the same RVM $\mathcal{M}$ requires placing their latent variables on a common probability space. An **amalgamation** constructs a probability space $\Lambda_0$ with probability-preserving maps $\rho_k \colon \Lambda_0 \to \Lambda_k$ ($k \in \{1, 2\}$) such that $\pi_1 \circ \rho_1 = \pi_2 \circ \rho_2$ as maps to $\Omega$.

The construction takes the fiber product $S = \{(\lambda_1, \lambda_2) : \pi_1(\lambda_1) = \pi_2(\lambda_2)\}$ and equips it with the conditional-independence coupling: for each $\omega \in \Omega$ with positive probability, the conditional distributions over the $\Lambda_1$-fiber and $\Lambda_2$-fiber above $\omega$ are taken to be independent. This ensures $\rho_1$ and $\rho_2$ are probability-preserving and the diagram commutes. After amalgamation, all $\mathbf{y}_A$ and $\mathbf{z}_A$ variables live on $\Lambda_0$ via pullback, making cross-LVM statements like "$\mathbf{y}_A$ is a function of $\mathbf{z}_{\supseteq A}$" well-defined.

## Exact Correspondence (Theorem 5.2)

**Theorem (Eisenstat).** Let $\mathcal{L}_1$ and $\mathcal{L}_2$ both perfectly condense the same RVM $\mathcal{M}$, with latents $(\mathbf{y}_A)$ and $(\mathbf{z}_A)$. In any amalgamation, $\mathbf{y}_A$ is a.e. a function of $\mathbf{z}_{\supseteq A}$, and $\mathbf{z}_A$ is a.e. a function of $\mathbf{y}_{\supseteq A}$, for all $A \in \mathcal{P}^+ I$.

The proof proceeds by induction using the ordered Markov condition (see `Condensation Basics`). Since $\mathcal{L}_2$ perfectly condenses $\mathcal{M}$, each $\mathbf{y}_A$ is a function of $\mathbf{x}_i$ for any $i \in A$, hence a function of $\mathbf{z}_{\ni i}$. The key step is a submodularity lemma: if $\mathbf{y}_A$ is a function of $\mathbf{z}_{\mathcal{F}}$ and of $\mathbf{z}_{\mathcal{G}}$, and these are conditionally independent given $\mathbf{z}_{\mathcal{F} \cap \mathcal{G}}$, then $\mathbf{y}_A$ is a function of $\mathbf{z}_{\mathcal{F} \cap \mathcal{G}}$. Repeated application across all $i \in A$ reduces $\mathbf{z}_{\ni i}$ down to $\mathbf{z}_{\supseteq A}$.

**Corollary.** $\mathbf{y}_{\supseteq A}$ and $\mathbf{z}_{\supseteq A}$ are mutually a.e. functions of each other for all $A$. This gives a structural equivalence between $\mathcal{L}_1$ and $\mathcal{L}_2$ at each level of the contribution hierarchy: perfect condensations of the same RVM are rigid.

**Agent interpretation.** Applied to the I/B/E decomposition with index set $\{I, B, E\}$: if two different models of the same agent-environment system both achieve perfect condensation, their latent variables at the $\{I, B\}$ level (which include the policy structure) must be mutually recoverable. In particular, the pairwise latent $\mathbf{y}_{\{I,B\}}$ -- which corresponds to $D_{I,B}$ and contains the external policy $\ddot{\Pi}$ -- is determined by $\mathbf{z}_{\supseteq \{I,B\}}$ and vice versa. Any two "perfect" accounts of the agent agree on what the agent's policy is.

## Approximate Submodularity (Lemma 6.1)

The exact submodularity lemma used above has a quantitative generalization. For random variables $X$, $Y_1$, $Y_2$, $C$ with finite entropy:

$$H(X \mid C) \leq H(X \mid Y_1, C) + H(X \mid Y_2, C) + I(Y_1; Y_2 \mid C)$$

The exact identity refining this is:

$$H(X \mid C) = H(X \mid Y_1, C) + H(X \mid Y_2, C) - H(X \mid Y_1, Y_2, C) + I(Y_1; Y_2; X \mid C)$$

The inequality follows by dropping the non-positive $-H(X \mid Y_1, Y_2, C)$ term and bounding the interaction information $I(Y_1; Y_2; X \mid C)$ by $I(Y_1; Y_2 \mid C)$. This lemma is the engine of the approximate correspondence theorem, converting exact "is a function of" into quantitative control on conditional entropy via induction over an intersection tree.

## Approximate Correspondence (Theorem 6.1)

**Theorem (Eisenstat).** Let $(\mathbf{x}_i)_{i \in I}$ be the RVM variables and $(\mathbf{y}_A)$, $(\mathbf{z}_A)$ the latents of two associated LVMs, in an amalgamation. For any $A \in \mathcal{P}^+ I$ and collection $\mathcal{F} \subseteq \mathcal{P}^+ I$, let $\mathcal{G} = \mathcal{F}^\circ = \{C \in \mathcal{P}^+ I : \forall B \in \mathcal{F},\, B \cap C \neq \emptyset\}$ be the polar. Then:

$$H(\mathbf{y}_{\supseteq A} \mid \mathbf{z}_{\mathcal{G}}) \leq \underbrace{\sum_{B \in \mathcal{F}} H(\mathbf{y}_{\supseteq A} \mid \mathbf{x}_B)}_{\text{recovery error}} + \underbrace{\sum_{v \in N} I(\mathbf{z}_{\mathcal{L}(v)}; \mathbf{z}_{\mathcal{R}(v)} \mid \mathbf{z}_{\mathcal{I}(v)})}_{\text{redundancy violation}}$$

where $N$ indexes the internal nodes of an intersection tree on the upward-closed subsets determined by $\mathcal{F}$.

The two kinds of error terms correspond to the two natural-latent conditions:

- **Recovery error** ($H(\mathbf{y}_{\supseteq A} \mid \mathbf{x}_B)$): How well can $\mathbf{y}$-latents be estimated from observables? Analogous to redundancy. Small when observables carry enough information to reconstruct the latent.
- **Redundancy violation** ($I(\mathbf{z}_{\mathcal{L}(v)}; \mathbf{z}_{\mathcal{R}(v)} \mid \mathbf{z}_{\mathcal{I}(v)})$): How much do $\mathbf{z}$-latents share information beyond what the contribution hierarchy dictates? Analogous to mediation failure. Zero when $\mathbf{z}$ satisfies the ordered Markov condition.

The polar $\mathcal{G}$ trades off against $\mathcal{F}$: a larger $\mathcal{F}$ gives more recovery-error terms but allows $\mathcal{G}$ to approximate $\{C : C \supseteq A\}$ more tightly. The theorem is asymmetric: interchanging $\mathbf{y}$ and $\mathbf{z}$ on the right-hand side may yield a different bound, so approximate mutual recoverability requires bounding both directions.

**Choose-$k$ corollary.** Taking $\mathcal{F}$ to be all $k$-element subsets of $A$, the polar becomes $\mathcal{G} = \{C : C \text{ contains all but at most } k-1 \text{ elements of } A\}$. If $H(\mathbf{y}_{\supseteq C} \mid \mathbf{x}_C) \leq \alpha$ for all $|C| = k$, and $\mathbf{z}$ satisfies the ordered Markov condition, then $H(\mathbf{y}_{\supseteq A} \mid \mathbf{z}_{\mathcal{G}}) \leq \binom{|A|}{k} \alpha$. This gives a concrete scaling law for how recovery error accumulates.

## Example: Coins with Continuous Bias

Let $L$ be a $[0,1]$-valued random variable (bias), and $(\mathbf{x}_i)_{i=1}^n$ conditionally independent coins with bias $L$. Since $L$ has continuous range, we discretize via a bucketing function $b$, setting $\mathbf{y}_{\{1,\dots,n\}} = b(L)$ and $\mathbf{y}_{\{i\}} = \mathbf{x}_i$. Different bucketing choices yield different LVMs for the same RVM, but as buckets shrink, these LVMs converge.

The approximate correspondence theorem formalizes this: the recovery error $H(\mathbf{y}_{\supseteq A} \mid \mathbf{x}_B)$ shrinks as $|B|$ grows (more flips reveal the bias), while the redundancy violation terms vanish entirely -- the coins are conditionally independent given the bias, so the ordered Markov condition holds and all conditional mutual information terms are zero. Any two "reasonable" LVMs for this RVM agree up to quantifiable error controlled by bucket size and sample count.

The multiple-coins variant -- several coins with independent biases, observed only through pairwise sums -- illustrates the same phenomenon with richer contribution structure. Similarly, LVMs derived from Bayesian networks (where latent variables correspond to unobserved causal ancestors) provide a natural class of examples. In the causal setting, identifiability failures correspond precisely to the recovery-error terms being large, connecting Eisenstat's framework to classical problems in latent causal discovery.

## Correspondence versus Optimality

The correspondence theorems above answer a *descriptive* question: if two observers both model the same agent-environment system with good condensations, do they agree on what the latents are? The answer is yes -- the latent structure is essentially unique. But the representation theorem needs something different. It asks a *normative* question: what should the agent's policy be?

These are distinct. Correspondence tells us that any adequate model of the agent will recover (approximately) the same $\ddot{\Pi}$. It does not tell us which $\ddot{\Pi}$ is optimal. The gap is between **intersubjectivity** (observers agree on what the policy IS) and **rationality** (what the policy SHOULD BE). Bridging this gap requires decision-determination and a rationality assumption, neither of which follows from condensation alone.

## The Bridge Argument

The bridge from condensation to UDT runs through optimal prediction in four steps:

1. **Optimal predictors extract good condensations.** If the environment optimally predicts the agent's behavior, it extracts the latent $\ddot{\Pi}$ -- the external policy -- because $\ddot{\Pi}$ is the minimal sufficient variable satisfying $H(\ddot{A} \mid \ddot{\Pi}, \ddot{O}) = 0$. An optimal predictor cannot do better than conditioning on $\ddot{\Pi}$, and any predictor that ignores $\ddot{\Pi}$ leaves predictable variance on the table.
2. **Decision-determination follows.** If the environment's response to the agent factors through its optimal prediction, and that prediction is $\ddot{\Pi}$, then $E$ is conditionally independent of $D_{I,B}$ given $\ddot{\Pi}$. This is exactly decision-determination (see [Decision-Determination](decision-determination.md)).
3. **Utility becomes a function of policy.** Under decision-determination, $U$ depends on the agent only through $\ddot{\Pi}$. The agent faces a choice among whole policies, not individual actions.
4. **The UDT formula follows.** Rationality (maximize $\mathbb{E}[U]$) applied to policy-level choice yields: $\pi(o) = \arg\max_a \mathbb{E}[U \mid \pi(o) = a]$.

The real content is in steps 1-2. The derivation from policy-based utility to the UDT formula (steps 3-4) is nearly mechanical and is machine-verified in Lean (see `lean/UDT/BasicSimple.lean`).

## Cross-Situation Dependence

The unity condition -- a single $\ddot{\Pi}$ contributing to ALL situations -- has a further consequence beyond uniqueness. Because $\ddot{\Pi}$ determines actions at every observation, the action $A_i$ at observation $o_i$ is not a free variable: it is determined by $\ddot{\Pi}$, which simultaneously determines $A_j$ at $o_j$ for every other $j$. Optimizing $A_i$ in isolation, as standard (updateful) decision theory does, ignores these cross-situation correlations.

This is the condensation-theoretic argument for why updateless reasoning is *forced*: the latent structure makes per-observation optimization incoherent. The agent must optimize $\ddot{\Pi}$ as a whole, because there is no way to vary $A_i$ at $o_i$ without simultaneously committing to the rest of $\ddot{\Pi}$'s outputs. The UDT formula $\pi(o) = \arg\max_a \mathbb{E}[U \mid \pi(o) = a]$ captures exactly this: each local choice is evaluated in terms of the global policy it implies.

## The Open Gap

The project's main research frontier is the step from general condensation theory to the agent-specific claim: **under condensation conditions on the I/B/E decomposition, optimal prediction of the environment factors through the external policy $\ddot{\Pi}$**.

In the agent setting, the RVM variables are $I$, $B$, $E$ (or their subvariables), and the latent variables include the dynamics $D_I$, $D_B$, $D_E$ at the singleton level and $D_{I,B}$ at the pairwise level. The external policy $\ddot{\Pi}$ is a coarsening of $D_{I,B}$. Decision-determination (see [Decision-Determination](decision-determination.md)) states that $E$ depends on the agent only through $\ddot{\Pi}$. The question is: under what condensation conditions does it follow that $\ddot{\Pi}$ is the *unique* (or approximately unique) latent variable mediating between agent dynamics and environment response?

The exact correspondence theorem gives a clean answer under perfect condensation: if two decompositions both perfectly condense the agent-environment system, their policy-level structure must agree. But perfect condensation is rare -- Eisenstat's characterization theorem shows it imposes strong structural constraints. The approximate theorem is more promising for real agents. It says that even with imperfect condensation, the policy is approximately the unique mediator, with explicit bounds.

Three specific sub-questions remain open:

1. **Recovery error in the agent setting.** What properties of the agent-environment interface ensure that $H(\ddot{\Pi} \mid \mathbf{x}_B)$ is small for observable subsets $B$? This requires understanding when the environment provides enough feedback to identify the agent's policy -- an analogue of estimating a coin's bias from its flips.
2. **Approximate ordered Markov condition.** When do the agent dynamics $D_I$, $D_B$, $D_E$ approximately satisfy the conditional independence structure required for the redundancy-violation terms to be small? Perfect condensation forces this exactly, but approximate versions need characterization.
3. **From approximate uniqueness to UDT.** Even given approximate uniqueness of $\ddot{\Pi}$ as mediator, the step to UDT-like reasoning -- conditioning on $\ddot{\Pi}(o) = a$ rather than on $a$ directly -- requires additional decision-theoretic argument connecting the information-theoretic uniqueness to the normative claim.

## See Also

- `Condensation Basics` -- general definitions: RVM, LVM, scores, perfect condensation, characterization theorem
- [Dynamics and Condensation](dynamics-and-condensation.md) -- agent-specific condensation variables $D_I$, $D_B$, $D_E$ and the agent dynamic constraint
- [Decision-Determination](decision-determination.md) -- the fairness condition linking $\ddot{\Pi}$ to environment response
- [Notation Standard](../notation.md) -- notation conventions and Eisenstat-to-standard translation table (SS5.2)
