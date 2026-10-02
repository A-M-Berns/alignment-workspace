# UDT1.01 Formalism

UDT1.01 is Diffractor's (Alexander Appel's) bounded formalization of Updateless Decision Theory, addressing the computational intractability of UDT1.1. Where UDT1.1 selects an optimal policy from the space of all observation-to-action mappings (doubly exponential in the observation sequence length), UDT1.01 performs local gradient ascent in policy space: at each observation, it selects the action whose marginal expected-utility influence is highest from the prior's perspective. The derivation proceeds through five assumptions about influence measures, yielding a recursive function $f^0_{h,\bar{S}_h}$ that the agent argmaxes at each decision point.

---

## Formal Setup

In our standard notation (translating from Diffractor's native formalism via notation.md section 5.3):

| Symbol | Meaning |
|--------|---------|
| $\mathcal{R}\ddot{O}$ | Finite set of (plannable) observations |
| $\mathcal{R}\ddot{A}$ | Finite set of actions |
| $h \in (\mathcal{R}\ddot{O})^{\leq n}$ | Observation history (sequence of length $\leq n$) |
| $\hat{\mathbf{X}}_{h_{1:k}}$ | Epistemic state at partial history $h_{1:k}$ (a probability space) |
| $\bar{S}_h$ | Full sequence of epistemic states encountered on the path to $h$ |
| $\pi : (\mathcal{R}\ddot{O})^{<n} \to \mathcal{R}\ddot{A}$ | A deterministic policy |

An **algorithm** (rich policy) $A$ maps a history $h$ together with its epistemic-state sequence $\bar{S}_h$ to a distribution over $\mathcal{R}\ddot{A}$. This is richer than a deterministic policy because $A$ can condition on unplannable information (the epistemic states). The environment function has type $e : \Pi \times (\mathcal{R}\ddot{O})^{<n} \to \Delta(\mathcal{R}\ddot{O})$, making observations depend on the full policy -- the signature of a prediction-dependent (Newcomb-like) environment.

---

## Key Assumptions

UDT1.01's derivation rests on five numbered assumptions. The first three (from Post 6) set up the influence calculus:

**Assumption 1 (Influence limits exist).** For every algorithm $A$, history $h$, and observation $o$, the derivatives of observation-probability and conditional expected-utility with respect to $\varepsilon$-mixing in $A$ at $h$ exist. These limits define the **influence measures** $\mathbb{I}^{\mathbb{P}}_{h_{1:k}}(A,h,o)$ (influence on probability of $o$) and $\mathbb{I}^{\mathbb{E}}_{h_{1:k}}(A,h,o)$ (influence on conditional expected utility given $o$).

**Assumption 2 (Expected utility decomposition).** Conditional expected utility decomposes as the standard sum $\mathbb{E}_{h_{1:k}}[U] = \sum_o \mathbb{P}_{h_{1:k}}(o)\,\mathbb{E}_{h_{1:k}}[U \mid o]$, even under $\varepsilon$-mixing. This is a one-step coherence condition enforced by dutch-book arguments.

**Assumption 3 (Only average behavior matters).** For observations $o$ off the agent's current branch ($o \neq h_{k+1}$), the influence of algorithm $A$ matches that of $\bar{A}_{h,k}$ -- the precommitment that randomizes according to $h_{1:k}$'s estimate of what $A$ would do. This is a **strategy-stealing assumption**: acausal and retrocausal effects depend only on the agent's average behavior, not on the process generating it.

**Connection to DD.** Assumption 3 is the UDT1.01 analogue of decision-determination. Both say the environment responds to the agent's *behavioral profile* (external policy $\ddot{\Pi}$), not to its internal decision procedure ($D_{I,B}$ beyond $\ddot{\Pi}$). In UDT1.01's terms: predictors track average behavior, not the algorithm that produces it.

---

## Influence Measures and Local Affineness

The influence of action $a$ at history $h$, as assessed from epistemic state $h_{1:k}$, decomposes via Lemma 1 (Post 6) into:

$$\mathbb{I}^{\mathbb{E}}_{h_{1:k}}(A,h) = \sum_o \bigl[\mathbb{P}_{h_{1:k}}(o)\,\mathbb{I}^{\mathbb{E}}_{h_{1:k}}(A,h,o) + \mathbb{I}^{\mathbb{P}}_{h_{1:k}}(A,h,o)\,\mathbb{E}_{h_{1:k}}[U \mid o]\bigr]$$

The first summand captures **acausal/cross-branch influence** (changing the quality of timelines), the second captures **retrocausal influence** (changing the probability of timelines). **Assumption 5 (Affineness)**: influence is affine in the action distribution, so $\mathbb{I}(\mu,h,o) = \mathbb{E}_{a \sim \mu}[\mathbb{I}(a,h,o)]$. This makes influence behave like a derivative and enables expectation-shuffling.

---

## Conservation of Expected Gain

Conservation of Expected Influence (CEI) -- the claim that $\mathbb{I}^{\mathbb{E}}_{h_{1:k}}(A,h,h_{k+1}) = \mathbb{E}_{h_{1:k}}[\mathbb{I}^{\mathbb{E}}_{h_{1:k+1}}(A,h) \mid h_{k+1}]$ -- fails. The failure arises from **diffuse influence**: predictors that track average behavior implicitly update on unplannable information, creating a gap between current and expected-future influence assessments.

**Assumption 4 (Conservation of Expected Gain, CEG)** resolves this by noting that diffuse influences cancel between $A$ and its precommitment approximation $\bar{A}_{h,k}$:

$$\mathbb{I}^{\mathbb{E}}_{h_{1:k}}(A,h,h_{k+1}) - \mathbb{I}^{\mathbb{E}}_{h_{1:k}}(\bar{A}_{h,k},h,h_{k+1}) = \mathbb{E}_{h_{1:k}}\bigl[\mathbb{I}^{\mathbb{E}}_{h_{1:k+1}}(A,h) - \mathbb{I}^{\mathbb{E}}_{h_{1:k+1}}(\bar{A}_{h,k},h) \;\big|\; h_{k+1}\bigr]$$

CEG acts as a **soft commitment mechanism**: the agent's current assessment of a precommitment's value anchors future evaluation, but can be overridden when reality diverges substantially from expectations.

---

## The Algorithm

Define $f^k_{h,\bar{S}_h} : \mathcal{R}\ddot{A} \to \mathbb{R}$ recursively. For $k = |h|$ (the base case at the decision point):

$$f^{|h|}_{h,\bar{S}_h}(a) = \sum_o \bigl[\mathbb{P}_h(o)\,\mathbb{I}^{\mathbb{E}}_h(a,h,o) + \mathbb{I}^{\mathbb{P}}_h(a,h,o)\,\mathbb{E}_h[U \mid o]\bigr]$$

For $k < |h|$ (recursive step tracing back toward the prior):

$$f^k_{h,\bar{S}_h}(a) = \sum_o \bigl[\mathbb{P}_{h_{1:k}}(o)\,\mathbb{I}^{\mathbb{E}}_{h_{1:k}}(a,h,o) + \mathbb{I}^{\mathbb{P}}_{h_{1:k}}(a,h,o)\,\mathbb{E}_{h_{1:k}}[U \mid o]\bigr] - \mathbb{P}_{h_{1:k}}(h_{k+1})\,\mathbb{E}_{h_{1:k}}[\mathbb{I}^{\mathbb{E}}_{h_{1:k+1}}(a,h) \mid h_{k+1}] + \frac{\mathbb{P}_{h_{1:k}}(h)}{\mathbb{P}_{h_{1:k+1}}(h)}\,f^{k+1}_{h,\bar{S}_h}(a)$$

The **UDT1.01 decision rule** at history $h$ with epistemic-state sequence $\bar{S}_h$ is:

$$\text{UDT1.01}(h,\bar{S}_h) := \arg\max_{a \in \mathcal{R}\ddot{A}}\; f^0_{h,\bar{S}_h}(a)$$

The function $f^0$ aggregates influence assessments from every past epistemic state back to the prior, weighting each by $\mathbb{P}_{h_{1:k}}(h)/\mathbb{P}_{h_{1:k+1}}(h)$ -- a ratio that amplifies contributions from epistemic states that assign higher probability to $h$ occurring.

---

## Tiling Theorem

**Theorem 2.** Under Assumptions 1-5, for any competitor algorithm $A$ and history $h$:

$$\mathbb{I}^{\mathbb{E}}_\emptyset(\text{UDT1.01}, h) \geq \mathbb{I}^{\mathbb{E}}_\emptyset(A, h)$$

That is, from the prior's perspective, no algorithm has higher marginal expected-utility influence than UDT1.01 at any decision point. The proof is immediate: $f^0$ is affine (Lemma 2), so $f^0(A(h,\bar{S}_h)) = \mathbb{E}_{a \sim A}[f^0(a)] \leq \max_a f^0(a) = f^0(\text{UDT1.01}(h,\bar{S}_h))$. This is the **self-re-derivation** (tiling) property: a UDT1.01 agent, asked which algorithm to deploy at any future decision point, re-derives UDT1.01.

---

## Relationship to C&T Framework

| UDT1.01 concept | Standard (C&T) equivalent | Notes |
|-----------------|--------------------------|-------|
| Source code / algorithm identity | $D_{I,B}$ (agent dynamics) | What the agent *is*, computationally |
| $\text{output}(A, h)$ | $\Pi^*(o)$ (chosen policy at observation) | Policy evaluation at a decision point |
| Epistemic state $\mathbb{S}_{h_{1:k}}$ | Not directly modeled | C&T abstracts over computational bounds |
| Logical counterfactual | Conditioning on $\Pi^*(o) = a$ | UDT conditioning type |
| Plannable observations | $\ddot{O}$ (external observations) | What the agent sees from the environment |
| Unplannable observations | Aspects of $\dot{O}$ or $D_B$ | Internal computational states |
| $\bar{A}_{h,k}$ (precommitment approx.) | Not directly modeled | Bounded-computation artifact |
| Assumption 3 (avg. behavior matters) | Decision-determination condition (2) | Environment depends on $\ddot{\Pi}$, not $D_{I,B}$ |

The key difference: UDT1.01 explicitly models computational boundedness through the plannable/unplannable distinction and epistemic-state sequences, while the C&T framework abstracts this away, working directly with the external policy $\ddot{\Pi}$ as the decision-relevant quantity.

---

## Open Questions

From Diffractor's Post 10, several problems remain open:

- **UDT game theory**: behavior when two UDT1.01 agents interact in repeated games
- **UDT1.1 coordination**: achieving cross-instance policy coordination (related to bargaining and harmony)
- **Chunking/splitting**: dynamically coarse-graining or fine-graining the observation space
- **Externalizing observations**: formalizing "treat computation results as plannable observations" to strengthen Assumption 3
- **Updateless value learning**: extending UDT1.01 when the utility function is learned over time
- **Inductor compatibility**: finding a logical-inductor-like mechanism where the assumptions hold approximately

---

## Cross-Framework Structural Differences

The [concept-mapping table above](#relationship-to-ct-framework) shows how C&T and UDT1.01 terms correspond, but the frameworks differ along four orthogonal structural dimensions:

| Dimension | C&T | UDT1.01 |
|-----------|-----|---------|
| **Observation classification** | By *source*: $\dot{O}$ from $I$, $\ddot{O}$ from $E$ | By *tractability*: plannable $h$ (can write lookup-table policy) vs. unplanned $S$ (cannot) |
| **Self-uncertainty** | In $D_B$ (mechanism): given $D_B$ and $O$, action is determined | In $S$ (epistemics): given $h$, epistemic state $S$ is uncertain until "thinking" occurs |
| **Instance granularity** | Coarse: one instance per $\ddot{O}$ value; different $\dot{O}$ values are internal detail | Fine: one instance per $(h, S)$ pair; a C&T instance = a family $\{(h, S) : S \text{ varies}\}$ |
| **Legitimacy** | Explicit: $\hat{O}$ (semantic) vs. $\check{O}$ (side channel) distinguishes legitimate from illegitimate internal information | No explicit distinction: all $S$ treated symmetrically, manipulation of $S$ left implicit |

The source/tractability distinction is genuinely orthogonal: external observations $\ddot{O}$ are typically plannable, but internal observations $\dot{O}$ may be either plannable (predictable memories) or unplanned (computation outputs). The self-uncertainty duality reflects two ways of locating the same phenomenon -- action-uncertainty from self-ignorance -- with C&T placing it in the mechanism ($D_B$) and UDT1.01 placing it in the epistemic state ($S$).

---

## Multi-Agent Interpretation of CEG

The [formal CEG statement above](#conservation-of-expected-gain) describes the mechanism (diffuse influences cancel between $A$ and $\bar{A}_{h,k}$). The multi-agent interpretation gives this a coordination reading.

Each instance $(h, S)$ does not optimize for its own current beliefs. Instead, CEG ensures that instance $(h, S)$ optimizes for the *prior-weighted* expected utility across all epistemic states at $h$:

$$\text{Instance }(h, S)\text{ acts for }\sum_{S'} \mathbf{P}(S')\,\mathbb{E}_{S'}[U \mid \text{action}]$$

rather than just $\mathbb{E}_S[U \mid \text{action}]$. This is a **non-interference** property: instance $(h, S)$ does not hijack the policy to serve its own epistemic state but acts for the benefit of all instances, weighted by the prior probability of each $S'$ occurring.

The prior $\mathbf{P}$ thus serves as an **arbitration mechanism** -- the weighting that all instances agreed to before knowing which epistemic state they would inhabit. This is the "social contract" reading: the prior is a veil-of-ignorance agreement among instances, and CEG is the constraint that each instance honors that agreement even after learning its own $S$.

---

## See Also

- [Policy Types](policy-types.md) -- the policy $\Pi^*$ that UDT1.01 implements, and its factorization
- [Decision-Determination](decision-determination.md) -- the fairness condition that Assumption 3 approximates
- [Bargaining and Harmony](bargaining-and-harmony.md) -- cross-instance coordination, the UDT1.1 ideal
- [Self-Trust](self-trust.md) -- the C&T framework's tiling-like result, parallel to Theorem 2
- `Decision-Points` -- the heterogeneous generalization of UDT decision structure
