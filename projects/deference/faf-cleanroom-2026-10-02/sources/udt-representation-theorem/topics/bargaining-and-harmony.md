# Bargaining and Harmony

The bargaining game formalizes the harmony condition for heterogeneous decision-points: each $d_i$ proposes a batna and an acceptable set of joint outcomes, and a welfare-consistent selection rule picks from the intersection. Harmony is identified with trembling-hand equilibrium of this game. The central result (Theorem 11.1) is that any harmonious outcome is not subjectively Pareto-dominated -- coordination through bargaining avoids waste even when decision-points hold genuinely different beliefs.

---

## The Bargaining Game

### Motivation

Classical UDT's policy-before-updating criterion enforces coordination across decision instances: no instance wishes it had acted differently, given what others did. The bargaining game generalizes this by asking that no decision-point wishes to *modify the computation* of any other.

**Definition 10.1 (Harmony).** A strategy profile $\sigma = (\sigma_i)_i$ is *harmonious* if no decision-point has a profitable unilateral deviation that modifies the computation of any other decision-point's action.

### Formal Structure

**Definition 10.2 (Bargaining Game).** The *bargaining game* $\mathcal{G}$ for a collection of `decision-points` $\{d_i\}$ has:

- **Strategies.** A strategy for $d_i$ is a pair $\sigma_i = (b_i, \mathcal{A}_i)$ where:
  - $b_i \in A_i$ is a *batna* (best alternative to negotiated agreement) -- the basic action taken if no deal is reached;
  - $\mathcal{A}_i \subseteq A$ is a finite set of *acceptable outcomes*.

- **Outcome rule.** Let $b = (b_1, \ldots, b_n) \in A$ be the batna profile. The realized outcome is:

$$O(\sigma) = \begin{cases} \mathrm{sel}\!\left(\bigcap_i \mathcal{A}_i\right) & \text{if } \bigcap_i \mathcal{A}_i \neq \emptyset, \\ b & \text{otherwise.}\end{cases}$$

- **Selection rule.** $\mathrm{sel}(S)$ selects an outcome from a nonempty finite set $S \subseteq A$.

### Welfare Selection

**Definition 10.3 (Welfare Selection Rule).** A selection rule $\mathrm{sel}$ is a *welfare selection rule* if there exists a function $W \colon A \to \mathbb{R}$ satisfying:

1. **Pareto-consistency:** if $O^*$ subjectively Pareto-dominates $O$ then $W(O^*) > W(O)$;
2. **Selection:** $\mathrm{sel}(S) = \arg\max_{O \in S} W(O)$ (breaking ties arbitrarily but consistently).

One natural choice is $W(O) = \sum_i \tilde{U}_i(O)$ where $\tilde{U}_i$ normalizes $U_i$ to $[0, 1]$, but any Pareto-consistent aggregation suffices. The existence of a Pareto-consistent $W$ follows from a standard argument whenever $A$ is finite and each $U_i$ is real-valued.

## Trembling-Hand Equilibrium

**Definition 10.4 (Trembling-Hand Equilibrium).** A strategy profile $\sigma^*$ is a *trembling-hand equilibrium* of $\mathcal{G}$ if there exists a sequence of perturbed games $\mathcal{G}^\epsilon$ (in which every strategy is played with probability at least $\epsilon > 0$) and corresponding Nash equilibria $\sigma^\epsilon$ of $\mathcal{G}^\epsilon$ such that $\sigma^\epsilon \to \sigma^*$ as $\epsilon \to 0$.

**Harmony is identified with this equilibrium condition:** a strategy profile is harmonious iff it is a trembling-hand equilibrium of $\mathcal{G}$.

The trembling-hand refinement matters because ordinary Nash equilibria of the bargaining game are too permissive. A decision-point might include dominated outcomes in its acceptable set without cost in a pure Nash equilibrium (since the intersection may not contain them), but the trembling-hand perturbation ensures that every proposal has a small chance of being the only one on the table.

## The Pareto Result

**Theorem 11.1.** *In the bargaining game $\mathcal{G}$ with a welfare selection rule, any trembling-hand equilibrium outcome is not subjectively Pareto-dominated.*

### Proof Sketch

Suppose $\sigma^*$ is a trembling-hand equilibrium with outcome $O = O(\sigma^*)$, and suppose for contradiction that $O^*$ subjectively Pareto-dominates $O$. Let $j$ be a decision-point with $U_j(O^*) > U_j(O)$.

Since $\sigma^*$ is the limit of Nash equilibria $\sigma^\epsilon$ of perturbed games $\mathcal{G}^\epsilon$, every strategy is played with probability at least $\epsilon$. Consider $d_j$ deviating from $(b_j, \mathcal{A}_j)$ to $(b_j, \mathcal{A}_j \cup \{O^*\})$.

The event $E_\epsilon$ that every $d_i$ ($i \neq j$) plays a strategy with $O^* \in \mathcal{A}_i$ has probability at least $\epsilon^{n-1} > 0$. Conditional on $E_\epsilon$, the intersection includes $O^*$, and $\mathrm{sel}(\{O^*\}) = O^*$. The expected utility gain includes:

$$\epsilon^{n-1} \cdot [U_j(O^*) - U_j(O)] > 0.$$

Additional terms from other profiles are bounded and $O(\epsilon)$; for small enough $\epsilon$, the positive term dominates. The deviation is strictly profitable in $\mathcal{G}^\epsilon$, contradicting that $\sigma^\epsilon$ is a Nash equilibrium. $\square$

### Remarks

**On the selection rule (Remark 11.2).** The proof only uses that $\mathrm{sel}(\{O^*\}) = O^*$ -- any selection rule returning the unique element of a singleton works. The welfare assumption matters for determining *which* Pareto-optimal outcome is selected at equilibrium, not for the Pareto result itself.

**Heterogeneous beliefs (Remark 11.3).** Since different $d_i$ may assign different probabilities to the same events, the $U_i$ are genuinely distinct. Subjective Pareto dominance asks that every decision-point, reasoning from its own world-model $\hat{\mathbf{X}}_i$, weakly prefers $O^*$. No common prior is required.

**What harmony does not guarantee (Remark 11.4).** Theorem 11.1 shows harmonious profiles are Pareto-optimal. It does *not* show that all Pareto-optimal profiles are harmonious, nor that there is a unique harmonious profile. Multiple harmonious profiles may coexist; selection among them requires additional principles (e.g., a bargaining solution applied to the $U_i$). The question of unique harmonious outcomes is an `open problem`.

## Summary of the Logical Flow

```
Decision-points {d_i}          [decision-points.md]
       |
       v
Bargaining game G              [this file]
  - strategies (b_i, A_i)
  - welfare selection rule
       |
       v
Trembling-hand equilibrium      = Harmony
       |
       v
Theorem 11.1: Pareto-optimality
       |
       v
Classical UDT recovery          [epistemic-coherence.md]
  (when X_i = X, u_i = u)
```

## Conservation of Expected Gain (UDT1.01)

Diffractor's UDT1.01 sequence derives an independent coordination mechanism for observation-instances that converges on the same stability concept as harmony.

### Why Conservation of Expected Influence (CEI) fails

The naive hope is that an agent's current beliefs about the influence of running algorithm $A$ at a plannable situation $h$ would equal the expected future beliefs about that influence -- Conservation of Expected Influence (CEI). CEI fails because influence can be **diffuse** (spread across many epistemic timelines via average behavior) or **concentrated** (a timeline affecting itself). When the agent conditions on its future epistemic state, the diffuse component vanishes -- future-you cannot detect the cross-timeline influence that past-you was accounting for. In the Agent Simulates Predictor problem, current-you sees large positive influence from one-boxing, but future-you (having simulated Omega) sees negative influence, because updating destroyed the diffuse entanglement with the predictor. Influence is not conserved across epistemic updates.

### CEG as the correct conservation law

Instead of conserving influence directly, Diffractor shows that the **gain** -- the difference in influence between running algorithm $A$ and its precommitment approximation $\bar{A}$ -- is conserved. Translating to standard notation: let $\pi$ be a policy and $\Pi^*(\ddot{o})$ be the prior-predictive policy (the best approximation to $\pi$ computable before observing unplannable information). CEG states:

$$\mathbb{E}\bigl[\text{Influence}(\pi, h) - \text{Influence}(\Pi^*, h) \;\big|\; \ddot{o}\bigr] = \text{Influence}(\pi, h, \ddot{o}) - \text{Influence}(\Pi^*, h, \ddot{o})$$

The diffuse components cancel in the difference, leaving only concentrated (self-affecting) influence, about which future epistemic states are authoritative. This yields a recursive decomposition: the agent's current assessment of how much $\pi$ outperforms the precommitment equals the expected future assessment of the same quantity. At the optimal policy, no observation-instance can improve expected utility by unilateral deviation once cascading effects through the recursive expansion are properly accounted for.

### CEG as soft commitment

CEG functions as a **soft commitment** mechanism between observation-instances. Unlike hard precommitment (where an instance fixes its action in advance and ignores future data), CEG allows each instance to reconsider in light of new unplannable information. The correction term has the form: current beliefs equal expected future beliefs, plus a predictable-error adjustment for the precommitment. If future-you would predictably undervalue a commitment, the adjustment compensates; if future-you would predictably overvalue it, the adjustment dampens. Commitments bind softly -- they can be overridden when genuinely surprising evidence arrives, but not when the deviation was predictable in advance.

### The Prior as Social Contract

The radical probabilist multi-agent interpretation reframes the prior $\mathbf{P}$ (or $\mathbf{X}$) as a **social contract** among `decision-points`. Each instance $d_i$ is a negotiating party who agrees to use $\mathbf{P}$ as the shared arbitration mechanism for weighting interests and resolving disputes. The contract is not "believe $\mathbf{P}$" -- instances may hold radically different local beliefs $\hat{\mathbf{X}}_i$ after updating -- but rather "act as if $\mathbf{P}$ for coordination purposes."

This is a **veil of ignorance** perspective: the prior is what all instances would have agreed to before knowing which epistemic state each would occupy. Instance $d_i$, having observed $\ddot{o}_i$ and formed posterior beliefs that may diverge sharply from $\mathbf{P}$, still honors the contract because:

1. **Consequentialist justification.** Unilateral deviation breaks coordination; if $d_i$ defects, other instances may also defect, and everyone loses.
2. **Contractual justification.** The prior was (counterfactually) agreed to by all instances including $d_i$. Breaking the contract means defecting on one's other selves.
3. **Credibility justification.** An agent who honors prior commitments despite changed beliefs is the kind of agent who can make credible commitments -- a prerequisite for beneficial coordination.

The prior-as-arbitration idea connects directly to the welfare selection rule $\mathrm{sel}$ in the bargaining game: $\mathbf{P}$ provides the weighting that determines whose interests count and by how much when selecting from the intersection $\bigcap_i \mathcal{A}_i$.

### Dynamic Consistency as Contract-Following

Diffractor's UDT1.01 framework gives computational content to the social contract: the contract is to run the UDT1.01 algorithm, not to commit to specific action outputs. This is **commitment without rigidity** -- the algorithm adapts to each instance's epistemic state $S$ while still respecting the prior-based arbitration. Dynamic consistency under this reading means: even if $d_i$'s local beliefs (after radical updates) suggest a different action, $d_i$ follows the agreed-upon algorithm because its current action should be what the prior-weighted expectation endorses.

The key distinction is between *hard precommitment* (fixing actions in advance, ignoring future data) and *algorithmic commitment* (agreeing on a decision procedure that incorporates new information within the contract's constraints). CEG's correction term captures this: predictable deviations from the precommitment are dampened, but genuinely surprising evidence can override -- commitments bind softly through the algorithm rather than rigidly through fixed outputs.

### Connection to harmony

The C&T framework's [harmony condition](bargaining-and-harmony.md) (trembling-hand equilibrium of the bargaining game) and CEG both capture the same core intuition: **a stable policy profile where no participant gains from unilateral deviation**. They arrive at this from different starting points:

- **Harmony** derives stability from game-theoretic primitives: batnas $b_i$, acceptable sets $\mathcal{A}_i$, welfare selection $\mathrm{sel}$, and trembling-hand refinement. Each `decision-point` $d_i$ proposes and negotiates; stability means no $d_i$ profits from changing its proposal.
- **CEG** derives stability from information-theoretic primitives: diffuse vs. concentrated influence, affineness of influence measures, and the recursive expansion of expected gain. Each observation-instance reconsiders; stability means the gain from reconsidering is non-negative only at the optimum.

Both frameworks conclude that the optimal policy is a fixed point: no instance (whether modeled as a bargaining participant or as a node in the recursive influence expansion) can improve by unilateral deviation when downstream effects are properly internalized. CEG provides the computational mechanism (polynomial-time recursive expansion) while harmony provides the welfare guarantee (Pareto-optimality via Theorem 11.1).

---

## See Also

- `Decision-Points` -- definition of $d_i = (\hat{\mathbf{X}}_i, A_i, u_i)$, expected utility $U_i$, and subjective Pareto dominance
- `Epistemic Coherence` -- how coherence constrains bargaining; classical UDT as a special case; the mixed theory
- [Notation Standard](../notation.md) -- formal definitions: bargaining game, batna, welfare selection, harmony (Section 3.4)
