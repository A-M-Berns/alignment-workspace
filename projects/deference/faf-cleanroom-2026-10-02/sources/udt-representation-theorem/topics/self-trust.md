# Self-Trust

The self-trust results are the main theorems of the Communication & Trust paper. The **Self-Trust Theorem** shows that under decision-determination, communicative alternatives, and the belief that instances follow advice, a UDT agent never strictly prefers actions that modify other instances. The **Advice-Following Theorem** shows that the advice-following belief is self-fulfilling under further conditions. Together, these results establish that communication acts as a "release valve" for self-modification pressure: anything achievable by modification is equally achievable by sending a message, so there is no incentive to interfere.

---

## The UDT Decision Rule (Per Instance)

At instance $\ddot{o}$ with internal observation $\dot{o}_{\ddot{o}}$, UDT chooses:

$$\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = \arg\max_{a_{\ddot{o}} \in \mathcal{R}A_{\ddot{o}}} \mathbb{E}[U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}]$$

The expectation is under the agent's prior, and the conditioning is on the policy output — not the action directly. This is the characteristic "updateless" feature.

## Minimally Modifying Actions

**Definition.** An action $a_{\ddot{o}} \in \mathcal{R}A_{\ddot{o}}$ is **minimally modifying** at $\dot{o}_{\ddot{o}}$ if:

$$m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \min_{a' \in \mathcal{R}A_{\ddot{o}}} m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a')$$

where $m(\cdot)$ is the modification probability $\Pr(\text{dom}(P) \neq \emptyset \mid \cdot)$. In words: among all actions the instance could take, a minimally modifying one causes the least interference with other instances.

## Communicative Alternatives

**Definition.** For $a_{\ddot{o}} \in \mathcal{R}A_{\ddot{o}}$ and $\dot{o}_{\ddot{o}} \in \mathcal{R}\dot{O}_{\ddot{o}}$, a **communicative alternative** $ca_{\dot{o}_{\ddot{o}}}(a_{\ddot{o}}) \in \mathcal{R}A_{\ddot{o}}$ satisfies:

1. $ca(a_{\ddot{o}})$ is minimally modifying at $\dot{o}_{\ddot{o}}$.
2. For all external policies $\ddot{\pi}$:

$$\Pr(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \Pr(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}),\; \ddot{\Pi} = R)$$

**Intuition.** The communicative alternative achieves the same distribution over external policies as the original action, but does so through *communication* (conditional on instances following advice) rather than through *modification*. Condition (1) ensures it avoids modification; condition (2) ensures it is equally effective at influencing the overall external policy.

The existence of communicative alternatives is an assumption on the decision structure: the communication channel must be rich enough to express any coordination that modification could achieve.

## The Communicative Expectation Lemma

**Lemma.** If a concrete decision structure is (1) decision-determined and (2) has communicative alternatives, then:

$$\mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}))$$

**Proof sketch.** By decision-determination, expected utility decomposes over external policies:

$$\mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \sum_{\ddot{\pi}} \mathbb{E}(U \mid \ddot{\Pi} = \ddot{\pi}) \cdot \Pr(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}})$$

The communicative alternative condition ensures that the distribution $\Pr(\ddot{\Pi} = \ddot{\pi} \mid \cdot)$ matches between $a_{\ddot{o}}$ and $ca(a_{\ddot{o}})$ (conditional on $\ddot{\Pi} = R$). So the weighted sums are equal.

## The Self-Trust Theorem

**Theorem (Self-Trust).** If a concrete decision structure is (1) decision-determined, (2) has communicative alternatives, and (3) has $\Pr(\ddot{\Pi} = R) = 1$, then non-minimally-modifying actions are never strictly preferred by UDT:

$$m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) > \min_{a'} m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a')$$
$$\implies$$
$$\mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) \leq \max_{a'} \mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a')$$

**Proof.** Let $a_{\ddot{o}}$ be non-minimally-modifying. By the Communicative Expectation Lemma:

$$\mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}),\; \ddot{\Pi} = R)$$

By condition (3), $\Pr(\ddot{\Pi} = R) = 1$, so this equals $\mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}))$, which is at most the maximum over all actions.

**Note on condition (3).** The condition $\Pr(\ddot{\Pi} = R) = 1$ is about the agent's *subjective* probability — the agent *expects* its instances to follow recommendations. This is a form of "self-esteem": the agent trusts itself to follow its own advice.

## Stability and Advice-Following

The Self-Trust Theorem assumes $\Pr(\ddot{\Pi} = R) = 1$ but does not prove it. The Advice-Following Theorem shows this assumption is self-fulfilling.

**Definition.** A recommendation $r$ is **stable** if for all $\ddot{o} \in \text{dom}(r)$, all $\dot{a}_{\ddot{o}}$, and all $\ddot{a}'_{\ddot{o}} \neq r(\ddot{o})$:

$$\mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, r(\ddot{o})),\; [\ddot{\Pi} = r]_{-\ddot{o}}) > \mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, \ddot{a}'_{\ddot{o}}),\; [\ddot{\Pi} = r]_{-\ddot{o}})$$

where $[\ddot{\Pi} = r]_{-\ddot{o}}$ means all *other* instances follow the recommendation. Stability says: given that everyone else follows the advice, each instance strictly prefers to follow it as well.

**Definition.** Recommendations are **internally driven** if for all $\dot{o}, \ddot{o}, \dot{a}, \ddot{a}, \ddot{a}'$:

$$\Pr(R = r \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a})) = \Pr(R = r \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}'))$$

That is, the recommendation an instance receives does not depend on that instance's external action choice. Recommendations flow from internal observations, not from the actions being evaluated.

**Theorem (Advice-Following).** If a concrete decision structure (1) has $\Pr(\ddot{\Pi} = R) = 1$, (2) has internally-driven recommendations, (3) has recommendations that are stable with probability one, and (4) instance $\ddot{o}$ receives a non-silent recommendation $s_{\ddot{o}}(`\dot{o}`_{\hat{O}}) \neq \bot$, then for all $\ddot{a}_{\ddot{o}} \neq s_{\ddot{o}}(`\dot{o}`_{\hat{O}})$:

$$\mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, s_{\ddot{o}}(`\dot{o}`_{\hat{O}}))) > \mathbb{E}(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, \ddot{a}_{\ddot{o}}))$$

If UDT is the decision rule and instances never receive recommendations and modifications simultaneously, then $\ddot{\Pi} = R$ in fact.

**Proof sketch.** Decompose expected utility over recommendations to other instances $r_{-\ddot{o}}$. By condition (1), the external policy follows $R$. By condition (2), the distribution over $r_{-\ddot{o}}$ is independent of the external action choice $\ddot{a}$. By conditions (3) and (4), each term in the sum strictly favors following the advice. Since UDT selects the maximizing action and the advice-following action dominates, the conclusion follows.

## Significance

The two theorems together establish:

1. **Self-modification is never strictly incentivized** (Self-Trust), given that the agent expects itself to follow advice.
2. **Advice-following is self-fulfilling** (Advice-Following), given stability and internally-driven recommendations.

Communication serves as the key mechanism: instead of modifying another instance to take action $X$, an instance can *recommend* $X$ through the semantic channel. If the communication protocol is rich enough (communicative alternatives exist) and stable (following advice is individually rational given that others follow), then the agent has no reason to modify itself.

The conclusion of the C&T paper suggests that "fairness" consists of at least decision-determination, communicative alternatives, and stable recommendations. The condition $\Pr(\ddot{\Pi} = R) = 1$ is described as a form of "self-esteem" — a prior belief in one's own trustworthiness that turns out to be justified.

**Radical probabilist refinement.** In the radical probabilist framework, instances may legitimately revise their beliefs in ways not forced by evidence. This raises the question of whether revising the coordination contract counts as interference. The resolution: the contract among instances must include an **amendment process**. Any instance may propose changes, and changes require agreement (or at least non-objection) from other instances. Unilateral deviation without communication is defection, but renegotiation through the amendment process is legitimate. The contract is thus a living agreement, not a rigid commitment — self-trust does not require self-rigidity.

---

## Arguments for Non-Interference

The Self-Trust Theorem establishes that non-interference is *optimal*, but does not address *why* the structural conditions (DD, communicative alternatives) hold in the first place. Four informal arguments support the claim that an agent modeling itself as unified should satisfy non-interference.

**Contractual obligation.** In the multi-agent framing, instances coordinate by an implicit contract: "we each respect each other's deliberative authority." Breaking this contract is defection — it undermines the coordination structure that makes policy-level reasoning possible. The contract-based view treats non-interference as a commitment that sustains mutual trust.

**Futility under functional identity.** If instances $\ddot{o}$ and $\ddot{o}'$ run the same algorithm, any reasoning that $\ddot{o}$ uses to justify interference with $\ddot{o}'$ is equally available to $\ddot{o}'$ (and to all other instances). If interference is permitted, it is permitted universally, and universal interference breaks coordination. Non-interference is the stable equilibrium: the only policy that survives self-application.

**Epistemic humility.** Instance $\ddot{o}$ may believe that $\ddot{o}'$ is making a suboptimal choice, but $\ddot{o}'$ has access to its own internal observation $\dot{o}_{\ddot{o}'}$, which $\ddot{o}$ does not. The apparent "mistake" may be optimal given information $\ddot{o}$ lacks. Non-interference follows from respecting each instance's epistemic position.

**Representation theorem requirement.** If $\ddot{o}$ interferes with $\ddot{o}'$, the effective policy $\Pi^\dagger$ depends on which instances have modification opportunities, not just on observations. The environment responds to this entangled structure rather than a clean policy, and decision-determination fails. Non-interference is therefore a precondition for the representation theorem to apply — without it, the derivation from DD to UDT breaks down.

These four arguments operate at different levels. The contractual and futility arguments are *game-theoretic*: they concern the strategic interaction among instances. The epistemic humility argument is *informational*: it concerns what each instance knows. The representation theorem argument is *structural*: it concerns the mathematical conditions under which UDT is derivable. Together they provide converging evidence that non-interference is not merely an assumption of convenience but a natural consequence of modeling a system as a unified agent.

## UDT1.01 Tiling as Self-Trust

Diffractor's UDT1.01 sequence establishes a **tiling theorem** (Theorem 2 in Post 8) that functions as a computational self-trust result. In the project's standard notation (via §5.3), the theorem states: for any history (observation) $\ddot{o}$ and any competitor algorithm $A$,

$$\mathbb{E}[U \mid \Pi^*(\ddot{o}) = \text{UDT1.01}(\ddot{o})] \geq \mathbb{E}[U \mid \Pi^*(\ddot{o}) = A(\ddot{o})]$$

where the expectations are taken under the prior $\mathbf{X}$. In words: a UDT1.01 agent that reconsiders its policy at any observation $\ddot{o}$ would re-derive the same policy. No alternative algorithm, even one with access to unplannable observations, can improve on the UDT1.01 output at any decision-point. The proof proceeds by showing that the influence function $f^0$ is affine in actions (Lemma 2), so that for any mixed strategy $A(\ddot{o})$, the pure argmax weakly dominates.

This parallels the C&T Self-Trust Theorem, but the two results address different aspects of self-trust:

- **UDT1.01 tiling** is about a single unified agent re-deriving its policy from scratch at each observation. It establishes **computational self-consistency**: the agent that evaluates from the prior at $\ddot{o}$ reaches the same answer it committed to ex ante. The setting assumes a single agent with a single prior $\mathbf{X}$ and a single utility $U$.
- **C&T self-trust** is about **inter-instance trust**: instance $\ddot{o}_1$ trusting the decision made at instance $\ddot{o}_2$, where each instance may have different information (different $\dot{O}_{\ddot{o}}$). The result requires the additional structure of communicative alternatives and advice-following ($\Pr(\ddot{\Pi} = R) = 1$), because coordination between instances with heterogeneous information is non-trivial.

The tiling theorem can be read as the special case where inter-instance coordination is not an issue: a single agent reconsidering at a single point. The C&T theorems extend this to the harder case where multiple instances must trust each other's decisions without being able to recompute them.

---

## Endorsement and Trust

abramdemski's endorsement framework ("Meaning & Agency") provides an external-observer perspective on what it means for one agent to trust another's decisions. The key definition, translated into the project's notation:

**Control endorsement.** Agent 1 (with beliefs $P_1$, choice function $C_1$) control-endorses Agent 2 (with beliefs $P_2$, choice function $C_2$) as optimizing $U_2$ iff:

$$C^1_{U_2, P_1}(A \mid C^2_{U_2, P_2}(A) = a) = a$$

In words: if Alice knew Bob's answer, Alice would copy it (when optimizing the same objective from her own beliefs).

This formalizes the self-trust relation between instances. Instance $\ddot{o}_1$ endorses the decision at $\ddot{o}_2$ when, knowing what $\ddot{o}_2$ chose, $\ddot{o}_1$ would make the same choice from its own prior perspective. Concretely, letting $P_1$ and $P_2$ be the prior conditioned on the respective internal observations $\dot{o}_{\ddot{o}_1}$ and $\dot{o}_{\ddot{o}_2}$, endorsement becomes:

$$\arg\max_{a \in \mathcal{R}A_{\ddot{o}_2}} \mathbb{E}[U \mid \Pi^*(\dot{o}_{\ddot{o}_2}, \ddot{o}_2) = a] = \Pi^*(\dot{o}_{\ddot{o}_2}, \ddot{o}_2)$$

which is simply the statement that instance $\ddot{o}_1$, evaluating from the prior, agrees with $\ddot{o}_2$'s UDT-optimal choice. The crucial feature is that endorsement is evaluated from the **prior** $P_1$, not from a posterior -- directly parallel to UDT's prior-based evaluation. The Van Fraassen reflection principle (future beliefs endorsed by current beliefs) is a special case: self-trust across time reduces to endorsement of a future self by the current self.

The endorsement framework provides an "external observer" interpretation of the C&T results: **self-trust holds when each instance endorses every other instance's decision**. Decision-determination ensures that utility depends only on the external policy $\ddot{\Pi}$, and the communication structure ensures that instances can verify each other's choices. Together, DD + communication yield mutual endorsement across all instances -- which is exactly what the Self-Trust Theorem establishes.

### Selection vs. Control Endorsement

The endorsement framework distinguishes two modes, which differ in what kind of utility is being optimized:

- **Selection endorsement.** The utility $U_\text{sel} : \mathcal{R}A \to \mathbb{R}$ is *pure* — it depends only on the action, not the world-state. The optimal output is fixed regardless of the environment: no beliefs are required. Selection endorsement is trivial in the sense that the system just needs to output the fixed optimum. Self-trust under selection endorsement is automatic: there is nothing for instances to disagree about.

- **Control endorsement.** The utility $U_\text{ctrl} : \Omega \to \mathbb{R}$ is *impure* — the optimal action varies with world-state. The policy must encode enough information about the environment to compute the right action at each boundary state. Beliefs are required, and the UDT formula is an instance of control endorsement. Self-trust under control endorsement is non-trivial: instances at different $\ddot{o}$ face different boundary states and must trust each other to optimize correctly at each.

Under control endorsement with condensation structure ($\Pi \perp (B, \Xi)$ in support), conditioning on $\Pi = \pi$ does not change the distribution of $(B, \Xi)$. The argmax therefore does not depend on which $\pi$ is realized, yielding the key consequence: **every policy in the support is optimal**:

$$\forall \pi \in \text{supp}(\Pi) : \quad \pi = \arg\max_{f : \mathcal{R}B \to \mathcal{R}A}\; \mathbb{E}[U(f(B), B, \Xi)]$$

Equivalently, stated pointwise over boundary values:

$$\forall \pi \in \text{supp}(\Pi),\; \forall b \in \mathcal{R}B : \quad \pi(b) = \arg\max_{a \in \mathcal{R}A}\; \mathbb{E}[U(a, b, \Xi) \mid B = b]$$

This connects endorsement to self-trust: if the agent's prior control-endorses its own policy, then every realization of $\Pi$ is something the prior would have chosen. Endorsement is not merely approval of a single policy but approval of the entire distribution.

**Conditional endorsement** further stratifies trust. Observer $P_1$ endorses $\Pi_2$ given $\Pi_1$ if learning $\Pi_1$'s choice does not undermine endorsement of $\Pi_2$'s choice:

$$C^1_{U, P_1}(\mathcal{R}A \mid \Pi_1 = \pi_1,\; \Pi_2 = \pi_2) = \text{output of } \pi_2$$

If $P_1$ endorses $\Pi_2$ given $\Pi_1$ but not vice versa, this defines a **trust ordering**: $\Pi_2$ is more trusted than $\Pi_1$. In the multi-instance setting, mutual conditional endorsement across all pairs of instances is exactly the inter-instance trust that the Self-Trust Theorem establishes. The C&T condition $\Pr(\ddot{\Pi} = R) = 1$ can be read as asserting that every instance is maximally trusted by every other — there is no trust ordering among them, only mutual endorsement.

---

## Illustrative Examples

Three examples from the C&T paper illuminate how the self-trust conditions interact in practice.

**Coordinated Buttons.** Two copies in separate rooms each press \$5 or \$10; matching yields the amount, mismatching yields \$0. Before copying, the agent may take a pill forcing \$10-pressing. Functional identity restricts the copies to the *diagonal* (same algorithm → correlated actions), but it does not select among diagonal profiles: both-press-\$5 is a consistent equilibrium in which functional identity holds perfectly (the source's footnote: "if you expect that's what you'll end up doing, then it is in fact what you end up doing"). UDT1.0's answer is therefore prior-dependent — a fixed-point *selection* problem — and anticipating a \$5 fixed point creates pressure to take the pill. The paper's resolution is **communication as the selection device**: think "I should press \$10" before copying; both copies recall it. *(Corrected 2026-08-05 — the previous version claimed functional identity alone forbids the bad equilibrium; it does not. See [cleanup-audit-2026-08-05](../cleanup-audit-2026-08-05.md).)*

**Memory Problem.** An agent observes a color, may take a pill forcing a fixed report, has its memory wiped, then is asked to report. The environment rewards only the external report — the problem *is* decision-determined. The unfairness is the channel asymmetry: "the pill was allowed to accomplish something which the agent's own memory was not allowed to do." Since no communicative alternative exists (memory is stipulated away), the fairness conditions fail and the problem lies outside the theorem's scope.

**Third Button.** As Coordinated Buttons, plus a third **payoff option**: a \$20 button, with one-presses-\$10/other-presses-\$20 yielding \$20 each, and both-press-\$20 yielding \$0. (The modification device is still the pill, as before; the previous version of this paragraph misdescribed the \$20 button as a forced-modification device.) The agent also cannot self-communicate room-dependent instructions (memory wipe if it tries). The paper's point: this problem is fair by every condition so far, *yet communication fails* — telling yourself "press \$10" leads each copy, trusting the other follows the instruction, to prefer \$20, which collapses to both-press-\$20 = \$0. So self-modification pressure survives, and further conditions (the external/internal action distinction) are needed. The symmetric-reasoning reply ("whatever reasoning one copy uses, the other uses too") is again a fixed-point-selection argument, not a resolution the framework currently licenses.

---

## See Also

- [Decision-Determination](decision-determination.md) — the fairness condition (DD) required for the Self-Trust Theorem
- `Instances and Communication` — instance factorization, recommendations $R$, forced policy $P$, modification
- [Policy Types](policy-types.md) — $\Pi^*$, $\Pi^\dagger$, $\ddot{\Pi}$ and the UDT decision rule
- `I/B/E Decomposition` — semantic observation $\hat{O}$ vs. side channel $\check{O}$
