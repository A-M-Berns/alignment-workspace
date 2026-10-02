---
title: "Organizing a Research Agenda for Improving UDT Tiling"
uuid: 835551d3-4a0e-4dff-8dfb-0de80499bdb2
date: 2024-12-09
source: claude.ai
path: ai-safety/decision-theory/udt-tiling
messages: 6
keywords: ["udt", "updateless decision theory", "tiling", "ai safety", "logical induction", "decision theory", "self-modification", "coordination", "game theory", "research agenda"]
classification_confidence: high
sensitive: false
---

# Organizing a Research Agenda for Improving UDT Tiling

**Summary.** Technical research planning discussion on Updateless Decision Theory and AI safety. User outlines ambitious five-phase research program addressing temporal/causal constraints, logical uncertainty, value uncertainty, ontological foundations, and coordination. Claude organizes into clear phases with dependencies, then creates comprehensive artifact document formalizing the agenda with mathematical definitions and theorems. Covers LUV coherence, Bayesian Logical Induction, geometric updates, and multi-agent coordination approaches including Distributed Cooperative Oracles, Payor's Lemma, and Higher-Order Game Theory.

**Where to look:**
- 1: User outlines five-phase research agenda addressing UDT limitations
- 2: Claude organizes into structured phases with clear dependencies and interdependencies
- 3: User clarifies coordination challenges and three approaches (DCO, Payor's Lemma, Higher-Order GT)
- 4: Claude expands Phase 5 with detailed self-coordination and multi-agent sections
- 5: User requests integrated artifact document
- 6: Claude creates comprehensive research agenda artifact with formal definitions, theorems, and mathematical notation

---

## [1] Human — 2024-12-09T18:44:58.647237Z


I would like you to help me organize an agenda for taking this research further.

Here are the basic steps.

First, there are some basic things to fix or improve about the UDT tiling results so far. I haven't accounted for time and causality to my satisfaction. That is: an agent cannot meaningfully modify its policy about the past, or about other branches of possibility that are not causally downstream of the present. Only some forms of self-modification are even possible. I haven't properly accounted for that.

There are also other things that can be improved about these basic results, probably.

Second, combining UDT with logical uncertainty and getting a tiling result there. I need to formalize LUV coherence and show that BLI follows from it, and figure out what other important properties follow from it. Then I need to figure out any other important properties which don't follow, but which are needed for a tiling theorem to hold, and work on that.

Third, combining this with value uncertainty to justify something like open-minded updatelessness. Figure out better ways to formally approach what to be updateful about vs updateless about. Ways to separate value uncertainty from other forms of uncertainty. Study Geometric UDT. Study generalizations of Nash bargaining to cases where some players can't get any gains from trade. 

Fourth, ontology uncertainty and ontology change. Investigate what it means to treat things as real. Come up with a few definitions of realism relevant to the project. Analyze the role of what-is-taken-as-proposition in logically uncertain UDT. Define a notion of "derivatives" based on a market analogy; find the natural underlying algebra for logical uncertainty (in contrast to sigma-algebras for normal uncertainty). This gives an "inferential semantics" IE a notion of meaning in terms of how-we-reason. We need the notions of "how to treat things as real" to link this up with map-territory semantics. The resulting tiling theorem should establish tiling-style trust by virtue of an appropriate connection between the inferential semantics and map-territory semantics. IE the agent is reasoning about its future self, and it understands mechanistically how its future self reasons, and it understands the connection between that style of reasoning and orienting towards reality -- it understands how that style of reasoning improves accuracy in a map-territory sense. It therefore trusts its future self.

Fifth, cooperation and coordination.

## [2] Claude — 2024-12-09T18:44:58.647237Z


 Let me help organize a research agenda based on these directions. I'll break this down into clear phases with specific objectives and dependencies.

Phase 1: Foundational UDT Tiling Improvements

Primary Objective: Strengthen the basic UDT tiling results by properly accounting for temporal and causal constraints.

Key Components:
1. Develop a formal representation of causal structure that captures which policy modifications are possible at each decision point
2. Update the definition of effective policies (eff(π)) to respect causal constraints
3. Modify the fairness assumptions to account for these constraints
4. Strengthen the tiling theorems to show that agents won't attempt impossible modifications
5. Consider additional improvements to axioms and proofs, particularly around the "Faith in Argmax" assumption

Expected Outcome: A more realistic set of tiling theorems that properly respect causality and time.

Phase 2: Logical Uncertainty Integration

Primary Objective: Develop a rigorous framework for logically uncertain UDT with tiling properties.

Key Components:
1. Formalize LUV (Logical Uncertainty Value) coherence
2. Prove that Bayesian Logical Induction (BLI) follows from LUV coherence
3. Identify and prove additional important properties that follow from LUV coherence
4. Determine what additional properties are needed for tiling
5. Develop and prove tiling theorems in this context

Phase 3: Value Uncertainty Framework

Primary Objective: Create a formal framework for handling value uncertainty in UDT.

Key Components:
1. Develop formal criteria for what to be updateful versus updateless about
2. Create a rigorous separation between value uncertainty and other forms of uncertainty
3. Study and incorporate insights from Geometric UDT
4. Develop generalizations of Nash bargaining for asymmetric cases
5. Create formal criteria for "open-minded updatelessness"

Phase 4: Ontological Foundations

Primary Objective: Develop a comprehensive framework for handling ontology uncertainty and change.

Key Components:
1. Define multiple formal notions of realism relevant to the project
2. Analyze the role of propositions in logically uncertain UDT
3. Develop a market-based derivative framework for logical uncertainty
4. Identify the natural underlying algebraic structure for logical uncertainty
5. Create formal connections between inferential semantics and map-territory semantics
6. Prove tiling theorems based on these connections

Phase 5: Cooperation and Coordination

Primary Objective: Extend the framework to handle multi-agent scenarios and coordination.

This phase needs more specification, but likely includes:
1. Extending the ontological framework to multiple agents
2. Developing formal criteria for coordination
3. Proving tiling theorems in multi-agent contexts

Dependencies and Order:
- Phase 1 should be completed first as it provides the foundation
- Phases 2 and 3 can be pursued in parallel after Phase 1
- Phase 4 depends on both Phase 2 and 3 being substantially complete
- Phase 5 depends on Phase 4

Would you like me to elaborate on any of these phases or discuss specific technical challenges within them?

## [3] Human — 2024-12-09T19:06:57.386995Z


For cooperation & coordination, it is important to note that all the tiling theorems so far will face a tricky self-coordination issue. UDT 1.1 is able to self-coordinate well, but the tiling theorems associated with it are trivial and don't give us the insights we want. UDT 1.0 is more promising for nontrivial theorems, but self-coordination is a real problem for it, which creates tiling difficulties. To get theorems without directly addressing these problems, we have to assume away those difficulties. This makes the theorems inherently worse.

So, coordination has two parts: coordinating with oneself, and coordinating with others. However, these may be similar enough that we borrow a lot of techniques from one to the other. Self-coordination has especially critical relevance to getting good tiling results, but coordination with others may also have some relevance, since coordinating poorly could be grounds for wanting to self-modify.

There are three main routes to coordination with others which I want to explore: Distributed Cooperative Oracles, Payor's Lemma, and Higher-Order Game Theory.

## [4] Claude — 2024-12-09T19:06:57.386995Z


 Thank you for that important clarification about coordination. Let me revise and expand Phase 5 of the research agenda to properly address these coordination challenges.

Phase 5: Coordination and Trust

Primary Objective: Develop a comprehensive framework for both self-coordination and coordination with others, with the goal of strengthening tiling results.

Part A: Self-Coordination

This addresses the fundamental tension between getting meaningful tiling results and achieving good coordination properties:

1. Examine why UDT 1.1's strong coordination properties come at the cost of trivial tiling results
2. Identify what makes UDT 1.0's coordination problems create tiling difficulties
3. Develop new frameworks that can achieve both meaningful tiling and strong coordination
4. Create formal criteria for when coordination assumptions are justified versus when they constitute problematic shortcuts

Part B: Coordination with Others

This explores three primary approaches to coordination between agents:

Distributed Cooperative Oracles
- Formalize the notion of distributed cooperation through oracle-based coordination
- Study how this framework can provide guarantees about cooperative behavior
- Examine how this relates to self-modification incentives
- Investigate connections between distributed cooperation and tiling properties

Payor's Lemma Approach
- Develop formal criteria for when cooperation is rational based on Payor's Lemma principles
- Study how these criteria interact with self-modification incentives
- Examine connections between payment-based cooperation and tiling
- Investigate how this framework handles asymmetric cooperation scenarios

Higher-Order Game Theory
- Create formal models of recursive strategic reasoning
- Study how higher-order reasoning can enable stable cooperation
- Examine connections between game-theoretic equilibria and tiling properties
- Investigate how this approach handles uncertainty about other agents' decision procedures

Integration Challenges

The framework needs to address several key questions:
- How do self-coordination solutions extend to coordination with others?
- What properties need to hold across both domains for stable cooperation?
- How do coordination failures create incentives for self-modification?
- What assumptions about other agents are needed for tiling results to hold?

Dependencies and Relationships
- This phase depends on the ontological foundations from Phase 4
- The self-coordination work should be prioritized as it directly impacts tiling
- The three approaches to coordination with others can be explored in parallel
- Results from each approach should inform revisions to the others
- Insights about coordination may require revisiting earlier phases' assumptions

Would you like me to elaborate on any of these components or discuss specific technical challenges within them?

## [5] Human — 2024-12-09T19:08:55.503469Z


Please integrate all of the ideas so far into a thorough Artifact document. Integrate information from the background reading in context, and your own prior knowledge, to flesh out ideas as much as you can. Use latex to express formal mathematical ideas.

## [6] Claude — 2024-12-09T19:08:55.503469Z


 <antThinking>This requires creating a comprehensive research agenda document that integrates mathematical formalism with clear exposition. Given the technical and long-form nature of this content, an artifact is appropriate.</antThinking>

<antArtifact identifier="research-agenda" type="text/markdown" title="Research Agenda: Tiling and Trust in AI Systems">
# A Research Agenda for Tiling and Trust in AI Systems

## Introduction

This document outlines a research agenda for developing a comprehensive theoretical framework for trust in AI systems, building on existing work in Updateless Decision Theory (UDT) and extending it to handle more realistic scenarios. The core question we address is: under what conditions can an AI system trust its future self and other AI systems to maintain desirable properties over time?

## Background and Motivation

The concept of "tiling" refers to the preservation of desirable properties over time in AI systems. A set of properties "tiles" if an agent conforming to those properties is not motivated to change them. This is crucial for AI safety, as we need to ensure that AI systems maintain their safety properties rather than being motivated to remove or modify them.

Existing work has shown some basic tiling results for UDT, but these results have important limitations:

1. They fail to properly account for temporal and causal constraints
2. They don't adequately handle computational uncertainty
3. They make unrealistic assumptions about coordination
4. They don't address ontological uncertainty
5. They don't fully address multi-agent scenarios

This agenda aims to systematically address these limitations.

## Phase 1: Foundational UDT Tiling Results

### 1.1 Temporal and Causal Structure

We first need to properly formalize the causal constraints on self-modification. Let's define:

\begin{definition}
For states $\omega_1, \omega_2 \in \Omega$, we write $\omega_1 \prec \omega_2$ if $\omega_1$ causally precedes $\omega_2$.
\end{definition}

\begin{definition}
A policy modification $m: \Pi \to \Pi$ is causally valid at state $\omega$ if:
1. For all $\omega' \prec \omega$, $m(\pi)(\omega') = \pi(\omega')$
2. For all $\omega'$ not causally downstream of $\omega$, $m(\pi)(\omega') = \pi(\omega')$
\end{definition}

We can then update the definition of effective policies:

\begin{definition}
For any policy $\pi$, define $\text{eff}_\omega(\pi)$ as the effective policy when evaluated from state $\omega$:

$\text{eff}_\omega(\pi)(\omega') = \begin{cases}
\hat{a} & \text{if } \pi(\omega') = a \in A_s \text{ and } \omega' \text{ is causally accessible from } \omega \\
\pi(\omega') & \text{otherwise}
\end{cases}$

where $\hat{a}$ represents the non-self-modifying version of action $a$.
\end{definition}

### 1.2 Modified Fairness Assumptions

The fairness assumptions need to be updated to respect causal structure:

\begin{assumption}[Causal Policy Fairness]
For any policies $\pi_1$ and $\pi_2$ and state $\omega$, if $\text{eff}_\omega(\pi_1) = \text{eff}_\omega(\pi_2)$, then:

$E_p(u|\pi^*=[\pi_1], \text{state}=\omega) = E_p(u|\pi^*=[\pi_2], \text{state}=\omega)$
\end{assumption}

### 1.3 Strengthened Tiling Theorems

Using these definitions, we can prove stronger tiling theorems. For UDT 1.0:

\begin{theorem}
Under Causal Policy Fairness and appropriate coordination assumptions, UDT 1.0 does not strictly prefer any causally valid self-modifying action.
\end{theorem}

The proof follows similar lines to previous tiling theorems but explicitly handles causal constraints.

## Phase 2: Logical Uncertainty Integration

### 2.1 LUV Coherence

We need to formalize how agents reason about their own computations. Building on the Logical Induction framework:

\begin{definition}[LUV Coherence]
A sequence of probability distributions $P_n$ is LUV-coherent if:
1. It satisfies the Logical Induction criterion
2. For any random variables X and Y:
   $|E_{P_n}[X + Y] - (E_{P_n}[X] + E_{P_n}[Y])| \to 0$ as $n \to \infty$
3. For any sentence $\phi(x)$ and term t:
   $|P_n(\forall x.\phi(x)) - P_n(\phi(t))| \to 0$ as $n \to \infty$
\end{definition}

### 2.2 Bayesian Logical Induction

We can then show that LUV coherence implies the key properties of Bayesian Logical Induction:

\begin{theorem}
Any LUV-coherent sequence satisfies the BLI properties:
1. $P_n(\phi) = Q_n(\phi)$ for simple $\phi$
2. $P_n(\phi|Q_m = q) = q(\phi)$ for $n < m$
3. Proper handling of nested beliefs
\end{theorem}

### 2.3 Additional Properties

For tiling results in this context, we need additional properties:

\begin{definition}[Computational Trust]
An agent exhibits computational trust if, for any computation C:
$E[u|\text{Compute}(C) = x] \geq E[u|\text{Hardcode}(x)]$

where $\text{Compute}(C)$ represents running computation C and $\text{Hardcode}(x)$ represents directly using value x.
\end{definition}

## Phase 3: Value Uncertainty

### 3.1 Update Criteria

We need formal criteria for what to be updateful about. One approach:

\begin{definition}[Value-Relevance]
Information I is value-relevant if:
$\exists \pi_1, \pi_2. E[u|\pi, I] > E[u|\pi, \neg I]$ and
$\forall \pi. E[u|\pi, I] \neq E[u|\pi]$
\end{definition}

### 3.2 Geometric UDT

Geometric UDT provides insights for handling value uncertainty:

\begin{definition}[Geometric Update]
Given prior P and observation x, the geometric update is:
$P'(\phi) = \arg\min_{Q} D(Q||P)$ subject to $Q(x) = 1$

where D is an appropriate divergence measure.
\end{definition}

## Phase 4: Ontological Foundations

### 4.1 Realism Criteria

We need multiple formal notions of realism:

\begin{definition}[Pragmatic Realism]
A reasoning system exhibits pragmatic realism about X if:
1. It treats X as causally upstream of observations
2. It updates beliefs about X based on evidence
3. It coordinates with others regarding X
\end{definition}

### 4.2 Market-Based Framework

For logical uncertainty:

\begin{definition}[Logical Derivative]
The logical derivative of proposition P with respect to axiom A is:
$\frac{\partial P}{\partial A} = \lim_{\epsilon \to 0} \frac{P(A + \epsilon) - P(A)}{\epsilon}$

where addition represents strengthening/weakening of the axiom.
\end{definition}

## Phase 5: Coordination

### 5.1 Self-Coordination

The core challenge is achieving both meaningful tiling and good coordination. One approach:

\begin{definition}[Stable Self-Trust]
A decision procedure exhibits stable self-trust if:
1. It achieves coordination across time without requiring global optimization
2. It maintains tiling properties
3. It handles computational uncertainty appropriately
\end{definition}

### 5.2 Multi-Agent Coordination

Three main approaches:

#### Distributed Cooperative Oracles
\begin{definition}
A distributed cooperative oracle is a function $f: \mathcal{A}^n \to \{0,1\}$ such that:
1. $f(a_1,...,a_n) = 1$ iff the actions constitute a cooperative equilibrium
2. Each agent can compute $f$ with high probability
3. The computation of $f$ is distributed across agents
\end{definition}

#### Payor's Lemma
\begin{theorem}[Informal Payor's Lemma]
If agent A can pay agent B to take action X, and the benefit to A exceeds the cost to B, then cooperation emerges naturally through trade.
\end{theorem}

#### Higher-Order Game Theory
\begin{definition}[Higher-Order Strategy]
A higher-order strategy is a function $s: \mathcal{T} \to \mathcal{A}$ where $\mathcal{T}$ is the space of opponent types, including their reasoning about your type.
\end{definition}

## Next Steps

1. Develop rigorous proofs for the foundational UDT tiling results with proper causal structure
2. Formalize LUV coherence and prove its key properties
3. Create concrete criteria for update policies under value uncertainty
4. Develop the market-based framework for logical uncertainty
5. Prove initial results about multi-agent coordination

## Open Questions

1. How can we weaken the coordination assumptions while maintaining tiling?
2. What is the right algebraic structure for logical uncertainty?
3. How do we handle nested beliefs efficiently?
4. What are the minimal conditions needed for stable multi-agent cooperation?
5. How do we handle ontological shifts in a principled way?

## Conclusion

This research agenda outlines a path toward a comprehensive theoretical framework for trust in AI systems. Success in this endeavor would provide crucial foundations for ensuring that AI systems remain aligned with human values over time and across multiple agents. While significant challenges remain, the structured approach outlined here provides concrete steps toward addressing these fundamental problems in AI safety.

## References

[Full bibliography would be added here, incorporating the references from provided materials plus additional relevant papers]
</antArtifact>

Would you like me to expand on any particular section or add additional technical details to specific parts of the agenda?
