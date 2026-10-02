# Meaning & Agency
**Author:** abramdemski  
**Date:** 19th Dec 2023  
**Source:** LessWrong / AI Alignment Forum

## Overview

The goal of this post is to clarify a few concepts relating to AI Alignment under a common framework. The main concepts to be clarified:

- **Optimization.** Specifically, this will be a type of Vingean agency. It will split into Selection vs Control variants.
- **Reference** (the relationship which holds between map and territory; aka semantics, aka meaning). Specifically, this will be a teleosemantic theory.

The main new concepts employed will be **endorsement** and **legitimacy**.

### TLDR:

- **Endorsement** of a process is when you would take its conclusions for your own, if you knew them.
- **Legitimacy** relates to endorsement in the same way that good relates to utility. (IE utility/endorsement are generic mathematical theories of agency; good/legitimate refer to the specific thing we care about.)
- We perceive **agency** when something is better at doing something than us; we endorse some aspect of its reasoning or activity. (Endorse as a way of achieving its goals, if not necessarily our own.)
- We perceive **meaning** (semantics/reference) in cases where something has been optimized for accuracy -- that is, the goal we endorse a conclusion with respect to is some notion of accuracy of representation.

---

## Broader Context

The basic idea is to investigate agency as a natural phenomenon, and have some deep insights emerge from that, relevant to the analysis of AI Risk. Representation theorems -- also sometimes called coherence theorems or selection theorems depending on what you want to emphasize -- start from a very normative place, typically assuming preferences as a basic starting object. Perhaps these preferences are given a veneer of behaviorist justification: they supposedly represent what the agent would choose if given the option. But actually giving agents the implied options would typically be very unnatural, taking the agent out of its environment.

There are many ways to drive toward more naturalistic representation theorems. The work presented here takes a particular approach: **cognitive reduction**. I want to model what it means for one agent to think of something as being another agent. Daniel Dennett called this the **intentional stance**.

The goal of the present essay is to sketch a formal picture of the intentional stance. This is not yet a representation theorem -- it does not establish a type signature for agency based on the ideas. However, for me at least, it seems like an important piece of deconfusion. It paints a picture of agents who understand each other, as thinking things. I hope that it can contribute to a useful representation theorem and a broader picture of agency.

---

## Meaning

In *Signalling & Simulacra*, I argued that the signal-theoretic analysis of meaning (which is the most common Bayesian analysis of communication) fails to adequately define lying, and fails to offer any distinction between denotation and connotation or literal content vs conversational implicature.

### Teleosemantics

In *Teleosemantics!*, I argue that the denotative meaning is what a symbol is **optimized to correspond to**.

The signal-theoretic analysis of meaning gives us the information-theoretic content of a communicative act; but any observation carries information in this sense. What distinguishes symbolic communication from other information-carrying signals is that some care has been taken to convey specific information. Sometimes the probabilistic information is all we care about; but tracking literal meaning is also an important part of language.

Commonly confused words, such as imply vs infer, probabilistically carry some of each other's signal-theoretic meaning (based on the probability we assign to the speaker having confused the two words). But the community of speakers overall puts optimization pressure on avoiding this confusion.

Similarly, lying happens, so the signal-theoretic meaning of an utterance includes some probability of it being a lie (and the probabilistic implications thereof). But the linguistic community optimizes against lying, so there's a sense in which the lie is not part of the intended meaning of the utterance.

If a liar claims (falsely) "I am very wealthy", there's a commonsense way in which they mean that they're very wealthy. That's the meaning they're trying to convey. I want to be clear that **this does not fit with the technical theory of meaning which I am advocating here.**

### Plurality of Teleosemantic Meaning

Meaning, on my account, comes from optimizing symbols to have a specific correspondence to reality; that is, to be accurate under a specific intended reading. This is entirely different from optimizing words to create a specific belief in their audience, which is what the liar is doing. On my account, optimizing for impact on an audience rather than accuracy fails to impart those words with (teleosemantic) meaning.

Since the liar's use of words does not impart them with meaning in itself, the only relevant optimization process which gives meaning to the words is the broader linguistic community.

However, there are cases where multiple optimization processes may be trying to give meaning to the same words, perhaps at cross-purposes. So in general, the theory here requires **meaning to be indexed by an agent** (or optimization process); we can differentiate what an individual person means by their words from what larger linguistic communities mean by those words.

Now, obviously, in order to understand the teleosemantic definition of meaning, we need to understand what "agent" or "optimization process" or "optimized" means.

---

## Agency

In *Belief in Intelligence*, Eliezer sketches the peculiar mental state which regards something else as intelligent:

> Imagine that I'm visiting a distant city, and a local friend volunteers to drive me to the airport. I don't know the neighborhood. Each time my friend approaches a street intersection, I don't know whether my friend will turn left, turn right, or continue straight ahead. I can't predict my friend's move even as we approach each individual intersection - let alone, predict the whole sequence of moves in advance.
>
> Yet I can predict the result of my friend's unpredictable actions: we will arrive at the airport.
> [...]
> I can predict the outcome of a process, without being able to predict any of the intermediate steps of the process.

In *Measuring Optimization Power*, he formalizes this idea by taking a preference ordering and a baseline probability distribution over the possible outcomes. The optimization power of the friend is measured by how well they do relative to this baseline.

I think this can be a useful notion of agency, but constructing this baseline model does strike me as rather artificial. We're not just sampling from Eliezer's world-model. If we sampled from Eliezer's world-model, the friend would turn randomly at each intersection, but they'd also arrive at the airport in a timely manner no matter which route they took -- because Eliezer's actual world-model believes the friend is capably pursuing that goal.

So to construct the baseline model, it is necessary to **forget the existence of the agency we're trying to measure** while holding other aspects of our world-model steady. While it may be clear how to do this in many cases, it isn't clear in general. I suspect if we tried to write down the algorithm for doing it, it would involve an "agency detector" at some point; you have to be able to draw a circle around the agent in order to selectively forget it.

I will propose a variation of Eliezer's definition which does not have this problem.

---

## Endorsement

I will say that one set of beliefs P₁ **endorses** another P₂ (with respect to topic X) in the case that, if we condition P₁ on P₂'s belief about a thing, then P₁ adopts that belief as its own:

**Belief Endorsement:** Probability distribution P₁ belief-endorses P₂ in the case that P₁(X | "P₂(X) = p") = p.

This is already enough to get my proposed formal definition of meaning off the ground. When the above condition holds, P₁ sees "P₂(X)" as a belief about X. The notation somewhat obscures the dependence on a particular translation between P₁'s ontology and P₂'s ontology. The quotation marks are communicating a translation into P₁'s event algebra.

For example, Alice and Bob both start out regarding a coinflip as 50-50. Bob gets to see the coin after the flip, and updates to near-certainty about which way the coin landed. Because of the way Alice knows Bob's beliefs about the coin have been correlated with the coin itself, and because Alice's beliefs have not been so correlated, Alice now endorses Bob's belief about "the coin landed heads" as meaning the coin landed heads, and Bob's "the coin landed tails" as meaning the coin landed tails. This is not because Alice thinks Bob's beliefs are perfectly accurate; only more accurate than Alice's.

However, to see why this is a teleosemantic notion of meaning, I need to generalize "endorsement" more, in order to properly relate it to optimization.

### Expectation Endorsement

**Expectation Endorsement:** E_{ω∼P₁}(V(ω) | "E_{ω∼P₂}(V(ω)) = x") = x

This notion of endorsement generalizes the previous, because we can take V to be the indicator variable for X.

### Selection Endorsement

For non-convex optimization, we need to endorse *choices* rather than expectations. I introduce C to represent an agent's choices. Given a set of possible 'actions' A, the choice function C^1_{U₁,P₁}(A) gives agent 1's choice a ∈ A under beliefs P₁ and objective function U₁.

**Selection Endorsement:** Agent 1, having beliefs P₁ and a choice function C₁, selection-endorses Agent 2 as optimizing U₂ via the choice C₂ if and only if C^1_{U₂,P₁}(A | "C^2_{U₂,P₂}(A) = a") = a.

So, Alice thinks of Bob as optimizing for U₂ if Alice would copy Bob's answer (if she were optimizing for U₂).

Selection endorsement somewhat resembles *The ground of optimization* if we take the random variable V to be a system's state at a single time-slice. I selection-endorse the whole system (as optimizing some U₂) if, ignorant of what scores highly in U₂ myself, I would take the system's state as a plausible answer.

Since U₂(a) is a mathematically pure function U₂: A → ℝ, this is **selection** in a Selection vs Control sense. If we think of the variable V as some little piece of the world, it is being optimized to maximize some property of itself, not some property of the broader world.

### Control Endorsement

If U() is an impure function, its values depend on the wider world: U: Ω × A → ℝ. Now, the optimization has to be explicitly defined with a dependence on worlds ω ∈ Ω.

**Control Endorsement:** C^1_{U₂,P₁}(A | "C^2_{U₂,P₂}(A) = a") = a, where U₂ is now a two-argument function, taking worlds and actions, rather than a one-argument function.

**Control endorsement is the notion of intentional stance that I have been driving towards.** The formula tracks someone tracking agency. If Alice control-endorses Bob (as optimizing U₂), Alice sees Bob as an agent.

This resembles ideas in *Vingean Agency* and *Optimization at a Distance*. Like Eliezer's *Measuring Optimization Power*, agency is defined relative to a baseline distribution (P₁); but the sort of baseline distribution we need is much less artificial than what Eliezer's definition needed. It can just be our honest beliefs.

Control endorsement generalizes selection endorsement (since U can ignore its first argument), expectation endorsement (since U can be some loss function), and belief endorsement (when that loss function is a proper scoring rule).

### "Absolute" Endorsement

**"Absolute" Endorsement:** control endorsement where U₂ is the utility function of the observer whose beliefs are P₁.

Speculatively, this might have some useful connection to corrigibility. If Alice were to absolutely endorse Bob's actions, then Alice should be fine with Bob modifying Alice's source code.

---

## Conditional Endorsement

Consider an example with Alice, Bob, and Carol. Alice endorses both Bob and Carol, but she continues to endorse Carol even after learning Bob's decision; the reverse is not the case. Obviously, she trusts Carol more than Bob.

**Conditional (Control) Endorsement:** P₁ endorses W given V iff argmax_{v∈A} E_{ω∼P₁|X∧Y} U(ω,v) = y, where X is the event V = x, and Y is the event W = y.

Thus, holding the utility function fixed but changing the random variable considered, we can (partially) order different random variables by how endorsed they are.

---

## Legitimacy

**Legitimacy** is to endorsement as goodness is to utility: "utility" is an abstract notion of an agent's preferences, whereas "good" is the thing we actually care about. Similarly, "endorsement" is an abstract notion intended to apply to agency in general, while "legitimacy" is the thing we care about as humans.

So, a mode of reasoning is legitimate if it has a reliable tendency toward the truth. Correct mathematical proofs are legitimate. The scientific method, when carried out well, is legitimate.

Wireheading is not legitimate. Taking a murder pill is not legitimate. Some drugs impact your reasoning in legitimate ways, while others are illegitimate.

I think there may be a technical sense (yet to be articulated) in which we'd prefer to align AI to legitimacy, but we can only align it to specific forms of endorsement and hope that's close enough. An AI aligned to endorsement can (more or less...) only do things that humans would consent to. But humans are sometimes grateful in retrospect about things which seemed terrible at the time.

However, anyone who purposefully built a superintelligent AGI aligned to some notion of legitimacy designed to trample on endorsement in select cases would be unilaterally imposing their own guess at legitimate values. I claim this is bad behavior.

---

## Updatelessness

I think it is clear that endorsement gives a picture where, when Alice considers whether Bob is an agent, Bob being updateless will boost his agency and any updateful behavior from Bob will be to the detriment of Bob's agency. After all, Alice is judging from the perspective of P₁. Any optimization will be judged by how well it optimizes the expectations of P₁.

This suggests that Alice should probably be updateless as well; that is, P₁ should be Alice's prior, not Alice's posterior.

---

## The Van Fraassen Reflection Principle

The Reflection Principle says that if P₁ is an agent's beliefs at one time, and P₂ is an agent's beliefs at a future time, then P₁ should belief-endorse P₂.

"Endorsement" differs from "reflection" in that: the Reflection Principle is about insisting that X should endorse Y in specific cases, whereas I am more focusing on studying the relation in general. Indeed, there are cases where it is not rational to endorse our future beliefs, such as when we plan to be inebriated at a specific time.

---

## Questions & Conjectures

1. How well can we use conditional endorsement to characterize optimization power (or more generally, level of endorsement)? Is it transitive?
2. What further generalizations or alternative definitions of endorsement might be important?
3. How do we build a useful representation theorem out of this idea?
4. Can we prove something within this framework along the lines of capable agents have beliefs?
5. How can we integrate value change into this picture?
6. There's a big difference between endorsing some beliefs as a posterior (which is accuracy-centric) and endorsing them as a prior for use in updateless decisionmaking. How should this be characterized?
7. It seems sensible to call selection "myopic" and control "nonmyopic". However, although epistemic accuracy falls on the control side, it doesn't feel very control-oriented, and it feels to me like there's a strong sense in which it is myopic. Can this be characterized?
8. Looking at things through an algorithmic information theory lens, it makes sense to say that endorsement, as an interpretation of something as an optimization process, is a "better" interpretation when the utility function used to interpret something as an agent is simpler.
9. I have an intuition that insights for eliciting latent knowledge can be uncovered by examining what happens when we translate back and forth between interpreting something as a selection process vs a control process.
10. Can something interesting be said about inner alignment via this framework?
11. What does it look like to build a system with endorsement as the target?
12. I imagine there is something to be gained by thinking about different ways of varying all the parameters of endorsement, the way conditional endorsement varies the baseline probability distribution.

---

## Notes

[1] I'm saying "signal-theoretic" rather than "signalling-theoretic" here because it sounds better to me; but the field is called "signalling theory" not "signal theory".

[2] I don't recall the appropriate reference now, but I think at one point Eliezer defines lying as communicating with the intent to mislead, IE the intent to make your audience's beliefs less accurate. While I think this is a pretty good pragmatic definition, it fails to differentiate lying from filtering evidence or other clever ways to mislead.

[3] For our purposes here, it is fine to imagine that "beliefs" are probability distributions as normally defined. But I also have in mind more computationally bounded notions, which may be only approximately probabilistically coherent; and we can also consider other variations, such as infradistributions.

[4] Credit for the term "endorsement" goes to Scott Garrabrant.

[5] We can slide between selection and control if we are happy to vary how V and U are defined. Since random variables are a function of the whole event-space anyway, we can pack as much information about the world into V as we like, so long as we are happy to make U just not care about those extra bits of information. However, seeing an agent as a selector rather than a controller means that U() has to encode the beliefs of the agent, to calculate the expected values. So beliefs are being represented as part of the preferences. When seeing an agent as a controller, the beliefs are instead seen as a part of the mechanism for optimizing the preferences. I expect this means it is often simpler to view something as a controller, if it is good at controlling; the selection view is overcomplicated by the belief information.

[6] It feels a bit weird that the utility function takes the world and the action, here. We have to think of this as being in world ω, but then counterfacting on action V = x. I could see this aspect of the theory being fiddled with.

[7] If Alice is interpreting Bob as an agent, Alice is the "radical interpreter". This terminology comes from philosophy; the "radical interpreter" is like an alien looking at human brains and trying to interpret the meaning of human beliefs.


---
# === FILE: communication-trust-translated.md ===
---


\documentclass{article}

% Language setting
% Replace `english' with e.g. `spanish' to change the document language
\usepackage[english]{babel}

% Set page size and margins
% Replace `letterpaper' with `a4paper' for UK/EU standard size
\usepackage[letterpaper,top=2cm,bottom=2cm,left=3cm,right=3cm,marginparwidth=1.75cm]{geometry}

% Useful packages
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{graphicx}
\usepackage[colorlinks=true, allcolors=blue]{hyperref}
\usepackage{mathtools}
\usepackage{thmtools}
\usepackage{enumitem}
\usepackage{xcolor}
\usepackage{amsthm}
\usepackage{csquotes}

% Theorem environments

\theoremstyle{plain}
\newtheorem{assumption}{Assumption}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}

\theoremstyle{definition}
\newtheorem{definition}{Definition}
\newtheorem{example}{Example}

\theoremstyle{remark}
\newtheorem{remark}{Remark}

% Useful commands
\DeclareMathOperator*{\argmax}{arg\,max}
\DeclareMathOperator*{\argmin}{arg\,min}
\DeclareMathOperator{\dom}{dom}
\DeclareMathOperator{\range}{\mathcal{R}}
\newcommand{\E}{\mathbb{E}}
\newcommand{\Prob}{\mathbb{P}}
\newcommand{\is}{{i \in \mathcal{I}}}
\newcommand{\ddo}{{\ddot o}}

\title{Communication \& Trust}
\author{the author}

\begin{document}
\maketitle

\begin{abstract}
Yudkowsky suggested the criterion of \emph{reflective consistency} for decision theories (roughly: does a decision theory choose itself?) \cite{yudkowsky2010timeless}. Dai proposed Updateless Decision Theory (UDT) as a response to Yudkowsky's ideas \cite{dai2009udt}. \cite{demski2025trust} offered the first published proofs of reflective consistency for UDT. However, those results were not entirely satisfying, due to their reliance on strong assumptions. The current work offers a new attempt, inspired by Critch's notion of agent boundaries \cite{Critch2022BoundariesSequence} as well as Garrabrant's work on Cartesian Frames \cite{garrabrant2021cartesian} and Finite Factored Sets \cite{garrabrant2021temporal}. The approach here uses \emph{communication between agent-moments} as a ``release valve'' for pressures which could otherwise lead to self-modification.
\end{abstract}

\section{Introduction}

Self-trust is an important safety property for agentic AI. Without such trust, AI systems have an incentive to modify themselves or create successor agents, which could undermine other safety properties. A better understanding of trust could also contribute to safety in other ways; see \cite{demski2025trust} for further details.

The current paper, like \cite{demski2025trust}, analyzes conditions under which multiple instances of an agent (across space and/or time) can justifiably trust each other. Trust is operationalized as non-interference: given the opportunity to modify how an instance makes decisions, a preference to do so indicates a lack of trust.

Unlike \cite{demski2025trust}, the current paper focuses on \emph{communication} as a means of creating trust. Without communication, coordination problems can create a lack of trust even between agents with shared goals and beliefs. This resulted in overly strong coordination assumptions for previous results. The current work makes coordination assumptions \emph{only with respect to communication itself}, assuming enough for the agent-instances to have a shared communication protocol. This is used to overcome any other coordination problems which could otherwise break trust.\footnote{This strategy owes a significant debt to discussions with Scott Garrabrant, although the strategy he was advocating in those discussions differs considerably from my strategy here.}

Section 2 will provide further historical context for the ideas to be presented here, by contrasting the notion of ``trust'' used here with the common notion of \emph{dynamic consistency}. Section 3 will provide further motivation for the current approach by way of example decision problems.

Section 4 will begin the formal development of these ideas by introducing important notation and mathematical terminology. This includes a notion of factorization inspired by (but distinct from) Garrabrant's work on Finite Factored Sets \cite{garrabrant2021temporal}.
Section 5 will apply these mathematical tools to model agents, inspired by (but distinct from) Garrabrant's Cartesian Frames \cite{garrabrant2021cartesian} and Critch's work on agent boundaries \cite{Critch2022BoundariesSequence}.
Section 6 elaborates this model to deal with multiple instances of an agent and communication between those instances.
Section 7 proves the main result on the avoidance of self-modification.
Section 8 deals with the question of whether agent-instances will follow advice that is communicated to them by other instances.
Section 9 concludes with a discussion of the significance of the results and future work.

Throughout the paper, I will use ``I/my'' to take personal responsibility for decisions/thoughts/etc (EG ``I will call this variable $X$ ...''), and ``we/our'' to invite the reader along (EG ``With this technique, we can ...'').

% DYNAMIC VS REFLECTIVE CONSISTENCY
% current work formalizes trust as non-interference
% this closely resembles dynamic consistency (cite literature)
% dynamic consistency is about whether an agent would agree with its future actions _if it knew them precisely_
% yudkowsy introduced _reflective consistency_ and contrasted it with dynamic consistency (cite tdt paper) but didn't define it precisely
% later work by yudkowsy formalized the _vingean principle_, which distinguishes the type of self-trust yudkowsy wants: agents should trust other instances of themselves _even if they can't precisely anticipate each other's actions_
% this better reflects realistic trust, since realistic agents cannot have everything planned out from the beginning; however, it deprives us of the tool of equilibrium analysis, while asking the same fundamental question of game theory which equilibrium analysis was created to solve (ie, how do we model agents reasoning about each other reasoning about each other reasoning about...)

\section{Trust vs. Dynamic Consistency}

Suppose that an agent has, by virtue of its constitution (biological or synthetic), a specific decision rule. So long as the agent is functioning normally, this decision rule determines how all instances of the agent make decisions. However, the environment might provide some instances of the agent with opportunities to interfere with other instances (or with themselves)\footnote{It may be sensible to assume an instance cannot modify itself, as this would seem to require time-travel. It might further be sensible to assume a temporal partial order, so that later instances can only be influenced by strictly earlier instances. However, the present work avoids such assumptions. This is done to minimize unecessary assumptions, as well as to respect the spirit of Updateless Decision Theory, which is not supposed to rely on any notion of time or causality.}, creating a circumstance where an instance is \emph{not} operating normally, and can make decisions which do not conform to the decision rule. Some agents may prefer to interfere with themselves in such a way. The current work formalizes trust as the absence of such a preference.\footnote{I do not intend to assume that an agent can perfectly identify instances of itself within the environment. What is important is that the agent reasons in such a way as to imagine that there may be instances, and may plan (using its uncertain understanding of the world) to interfere with those instances.}

This closely resembles the concept of \emph{dynamic consistency} which is familiar to both economists and decision theorists \cite{strotz1955myopia, pollak1968consistent, machina1989dynamic, frederick2002time}.\footnote{Dynamic consistency is sometimes alternatively called time consistency or intertemporal consistency.} An agent is dynamically consistent if, \emph{told of its future actions}, it would endorse them.\footnote{More precisely, dynamic consistency is often defined as consistency between the plans an agent would make ahead of time with the decisions which it would make in the moment. However, this amounts to the same thing.} A dynamic inconsistency of this sort implies that an agent would choose to interfere with its future decisions if (a) it had the opportunity to do so, and (b) it could foresee those future decisions precisely.

Yudkowsky contrasts dynamic consistency with \emph{reflective consistency}:\footnote{Pettigrew et al \cite{PettigrewForthcoming-PETOCH} examine a very similar concept which they term \emph{self-recommending} (calling its negation \emph{self-undermining}).}

\begin{displayquote}[\cite{yudkowsky2010timeless}]
I wish to generalize the notion of \emph{dynamic consistency} to the notion of \emph{reflective consistency}. A decision algorithm is \emph{reflectively inconsistent} whenever an agent using that algorithm wishes she possessed a different decision algorithm. Imagine that a decision agent possesses the ability to choose among decision algorithms—perhaps she is a self-modifying Artificial Intelligence with the ability to rewrite her source code, or more mundanely a human pondering different philosophies of decision.
\end{displayquote}

Yudkowsky doesn't offer a precise definition of reflective consistency in that work.\footnote{``I have never seen a formal framework for computing the relative expected utility of different abstract decision algorithms, and until someone invents such, arguments about reflective inconsistency will remain less formal than analyses of dynamic inconsistency.'' \cite{yudkowsky2010timeless}} However, his later work on the concept of \emph{tiling agents} articulates the \emph{Vingean principle}:

\begin{displayquote}[\cite{yudkowsky2013tiling}]
    An agent building a successor (equivalently: a self-modifying agent creating the next generation of its code) should not need to know the successor's exact actions and thoughts in advance.
\end{displayquote}

In the current work, I interpret the Vingean principle as follows: we are not allowed to assume an agent can perfectly predict the strategy of all of its instances. This bars predicting the precise actions of instances (and also bars precise calculation of mixed-strategy equilibria).\footnote{I do not intend this as the only or ultimate interpretation of the Vingean principle. In \cite{yudkowsky2013tiling}, the authors state ``For our purposes we cash out the Vingean principle as follows: \emph{In the parent's reasoning, the offspring's actions should only appear inside quantifiers}.''}

In my experience, those influenced by Yudkowsy's ideas use `tiling' and `reflective consistency' interchangeably. Both terms are, in my opinion, best understood as what the current work calls `self-trust': a variant of dynamic consistency where one does not assume that the agent can foresee the decisions of all its instances. Instead, an agent must reason about itself abstractly, establishing trust in its other instances to do the right thing based on shared goals and properties of the shared decision procedure. This better reflects the problems of self-trust in the real world, since realistic agents cannot precisely plan everything out ahead of time.\footnote{A possible distinction between the current work's notion of `trust' and reflective consistency, on the one hand, and dynamic consistency and tiling on the other hand: the second pair are described in relation to time, whereas the first two deal with `instances' which may be across time or otherwise; however, I see this as a less important distinction.}

Dynamic consistency is sometimes treated as a fundamental rationality constraint; for example, Dutch Book \cite{sep-dutch-book} and Money Pump arguments \cite{gustafsson2022money} can be interpreted as dynamic inconsistency arguments (illustrating a sequence of decisions which an agent would endorse individually, but would not endorse as a plan chosen all at once). I read Yudkowsky as intending to suggest that reflective consistency is equally or more fundamental (and I am inclined to agree). However, Yudkowsky cautions:

\begin{displayquote}[\cite{yudkowsky2013tiling}]
    Therefore I cannot say: If there exists \emph{any} dilemma that would render an agent reflectively inconsistent, that agent is irrational. The criterion is definitely too broad. Perhaps a superintelligence says: "Change your algorithm to alphabetization or I'll wipe out your entire species." [...] To make \emph{reflective inconsistency} an interesting criterion of irrationality, we have to \emph{restrict} the range of dilemmas considered fair. I will say that I consider a dilemma "fair," if when an agent underperforms other agents on the dilemma, I consider this to speak poorly of that agent's rationality.
\end{displayquote}

Yudkowsky goes on to discuss how different notions of fairness will lead one to endorse different decision theories. Yudkowsky endorses a specific notion of fairness, which he calls \emph{decision-determination}.

\begin{displayquote}[\cite{yudkowsky2010timeless}]
    An expected utility maximizer can succeed even on problems designed for the convenience of alphabetizers, if the expected utility maximizer knows enough to calculate that the alphabetically first
decision has maximum expected utility, \emph{and if the problem structure is such that all agents who make the same decision receive the same payoff regardless of which algorithm produced the decision}. This last requirement is the critical one; I will call it \emph{decision-determination}.
\end{displayquote}

The main contributions of the current work are to offer a particular formalization of Yudkowsky's notion of fairness, and prove a result analyzing the reflective consistency (self-trust) of Wei Dai's Updateless Decision Theory.

% reflective consistency vs dynamic consistency
% propose new definition of reflective consistency
% UDT was created for reflective consistency, but no proof
% previous paper offered proofs which were dissatisfying, state reasons
% new formalism and proof
% generalizaiton to multi-agent trust
% can't quite use game-theoretic frame, due to vingean assumption

% MOTIVATING EXAMPLES
% introduce UDT 1.0
% coordination problems: red-room green-room
% UDT 1.1 (is nonvingean)
% coordination problems create trust problems
% communication as a strategy for creating trust
% 5-10-20 version of red/green rooms
% need for an assumption which rules out this counterexample

\section{Motivating Examples}

In response to some of Yudkowsky's ideas about decision theory, Wei Dai proposed Updateless Decision Theory (UDT) \cite{dai2009udt}. Its decision rule is as follows: $$\pi(o) = \argmax_{a \in A} \E(U|\pi(o)=a)$$

Here, $\pi$ is the agent's policy; that is, a function taking observations $o \in O$ and outputting actions $a \in A$. $U$ is the agent's global utility function, and $\E$ takes the expectation in terms of the agent's prior. (This notation will be revised and elaborated later.) This decision procedure achieved self-trust in many examples of interest where other decision procedures failed.

Dai later noticed examples where the above decision rule fails to achieve self-trust \cite{dai2010udt}. These examples are \emph{coordination problems}, where multiple agent-instances must take coordinated action to achieve a desired outcome. For example:

\begin{example}[Coordinated Buttons problem]\footnote{This example is a slight variation on one considered by Wei Dai.}
    You are about to be copied. You will be put in a red room, while your copy will be put in a green room. In both rooms, there are two buttons: one labeled \$5, and another labeled \$10. Each copy can press one button. If you both press matching buttons, then you both receive the amount of money written on that button. Otherwise, you receive no money.
    Before being copied, you have an opportunity to take a pill which will override your thinking for the duration of the problem, giving you the overwhelming reflex to press buttons labeled \$10.
\end{example}

Intuitively, the correct answer is to press the \$10 button, and be indifferent about taking the pill (because you'll do the same thing whether you take the pill or not). Unfortunately, UDT's answer depends on its prior! If you have a sufficiently high prior expectation that you'll press the \$5 button, then both red-room self and green-room self will prefer to press \$5.\footnote{Note that this problem is not ruled out by ditching the Vingean principle. Choosing the \$5 button is a consistent equilibrium; if you expect that's what you'll end up doing, then it is in fact what you end up doing.} If you anticipate this, then you will prefer to take the pill before being copied, reflecting a lack of self-trust.

Dai proposed a revised version of UDT to fix this problem, which he called UDT1.1 (making the original UDT retroactively UDT1, or as I prefer, UDT1.0). The suggested fix was to choose the whole policy at once, rather than choosing actions individually. This solves any potential coordination problems between instances. Unfortunately, it does not suit our purposes here, because it violates the Vingean principle: it requires the agent to plan everything at once, which is not realistic.\footnote{One might quibble over whether \emph{deciding} everything at once violates my version of the Vingean principle, which only forbids requiring the agent to \emph{predict} everything at once; however, it is clear that this should be forbidden for the same reason, namely that it is not cognitively realistic for an agent living in a large world.} (In the rest of this paper, plain UDT refers to UDT1.0, but the reader is cautioned that this convention is not universal.)

The approach taken in this paper instead revolves around \emph{communication}. Notice how UDT does not explicitly model agents with memory. If an agent does have memory, it needs to be modeled as part of the observation. This is a sort of communication between instances.

\begin{example}[Memory problem]\footnote{As far as I know, this example is novel, although it is simple enough that I would not be surprised to find an analogue in the literature.}
    At time one, you will observe a red light or a green light. At time two, you will be offered an option to take one (or none) of two pills; one pill makes you say ``red light" in response to any question for the duration of the problem, while the other does the same for ``green light". After making this choice, you will get your memory wiped, and then (at time three) will be asked to report whether the light at time one was green or red, and rewarded for a correct answer.
\end{example}

Clearly, UDT lacks self-trust in this example; it will take the pill to modify its behavior. However, my contention is that this example is ``unfair'' in some sense: the pill was allowed to accomplish something which the agent's own memory was not allowed to do. In order to narrow things down to cases where self-trust can be treated as a rationality criterion, cases like this need to be ruled out. The intuition behind the present work is that lines of communication should ``exactly parallel'' lines of self-modification: if the agent has the ability to act like it remembers something with a self-modifying pill, then it should also be given the ability to remember normally. (All of this will be formalized later.)

Returning to Coordinated Buttons, the suggestion is this: before being copied, when considering whether to take the pill, you can can think to yourself ``I should press the \$10 button''. Once you are copied, you and the copy can recall this thought and press the \$10 button, secure in the knowledge that there would be no reason for your other instance to change its mind.

This allows communication to act as a release valve for pressures which would otherwise give rise to self-modification. Although it does imply some ability to predict other instances in some cases, it only does this to the extent that self-modification can be predicted; if a self-modifying action has effects which are uncertain in their particulars, then the corresponding self-communication will have similarly uncertain impacts. (This will become clearer when stated formally.) As such, I believe it respects the spirit of the Vingean principle.

Unfortunately, this idea will not be enough to carry us all the way.

\begin{example}[Third Button problem]\footnote{I believe this example is a novel contribution.}
    As in Coordinated Buttons, you are about to be copied, and you have the option of taking a pill which will cause you to press buttons labeled \$10 for the duration of the problem. You also have the option of telling yourself to press \$10 buttons. However, when you get into the red and green rooms, there will be a third button labeled \$20. If both of you press \$5, you both get \$5; if both of you press \$10, you both get \$10; if one of you presses \$10 and the other presses \$20, you both get \$20; in all other cases, you both receive \$0. You have no way to randomize your choices, and you cannot tell yourself to do different things depending on the color of the room (your memory will be wiped in such a case).
\end{example}

This problem seems to be ``fair'' by the standards mentioned so far, yet UDT may still choose self-modification. Depending on its prior, UDT may still need to use the pill to choose \$10. If it instead elects to tell itself to choose \$10, then by the reasoning proposed earlier, each copy would trust that the other copy will follow this instruction; however, if that were true, \emph{this would lead both copies to choose \$20}, resulting in a payoff of \$0.

As such, we will also need to rule out cases like this in order to achieve self-trust. To achieve this, we will need to deal with a conceptual flaw which arises in some interpretations of Yudkowsky's notion of fairness: naively, at least, self-modification is itself a decision, so Yudkowsky's notion of decision-determination fails to rule out universes which ask you to self-modify into an alphabetizer and punish you for not doing so (exactly the scenario Yudkowsky wants to rule out). We can resolve this problem by distinguishing between an agent's \emph{external} observations and actions (these are the observations and actions most typically studied by decision theory), versus \emph{internal} observations and actions (such as recalling or storing memories). A fair environment is, roughly, allowed to depend on external behaviors but not internal behaviors.

The remainder of the paper formalizes these ideas.


\section{Mathematical Preliminaries}

The mathematical formalism used here was significantly inspired by Finite Factored Sets \cite{garrabrant2021temporal}, although it differs considerably in the details, and does not attempt to deal with issues of time or causality.

\subsection{Random Variables}

We work with a probability space $(\Omega, \Prob)$. A \emph{random variable} is a measurable function $X : \Omega \to \range X$ from $\Omega$ to some measurable space $\range X$, which we call the \emph{range} of $X$. We will generally assume our random variables have countable discrete range and finite entropy.

Following standard conventions, we treat random variables as if they are elements of their ranges. For example, if $X$ is a random variable valued in $R$ and $f : R \to S$ is a measurable function, we write $f(X)$ to mean $f \circ X$. Given random variables $X : \Omega \to R$ and $Y : \Omega \to S$, we write $(X, Y)$ for the \emph{product random variable} $\Omega \to R \times S$ defined as $\omega \mapsto (X(\omega), Y(\omega))$.

More generally, if $(X_i)_{i \in I}$ is a family of random variables on $\Omega$, we use the \emph{tuple-builder notation} $(X_i : i \in I, \phi(i))$ to denote the product random variable of those $X_i$ such that $\phi(i)$ holds. The range of this random variable is the product space $\prod_{i : \phi(i)} \range X_i$.

\begin{definition}
If $X$ and $Y$ are random variables on $\Omega$, we say $Y$ \emph{is a function of} $X$ if there exists a measurable function $f : \range X \to \range Y$ such that $Y = f(X)$ almost everywhere. Equivalently, $H(Y | X) = 0$.
\end{definition}

When $Y$ is a function of $X$, we also say $Y$ is a \emph{coarsening} of $X$, or $X$ is a \emph{refinement} of $Y$, or $Y$ is a \emph{subvariable} of $X$. Intuitively, $X$ provides at least as much information as $Y$, since knowing $X$ determines $Y$.

\begin{definition}
If $Y$ is a function of $X$ via $f : \range X \to \range Y$, we call $f$ the \emph{projection} from $X$ to $Y$, and write $`x`_Y = f(x)$ for $x \in \range X$. For a function $g : Z \to \range X$, we define $`g`_Y = f \circ g$.
\end{definition}

\begin{definition}
Given random variables $X$ and $Y$:
\begin{itemize}
    \item The \emph{joint random variable} $(X, Y)$ serves as the coarsest common refinement of $X$ and $Y$: both $X$ and $Y$ are functions of $(X,Y)$.
    \item The \emph{common information} $X \vee Y$ is defined (when it exists) as the finest random variable that is a function of both $X$ and $Y$. Equivalently, it captures exactly the information shared by $X$ and $Y$.
\end{itemize}
\end{definition}

\begin{remark}
Unlike the partition-based framework, where meet and join always exist, the common information $X \vee Y$ may not exist as a single random variable in general. However, it can always be characterized information-theoretically, and in our discrete setting it will exist.
\end{remark}

\subsection{Random Variable Models}

Following the framework of \cite{eisenstat2024condensation}, we package our random variables together with their probability space.

\begin{definition}
A \emph{random variable model} is a countable discrete probability space $\Omega$ with finite entropy, together with a finite family of random variables $(X_i)_{i \in I}$, each with countable discrete range.
\end{definition}

We use subscript notation for joint random variables: if $A \subseteq I$, then $X_A = (X_i : i \in A)$ denotes the product random variable.

\subsection{Factorization}

\begin{definition}
A random variable $X$ \emph{factors as} $(Y, Z)$ if and only if:
\begin{enumerate}
    \item $X = (Y, Z)$ as random variables (i.e., $X$ is the product of $Y$ and $Z$), and
    \item For every $y \in \range Y$ and $z \in \range Z$, there exists $\omega \in \Omega$ with $Y(\omega) = y$ and $Z(\omega) = z$.
\end{enumerate}
\end{definition}

The second condition says that all combinations of values are possible---$Y$ and $Z$ are \emph{independent in support}. This is stronger than merely having $X = (Y, Z)$, which only says that knowing $Y$ and $Z$ determines $X$.

\begin{definition}
When $X$ factors as $(Y, Z)$, there exists a surjective function $m : \range Y \times \range Z \to \range X$, namely $m(y, z) = (y, z)$. We call this the \emph{restriction map}. For fixed $y \in \range Y$, we get a function $m_y : \range Z \to \range X$ given by $m_y(z) = m(y, z)$.
\end{definition}

This notion extends to families of random variables:

\begin{definition}
$X$ \emph{factors as} $(X_i)_{i \in I}$ if and only if there exists a surjective map $m$ from choice functions $c : (i : I) \to \range X_i$ to $\range X$, namely $m(c) = (c(i))_{i \in I}$.
\end{definition}

Here $(a : A) \to B_a$ denotes a dependent function type: the domain is $A$, and for every $a \in A$, $f(a) \in B_a$.

\subsection{Function Decomposition}

\begin{definition}
A function $f : \range X \to \range Y$ \emph{decomposes into} functions $(f_i : \range X_i \to \range Y_i)_{i \in I}$ if:
\begin{enumerate}
    \item $Y$ factors as $(Y_i)_{i \in I}$
    \item Each $X_i$ is a subvariable of $X$
    \item $f(x) = (f_i(`x`_{X_i}))_{i \in I}$ for all $x \in \range X$
\end{enumerate}
\end{definition}

\subsection{Partial Functions}

We write $X \rightharpoonup Y$ for the type of partial functions from $\range X$ to $\range Y$. For $f : X \rightharpoonup Y$, we write $f(x) = \bot$ when $f$ is undefined at $x$. The domain $\dom(f)$ is the set of inputs where $f$ is defined.

\subsection{Probability and Expectation}

We assume a probability measure $\Prob$ on $\Omega$. For a random variable $X$ and value $x \in \range X$, we write $\Prob(X = x)$ for $\Prob(\{\omega : X(\omega) = x\})$.

We will have a utility random variable $U : \Omega \to \mathbb{R}$, assumed bounded with $U(\omega) \in [0, 1]$. The conditional expectation $\E(U | X = x)$ is well-defined when $\Prob(X = x) > 0$. When $\Prob(X = x) = 0$, we stipulate $\E(U | X = x) = -1$.\footnote{This ensures an agent will not choose a probability-zero action. An earlier draft used $\E(U|X=x)=2$ in such cases; however, this causes problems with the ``instances are believed to follow recommendations'' assumption.}


\section{Agents \& Environments}

In this section, we apply the above framework to model agents. This approach takes significant inspiration from Critch's work on agent boundaries \cite{Critch2022BoundariesSequence} and Garrabrant's work on Cartesian Frames \cite{garrabrant2021cartesian}, though it differs considerably in the details.

We model the world using three random variables:

\begin{itemize}
    \item $I$: The \textbf{interior} of the agent, representing persistent state (memories or more complex cognition).
    \item $B$: The \textbf{boundary} of the agent, implementing the decision procedure (handling input/output with the environment).
    \item $E$: The \textbf{external environment}, containing everything in the agent's exterior.
\end{itemize}

For example, if $I$ represents an SSD's state, each value $i \in \range I$ corresponds to a specific bit pattern, and $I(\omega) = i$ means that in world $\omega$, the SSD holds that pattern.

\subsection{Information Flow}

Four random variables mediate information flow between $I$, $B$, and $E$:

\begin{itemize}
    \item $\dot{O}$: The \textbf{internal observation}---memories or internal computations accessible to the decision procedure. $\dot{O}$ is a subvariable of both $I$ and $B$, representing output from $I$ that flows into $B$.

    \item $\ddot{O}$: The \textbf{external observation}---sense data. $\ddot{O}$ is a subvariable of both $E$ and $B$, representing output from $E$ that flows into $B$.

    \item $\dot{A}$: The \textbf{internal action}---data to store/process. $\dot{A}$ is a subvariable of both $I$ and $B$, representing output from $B$ that flows into $I$. Together with $\dot{O}$, this exhausts the overlap between $I$ and $B$: the common information $I \vee B$ equals $(\dot{O}, \dot{A})$.

    \item $\ddot{A}$: The \textbf{external action}---motor commands. $\ddot{A}$ is a subvariable of both $E$ and $B$, representing output from $B$ that flows into $E$. Together with $\ddot{O}$, this exhausts the overlap between $B$ and $E$: the common information $B \vee E$ equals $(\ddot{O}, \ddot{A})$.
\end{itemize}

We define composite random variables:
\begin{itemize}
    \item $O = (\dot{O}, \ddot{O})$: the full observation (all inputs to $B$)
    \item $A = (\dot{A}, \ddot{A})$: the full action (all outputs from $B$)
\end{itemize}

We assume $O$ factors as $(\dot{O}, \ddot{O})$ and $A$ factors as $(\dot{A}, \ddot{A})$.

We also define two subvariables of $\dot{O}$:
\begin{itemize}
    \item $\hat{O}$: the \textbf{semantic observation}---the information the agent is \emph{supposed to} receive when functioning normally.
    \item $\check{O}$: the \textbf{side channel}---aspects of the input that may modify the agent's behavior, causing it to act ``off-policy.''
\end{itemize}

Note that $\hat{O}$ and $\check{O}$ need not factor $\dot{O}$; some semantic observations may be inextricably linked to side-channel effects.

\subsection{Dynamics}

The relationships between these variables are captured by \emph{dynamics}---random variables that encode input-output behavior. Dynamics are examples of what we call \emph{condensation variables}: random variables that represent the ``missing information'' needed to determine an output from an input.

\begin{definition}[Condensation Variable]
Given random variables $X$ and $Y$, a random variable $V$ is a \textbf{condensation variable} for $H(X|Y)$ (the conditional entropy of $X$ given $Y$) if:
\begin{enumerate}
    \item $H(X | Y, V) = 0$ (knowing both $Y$ and $V$ determines $X$)
    \item $V$ is independent of $Y$ in support (all combinations of values are possible)
    \item $H(V) = H(X | Y)$ (V is minimal---it contains exactly the missing information)
\end{enumerate}
\end{definition}

Intuitively, if we think of $Y$ as an input and $X$ as an output, then a condensation variable $V$ captures exactly the additional information needed to compute $X$ from $Y$. The factorization $X = f(Y, V)$ makes the input-output relationship explicit: different values of $V$ correspond to different functions from $Y$ to $X$.

\begin{assumption}[Internal Dynamic]
$I$ factors as $(\dot{A}, D_I)$.
\end{assumption}

The random variable $D_I$ is the condensation variable for $H(I | \dot{A})$---it represents the residual information needed to determine the interior state $I$ given the internal action $\dot{A}$. For a fixed value $d_I \in \range D_I$, there is a function $\iota_{d_I} : \range \dot{A} \to \range I$ giving the interior's response to each internal action. Since $\dot{O}$ is a subvariable of $I$, this yields the input-output function $`\iota_{d_I}`_{\dot{O}} : \range \dot{A} \to \range \dot{O}$.

\begin{assumption}[Environment Dynamic]
$E$ factors as $(\ddot{A}, D_E)$.
\end{assumption}

Similarly, $D_E$ is the condensation variable for $H(E | \ddot{A})$---it represents the residual information needed to determine the environment $E$ given the external action $\ddot{A}$. For $d_E \in \range D_E$, we get $\epsilon_{d_E} : \range \ddot{A} \to \range E$.

\begin{assumption}[Boundary Dynamic]
$B$ factors as $(O, D_B)$.
\end{assumption}

The dynamic $D_B$ is the condensation variable for $H(A | O)$ (equivalently, $H(B | O)$ since $B$ factors as $(O, A)$ up to the action)---it represents the residual information needed to determine the agent's action $A$ given the observation $O$. For $d_B \in \range D_B$, we get $\beta_{d_B} : \range O \to \range B$.

\begin{assumption}[Agent Dynamic Constraint]
$(I, B)$ factors as $(\ddot{O}, D_{I,B})$, where $D_{I,B} = (D_I, D_B)$.
\end{assumption}

This states that the combined agent state $(I, B)$ is fully determined by the external observation and the joint dynamics. We write $\rho_{d_{I,B}} : \range \ddot{O} \to \range(I, B)$ for the resulting function.

\subsection{Notions of Policy}

\begin{definition}
A \textbf{full policy} is a function $\pi : \range O \to \range A$.
\end{definition}

\begin{definition}
The \textbf{effective policy} $\Pi^\dagger$ is the random variable representing the full policy actually implemented by the agent: $\Pi^\dagger = `\beta_{D_B}`_A$, which maps observations to actions.
\end{definition}

We treat $\Pi^\dagger$ both as a set of functions and as a subvariable of $D_B$. This subvariable relationship has a natural interpretation in terms of condensation: the boundary dynamic $D_B$ is the full condensation variable for $H(A|O)$, while the policy $\Pi^\dagger$ is a \emph{coarsening} of $D_B$ that preserves the observation-to-action function while forgetting implementation details. Multiple values of $D_B$ may correspond to the same policy---they represent different ``implementations'' of the same input-output behavior.

\begin{definition}
The \textbf{chosen policy} $\Pi^*$ is the random variable representing the full policy that \emph{would be} implemented if the agent's decision procedure were never modified.
\end{definition}

\begin{definition}
The \textbf{external policy} $\ddot{\Pi}$ is the function $\ddot{\pi} : \range \ddot{O} \to \range \ddot{A}$ that the agent appears to implement from an external perspective: $\ddot{\pi}(\ddot{o}) = `\rho_{d_{I,B}}(\ddot{o})`_{\ddot{A}}$.
\end{definition}

The external policy $\ddot{\Pi}$ is a subvariable of $D_{I,B}$.

\begin{definition}[Abstract Decision Structure]
An \emph{abstract decision structure} consists of random variables $(I, B, E, \dot{O}, \ddot{O}, \dot{A}, \ddot{A}, D_I, D_E, D_B, \hat{O}, \check{O}, \Pi^*, U)$ satisfying all the above definitions and assumptions.
\end{definition}

\begin{definition}[Decision-Determination]
An abstract decision structure is \textbf{decision-determined} if and only if:
\begin{enumerate}
    \item $U$ is a function of $E$, and
    \item $E$ is conditionally independent of $D_{I,B}$ given $\ddot{\Pi}$:
    $$\Prob(E = e \mid D_{I,B} = d_{I,B}) = \Prob(E = e \mid \ddot{\Pi} = `d_{I,B}`_{\ddot{\Pi}})$$
\end{enumerate}
\end{definition}

In words: the external policy is the only thing intrinsic to the agent that impacts the external environment, and utility depends only on the external environment.


\section{Instances \& Communication}

To model agents with multiple instances, we factor the agent by external observation---each value of $\ddot{O}$ defines a different instance.

\subsection{Instance Structure}

\begin{definition}[Instance Factorization]
$B$ factors as $(B_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$. Each $B_{\ddot{o}}$ represents the decision-making for observation $\ddot{o}$. Correspondingly:
\begin{itemize}
    \item $\dot{A}$ factors as $(\dot{A}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
    \item $\ddot{A}$ factors as $(\ddot{A}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
    \item $A$ factors as $(A_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$, with each $A_{\ddot{o}}$ factoring as $(\dot{A}_{\ddot{o}}, \ddot{A}_{\ddot{o}})$
    \item $\dot{O}$ factors as $(\dot{O}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
    \item $\check{O}$ factors as $(\check{O}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$, each a subvariable of $\dot{O}_{\ddot{o}}$
    \item $\hat{O}$ factors as $(\hat{O}_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$, each a subvariable of $\dot{O}_{\ddot{o}}$
    \item Full policies $\pi$ decompose into \textbf{instance policies} $\pi_{\ddot{o}} : \range \dot{O}_{\ddot{o}} \to \range A_{\ddot{o}}$
    \item $\Pi^*$ factors as $(\Pi^*_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
    \item $\Pi^\dagger$ factors as $(\Pi^\dagger_{\ddot{o}})_{\ddot{o} \in \range \ddot{O}}$
\end{itemize}
\end{definition}

\subsection{Communication Structure}

\begin{definition}[Message Semantics]
For each $\ddot{o} \in \range \ddot{O}$, there is a partial function $s_{\ddot{o}} : \range \hat{O}_{\ddot{o}} \rightharpoonup \range \ddot{A}$ giving the semantics: each $\hat{o}_{\ddot{o}}$ either recommends a specific external action or remains silent.

The \textbf{recommendation} $R$ is the random variable whose values are partial functions $r : \range \ddot{O} \rightharpoonup \range \ddot{A}$, where $r(\ddot{o}) = s_{\ddot{o}}(`\dot{O}`_{\hat{O}_{\ddot{o}}})$. $R$ is a subvariable of $\dot{O}$.
\end{definition}

We write $\ddot{\Pi} = R$ to indicate that recommendations are followed: for all $\hat{o}$ and all $\ddot{o} \in \dom(r_{\hat{o}})$, we have $\ddot{\pi}(\ddot{o}) = r_{\hat{o}}(\ddot{o})$.

\begin{definition}[Side-Channel Impact]
For each $\ddot{o}$, there is a partial function $p_{\ddot{o}} : \range \check{O}_{\ddot{o}} \rightharpoonup \range \ddot{A}$ indicating what action is forced by a side-channel value.

The \textbf{forced external policy} $P$ is the random variable with values $q : \range \ddot{O} \rightharpoonup \range \ddot{A}$, where $q(\ddot{o}) = p_{\ddot{o}}(`\dot{O}`_{\check{O}_{\ddot{o}}})$. $P$ is a subvariable of $\dot{O}$.
\end{definition}

\begin{definition}[Modification]
A \textbf{modification} occurs when $\dom(P) \neq \emptyset$. The \textbf{modification probability} of an event $e$ is $m(e) = \Prob(\dom(P) \neq \emptyset \mid e)$.
\end{definition}

\begin{definition}[Concrete Decision Structure]
A \emph{concrete decision structure} is an abstract decision structure satisfying all the instance and communication conditions above.
\end{definition}


\section{Avoiding Self-Modification}

Consider an agent with chosen instance policy determined by UDT:
$$\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = \argmax_{a_{\ddot{o}} \in \range A_{\ddot{o}}} \E[U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}]$$

\begin{definition}
An action $a_{\ddot{o}} \in \range A_{\ddot{o}}$ is \textbf{minimally modifying} at $\dot{o}_{\ddot{o}}$ if:
$$m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \min_{a' \in \range A_{\ddot{o}}} m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a')$$
\end{definition}

\begin{definition}[Communicative Alternative]
For $a_{\ddot{o}} \in \range A_{\ddot{o}}$ and $\dot{o}_{\ddot{o}} \in \range \dot{O}_{\ddot{o}}$, a \textbf{communicative alternative} $ca_{\dot{o}_{\ddot{o}}}(a_{\ddot{o}}) \in \range A_{\ddot{o}}$ satisfies:
\begin{enumerate}
    \item $ca(a_{\ddot{o}})$ is minimally modifying at $\dot{o}_{\ddot{o}}$
    \item For all external policies $\ddot{\pi}$:
    $$\Prob(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \Prob(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}), \ddot{\Pi} = R)$$
\end{enumerate}
\end{definition}

\begin{lemma}[Communicative Expectation]
If a concrete decision structure is (1) decision-determined and (2) has communicative alternatives, then:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}))$$
\end{lemma}

\begin{proof}
By decision-determination:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \sum_{\ddot{\pi}} \E(U \mid \ddot{\Pi} = \ddot{\pi}) \Prob(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}})$$

$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}), \ddot{\Pi} = R) = \sum_{\ddot{\pi}} \E(U \mid \ddot{\Pi} = \ddot{\pi}) \Prob(\ddot{\Pi} = \ddot{\pi} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}), \ddot{\Pi} = R)$$

Since the distributions match by the communicative alternative condition, the expected utilities are equal.
\end{proof}

\begin{theorem}[Self-Trust]
If a concrete decision structure is (1) decision-determined, (2) has communicative alternatives, and (3) has $\Prob(\ddot{\Pi} = R) = 1$, then non-minimally-modifying actions are never strictly preferred by UDT:
$$m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) > \min_{a'} m(\Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a')$$
$$\implies$$
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) \leq \max_{a'} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a')$$
\end{theorem}

\begin{proof}
Let $a_{\ddot{o}}$ be non-minimally-modifying. By the lemma:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = a_{\ddot{o}}) = \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}), \ddot{\Pi} = R)$$

By condition (3), this equals $\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = ca(a_{\ddot{o}}))$, which is at most the maximum over all actions.
\end{proof}

Note that condition (3) is about the agent's \emph{subjective} probability---we assume the agent \emph{expects} its instances to follow recommendations.


\section{Following Advice}

\begin{definition}[Stability]
A recommendation $r$ is \textbf{stable} if for all $\ddot{o} \in \dom(r)$, all $\dot{a}_{\ddot{o}}$, and all $\ddot{a}'_{\ddot{o}} \neq r(\ddot{o})$:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, r(\ddot{o})), [\ddot{\Pi} = r]_{-\ddot{o}}) > \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, \ddot{a}'_{\ddot{o}}), [\ddot{\Pi} = r]_{-\ddot{o}})$$
\end{definition}

\begin{definition}[Internally-Driven Recommendations]
Recommendations are \textbf{internally driven} if for all $\dot{o}, \ddot{o}, \dot{a}, \ddot{a}, \ddot{a}'$:
$$\Prob(R = r \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a})) = \Prob(R = r \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}'))$$
\end{definition}

\begin{theorem}[Advice-Following]
If a concrete decision structure (1) has $\Prob(\ddot{\Pi} = R) = 1$, (2) has internally-driven recommendations, (3) has recommendations that are stable with probability one, and (4) $s_{\ddot{o}}(`\dot{o}`_{\hat{O}}) \neq \bot$, then for all $\ddot{a}_{\ddot{o}} \neq s_{\ddot{o}}(`\dot{o}`_{\hat{O}})$:
$$\E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, s_{\ddot{o}}(`\dot{o}`_{\hat{O}}))) > \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}_{\ddot{o}}, \ddot{a}_{\ddot{o}}))$$

If UDT is the decision rule and instances never receive recommendations and modifications simultaneously, then $\ddot{\Pi} = R$ in fact.
\end{theorem}

\begin{proof}
We show $\argmax_{\ddot{a}} \max_{\dot{a}} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a})) = r_{`\dot{o}`_{\hat{O}}}(\ddot{o})$.

Decomposing over recommendations to other instances $r_{-\ddot{o}}$:
$$\argmax_{\ddot{a}} \max_{\dot{a}} \sum_{r_{-\ddot{o}}} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}), r_{-\ddot{o}}) \Prob(r_{-\ddot{o}} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}))$$

Let $\dot{a}$ be optimal given the best $\ddot{a}$. By (1):
$$= \argmax_{\ddot{a}} \sum_{r_{-\ddot{o}}} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}), [\ddot{\Pi} = r]_{-\ddot{o}}) \Prob(r_{-\ddot{o}} \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}))$$

By (2), $\Prob(r_{-\ddot{o}} \mid \cdots)$ is constant in $\ddot{a}$:
$$= \argmax_{\ddot{a}} \sum_{r_{-\ddot{o}}} \E(U \mid \Pi^*(\dot{o}_{\ddot{o}}, \ddot{o}) = (\dot{a}, \ddot{a}), [\ddot{\Pi} = r]_{-\ddot{o}})$$

By (3) and (4), this equals $r_{`\dot{o}`_{\hat{O}}}(\ddot{o})$.
\end{proof}


\section{Conclusion}

Yudkowsky's notion of fairness (decision-determination) arguably had a conceptual flaw: self-modification is itself a decision, so decision-determination does not rule out problems that directly incentivize self-modification.

I interpreted decision-determination to avoid this problem by distinguishing internal from external actions. A ``fair problem'' is one where the universe doesn't care about internal makeup except through external choices.

However, decision-determination still isn't enough. Section 3 provided counterexamples where self-trust fails without it being the decision procedure's fault.

Theorem 1 showed self-trust for UDT under three conditions: decision-determination, communicative alternatives, and belief that one follows advice. Theorem 2 showed that advice-following belief is self-fulfilling under further conditions of internally-driven recommendations, stable recommendations, and mutual exclusivity of recommendations and modifications.

I suggest fairness consists of at least decision-determination, communicative alternatives, and stable recommendations. Something like $\Prob(\ddot{\Pi} = R) = 1$ also seems necessary---a form of ``self-esteem.''

Future work could:
\begin{itemize}
    \item Transform these ideas into a representation theorem
    \item Model computational uncertainty properly
    \item Generalize to agents without shared goals/beliefs
    \item Generalize to agents without shared ontology
\end{itemize}



\bibliographystyle{alpha}
\bibliography{sample}

\end{document}


---
# === FILE: condensation-variables.md ===
---

# Condensation Variables

## Overview

In standard probability theory, information-theoretic quantities like mutual information I(X; Y) and conditional entropy H(X | Y) are **numbers**. Condensation theory's central claim is that these quantities can be **represented as random variables**.

This document defines precisely what "representable" means and establishes the vocabulary for the rest of the UDT representation theorem project.

## The Representability Condition

### Mutual Information as Common Information

For random variables X and Y, the mutual information I(X; Y) is **representable** if there exists a random variable V such that:

1. **V is a subvariable of both X and Y**: There exist measurable functions f and g such that V = f(X) = g(Y) almost everywhere.

2. **V captures the mutual information**: H(V) = I(X; Y)

3. **V is maximal**: V is the finest (highest-entropy) random variable satisfying conditions 1 and 2.

When these conditions hold, we call V the **common information** of X and Y, written X ∨ Y. This is the Gács-Körner common information — the "shared part" of X and Y reified as an actual random variable, not just a number.

**Intuition**: V represents the information that is simultaneously "contained in" both X and Y. Knowing X tells you V; knowing Y also tells you V; and V captures all and only the information that both provide.

### Conditional Entropy as Residual Information

For random variables X and Y, the conditional entropy H(X | Y) is **representable** if there exists a random variable W such that:

1. **W completes Y to determine X**: H(X | Y, W) = 0. Equivalently, X is a function of (Y, W).

2. **W is independent of Y in support**: For every y ∈ range(Y) and w ∈ range(W), there exists ω ∈ Ω with Y(ω) = y and W(ω) = w.

3. **W is minimal**: H(W) = H(X | Y)

When these conditions hold, we call W the **residual** of X given Y, or the **condensation variable** for the relationship X | Y.

**Intuition**: W is the "missing information" — exactly what you would need to know, beyond Y, in order to determine X. The independence condition (2) ensures W genuinely represents new information rather than being entangled with Y.

### Higher-Order Quantities

The same representability concept extends to:

- **Conditional mutual information** I(X; Y | Z): Representable as a variable that is a common subvariable of X and Y when conditioned on Z.

- **Interaction information** I(X; Y; Z): The three-way generalization, which can be positive or negative.

- **Conditional interaction information** I(X; Y; Z | W): And so on for higher orders.

## The Condensation Assumption

**Definition (Condensation Assumption)**: A probability space satisfies the **condensation assumption** if all information-theoretic quantities — mutual informations, conditional entropies, and all higher-order interaction informations and conditional variants — are representable as random variables.

This is a **strong assumption** that does not hold for arbitrary probability distributions. 

**When it holds**: Finite discrete probability spaces with full support typically satisfy condensation. More generally, spaces that factor nicely into independent components.

**When it fails**: Continuous distributions, or discrete distributions with complex dependency structures, may have information-theoretic quantities that cannot be captured by any single random variable.

## Condensation Variables in the IBE Framework

Given the condensation assumption, the "dynamics" in the Interior/Boundary/Environment framework are precisely condensation variables:

### Boundary Dynamic D_B

D_B is the condensation variable for the relationship A | O (action given observation):

- H(A | O, D_B) = 0 — knowing observation and dynamic determines action
- D_B is independent of O in support — all (observation, dynamic) pairs are possible
- H(D_B) = H(A | O) — D_B captures exactly the "missing information"

**Interpretation**: D_B represents everything about the agent's decision procedure that isn't determined by the observation. Two worlds with the same D_B value will map observations to actions in the same way.

### Interior Dynamic D_I

D_I is the condensation variable for the relationship I | Ȧ (interior given internal action):

- H(I | Ȧ, D_I) = 0
- D_I is independent of Ȧ in support  
- H(D_I) = H(I | Ȧ)

**Interpretation**: D_I represents how the interior processes and stores information.

### Environment Dynamic D_E

D_E is the condensation variable for the relationship E | Ä (environment given external action):

- H(E | Ä, D_E) = 0
- D_E is independent of Ä in support
- H(D_E) = H(E | Ä)

**Interpretation**: D_E represents everything about the environment's response that isn't determined by the agent's action.

## Policy as Coarsening of D_B

The **policy** Π is a coarsening (subvariable) of D_B defined by:

**Definition**: Two values d_B and d'_B of D_B are **policy-equivalent** if they induce the same function from observations to actions:
```
`β_{d_B}`_A = `β_{d'_B}`_A
```

The policy Π is the quotient of D_B by this equivalence relation.

**Key properties**:
- Π is a subvariable of D_B (every policy value corresponds to a set of D_B values)
- H(A | Π, O) = 0 (policy + observation determines action)
- Π forgets "implementation details" while preserving input-output behavior

This connects to the information-theoretic characterization in policy-as-latent.md: the policy is the minimal variable such that H(A | Π, O) = 0.

## Why Condensation Matters for Agency

The condensation assumption allows us to:

1. **Reify abstract relationships**: Instead of talking about "the information needed to predict A from O," we can point to an actual random variable D_B.

2. **Factor complex systems**: The IBE decomposition with dynamics becomes a precise factorization of the probability space.

3. **Define agency information-theoretically**: Agency attribution becomes the problem of finding appropriate condensation variables (policy, utility, etc.) that explain observed behavior.

4. **Connect to decision-determination**: The condition I(E; D_B | Π) = 0 (environment responds only to policy, not to implementation details) becomes a precise statement about conditional independence given a condensation variable.

## References

- Gács, P., & Körner, J. (1973). Common information is far less than mutual information.
- Eisenstat (2024). Condensation framework.
- Garrabrant. Finite Factored Sets.


---
# === FILE: policy-as-latent.md ===
---

# Policy as Latent Variable

## The Core Insight

When we have two random variables A (actions) and B (observations), the "policy" isn't just a function π : B → A. It's a **random variable Π** that captures *which* function relates them.

## Information-Theoretic Decomposition

Given random variables A and B:

- **I(A; B)** — mutual information, what's shared
- **H(A | B)** — conditional entropy, what remains uncertain about A given B
- **H(B | A)** — conditional entropy, what remains uncertain about B given A

Condensation theory says we can reify these as random variables:
- **A ∨ B** — the common information (finest variable that's a function of both)
- The "conditional parts" — what's left over

## The Deterministic Case

If **H(A | B) = 0**, then A is a deterministic function of B. Knowing B determines A completely.

But in general, **H(A | B) > 0** — there's uncertainty about A even knowing B.

## The Policy as "Missing Information"

The policy Π is the random variable such that:

```
H(A | Π, B) = 0
```

That is: once we know both the policy Π and the observation B, the action A is determined.

But:
```
H(A | B) > 0  (in general)
```

The policy is exactly the information that's "missing" — what you'd need to know, in addition to B, to predict A.

## Different Worlds, Different Policies

This framing makes clear: different worlds ω ∈ Ω might have different policies.

- In world ω₁, the policy might be π₁ (always cooperate)
- In world ω₂, the policy might be π₂ (always defect)

The random variable Π assigns to each world its policy: Π(ω) = the function that world uses to map observations to actions.

## Connection to the IBE Framework

In the Communication & Trust framework:

- **D_B** (boundary dynamic) is a random variable encoding the full decision mechanism
- **Π** (policy) is a *coarsening* of D_B — the equivalence class that forgets implementation details
- **Π†** (effective policy) is what actually gets implemented
- **Π*** (chosen policy) is what would be implemented without modification

The policy Π is the latent that:
1. Is a subvariable of the mechanism D_B
2. Together with observations O, determines actions A
3. Is what the environment responds to (decision-determination)

## Why This Matters for the Representation Theorem

The question "what does it mean to recognize an agent?" becomes:

> Finding a latent variable Π such that H(A | Π, B) = 0

This is a **condensation condition** — we're finding the minimal latent that explains the action-observation relationship.

The representation theorem should say: if you find such a Π, and the environment only responds to Π (decision-determination), then optimizing over Π gives the UDT formula.

## Contrast with "Policy as Function"

**Old framing (policy as function):**
- A policy is π : Obs → Act
- We optimize over the space of functions
- The theorem says: optimal π satisfies UDT formula

**New framing (policy as latent):**
- A policy is a random variable Π
- Π is characterized by: H(A | Π, O) = 0
- The theorem should derive: if Π is a good condensation, and environment responds only to Π, then UDT

The new framing connects to condensation theory and makes the information-theoretic content explicit.


---
# === FILE: formal-single-agent.md ===
---

# Formalizing "Single Agent": The Mathematical Core

## The Challenge

The core argument says: if you model X as a *single agent*, updateless reasoning follows.

But what exactly does "single agent" mean mathematically? We need a definition that:
1. Is independently motivated (not circular with UDT)
2. Captures the intuitive concept of unified agency
3. Has determinate formal consequences (implies UDT)

## Starting Point: Situations and Behaviors

**Definition.** A **multi-situation decision problem** is a tuple (S, P, A, U) where:
- S is a finite set of **situations** (decision points the agent might face)
- P is a probability distribution over S (which situation obtains)
- A is a finite set of **actions** available at each situation
- U: S × A → ℝ is a **utility function**

Note: We're being deliberately agnostic about what "situations" are. They could be:
- Different times
- Different possible worlds
- Different copies of the agent
- Different observations

The key is that an agent might face *any* of these situations and must choose an action.

## Approach 1: Split Model (Multiple Optimizers)

**Definition.** A **split decision procedure** is a family of functions {D_s : s ∈ S} where each D_s chooses an action for situation s.

Under the split model:
- Each D_s optimizes independently
- D_s chooses a_s = argmax_a E[U(s, a) | s obtains]
- The D_s's might share a utility function, but they optimize separately

**Key property:** D_s's choice depends only on what's optimal *given s obtains*. It ignores other situations.

## Approach 2: Unified Model (Single Optimizer)

**Definition.** A **unified decision procedure** is a single function D: S → A choosing an action for each situation.

Under the unified model:
- There's ONE optimization
- D is chosen to maximize E[U(s, D(s))] = Σ_s P(s) · U(s, D(s))
- Each D(s) is part of a globally optimal *policy*

**Key property:** D(s) is chosen considering how the choice affects total expected utility, not just utility in situation s.

## Why These Are Different

In many problems, the split and unified approaches give the same answer. But they diverge when:

**Condition C:** The environment's response to the agent depends on the *pattern* of actions across situations, not just the action in the current situation.

Under Condition C:
- U(s, a) might depend on what the agent does in other situations
- The split approach ignores these dependencies
- The unified approach accounts for them

## Formalizing "Pattern Dependence"

**Definition.** A problem has **cross-situation dependence** if there exist situations s ≠ s' and actions a, a' such that:

U(s, a) depends on the action chosen at s'

More precisely: there exists a policy π with π(s) = a and π(s') = a₁, and another policy π' with π'(s) = a and π'(s') = a₂, such that:

E[U | π] ≠ E[U | π'] despite agreeing on action at s

This happens when "what you do elsewhere" affects "what happens here."

## The Core Theorem

**Theorem (Single Agent = Updateless).**
Let D be a decision problem with cross-situation dependence. If an agent:
1. Treats all situations as "itself" (unity)
2. Aims to maximize expected utility (rationality)
3. Recognizes the cross-situation dependence (awareness)

Then the agent reasons updatelessly: for each s, it chooses the action that is part of the globally optimal policy.

**Proof sketch:**
- By (1), the agent views S as situations it might face as a single entity
- By (2), it wants to maximize E[U]
- By (3), it recognizes that U depends on the full policy, not just local actions
- Therefore, it chooses a policy π maximizing E[U(s, π(s))]
- At each s, it implements π(s)

## Why the Split Model Violates Unity

If an agent uses the split model, it's implicitly treating each D_s as a separate decision-maker.

**Argument:** D_s, optimizing independently, asks: "What should *I* do, given that situation s obtains?"

This question treats s as primitive and separate. It doesn't ask: "What should *the agent* do across all situations?"

If the agent is truly unified, there's no "I" at situation s separate from the agent as a whole. The question "what should I do at s?" is really "what should the agent's policy say for s?"

## The Burden of Proof (Formalized)

**Claim:** The unified model is the *default* when attributing agency. The split model requires additional structure.

**Formal version:** Given a utility function U over situations and actions, the simplest model is a single optimization:

max_π E[U(s, π(s))]

The split model requires specifying:
- What defines the boundaries between D_s's
- How the D_s's are related
- Why they share a utility function but not an optimization

These are additional modeling choices beyond the basic agency attribution.

## Connection to Functional Identity

**Functional identity** provides one way to justify unity formally:

**Definition.** An agent has **functional identity** if all instances (situations) are outputs of the same algorithm F: O → A, where O is the observation space.

**If functional identity holds:** When the agent asks "what should I do at observation o?", the answer is F(o). Since F is fixed, this answer is part of a complete policy. Changing F(o) means changing F, which changes all outputs.

**Consequence:** An agent with functional identity cannot coherently ask "what should I do at o?" in isolation. Its action at o is part of its global algorithm F.

## The Conditioning Interpretation

The split vs. unified distinction maps to conditioning:

**Split (EDT-style):** E[U | s obtains and I take action a]

**Unified (UDT-style):** E[U | my policy maps s to a]

The difference:
- Split conditions on being-in-situation-s as a separate fact
- Unified conditions on having-a-policy-that-says-a-for-s

For a unified agent, "being in situation s" isn't separate from "having a policy." The agent's policy IS its global behavior, of which the current situation is one instance.

## When Do Split and Unified Agree?

**Theorem.** Split and unified reasoning agree when there's no cross-situation dependence.

**Proof:** If U(s, a) depends only on s and a (not on actions at other situations), then:

max_π Σ_s P(s) · U(s, π(s)) = Σ_s P(s) · max_a U(s, a)

The global optimization decomposes into independent local optimizations.

**Interpretation:** When situations are truly independent, treating them separately is fine. The split model is a special case of the unified model when cross-situation dependence is absent.

## Decision-Determination Revisited

**Decision-determination** is the condition that makes cross-situation dependence "fair":

**Definition.** A problem is **decision-determined** if:
1. The environment responds to policies (which actions are taken in each situation)
2. Not to the internal mechanism (how the policy is computed)

Under decision-determination, cross-situation dependence arises from how the environment responds to behavior, not from discrimination based on internals.

**Claim:** In decision-determined problems, unified reasoning is unambiguously correct for unified agents.

## Summary: The Formal Core

1. **Multi-situation problems** involve an agent facing multiple situations
2. **Split model:** Optimize each situation independently → EDT-style reasoning
3. **Unified model:** Optimize the whole policy → UDT-style reasoning
4. **The models differ** when there's cross-situation dependence
5. **Unity (being a single agent)** = treating situations as parts of one entity's behavior
6. **Unified agents in problems with cross-situation dependence** must reason updatelessly
7. **This is the representation theorem:** single agent + cross-situation structure → UDT

## What's Non-Trivial

The representation theorem is:
- **Trivial** if we define "single agent" as "unified optimizer" (circular)
- **Non-trivial** if we motivate "single agent" independently and derive unification

The independent motivation comes from:
- Agency as modeling (the agent is ONE entity we're predicting)
- Functional identity (same algorithm across instances)
- Parsimony (simpler model than split)
- Burden of proof (splitting requires justification)

These motivations are *prior* to the decision theory debate. We'd accept them even before considering Newcomb problems.

---

## Open Questions

1. **Observations vs situations:** How does observation structure (imperfect information) fit in?

2. **Ties:** What if multiple policies are equally optimal?

3. **Logical uncertainty:** What if the agent doesn't know its own policy?

4. **Approximate unity:** What if the agent is "mostly" unified but not perfectly?

5. **Causal structure:** How does this relate to causal vs. evidential decision theory debates?


---
# === FILE: agency-via-endorsement.md ===
---

# Agency via Endorsement: A Condensation-Theoretic Treatment

## Setup: Bipartite Agent-Environment Model

We work with a probability space (Ω, P). We have two primary random variables:

- **A** : Ω → R_A — the "agent" (what the agent controls/is)
- **E** : Ω → R_E — the "environment" (everything external)

Under condensation assumptions, we can reify the information-theoretic relationships:

### Condensation Variables

**Boundary (mutual information):**
- **B = A ∨ E** — the common information, finest variable that's a function of both A and E
- H(B) = I(A; E)
- B is a subvariable of both A and E

**Policy (agent's residual):**
- **Π** — the condensation variable for H(A | E)
- Satisfies: H(A | Π, E) = 0, and Π is independent of E in support
- A factors as (B, Π) where B = A ∨ E
- Intuitively: Π is what the agent "brings to the table" beyond what's shared with environment

**Environment's residual:**
- **Ξ** — the condensation variable for H(E | A)
- Satisfies: H(E | Ξ, A) = 0, and Ξ is independent of A in support
- E factors as (B, Ξ)

### The Factorization Picture

```
        A = (B, Π)          E = (B, Ξ)
            ↓                   ↓
            B ←───────→ B
       (boundary)        (boundary)
```

The world Ω factors as (Π, B, Ξ) where:
- Π, B, Ξ are mutually independent in support
- A = (B, Π) and E = (B, Ξ)
- The boundary B is the "interface" — the shared information

---

## Endorsement-Based Agency

Following "Meaning & Agency", we define agency through the lens of an **observer** (Alice) attributing agency to a **system** (Bob).

### The Observer's Perspective

Alice has:
- Beliefs P₁ over the sample space Ω
- A choice function C₁ (how Alice would optimize)
- Access to some variables as "observable" — she can condition on their values

Alice observes the system and asks: "Is this system optimizing something?"

### Belief Endorsement (Simplest Case)

**Definition (Belief Endorsement):** P₁ belief-endorses Π with respect to target X if:

$$P_1(X \mid \Pi = \pi) = f_\pi(X)$$

where f_π is the "belief about X" encoded by policy π, and Alice adopts this belief upon learning the policy.

More precisely: if we think of each π ∈ R_Π as encoding a belief about X, then P₁ endorses Π if conditioning on Π = π gives Alice the belief that π encodes.

This is relevant when the "optimization target" is epistemic — the system is trying to have accurate beliefs.

---

## Selection Endorsement

**Setup:**
- Let V be a random variable we interpret as the system's "output" or "choice"
- Let U_sel : R_V → ℝ be a **pure utility function** (depends only on the choice, not the world)

**Definition (Selection Endorsement):** Alice selection-endorses the system (with policy Π) as optimizing U_sel if:

$$C^1_{U_{sel}, P_1}(R_V \mid \Pi = \pi) = v_\pi$$

where v_π is the value of V determined by policy π.

In words: If Alice were trying to optimize U_sel, and she learned the system's policy is π, she would choose the same action that π chooses.

### Formal Expansion

Let C be argmax for simplicity. Then selection endorsement means:

$$\arg\max_{v \in R_V} E_{P_1}[U_{sel}(v) \mid \Pi = \pi] = v_\pi$$

But U_sel(v) doesn't depend on ω, so:

$$\arg\max_{v \in R_V} U_{sel}(v) = v_\pi$$

This is trivial unless we interpret it correctly: the point is that **v_π must be optimal**, i.e., the system's policy always picks U_sel-optimal actions.

### Selection Endorsement with Observation Structure

More interesting: suppose the system observes O (a subvariable of E) and chooses action Act. The policy is π : R_O → R_{Act}.

**Definition (Selection Endorsement with Observations):** Alice selection-endorses (Π, O, Act) as optimizing U_sel : R_{Act} → ℝ if for all o ∈ R_O:

$$\arg\max_{a \in R_{Act}} U_{sel}(a) = \pi(o)$$

This says: regardless of observation, the policy picks the U_sel-optimal action.

This is only non-trivial if U_sel depends on o — but then it's not a pure function of Act. So pure selection endorsement is essentially: "the system always outputs the same optimal thing."

---

## Control Endorsement

**Setup:**
- Let V be the system's output
- Let U_ctrl : Ω × R_V → ℝ be an **impure utility function** (depends on world and choice)

Or equivalently, since we're conditioning on policy:
- U_ctrl : R_Ξ × R_B × R_V → ℝ — utility depends on environment's residual, boundary, and choice

**Definition (Control Endorsement):** Alice control-endorses the system (with policy Π) as optimizing U_ctrl if:

$$C^1_{U_{ctrl}, P_1}(R_V \mid \Pi = \pi) = v_\pi$$

where v_π is the value of V determined by policy π (as a function of boundary B).

### Formal Expansion with Condensation Structure

The system's policy Π determines a function π : R_B → R_V (mapping boundary values to outputs).

Control endorsement means: for each π,

$$\arg\max_{v : R_B \to R_V} E_{P_1}\left[\sum_{b \in R_B} \mathbf{1}[B=b] \cdot U_{ctrl}(\Xi, b, v(b)) \mid \Pi = \pi\right] = \pi$$

Since Π is independent of (B, Ξ) in support, conditioning on Π = π doesn't change the distribution of (B, Ξ). So:

$$\arg\max_{v : R_B \to R_V} E_{P_1}\left[U_{ctrl}(\Xi, B, v(B))\right] = \pi$$

This is interesting! It says: **the policy π that the system implements is exactly the policy Alice would choose** if she were optimizing U_ctrl.

### Pointwise Control Endorsement

We can also state this pointwise over boundary values:

$$\arg\max_{a \in R_V} E_{P_1}\left[U_{ctrl}(\Xi, b, a) \mid B = b\right] = \pi(b) \quad \forall b \in R_B$$

This is: at each boundary value b, the policy's action π(b) is what Alice would choose.

---

## The UDT Connection

In the UDT representation theorem, we have:
- Observations O (part of boundary B in our framing)
- Actions Act (what the policy chooses)
- Global utility U : Ω → ℝ

The UDT formula says:
$$\pi(o) = \arg\max_a E[U \mid \Pi(o) = a]$$

### Translating to Endorsement Language

Let Alice's beliefs P₁ be the agent's prior. Let U_ctrl(ω, a) = U(ω) when the action at observation o is a.

Then UDT says: for all observations o,
$$\arg\max_a E_{P_1}[U \mid \Pi(o) = a] = \pi(o)$$

**Claim:** An agent following UDT is control-endorsed by its own prior.

**Why:** The UDT agent, at each observation, chooses the action that maximizes expected utility from the prior's perspective. This is exactly what control endorsement requires: Alice (= the prior) would make the same choice.

---

## Selection vs Control: The Key Distinction

### Selection (Pure U)

- U_sel : R_V → ℝ depends only on the output
- The optimal output is fixed regardless of world-state
- Example: "Output the largest number" — the system just needs to output ∞ (or max of range)
- **No beliefs required** — the system doesn't need to know anything about the world

### Control (Impure U)

- U_ctrl : Ω × R_V → ℝ depends on world and output
- The optimal output varies with world-state
- Example: "Output a prediction of X" — the system needs beliefs about X
- **Beliefs required** — the system must track world-state to optimize

### The Condensation Perspective

In selection: the policy Π can be trivial (constant function) and still be endorsed.

In control: the policy Π must **encode information about E** to be endorsed. Specifically, the policy must encode enough to compute the optimal action at each boundary state.

This suggests: **control endorsement implies the policy has structure** — it's not arbitrary, but reflects optimization under uncertainty.

---

## Endorsement with Explicit Boundary Structure

Let's be fully explicit with our condensation variables.

**Setup:**
- (Ω, P) probability space
- A, E random variables with A ∨ E = B (boundary)
- A factors as (Π, B) with Π the policy (condensation variable for H(A|E))
- E factors as (Ξ, B) with Ξ the environment's residual

**The agent's "choice" is:** given B = b, output some value. The policy Π determines this: Π = π means "use function π : R_B → R_A".

**Utility:** U : Ω → ℝ, which we can write as U : R_Π × R_B × R_Ξ → ℝ.

**Definition (Full Control Endorsement):** Observer with beliefs P₁ control-endorses Π as optimizing U if:

$$\forall \pi \in R_\Pi : \quad \pi = \arg\max_{f : R_B \to R_A} E_{P_1}[U(f, B, \Xi) \mid \Pi = \pi]$$

Under independence (Π ⊥ (B, Ξ)):

$$\forall \pi \in R_\Pi : \quad \pi = \arg\max_{f : R_B \to R_A} E_{P_1}[U(f, B, \Xi)]$$

This means: **every policy in the support is optimal**. The distribution over policies P₁(Π = π) can have any shape, but each π in the support must be an optimizer.

---

## Conditional Endorsement and Levels of Trust

Following "Meaning & Agency", we can partially order systems by how much they're endorsed.

**Definition (Conditional Control Endorsement):** P₁ endorses Π₂ given Π₁ (both as optimizing U) if:

$$C^1_{U, P_1}(R_V \mid \Pi_1 = \pi_1, \Pi_2 = \pi_2) = v_{\pi_2}$$

Alice still endorses Π₂'s choice even after learning Π₁'s choice.

If Alice endorses Π₂ given Π₁ but not vice versa, she trusts Π₂ more.

---

## Summary: The Definitions

Let (Ω, P) be a probability space with A, E, B = A ∨ E, and Π the condensation variable for H(A|E).

**Selection Endorsement:** P₁ selection-endorses Π as optimizing U_sel : R_A → ℝ if every π in support(Π) satisfies:
$$\pi(b) \in \arg\max_a U_{sel}(a) \quad \forall b$$

**Control Endorsement:** P₁ control-endorses Π as optimizing U_ctrl : Ω → ℝ if every π in support(Π) satisfies:
$$\pi = \arg\max_f E_{P_1}[U_{ctrl}(f(B), B, \Xi)]$$

**UDT as Self-Endorsement:** An agent using UDT with prior P is control-endorsed by P as optimizing its utility U:
$$\pi^{UDT}(b) = \arg\max_a E_P[U \mid \text{action at } b \text{ is } a]$$

The representation theorem goal: show that under appropriate conditions (decision-determination, condensation, etc.), **any control-endorsed policy must satisfy the UDT formula**.


---
# === FILE: fair-environment-theorem.md ===
---

# Toward a Real Theorem: Fair Environments

## The Key Question

**When does decision-determination hold?**

If we can characterize this in condensation terms, we get a real theorem.

---

## Decision-Determination Revisited

**Decision-determination says:**
The environment responds to your policy π, not to your internal mechanism.

**Formally:**
For any two mechanisms M₁, M₂ that implement the same policy π:
  U(M₁) = U(M₂)

**In other words:**
Utility is a function of the extensional behavior, not the intensional procedure.

---

## When Should This Hold?

### Case 1: No Predictors

If the environment has no way to predict your behavior, it can't respond to your policy at all. But it also can't discriminate based on mechanism.

**Result:** Decision-determination holds trivially (environment doesn't condition on you at all).

**But this means:** No cross-situation dependence. EDT and UDT agree. Boring case.

### Case 2: Perfect Predictors

If the environment perfectly predicts your behavior, it responds to your policy.

**Key question:** Does it respond to ONLY your policy, or also your mechanism?

**"Fair" predictor:** Responds only to input-output behavior (the policy).

**"Unfair" predictor:** Looks inside your implementation.

### Case 3: Imperfect Predictors

Realistic predictors are imperfect. They have some model of you.

**Question:** Under what conditions is this model effectively "just the policy"?

---

## A Condensation Characterization of Fair Environments

### Setup

- Agent has mechanism M that implements policy π = behavior(M)
- Environment has model E of agent
- Environment responds based on E(M)

### The Fairness Condition (attempt 1)

**The environment's model E is "fair" if:**
E(M) depends only on behavior(M), not on M directly.

Formally: behavior(M₁) = behavior(M₂) → E(M₁) = E(M₂)

**This is just decision-determination restated.** Not a new characterization.

### The Fairness Condition (attempt 2)

**Using condensation:** The environment's model E should be a good condensation of the agent's observable behavior.

If E is trying to predict the agent, and the policy π is a good condensation of behavior, then a good E should recover π.

**Claim:** If E is a good predictor (accurate, minimal), and π is a good condensation of agent behavior, then E ≈ π (up to sufficient statistics).

**Proof sketch:**
- E is accurate → E captures predictive information about behavior
- π is a good condensation → π is the minimal predictor of behavior
- Therefore E contains π (or is equivalent to π)

**Consequence:** A good predictor responds to the policy.

---

## The Potential Theorem

**Theorem (sketch):**

Let:
- Agent behavior B be observable
- Policy π be a perfect condensation of B
- Predictor E be optimal (accurate and minimal)

Then:
- E depends only on π (E is a function of π)
- Any response to E is a response to π
- Decision-determination holds

**This would be a real condensation result!**

---

## Checking the Logic

### Premise 1: Policy is a perfect condensation of behavior

This means:
- H(Bᵢ | π, Oᵢ) = 0 (determination)
- H(π | B) ≈ 0 (recoverability)

In other words: π and B are informationally equivalent (given observation distribution).

### Premise 2: Predictor is optimal

This means:
- E has minimal complexity for its predictive accuracy
- E is a sufficient statistic for predicting B

### Conclusion: Predictor depends only on policy

**Argument:**
1. An optimal predictor extracts the minimal sufficient statistic for prediction
2. The policy π is a sufficient statistic for behavior (given observations)
3. Therefore, an optimal predictor E is a function of π (or equivalent)

**The key step:** Why is π THE minimal sufficient statistic?

**Answer:** By the recoverability condition, π ≈ f(B) for some f. And by determination, B ≈ g(π, O). So π and B are informationally equivalent given O.

If the predictor is predicting B, it needs to recover the information in B. This information is captured by π (given O).

---

## Making This Rigorous

### Definition: Predictive Equivalence

Two latents L₁, L₂ are **predictively equivalent** for observables X if:
  I(L₁ ; X) = I(L₂ ; X) and both are sufficient statistics

### Lemma: Condensations are Predictively Equivalent

If L₁ and L₂ are both perfect condensations of X, they are predictively equivalent.

### Theorem: Optimal Predictors Agree with Condensations

If:
- π is a perfect condensation of behavior B
- E is an optimal (minimal sufficient) predictor of B

Then:
- E is predictively equivalent to π
- Any function of E is a function of π

### Corollary: Decision-Determination from Optimality

If the environment uses an optimal predictor, decision-determination holds.

---

## What This Proves

**The theorem says:**
Optimal predictors respond to policies, not mechanisms.

**Why?**
Because optimal prediction extracts the policy (the sufficient statistic).

**Therefore:**
In environments with optimal predictors, UDT is correct.

---

## Caveats and Limitations

### Caveat 1: Optimal Predictors Are Idealized

Real predictors aren't optimal. They might:
- Use suboptimal features (mechanism-dependent)
- Have limited computation
- Make systematic errors

**Response:** The theorem provides an ideal. Deviations from optimality might break decision-determination.

### Caveat 2: The Observation Distribution Matters

Recoverability depends on the observation distribution having sufficient coverage.

If you only ever see observation o*, the predictor can only learn π(o*).

**Response:** The theorem assumes sufficient observation diversity.

### Caveat 3: This Doesn't Cover All "Fair" Environments

Some environments might be "fair" for non-condensation reasons:
- Normative constraints (it's wrong to discriminate on mechanism)
- Physical constraints (can't observe mechanism)

**Response:** The theorem covers one important case, not all cases.

---

## Summary: A Real Theorem

**Theorem (Informal):**
If the policy is a good condensation of behavior, and the environment uses an optimal predictor, then decision-determination holds.

**Structure:**
- Premise 1: Agency condensation conditions
- Premise 2: Environment optimality
- Conclusion: Decision-determination

**Combined with the representation theorem:**
- Premises 1 & 2 → decision-determination
- Decision-determination + rationality → UDT formula

**This IS a condensation-to-UDT theorem!**

---

## Open Questions

1. **Formalize "optimal predictor"** in information-theoretic terms
2. **Prove the lemma** about condensations being predictively equivalent
3. **Extend to approximate condensation** for realistic settings
4. **Connect to Diffractor's framework** for computational aspects

---

## What This Means for the Presentation

**Original claim:** "Agency as condensation implies UDT"

**Refined claim:** "Agency condensation + optimal prediction implies UDT"

**The added premise (optimal prediction) is:**
- Plausible for sophisticated predictors
- Connects prediction quality to decision theory correctness
- Provides a criterion for when UDT applies


---
# === FILE: agency-as-condensation.md ===
---

# Agency as Condensation: Formalizing the Connection

## Goal

Make precise the claim that agency attribution is a special case of latent variable modeling, and that the UDT representation theorem is analogous to condensation's correspondence theorem.

---

## The Core Insight: Policy as Latent Variable

**Key reframing:** The policy isn't just a function π : O → A that we optimize over. It's a **random variable Π** — a latent that captures which function relates observations to actions.

### Information-Theoretic Characterization

Given random variables A (actions) and B (observations):

- **H(A | B)** — what remains uncertain about A given B
- **H(B | A)** — what remains uncertain about B given A
- **I(A; B)** — mutual information, what's shared

The **policy Π** is the random variable such that:

```
H(A | Π, B) = 0
```

That is: once we know both the policy Π and the observation B, the action A is completely determined.

But in general:
```
H(A | B) > 0
```

The policy is the "missing information" — what you need to know, beyond the observation, to predict the action.

### Different Worlds, Different Policies

Different worlds ω ∈ Ω might have different policies:
- In world ω₁, Π(ω₁) = π₁ (cooperate strategy)
- In world ω₂, Π(ω₂) = π₂ (defect strategy)

The random variable Π assigns each world its policy.

---

## Review: Condensation Setup

### Random Variable Models

A **random variable model** M = (Ω, (X_i)_{i∈I}) consists of:
- A probability space Ω
- A finite family of observable random variables X_i

### Latent Variable Models

A **latent variable model** L for M consists of:
- An expanded probability space Λ with map π: Λ → Ω
- Latent random variables (Y_j)_{j∈J} on Λ
- A **contribution relation** ▷ ⊆ J × 𝒫(I)

**Condition:** Each X_i is (almost everywhere) a function of the Y_j that contribute to it.

### The Correspondence Theorem

**Perfect condensation** (roughly): The latent variables efficiently summarize the observables.

**Theorem (informal):** If L₁ and L₂ are both perfect condensations of M, then their latent variables correspond.

---

## Agency as Latent Variable Model

### The Observable Variables

When attributing agency to system S:

Let I = {situations the system might face}

For each i ∈ I, let X_i = (O_i, A_i) where:
- O_i = observation in situation i
- A_i = action in situation i

The **random variable model** M = (Ω, (X_i)_{i∈I}) represents all possible behaviors of S across situations.

### The Policy as Central Latent

**The policy Π is a random variable such that:**

For all situations i:
```
H(A_i | Π, O_i) = 0
```

This says: given the policy and the observation, the action is determined.

**Key structural property:** Π contributes to ALL situations — it's a single latent explaining all behavior.

### The Agency Latent Variable Model

**L_agency consists of:**
- Policy random variable Π (values are functions O → A)
- Contribution: Π ▷ I (policy contributes to all situations)
- Determination: H(A_i | Π, O_i) = 0 for all i

**This is the "single latent explains many observables" structure** that condensation identifies as special.

---

## Condensation Conditions for Agency

### Condition 1: Determination

**The policy + observation determines the action.**

```
H(A_i | Π, O_i) = 0
```

For deterministic policies, this is automatic: if Π = π means "use function π," then A_i = π(O_i).

### Condition 2: Recoverability (Redundancy)

**The policy is recoverable from behavior.**

```
H(Π | (O_i, A_i)_{i∈I}) ≈ 0
```

Or with redundancy: for any i₀,
```
H(Π | (O_i, A_i)_{i ≠ i₀}) ≈ 0
```

**Meaning:** The policy isn't hidden — it's manifest in behavior. If we observe enough situations, we can reconstruct which policy is in use.

### Condition 3: Unity

**There is ONE policy across all situations.**

Not: separate policies Π_i for each situation
But: a single Π that determines behavior everywhere

This is the claim that there's a unified agent, not just coincidentally correlated behaviors.

### Condition 4: Decision-Determination

**The environment responds to the policy, not the mechanism.**

Let D be the "dynamics" or "mechanism" — the internal implementation details.

Decision-determination:
```
I(E ; D | Π) = 0
```

The environment E is independent of the mechanism D given the policy Π.

---

## The Representation Theorem

### Setup

- Unified agency: single policy Π with H(A_i | Π, O_i) = 0 for all i
- Recoverability: H(Π | behavior) ≈ 0
- Decision-determination: I(E ; D | Π) = 0
- Rationality: agent maximizes E[U]

### Conclusion

The optimal policy satisfies the UDT formula:

```
π(o) = argmax_a E[U | Π(o) = a]
```

### Why This Follows

1. **Unity** means there's ONE Π determining all actions
2. **Decision-determination** means U depends on Π (via E), not on D
3. **Rationality** means we maximize E[U] over policies
4. **The formula** is just: at each o, choose the action that makes Π globally optimal

The condensation structure (single latent contributing to all observables) plus rationality forces updateless reasoning.

---

## Connection to Communication & Trust Framework

In the IBE framework from Communication & Trust:

- **D_B** (boundary dynamic) is a random variable encoding the decision mechanism
- **Π** (policy) is a coarsening of D_B — it forgets implementation details
- **Π†** (effective policy) is what actually gets implemented
- **Π*** (chosen policy) is what would be implemented without modification

**The relationship:**
- D_B is like "full state"
- Π is the latent we extract
- H(A | Π, O) = 0 is the determination condition
- Decision-determination says E responds to Π, not to D_B

---

## Cross-Situation Dependence

### Why It Matters

When policy Π determines actions in multiple situations:
- Changes in Π affect actions everywhere
- You can't optimize situation i in isolation
- The policy structure induces correlations across situations

**Cross-situation dependence = the condensation structure applied to agency.**

### The Key Insight

Updateless reasoning follows because Π is a SINGLE latent contributing to ALL situations.

Optimizing A_i at observation o_i in isolation ignores that A_i is determined by Π, which also determines A_j at o_j, which affects U.

To optimize properly, you must optimize Π as a whole.

---

## The Information-Theoretic Formulation

### Agency Condensation Conditions

1. **Determination:** H(A_i | Π, O_i) = 0 for all i
2. **Recoverability:** H(Π | (O_i, A_i)_{i∈I}) ≈ 0
3. **Unity:** Single Π contributes to all situations
4. **Decision-determination:** I(U ; D | Π) = 0

### The Theorem

**Given** conditions 1-4 and rationality (maximize E[U]):

**Then** optimal Π satisfies: Π(o) = argmax_a E[U | Π(o) = a]

---

## Open Questions

### Technical

1. What's the exact relationship between condensation's correspondence theorem and the agency representation theorem?
2. How do approximate versions work?
3. Can we state this purely information-theoretically without assuming deterministic policies?

### Conceptual

1. How does the "endorsement" framing from Meaning & Agency connect to these condensation conditions?
2. Is recoverability actually necessary, or just determination + unity + decision-determination?
3. What happens when condensation conditions fail partially?

### For the Full Stack

1. How does Diffractor's plannable/unplanned distinction map onto this?
2. Can UDT1.01's optimality be stated as a condensation result?
3. What are the conditions for multi-agent settings?

---

## Summary

**Agency attribution = introducing a latent variable Π with specific structure:**
- Π is the "missing information" such that H(A | Π, O) = 0
- Π contributes to all situations (unity)
- Π is recoverable from behavior

**The representation theorem = condensation applied to agency:**
- The structure constrains the content
- Optimizing over Π (not local actions) is forced by the structure
- This IS updateless reasoning


---
# === FILE: grand-synthesis.md ===
---

# The Grand Synthesis: From Condensation to UDT

## The Vision

A unified theory with four layers:

1. **Condensation:** A theory of concepts built on probability/information theory
2. **Agency as Abstraction:** A rigorous intentional stance - when to recognize agents
3. **UDT Representation Theorem:** What follows from agency attribution
4. **Computational Realization:** How this works under logical uncertainty

Each layer builds on the one below.

---

## Layer 1: Condensation (Sam's Theory)

### The Core Idea

**Observable variables** X_i are what we can directly measure/perceive.

**Latent variables** Y_j are concepts we introduce to *organize* our understanding of the observables.

**Contribution relation** j ▷ i says which latent Y_j helps explain which observable X_i.

### The Key Theorem

Under certain information-theoretic conditions ("perfect condensation" or approximations thereof), different latent variable models for the same observables must **correspond**.

**Roughly:** If two agents both have good latent variable models for the same phenomena, their concepts must line up - Y_A in one model corresponds to Z_A in the other.

### What This Means

**Intersubjectivity:** Concepts aren't arbitrary. If you're carving reality well, your concepts will correspond to anyone else who's also carving well.

**Objectivity of abstraction:** Latent variables aren't "just in the map." There's a fact of the matter about which latent structures are appropriate.

**Information-theoretic foundation:** All of this is grounded in entropy and mutual information, not in metaphysics.

---

## Layer 2: Agency as Abstraction

### The Core Idea

**Agency attribution = introducing a particular kind of latent variable structure.**

When we say "X is an agent with utility U," we're not making a metaphysical claim. We're introducing latent variables:
- The agent's **observations** O (what information it receives)
- The agent's **actions** A (what outputs it produces)
- The agent's **policy** π: O → A (the mapping from observations to actions)
- The agent's **utility** U (what it's optimizing)

### The I/B/E Decomposition as Latent Structure

The Communication & Trust framework's I/B/E decomposition is a specific latent variable model:

- **I** (Interior): Latent variables for persistent state
- **B** (Boundary): Latent variables for the decision procedure
- **E** (Environment): Everything outside the agent

The **observation/action** variables mediate information flow.

The **policy** is a latent variable that summarizes how B responds to O.

### When Is Agency Attribution Appropriate?

By analogy with condensation:

**Agency is appropriate when the agent latent structure "condenses" the observables well.**

Formally: The policy π should satisfy information-theoretic conditions analogous to perfect condensation - it should efficiently summarize the agent's behavior.

**The intentional stance is justified** when:
1. The agent-concept reduces entropy (predictive power)
2. The structure is intersubjective (other observers would attribute similar agency)
3. The contribution relations are natural (clean factorization)

### The "Single Agent" Condition

**One agent vs many:** When we attribute the *same* agency across situations, we're positing a *single* latent structure.

This is like positing a single latent variable Y_I that explains multiple observables X_i, rather than separate latents for each.

**Unity = shared latent structure across instances.**

---

## Layer 3: The UDT Representation Theorem

### From Condensation Conditions to UDT

**Condensation says:** If you have a good latent variable model, it corresponds to any other good model.

**For agency, this becomes:** If you have a unified agent model (single policy explaining multiple situations), it has determinate implications.

### The Theorem Structure

**Axioms (the "agency condensation conditions"):**

1. **Unity:** We model a SINGLE agent with policy π across situations
2. **Contribution:** The policy explains behavior at each observation
3. **Decision-Determination:** Environment responds to policy, not internals
4. **Rationality:** The agent maximizes expected utility

**Theorem:** Under these axioms, the agent reasons updatelessly:

At each observation o: π(o) = argmax_a E[U | π(o) = a]

### Why This Is Like Condensation

In condensation: Given appropriate conditions, latent variables Y_A must equal functions of Z_⊇A (correspondence).

In UDT: Given appropriate conditions, local actions must be parts of globally optimal policy (updatelessness).

**Both are "the structure forces this conclusion" results.**

The structure of unified agency *forces* policy-centric reasoning, just as the structure of good latent models *forces* correspondence.

### The "Cross-Situation Dependence" Connection

In condensation: Latent Y_j contributes to multiple observables X_i.

In agency: Policy π determines actions at multiple observations o.

**Cross-situation dependence** = the agent's policy affects utility across situations, just as a latent variable affects multiple observables.

When there's cross-situation dependence, you can't reason about situations independently - you must reason about the whole policy/latent structure.

---

## Layer 4: Computational Realization

### The Problem

Condensation and the representation theorem assume we *know* the latent structure. But:
- We don't know our own policy (logical uncertainty)
- We can't plan for everything (computational limits)
- Our beliefs change in ways not forced by evidence (radical probabilism)

### Diffractor's Contribution

**Plannable vs unplanned observations:**
- Plannable h: What we can write a lookup-table policy for
- Unplanned S: Epistemic states that affect action but can't be pre-planned

**UDT1.01:** An algorithm that handles unplanned observations optimally.

**Key result:** UDT1.01 is universally locally optimal - for any situation and any competing algorithm, adding more UDT1.01 improves expected utility.

### The Multi-Agent Interpretation

Under logical uncertainty, "instances" are genuinely different:
- Instance (h, S) has observation h and epistemic state S
- Different S values = different "minds"

**Coordination happens through:**
1. Shared algorithm (all instances run UDT1.01)
2. Conservation of expected gain (optimize for prior-weighted expectation)
3. The "contract" (agreement on principles, not outputs)

### Radical Probabilism Fits

**Radical updates** = changes of mind not forced by evidence.

In Diffractor's framework: Your epistemic state S can change through computation, not just observation.

**The contract handles this:** You agree to follow UDT1.01 regardless of how your beliefs change. The algorithm is stable under radical updating.

### Connection Back to Condensation

**Different epistemic states S are like different latent variable models.**

If different instances (with different S) are both "good" (following UDT1.01), their actions will correspond - they'll coordinate.

**This is intersubjectivity at the computational level:** Even with different beliefs, agents following the right algorithm will converge on coordinated behavior.

---

## The Full Picture

### The Stack

```
Layer 4: Computational Realization
         (Diffractor's UDT1.01, logical uncertainty, radical probabilism)
              ↓ implements
Layer 3: UDT Representation Theorem
         (Agency axioms → updateless reasoning)
              ↓ is an instance of
Layer 2: Agency as Abstraction
         (I/B/E decomposition, policy as latent variable)
              ↓ is a special case of
Layer 1: Condensation
         (Latent variable models, correspondence theorems)
```

### How the Layers Connect

**1 → 2:** Agency attribution is introducing a particular latent variable structure (I/B/E, policy, utility). The conditions for "good" agency attribution are instances of condensation conditions.

**2 → 3:** If the agency structure satisfies unity + decision-determination + rationality, the representation theorem applies. Updateless reasoning follows.

**3 → 4:** The representation theorem tells us *what* to do (condition on policy). Diffractor's work tells us *how* to do it computationally (UDT1.01). Radical probabilism tells us how to handle epistemic changes.

### The Intersubjectivity Thread

**Condensation:** Different good latent models correspond.

**Agency:** Different good agency attributions agree.

**UDT:** Different instances with the same algorithm coordinate.

**Radical probabilism:** Different epistemic states following the same principles converge.

**Throughout:** "Doing it right" leads to agreement/correspondence/coordination.

---

## Open Questions

### For the Condensation → Agency Connection

1. What exactly are the condensation conditions for agency attribution?
2. How does the contribution relation ▷ map to the observation/action structure?
3. Can we prove a "correspondence theorem for agency" - different good agency attributions must agree?

### For the Agency → UDT Connection

1. How tight is the analogy between condensation correspondence and updateless reasoning?
2. Can we derive the UDT formula directly from information-theoretic conditions?
3. What's the role of "perfect" vs "approximate" condensation in agency?

### For the UDT → Computation Connection

1. How does UDT1.01 relate to the representation theorem axioms?
2. What are the condensation conditions for Diffractor's framework?
3. Can we unify the C&T and Diffractor frameworks using condensation?

### For the Full Stack

1. Is there a single theorem that connects all four layers?
2. What are the failure modes at each layer?
3. How do approximations propagate up the stack?

---

## Implications

### For AI Alignment

**Value learning:** If values are latent variables, condensation conditions tell us when value learning succeeds.

**Corrigibility:** Self-trust / non-interference follows from the representation theorem - agents satisfying the axioms don't want to modify themselves.

**Multi-agent coordination:** The stack explains how different AI systems can coordinate despite different internals.

### For Philosophy

**Intentional stance:** Dennett's intentional stance gets a rigorous foundation - agency attribution is justified when condensation conditions hold.

**Free will:** The "choice" an agent makes is the policy variable. This is a latent, not directly observable, but objectively constrained by condensation.

**Intersubjectivity:** Why different agents use similar concepts - condensation forces correspondence.

### For Decision Theory

**Why UDT:** Not just "it performs well" but "it's what agency attribution implies."

**The EDT/CDT/UDT debate:** These differ in how they treat the policy latent variable. UDT treats it as unified; others split it.

**Reflective stability:** Falls out of the representation theorem - optimal policies don't prefer self-modification.

---

## Summary

**The grand synthesis:**

1. **Condensation** tells us when concepts are "real" - when latent variable models must correspond.

2. **Agency** is a particular conceptual structure (I/B/E, policy, utility). It's "real" when condensation conditions hold.

3. **UDT** is what falls out when you take unified agency seriously. The representation theorem makes this precise.

4. **Computational realization** (UDT1.01, logical uncertainty, radical probabilism) tells us how to actually implement this.

**The core insight:** At every level, "doing it right" forces convergence/correspondence/coordination. This isn't just pragmatic - it's information-theoretically necessary.

**Agency isn't mysterious.** It's a well-structured latent variable model, and UDT is what that structure implies.


---
# === FILE: ibe-connection.md ===
---

# Connecting the Representation Theorem to the I/B/E Framework

## Goal

Show how the representation theorem framework relates to the I/B/E (Interior/Boundary/Environment) decomposition in the original paper. The key claim: the I/B/E framework is the mathematical structure we impose when attributing agency, and the representation theorem follows from taking this attribution seriously.

## The I/B/E Framework (Summary)

From the original paper:

**Three components:**
- **I (Interior):** Persistent state (memories, computations)
- **B (Boundary):** Decision procedure (input/output mapping)
- **E (Environment):** Everything external to the agent

**Information flow:**
- O = (Ȯ, Ö) : observations (internal + external)
- A = (Ȧ, Ä) : actions (internal + external)

**Dynamics:**
- D_I : how interior processes inputs
- D_B : the agent's decision rule
- D_E : how environment processes actions

**Policy:**
- Full policy π : O → A
- Effective policy Π† : what the agent actually implements
- Chosen policy Π* : what would be implemented without modification
- External policy Π̈ : how the agent appears externally

## Reinterpreting I/B/E as Modeling Choice

**Claim:** The I/B/E decomposition is not discovered in the world; it's imposed when we model something as an agent.

**The modeling step:**
1. We observe a system S
2. We decide to model S as an "agent with utility U"
3. We draw the I/B/E boundaries to make this modeling work
4. The boundaries define what counts as "observation," "action," "policy"

**This is agency attribution:**
- We're not claiming S "really is" an agent in some metaphysical sense
- We're claiming the teleological model (S optimizes U) predicts S's behavior well
- The I/B/E structure is the mathematical scaffolding for this model

## How the Representation Theorem Uses I/B/E

**The representation theorem's setup maps to I/B/E:**

| Representation Theorem | I/B/E Framework |
|------------------------|-----------------|
| Situations S | Observation space O |
| Actions A | Action space A |
| Policy π: S → A | Full policy π: O → A |
| Cross-situation dependence | Policy-dependent environment response |
| Decision-determination | E responds to Π, not to D_B's internals |

**Key correspondence:**
- "Situation" in the theorem = "observation" in I/B/E
- Both define the finest grain at which the agent can condition

## The Unity Axiom and Effective Policy

**In the representation theorem:** The unity axiom says the agent is a single optimizer with one policy.

**In I/B/E terms:** The agent has a single effective policy Π†. All "instances" (appearances at different observations) are outputs of this same policy.

**The connection:**
- Unity ↔ single Π†
- Split model ↔ treating each Π†(o) as a separate optimizer
- Unified model ↔ treating Π† as a coherent whole

## Decision-Determination in I/B/E Terms

**Definition from representation theorem:** The environment responds to policies, not to internal mechanisms.

**In I/B/E terms:** E's response depends on the external policy Π̈, not on D_B's internal structure.

**Formally:**
- Decision-determined: E = f(Π̈, D_E) for some f
- NOT decision-determined: E could depend on details of D_B beyond Π̈

**Example of non-decision-determined:**
- A predictor that can read the agent's source code
- The environment might discriminate based on *how* π is computed, not just *what* π is

**Example of decision-determined:**
- A predictor that can only observe the agent's behavior
- Environment responds to the policy (external behavior), not internals

## The Self-Trust Connection

**Paper's self-trust theorem:** In appropriate conditions, the agent doesn't prefer to self-modify.

**Representation theorem version:** A unified agent choosing an optimal policy has no reason to change its policy.

**The I/B/E connection:**

Self-modification = changing D_B (the boundary's decision rule)
Self-trust = D_B being stable (no preference to change it)

**Why unified agents have self-trust:**
1. The agent chooses policy π* maximizing E[U]
2. Self-modification would change π* to some π'
3. By optimality of π*, E[U | π*] ≥ E[U | π']
4. So no self-modification is preferred

**Condition needed:** The modification must be "fair" (decision-determined). If modification lets the agent achieve something π* couldn't (e.g., convince a source-code-reading predictor), this argument fails.

## The Paper's "Communicative Alternative" Condition

**The paper requires:** If modification opportunity exists, a communicative alternative should exist.

**Translation:** Any modification to D_B should be achievable by a policy choice in Π*.

**In representation theorem terms:** The policy space should include all relevant behavioral options. If "being a one-boxer" is achievable by modification, it should be achievable by policy choice.

**Why this matters:**
- Without this, modification might dominate policy choice
- The agent could prefer to self-modify, breaking self-trust
- The "fairness" (decision-determination) condition ensures policy choice is sufficient

## Instances as Applications of the Model

**Paper's definition:** "Instances" are the agent at different observations, factored by Ö (external observation).

**Reinterpretation:** Instances aren't ontologically separate. They're applications of the agency model to different contexts.

**The modeling story:**
1. We attribute agency to S (draw I/B/E boundaries)
2. We identify S's policy π: O → A
3. For each observation o, π(o) is what S does in that context
4. "Instance at o" = the application of the agency model where O = o

**Why this isn't UDT-biased:**
- Observation-based factoring is natural for any informationally-constrained agent
- The agent can't distinguish worlds with the same observation
- So the policy must be observation-level, not world-level
- This is a feature of limited information, not a UDT assumption

## The Representation Theorem as I/B/E Consequence

**Claim:** The representation theorem follows from taking I/B/E seriously.

**Argument:**
1. I/B/E decomposes the world into agent and environment
2. The boundary B implements a policy π: O → A
3. Unity means: there's one π, not separate optimizers for each o
4. Decision-determination means: E responds to π, not to B's internals
5. Rationality means: π is chosen to maximize E[U]
6. Conclusion: At each o, π(o) is part of the globally optimal policy
7. This is the UDT formula

**The theorem's content:** Steps 1-5 are what "coherent agency attribution" means. Step 6-7 are derivable consequences.

## Why the Paper's Framework is Compatible

The paper's formal structure is fully compatible with this interpretation:

| Paper's Framework | Representation Theorem Interpretation |
|-------------------|--------------------------------------|
| Defines I/B/E | Structural choice when attributing agency |
| Defines policies π | Agent's behavioral specification |
| Defines instances | Applications of the model |
| Proves self-trust | Consequence of unity + optimality |
| Communication | Enables coordination across instances |

**What the representation theorem adds:**
- Explicit argument that unity is the *default*
- Clearer connection to "what agency attribution means"
- Burden-of-proof argument against the split model
- Independent motivation for each axiom

## Remaining Work

1. **Formalize "unity" in I/B/E terms:** What does it mean mathematically for instances to be "the same agent"?

2. **Connect communication to functional identity:** How does the paper's communication structure relate to algorithmic identity across instances?

3. **Handle the semantic/side-channel distinction:** The paper distinguishes Ô (semantic) from Ǒ (side-channel). How does this affect the theorem?

4. **Address imperfect self-knowledge:** What if the agent doesn't know its own D_B?

## Summary

The I/B/E framework provides the mathematical structure for agency attribution. The representation theorem shows that:

1. Accepting I/B/E = accepting a single agent with a policy
2. Single agent + decision-determination + rationality = updateless reasoning
3. Updateless reasoning = self-trust (in fair problems)

The paper's results follow from taking the I/B/E decomposition seriously as a model of unified agency.


---
# === FILE: critical-analysis.md ===
---

# Critical Analysis: What Actually Works?

## The Goal

Ruthlessly examine the claims made so far. For each claim:
1. State it precisely
2. Identify problems/gaps
3. Attempt to prove or find counterexamples
4. Be honest about what we know

---

## Claim 1: Agency Attribution is a Latent Variable Model

### The Claim (Informal)
"When we attribute agency, we introduce latent variables: policy π, utility U, etc."

### Attempt at Precise Statement

**Setup:**
- Let Obs be a finite set of observations
- Let Act be a finite set of actions
- Let I be a set of "situations" (indices)
- For each i ∈ I, we observe (O_i, A_i) ∈ Obs × Act

**The Random Variable Model:**
- Ω = (Obs × Act)^I (space of all possible behavior patterns)
- P is a probability distribution on Ω
- X_i : Ω → Obs × Act is the projection onto situation i

**The Latent Variable Model:**
- Λ = (Obs → Act) (space of all policies)
- Q is a probability distribution on Λ (the "prior over policies")
- Y_π : Λ → (Obs → Act) is the identity (the policy random variable)
- Need a map π_map : Λ → Ω connecting policies to behaviors

### Problem 1: What is the map π_map?

A policy π ∈ Λ = (Obs → Act) determines actions GIVEN observations. But it doesn't determine which observations occur!

To get a distribution on Ω from a distribution on Λ, we need:
- A distribution over observations P(O_i)
- Then A_i = π(O_i) deterministically

**So the full model is:**
- P(O_i) : distribution over observations (from environment/situation structure)
- Q(π) : distribution over policies (the latent)
- A_i = π(O_i) : deterministic given policy and observation

**This means:** The latent variable model is really (Λ × Obs^I, Q × P_O), where:
- Λ contributes the policy
- Obs^I contributes the observations
- Actions are determined: A_i = π(O_i)

### Problem 2: What does "situation i" mean?

I've been vague about what I indexes. Options:
1. **Time:** i = timestep t. Then O_i, A_i are the observation/action at time t.
2. **Possible worlds:** i = world ω. Then O_i, A_i are what happens in world ω.
3. **Copies/instances:** i = instance. Then O_i, A_i are what that instance sees/does.

**For the representation theorem, we need:** Situations where the SAME policy applies.

If different situations have different policies, we have multiple agents, not one.

**Definition attempt:** The situations I are the set of observation-contexts where we're applying the same agency model.

### Problem 3: This only makes sense for deterministic policies

If the policy is stochastic (π : Obs → Δ(Act)), then:
- A_i is not determined by (π, O_i)
- We need: A_i ~ π(O_i)

This changes the information-theoretic conditions:
- H(A_i | π, O_i) = H(π(O_i)) (the entropy of the stochastic policy at O_i)
- Not zero unless policy is deterministic

**Resolution:** Focus on deterministic policies first. This is what UDT typically assumes anyway.

### Assessment

The claim "agency attribution is a latent variable model" is **partially valid** but requires:
1. Specifying the observation distribution separately
2. Clarifying what "situations" are
3. Assuming deterministic policies (or being careful about stochastic ones)

---

## Claim 2: The Condensation Conditions Imply Updateless Reasoning

### The Claim (Informal)
"If the agency latent model satisfies condensation conditions, updateless reasoning follows."

### What Are the Condensation Conditions?

From Sam's paper, **perfect condensation** (roughly) means:
- The latent variables "efficiently summarize" the observables
- Formally: certain entropy/information conditions hold

**For agency, I claimed:**
1. H(A_i | π, O_i) = 0 (determination)
2. H(π | (X_i)_{i∈I-{i₀}}) ≈ 0 (redundancy)

### Problem 4: These conditions don't imply updateless reasoning!

Let me check. Suppose:
- There's a prior Q over policies
- Each policy π determines behavior via A_i = π(O_i)
- The conditions hold

**Does it follow that the "rational" π satisfies π(o) = argmax_a E[U | π(o) = a]?**

**No!** The conditions are about information theory, not about optimality.

The conditions tell us:
- The policy determines behavior (condition 1)
- The policy is identifiable from behavior (condition 2)

But they don't say anything about:
- What makes a policy "rational"
- What the utility function is
- How the utility depends on the policy

### Problem 5: What's the actual theorem?

Let me try to state what should be true:

**Claim (revised):** If:
1. The agent has a single policy π (unity)
2. The utility U depends on the policy (cross-situation dependence)
3. The environment responds to the policy, not mechanism (decision-determination)
4. The agent maximizes E[U | π] (rationality)

Then: For each o, π(o) = argmax_a E[U | π(o) = a]

**Is this even non-trivial?**

If π maximizes E[U | π], and we can vary π(o) independently of π(o') for o' ≠ o, then:
- π(o) should be chosen to maximize contribution to E[U | π]
- This is just calculus: ∂/∂π(o) E[U | π] = 0 at optimum

**The question is:** Does this equal argmax_a E[U | π(o) = a]?

### Let's Actually Compute

**Setup:**
- Situations I, observations Obs, actions Act
- Prior P over (situations × observations): P(i, o)
- Policy π : Obs → Act
- Utility U : I × Obs × Act → ℝ (depends on situation, observation, action)

**Expected utility of a policy:**
E[U | π] = Σ_{i,o} P(i, o) · U(i, o, π(o))

**The derivative with respect to π(o₀):**

This is tricky because π(o₀) is discrete. Let's think of it as: what's the difference if we change π(o₀) from a to a'?

E[U | π with π(o₀)=a'] - E[U | π with π(o₀)=a]
= Σ_i P(i, o₀) · [U(i, o₀, a') - U(i, o₀, a)]

**Optimal π(o₀):**
π(o₀) = argmax_a Σ_i P(i, o₀) · U(i, o₀, a)
       = argmax_a E[U(i, o₀, a) | O = o₀]

### This Is NOT the UDT Formula!

The formula I derived is:
π(o) = argmax_a E[U | O = o, A = a]

But the UDT formula is:
π(o) = argmax_a E[U | π(o) = a]

**These are different!**

- E[U | O = o, A = a] conditions on the observation being o
- E[U | π(o) = a] conditions on the policy mapping o to a

### When Do They Differ?

**Case 1: No cross-situation dependence**

If U(i, o, a) depends only on the local (o, a), not on what happens elsewhere, then:
- E[U | π(o) = a] = E[U | O = o, A = a] (they're the same)
- UDT and EDT agree

**Case 2: Cross-situation dependence**

If U depends on the whole policy (e.g., through a predictor), then:
- E[U | π(o) = a] ≠ E[U | O = o, A = a] in general
- They condition on different things

### The Actual Content of UDT

**UDT says:** Condition on the policy fact π(o) = a, not on the local fact (O = o, A = a).

**When does this matter?** When the utility depends on the policy beyond just the local action.

**The representation theorem should say:**
If utility depends on the policy (cross-situation dependence), then the correct expected utility maximization is E[U | π], which gives the UDT formula.

### But Wait - This Is Almost Tautological!

If we define "rational" as "maximizes E[U | π]", then of course we get the UDT formula. We assumed it!

**The real question is:** Why should we maximize E[U | π] rather than E[U | O = o, A = a]?

This is where the "unity" and "latent structure" arguments come in.

---

## Claim 3: Unity Implies Policy-Centric Evaluation

### The Claim (Informal)
"If you model a SINGLE agent, you should evaluate policies, not individual actions."

### Attempt at Precise Statement

**Definition:** An agency model is **unified** if there's a single policy π that applies to all situations.

**Claim:** For unified agency, the correct evaluation is E[U | π], not E[U | O = o, A = a].

### Why Should This Be True?

**Argument 1: Consistency**

If we have a single π, then the actions at different observations are not independent choices - they're all determined by π.

So when we ask "what action should I take at o?", we're really asking "what should π(o) be?", which is a question about the policy.

**Argument 2: The Environment Responds to the Policy**

Under decision-determination, the environment responds to π, not to individual actions.

So the utility U(π) is really a function of the whole policy.

To maximize U(π), we need to optimize π, which means optimizing each π(o) as part of the whole.

**Argument 3: Information-Theoretic**

When I observe that I'm at observation o, what do I learn?
- I learn O = o (I'm in this situation)
- But I DON'T change my policy π

So conditioning should be: E[U | π, O = o] = E[U | π] (since π already determines what I do at o)

No wait, that's not quite right either...

### Actually, Let's Be Careful

**What does "conditioning on π(o) = a" mean?**

Option 1: I'm uncertain about my policy. Conditioning updates my beliefs about π.

Option 2: I'm choosing my policy. Conditioning is "what if I set π(o) = a".

**For UDT, it's Option 2:** We're choosing the policy, not learning about it.

So E[U | π(o) = a] means: "Expected utility if I commit to doing a at o."

**Compared to E[U | O = o, A = a]:**
This means: "Expected utility given that I observe o and do a."

**The difference:**
- UDT: The commitment to do a at o is known to the environment (via prediction)
- EDT: The environment may not "know" you'll do a at o; you're just calculating given that you end up doing a

### The Key Assumption: Decision-Determination

**Decision-determination:** The environment responds to your policy π, not to your mechanism.

**This means:** The environment "knows" your policy (via prediction or correlation).

**So:** When you commit to π(o) = a, the environment responds to this commitment.

**Therefore:** The correct calculation is E[U | π(o) = a], which accounts for how the environment responds to your commitment.

### The Theorem (More Precise)

**Setup:**
- Situations I, observations Obs, actions Act
- Policy space Π = Obs → Act
- Environment response: E(π) (depends on policy)
- Utility: U(E(π), π) (depends on environment and policy)

**Decision-determination:** U depends on π only through E(π), and E depends only on π (not on how π is computed).

**Rationality:** Choose π to maximize E[U | π] = U(E(π), π).

**Theorem:** The optimal policy satisfies:
For each o, π(o) = argmax_a [U(E(π'), π') where π'(o) = a and π'(o') = π(o') for o' ≠ o]

**If E is "smooth" in π (small changes in π cause small changes in E):**
Then this simplifies to: π(o) = argmax_a E[U | π(o) = a, π optimal elsewhere]

**For a coherent agent:** "π optimal elsewhere" is just π, so:
π(o) = argmax_a E[U | π(o) = a]

---

## Claim 4: This Is Analogous to Condensation Correspondence

### The Claim (Informal)
"The representation theorem is like condensation's correspondence theorem."

### Is This Analogy Precise?

**Condensation correspondence:** If L₁ and L₂ are both perfect condensations of M, their latents correspond.

**Agency "correspondence":** If we attribute unified agency correctly, we get UDT.

**The analogy:**
- Condensation: Structure → latents must correspond
- Agency: Structure → must evaluate policies

### Problem 6: This Isn't Really Correspondence

Condensation correspondence is about **different models agreeing**.

The representation theorem is about **what a single model implies**.

They're not the same structure!

**A better analogy might be:**
- Condensation: Given observables, what latents are appropriate?
- Agency: Given behavior, what decision rule is appropriate?

But even this is loose.

### What We Actually Have

**Condensation contribution:** The framework of latent variables and contribution relations.

**Agency application:** Viewing the policy as a latent that contributes to all behaviors.

**The connection:** Agency is a *special case* of latent variable modeling, not an *analogy* to correspondence.

---

## What Actually Needs to Be Proven

### Theorem 1: The UDT Formula Follows from Policy Optimization

**If:**
1. There's a single policy π : Obs → Act
2. Utility U : Π → ℝ is a function of the policy
3. We choose π to maximize U(π)

**Then:**
For each o, π(o) = argmax_a U(π_{a,o}) where π_{a,o}(o) = a and π_{a,o}(o') = π(o') for o' ≠ o.

**This is nearly tautological** - it's just saying "optimal π means each component is locally optimal."

The non-trivial content is: **Why should we maximize U(π)?**

### Theorem 2: Decision-Determination Implies Policy-Dependence

**If:**
1. The environment E responds to policy: E = f(π) for some f
2. Utility depends on environment: U = g(E)

**Then:**
U = g(f(π)) depends only on π.

**This is trivial** - just composition of functions.

### The Real Content: Why Is Decision-Determination Reasonable?

**Claim:** In "fair" problems, the environment can only respond to behavior (policy), not to internal mechanism.

**This is a substantive assumption** about the environment, not something we prove.

### Theorem 3: The Multi-Agent Interpretation

**If:**
1. There's logical uncertainty about the policy (we don't know π)
2. All "instances" (possible epistemic states) agree to run the same algorithm
3. The algorithm approximates policy optimization

**Then:**
The instances coordinate.

**This needs to be made precise.** What does "coordinate" mean formally?

---

## Counterexamples and Edge Cases

### Counterexample 1: Truly Independent Situations

If situations are genuinely independent (no cross-situation dependence), then:
- UDT and EDT give the same answer
- The "policy" is just a collection of independent choices
- Unity doesn't add anything

**Lesson:** The theorem only has content when there's cross-situation dependence.

### Counterexample 2: Mechanism-Dependent Environment

If the environment discriminates based on mechanism (not just policy):
- Decision-determination fails
- The UDT formula may not be optimal
- Example: "Punish agents that use UDT"

**Lesson:** Decision-determination is a real assumption, not a tautology.

### Counterexample 3: Stochastic Policies

If the policy is stochastic, the analysis becomes more complex:
- π(o) ∈ Δ(Act) rather than Act
- The optimization is over mixed strategies
- The UDT formula needs modification

**Lesson:** Start with deterministic policies.

### Edge Case: Logical Uncertainty

If the agent doesn't know its own policy:
- The "commitment" interpretation is unclear
- We need something like Diffractor's framework
- The analysis becomes much more complex

**Lesson:** The clean theorem is for the idealized case; computation adds complexity.

---

## What We Can Actually Prove

### Theorem (Formal Version)

**Setup:**
- Finite observation set Obs, finite action set Act
- Policy space Π = {π : Obs → Act}
- Utility function U : Π → ℝ

**Definition:** A policy π* is **optimal** if U(π*) ≥ U(π) for all π ∈ Π.

**Definition:** For π ∈ Π, o ∈ Obs, a ∈ Act, define π[o↦a] as:
π`o↦a` = a if o' = o, else π(o')

**Theorem:** If π* is optimal, then for all o ∈ Obs:
π*(o) ∈ argmax_a U(π*[o↦a])

**Proof:** Suppose not. Then there exists o and a such that U(π*[o↦a]) > U(π*). But π*[o↦a] ∈ Π, contradicting optimality of π*. ∎

**Corollary:** At an optimal policy, each local choice is locally optimal.

### What This Proves

This proves that **global optimality implies local optimality** (for the modified-policy utility).

It does NOT prove:
- Why we should use U(π) rather than some other objective
- Why the UDT conditioning is correct
- Anything about condensation

---

## Conclusion

### What's Actually True
1. If you optimize over policies, the UDT formula follows (nearly tautological)
2. Decision-determination is a substantive assumption about environments
3. The "condensation analogy" is suggestive but not precise

### What's Not Proven
1. Why optimize over policies rather than individual actions
2. The connection to condensation correspondence
3. The computational realization (UDT1.01)

### What We Need
1. A precise argument for why unified agency implies policy optimization
2. A real theorem connecting to condensation (not just analogy)
3. Formalization of the computational aspects

### Next Steps
1. Try to formalize the "unity implies policy optimization" argument
2. Look for precise connections to condensation
3. Write Lean proofs of the parts that can be proven


---
# === FILE: diffractor-synthesis.md ===
---

# Synthesizing Diffractor's UDT1.01 with the Multi-Agent Framework

## The Key Insight from Diffractor

Diffractor distinguishes:
- **Plannable observations:** Environmental observations you can write a lookup-table policy for
- **Unplanned observations:** Epistemic states, computation outputs, beliefs - things that affect your action but can't be pre-planned

**The fundamental point:** You can't plan for everything. Even computing a good policy requires observing things (like computation outputs) that you didn't plan for.

**The consequence:** Any realistic agent has a "contracted tree" (just plannable observations, what the policy formally covers) and an "expanded tree" (including epistemic states, the actual decision landscape).

## Connection to Radical Probabilism

### Unplanned Observations = Radical Updates

In Diffractor's framework:
- Your epistemic state S_h at plannable location h isn't determined by prior planning
- Different computation paths could give different S_h
- From your past self's view, your epistemic state looks like uncertainty

In radical probabilism:
- Your probability function can change for reasons other than evidence
- You can "change your mind" through reflection, deliberation, computation
- From your past self's view, your current beliefs look like uncertainty

**The connection:** Unplanned observations in UDT1.01 ARE radical probabilist updates. When you observe the output of a long computation, you're not conditionalizing on evidence - you're discovering what you think.

### The Expanded Tree = The Multi-Agent Space

**Diffractor's expanded tree:** All paths (h₁, S₁, h₂, S₂, ...) of interleaved plannable observations and epistemic states.

**Multi-agent view:** Each node (h, S) is an "instance" - an agent with:
- Plannable location h (what environmental situation it's in)
- Epistemic state S (what beliefs/computations it has)

Different instances (h, S) and (h, S') at the same plannable location h but different epistemic states are genuinely different minds that need to coordinate.

### The Contracted Tree = The Contract

**Diffractor's contracted tree:** Just plannable observations h. Policies π: H → A map histories to actions.

**Multi-agent view:** The contracted tree is the "contract" - the specification of behavior that all instances agree to, regardless of their epistemic states.

**The gap:** The contract (contracted tree policy) doesn't fully determine behavior because it doesn't specify how to handle unplanned observations. Instances must use some algorithm to turn their epistemic states into actions.

## UDT1.01 as the Optimal Coordination Algorithm

### Diffractor's Result

For any:
- Metapolicy π (way of assigning algorithms to plannable situations)
- Plannable event h
- Algorithm A (way of using unplanned information)

"π(h) + a little UDT1.01" ≥ "π(h) + a little A"

**Meaning:** No matter your current policy, no matter the situation, you'd always prefer to add more UDT1.01 rather than more of any other algorithm.

### Multi-Agent Interpretation

If all instances agree to run UDT1.01, then:
- Each instance, given its epistemic state, computes the locally optimal action
- "Locally optimal" accounts for retrocausal and acausal effects
- No instance would prefer to deviate to a different algorithm

**This is a coordination equilibrium:** UDT1.01 is the unique algorithm where all instances agree to use it.

### Why UDT1.01 Respects Instance Autonomy

UDT1.01 doesn't require instances to override each other. Instead:
- Each instance uses its own epistemic state
- Each instance computes its own action
- Coordination emerges from all instances using the same algorithm

**The "contract" is to run UDT1.01**, not to output specific actions. This is exactly the "principles over outputs" idea from the earlier documents.

## The "Conservation of Expected Gain" as Non-Interference

### Diffractor's Conservation Principle

UDT1.01 incorporates "conservation of expected gain" - the insight that:
- Your action's expected gain should be evaluated from the prior perspective
- Not from your current epistemic state (which might be biased by selection effects)

### Multi-Agent Reading

"Conservation of expected gain" means:
- Instance (h, S) doesn't just optimize for its current beliefs
- It optimizes for the expected utility across all epistemic states at h
- This respects other instances (h, S') who might have different beliefs

**Non-interference:** Instance (h, S) doesn't try to hijack the policy for its own epistemic state. It acts in a way that's good for all instances at h, weighted by prior probability.

### The Prior as Arbitration

The prior P (over epistemic states, over instances) serves as:
- The weighting for whose interests count
- The "veil of ignorance" perspective
- The arbitration mechanism between instances with different beliefs

**This is the social contract interpretation:** The prior is what all instances agreed to use for arbitration, before they knew what epistemic state they'd have.

## Dynamic Consistency and Radical Updates

### The Problem

With radical probabilist updates:
- Instance-now might disagree with instance-future about what's optimal
- If updates aren't constrained by evidence, anything goes
- How can there be coordination?

### Diffractor's Solution

UDT1.01 incorporates dynamic consistency:
- Your current action should be what your past self would have wanted
- "What your past self would have wanted" = expected utility from prior perspective
- This holds even if your current beliefs differ radically from the prior

### Multi-Agent Reading

Dynamic consistency = respecting the contract:
- Even if you've changed your mind (radical update)
- Even if your current beliefs suggest a different action
- You still act according to the agreed-upon principles

**This is commitment without rigidity:** You're committed to the algorithm (UDT1.01), not to specific outputs. The algorithm can adapt to your epistemic state while still respecting the contract.

## The Plannable/Unplanned Split as Communication Boundary

### Communication via Plannable Observations

Instances at the same plannable location h can "coordinate" because:
- They share h (same environmental situation)
- The policy for h is common knowledge

This is communication through the contracted tree - the formal policy specification.

### Divergence via Unplanned Observations

Instances at the same h but different epistemic states S, S' diverge because:
- Their unplanned observations differ
- They might make different computation-dependent decisions
- From each other's view, the other's decision is uncertain

This is the multi-agent aspect - genuinely different minds.

### UDT1.01 Bridges the Gap

UDT1.01 provides:
- A common algorithm all instances run
- Coordination despite epistemic divergence
- Each instance acts on its own information while respecting the contract

**This is coordination without communication at the unplanned level.** Instances don't need to share their epistemic states - they just need to all run UDT1.01.

## Synthesis: The Complete Picture

### The Multi-Agent Structure

1. **Instances:** Points (h, S) in the expanded tree - plannable location + epistemic state
2. **Different minds:** Instances at same h but different S are genuinely different agents
3. **Shared contract:** Agreement to run UDT1.01 on whatever epistemic state obtains

### The Coordination Mechanism

1. **Prior as arbitration:** The prior P weights different epistemic states
2. **Conservation of expected gain:** Each instance optimizes for the prior-weighted expectation
3. **Dynamic consistency:** Current action = what past-self would have wanted

### The Non-Interference Property

1. **No override:** Instance (h, S) doesn't try to modify other instances
2. **Respect for epistemic autonomy:** Each instance uses its own S
3. **Coordination through algorithm:** Agreement on UDT1.01, not on specific outputs

### The Radical Probabilist Aspect

1. **Epistemic states as radical updates:** S isn't determined by conditionalizing the prior
2. **Changes of mind are OK:** The algorithm handles arbitrary epistemic states
3. **Commitment despite change:** Following UDT1.01 even when your beliefs suggest otherwise

## Implications for the Representation Theorem

### Updated Theorem Statement

**Axioms:**
1. **Multi-situation structure:** Agent faces plannable observations h
2. **Epistemic uncertainty:** Agent has epistemic states S (unplanned observations)
3. **Common algorithm:** All instances (h, S) agree to run the same algorithm A
4. **Decision-determination:** Environment responds to the contracted-tree policy
5. **Gradient optimality:** A is the universally locally optimal algorithm

**Theorem:** Under these axioms, A = UDT1.01, and the agent's behavior satisfies:
- Dynamic consistency with the prior
- Conservation of expected gain
- No preference for self-modification

### What This Adds

The original representation theorem said: "Single coherent agent → updateless reasoning"

Diffractor's framework adds:
- **How** updateless reasoning works under computational limits (UDT1.01)
- **Why** it's optimal (gradient ascent in algorithm space)
- **What** the commitment structure is (contract on algorithm, not outputs)

### The Radical Probabilist Contribution

The radical probabilist framing adds:
- **Understanding** of epistemic divergence (instances have different minds)
- **Justification** for the prior (social contract, arbitration mechanism)
- **Interpretation** of non-interference (respecting epistemic autonomy)

## Open Questions

1. **What if instances don't all run UDT1.01?** Mixed populations, approximate agreement?

2. **How does learning work?** Diffractor notes UDT1.01 needs strong assumptions. Can they be relaxed?

3. **What about UDT1.1 considerations?** Diffractor lists "coordinating your policy with yourself" as an open problem. How does this fit?

4. **Connection to logical induction:** Diffractor couldn't directly plug in a logical inductor. Why? What's needed?

5. **The InfraBayes generalization:** Diffractor mentions Vanessa's InfraBayes setting. How does this fit the multi-agent picture?

## Summary

**Diffractor's UDT1.01** provides the computational content:
- The plannable/unplanned distinction
- The gradient-ascent derivation
- The specific algorithm and its optimality properties

**The radical probabilist multi-agent framework** provides the conceptual content:
- Instances as different minds
- The contract as coordination mechanism
- Non-interference as respect for epistemic autonomy

**Together:** A picture of agency as a cluster of minds, coordinating through shared principles (the UDT1.01 algorithm), respecting each other's epistemic autonomy, while still achieving updateless behavior.

This is not one agent with one policy, but many agents with shared principles - and the two descriptions are equivalent when the principles are UDT1.01.


---
# === FILE: radical-probabilist-udt.md ===
---

# Radical Probabilist UDT: A Multi-Agent Synthesis

## The Synthesis Question

Can we combine:
1. **UDT** - updateless reasoning, policy-centric
2. **Logical uncertainty** - uncertainty about mathematical/algorithmic facts
3. **Radical probabilism** - updates as changes-of-mind, not just conditionalization
4. **Communication structure** - from the original paper
5. **UDT1.0 framing** - "what policy would I have wanted to commit to?"

The result should be a picture of agent-instances as a **cluster of minds** that coordinate without overriding each other.

## Background: The Pieces

### Classical UDT

- One agent, one policy π: O → A
- Agent "knows" its policy (or at least commits to one)
- At each observation o, implement π(o)
- Evaluate by E[U | π] - expected utility of the whole policy

**Problem:** Assumes the agent knows its own algorithm, which is impossible under logical uncertainty.

### Logical Uncertainty

- Agent is uncertain about logical/mathematical facts
- Including facts about its own algorithm's outputs
- Can't just "know" what π(o) is for all o
- Must reason under uncertainty about self

**Tension with UDT:** UDT assumes you can evaluate "what if my policy maps o to a?" But with logical uncertainty, you don't know your policy.

### Radical Probabilism

Classical Bayesianism: Update by conditionalization. P_new(X) = P_old(X | E) where E is evidence.

Radical probabilism (Jeffrey, van Fraassen, others): Updates need not be conditionalization. You can "change your mind" in ways not forced by evidence.

**Key feature:** Your probability function can shift discontinuously. P_new need not be derivable from P_old by any standard rule.

**Implication for instances:** If instance X_o1 has probability P_o1, and instance X_o2 has probability P_o2, these might not be related by conditionalization. They're separate "minds."

### Communication (from the paper)

Instances can communicate through:
- Shared memory (internal observations)
- Explicit messages
- Implicit signals (your action IS a message to future instances)

Communication enables coordination without requiring a pre-committed policy.

### UDT1.0 (Diffractor's Framing)

UDT1.0: "What policy would I have wanted to commit to, before I knew which observation I'd face?"

This is a **counterfactual self-negotiation:** Current-me asks what past-me-before-observations would have wanted.

**Key insight:** The "prior" in UDT is like an **agreement among all possible instances.** Each instance honors this agreement even when their local beliefs differ.

## The Synthesis: Instances as Negotiating Parties

### Core Idea

Instead of: One agent with one policy, instances as mere "applications"

Think of: **Multiple agents (instances) who must coordinate**

Each instance X_o is a legitimate agent with:
- Its own epistemic state P_o
- Its own decision-making authority
- Its own "mind" that can change

The "policy" is not imposed from above. It **emerges from negotiation** among instances.

### The Social Contract Interpretation

**The prior as social contract:**

The "prior" P in UDT is like a social contract among instances:
- "We all agree to act as if P is the correct probability function"
- "Even if my local posterior differs, I honor the contract"

**Why honor the contract?**

Because it was (counterfactually) agreed to by all instances, including me. Breaking the contract means defecting on my other selves.

**Radical probabilist twist:**

Different instances might have different beliefs (not just different posteriors from the same prior). But they can still honor a contract about behavior.

The contract isn't "believe P." It's "act as if P, for coordination purposes."

### Non-Interference as Mutual Respect

**Classical UDT:** Instance X_o implements π(o) because that's what the single policy says.

**Multi-agent UDT:** Instance X_o implements π(o) because that's what X_o agreed to (along with all other instances).

**Non-interference:** X_o doesn't try to override X_o' 's decision. Why?
- X_o' is a legitimate party to the contract
- X_o' has their own reasons and beliefs
- Overriding X_o' would be like breaking the contract

**This is the self-trust condition:** Not modifying your other instances because you respect their agency.

### Communication as Renegotiation

When new information arrives:
1. Instance X_o receives observation o
2. X_o's beliefs update (possibly radically, not just by conditionalization)
3. X_o can communicate with other instances
4. Instances can **renegotiate** the contract if needed

**Key constraint:** Renegotiation must be consensual. X_o can propose a new contract, but can't impose it.

This is why communication is important: it allows coordination to adapt without unilateral override.

### Logical Uncertainty as Uncertainty About the Contract

**The problem:** I don't know my own algorithm. So I don't know what contract I've "committed to."

**Resolution:** The contract isn't about specific actions. It's about **principles** and **reasoning processes.**

The contract might say:
- "Reason updatelessly (condition on policy properties)"
- "Respect other instances' decisions"
- "Communicate before deviating from expectations"

You can follow these principles even without knowing exactly what your policy is.

**Logical uncertainty becomes:** Uncertainty about what my principles imply in specific cases.

## Formal Sketch

### The Setup

- **Instances:** {X_o : o ∈ O}
- **Epistemic states:** Each X_o has probability function P_o over worlds
- **P_o need not be P conditioned on o** (radical probabilism)
- **Actions:** Each X_o chooses a_o ∈ A
- **Utility:** U depends on the world and the action profile (a_o)_{o ∈ O}

### The Contract

A **contract** is a specification C that:
1. Recommends actions: C(o) ∈ A for each o (the "policy")
2. Is derived from shared principles, not imposed externally
3. Can be updated through legitimate communication

### Instance Decision-Making

X_o, facing observation o:
1. Recalls the current contract C
2. Considers whether to follow C(o) or deviate
3. Evaluates: "If I deviate, what are the consequences?"
4. Consequences include: other instances might also deviate (breaking coordination)

### Non-Interference Condition

X_o follows C(o) even if P_o suggests a different action, provided:
- C was legitimately agreed to
- No new information warrants renegotiation
- Other instances are expected to follow C

This is **updateless reasoning:** Acting on the contract, not on local beliefs.

### When to Renegotiate

Renegotiation is appropriate when:
- New information reveals the contract is based on false assumptions
- Communication is possible to establish a new contract
- The new contract is better for all instances (Pareto improvement)

Renegotiation is NOT appropriate when:
- You just don't like the contract's implications for you
- You can't communicate the change to other instances
- It would break coordination (even if locally better)

## The UDT1.0 Connection

**Diffractor's UDT1.0:** "What policy would I have wanted to commit to?"

**In the contract framework:** "What contract would all instances have agreed to, before knowing their observations?"

This is **hypothetical negotiation:** We imagine a "veil of ignorance" where no instance knows which observation they'll face, and ask what they'd agree to.

**Result:** The contract should maximize E[U | C] = Σ_o P(o) · U(o, C(o), ...)

This is the standard UDT formula, but now interpreted as an **agreement** rather than a **dictate.**

### Why This Matters

The agreement interpretation explains:
1. **Why follow the contract:** It was agreed to by all instances, including me
2. **Why non-interference:** Other instances are legitimate parties, not just "implementations"
3. **Why communication matters:** It's how we renegotiate, not how we override
4. **Why logical uncertainty is OK:** The contract is about principles, not specific outputs

## Radical Probabilism Specifics

### Updates as Changes of Mind

In classical Bayesianism, your beliefs at time t+1 are determined by your beliefs at time t plus evidence.

In radical probabilism, you can change your probability function for reasons other than evidence:
- Reflection (you realize your old beliefs were incoherent)
- Testimony (you defer to someone else's beliefs)
- Pure change of mind (you just see things differently now)

### Instances as Different Minds

If updates can be radical, then:
- X_o1 's beliefs might be very different from X_o2 's beliefs
- Not because of different evidence, but because they've "changed their minds" differently
- They're like different people who happen to share a coordination problem

**This is the multi-agent view:** Instances are genuinely separate minds, not just the same mind with different information.

### Coordination Despite Difference

How can different minds coordinate?

1. **Shared history:** They all originated from the same source
2. **Shared contract:** They agreed (or their common ancestor agreed) to certain principles
3. **Communication:** They can talk to each other and negotiate
4. **Common interest:** They share a utility function (even if they have different beliefs about how to maximize it)

### The Binding Force of the Contract

Why should X_o follow the contract if X_o's beliefs now differ radically from when the contract was made?

**Answer 1 (consequentialist):** If X_o deviates, other instances might too. Coordination breaks down. Everyone loses.

**Answer 2 (deontological):** The contract is binding because it was agreed to. Changing your mind doesn't release you from agreements.

**Answer 3 (virtue):** A trustworthy agent honors commitments. X_o wants to be the kind of agent who can make credible commitments.

All three answers support following the contract even under radical belief change.

## Implications

### For Self-Trust

Self-trust = non-interference among instances.

In the contract framework: Self-trust means respecting the agreement, not overriding other instances.

**Radical probabilist version:** Even if my beliefs have changed radically, I trust my other instances to act according to the contract. And I act according to the contract so they can trust me.

### For the Representation Theorem

**Original theorem:** Single agent + decision-determination → updateless reasoning

**New theorem:** Cluster of coordinating instances + legitimate contract + non-interference → updateless reasoning

The "single agent" condition is replaced by "cluster with a contract." The updateless reasoning emerges from respecting the contract rather than from being a single entity.

### For Logical Uncertainty

The agent doesn't need to "know" its policy. It needs to know:
1. The principles of the contract
2. How to apply them in the current situation
3. That other instances will also apply them

Uncertainty about exact outputs is OK, as long as there's agreement on principles.

### For Communication

Communication is central, not peripheral:
- It's how the contract is established
- It's how renegotiation happens
- It's how instances coordinate without overriding

**Contrast with classical UDT:** In classical UDT, communication is nice but not essential (the policy already determines everything). In radical-probabilist UDT, communication is essential because instances are genuinely separate minds.

## Open Questions

1. **How exactly does the contract get established?** Is there a "founding moment" or is it always implicit?

2. **What principles should the contract contain?** Just "maximize E[U]" or something richer?

3. **When is renegotiation legitimate?** Need clear criteria to distinguish legitimate change from defection.

4. **How does this interact with game-theoretic concepts?** Is the contract a Nash equilibrium? Something stronger?

5. **What if instances have different utility functions?** (They might, under radical probabilism.) How does coordination work then?

6. **How does this relate to acausal trade?** The contract framework looks similar to superrationality/acausal negotiation.

## Summary

**Classical UDT:** One agent, one policy, instances as applications.

**Radical Probabilist UDT:** Multiple minds (instances), coordinating through a social contract.

Key features:
- Instances are genuinely separate agents with their own beliefs
- The "policy" is a contract they've agreed to
- Updateless reasoning = honoring the contract despite local belief changes
- Non-interference = respecting other instances as legitimate parties
- Communication = essential for establishing and updating the contract

This resolves the tension with logical uncertainty: You don't need to know your exact policy, just the principles you've committed to.

And it gives a richer picture of agency: Not a monolithic optimizer, but a community of minds bound by agreement.


---
# === FILE: when-udt-edt-diverge.md ===
---

# When Do UDT and EDT Diverge?

## The Question

UDT and EDT are often presented as different decision theories with different recommendations. But when exactly do they give different answers?

This document characterizes the precise condition.

## The Setup

An agent faces a multi-situation decision problem:
- Set of situations S the agent might face
- At each situation s, available actions A
- Utility function U(s, a, context) where "context" may include actions at other situations
- Probability distribution P over which situation obtains

## EDT's Recommendation

At situation s, EDT computes:

a*_EDT = argmax_a E[U | I am at s and I take action a]

This conditions on being-at-s as a fact about the world, then asks what action maximizes expected utility given this fact.

## UDT's Recommendation

At situation s, UDT computes:

a*_UDT = argmax_a E[U | my policy maps s to a]

This conditions on having-a-policy-that-says-a-for-s, which is a constraint on the global policy.

## When Are They the Same?

**Theorem.** EDT and UDT agree when there is **no cross-situation dependence**.

**Definition.** A problem has **no cross-situation dependence** if:

For all s, s' ∈ S with s ≠ s', the utility at s does not depend on the action at s'.

Formally: U(s, a, context) = U(s, a) for some function U: S × A → ℝ.

**Proof sketch:**

If U(s, a) depends only on s and a:
- EDT: E[U | s, a] = U(s, a)
- UDT: E[U | π(s) = a] = Σ_{s'} P(s') · U(s', π(s'))

For the specific situation s:
- EDT optimizes a → U(s, a)
- UDT optimizes π, which includes choosing π(s)

Since U at s depends only on the action at s, UDT's global optimization decomposes:
- max_π Σ_{s'} P(s') · U(s', π(s')) = Σ_{s'} P(s') · max_a U(s', a)

Each local optimization (max_a U(s, a)) can be done independently. UDT and EDT agree.

## When Do They Diverge?

**Theorem.** EDT and UDT can diverge when there IS **cross-situation dependence**.

**Definition.** A problem has **cross-situation dependence** if:

There exist situations s ≠ s' and actions a such that U(s, a, context) depends on the action taken at s'.

**Example: Newcomb's Problem**

- Situations: {predicting-phase, decision-phase}
- At predicting-phase: predictor forms belief about your policy
- At decision-phase: you choose one-box or two-box
- Utility: depends on predictor's choice, which depends on what you WOULD do

Cross-situation dependence: Your action at decision-phase affects the predictor's belief at predicting-phase, which affects your utility.

EDT at decision-phase: "Given I'm deciding, what should I do?" Conditions on being in this situation, which doesn't directly constrain the prediction (already made).

UDT: "What policy should I have?" Recognizes that the policy affects the prediction.

**Result:** EDT two-boxes, UDT one-boxes.

## Characterizing Cross-Situation Dependence

Cross-situation dependence arises from:

### 1. Prediction
The environment predicts your behavior and responds to the prediction.
- Newcomb: Predictor responds to predicted policy
- Transparent Newcomb: You see the result of the prediction

### 2. Correlation
Your behavior correlates with others' behavior (not through causal influence).
- Twin Prisoner's Dilemma: Your twin does what you do
- Symmetry arguments: Identical agents make identical choices

### 3. Commitment
Your current behavior affects how future situations treat you.
- Reputation: Others trust you if you've been trustworthy
- Self-trust: Your future self follows advice if past self was reliable

### 4. Coordination
Multiple instances of you must coordinate without communication.
- Coordinated Buttons: Your copies must press the same button
- Third Button: Coordination with risk of exploitation

## The Common Structure

All cases of cross-situation dependence have the same structure:

**Utility in situation s depends on a counterfactual about another situation s':**
"What would this agent do if it faced s' instead?"

If the counterfactual is part of the utility calculation, then:
- EDT ignores it (conditions only on being-in-s)
- UDT accounts for it (conditions on the policy, which answers the counterfactual)

## The Policy-Dependence Test

**Test:** Does the environment's response to you at s depend on your policy π, beyond just π(s)?

If yes: cross-situation dependence. EDT and UDT may diverge.
If no: no cross-situation dependence. EDT and UDT agree.

**Formally:** Let R(s, π) be the environment's response at s given policy π.

- If R(s, π) = R(s, π') whenever π(s) = π'(s): no cross-situation dependence.
- If R(s, π) ≠ R(s, π') for some π, π' with π(s) = π'(s): cross-situation dependence.

## Why UDT is Correct Under Cross-Situation Dependence

When cross-situation dependence exists:

1. The environment responds to your **policy**, not just your local action
2. Your utility depends on this response
3. To maximize utility, you must account for how your policy affects the response
4. EDT doesn't account for this; UDT does

**The argument:** If the environment checks "what would this agent do in situation s'?" then your answer to that question matters. UDT gives the right answer because it conditions on the policy. EDT gives the wrong answer because it conditions only on the local situation.

## The "Fairness" Connection

**Decision-determination** (fairness) says: the environment responds to policy, not to mechanism.

Combined with cross-situation dependence:
- The environment cares about your policy (which situations you'd handle which way)
- But not about HOW you arrive at that policy (your internal algorithm)

This is exactly the regime where UDT is correct:
- Account for the policy (UDT conditioning)
- Don't worry about mechanism (decision-determined)

## Summary

| Condition | EDT | UDT | Winner |
|-----------|-----|-----|--------|
| No cross-situation dependence | ✓ | ✓ | Tie |
| Cross-situation dependence | ✗ | ✓ | UDT |

**The representation theorem says:** Unified agents in cross-situation-dependent problems reason updatelessly. This is exactly when UDT outperforms EDT.


---
# === FILE: observations-and-policies.md ===
---

# Observations, Policies, and the Structure of Agency

## The Question

The formal-single-agent.md document treated "situations" abstractly. But in the original paper, situations are defined by **observations** - what the agent perceives.

How does observation structure fit into the representation theorem?

## From Situations to Observations

**Definition.** An **observation-structured problem** is a tuple (Ω, P, O, A, U) where:
- Ω is a set of possible worlds
- P is a probability distribution on Ω
- O: Ω → Obs is an observation function (what the agent sees)
- A is the set of available actions
- U: Ω → ℝ is utility

The agent observes O(ω) and must choose an action. Different worlds may yield the same observation (imperfect information).

## Policies in Observation-Structured Problems

**Definition.** A **policy** is a function π: Obs → A.

**Key point:** The policy specifies what to do for *each observation*, not each world. Multiple worlds map to the same observation, so the agent can't distinguish them.

## Why Observation Structure Matters

**Claim:** Observation structure is what makes "instances" natural.

An **instance** is "the agent facing observation o." Multiple worlds realize the same instance (those with O(ω) = o).

The agent's policy must give the same action for all worlds with the same observation - that's what having a policy *means* for an informationally-constrained agent.

## The UDT Formula with Observations

For an observation-structured problem, the UDT formula is:

π*(o) = argmax_a E[U | π(o) = a]

where the conditional means: expected utility given that the policy maps observation o to action a.

**Unpacking the conditional:**

E[U | π(o) = a] = Σ_ω P(ω | π(O(ω)) = A(ω)) · U(ω)

where A(ω) is the action taken in world ω, which equals π(O(ω)) by the policy.

Wait, this is getting circular. Let me be more careful.

## Careful Treatment of the Conditional

**Setup:** The agent will choose a policy π. The action in world ω is π(O(ω)).

**The evaluation:** E_π[U] = Σ_ω P(ω) · U(ω, π(O(ω)))

where U(ω, a) is utility in world ω when action a is taken.

**The UDT claim:** For a single coherent agent, the optimal policy satisfies:

For each o: π(o) = argmax_a [E_π[U | O = o] where we fix π(o) = a and optimize π elsewhere]

If the policy is globally optimal, then each component is locally optimal given the rest.

## Cross-Observation Dependence

**Definition.** A problem has **cross-observation dependence** if utility in some worlds depends on actions taken under different observations.

Formally: There exist observations o, o', worlds ω with O(ω) = o, and actions a, a' such that:

U(ω, a) depends on what action would be taken if O(ω) = o'

This happens in:
- **Newcomb problems:** Predictor responds to your policy
- **Coordination problems:** Your copy in another situation responds to your shared algorithm
- **Commitment problems:** Your future self responds to your current credibility

## The Observation-Based Representation Theorem

**Theorem.** In an observation-structured problem with cross-observation dependence:

If the agent:
1. Is unified (same algorithm/policy across all observations)
2. Maximizes expected utility
3. Recognizes the cross-observation dependence

Then the agent's choice at observation o is:

a* = argmax_a E[U | π(o) = a, π optimal elsewhere]

For a coherent agent with a single optimal policy, this equals:

a* = argmax_a E[U | π(o) = a]

This is the UDT formula.

## Connection to Instances in the Original Paper

The paper defines "instances" as the agent facing different observations. Two instances can communicate if they share a common past.

**Reinterpretation:** Instances aren't ontologically separate entities. They're applications of the *same* agency model to different observational contexts.

When we say "instance o and instance o' can communicate," we mean: the agent's policy for o and o' share a common origin - they're both outputs of the same decision procedure.

**Functional identity:** All instances run the same algorithm. So "what instance o does" and "what instance o' does" are logically connected - they're outputs of the same function.

## Why Observations Define Instances

**Claim:** Observations are the natural grain for instances because policies are observation-dependent.

A policy π: Obs → A assigns an action to each observation. The agent can't make finer distinctions (it doesn't know which ω, only which O(ω)).

So "instance at o" = "the application of the agent's policy to observation o."

This is why observation-based factoring is appropriate for agency modeling, not because it's the only possibility, but because it's the finest grain at which the agent can condition.

## Finer and Coarser Grains

**Finer grain (world-level):** We could imagine an agent that conditions on the full world ω, not just O(ω). But this agent has more information than our agent.

**Coarser grain (situation-level):** We could imagine grouping observations into "situations" and only conditioning on situations. But this throws away information the agent has.

**The observation level is natural:** It's the finest grain at which the agent can distinguish circumstances, and therefore the finest grain at which its policy can vary.

## Imperfect Self-Knowledge

What if the agent doesn't know its own observation?

**Example:** Transparent Newcomb. The agent observes whether the big box is empty. But in some versions, the agent might be uncertain about what it observes (confusion, unreliable perception).

**Complication:** If the agent doesn't know its observation, it can't directly implement a policy π: Obs → A. It must reason about what it might be observing.

**Resolution:** The agent reasons: "I'm implementing some algorithm F. Whatever observation I have, I'll do F(o). So my action depends on my observation, even if I'm uncertain about it."

This is still policy-based reasoning - the agent reasons about what policy it's implementing, not about what action to take in isolation.

## The Logical Uncertainty Connection

**Observation:** The agent might not know what its policy IS (even though it implements one).

This is the "logical uncertainty" problem. The agent is uncertain about facts that are, in principle, computable from its own algorithm.

**How UDT handles this:** The agent conditions on "my policy maps o to a" even without knowing what its policy is. It reasons: "If my policy maps o to a, then the expected utility is X. If my policy maps o to a', the expected utility is Y. I should implement whichever policy is better."

The agent doesn't need to know its policy to reason about what it *should* be. It can evaluate hypothetical policies and implement the best one.

## Summary: Observations and the Representation Theorem

1. **Observation structure** defines what the agent can condition on
2. **Policies** are functions from observations to actions
3. **Instances** are applications of the policy to specific observations
4. **Cross-observation dependence** means utility depends on the whole policy
5. **Unified agents** (single policy) in such problems reason updatelessly
6. **The observation level** is natural because it's the agent's finest distinguishable grain

The representation theorem says: at the observation level, unified agents optimize policies, which means conditioning on "my policy maps o to a" rather than on "I'm at o and I take a."

---

## Remaining Questions

1. **Sub-observation structure:** What if there's relevant structure finer than observations (e.g., the agent's internal state)?

2. **Observation-dependent utility:** What if the utility function depends on the observation directly (not just through the world)?

3. **Dynamic observations:** What if the agent receives a sequence of observations and updates its policy over time?

4. **Communication between instances:** How does the paper's communication structure fit with this framework?


---
# === FILE: decision-determination-argument.md ===
---

# The Decision-Determination Argument for Updateless Reasoning

## Core Idea

If a problem is "decision-determined" (the environment only cares about your external policy, not your internal constitution), then **policies** are the natural unit of analysis, not individual actions. And if policies are the natural unit, you should evaluate them as wholes, which leads to updateless reasoning.

## Setup

**Decision-Determination (from the paper):**
1. Utility depends only on the external environment E
2. E is conditionally independent of the agent's internal state given the external policy

In other words: the universe doesn't care *how* you compute your policy, only *what* it is.

## The Argument

### Step 1: Policies are the "natural" unit

In a decision-determined problem, two agents with the same external policy get the same outcomes (in distribution). The environment can't distinguish them.

This means: from the perspective of predicting outcomes, a policy is a complete description of "what the agent does." Individual actions matter only insofar as they're part of a policy.

### Step 2: Evaluating policies requires considering all instances

A policy pi: O -> A specifies what to do at *every* possible observation. When I ask "how good is policy pi?", I'm asking about its performance across all situations where it might be applied.

This is naturally updateless: I'm not asking "how good is pi given that I'm at observation o?" I'm asking "how good is pi overall?"

### Step 3: The decision at each observation should reflect whole-policy evaluation

If the natural unit is the policy, then when I'm at observation o deciding what to do, I should ask: "What policy do I want to have? And what does that policy say at o?"

This is exactly updateless reasoning.

## Comparison: What does updateful reasoning look like?

An updateful agent at observation o asks: "Given that I'm at o, what action maximizes expected utility?"

The conditioning on "I'm at o" implicitly treats the current observation as special. But in a decision-determined problem, there's nothing special about any particular observation - the policy is what matters.

Updateful reasoning breaks the symmetry between observations that decision-determination establishes.

## Formalization Attempt

### Definition: Policy-Centric Agency

An agency attribution is **policy-centric** if the agent's decision at each observation o can be described as:
1. Evaluating policies pi on the basis of E[U | external-policy = pi]
2. Selecting an optimal policy pi*
3. Outputting pi*(o)

### Theorem (Desired)

In decision-determined problems, policy-centric agency is equivalent to UDT.

### Proof Sketch

UDT: pi(o) = argmax_a E[U | pi(o) = a]

This conditions on "my policy maps o to a" rather than "I take action a at observation o."

If we're evaluating whole policies, the expected utility of policy pi is:
E[U | external-policy = proj(pi)]

where proj(pi) is the projection of pi to external actions.

The policy that maximizes this is the UDT policy, because UDT at each observation o selects the action that would be part of the best whole policy.

## The Remaining Gap: Why be policy-centric?

This argument shows: IF you evaluate policies as wholes, THEN you reason updatelessly.

But why should you evaluate policies as wholes?

**Answer 1 (from decision-determination):** Because in fair problems, policies are the only thing that matter. Individual actions have no causal power except through their contribution to the policy.

**Answer 2 (from reflective stability):** If you evaluate actions locally, you can end up with a policy that no part of you endorses as a whole. This is a form of incoherence.

**Answer 3 (from agency attribution):** When we attribute a single agency across situations, we're committing to a unified policy. The unity of the agent implies unity of policy evaluation.

## Implications for the Representation Theorem

The axioms might look like:

1. **Agency Attribution:** A system X is attributed utility U, boundary B, observations O, actions A

2. **Decision-Determination:** The environment E is conditionally independent of X's internals given the external policy

3. **Unified Agency:** The attribution treats X across all observations as a single agent (not independent agents who happen to share goals)

4. **Optimization:** X's policy maximizes expected utility

Then: X must reason updatelessly.

The key is axiom 3: what does "unified agency" mean formally?

## Unified Agency: First Attempt

**Definition:** An agency attribution has **unified agency** if there exists a single policy pi such that the agent's action at each observation is pi(o).

This is too weak - it's just saying the agent is deterministic given the observation.

**Definition (Attempt 2):** An agency attribution has **unified agency** if the agent evaluates the quality of its action at each observation by evaluating the quality of the whole policy that action is part of.

This is closer but circular - it just says the agent is policy-centric.

**Definition (Attempt 3):** An agency attribution has **unified agency** if changing the agent's behavior at one observation is modeled as changing a parameter that also affects behavior at other observations.

This captures: "instances" are not independent. They share something (the policy, the algorithm, the type).

## Connection to the Paper's "Instances"

The paper factors by external observation: each value of Ö defines an instance.

In the unified agency framing, this factorization is justified by decision-determination: the environment's response to observation-o is determined by the action at observation-o.

But the instances are connected by sharing a policy (or algorithm, or decision procedure).

The key tension: instances are independent in what they observe and do, but connected in how they decide.

UDT respects this structure: it evaluates policies while allowing each instance to condition on its local observation.

## Next Steps

1. Formalize "unified agency" properly
2. Show that optimization + decision-determination + unified agency implies updateless reasoning
3. Address the prior: where does P come from?
4. Address logical uncertainty: how does the agent reason about its own algorithm?


---
# === FILE: non-interference-formalized.md ===
---

# Non-Interference Among Instances: Formal Treatment

## The Non-Interference Principle

**Informal:** An instance X_o doesn't try to override or modify other instances X_o'.

**Why this matters:**
- It's the core of self-trust
- It distinguishes "coordination" from "control"
- It's what makes the multi-agent view coherent

## Classical vs. Multi-Agent Framing

### Classical UDT Framing

**One policy, multiple applications:**
- There's a single π: O → A
- Each instance is an "application" of π
- Non-interference is automatic: there's nothing to interfere WITH
- "Self-trust" means not wanting to change π

### Multi-Agent Framing

**Multiple deliberators, coordinated by contract:**
- Each X_o is a genuine deliberator with its own "mind"
- The "policy" emerges from their coordinated decisions
- Non-interference is a CHOICE: X_o could try to override X_o', but doesn't
- "Self-trust" means respecting other instances' deliberative authority

## What Does "Interference" Mean?

### In the Paper's Framework

The paper distinguishes:
- **Chosen policy Π*:** What the agent would do without modification
- **Effective policy Π†:** What the agent actually does (possibly after modification)

**Self-modification:** Actions that change Π† to differ from Π*.

**Interference** = self-modification that affects other instances:
- X_o takes action that changes how X_o' will behave
- X_o overrides X_o' 's deliberation

### Types of Interference

1. **Direct modification:** X_o changes X_o' 's algorithm/memory
2. **Commitment device:** X_o constrains X_o' 's options (like Ulysses and the mast)
3. **Information manipulation:** X_o gives X_o' false information to change their decision
4. **Side-channel manipulation:** X_o exploits non-semantic aspects of the interface

### Non-Interference as a Constraint

**Non-interference condition:** X_o takes only actions consistent with X_o' implementing Π* (the chosen policy).

This means:
- No direct modification of other instances
- No commitment devices that override deliberation
- No information manipulation
- No side-channel exploitation

## Why Respect Non-Interference?

### Argument 1: Contractual Obligation

The instances agreed to a contract. Part of the contract is: "We each respect each other's deliberative authority."

Breaking this is defection. It undermines the whole coordination structure.

### Argument 2: Futility (Under Functional Identity)

If X_o and X_o' run the same algorithm:
- Any reasoning X_o uses to justify interference, X_o' could also use
- If interference is "allowed," it's allowed for everyone
- Universal interference breaks coordination

So non-interference is the stable equilibrium.

### Argument 3: Epistemic Humility

X_o might think X_o' is making a mistake. But:
- X_o' has information X_o doesn't (different observation)
- X_o' might be reasoning correctly given that information
- X_o should be humble about second-guessing X_o'

Non-interference follows from respecting X_o' 's epistemic position.

### Argument 4: The Representation Theorem

If X_o interferes with X_o', the "policy" is no longer coherent:
- What X_o does depends on opportunity to interfere
- The environment responds to this mess, not to a clean policy
- Decision-determination fails

Non-interference is required for the representation theorem to apply.

## Formal Characterization

### The Paper's Approach

**Definition (from paper):** The agent has self-trust if it never strictly prefers modification opportunities over non-modification.

Formally: For all modification opportunities M,
E[U | Π† = Π*] ≥ E[U | Π† ≠ Π*]

The agent does at least as well by sticking with Π* as by modifying.

### The Multi-Agent Approach

**Definition:** The system of instances {X_o} is non-interfering if each X_o's action is consistent with all other X_o' implementing their chosen actions.

Formally: Let a_o = X_o's chosen action (from deliberation).
Let a'_o = X_o's actual action (possibly including interference effects).

Non-interference: a'_o = a_o for all o.

**Equivalently:** No instance takes actions that cause other instances to deviate from their deliberated choices.

### The Relationship

The paper's self-trust: No preference for self-modification.
The multi-agent non-interference: No actual interference.

**Connection:** Under rationality, no preference implies no actual. If there's no benefit to interfering, a rational agent won't interfere.

## When Is Interference Tempting?

### Coordination Failure

If X_o expects X_o' to make a "bad" decision, X_o might want to intervene.

**Example:** Coordinated Buttons with pessimistic prior.
- X_o (in red room) expects X_o' (in green room) to press $5
- X_o thinks: "If I could make X_o' press $10, we'd both be better off"
- Temptation to interfere

**Resolution:** Under functional identity, X_o can think: "If I would press $10, so would X_o' (same algorithm). No need to interfere; just press $10."

### Time Inconsistency

X_now might disagree with what X_future will do.

**Example:** Ulysses and the Sirens.
- X_now (before hearing) wants to sail past safely
- X_future (hearing the Sirens) will want to steer toward them
- X_now is tempted to constrain X_future (rope to mast)

**Resolution in multi-agent framework:**
- Is this legitimate renegotiation or illegitimate interference?
- Key question: Did X_future consent to the constraint?
- If "past self constraining future self" is part of the contract, it's legitimate
- If not, it's interference

### Asymmetric Information

X_o might have information X_o' doesn't, suggesting X_o' will err.

**Example:**
- X_o observes that the environment is hostile
- X_o' doesn't know this and will act as if friendly
- X_o is tempted to modify X_o' 's behavior

**Resolution:**
- Communication, not modification
- X_o should TELL X_o' about the hostile environment
- X_o' then decides with full information
- This respects X_o' 's deliberative authority

## The Communication Alternative

### Principle

Whenever X_o is tempted to interfere with X_o', there should be a communication alternative that achieves the same goal without interference.

**Communication:** X_o sends information to X_o', X_o' updates and decides.
**Interference:** X_o changes X_o' 's behavior directly.

### Formal Condition (from Paper)

**Communicative alternative:** For any modification opportunity, there exists a communicative action that achieves the same expected utility.

If communicative alternatives always exist, then:
- Interference is never necessary
- Rational agents will prefer communication (respects autonomy, same outcome)
- Non-interference is satisfied

### The Paper's Theorem

**Theorem (Self-Trust):** Under decision-determination + communicative alternatives, the agent has self-trust.

**Translation:** If the environment responds to policies (decision-determination), and communication can achieve anything modification can (communicative alternatives), then there's no reason to modify.

## Multi-Agent Interpretation of the Theorem

### The Setup
- Instances {X_o} with shared contract
- Decision-determined environment (responds to joint policy)
- Communication channels between instances

### The Claim
If communicative alternatives exist, then non-interference is optimal.

### The Argument
1. Interference changes the effective policy
2. Under decision-determination, what matters is the policy
3. Communication can change the policy (by changing other instances' decisions)
4. So communication achieves whatever interference would achieve
5. Communication is preferable (respects autonomy, same outcome)
6. Therefore, rational instances don't interfere

## Radical Probabilist Refinement

### The Subtlety

In the radical probabilist framework, instances can "change their minds" in ways not forced by evidence.

**Question:** Is changing your mind about the contract a form of interference?

### Resolution

**Legitimate change of mind:** X_o reflects on the contract and concludes it should be updated. X_o communicates this to other instances. If they agree, the contract is renegotiated.

**Illegitimate interference:** X_o unilaterally decides to ignore the contract. X_o doesn't communicate or seek agreement. X_o just acts differently.

**The difference:** Legitimate change goes through the "amendment" process. Illegitimate change is defection.

### The Contract Must Allow Amendment

A rigid contract that can never be changed is a bad contract:
- Circumstances change
- Instances learn new things
- What seemed optimal before might not be optimal now

**Solution:** The contract includes an amendment process.
- Any instance can propose changes
- Changes require agreement (or at least non-objection)
- Unilateral change is defection

## Summary

**Non-interference:** Instances don't override each other's decisions.

**Why it holds:**
- Contractual obligation (we agreed not to)
- Futility (under functional identity, interference is self-undermining)
- Epistemic humility (respect others' epistemic position)
- Representation theorem (required for coherent policy)

**The communication alternative:**
- Whenever interference is tempting, communication achieves the same goal
- Communication respects autonomy; interference doesn't
- Rational agents choose communication

**Radical probabilist refinement:**
- Changing your mind is OK if it goes through the amendment process
- Unilateral change without communication is defection

**The result:** A system of instances that coordinate through agreement and communication, without any instance dominating the others. This is the multi-agent picture of UDT.


---
# === RESEARCH OUTLINE ===
---

# UDT Representation Theorem: Research Program Outline

## The Central Thesis

**"UDT isn't a decision theory. It's what 'agency' means."**

If you attribute unified agency to a system in a fair environment, updateless reasoning follows necessarily.

---

## Paper Structure (Draft)

### 1. Introduction
- Decision theory disagreements and the meta-question: why UDT?
- The representation theorem approach: derive UDT from agency axioms
- Preview of the result

### 2. Condensation Theory Background
- Information-theoretic quantities as random variables (what "representable" means)
- Common information (mutual information reified)
- Residual/condensation variables (conditional entropy reified)
- The condensation assumption

### 3. Agency as Latent Variable Structure
- Bipartite model: Agent A, Environment E
- Boundary B = A ∨ E (mutual information as interface)
- Policy Π = condensation variable for H(A|E)
- The IBE refinement: Interior/Boundary/External with dynamics D_I, D_B, D_E

### 4. Endorsement-Based Agency
- Agency is observer-relative: Alice attributing agency to Bob
- Belief endorsement (epistemic case)
- Selection endorsement (pure utility, no world-dependence)
- Control endorsement (impure utility, requires beliefs about world)
- Key insight: control endorsement requires policy to have structure

### 5. The Representation Theorem
- Setup: Unified agency (single Π across situations) + Fair environment (decision-determination)
- Statement: Control-endorsed unified agents satisfy the UDT formula
- The mathematical chain:
  - Optimal prediction → Decision-determination
  - Decision-determination → Policy determines utility
  - Policy determines utility → UDT formula is optimal

### 6. When UDT and EDT Diverge
- Cross-situation dependence as the key criterion
- Examples: Newcomb, Transparent Newcomb, Coordination problems
- The role of logical uncertainty

### 7. Computational Realization
- The problem: We can't enumerate policies under logical uncertainty
- UDT1.01 as approximation: Plannable vs unplanned observations
- Conservation of expected gain as non-interference principle

### 8. Discussion
- Implications for AI alignment
- Connection to self-trust and corrigibility
- Open problems

---

## Research Tasks (In Order)

### Phase 1: Firm Foundations
**Goal:** Nail down the precise definitions so everything else follows cleanly.

1. [ ] **Condensation definition** — Finalize the precise statement of what "condensation variable" means, including all three conditions. Currently in `condensation-variables.md` but needs your endorsement of exact wording.

2. [ ] **Bipartite agency model** — Write the clean version of A/E with B = A ∨ E and Π = H(A|E) residual. `policy-as-latent.md` has the idea but needs tightening.

3. [ ] **Endorsement definitions** — Selection vs Control endorsement with full formulas. `agency-via-endorsement.md` is a first pass but written hastily.

### Phase 2: The Core Argument
**Goal:** State and prove the main theorem(s).

4. [ ] **Unified agency definition** — What makes situations "belong to the same agent"? `formal-single-agent.md` has material but needs integration with condensation framing.

5. [ ] **Decision-determination formalized** — Using condensation language: I(E; D_B | Π) = 0. Connect to `fair-environment-theorem.md`.

6. [ ] **Main theorem statement** — Unified agency + DD + control endorsement → UDT formula

7. [ ] **Proof** — Either formal (Lean) or semi-formal with clear steps

### Phase 3: Extensions and Connections
**Goal:** Show the framework handles the full landscape.

8. [ ] **IBE integration** — How does the tripartite I/B/E structure refine the bipartite model? When does it matter?

9. [ ] **Multi-instance treatment** — Instances as values of external observation. Self-trust as non-interference.

10. [ ] **Computational story** — UDT1.01, logical uncertainty, plannable observations

### Phase 4: Writing Up
**Goal:** Produce the paper.

11. [ ] **Examples section** — Newcomb, Transparent Newcomb, Coordination buttons, worked through in the framework

12. [ ] **Objections section** — Address [scrubbed], circularity concerns, etc.

13. [ ] **Full draft**

---

## Key Questions To Resolve (Collaboratively)

1. **Is the bipartite A/E model sufficient, or do we need IBE from the start?**
   - Bipartite is simpler; IBE handles self-modification
   - Suggestion: Start bipartite, extend to IBE when needed

2. **How exactly does endorsement connect to condensation?**
   - Current attempt in `agency-via-endorsement.md` uses Π as the thing being endorsed
   - Is this the right level of abstraction?

3. **What's the exact statement of the main theorem?**
   - Need to nail down: premises, conclusion, what's trivial vs substantive

4. **How do we handle the "every policy in support is optimal" issue?**
   - Control endorsement seems to require this
   - Is this too strong? Or is it actually what we want?

5. **Selection vs Control: Is there a clean boundary?**
   - Current framing: pure vs impure utility
   - But "meaning & agency" suggests you can slide between them by encoding beliefs in U

---

## Notes for Collaborative Work

- This document is for working in Obsidian with AI completion
- Aim to write sentences you actually endorse, not generate slop
- When stuck, articulate the specific question rather than generating more prose
- The goal is a paper, not a collection of fragments

