---
title: "Unbounded Embedded Agency: AEDT w.r.t. rOSI"
author: Cole Wyeth
posted: 2025-07-20
source: https://www.lesswrong.com/posts/B6gumHyuxzR5yn5tH/unbounded-embedded-agency-aedt-w-r-t-rosi
karma: 36
comments: 0
fetched: 2026-08-22 via LessWrong GraphQL (contents.markdown, raw LaTeX preserved)
---

> **Note (2026-08-22):** this is the *current* version of the post, fetched via the LessWrong GraphQL API with raw LaTeX. It differs from the 2025-07 Logsidian copy (`lesswrong-post--logsidian-annotated-copy-2025-07.md`): Theorem 1 has been restated ("There is a reflective oracle relative to which, for every $\varepsilon>0$, $w(\xi^{\pi_S}|h_{<t}) > 1-\delta$ implies $V^{\pi_S}_\xi(h_{<t}) > V^*_\xi(h_{<t}) - \varepsilon$") and re-proved via a modified reflective-oracle fixed-point construction ("resetting the subtree"), citing Wyeth's *Limit-Computable Grains of Truth* paper (arXiv:2508.16245). The old Lemma 1 / Lemma 2 proof is gone. The LW API reports 0 comments.

# Unbounded Embedded Agency: AEDT w.r.t. rOSI

\(\) *Epistemic status: This post synthesizes 1.5 years of research insights supported by the Long-Term Future Fund. Parts are higher context (comparisons with* [*hardened AIXI*](https://www.lesswrong.com/posts/WECqiLtQiisqWvhim/free-will-and-dodging-anvils-aixi-off-policy) *and* [*joint AIXI*](https://arxiv.org/abs/2505.17882)) but you don't actually need much math to follow - in particular this post pretty much uses reflective oracles as a black box, and everything else has short inferential distance assuming basic familiarity with [*AIXI*](https://www.lesswrong.com/w/aixi) *and reinforcement learning. Most readers should skip the highly compressed technical summary below - the rest of the post is pretty friendly, except the proof of the theorem.*

**Highly compressed technical summary \[NOT intended to be widely legible\]:** A preliminary investigation of action evidential decision theory with respect to reflective oracle Solomonoff induction on the joint action/percept sequence shows that it solves some problems of ideal embedded agency and mimics Bayes-optimal sequential planning under a self-trust assumption. 

AIXI is not an embedded agent. It interacts with its environment from the outside, like this:

![](http://res.cloudinary.com/lesswrong-2-0/image/upload/v1672577367/mirroredImages/i3BTagvt3HbPMx6PN/ekude8k13w2p8nm8mhfc.png)

The red arrows indicate that the environment sends AIXI percepts and AIXI sends the environment actions. This is the only way they affect each other. 

I stole the picture from this [great (but long) post](https://www.lesswrong.com/posts/i3BTagvt3HbPMx6PN/embedded-agency-full-text-version) of `Garrabrant and Demski`. A shorter (and slightly more formal) version is [this paper on realistic world models](https://intelligence.org/files/RealisticWorldModels.pdf) from Soares. Since all of these individuals have been or are currently MIRI researchers, I'll lump their views together as the views of (typical) MIRI researchers.

In their work, MIRI researchers pointed out various ways that AIXI's assumption causes it to fall short of a complete mathematical model for artificial superintelligence (ASI). For instance, AIXI can't natively reason about the environment changing its source code (your video game will not reach out of the console and perform brain surgery on you). Also, AIXI is computationally unbounded, but a real agent running on a computer has computational bounds - and since its computational substrate is strictly smaller than (and contained in) the environment, it presumably can't compute everything that is happening in the environment. [^4ldhsz2mr3t]

I'm an AIXI enthusiast, so I wanted to investigate these limitations more rigorously. I've [argued for this approach](https://www.lesswrong.com/s/sLqCreBi2EXNME57o) in the past: since AIXI is kind of a common point of departure for many agent foundations agendas, it seems worth understanding it well. 

Before getting into the details though, I think it's worth observing that MIRI researchers are setting a very high bar here. A rigorous theory of embedded agency would be a rigorous theory of ASI design - it would basically have to solve everything except alignment, which would hopefully be a corollary. Specifically, computational boundedness is very hard - it asks for an agent that actually runs efficiently. Stuart Russell has [phrased the AI problem](https://arxiv.org/abs/cs/9505103) in terms of bounded rationality. It seems like a complete solution must be something like an optimal program for your physical machine (or better, programs for machines of every size). Even an approximate solution seems to solve AI in practice. Again, that's a lot to ask. 

+++ Prospects for a theory of bounded rationality

I no longer believe (or rather, I newly disbelieve) that the theory of AIXI can directly address the problems related to bounded rationality. AIXI just isn't computationally bounded, which means that it would not need to think about using bounded cognitive resources or taking advantage of external computation like calculators or scratchpads.[^f9r6lwgh4h] I initially tried to think of some meta-cognitive AIXI sending a few bits of advice to a lower-level bounded reasoning engine, but ultimately AIXI-level compute seems to just be too powerful and I think there's not much of interest to say here. Studying AIXI approximations may yield progress though - that's sort of how the model is intended to be used after all.

Existing agent foundations research directions try to tackle computational bounds by studying computational uncertainty (that is, uncertainty about the results of computations). Roughly speaking, there are two approaches to this: try to put probabilities on uncertain computational statements or don't. UDT falls in the former group and IB falls in the later. A proper approach to UDT seems to go through much of computational complexity theory, so I think it will be hard to find (the current SOTA proposals boast of beating all polynomial time heuristics, but are unfortunately exponential time themselves). IB seems more promising the more I look into it - it is basically trying to invent algorithms with provably good properties, which is a sort of frequentist approach. However, I suspect that relying on this kind of tinkering means it may be hard to demonstrate you have a good model of ASI (which could have tinkered further than you!) unless you're only trying to model the ASI you actually built - and then you have to push the theory far enough to get a blueprint for (safe) ASI.

+++

I'm interested in the easier (?) problem: how should a computationally *unbounded* embedded agent act?[^cj9hyifbkat]

It's not a priori obvious that this a well-defined question. All agents embedded in a computationally bounded universe must be computationally bounded themselves, so we risk constructing a "theory of nothing." We can of course take the limit of increasing compute, but the result may be path dependent - it might matter how compute scales differentially across the agent/environment system. 

On the other hand, it seems like some problems of embeddedness really have nothing to do with computational bounds. For instance, the possibility that the environment might corrupt your source code seems to have more to do with side-channels than computational bounds. Some forms of anthropic and evidential reasoning seem to fall into the same category.

In previous work, I've created some formal frameworks to talk about aspects of embedded agency. These include evidential learning from one's own actions and robustness to side-channel corruption. In this post, I want to investigate how a reflective oracles handle these problems. This leads to the construction of a reflective AIXI generalization which I think combines the virtues of some of my previous ideas (actually, in many cases, Marcus Hutter's ideas which I formalized). This agent follows sequential evidential decision theory (SAEDT) with respect to reflective oracle Solomonoff induction (rOSI) as joint action/percept history distribution.[^sll47oeadz9] For short, I'll call this agent self-reflective AIXI (which turns out to respect previous terminology - conveniently, it combines ideas from Self-AIXI and reflective AIXI). Next I'll discuss prospects for alignment applications and further development of this theory.

I don't think there's much novel math here, and none of it is deep - at least when you factor out the existence of reflective oracles. I'm mostly trying to tie my thinking together into a cohesive research program.

Standard Notation
-----------------

$\epsilon$ : the empty string

$\varepsilon$, $\delta$ : (small) positive numbers, NOT the same as $\epsilon$

$\gamma_t$ : discount factor at time $t$, a positive number.

$\Gamma_T$: tail some of discount factors $\sum_{t=T}^\infty \gamma_t$ 

$Q^\pi_\nu$ : the action-value function for policy $\pi$ and environment $\nu$

$V^\pi_\nu$ : the (state) value function for policy $\pi$ and environment $\nu$  

Loosening the Dualistic Assumption 
-----------------------------------

That picture I opened with (of AIXI playing a video game) accurately describes its "ontology." AIXI really believes that the environment is a (Probabilistic Turing) machine that it can (only) exchange messages with. Specifically, action $a_t$ is sent at time $t$, and then percept $e_t := o_t r_t$ is received (where $o_t$ is an observation and $r_t$ is a reward). That means AIXI "only does Solomonoff induction on the percepts" with the actions as an additional input. Marcus Hutter made this formal by defining "chronological semimeasures," so in a sense AIXI does "Solomonoff-Hutter" induction, rather than ordinary Solomonoff induction. This is basically the move that MIRI objects to most loudly.

We can write $\nu(e_{1:t} ||a_{1:t})$ to describe a belief distribution that treats actions as received on such a distinguished input channel (or "tape") and then randomly generates the percepts. AIXI uses a Bayesian mixture of this form, the universal lower semicomputable chronological semimeasure $\xi(e_{1:t}||a_{1:t})$. Chronological means the actions and percepts are exchanged in the right order. You don't need to know what the rest of those words mean to understand this post.

Years ago, when I first started working with Professor Hutter, I convinced myself that I had brilliantly solved this problem - just do Solomonoff induction on the whole sequence, including actions and observations! 

You can totally do this! But it causes other problems - it's a worse theory of intelligence.

First of all, it's not so clear how planning should work any more. 

Do you even plan ahead? If so, do you update in advance on all the actions you plan to take? [This paper](https://arxiv.org/abs/1506.07359) formalizes two approaches to planning ahead in evidential decision theory. 

Since we are treating our future actions as uncertain, I think it is more natural to plan only one step ahead (what I call *action evidential* decision theory as opposed to the previous paper's sequential action evidential decision theory).

$\pi_S(h_{<t}) = a^*_t \in \text{argmax}_{a_t} Q_\xi(a_t, h_{<t}) := \text{argmax}_{a_t} \mathbb{E}_{\xi}[\sum_{i=t}^\infty \gamma_i r_i | h_{<t}a_t]$

where $h_{<t} := a_1e_1a_2e_2...a_{t-1}e_{t-1}$

A similar approach is advocated by the [Self-AIXI](https://openreview.net/pdf?id=psXVkKO9No) paper, which we will return to later. 

Either way, the problem is that the action sequence is no longer computable (or even lower semicomputable). AIXI is too smart for AIXI to be able to understand it - so we can't guarantee that it ever learns to predict the future. 

Actually, this isn't trivially obvious, since predicting only the percepts might be good enough for the sequential planning approach (which intervenes on the actions anyway), and the percepts are still (lower semi)computable as a function of the actions, loosely speaking. I wrote [a paper](https://arxiv.org/abs/2505.17882) with Marcus Hutter about the resulting (potential for) convergence failure, and it can occur under sufficiently unfortunate action choices (though we don't know whether AIXI actually takes these unfortunate actions). However, a weak positive convergence result can be proven by renormalizing the universal distribution. Clearly the situation is messy - it seems MIRI had a point about this one.

Adding a reflective oracle completely solves this problem - when $\xi$ is chosen as rOSI, the resulting $\pi_{S}$ is reflective oracle computable (rO-computable) by essentially the same trick used to construct [reflective AIXI](https://intelligence.org/files/ReflectiveSolomonoffAIXI.pdf). This means that ordinary merging-of-opinions results apply.

What do we get out of this approach? Well, learning about the environment from our own actions seems useful. For instance, it should effect the agent's behavior in games against copies of itself - other agents known to have the same source code. Here we would probably want to use a specially chosen ["cooperative" reflective oracle](https://www.lesswrong.com/posts/SgkaXQn3xqJkGQ2D8/cooperative-oracles). I haven't studied this yet. Another question I am interested in is "what actually happens if such an agent reads its own source code?" Presumably it would become certain of its future decisions, which seems to mean conditioning on impossible counterfactuals (another complaint of MIRI). A direct answer is that is not possible for this to actually cause a divide-by-zero error because rOSI never assigns 0 probability to any (finite) action/percept history. **Still, it seems worth investigating what happens when certain action probabilities are driven very close to zero through the learning process (an as-yet under-specified open problem).**

Evidential learning seems to be the main "advantage" when sequential planning is used, but we chose one-step-ahead planning for an additional advantage: it doesn't assume that we will control all of our future actions. 

Radiation Hardening AIXI
------------------------

One of the examples in Soares' critique of AIXI is the "Heating Up" game:

> **The Heating Up game.** An agent A faces a box containing prizes. The box is designed to allow only one prize per agent, and A may execute the action P to take a single prize. However, there is a way to exploit the box, cracking it open and allowing A to take all ten prizes. A can attempt to do this by executing the action X. However, this procedure is computationally very expensive: it requires reversing a hash. The box has a simple mechanism to prevent this exploitation: it has a thermometer, and if it detects too much heat emanating from the agent, it  
> self-destructs, destroying all its prizes.

He argues that AIXI is not equipped to solve this problem, because it does not understand itself as computed by a piece of hardware, so can never conceive of the possibility that thinking for longer might cause it to heat up. I think this example is not very good. Insofar as an AIXI approximation controls which computations are running on its hardware, it will absolutely learn any correlates of this in the environment. If the AIXI approximation doesn't control how its compute is used then it kind of faces an unfair problem here - but it will still be able to predict that it will heat up in this situation, given some experience of similar situations. The details depend on where you put the boundary around the thing you treat as an AIXI approximation. 

Anyway, I suggest an improved version of this example where heating up actually overheats the AIXI approximation's hardware, so that it takes unintended decisions. In this case, AIXI really wouldn't learn to predict this, because it does not predict its own decisions, it plans them.[^zky7dmaccu] 

A simpler version (suggested by Samuel Alexander) is a robot designed to clean up a nuclear disaster site. Some rooms might have high levels of radiation, which could flip bits and cause the robot to misbehave. Naively, AIXI would never learn this - it would keep going back into the room planning to "just behave properly" this time.

Previously, I formalized this by adding an action corruption function $f$ which may depend on both the past/present actions and the past/present percepts. Then I proposed a variation on AIXI (invented by myself and Professor Hutter) which recalculates its own "true" action history at every step, and is able to "externalize" action corruption. I now call this "hardened AIXI" after radiation hardening.

[Here is the post](https://www.lesswrong.com/posts/WECqiLtQiisqWvhim/free-will-and-dodging-anvils-aixi-off-policy) \- the rest of this section is easier to understand if you've read it.

**How does self-reflective AIXI deal with action corruption?** I would argue pretty well. Technically the argmax over $a_t$ is only what we want when our agent actually gets to pick its current action. That means $\pi_S$ doesn't handle adversarial action relabeling in the way that hardened AIXI does: if $f$ always swaps $a_1$ and $a_2$, and $\pi_S$ wants to take $a_1$, it just selects $a_1$. But this seems like a fairly reasonable answer: the point of a decision theory is to tell us which action we want to take, if we have control. $\pi_S$ is telling us the result it wants "after corruption." But otherwise it natively handles the situation without adding a hardening patch, which is nice. Below I'll be a little more formal about this.  

**Some contrived examples.** Assume that the environment $\nu$, policy $\pi$, and action corruption function $f$ are all rO-computable. Then the situation is realizable and (the reflective) $\xi$ learns correct prediction on-policy. If we assume also that $f$ always has some fixed $\delta > 0$ chance of selecting any action[^o19anrc70wg] then we even have

$Q_\xi(a_t,h_{<t}) \rightarrow Q^{f \circ \pi}_\nu(a_t,h_{<t})$

Setting $\pi = \pi_S$, this means that in the limit $\pi_S$ selects an $\varepsilon$-optimal action! However, technically the "external" policy we care about is $f \circ \pi_S$ which does the true action selection. Intuitively, it seems that $f \circ \pi_S$ is properly satisfying the Bellman equations "when $\pi_S$ is in control." 

Here is a much stronger set of assumptions that makes this idea explicit: 

Assume that there are two types of action corruption. In "out-of-control" situations, $f$ does not depend on $a_t$ at all. In "noisy" situations, $f$ just has a uniform $\delta < 1/|\mathcal{A}|$ chance of switching $a_t$ to some other action in the action space $\mathcal{A}$. Then $\pi_S$ takes the best action (accounting for corruption!) in noisy situations and trivially takes a best action (that is, any action) in out-of-control situations.

Convergence Under a Self-Trust Assumption
-----------------------------------------

I am interested in understanding when self-reflective AIXI converges to AIXI. This is desirable roughly when the dualistic assumptions are actually satisfied (and the agent can be reasonably expected to learn this). This is one test for whether a theory of embedded agency makes any sense - it is the same test I applied to joint AIXI. 

A similar convergence analysis was carried out (but not completed) for [Self-AIXI](https://openreview.net/pdf?id=psXVkKO9No), which is a minor variation on joint AIXI that maintains separate distributions over its own policy and the environment, drawn from hypothesis classes $\mathcal{P}$ and environment class $\mathcal{M}$. This doesn't make much sense as a theory of embedded agency; it was actually motivated as a theoretical model of policy distillation. 

We can describe it more formally as follows:

An  **environment distribution** is given by:

$\psi(e_t|h_{<t}a_t) = \sum_{\nu\in\mathcal{M}} w(\nu|h_{<t}) \nu(e_t|h_{<t}a_t) \text{ where } w(\nu|h_{1:t}) := w(\nu|h_{<t})\frac{\nu(e_t|h_{<t}a_t)}{\psi(e_t|h_{<t}a_t)}$

with prior probability $w(\nu|\epsilon) = w(\nu)$. 

(Unlike the paper, I chose $\psi$ for this environment mixture to reserve $\xi$ for the universal distribution on the joint history.)  

And a **policy distribution** is given by

$\zeta(a_t|h_{<t}) = \sum_{\pi\in\mathcal{P}} \omega(\pi|h_{<t}) \pi(a_t|h_{<t}) \text{ where } \omega(\pi|h_{1:t}) := \omega(\pi|h_{<t})\frac{\pi(a_t|h_{<t})}{\zeta(a_t|h_{<t})}$

with some prior probability $\omega(\pi|\epsilon) = \omega(\pi)$.[^2c49ccvmvnb]

Note that $w$ and $\omega$ are updated separately, depending only on percepts and actions respectively. This is superficially different from joint AIXI.

Interestingly, there is actually little difference when the classes are taken as rO-computable mixtures. This is a nice "lego block" property of the rO-computability; an rO-machine is completed to a Markov kernel yielding conditional probabilities which you can just snap together to form a joint distribution.

Speaking more formally:

There is an rO-machine that uses $\zeta$ for action symbols and $\psi$ for environment symbols, so the joint distribution (usually written) $\psi^\zeta$ is rO-computable. This means that $\xi \geq \psi^\zeta$ up to a constant factor (the prior probability of $\psi^\zeta$).

Similarly, since $\xi(e_t|h_{<t}a_t)$ is rO-computable, it's the case that 

$\psi(e_{1:t}||a_{1:t}) \geq w(\xi)\prod_{i=1}^t \xi(e_i|h_{<i}a_i)$

and similarly 

$\zeta(a_{1:t}||e_{<t}) \geq \omega(\xi) \prod_{i=1}^t \xi(a_i|h_{<i})$

Taking the product yields 

$\psi^\zeta \geq w(\xi)\omega(\xi)\xi$  

Which yields

**Observation 1:** $\xi = \psi^\zeta$ up to a constant factor. 

In the reflective oracle setting, the difference between Self-AIXI's dualistic belief distribution and self-reflective AIXI's joint belief distribution is, in some sense, epistemic but not ontological, and it makes surprisingly little difference. It's essentially just an inductive bias. Or, in other words: Self-AIXI approximately learn that it is an embedded agent, and self-reflective AIXI can learn that it isn't!

Therefore my choice to use the joint distribution for self-reflective AIXI is not that important, but only a simplification (again, none of this is proven for ordinary AIXI, and in fact we proved a related negative result that the joint distribution restricted to the percepts does not dominate the universal chronological semimeasure). 

Now we are prepared to discuss the convergence results in the Self-AIXI paper. The paper has some good ideas, but also some serious flaws and gaps:

1: It requires $\pi_S \in \mathcal{P}$  but demonstrates no such example. This can be easily fixed with reflective oracles, as I have informally described. *Note that this fact pretty much screens off the other details of reflective oracles from the rest of my analysis - I'm actually coming to believe that the role of programs in AIT is mostly as a type of building block with sufficiently rich compositional / recursive structure to ease the construction of belief distributions with interesting properties, and this feature remains useful independently of any ontological commitments to a computable universe or even epistemological commitments to computable mindspace.*

2: The paper introduces a technical assumption called "reasonable off-policy" which is inscrutable and essentially assumes the conclusion. 

The follow example (suggested by Diffractor) illustrates how the "reasonable off-policy" assumption can fail:

**Sink or swim.**  The agent wants to move from one island to another, but would much rather stay put than drown. Fortunately, the agent is an excellent swimmer and could easily swim to the other island if it jumped into the water. However, after jumping into the water, it could also choose to sink and drown.

![](https://39669.cdn.cke-cs.com/rQvD3VnunXZu34m86e5f/images/409bf46142744a07e8aee4aed5c168195d12acd0a0425f94.png)

The answer seems obvious: jump in, and then swim to the next island. That is the optimal policy. 

However, we have constructed an agent which is not certain it can trust itself to act as planned. This uncertainty may prevent the agent from jumping in and finding out that it will actually swim. A similar type of uncertainty blocking exploration is an obstacle for convergence in AIXI (or any Bayesian agent that believes the environment may contain inescapable traps). It just seems more jarring in this case because the agent could be built to trust itself by planning ahead sequentially - but that would prevent it from reasoning about action corruption through side-channels! There seem to be some inherent tradeoffs here.

The "reasonable off-policy" requirement (which I haven't reproduced here) basically encodes, in an obfuscated way, the knowledge that if you jump in you will actually swim, despite never having jumped in before.

Here is a much more transparent convergence result of the same flavor. Assume for simplicity that rewards are shifted and rescaled to \[0,1\]. The inspiration for this result is that when $\xi = \psi^{\pi_S}$, then $\pi_S$ satisfies the Bellman equations for $\psi$ and can be shown optimal.[^sfp5x0qbhs] In fact, MIRI relied on this logic implicitly to construct reflective AIXI. Intuitively, this result should be "continuous in $\xi$," and it is, though I found this slightly harder to show than expected because of the self-referentiality involved - $\pi_S$ is actually discontinuous in $\xi$ because of the argmax. However, we can still show the result in two steps, by showing that $\pi_S$ takes an $\varepsilon'$-optimal action for $\pi^*_\psi$, and then showing that this means $\pi_S$ is actually $\varepsilon$-optimal itself.

For simplicity I will phrase the argument in terms of the value function $V^{\pi_S}_\psi$ at $t=0$ but it generalizes automatically to conditionals on a finite history prefix. 

The significance of this result is that you don't need to directly assume you are (near)optimal. You just need to believe that you are probably doing action-evidential decision theory with rOSI. The result says that this consistent self knowledge is enough for near optimality: "If you are locally optimizing and expect to continue, you are nearly globally optimal." Importantly, this result doesn't require dogmatic Cartesian dualism: if it turns out that the environment sometimes corrupts its actions through side-channels, self-reflective AIXI can learn this (the inductive bias we built in can be washed out).

**Theorem 1 (**$\delta$-**Self-Trust is** $\varepsilon$-**Optimal):** There is a reflective oracle relative to which, for every $\varepsilon > 0$,  $w(\xi^{\pi_S}|h_{<t}) > 1 - \delta$ implies $V^{\pi_S}_\xi(h_{<t}) > V^*_\xi(h_{<t}) - \varepsilon$. In particular, $\pi_S$ remains $\varepsilon$-(Bayes)optimal for all time with high probability.

**Proof sketch:** 

In the existence proof for reflective oracles, there is a fixed point argument for a certain point-set map $f$. The points are in a space of pairs (query, eval) for each machine and history, where query specifies the oracle's answer and eval the machine's behavior; informally, $f$ enforces consistency between these values by mapping each (query,eval) pair to a set of (query', eval') pairs where eval' is consistent with query[^0kc62ztblax] and query' is consistent with eval, so that a fixed point is self-consistent. See e.g. [my paper](https://www.arxiv.org/abs/2508.16245) for a detailed definition. To ensure the trust property, we will redefine the behavior of $f$ when the machine is $\pi_S$ in order to pick a good fixed point.

Normally, eval' would be constrained to agree with the machine's computation given that O responds according to query. Our new $f$ also enforces that $\pi_S$ is supported on actions with value at least $w(\pi_S|h_{<t})V^*_\xi(h_{<t})$ as assessed by eval. The computation normally performed by $\pi_S$ is to randomized among actions that maximize $Q_\xi(h_{<t}a_t)$, and according to eval' it will do this as usual unless

$\text{argmax}_{a_t} Q_\xi(h_{<t},a_t) < w(\pi_S|h_{<t})V^*_\xi(h_{<t})$

in which case we say that $h_{<t}$ violates the trust bound. Both (action)value functions are rO-computable,  so we can check them "locally" with eval which must be accurate about such computations at fixed points - though we have to prove below that this is still so, after the following modification. For all minimal prefixes $h_{<t}$ that violate the trust bound, eval' of $\pi_S$ on all extensions $h_{<t}h_{t:T}$ is modified to behave as $\pi^*_\xi$.  I call this resetting the subtree of $h_{<t}$. Then $\pi_S(h_{<t})$ can be supported on a set of actions with sufficiently high value according to $\xi$, because simply acting as $\pi^*_\xi(h_{<t})$ has value $V^*_\xi(h_{<t})$ with probability at least $w(\xi^{\pi_S}|h_{<t})$ (which eval should "know" at fixed points).

This modified $f$ is nonempty and can easily be chosen convex and closed. Also, $f$ remains upper semicontinuous because we only reset the subtree when a strict inequality is satisfied. Therefore, $f$ has a fixed point by the infinite dimensional Kakutani fixed point theorem. 

Now we need to know that the resulting fixed point actually corresponds to computation with access to a reflective oracle - in other words, that eval is accurate. We have only changed eval on queries about $\pi_S$. Consider any history prefix $h_{<t}$. At the fixed point, either $h_{<t}$ is in a reset subtree, or it is not. If not, $\pi_S$ always performs its normal computation on $h_{<t}$ (possibly after resetting its subtree, but we are at a fixed point so this reset has no effect). If $h_{<t}$ is in a reset subtree, then $\pi_S = \pi^*_\xi$ on this whole subtree. But at a fixed point, eval knows this - Q and V are computed normally, since their computation is not performed by machine $\pi_S$ (though it may make queries about $\pi_S$), and the trust bound is not violated according to eval. But this means the subtree was not reset, a contradiction!

So at a fixed point, no subtrees are reset, and O is a reflective oracle.

Directly from the construction, $w(\xi^{\pi_S}|h_{<t}) > 1 - \delta$ implies that $\pi_S(h_{<t})$ is $\delta$-(Bayes)optimal. This is almost sufficient for the result, but we also need to know that later actions can be made near optimal with high probability, which is true as long as $w(\xi^{\pi_S}|h_{<t}h_{t:T})$ remains above $1 - \delta$. This is not certain because $\pi_S$ will have to flip coins to pick between actions of equal value, which implies a small chance that $w(\pi_S|h_{<t})$ declines as $t$ increases. But conditioning on true policy $\pi_S$, we can use a martingale argument to show that $n$ bits of evidence against $\pi_S$ has probability less than $2^{-n}$. This small chance of $\pi_S$ going insane can be absorbed into $\varepsilon$.

Closing Thoughts and Future Work
--------------------------------

It seems to me that MIRI wanted to be able to embed an agent's code inside a larger piece of code and evaluate its performance. When everything is an rO-machine, this is totally possible. These machines are like... flexible lego blocks. You can snap them together however you want, but Observation 1 suggests that updating treats whatever structure you build this way like a weak suggestion. This means that the resulting agents may not have very dogmatic beliefs. I am not sure whether this is good. 

In this setting, self-trust has a "basin of attraction" which depends on non-dogmatically elevating the weight on a certain hypothesis. Playing with prior weights like this feels very clumsy. I think it would be nicer to build in knowledge through logical statements, perhaps using Hutter et al.'s (uncomputable) [method](https://arxiv.org/abs/1209.2620) for assigning probabilities to logical statements. If I understand correctly, this is vaguely related to the type of tiling properties the corpus author and his collaborators study in the computationally bounded setting using UDT. I am not satisfied with the current versions of UDT (and as explained above, I think there are good reasons to expect it is very hard to find a satisfactory theory of computational uncertainty). But of course rO-computability is not realistic and eventually we must move beyond this idealized setting.

I think reflective oracles are a reasonable model for agents of similar intelligence reasoning about each other or about agents of lower intelligence than themselves. This seems sufficient for modeling CIRL between idealized agents of equal power, which would be an interesting case to evaluate next.

Appendix: Original Broken Argument
----------------------------------

**Theorem 1 (**$\delta$-**Self-Trust is** $\varepsilon$-**Optimal):** Let the true environment $\psi$ be deterministic. For any $\varepsilon>0$, there exists a $\delta>0$ such that if $\xi \geq (1-\delta)\psi^{\pi_S}$, then $\pi_S$ is $\varepsilon$-(Bayes-)optimal for environment $\psi$. If only one action is (Bayes-)optimal for $\xi$ at every time step $t$ and discounting is geometric, then $\pi_S$ remains $\varepsilon$-optimal at all times with high probability.

**Proof:**   

Let $T_\varepsilon$ be the minimal time such that $\Gamma_T := \sum_{t=T}^\infty \gamma_t < \varepsilon$. I'll also assume that the sum of discounts is 1. The following lemma is designed to prove that the action chosen by $\pi_S$ is near-optimal *for the optimal policy* $\pi^*_\psi$.

**Lemma 1:** Assuming that $\xi(\cdot|h_{<t}) \geq (1-\delta)\psi^{\pi_S}(\cdot|h_{<t})$ for $t \leq T_\varepsilon$ and $h_{<t}$ satisfying  $\pi_S(a_i|h_{<i}) > 0$,

$Q_\xi(a_t,\epsilon) \geq Q^{\pi^*_\psi}_\psi(a_t,\epsilon) - \varepsilon  - T_{\varepsilon}\delta$

**Proof:** Let $\bar{\xi} := \frac{1}{\delta}(\xi - (1-\delta)\psi^{\pi_S})$. By linearity,

$Q_\xi(a_1,\epsilon) = \delta Q_{\bar{\xi}}(a_t, \epsilon) + (1-\delta) Q_\psi^{\pi_S}(a_1,\epsilon) \geq (1-\delta) Q_\psi^{\pi_S}(a_1,\epsilon) \geq Q_\psi^{\pi_S}(a_1,\epsilon) - \delta$

But this is

$= \frac{1}{\Gamma_1}\mathbb{E}_{e_1 \sim \psi(\cdot|a_1)} [\gamma_1r_1 + \Gamma_2V^{\pi_S}_\psi(a_1e_1)] - \delta$

We can expand the value function in terms of the max of another action-value function. Iterating to \(\)depth $T_\varepsilon$, **\[This is the gap, the expansion is wrong because action-values / value functions off-policy are wrong\]**

$\geq \mathbb{E}_{e_1} \max_{a_2} ... \max_{a_{T_\varepsilon}} \mathbb{E}_{e_{T_\varepsilon}} [\frac{1}{\Gamma_1}\sum_{t=1}^{T_\varepsilon} \gamma_t r_t + \frac{\Gamma_{T_\varepsilon}}{\Gamma_1}V^{\pi_S}_\psi(h_{1:{T_\varepsilon}})] - \frac{\sum_{t=1}^{T_\varepsilon} \Gamma_t}{\Gamma_1}\delta$

Now we use the definition of $T_\varepsilon$ to observe $\frac{\Gamma_{T_\varepsilon}}{\Gamma_1} < \varepsilon$, and observe that all value functions are in \[0,1\]. This means we can substitute the optimal value function at a maximum cost of $\varepsilon$. Also, since $\Gamma_t$ is decreasing we can simplify the last fraction.  \(\)

$\mathbb{E}_{e_1} ... \max_{a_{T_\varepsilon}} \mathbb{E}_{e_{T_\varepsilon}} [\frac{1}{\Gamma_1}\sum_{t=1}^{T_\varepsilon} \gamma_t r_t + \frac{\Gamma_{T_\varepsilon}}{\Gamma_1}V^{\pi^*_\psi}_\psi(h_{1:T_\epsilon})] - \varepsilon - T_\varepsilon\delta$

$= Q^{\pi^*_\psi}_\psi(a_1,\varepsilon) - \varepsilon - T_\varepsilon \delta$

Okay, that could possibly have been cleaner, but Lemma 1 is proven. 

Lemma 1 tells us that $\pi_S$does not badly underestimate the value function. We actually need to know that $\pi_S$ does not badly overestimate the value function as well: 

**Lemma 2:** Assuming that $\xi(\cdot|h_{<t}) \geq (1-\delta)\psi^{\pi_S}(\cdot|h_{<t})$ for $t \leq T_\epsilon$, 

$Q_\xi(a_t,\epsilon) \leq Q^{\pi^*_\psi}_\psi(a_t,\epsilon) - \varepsilon  - T_{\varepsilon}\delta$

**I brush the proof of this lemma under the rug.** This case is more straightforward - as long as $\xi$'s percept distribution is close to $\psi$, no policy can outperform the optimal value function by much. I won't prove this explicitly - we can instead recite something about continuity of linear functional application. I assumed that $\psi$ is deterministic to ensure that $\xi$ never diverges from $\psi$ on percept bits. We can avoid this assumption by using Self-AIXI instead of self-reflective AIXI, and simply telling it the environment is $\psi$.  

**Proof of theorem:** We established at some effort that we can ensure each action is near optimal (for the optimal policy). Now we will find $\delta'$ so that $\xi(\cdot|h_{<t}) \geq (1-\delta')\psi^{\pi_S}(\cdot|h_{<t})$ ensures that each action is within $\varepsilon' = \frac{\varepsilon}{2T_{\varepsilon/2}}$of optimal. This is slightly tedious; let $T^t_\varepsilon$ is the minimum time satisfying $\Gamma_{T^t_\varepsilon}/\Gamma_t < \varepsilon$.  Given $\epsilon > 0$, we apply Lemma 1 to $\varepsilon' := \varepsilon/4T_{\varepsilon/2}$, then choose $\delta' < \min_{t \leq T_{\varepsilon/2}} \varepsilon'/T^t_{\varepsilon'}$. This choice ensures that every action chosen by $\pi_S$ is $2\varepsilon'$-optimal. Finally,

$V^{\pi_S}_\psi(\epsilon) - V^{\pi^*_\psi}_\psi(\epsilon) = \mathbb{E}_{a_t \sim \pi_S} Q^{\pi_S}_\psi(a_t,\epsilon) - \max_{a_1} Q^{\pi^*_\psi}_\psi(a_1,\epsilon)$

$= \mathbb{E}_{a_1 \sim \pi_S} [Q^{\pi_S}_\psi(a_1,\epsilon) - Q^{\pi^*_\psi}_\psi(a_1,\epsilon) + Q^{\pi^*_\psi}_\psi(a_1,\epsilon)] - \max_{a_1} Q^{\pi^*_\psi}_\psi(a_1,\epsilon)$ 

Applying Lemmas 1 and 2 to the last pair of terms, 

$\geq \mathbb{E}_{a_1 \sim \pi_S} \mathbb{E}_{e_1 \sim \psi} \frac{\Gamma_2}{\Gamma_1} [V^{\pi_S}_\psi(a_1e_1) - V^{\pi^*_\psi}_\psi(a_1e_1)] - 2\varepsilon'$

$= \mathbb{E}_{a_1 \sim \pi_S} \mathbb{E}_{e_1 \sim \psi} \mathbb{E}_{a_2 \sim \pi_S(\cdot|a_1e_1)} \frac{\Gamma_2}{\Gamma_1} [Q^{\pi_S}_\psi(a_2,a_1e_1) - Q^{\pi^*_\psi}_\psi(a_2,a_1e_1) ] - 2\varepsilon'$

We can iterate by expanding the inner expectation. Repeating this process to depth $T_{\varepsilon/2}$, we obtain:

$\geq \mathbb{E}_{a_1} \mathbb{E}_{e_2} ... \mathbb{E}_{a_{T_{\varepsilon/2}}} \mathbb{E}_{e_{T_{\varepsilon/2}}}\frac{\Gamma_{T_{\varepsilon/2}}}{\Gamma_1} [Q^{\pi_S}_\psi(a_{T_{\varepsilon/2}},h_{<T_{\varepsilon/2}}) - Q^{\pi^*_\psi}_\psi(a_{T_{\varepsilon/2}},h_{<T_{\varepsilon/2}})]- T_{\varepsilon/2} 2 \varepsilon'$

$\geq - \varepsilon/2 - T_{\varepsilon/2} 2 \varepsilon'$

$= -\varepsilon$

That is,

$V^{\pi_S}_\psi(\epsilon) \geq V^{\pi^*_\psi}_\psi(\epsilon) - \varepsilon$

Finally.[^nm83eixcrp]

**The basin of attraction.** Now all that remains is to show that the conditions of Lemmas 1 and 2 can be maintained after updating. Informally, this is true as long as we can only receive a finite amount of evidence against $\psi^{\pi_S}$ at every step - in that case, a sufficiently large odds ratio $1-\delta:\delta$ for $\psi^{\pi_S}:\bar{\xi}$ will remain above $1 - \delta' : \delta'$ up to time $T_{\epsilon/2}$. By assuming $\psi$ deterministic, we ensured that percepts never provide evidence against $\psi^{\pi_S}$. The action chosen by $\pi_S$ are always of course consistent with $\pi_S$, but it will randomize between equivalent options (this is the trick that makes it rO-computable). It is possible for this to provide about $|\mathcal{A}|$ bits against $\pi_S$ in the worst case (under the standard construction for $\pi_S$), though in expectation of course $\pi_S$ predicts itself best. That is where the condition (needed for the stronger result that $\pi_S$ remains $\varepsilon$-optimal for all time) that only one action is \(\)Bayes-optimal for $\xi$ comes from. I assumed geometric discounting to ensure that $T^t_{\varepsilon}$ does not depend on $t$, which could probably throw things off. Interestingly, if there were always two Bayes-optimal actions for $\xi$, the evidence against $\pi_S$ would be a kind of "$\xi$-randomness deficiency," which is the reflective-oracle analogue of M.L. randomness deficiency. So, the theory of algorithmic randomness has a connection to the basin of attraction for self-trust! This is a little unexpected - proper algorithmic information theory doesn't seem to come up in the theory of AIXI as much as you would expect.

This concludes the proof.

[^4ldhsz2mr3t]: I've written more extensively about these complaints in many places, particularly here - but as long as you can make sense of this high-level intuitive description, you probably know enough to understand the rest of this post. 

[^f9r6lwgh4h]: The corpus author has called this the scratchpad problem, and is more or less solely responsible for convincing me of this point. 

[^cj9hyifbkat]: This is also the topic of Herrmann's PhD thesis, which is more philosophical and focused on action identification. 

[^sll47oeadz9]: I realize this is a lot of jargon for one sentence. But I have to admit, there is something about uniting these ideas into something it would have been hard to formulate from scratch that I find pleasing. It makes the discussion feel more paradigmatic. 

[^zky7dmaccu]: For AIXI, deliberation crowds out prediction. 

[^o19anrc70wg]: I am smuggling in a free exploration rate, which causes merging-of-opinions to do what I want it to, so that Lemma 4.17 of Jan Leike's thesis remains applicable after action selection. Informally, this avoids a divide-by-zero. 

[^2c49ccvmvnb]: The Self-AIXI paper is inconsistent about whether the policy distribution should be updated on the current action when comparing action-values. The intention seems to be to do so, and I follow this convention. 

[^sfp5x0qbhs]: By expanding the value function \(V^{\pi_s}_\psi\) in terms of the defining (arg)max's to arbitrary (finite) depth, we see the result dominates any finite-horizon value function, which can be shown equivalent to optimality at infinite horizon. 

[^0kc62ztblax]: ...and technically other eval at other points, because computation is encoded recursively. 

[^nm83eixcrp]: I have a feeling that someone better than me at measure theory (like Kosoy or Diffractor) could have done this proof so far backwards in heels and still taken half the lines. Since it is currently a bit of a mess, I wouldn't be surprised if e.g. there's the wrong constant in front of an \(\varepsilon\) somewhere.
