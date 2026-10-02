



===
Here is Cole's post about his new theorem:

# Unbounded Embedded Agency: AEDT w.r.t. rOSI

by Cole Wyeth
20th Jul 2025

*Epistemic status: This post synthesizes 1.5 years of research insights supported by the Long-Term Future Fund. Parts are higher context (comparisons with `hardened AIXI` and `joint AIXI`) but you don't actually need much math to follow - in particular this post pretty much uses reflective oracles as a black box, and everything else has short inferential distance assuming basic familiarity with AIXI and reinforcement learning. Most readers should skip the highly compressed technical summary below - the rest of the post is pretty friendly, except the proof of the theorem.*

**Highly compressed technical summary \[NOT intended to be widely legible]:** A preliminary investigation of action evidential decision theory with respect to reflective oracle Solomonoff induction on the joint action/percept sequence shows that it solves some problems of ideal embedded agency and mimics Bayes-optimal sequential planning under a self-trust assumption.

AIXI is not an embedded agent. It interacts with its environment from the outside, like this:

![](http://res.cloudinary.com/lesswrong-2-0/image/upload/v1672577367/mirroredImages/i3BTagvt3HbPMx6PN/ekude8k13w2p8nm8mhfc.png)

The red arrows indicate that the environment sends AIXI percepts and AIXI sends the environment actions. This is the only way they affect each other.

I stole the picture from this `great (but long) post` of `Garrabrant and Demski`. A shorter (and slightly more formal) version is `this paper on realistic world models` from Soares. Since all of these individuals have been or are currently MIRI researchers, I'll lump their views together as the views of (typical) MIRI researchers.

In their work, MIRI researchers pointed out various ways that AIXI's assumption causes it to fall short of a complete mathematical model for artificial superintelligence (ASI). For instance, AIXI can't natively reason about the environment changing its source code (your video game will not reach out of the console and perform brain surgery on you). Also, AIXI is computationally unbounded, but a real agent running on a computer has computational bounds - and since its computational substrate is strictly smaller than (and contained in) the environment, it presumably can't compute everything that is happening in the environment.^[I've written more extensively about these complaints in many places, particularly `here` - but as long as you can make sense of this high-level intuitive description, you probably know enough to understand the rest of this post.]

I'm an AIXI enthusiast, so I wanted to investigate these limitations more rigorously. I've `argued for this approach` in the past: since AIXI is kind of a common point of departure for many agent foundations agendas, it seems worth understanding it well.

Before getting into the details though, I think it's worth observing that MIRI researchers are setting a very high bar here. A rigorous theory of embedded agency would be a rigorous theory of ASI design - it would basically have to solve everything except alignment, which would hopefully be a corollary. Specifically, computational boundedness is very hard - it asks for an agent that actually runs efficiently. Stuart Russell has `phrased the AI problem` in terms of bounded rationality. It seems like a complete solution must be something like an optimal program for your physical machine (or better, programs for machines of every size). Even an approximate solution seems to solve AI in practice. Again, that's a lot to ask.

> [!NOTE]- Prospects for a Theory of Bounded Rationality
> I no longer believe (or rather, I newly disbelieve) that the theory of AIXI can directly address the problems related to bounded rationality. AIXI just isn't computationally bounded, which means that it would not need to think about using bounded cognitive resources or taking advantage of external computation like calculators or scratchpads.^[The corpus author has called this the scratchpad problem, and is more or less solely responsible for convincing me of this point.] I initially tried to think of some meta-cognitive AIXI sending a few bits of advice to a lower-level bounded reasoning engine, but ultimately AIXI-level compute seems to just be too powerful and I think there's not much of interest to say here. Studying AIXI approximations may yield progress though - that's sort of how the model is intended to be used after all.
> 
> Existing agent foundations research directions try to tackle computational bounds by studying computational uncertainty (that is, uncertainty about the results of computations). Roughly speaking, there are two approaches to this: try to put probabilities on uncertain computational statements or don't. UDT falls in the former group and IB falls in the later. A proper approach to UDT seems to go through much of computational complexity theory, so I think it will be hard to find (the current SOTA proposals boast of beating all polynomial time heuristics, but are unfortunately exponential time themselves). IB seems more promising the more I look into it - it is basically trying to invent algorithms with provably good properties, which is a sort of frequentist approach. However, I suspect that relying on this kind of tinkering means it may be hard to demonstrate you have a good model of ASI (which could have tinkered further than you!) unless you're only trying to model the ASI you actually built - and then you have to push the theory far enough to get a blueprint for (safe) ASI.

I'm interested in the easier (?) problem: how should a computationally *unbounded* embedded agent act?^\[This is also the topic of \[\[Naturalizing Decision Theory by Hurrmann|Herrmann's PhD thesis]], which is more philosophical and focused on action identification.]

It's not a priori obvious that this a well-defined question. All agents embedded in a computationally bounded universe must be computationally bounded themselves, so we risk constructing a "theory of nothing." We can of course take the limit of increasing compute, but the result may be path dependent - it might matter how compute scales differentially across the agent/environment system.

On the other hand, it seems like some problems of embeddedness really have nothing to do with computational bounds. For instance, the possibility that the environment might corrupt your source code seems to have more to do with side-channels than computational bounds. Some forms of anthropic and evidential reasoning seem to fall into the same category.

In previous work, I've created some formal frameworks to talk about aspects of embedded agency. These include evidential learning from one's own actions and robustness to side-channel corruption. In this post, I want to investigate how a reflective oracles handle these problems. This leads to the construction of a reflective AIXI generalization which I think combines the virtues of some of my previous ideas (actually, in many cases, Marcus Hutter's ideas which I formalized). This agent follows sequential evidential decision theory (SAEDT) with respect to reflective oracle Solomonoff induction (rOSI) as joint action/percept history distribution.^\[I realize this is a lot of jargon for one sentence. But I have to admit, there is something about uniting these ideas into something it would have been hard to formulate from scratch that I find pleasing. It makes the discussion feel more paradigmatic.] For short, I'll call this agent self-reflective AIXI (which turns out to respect previous terminology - conveniently, it combines ideas from Self-AIXI and reflective AIXI). Next I'll discuss prospects for alignment applications and further development of this theory.

I don't think there's much novel math here, and none of it is deep - at least when you factor out the existence of reflective oracles. I'm mostly trying to tie my thinking together into a cohesive research program.

## Standard Notation

$\epsilon$ : the empty string

$\varepsilon, \delta$ : (small) positive numbers, NOT the same as $\epsilon$

$\gamma_t$ : discount factor at time $t$, a positive number.

$\Gamma_T$: tail some of discount factors $\sum_{t=T}^{\infty}\gamma_t$

$Q_\nu^\pi$ : the action-value function for policy $\pi$ and environment $\nu$

$V_\nu^\pi$ : the (state) value function for policy $\pi$ and environment $\nu$

## Loosening the Dualistic Assumption

That picture I opened with (of AIXI playing a video game) accurately describes its "ontology." AIXI really believes that the environment is a (Probabilistic Turing) machine that it can (only) exchange messages with. Specifically, action $a_t$ is sent at time $t$, and then percept $e_t := o_t r_t$ is received (where $o_t$ is an observation and $r_t$ is a reward). That means AIXI "only does Solomonoff induction on the percepts" with the actions as an additional input. Marcus Hutter made this formal by defining "chronological semimeasures," so in a sense AIXI does "Solomonoff-Hutter" induction, rather than ordinary Solomonoff induction. This is basically the move that MIRI objects to most loudly.

We can write $\nu(e_{1:t}||a_{1:t})$ to describe a belief distribution that treats actions as received on such a distinguished input channel (or "tape") and then randomly generates the percepts. AIXI uses a Bayesian mixture of this form, the universal lower semicomputable chronological semimeasure $\xi(e_{1:t}||a_{1:t})$. Chronological means the actions and percepts are exchanged in the right order. You don't need to know what the rest of those words mean to understand this post.

Years ago, when I first started working with Professor Hutter, I convinced myself that I had brilliantly solved this problem - just do Solomonoff induction on the whole sequence, including actions and observations!

You can totally do this! But it causes other problems - it's a worse theory of intelligence.

First of all, it's not so clear how planning should work any more.

Do you even plan ahead? If so, do you update in advance on all the actions you plan to take? \[\[Sequential Extensions of Causal and Evidential Decision Theory by Everitt, Leike, Hutter|This paper]] formalizes two approaches to planning ahead in evidential decision theory.

Since we are treating our future actions as uncertain, I think it is more natural to plan only one step ahead (what I call *action evidential* decision theory as opposed to the previous paper's sequential action evidential decision theory).

$$\pi_S(h_{<t}) = a_t^* \in \arg\max_{a_t} Q_\xi(a_t, h_{<t}) := \arg\max_{a_t} \mathbb{E}_\xi\left[\sum_{i=t}^{\infty}\gamma_i r_i | h_{<t} a_t\right]$$

where $h_{<t} := a_1 e_1 a_2 e_2 ... a_{t-1} e_{t-1}$

A similar approach is advocated by the \[\[Self-Predictive Universal AI by Hutter et al|Self-AIXI]] paper, which we will return to later.

Either way, the problem is that the action sequence is no longer computable (or even lower semicomputable). AIXI is too smart for AIXI to be able to understand it - so we can't guarantee that it ever learns to predict the future.

Actually, this isn't trivially obvious, since predicting only the percepts might be good enough for the sequential planning approach (which intervenes on the actions anyway), and the percepts are still (lower semi)computable as a function of the actions, loosely speaking. I wrote `a paper` with Marcus Hutter about the resulting (potential for) convergence failure, and it can occur under sufficiently unfortunate action choices (though we don't know whether AIXI actually takes these unfortunate actions). However, a weak positive convergence result can be proven by renormalizing the universal distribution. Clearly the situation is messy - it seems MIRI had a point about this one.

Adding a reflective oracle completely solves this problem - when $\xi$ is chosen as rOSI, the resulting $\pi_S$ is reflective oracle computable (rO-computable) by essentially the same trick used to construct `reflective AIXI`. This means that ordinary merging-of-opinions results apply.

What do we get out of this approach? Well, learning about the environment from our own actions seems useful. For instance, it should effect the agent's behavior in games against copies of itself - other agents known to have the same source code. Here we would probably want to use a specially chosen `"cooperative" reflective oracle`. I haven't studied this yet. Another question I am interested in is "what actually happens if such an agent reads its own source code?" Presumably it would become certain of its future decisions, which seems to mean conditioning on impossible counterfactuals (another complaint of MIRI). A direct answer is that is not possible for this to actually cause a divide-by-zero error because rOSI never assigns 0 probability to any (finite) action/percept history. **Still, it seems worth investigating what happens when certain action probabilities are driven very close to zero through the learning process (an as-yet under-specified open problem).**

Evidential learning seems to be the main "advantage" when sequential planning is used, but we chose one-step-ahead planning for an additional advantage: it doesn't assume that we will control all of our future actions.

## Radiation Hardening AIXI

One of the examples in Soares' critique of AIXI is the "Heating Up" game:

> **The Heating Up game.** An agent A faces a box containing prizes. The box is designed to allow only one prize per agent, and A may execute the action P to take a single prize. However, there is a way to exploit the box, cracking it open and allowing A to take all ten prizes. A can attempt to do this by executing the action X. However, this procedure is computationally very expensive: it requires reversing a hash. The box has a simple mechanism to prevent this exploitation: it has a thermometer, and if it detects too much heat emanating from the agent, it self-destructs, destroying all its prizes.

He argues that AIXI is not equipped to solve this problem, because it does not understand itself as computed by a piece of hardware, so can never conceive of the possibility that thinking for longer might cause it to heat up. I think this example is not very good. Insofar as an AIXI approximation controls which computations are running on its hardware, it will absolutely learn any correlates of this in the environment. If the AIXI approximation doesn't control how its compute is used then it kind of faces an unfair problem here - but it will still be able to predict that it will heat up in this situation, given some experience of similar situations. The details depend on where you put the boundary around the thing you treat as an AIXI approximation.

Anyway, I suggest an improved version of this example where heating up actually overheats the AIXI approximation's hardware, so that it takes unintended decisions. In this case, AIXI really wouldn't learn to predict this, because it does not predict its own decisions, it plans them.^[For AIXI, deliberation crowds out prediction.]

A simpler version (suggested by Samuel Alexander) is a robot designed to clean up a nuclear disaster site. Some rooms might have high levels of radiation, which could flip bits and cause the robot to misbehave. Naively, AIXI would never learn this - it would keep going back into the room planning to "just behave properly" this time.

Previously, I formalized this by adding an action corruption function $f$ which may depend on both the past/present actions and the past/present percepts. Then I proposed a variation on AIXI (invented by myself and Professor Hutter) which recalculates its own "true" action history at every step, and is able to "externalize" action corruption. I now call this "hardened AIXI" after radiation hardening.

`Here is the post` - the rest of this section is easier to understand if you've read it.

**How does self-reflective AIXI deal with action corruption?** I would argue pretty well. Technically the argmax over $a_t$ is only what we want when our agent actually gets to pick its current action. That means $\pi_S$ doesn't handle adversarial action relabeling in the way that hardened AIXI does: if $f$ always swaps $a_1$ and $a_2$, and $\pi_S$ wants to take $a_1$, it just selects $a_1$. But this seems like a fairly reasonable answer: the point of a decision theory is to tell us which action we want to take, if we have control. $\pi_S$ is telling us the result it wants "after corruption." But otherwise it natively handles the situation without adding a hardening patch, which is nice. Below I'll be a little more formal about this.

**Some contrived examples.** Assume that the environment $\nu$, policy $\pi$, and action corruption function $f$ are all rO-computable. Then the situation is realizable and (the reflective) $\xi$ learns correct prediction on-policy. If we assume also that $f$ always has some fixed $\delta > 0$ chance of selecting any action^[I am smuggling in a free exploration rate, which causes merging-of-opinions to do what I want it to, so that Lemma 4.17 of Jan Leike's thesis remains applicable after action selection. Informally, this avoids a divide-by-zero.] then we even have

$$Q_\xi(a_t, h_{<t}) \to Q_\nu^{f \circ \pi}(a_t, h_{<t})$$

Setting $\pi = \pi_S$, this means that in the limit $\pi_S$ selects an $\varepsilon$-optimal action! However, technically the "external" policy we care about is $f \circ \pi_S$ which does the true action selection. Intuitively, it seems that $f \circ \pi_S$ is properly satisfying the Bellman equations "when $\pi_S$ is in control."

Here is a much stronger set of assumptions that makes this idea explicit:

Assume that there are two types of action corruption. In "out-of-control" situations, $f$ does not depend on $a_t$ at all. In "noisy" situations, $f$ just has a uniform $\delta < 1/|A|$ chance of switching $a_t$ to some other action in the action space $A$. Then $\pi_S$ takes the best action (accounting for corruption!) in noisy situations and trivially takes a best action (that is, any action) in out-of-control situations.

## Convergence Under a Self-Trust Assumption

I am interested in understanding when self-reflective AIXI converges to AIXI. This is desirable roughly when the dualistic assumptions are actually satisfied (and the agent can be reasonably expected to learn this). This is one test for whether a theory of embedded agency makes any sense - it is the same test I applied to joint AIXI.

A similar convergence analysis was carried out (but not completed) for `Self-AIXI`, which is a minor variation on joint AIXI that maintains separate distributions over its own policy and the environment, drawn from hypothesis classes $\mathcal{P}$ and environment class $\mathcal{M}$. This doesn't make much sense as a theory of embedded agency; it was actually motivated as a theoretical model of policy distillation.

We can describe it more formally as follows:

An **environment distribution** is given by:

$$\psi(e_t|h_{<t}a_t) = \sum_{\nu \in \mathcal{M}} w(\nu|h_{<t}) \nu(e_t|h_{<t}a_t)$$

where $w(\nu|h_{1:t}) := \frac{w(\nu|h_{<t}) \nu(e_t|h_{<t}a_t)}{\psi(e_t|h_{<t}a_t)}$

with prior probability $w(\nu|\epsilon) = w(\nu)$.

(Unlike the paper, I chose $\psi$ for this environment mixture to reserve $\xi$ for the universal distribution on the joint history.)

And a **policy distribution** is given by

$$\zeta(a_t|h_{<t}) = \sum_{\pi \in \mathcal{P}} \omega(\pi|h_{<t}) \pi(a_t|h_{<t})$$

where $\omega(\pi|h_{1:t}) := \frac{\omega(\pi|h_{<t}) \pi(a_t|h_{<t})}{\zeta(a_t|h_{<t})}$

with some prior probability $\omega(\pi|\epsilon) = \omega(\pi)$.^[The Self-AIXI paper is inconsistent about whether the policy distribution should be updated on the current action when comparing action-values. The intention seems to be to do so, and I follow this convention.]

Note that $w$ and $\omega$ are updated separately, depending only on percepts and actions respectively. This is superficially different from joint AIXI.

Interestingly, there is actually little difference when the classes are taken as rO-computable mixtures. This is a nice "lego block" property of the rO-computability; an rO-machine is completed to a Markov kernel yielding conditional probabilities which you can just snap together to form a joint distribution.

Speaking more formally:

There is an rO-machine that uses $\zeta$ for action symbols and $\psi$ for environment symbols, so the joint distribution (usually written) $\psi^\zeta$ is rO-computable. This means that $\xi \geq \psi^\zeta$ up to a constant factor (the prior probability of $\psi^\zeta$).

Similarly, since $\xi(e_t|h_{<t}a_t)$ is rO-computable, it's the case that

$$\psi(e_{1:t}||a_{1:t}) \geq w(\xi) \prod_{i=1}^t \xi(e_i|h_{<i}a_i)$$

and similarly

$$\zeta(a_{1:t}||e_{<t}) \geq \omega(\xi) \prod_{i=1}^t \xi(a_i|h_{<i})$$

Taking the product yields

$$\psi^\zeta \geq w(\xi)\omega(\xi) \xi$$

Which yields

**Observation 1:** $\xi = \psi^\zeta$ up to a constant factor.

In the reflective oracle setting, the difference between Self-AIXI's dualistic belief distribution and self-reflective AIXI's joint belief distribution is, in some sense, epistemic but not ontological, and it makes surprisingly little difference. It's essentially just an inductive bias. Or, in other words: Self-AIXI approximately learn that it is an embedded agent, and self-reflective AIXI can learn that it isn't!

Therefore my choice to use the joint distribution for self-reflective AIXI is not that important, but only a simplification (again, none of this is proven for ordinary AIXI, and in fact we proved a related negative result that the joint distribution restricted to the percepts does not dominate the universal chronological semimeasure).

Now we are prepared to discuss the convergence results in the Self-AIXI paper. The paper has some good ideas, but also some serious flaws and gaps:

1: It requires $\pi_S \in \mathcal{P}$ but demonstrates no such example. This can be easily fixed with reflective oracles, as I have informally described. *Note that this fact pretty much screens off the other details of reflective oracles from the rest of my analysis - I'm actually coming to believe that the role of programs in AIT is mostly as a type of building block with sufficiently rich compositional / recursive structure to ease the construction of belief distributions with interesting properties, and this feature remains useful independently of any ontological commitments to a computable universe or even epistemological commitments to computable mindspace.*

2: The paper introduces a technical assumption called "reasonable off-policy" which is inscrutable and essentially assumes the conclusion.

The follow example (suggested by Diffractor) illustrates how the "reasonable off-policy" assumption can fail: 

**Sink or swim.** The agent wants to move from one island to another, but would much rather stay put than drown. Fortunately, the agent is an excellent swimmer and could easily swim to the other island if it jumped into the water. However, after jumping into the water, it could also choose to sink and drown.

![](https://res.cloudinary.com/lesswrong-2-0/image/upload/f_auto,q_auto/v1/mirroredImages/B6gumHyuxzR5yn5tH/u3bpf8odwwbb2xus4g85)

The answer seems obvious: jump in, and then swim to the next island. That is the optimal policy.

However, we have constructed an agent which is not certain it can trust itself to act as planned. This uncertainty may prevent the agent from jumping in and finding out that it will actually swim. A similar type of uncertainty blocking exploration is an obstacle for convergence in AIXI (or any Bayesian agent that believes the environment may contain inescapable traps). It just seems more jarring in this case because the agent could be built to trust itself by planning ahead sequentially - but that would prevent it from reasoning about action corruption through side-channels! There seem to be some inherent tradeoffs here.

The "reasonable off-policy" requirement (which I haven't reproduced here) basically encodes, in an obfuscated way, the knowledge that if you jump in you will actually swim, despite never having jumped in before.

Here is a much more transparent convergence result of the same flavor. Assume for simplicity that rewards are shifted and rescaled to $[0,1]$. The inspiration for this result is that when $\xi = \psi^{\pi_S}$, then $\pi_S$ satisfies the Bellman equations for $\psi$ and can be shown optimal.^\[By expanding the value function $V_\psi^{\pi_s}$ in terms of the defining (arg)max's to arbitrary (finite) depth, we see the result dominates any finite-horizon value function, which can be shown equivalent to optimality at infinite horizon.] In fact, MIRI relied on this logic implicitly to construct reflective AIXI. Intuitively, this result should be "continuous in $\xi$," and it is, though I found this slightly harder to show than expected because of the self-referentiality involved - $\pi_S$ is actually discontinuous in $\xi$ because of the argmax. However, we can still show the result in two steps, by showing that $\pi_S$ takes an $\varepsilon'$-optimal action for $\pi_\psi^*$, and then showing that this means $\pi_S$ is actually $\varepsilon$-optimal itself.

For simplicity I will phrase the argument in terms of the value function $V_\psi^{\pi_S}$ at $t=0$ but it generalizes automatically to conditionals on a finite history prefix.

(As mentioned later, the proof is actually simpler if one uses Self-AIXI with $\zeta = \pi_S$ and the correct $\psi$ given - and in that case, it is not necessary to assume $\psi$ deterministic)

[EDIT: This theorem is currently broken. The problem is that, in Lemma 1, the action-values for off-policy actions can be underestimates, which means the expansion in terms of maxima is wrong. This may be possible to repair with cooperative oracles, but I don't think it is true as stated.]

**Theorem 1 ($\delta$-Self-Trust is $\varepsilon$-Optimal):** Let the true environment $\psi$ be deterministic. For any $\varepsilon > 0$, there exists a $\delta > 0$ such that if $\xi \geq (1-\delta)\psi^{\pi_S}$, then $\pi_S$ is $\varepsilon$-(Bayes-)optimal for environment $\psi$. If only one action is (Bayes-)optimal for $\xi$ at every time step $t$ and discounting is geometric, then $\pi_S$ remains $\varepsilon$-optimal at all times.

The significance of this result is that you don't need to directly assume you are (near)optimal. You just need to believe that you are probably doing action-evidential decision theory with rOSI. The result says that this consistent self knowledge is enough for near optimality: "If you are locally optimizing and expect to continue, you are nearly globally optimal." Importantly, this result doesn't require dogmatic Cartesian dualism: if it turns out that the environment sometimes corrupts its actions through side-channels, self-reflective AIXI can learn this (the inductive bias we built in can be washed out).

Let $T_\varepsilon$ be the minimal time such that $\Gamma_T := \sum_{t=T}^{\infty}\gamma_t < \varepsilon$. I'll also assume that the sum of discounts is 1. The following lemma is designed to prove that the action chosen by $\pi_S$ is near-optimal *for the optimal policy* $\pi_\psi^*$.

**Lemma 1:** Assuming that $\xi(\cdot|h_{<t}) \geq (1-\delta)\psi^{\pi_S}(\cdot|h_{<t})$ for $t \leq T_\varepsilon$ and $h_{<t}$ satisfying $\pi_S(a_i|h_{<i})>0$, $$Q_\xi(a_t, \epsilon) \geq Q_\psi^{\pi_\psi^*}(a_t, \epsilon) - \varepsilon - T_\varepsilon\delta$$

**Proof:** Let $\bar{\xi} := \frac{1}{\delta}(\xi - (1-\delta)\psi^{\pi_S})$. By linearity, $$Q_\xi(a_1, \epsilon) = \delta Q_{\bar{\xi}}(a_t, \epsilon) + (1-\delta)Q_\psi^{\pi_S}(a_1, \epsilon) \geq (1-\delta)Q_\psi^{\pi_S}(a_1, \epsilon) \geq Q_\psi^{\pi_S}(a_1, \epsilon) - \delta$$

But this is $$= \frac{1}{\Gamma_1} \mathbb{E}_{e_1 \sim \psi(\cdot|a_1)}[\gamma_1 r_1 + \Gamma_2 V_\psi^{\pi_S}(a_1 e_1)] - \delta$$

We can expand the value function in terms of the max of another action-value function. Iterating to depth $T_\varepsilon$,  **[This is the gap, the expansion is wrong because action-values / value functions off-policy are wrong]** $$\geq \mathbb{E}_{e_1...} \max_{a_{T_\varepsilon}} \mathbb{E}_{e_{T_\varepsilon}}\left[\frac{1}{\Gamma_1}\sum_{t=1}^{T_\varepsilon} \gamma_t r_t + \frac{\Gamma_{T_\varepsilon}}{\Gamma_1} V_\psi^{\pi_S}(h_{1:T_\varepsilon})\right] - \sum_{t=1}^{T_\varepsilon} \frac{\Gamma_t}{\Gamma_1} \delta$$

Now we use the definition of $T_\varepsilon$ to observe $\frac{\Gamma_{T_\varepsilon}}{\Gamma_1} < \varepsilon$, and observe that all value functions are in $[0,1]$. This means we can substitute the optimal value function at a maximum cost of $\varepsilon$. Also, since $\Gamma_t$ is decreasing we can simplify the last fraction.

$$\mathbb{E}_{e_1...} \max_{a_{T_\varepsilon}} \mathbb{E}_{e_{T_\varepsilon}}\left[\frac{1}{\Gamma_1}\sum_{t=1}^{T_\varepsilon} \gamma_t r_t + \frac{\Gamma_{T_\varepsilon}}{\Gamma_1} V_{\psi}^{\pi_\psi^*}(h_{1:T_\varepsilon})\right] - \varepsilon - T_\varepsilon\delta$$

$$= Q_\psi^{\pi_\psi^*}(a_1, \varepsilon) - \varepsilon - T_\varepsilon\delta$$

Okay, that could possibly have been cleaner, but Lemma 1 is proven.

Lemma 1 tells us that $\pi_S$ does not badly underestimate the value function. We actually need to know that $\pi_S$ does not badly overestimate the value function as well:

**Lemma 2:** Assuming that $\xi(\cdot|h_{<t}) \geq (1-\delta)\psi^{\pi_S}(\cdot|h_{<t})$ for $t \leq T_\varepsilon$,

$$Q_\xi(a_t, \epsilon) \leq Q_\psi^{\pi_\psi^*}(a_t, \epsilon) + \varepsilon + T_\varepsilon\delta$$

**I brush the proof of this lemma under the rug.** This case is more straightforward - as long as $\xi$'s percept distribution is close to $\psi$, no policy can outperform the optimal value function by much. I won't prove this explicitly - we can instead recite something about continuity of linear functional application. I assumed that $\psi$ is deterministic to ensure that $\xi$ never diverges from $\psi$ on percept bits. We can avoid this assumption by using Self-AIXI instead of self-reflective AIXI, and simply telling it the environment is $\psi$.

**Proof of theorem:** We established at some effort that we can ensure each action is near optimal (for the optimal policy). Now we will find $\delta'$ so that $\xi(\cdot|h_{<t}) \geq (1-\delta')\psi^{\pi_S}(\cdot|h_{<t})$ ensures that each action is within $\varepsilon' = \frac{\varepsilon}{2T_{\varepsilon/2}}$ of optimal. This is slightly tedious; let $T_t^\varepsilon$ is the minimum time satisfying $\Gamma_{T_t^\varepsilon}/\Gamma_t < \varepsilon$. Given $\varepsilon > 0$, we apply Lemma 1 to $\varepsilon' := \varepsilon/4T_{\varepsilon/2}$, then choose $\delta' < \min_{t \leq T_{\varepsilon/2}} \frac{\varepsilon'}{T_t^{\varepsilon'}}$. This choice ensures that every action chosen by $\pi_S$ is $2\varepsilon'$-optimal. Finally,

$$V_\psi^{\pi_S}(\epsilon) - V_\psi^{\pi_\psi^*}(\epsilon) = \mathbb{E}_{a_t \sim \pi_S} Q_\psi^{\pi_S}(a_t, \epsilon) - \max_{a_1} Q_\psi^{\pi_\psi^*}(a_1, \epsilon)$$

$$= \mathbb{E}_{a_1 \sim \pi_S}[Q_\psi^{\pi_S}(a_1, \epsilon) - Q_\psi^{\pi_\psi^*}(a_1, \epsilon) + Q_\psi^{\pi_\psi^*}(a_1, \epsilon)] - \max_{a_1} Q_\psi^{\pi_\psi^*}(a_1, \epsilon)$$

Applying Lemmas 1 and 2 to the last pair of terms,

$$\geq \mathbb{E}_{a_1 \sim \pi_S} \mathbb{E}_{e_1 \sim \psi} \frac{\Gamma_2}{\Gamma_1}[V_\psi^{\pi_S}(a_1 e_1) - V_\psi^{\pi_\psi^*}(a_1 e_1)] - 2\varepsilon'$$

$$= \mathbb{E}_{a_1 \sim \pi_S} \mathbb{E}_{e_1 \sim \psi}  \mathbb{E}_{a_2 \sim \pi_S(\cdot|a_1 e_1)} \frac{\Gamma_2}{\Gamma_1}[Q_\psi^{\pi_S}(a_2, a_1 e_1) - Q_\psi^{\pi_\psi^*}(a_2, a_1 e_1)] - 2\varepsilon'$$

We can iterate by expanding the inner expectation. Repeating this process to depth $T_{\varepsilon/2}$, we obtain:

$$\geq \mathbb{E}_{a_1} \mathbb{E}_{e_2} ... \mathbb{E}_{a_{T_{\varepsilon/2}}} \mathbb{E}_{e_{T_{\varepsilon/2}}} \frac{\Gamma_{T_{\varepsilon/2}}}{\Gamma_1}[Q_\psi^{\pi_S}(a_{T_{\varepsilon/2}}, h_{<T_{\varepsilon/2}}) - Q_\psi^{\pi_\psi^*}(a_{T_{\varepsilon/2}}, h_{<T_{\varepsilon/2}})] - \frac{T_{\varepsilon/2}}{2}\varepsilon'$$

$$\geq -\frac{\varepsilon}{2} - \frac{T_{\varepsilon/2}}{2}\varepsilon'$$

$$= -\varepsilon$$

That is,

$$V_\psi^{\pi_S}(\epsilon) \geq V_\psi^{\pi_\psi^*}(\epsilon) - \varepsilon$$

Finally.^\[I have a feeling that someone better than me at measure theory (like Kosoy or Diffractor) could have done this proof so far backwards in heels and still taken half the lines. Since it is currently a bit of a mess, I wouldn't be surprised if e.g. there's the wrong constant in front of an $\varepsilon$ somewhere.]

**The basin of attraction.** Now all that remains is to show that the conditions of Lemmas 1 and 2 can be maintained after updating. Informally, this is true as long as we can only receive a finite amount of evidence against $\psi^{\pi_S}$ at every step - in that case, a sufficiently large odds ratio $(1-\delta):\delta$ for $\psi^{\pi_S}:\bar{\xi}$ will remain above $(1-\delta'):\delta'$ up to time $T_{\varepsilon/2}$. By assuming $\psi$ deterministic, we ensured that percepts never provide evidence against $\psi^{\pi_S}$. The action chosen by $\pi_S$ are always of course consistent with $\pi_S$, but it will randomize between equivalent options (this is the trick that makes it rO-computable). It is possible for this to provide about $|A|$ bits against $\pi_S$ in the worst case (under the standard construction for $\pi_S$), though in expectation of course $\pi_S$ predicts itself best. That is where the condition (needed for the stronger result that $\pi_S$ remains $\varepsilon$-optimal for all time) that only one action is Bayes-optimal for $\xi$ comes from. I assumed geometric discounting to ensure that $T_t^\varepsilon$ does not depend on $t$, which could probably throw things off. Interestingly, if there were always two Bayes-optimal actions for $\xi$, the evidence against $\pi_S$ would be a kind of "$\xi$-randomness deficiency," which is the reflective-oracle analogue of M.L. randomness deficiency. So, the theory of algorithmic randomness has a connection to the basin of attraction for self-trust! This is a little unexpected - proper algorithmic information theory doesn't seem to come up in the theory of AIXI as much as you would expect.

This concludes the proof.

## Closing Thoughts and Future Work

It seems to me that MIRI wanted to be able to embed an agent's code inside a larger piece of code and evaluate its performance. When everything is an rO-machine, this is totally possible. These machines are like... flexible lego blocks. You can snap them together however you want, but Observation 1 suggests that updating treats whatever structure you build this way like a weak suggestion. This means that the resulting agents may not have very dogmatic beliefs. I am not sure whether this is good.

In this setting, self-trust has a "basin of attraction" which depends on non-dogmatically elevating the weight on a certain hypothesis. Playing with prior weights like this feels very clumsy. I think it would be nicer to build in knowledge through logical statements, perhaps using \[\[Probabilities on Sentences in an Expressive Logic|Hutter et al.'s (uncomputable) method]] for assigning probabilities to logical statements. If I understand correctly, this is vaguely related to the type of tiling properties the corpus author and his collaborators study in the computationally bounded setting using UDT. I am not satisfied with the current versions of UDT (and as explained above, I think there are good reasons to expect it is very hard to find a satisfactory theory of computational uncertainty). But of course rO-computability is not realistic and eventually we must move beyond this idealized setting.

I think reflective oracles are a reasonable model for agents of similar intelligence reasoning about each other or about agents of lower intelligence than themselves. This seems sufficient for modeling CIRL between idealized agents of equal power, which would be an interesting case to evaluate next.

===

# Here are the notes I made about Cole's post before we found the problem in the proof:

- `Cole Wyeth` published a tiling theorem on LessWrong
	- I would really like to do a proper review of it.
		- `Blog Post Ideas`
			- Just a thorough review of Cole's result.
				- Relationship to tiling.
					- Why is this of interest, if it doesn't handle Vingean uncertainty?
						- Define Vingean uncertainty.
						- Discuss my doubts about whether tiling proofs should focus first on the vingean case, based on my recent theorem.
							- Need to be in an equilibrium, rather than only reasoning abstractly about oneself.
							- First characterize the equilibrium, then characterize what's needed to approximate it (approaching it via boundedly rational process).
							- I still endorse what I've previously written about bounded rationality being the realest rationality; I think once we figure out a good approximation notion, the thing-that-approximates will be in the foreground, with the thing-being-approximated taking a backstage seat.
								- What I no longer endorse, if I buy Cole's methodology, is my methodological claim that the "computationally unbounded" case makes no sense. Cole's idea revolves around examining the computationally unbounded case.
									- This specifically means something like limit-computable; it is "bounded" in the sense that we can put it in a specific place in the hierarchy of hypercomputation.
									- The methodological claim can still apply in the future when working at the level of theoretical computer science.
							- However, I've been too stuck trying to make a Vingean proof, stuck between a need for a real theory of logical uncertainty & a desire to keep things agnostic, factoring out UDT-compatible logical uncertainty as a separate part to be solved.
							- In terms of the spectrum of levels of abstraction for AI safety research, which I've sketched out frequently in discussions about my research agenda, I would classify this as retreating to the level of mathematical philosophy, retreating from the somewhat-more-concrete realm of theoretical computer science.
								- The new plan is to factor the problem into solving the case for unbounded computation, and then appropriately relating that solution to bounded computation.
									- "appropriately relating" could mean finding a good approximation, or it could
							- Connection between updatefulness of this approach & factoring bounded computation out of embedded agency.
								- Although the theorem doesn't directly address it, self-trust seems like the sort of thing that must be learned, approached in the limit, updated towards.
								- The approach involves induction over decision-trees in a way I'm not sure has an updateless correlate.
				- Relationship to UDT.
					- Why is this result of interest, if it doesn't handle problems UDT handles?
					- Why is this result of interest, if it can't handle knowledge of your own source code?
					  collapsed:: true
						- Connection between avoiding source code and avoiding UDT.
						  collapsed:: true
							- UDT classically conditions on the behavior of its abstract algorithm, rather than conditioning on its body behaving a specific way.
							- Cole's theorem involves a system that doesn't perfectly know which algorithm it is, so can only condition on "its action" (basically, what its body does).
							- Can I create any weird decision-theoretic examples by exploiting this difference? An example where Cole's proposal seems to condition on the wrong thing, from an intuitive perspective?
							- Uncorrelated nature of algorithm output in ROs means that EDT is weak here; actions of agents running the same algorithm aren't correlated unless identical.
								- Can't charitably interpret the action predicate as "output of my unknown decision procedure, whatever it may be"; it's just one instance (one sample).
								- So we *can* describe the agent as thinking of itself as an *instance* of an unknown abstract decision procedure.
						- Learning its source code naturalistically doesn't create division-by-zero errors, but only because it doubts the accuracy of such an observation!
							- The skeptic says: Yes, I see that you've engineered a system without division-by-zero problems. But you've only accomplished this by deliberately choosing to make a system ignorant of its own nature. The universal distribution is of particular philosophical interest, but we can also judge a proposed decision theory on other belief distributions. Why can't I choose to enforce perfect self-knowledge? I am only telling the agent true facts! It should not break the agent!
								- Cole might reply: the uncertainty about self-trust is essential to the story I'm telling about embedded agents. The non-dogmatism assumption with respect to one's own actions is what puts one into a world.
								- However, Cole has a better reply available: if the skeptic insists on enforcing self-knowledge of this strength, Cole can insist on enforcing belief in cdt-rationality (optimality wrt the causal story).
						- "Knowledge of your own action" is a more accurate description of what this idea can't handle than "knowledge of your own source code".
						- Compare to Jessica's approach: https://www.lesswrong.com/posts/Rcwv6SPsmhkgzfkDw/edt-solves-5-and-10-with-conditional-oracles
				- Action correlations concern.
					- Compare to Jessica's approach: https://www.lesswrong.com/posts/Rcwv6SPsmhkgzfkDw/edt-solves-5-and-10-with-conditional-oracles
				- What does it look like to try and add computational bounds to this result?
					- Prove optimality wrt bounds placed by self-limiting beliefs (fear of permanent consequences blocking exploration).
					- Learning optimality, rather than just stability of self-trust.
					- Extend to LIDT or another boundedly rational case.
						-
			- Put it in the context of the `Understanding Trust` group & the work we've done over the past year.
				- My two papers, plus the results of my collaborators
				- release the videos at the same time
				- Ask Roman about publishing his proof


===

[scrubbed: chat log]


===

# Here are a few other little notes I made recently, in relation to this topic:

- The problem with perfectly knowing your own actions, and thereby getting a division-by-zero error (or a contradiction or other similar issues which prevent good counterfactual reasoning) is *illustrated by* the problem of actions with very small probability: such actions can only be evaluated by conditioning out of the self-trust, since self-trust doesn't believe in such actions.
	- The problem with actions of very small probability shows that there are cases where conditioning on your body taking the action & conditioning on your abstract algorithm output is different, even though you're quite confident the two are equal: conditioning on your body moving can condition you out of knowing your own algorithm.
	- It is not literally impossible to learn self-trust even conditional on a self-trust violation, however: if it did occasionally happen thru $\epsilon$ -exploration, the agent could observe itself engaging in trustworthy behaviors thereafter, so could learn that taking actions it doesn't expect itself to take doesn't make it insane or any such thing.
	- $\epsilon-exploration$ , however, introduces an explicit mechanism differentiating 'the body taking the action' and 'the algorithm outputting the action'. Cole wants to prove the result more generically, with general uncertainty about the difference.

- Argument for `UDT` over `EDT`:
	- To judge decision theories, need to be able to put agents into environments.
		- I'm basically arguing something like: cartesian frames get it right.
			- It can still matter what we do in observations with probability zero.
		- Seem to need a probabilistic version of cartesian frames, to talk about this properly.
		- There's an (meta-)action that chooses the decision theory, and then the decision theory, and then the decision theory chooses an (object-)action.
			- EDTer view: UDT is just the normative theory of choosing a policy.
				- If you're in that situation of choosing the policy, if that's your options to choose from, EDT agrees with the UDT recommendation.
			- UDTer: decision theories should 'tile' across this meta/object divide.
				- Can't objectively say which decision theory is better in this game of choosing decision theories, but can check whether a decision theory endorses itself (for some class of decision problems).
				-
	- Should the decision problem also need to be learnable? Interpreted as part of a sequence?
		- `mixed-strategy ratifiability`: the agent should have a calibrated probability distribution over its own actions, as a consequence of having calibrated probabilities about the situation generally.
			- This is an interpretation of what it means for the agent to know that it is in the decision problem.
			- Incompatible with some versions of `Vingean uncertainty`?
			-

- `Vingean uncertainty`
	- Can't represent it in an equilibriated probability distribution; fundamentally about computational uncertainty.
	- But we can think of it in terms of optimal estimation wrt some sequence of problems.
		- Calibration isn't a requirement here. We do need our epistemics to have some relevantly good class of subsequence properties. Otherwise we can't do reference class reasoning. Think of it as a weak version of calibration: doing as well as some class of modifications to our prediction algorithm (namely, subsequence modifications), but not necessarily arbitrary calibration functions ("the probability is in range blah" is not necessarily a valid subsequence to learn well wrt).
			- Without subsequence properties, we can't do isolated frequentist reasoning based on a given sequence of experiments. This generally damages our ability to reason about the behavior of the system based on its training, since anything in its training might be relevant to its response.



===

# New Notes

Basically, I would like to write about all of this more thoroughly. I don't understand all the details of Cole's broken proof yet. I would like to understand it and then check myself whether his proposed fix works.

Even more importantly, however, I want to suppose that his fix does work, and then think through the implications.

Please pick out all the topics discussed in this document. I want to take notes on these topics, writing out all of my thoughts, so that I can explore and refine those thoughts, in order to become firm in my understanding. Please propose an outline for those notes, so that I can proceed section-by-section. Prioritize the ordering so that I am starting with what is most important and central. Also consider the ordering carefully in terms of what I need to understand first, to deconfuse the rest.

The ordering should be big-picture-first, grappling with overall questions of context and what it is that I'm doing first, and proceeding in stages towards more concrete topics, so that I can plan out what the rest of the notes should look like incrementally as I go. This helps me avoid spending too much time thinking about the wrong thing.

First let's consider my earlier plan for writing a review of Cole's result, before we figured out that it was wrong. This is still in some sense close to what I want to write:
- Just a thorough review of Cole's result.
    - Relationship to tiling.
        - Why is this of interest, if it doesn't handle Vingean uncertainty?
            - Define Vingean uncertainty.
            - Discuss my doubts about whether tiling proofs should focus first on the vingean case, based on my recent theorem.
                - Need to be in an equilibrium, rather than only reasoning abstractly about oneself.
                - First characterize the equilibrium, then characterize what's needed to approximate it (approaching it via boundedly rational process).
                - I still endorse what I've previously written about bounded rationality being the realest rationality; I think once we figure out a good approximation notion, the thing-that-approximates will be in the foreground, with the thing-being-approximated taking a backstage seat.
                    - What I no longer endorse, if I buy Cole's methodology, is my methodological claim that the "computationally unbounded" case makes no sense. Cole's idea revolves around examining the computationally unbounded case.
                        - This specifically means something like limit-computable; it is "bounded" in the sense that we can put it in a specific place in the hierarchy of hypercomputation.
                        - The methodological claim can still apply in the future when working at the level of theoretical computer science.
                - However, I've been too stuck trying to make a Vingean proof, stuck between a need for a real theory of logical uncertainty & a desire to keep things agnostic, factoring out UDT-compatible logical uncertainty as a separate part to be solved.
                - In terms of the spectrum of levels of abstraction for AI safety research, which I've sketched out frequently in discussions about my research agenda, I would classify this as retreating to the level of mathematical philosophy, retreating from the somewhat-more-concrete realm of theoretical computer science.
                    - The new plan is to factor the problem into solving the case for unbounded computation, and then appropriately relating that solution to bounded computation.
                        - "appropriately relating" could mean finding a good approximation, or it could
                - Connection between updatefulness of this approach & factoring bounded computation out of embedded agency.
                    - Although the theorem doesn't directly address it, self-trust seems like the sort of thing that must be learned, approached in the limit, updated towards.
                    - The approach involves induction over decision-trees in a way I'm not sure has an updateless correlate.
    - Relationship to UDT.
        - Why is this result of interest, if it doesn't handle problems UDT handles?
        - Why is this result of interest, if it can't handle knowledge of your own source code?
            - Connection between avoiding source code and avoiding UDT. collapsed:: true
                - UDT classically conditions on the behavior of its abstract algorithm, rather than conditioning on its body behaving a specific way.
                - Cole's theorem involves a system that doesn't perfectly know which algorithm it is, so can only condition on "its action" (basically, what its body does).
                - Can I create any weird decision-theoretic examples by exploiting this difference? An example where Cole's proposal seems to condition on the wrong thing, from an intuitive perspective?
                - Uncorrelated nature of algorithm output in ROs means that EDT is weak here; actions of agents running the same algorithm aren't correlated unless identical.
                    - Can't charitably interpret the action predicate as "output of my unknown decision procedure, whatever it may be"; it's just one instance (one sample).
                    - So we _can_ describe the agent as thinking of itself as an _instance_ of an unknown abstract decision procedure.
            - Learning its source code naturalistically doesn't create division-by-zero errors, but only because it doubts the accuracy of such an observation!
                - The skeptic says: Yes, I see that you've engineered a system without division-by-zero problems. But you've only accomplished this by deliberately choosing to make a system ignorant of its own nature. The universal distribution is of particular philosophical interest, but we can also judge a proposed decision theory on other belief distributions. Why can't I choose to enforce perfect self-knowledge? I am only telling the agent true facts! It should not break the agent!
                    - Cole might reply: the uncertainty about self-trust is essential to the story I'm telling about embedded agents. The non-dogmatism assumption with respect to one's own actions is what puts one into a world.
                    - However, Cole has a better reply available: if the skeptic insists on enforcing self-knowledge of this strength, Cole can insist on enforcing belief in cdt-rationality (optimality wrt the causal story).
            - "Knowledge of your own action" is a more accurate description of what this idea can't handle than "knowledge of your own source code".
            - Compare to Jessica's approach: [https://www.lesswrong.com/posts/Rcwv6SPsmhkgzfkDw/edt-solves-5-and-10-with-conditional-oracles](https://www.lesswrong.com/posts/Rcwv6SPsmhkgzfkDw/edt-solves-5-and-10-with-conditional-oracles)
    - Action correlations concern.
        - Compare to Jessica's approach: [https://www.lesswrong.com/posts/Rcwv6SPsmhkgzfkDw/edt-solves-5-and-10-with-conditional-oracles](https://www.lesswrong.com/posts/Rcwv6SPsmhkgzfkDw/edt-solves-5-and-10-with-conditional-oracles)
    - What does it look like to try and add computational bounds to this result?
        - Prove optimality wrt bounds placed by self-limiting beliefs (fear of permanent consequences blocking exploration).
        - Learning optimality, rather than just stability of self-trust.
        - Extend to LIDT or another boundedly rational case.

Please create an extended outline based on this planned review, but revising it to reflect our new understanding of the flaw in the proof. Feel free to rearrange things to make the outline into a better research plan, prioritizing the most important things first, grouping like things together, etc.

Here's an extended outline based on your planned review, revised to reflect the discovered flaw:

## A Thorough Review of Cole's Result (and Its Instructive Failure)

### Relationship to Tiling

- **Why is this of interest, even with the proof flaw?**
    - The flaw reveals fundamental obstacles to tiling
    - Shows precisely where self-trust can fail
    - **Define Vingean uncertainty**
        - Uncertainty about consequences of self-modification
        - Reasoning about smarter versions of oneself
    - **My doubts about focusing on Vingean case first**
        - The flaw actually strengthens my position here
        - **Need to be in an equilibrium first**
            - Cole's broken proof shows: can't just assume good equilibrium exists
            - Bad equilibria (low probability actions staying low) are real
            - Must characterize which equilibria are possible
        - **First characterize the equilibrium, then approximation**
            - The proof gap shows we need stronger characterization
            - Can't just say "self-trust leads to optimality"
            - Need constraints on oracle fixed points
        - **Bounded rationality as the realest rationality**
            - Still endorse this view
            - The flaw doesn't change fundamental position
            - But shows even unbounded case has deep problems
            - **What I no longer endorse: "unbounded case makes no sense"**
                - Cole's work shows it's meaningful to study
                - Even the flaw is philosophically instructive
                - Limit-computable as specific hypercomputation level
                - Methodological claim still applies at CS level
    - **My own research obstacles**
        - Stuck between logical uncertainty theory needs and agnosticism
        - The flaw shows these obstacles are fundamental
        - Can't just factor out logical uncertainty
    - **Spectrum of abstraction levels**
        - This work is mathematical philosophy
        - Retreat from theoretical computer science
        - **The new factorization plan**
            - Solve unbounded case first (harder than expected!)
            - Then relate to bounded case
            - "Appropriately relating" now includes handling bad equilibria
    - **Connection to updatefulness**
        - Self-trust must be learned/approached
        - The flaw shows why: wrong initial beliefs → stuck
        - Induction over decision trees
        - Updateless correlate unclear

### Relationship to UDT

- **Problems this approach can't handle (even if fixed)**
    - Newcomb-like problems with predictors
    - Coordination via shared algorithms
    - The flaw shows these limitations are deep
- **Knowledge of own source code**
    - **Connection between avoiding source code and avoiding UDT**
        - UDT conditions on abstract algorithm behavior
        - Cole's approach conditions on body's action
        - The flaw shows these are crucially different
        - **Weird decision-theoretic examples**
            - Sink-or-swim validates this concern!
            - Agent won't jump in water
            - Conditions on wrong thing
        - **Uncorrelated RO outputs**
            - EDT weak without correlation
            - Can't interpret as "my decision procedure"
            - Agent as _instance_ not _algorithm_
    - **Learning source code naturalistically**
        - No division-by-zero only via doubt
        - The flaw shows this doubt can be harmful
        - **The skeptic dialogue**
            - Skeptic more vindicated by the flaw
            - "You made it ignorant to avoid problems"
            - "But the ignorance creates new problems!"
            - **Cole's possible replies**
                - Essential uncertainty for embeddedness
                - But uncertainty enables bad equilibria
                - CDT-rationality enforcement response weaker
    - **"Knowledge of action" vs "knowledge of source code"**
        - More precise description of limitation
        - The flaw is specifically about action knowledge
    - **Compare to Jessica's conditional oracle approach**

### The Core Flaw and What It Reveals

- **The technical gap**
    - Off-policy actions can be undervalued
    - Expansion of value function incorrect
    - Lemma 1 fails for inconsistent histories
- **The sink-or-swim problem**
    - Not just a thought experiment
    - Actual failure mode of the approach
    - Agent believes jumping → not πS
    - Therefore doesn't jump
- **Philosophical implications**
    - Self-trust doesn't automatically → optimality
    - Can be optimal at limit but wrong off-policy
    - High confidence still allows total mistakes
    - Bad fixed points are possible

### Action Correlations and Cooperative Oracles

- **Why standard ROs fail**
    - Allow bad equilibria
    - No correlation between identical algorithms
    - Compare to Jessica's approach
- **Cooperative oracles as potential fix**
    - Constrain fixed point selection
    - Rule out bad equilibria
    - Connection to 5-and-10 problem
- **What constraints are actually needed**
    - Minimal assumption to fill the hole
    - Representation theorem possibilities

### Computational Bounds Extension

- **Why this matters even more given the flaw**
    - Unbounded case already has problems
    - Bounded case will be even harder
- **Possible approaches**
    - Fix unbounded case first
    - Then prove approximation results
    - **Self-limiting beliefs**
        - Optimality within exploration bounds
        - How flaw interacts with exploration
    - **Learning optimality**
        - Not just stability but improvement
        - Epsilon-exploration implications
    - **Extension to LIDT**
        - Would need to handle flaw first

### Value of the Negative Result

- **Characterizing necessity of assumptions**
    - Shows self-trust alone insufficient
    - Need oracle selection constraints
    - Philosophical clarity from failure
- **Research methodology lessons**
    - Importance of careful review
    - "Exploratory" work finding deep issues
    - Collaborative debugging value
- **Future directions**
    - Fix with minimal assumptions
    - Prove cooperative oracles work
    - Extend to bounded case
    - Connect to other tiling approaches

That's a good start. I've sat down independently and tried to write down everything important in the order I want to tackle it, taking some inspiration from the above but not being totally thorough about incorporating everything. Here are my new outline notes:

- Describing what I'm trying to grapple with wrt Cole's theorem.
	- The big question is the methodological question, shoring up the "computationally unbounded" (limit-computable) perspective before tackling computational uncertainty as an approximation question.
		- I have previously argued against this. I want to thoroughly consider my previous argument, recalling the reasons and the intuitions. My methodological conclusion was that you've got to tackle boundedness head-on to address the problems we're interested in.
		- However, in writing my recent paper, I have come to doubt this approach, and in particular my ongoing effort to respect Eliezer's Vingean Principle while making UDT tiling proofs which hug the fence between computationally bounded and computationally unbounded. I want to write more detailed notes on this recent feeling of mine, considering why I think this and what approach it suggests instead.
		- And then there's Cole's methodological perspective, which I don't totally understand but which seems very well-considered. So far I've seen it as making the mistakes I've argued against historically. [scrubbed] However, I should try to spell out and steelman his approach as best I can.
		- I should then write about my all-things-considered methodological perspective.
	- Then there's the more medium-sized contextual questions.
		- How is this a tiling theorem? It isn't framed like I've been framing my theorems, but I think it does simply imply something similar.
			- Cole's theorem actually pulls a trick that's very similar to what I did in my recent paper, focusing on stability rather than tiling.
		- What about the distinction between internal and external, from my recent paper? I needed that distinction to even make sense of Eliezer's notion of tiling. Why doesn't it pop up here? Could we / should we add it in?
		- Is Cole's formalism a good notion of embedded agency sans computational uncertainty? Can we make sense of that idea? Has he done it?
	- Then there's the question of why it isn't updateless, and how one would deal with updatelessness in a similar format.
		- I think this is a combination of the CDT optimality notion, which enforces linear causality on the world, and the way ROs further exclude acausal influences by assuming program outputs are uncorrelated.
			- I want to write about how this relates to `CDT=EDT view`.
		- Thus, applying `coedt` should solve the problem.  Or, more generally, replacing ROs with something allowing for correlations.
		- I also want to think more about the general argument for updateless as opposed to updateful, in two subsections:
			- One subsection about the pragmatic question: can we solve alignment in just the updateful case, and leave that as good enough?
			- Another subsection about the theoretical argument in favor of updatelessness: what it means to judge decision theories, etc.
	- Then there's all the stuff about probability-zero actions and low-probability actions.
		- Again, `coedt` should shed some further light on this.
		- However, probably more interesting is [scrubbed], and the light which could be further shed by working through this carefully.
		- I want to work through the broken proof and figure out whether Cole's proposed fix works, to address low-probability concerns.
		- I want to also verify whether the idea about the non-dogmatic case works to answer zero-probability concerns.
			- I also want to think about how RO decision theories handle division by zero computationally. Zero should be impossible to perfectly distinguish, so we can't just throw an error in that case.
	- Then there's the question about how to turn this into a more bounded picture, if the unbounded picture works out.
		- ROSI=ROLI
		- Translate the updateful version of Cole's theorem to logical induction.

Please take inspiration from this way of organizing the ideas, but also the previous ideas for note outline organization we've discussed, and create a very thorough outline incorporating all the ideas based on all of this. This will be the final planning outline before I start writing more seriously. As such, the aim is to include a high amount of detail. I don't want important research directions to get dropped, here.

## Final Outline: Unbounded Embeddedness Review

### 1. The Methodological Question
- 1a: **My Historical Position Against Unbounded Approaches**
	- "Unbounded" rationality isn't a coherent thing to want.
	- The quality of an abstraction is measured by how well it applies to the real world.
	- Trying to specify unbounded rationality and then figure out how to approximate it causes one to ignore important problems.
	- Solomonoff Induction vs Garrabrant Induction: how could Solomonoff hypothetically have avoided the 'mistake' of his universal prior, and jumped straight to Garrabrant Induction?
		- Radical Probabilism
		- Unifying principles: notice the layer-cake of regular probability theory to avoid unbounded Dutch Books, with learning theory layered on top to achieve bounded loss. Try to unify these.
- 1b: **My Recent Doubts**
	- The Vingean Principle
		- Vingean uncertainty as the interesting part about agency.
		- Non-Vingean self-trust is cognitively unrealistic & fails to tackle the interesting part of the problem.
	- Difficulties trying to apply the Vingean Principle.