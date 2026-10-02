*Copy of the author's public Notion page "Notes for Soto & Diff", fetched on 2026-09-29 through Notion's unauthenticated page API and converted to Markdown by a Keeper. Of its 742 blocks, none failed to fetch. Inline math is `$…$`, display math is `$$…$$`, and literal dollar signs are escaped as `\$`. A few spots where Notion nested bold inside italic may show stray asterisks. The page is the author's initial brain-dump for the 2023 summer project with Martín Soto, later revised for Diffractor. The heading "Sam's BLI vs Alternatives" is empty in Notion itself (checked against the rendered page). Section "Dump of more recent UDT notes" includes the author's notes on several of Martín's PDFs (copies in this folder's `soto-2023/`).*

---

# Notes for Soto & Diff

My initial brain-dump for the summer research project. Revised to try and add info about what happened during the summer, for Diffractor.

*I will use “garrabrant induction” and “logical induction” interchangeably.*

## Logical Updatelessness

### Basic Problem Statement

#### Radical Probabilism & Logical Uncertainty

Rational agents may — indeed, should — revise their beliefs over time, in ways that do not conform to Bayes’ Law. This is permissible so long as agents do not fall prey to the Diachronic Dutch Book argument, which is usually given as an argument for Bayesian updates, but in fact only establishes that Bayesian updates are required in cases where *agents know what they will update to (given evidence).* More generally, it is permissible for rational agents to update however they wish, so long as the *expectation* of these updates obeys Bayes’ Law. This view is called [Radical Probabilism](https://www.lesswrong.com/posts/xJyY5QkQvNJpZLJRo/radical-probabilism-1).

My primary motivation for this is logical uncertainty. We can also study the phenomenon in a logically omniscient case (so long as the agent’s future beliefs are ‘free’ — the agent is not mathematically defined, EG by source code, or at least, lacks knowledge of its own mathematical definition); but it makes more sense to study it in the context of bounded rationality. We will use logical induction as our framework, meaning that we only care about avoiding *efficiently computable* Dutch Books in a specific sense.

#### The Problem for Updatelessness

UDT (updateless decision theory) is, in some sense, the best and most complete decision theory which has come out of the modern rationalist agenda. It addresses many of the core rationalist concerns with respect to decision theory:

- Temporal consistency.
- 1-boxing in Newcomb’s Problem and variations such as Transparent Newcomb.
- Cooperating in Twin Prisoner’s Dilemma, including variations such as where the other player moves first.
However, it isn’t clear how to combine UDT with logical uncertainty (to get “logical updatelessness”). UDT was originally specified to use a mysterious logical uncertainty module for this. It was hoped that whatever logical-uncertainty solution was developed in the future, it would fill in this hole in the theory. Unfortunately, UDT naively doesn’t seem to fit with Radical Probabilism or Logical Induction. They apparently have the wrong “shape” to serve the purpose of the mysterious logical uncertainty module: a time-indexed belief distribution. UDT doesn’t update at all, so it’s unclear how to combine it with insights about generalized updating. 

One way we can try to think of Radical Probabilism is “Bayes with a side-channel” — ie, we imagine that the updates are Bayesian, but we don’t have access to all of the “observations” involved in those updates. But again, it isn’t clear how to fit this with UDT. 

However, there is still some hope: it might be possible to **define “observations” for Radical Probabilism to be** ***the future beliefs themselves***. You think longer about a problem, and you “observe” what you come to believe after thinking. This might give UDT all of the information it needs to utilize generalized updates, despite “not updating”. 

diffractor testing formatting. Diffractor comments are in blue.

#### The Research Direction

For better or worse, the apparent issues with combining UDT and logical uncertainty don’t add up to an impossibility proof (at least not yet). What happens if we try harder to get something to work? Can we succeed, or in failing, provide a clear impossibility proof?

	- *(More generally: can we map the conditions under which UDT has various desirable properties, and the conditions under which it will lack those properties?)*
The main hope here is to define “observations” for logical induction in terms of *the future beliefs themselves*. I will call this the “direct” route to logical updatelessness.

There is a secondary hope, which involves stepping back and thinking about what we want from a (logically uncertain) UDT, and trying to get that more indirectly through learning-theoretic means. I will call this the “indirect” route.

(It is not at all clear that direct/indirect are accurate labels here, but whatever.)

### Terminology

A ***policy*** is a map from observations to actions. Since the idea here is to take the whole (updated) market state as an observation, this means a map from market states to actions.

A ***policy point*** is a single pairing of a market state and an action, which we can think of as an element of a policy. 

***Branches*** (as in, branches of possible futures) are understood as elements of some partition of the event-space, where all events making up the partition are also observations. The “home branch” of a policy point is the observation mentioned in that policy point. 

Given a partition of the event space into branches, the expected value calculation for a policy-point can be decomposed into a weighted sum of its *updateful* expected value *given each branch*, with each branch’s weight equal to the probability of that branch given the policy-point. 

- We can divide this into three types of consideration: the value of a policy point in its home branch; its value in other branches; and its impact on the relative weight of branches. I will sometimes use the term ***acausal correlations*** to refer to everything other than the home-branch value, although this is somewhat bad terminology. Diffractor note: The 1.01 proposal has this breakdown. The effect of a policy taking an action at a position can be broken down into “cross-branch effects” (which perturb the expected utility of a different branch), “retroactive effects” (which perturb the probabilities of the various branches), and “causal effects” (a branch perturbing its own expected utility, and you generally but not always want to defer to future-you for working out what those are)

### “Direct” Route: Perfectly Updateless Logical Uncertainty

The goal here is to directly translate UDT 1.0 into Garrabrant induction. The obstacle is that the relevant notion of “observation” is the entire market state. This makes it impossible to meaningfully condition on “Agent(obs)=act” to evaluate expected utility, because the sentence is outside of the range where the market assigns meaningful prices, due to being too large. 

Agreed. UDT1.01 would state it as follows. There are two sorts of observations, which would be called reactables and seeables. Reactables tend to be small, merely polynomially-much data that tells you where you are. They are the “observations” in the sense of the phrase “a policy is a map from observations to actions”.  Seeables tend to be large. They are “information” in the sense of the phrase “UDT1.1 must know a bunch of information about what decisions at which places have effects at which other places to compute what the optimal policy is”. UDT1.01 handles this obstacle by saying that we’re conditioning on pi(h)=A, where h is a reactable (or a position) and contains a small amount of data, and A is an algorithm that maps seeables to actions. In some sense this is shoving the large size from the observation space into the action space. However many algorithms can be described compactly rendering the overall sentence pi(h)=A manageable to think about.

And I will remark that even in the logical inductor framework, you probably shouldn’t be conditioning on the ENTIRE market state, just having your observations be “small queries about the market state”. Basically, your observations should probably be stuff like “probability of phi is between 0.3 and 0.4” instead of going “here’s my entire beliefs about everything”. I observe that I’m thinking about how I’m cold right now instead of observing the entire state of my brain.

So, one way to think about the goal here: find ways to assign more meaningful prices to very large sentences. 

Yup, 1.01 still demands that this problem be solved, because it demands that the early logical inductor timesteps be able to think about sentences of the form pi(h)=A for unboundedly long strings h.

Of course, we can’t just do this arbitrarily in a way that seems nice; rather, we need to take a principled approach, specifying meaningful desiderata.

#### The Plan

So, the plan as I see it is to dovetail over the following points, iteratively refining our ideas about each of them:

1. **Think more about notions of “large” beliefs.**
	1. I have my main conjectures about what’s necessary here, but sensible coherence conditions for attributing large beliefs to small agents is *the main philosophical underpinning to the approach to UDT outlined here*, so it might be worth thinking more broadly about this.
	2. The troubling thing is that we want some notion of large beliefs “without further computation”, because the large beliefs are supposed to reflect the current state of logical uncertainty. But in reality, large beliefs will always require further calculation. (yeah, this is one of the issues that UDT1.01 is still sweeping under the rug)
	3. So, more precisely, what we want is: larger beliefs which *correctly represent the small-belief’s implied uncertainty about the large*. 
		1. The test for success here is to construct UDT based on the large beliefs, and then check whether the small beliefs are happy to use the large beliefs to make decisions; IE, the correct “large” beliefs are precisely those such that LIDT systematically prefers UDT over other options. (1.01 sorta passes the informal version of this test stated in the first sentence, although in a way I think is skew to what you’re intending.)
2. **List desirable properties for UDT.**
	1. Supposing we had a completely fleshed out proposal for logically updateless UDT, what could we prove about it to boost our confidence that it’s a good decision theory?
	2. What assumptions and intermediate lemmas might we expect might be useful or interesting?
3. **Try to write proof sketches for the most important desiderata,** assuming the UDT looks roughly like we expect.
	1. This helps us become clear on what properties the UDT would need to have, in order for us to prove the desiderata.
4. **Try to fully formulate the UDT, such that it fits the proof sketches and satisfies the desiderata.**
	1. **Nail down the picture in which the “observations” are simply the next belief-state.**
	2. **Specify a version of logical induction that is both propositionally coherent and “real-value coherent”**
	3. **Check what other properties we still need in order to satisfy the assumptions of our proof sketches.** Figure out how to get those properties, or else, how to revise them such that they’re both achievable and useful. Yup, this is a huge issue for 1.01. It assumes some… pretty strong properties in the proof, and one of the major ones is the presence of an oracle which can be queried with certain questions. And if you try to make a logical inductor play the role of that oracle then you run smack into a bunch of the questions you were pondering.
5. **Try to prove nice theorems about the behavior of the resulting UDT.**
	1. Flesh out the proof-sketches made earlier and check that they do indeed work.
	2. Think of more things we might want to prove about the proposed UDT.
6. **Consider critiques and attempt to address them.**
7. **Try to remove assumptions and generalize as much as possible.**
	1. The first version might have more assumptions than we really need, simply because we threw all our ideas at the problem to try to get something to work. But the less structure we assume, the more powerful the results are.
8. **Look at what separates this from a full theory of alignment. What more would we need, for this toy model of “large agents serving small agents” to become applicable to the relationship between humans and AI?**

#### Desiderata, Lemmas, Assumptions, & Other Important Propositions

The following desiderata are a mix of “final goals” (things we might want to prove in the end, to show that a version of UDT is good in some sense), “lemmas” (things we might prove in the middle, on the way to the final goal) and “assumptions” (things we might assume in order to get things going). So, part of the project here is to sort these things out.

- Beliefs and value estimates for large sentences should “cohere” with those for small sentences. For example: if my small-sentence beliefs hold that I’ll soon face a Transparent Newcomb and 2-boxing (upon seeing the large box full) means I in fact will see the large box empty, then my large-sentence expectations should reflect this appropriately, so that conditioning on such a policy-point yields the right expected value.
	- There are a few kinds of “coherence” which seem (speculatively) important. I am stating these in English rather than math, to highlight the importance of considering several alternative translations into math as part of this research.
		- **Epistemic Self-Trust:**
			- Logical induction has the property that it *eventually* trusts its own future beliefs to be more accurate. It’s probably important for UDT that the prior *already* has this property, from the beginning.
		- **Small marginalize large:** 
			- If small beliefs hold that I’ll believe such-and-such in expectation, then large beliefs about the entire range of future possible beliefs for me should agree with this expectation.
			- If small beliefs hold that I’ll probably come to either fully believe or fully disbelieve X soon, then large beliefs should be similarly bimodal about this; future market states which still have significant uncertainty about X should be (proportionately) improbable compared to market states where I become certain.
			- Similarly, if small beliefs show some complicated joint distribution between the future beliefs about several propositions or random variables, large beliefs about future market states should reflect this.
			- We can think about this requirement as: *UDT’s probability distribution over future “branches” should fit with the relevant small beliefs about this.* (”Branches” here means “branches of possibility”, ie, ways the future can evolve, as represented by future observations.)
		- **Sensible action consequences within-branch:**
			- When UDT considers taking an action within a branch (ie, upon seeing an observation), one component of its deliberation is the consequences of that action within that same branch. This is the “updateful” component — if all of the other considerations are negligible, then UDT should behave as if it had actually updated.
			- So when we condition on the large sentence “the agent does action a inside observation o”, then the component of that calculation where observation o actually occurs should look like we’ve actually taken action a.
			- Putting this more subjectively, in order for large beliefs to represent small beliefs appropriately, the consequences of a policy point in its home branch should respect any relevant small beliefs.
			- For example, if the small beliefs say “if I ever break this urn in the future, I’ll be in big trouble”, then when considering an urn-breaking action, UDT should indeed think that utility will be low in that action’s branch.
		- **Sensible action consequences** ***across*** **branches:**
			- Another component of UDT’s expectation for a specific action is whatever consequences that action may have in other branches.
			- To be more precise: we can partition the expectation into any set of mutually exclusive and jointly exhaustive observations we like. (There are many such partitions, since we can choose to look at “larger or smaller branches”, ie nearer to the present vs farther into the future.) UDT’s expectation for an action is a weighted mixture of the expectation within each branch, given that the action is taken within its home branch.
			- So for this expectation to be sensible, we need large, updated beliefs about action consequences to reflect small beliefs, not just within the “home branch” of the action, but also within all other branches.
			- For example, if I believe that I may face a counterfactual mugging, then the large beliefs used for UDT’s calculations need to accurately reflect the consequences of giving up the \$10 — not only should UDT expect to lose \$10 in those branches; it should also expect to gain \$100 in the other branches associated with the counterfactual mugging.
		- **Universal Instantiation:**
			- If my prior contains a small but quantified belief like “in any situation where Omega tells me that pushing a button will give me \$10, then pushing that button will give me \$10”, then it seems like I need to also believe all of the infinitely many instantiations of this belief, in order for “large beliefs to properly reflect small beliefs”.
			- This property appears to be important for UDT to work as expected, particularly when we have important quantified statements over large belief states. I will aim to include some examples later. 
			- However, the property might also cause some trouble.
			- (To give clear credit: Martin Soto came up with the Universal Instantiation idea.)
		- **Small** ***hypothetically*** **marginalizes large:**
			- If I believe that policy-points which press the red button when I’m in a pessimistic (ie, low-expected-utility) belief state are always extremely bad, and I condition on such a policy point, I still need one more thing in addition to universal instantiation to connect the dots and conclude “this is extremely bad”: I can’t just instantiate the “X(belief) → extremely bad” universal; I also need to be able to evaluate X(belief) to true when it is so.
			- I call this “hypothetical marginalization”. My idea for formalizing it is that we have expressions which say something like “marginalizing out variable X in big belief description Y gives value Z”, and we are completely updateful about these — ie, UDT just already knows their value, in the prior (perhaps with some epsilon uncertainty).
		- **Sensible branch re-weighing:**
			- Finally, if the small beliefs think that an action will re-balance the weights of different branches, then the large beliefs used to compute UDT need to correspondingly do so.
			- For example, if the small beliefs see a possibility of facing a Transparent Newcomb problem, then 1-boxing upon seeing an empty large box should make the probability of seeing such an observation much smaller (zero, if Omega is supposed to be a perfect predictor).
	- In reality, we want to figure out which of these coherence conditions are critical for decision-theoretic purposes, and ignore any that aren’t (to keep the theory as simple and general as possible).
- In addition to “coherence”-like properties, there will no doubt be some important decision-theoretic properties which we need to assume in order to get arguments going, even though we do not actually believe those assumptions apply to the real world.
	- **The no-traps assumption:**
		- Assuming this work gets all the way to learning-theoretic properties, it may be necessary to assume that there are “no traps”; IE, that no one action will spoil rewards forever. This assumption is needed for exploration to be rational.
	- **No coordination problems.**
		- Since we want to investigate UDT 1.0 first, and defer the problems solved by UDT 1.1, we need to assume that there are no coordination problems — that is, assume that the prior puts negligible probability on coordination problems, and the environments don’t provide systematic evidence toward such hypotheses.
		- Basically, this means: assume that, while policy points *can* impact the expected value of other branches, they *cannot* shift the *relative* expected values of *other* policy points (too much). We can’t have a stag-hunt situation where we need to know what our other selves are doing in order to do the right thing ourselves.
	- **Omega doesn’t care about things forever:**
		- In order for UDT to learn, it should be the case that UDT doesn’t assign significant probability to possibilities where one branch cares about infinitely many policy-points belonging to a different branch. (And also, the actual environment does not provide systematic evidence for such things.) Yup, I’ve got a formalization of this problem in terms of “influence measures”. If summed influence measure is high at a spot it messes up actions forever, and if it’s low at a spot then it means that making things go well at the spot only makes “bounded demands” of the agents behavior at other places. So it lets you test whether a given proposal for working out acausal effects would be the sort of thing that results in beliefs that makes “unbounded demands”.
	- **Agent-Environment Separation:**
		- In some sense, it should only matter *what policy the agent chooses*, not how they think about choosing that policy.
			- There’s a difficulty around defining this precisely: if Omega looks ahead to future actions in order to decide current actions, then some combinations of decision problem and agent will be inconsistent.
		- A different version of this assumption is one where *only actions actually taken matter*. 
			- For example, it’s interesting to think about problems where Omega uses a logical inductor to predict, and can only look at actions which have been taken in the past of the actual branch.
			- It’s also interesting to consider cases where Omega also gets to look at the output of the agent’s UDT on alternate observations (ie, alternate market states).
- **Logical updatelessness should preserve the benefits of updating, if at all possible.**
	- One of the big concerns with logical updatelessness is that it’s going to be really stupid, because an early garrabrant-induction state is just some arbitrary non-optimized stuff. We want to explore conditions under which this concern is valid or invalid. Use influence measures.
		- Show that this UDT behaves updatefully when appropriate.
			- Fully replicates LIDT when actions have no impact on other branches or on relative probability of branches. Not LIDT, per se, but yeah, 1.01 gets this.
			- Updates “as much as possible” in the presence of situations calling for UDT; EG, in counterlogical mugging, we would like to be able to show that it can update to reasonable estimates of the coin’s logical probability (as opposed to the terrible estimates from the very first market state). I’d have to double-check, but I strongly suspect the “conservation of expected influence” correction term being large instead of negligible corresponds precisely to situations where the agent flips from wanting to update to not wanting to update, and that might provide an angle of attack on this. Because it’s large precisely when past-you is like “future-me is going to predictably overestimate/underestimate the effects on utility of playing action a here.”
			- “Fine-grained” updates: we would like to show, if possible, that our UDT can behave updatefully wrt some propositions even if it cannot behave updatefully wrt others.
				- This is to address concerns that the most-updated market state that avoids all the forbidden knowledge is still not very updated. 
				- Example problem: Counterlogical Mugging With Homework. 
					- This is like a normal counterlogical mugging, but in order to give Omega the money, you have to speak the digit of pi aloud. This demonstrates a single action which simultaneously makes updateful use of information, while remaining updateless in order to evaluate the impacts.
	- If possible, establish good learning-theoretic results for UDT.
	- We want to formally specify what it means for an early belief state to think that “UDT concerns” are negligible, and show that in this case, our UDT amounts to a sensible updateful DT. 
		- This basically means our prior thinks that cross-branch concerns are negligible: which action we take in the current branch does not have a significant impact on utility in other branches, nor does it significantly modulate the probability ***of*** branches. (”branches” really means “observations” ie belief states.)
			- Under this condition, it makes sense that the relative value of different A(belief)=act amounts to the relative value of acts within the given belief state. Other differences in the global expectation calculation have been assumed away.
		- A quite different way of formalizing this: UDT thinks the policy which is updateful on a fact, X, cannot be significantly improved upon. (IE, UDT would endorse first updating its prior about X, then evaluating policy points.)
	- But of course, the early belief state need not *actually* believe that UDT concerns are negligible. Furthermore, this doesn’t seem like a property we want to enforce; if it were, we could just use updateful decision theory. 
		- One idea would be to establish conditions under which early UDT considerations eventually “wash out”. (washing out happens precisely when influence measures are low.)
			- Intuitively: Omega never demands *unbounded* commitments; cross-branch correlations only ever tangle up finitely many things.
			- This isn’t a *necessarily true* condition, but it is a kind of sanity condition; otherwise, a rational agent could have totally arbitrary behavior, because its early logical uncertainty contained some sufficiently expensive threat requiring arbitrary behavior of it.
				- So really one might want to ensure that an AI prior satisfied this condition *to a high degree of approximation*, such that the AI can later decide to keep unbounded commitments if a preponderance of evidence shows them to be important.
			- One way to formalize this idea is to say that for every LI_n, there is a time after which the UDT always acts as if it has updated its prior on LI_n.
				- The strongest version of this not only implies that the prior endorses policies which (eventually) behave updatefully with respect to LI_n; it *also* implies that *all LI_n* endorse policies which have this property (IE, policies which eventually behave as if updateful wrt LI_m, for all m>n).
			- Universal Instantiation might make it significantly more difficult to analyze when this is the case, however.
				- Without Universal Instantiation, we could have relied on the idea that early market states only have “strong opinions” about finitely many things (so perhaps a prior which extends small beliefs to large beliefs only believes in correlations within some specifiable bounds).
				- With Universal Instantiation, this idea becomes, at least, much less clear.
		- My hope is that these conditions allow for some good learning-theoretic results, where our UDT eventually behaves appropriately for a given sequence of decision problems. However, the form of such a result is not clear to me, and this gets into issues with the “indirect” route to be described in the next section.
			- (I have become less hopeful about this over the summer, but it would still be very interesting to know one way or the other.)
		- A related hope would be to go for some notion of subjective optimality, in which early considerations “wash out” precisely when the agent is OK with that (IE would not be motivated to self-modify out of this). 
			- For example, it’s intuitively OK in counterlogical mugging to update from a bad distribution over digits of pi (eg, simplicity-based) to a uniform distribution; but any specific calculations of the digit get us into territory where the Omega may spoof our calculations within its simulation. (Depending on how (we think) Omega works.)
				- So in this case, our UDT should act as if it has updated to the latest point before Omega would interfere with any calculations.
			- Generally speaking, Omega should be OK with agents reasoning enough to understand the decision problem being set up. Having some formal representation of this (”if Omega seems not to interfere with such-and-such reasoning to understand the nature of the decision problem, then our UDT acts as if it is at least that logically updateful”) would be reassuring with respect to the question of logically updateless agents being stupid/crazy due to their ignorant and poorly optimized prior.
- **UDT should tile.**
	- IE, under what assumptions can we show that UDT would not assign significantly higher expected value to pulling a self-modification lever, as opposed to not pulling the lever?
		- This may have many interesting versions, such as considering cases where UDT would/wouldn’t change its beliefs, would/wouldn’t choose to make precommitments for itself, etc.
- **UDT should perform optimally in some more “objective” sense.**
	- IE, there should be some “nice” class (of “fair” situations) in which, if UDT knows which situation it is in, UDT performs optimally in some objective-ish sense.
		- “objective-ish” because in situations including logical uncertainty, objectivity becomes a bit hard to work out; although we can use tricks such as talking about limiting frequencies of specific sequences of logical coins.
	- And in particular, it would be nice to show that this class is strictly larger than some related class in which updateful reasoning is optimal. (This is another way of saying “logical updatelessness does not make you lose out on the good things about logical updatefulness”.)
	- The optimality notion obviously needs to account for limited processing power somehow.
	- Under some assumptions, it will be the case that the optimal thing is always logically omniscient. This conceptual issue needs to be faced properly.
	- There’s a potential problem with “evil” decision problems, where Omega just happens to do whatever makes things bad for any agent equivalent to ours, and make things good for other agents. (”Omega puts the money in whichever box UDT would not choose.”)
		- For MUDT, the optimality result had to deal with this; eventually, what was shown was that problems where MUDT performed sub-optimally were “only because of this”. More precisely: MUDT can always perform optimally *if it uses a sufficiently powerful logic*. 
			- Perhaps our UDT can be shown to perform optimally *if it has access to sufficiently strong logical inductor states as observations*, where strong might mean processing power, or the power of the logic used for the deductive process, or some combination.
- **Other DTs should prefer to re-write to our UDT.**
	1. More formally: if LIDT faces a sequential decision problem, in which it has repeated opportunities to either precommit to follow the UDT strategy for some number of steps, or some other strategy, it will eventually not disprefer UDT.
		1. (We cannot so easily show, in a realistic learning-theoretic setting, that it would self-modify to become UDT forever. Since such a change is permanent, it cannot be tried repeatedly to reach good estimates of its value. So, this kind of full self-modification is necessarily a question of *how good the prior is* rather than how well it learns.)
	2. Stretch goal: if it’s able to choose between different time-length commitments, it will not disprefer the longest available commitment to UDT. 
		1. (This helps get us closer to establishing that you’d want to become UDT for as long as possible, even tho we still can’t address full self-modification to permanently become UDT in this kind of setting.)

Somewhat more formal and mathematical thoughts on desiderata follow. These are somewhat redundand with the above, and a better-organized document would merge some things and organize some things differently.

**Small Marginalizes Large**

Or, putting it a different way: UDT’s branch probabilities sensibly extrapolate small beliefs into a big joint distribution over the probability of future “branches”, ie observations, ie market states.

Some versions of this demand:

- BLI’s properties.
	- $\mathbb{P}_{n-1}(\phi)= \sum_{\mathcal{Q}}\mathbb{P}_{n-1}(\mathbb{Q}_n=\mathcal{Q})\mathbb{P}_{n-1}(\phi | \mathbb{Q}_n=\mathcal{Q})$
		- That is: my earlier belief in phi reflects what I would to believe about phi given what I might observe at a later time, weighed by the probability of each of those possible observations.
	- $\mathbb{P}_n (\phi | \mathbb{Q}_{m}=\mathcal{Q}) = \mathcal{Q}(\phi)$ when m>n and $\phi$ contains no info about market states later than m
		- That is: ‘large’ statements about future market states are trusted.
	- $\mathbb{P}_{n-1}(\phi)= \sum_{\mathcal{Q}} \mathbb{P}_{n-1}(\mathbb{Q}_n=\mathcal{Q})\mathcal{Q}(\phi)
$
		- That is: small beliefs *are just* the marginal expectations of our joint on large beliefs.
		- This follows from the previous two requirements.
- Propositional coherence.
	- If both small beliefs and large are (always defined, and) propositionally coherent, then there is a joint distribution over any set of propositions, since we can ask about large conjunctions made up of all of the propositions in the set or their negations. Furthermore, joint distributions over fewer variables will always equal the marginals of the larger joint distributions, thanks to propositional coherence.
- LUV coherence.
	- This accomplishes for LUVs what the previous point accomplishes for propositions.
	- Since all beliefs about propositions are themselves LUVs, this gives us a kind of coherence with respect to our beliefs about our beliefs, which was not given by propositional coherence alone.
	- Relationship to the BLI properties?
		- LUV coherence implies that small beliefs about future beliefs marginalize large beliefs about whole future market states.
		- If we further require that beliefs always equal the expectations of future beliefs (which is already approximately true for small beliefs in logical induction), then we get the final BLI property, that small beliefs are precisely the expectation of the large future beliefs over market states (marginalizing out all of the other stuff in our large future joint distribution over market states).
		- LUV coherence plus conditional trust in future beliefs (ie, $\mathbb{P_n}(\phi | \mathbb{P}_m(\phi) = p) = p$ for $m > n$), which is again approximately true for small beliefs already, implies *all* of the BLI conditions, if I’m not mistaken.
			- Conditional trust in future beliefs implies that current beliefs equal expected future beliefs.
			- Conditional trust plus LUV implies the BLI property of adopting market states when conditioning on them.
			- …
	- Hence, propositional coherence + LUV coherence + conditional trust plausibly implies every desirable property mentioned within this subsection, and perhaps more.
**Sensible within-branch action consequences:**

I see two important versions to consider:

- Conditioning on a ‘policy point’ ($A(obs= \mathcal{Q})=a$ where $\mathcal{Q}$ is a large specification of a market state, $A()$ is the observation-to-action function, and $a$ is an action) and also conditioning on the observation associated with that policy point ($obs = \mathcal{Q}$) should just give us exactly the updateful version of considering that action.
	- That is: the consequences of an action within its own branch should just be the updateful picture. This sounds like an important condition for establishing a “UDT behaves updatefully in the absence of considerations to the contrary” picture.
	- This implies that we should believe $\mathcal{Q}$ upon conditioning on it, as in Sam’s picture.
	- (On the other hand, perhaps Sam’s condition is stronger than necessary for behaving updatefully in the absence of reasons to the contrary — eg, seeing a very suspicious looking $\mathcal{Q}$ could itself constitute ‘reasons to the contrary’.)
- Conditioning on a policy point together with the associated observation should *sensibly respect small beliefs* about this contingency, as well.
	- EG, if the small beliefs say that breaking a vase in the future would be really bad, then conditioning on policy-points which would break vases should look bad within the home branches of those policy-points.
**Sensible action consequences across branches:**

Again I see at least two important conditions here: 

- If a branch thinks that policy-points of a different branch are relevant to its own expectations, then when the UDT conditions on those policy-points, it should see those consequences.
	- EG, a branch which thinks it is in the “Omega might give me \$100” branch of a counterfactual mugging should increase its expected utility when conditioned on a policy-point which gives up the \$10 in the other branch, and decrease its expectation when conditioned on a policy-point which refuses to give up the \$10.
	- One interpretation of what I want here is that when I am considering one branch, which has a (small relative to it) belief that another incompatible branch has a large impact on its utility (eg in counterfactual mugging), I want to actually see that impact when I condition on the large sentence which says I take the action in the other branch.
		- But! A tricky point about defining this is the amount of correlation between similar branches. Again consider counterfactual mugging. If I condition on, in a single alternative branch, I don’t pay up, how do I update about the *average* such branch? 
			- (Or whatever concept is relevant to Omega’s reasoning about us — maybe average is not quite right. Omega might aggregate somehow, or Omega might pick an individual case to check, or Omega might do something else entirely.) I mean, I guess Omega will be thinking about our concrete branch, not any average. But given our formalism of Omega using an LI, it’s true the state of Omega’s LI depends on previous action-points (and in fact, syntactic properties of our algorithm more generally), so it’s not clear exactly which of our action points influence Omega’s decision.
		- The small belief in the might-get-a-lot-of-money branch which says “I need to give up \$10 in the other branch to get a lot of money in this branch” is, obviously, small; so …
		- What would a small belief *about* the correlations of the large branches even look like?
			- To say “X is correlated to Y” we need to be able to say X and Y, but in this case these are large.
			- Some crazy sentence like “these are all correlated” (quantifying over some class)?? This seems like a belief *about our large beliefs*, which is weird. Somehow I think large beliefs should be derived from small beliefs, but not from small beliefs *about* large beliefs. But maybe it is ok?
- If the *small* beliefs think that policy-points of a specific sort will have specific sorts of cross-branch consequences, then the large beliefs used by UDT to judge consequences should reflect this (at least in expectation).
**Sensible branch-weights when conditioning on actions:**

- If the small beliefs think that specific sorts of policy-points would alter branch probabilities in a particular way, then the large beliefs used by UDT to judge action consequences should reflect this.
	- EG, 1-boxing in Transparent Newcomb upon seeing an empty large box should greatly reduce the probability of branches where we see the empty box.
‘**No’ Added Information In Large Beliefs:**

This condition is tricky. The basic idea is that large beliefs should not sneak in important logical updates. However, of course, large beliefs *do* contain ‘more information’, since the small beliefs by definition don’t know what the large beliefs are, specifically. Really, what we want to check is that large beliefs don’t contain a type of information which creates an incentive for the small beliefs to avoid using the UDT — EG, if Omega poses some sort of counterfactual mugging based on the details of the large beliefs. Perhaps it is sufficient that the large beliefs do not have detailed reflective knowledge of themselves which is not possessed by the small beliefs?

An obvious sort of condition to think about is maximum-entropy (ie, large beliefs should be max-entropy with respect to all the coherence constraints we want to impose upon them). However, I find it difficult to see how this could be the exact thing we need to make the decision theory work out, so I can’t say this is an especially promising direction.

**LIDT prefers to re-write to UDT:**

Rough outline of how we might prove this:

- Suppose some other policy (specified as a program) looks better than switching to UDT. 
- Due to a ‘fairness’ assumption (the environment only cares about the agent’s observation-to-action function, not how it computes those actions), the *actions* suggested by the policy must look good.
- Due to the no-coordination-problems assumption, it must be that the *individual* actions look better than what UDT would choose.
- But UDT just chooses the actions which look best; contradiction.
	- (This, of course, doesn’t explain how we bridge the small-to-large belief gap within the proof; LIDT only uses small beliefs, while UDT uses large beliefs to choose what’s best, so we need to somehow account for the difference.)
**UDT does not prefer to re-write to anything else:**

Rough outline of how we might prove this:

- Suppose some policy (specified as a program) looks better than continuing to use UDT.
- Due to a ‘fairness’ assumption (ie, actions are what matter, not how they’re computed), the action profile itself must look better.
- But due to the no-coordination-problem assumption, *individual* actions must look better.
- But UDT just chooses whichever individual action looks best, so it would do whatever this proposed policy does, if the actions taken by the proposed policy look better. Contradiction.
	- (Notice that this seems simpler to establish than the LIDT-rewrites-to-UDT version, since UDT already uses ‘large’ reasoning, so we don’t have to relate small to large as much.)
**UDT behaves in a fully updateful way when appropriate:**

**UDT updates as much as it can:**

**UDT updates in a ‘fine-grained’ manner:**

**UDT learns:**

**Self-Trust of Prior**

The small beliefs should not believe that some other set of small beliefs (which can already be computed) would result in better expected utility when plugged into the UDT. (This seems like it’s probably a necessary thing to enforce in order to get tiling... unless we somehow get this from other things.)

#### Formulations to Fit Desiderata

1. **Try to fully formulate the UDT, such that it fits the proof sketches and satisfies the desiderata.**
	1. **Nail down the picture in which the “observations” are simply the next belief-state.**
		- There is a thing called BLI, Bayesian Logical Induction, which might be sufficient. The idea here is to force logical induction into a bayes-update framework, such that updating on a description of the next market state puts us into that very state. This is due mainly to Sam.
			- $\mathbb{Q}_n$ is a ‘base’ logical inductor, defined in the normal way, which we’re going to modify.
			- $\mathbb{P}_n$ is the BLI we are trying to define.
			- $\mathcal{Q}$ is a (meta-logical) variable representing arbitrary market states. 
			- Strategy: the level of a sentence is the highest n of any sub-sentence of the form $\mathbb{Q}_n=\mathcal{Q}$. We define the level’s probability distribution (according to $\mathbb{P}_1$) successively.
				- We will keep all the “small” beliefs from $\mathbb{Q}_n$, only editing “large” beliefs (ie those containing $\mathbb{Q}_n=\mathcal{Q}$); since the logical induction criterion only cares about the “small” beliefs, $\mathbb{P}_n$ will still be a logical inductor.
			- $\mathbb{P}_n (\phi) = \mathbb{Q}_n (\phi)$ when $\phi$ contains no info about market states later than n.
				- “no info” is just the syntactic notion, but it might be interesting to consider what happens when there are non-syntactic mathematical correlates (EG, sentences of PA which are provably equivalent). Does something weird/concerning happen? Can we construct a case where UDT fails to act like it has control over a copy, for example?
			- $\mathbb{P}_n (\phi | \mathbb{Q}_{m}=\mathcal{Q}) = \mathcal{Q}(\phi)$ when m>n and $\phi$ contains no info about market states later than m
			- If $l<m$ and $l<n$, then  $\mathbb{P}_l(\phi|\mathbb{Q}_n=\mathcal{Q}, \mathbb{Q}_m = \mathcal{Q}') = \mathcal{Q}({\phi})$ if m<n, and $=\mathcal{Q}'(\phi)$ otherwise. (Unconstrained if m=n and $\mathcal{Q} \neq \mathcal{Q}'$)
			- $\mathbb{P}_{n-1}(\mathbb{Q}_n = \mathcal{Q})$ beliefs must balance:

$$
\mathbb{P}_{n-1}(\phi)= \sum_{\mathcal{Q}}\mathbb{P}_{n-1}(\mathbb{Q}_n=\mathcal{Q})\mathbb{P}_{n-1}(\phi | \mathbb{Q}_n=\mathcal{Q})
$$

$$
= \sum_{\mathcal{Q}} \mathbb{P}_{n-1}(\mathbb{Q}_n=\mathcal{Q})\mathcal{Q}(\phi)
$$

			- A solution to balance the beliefs should exist, since the number of constraints is small compared with the size of the space. 
			- Still, there is an interesting question here of “reasonable” distributions $\mathbb{P_n}(\mathbb{Q}_m=\mathcal{Q})$. For example, if the inductor is virtually certain that it will come to know whether $\phi$ in the next belief state, the distribution on next belief states should reflect this. Only requiring the expectations to balance doesn’t capture this.
		- BLI intuitively represents a Bayesian who 100% trusts a logical inductor. It might be interesting (perhaps even necessary?) to represent a lower degree of trust in the inductor, such that *the next market state is indeed a fixed point of updating on observing the next market state*, but this only holds for $\mathcal{Q}$ which are actually fixed-points of the market, rather than arbitrary $\mathcal{Q}$.
			- So the Bayesian update on belief can now be interpreted as a “correction” of the observed beliefs; “If I believed X, then I would prefer to believe Y instead.”. The next belief state is found by searching for a fixed-point that has no remaining corrections to make.
			- Scott and Benja both worked out (different) thingies like this a few years ago, but I don’t have detailed notes on them. 
	2. **Specify a version of logical induction that is both propositionally coherent and “real-value coherent”**
		- Propositional coherence is the thing where we precisely enforce rules like P(a & b) + P(a or b) = P(a) + P(b), rather than just getting these things approximately. Notice that this is a kind of coherence constraint on “large” sentences!
		- “real-value coherence” or “LUV coherence” would similarly impose consistency requirements on distributions over LUVs (logically uncertain variables, ie, real-valued expressions). 
			- IE, the probabilities add up as a distribution over ‘worlds’ where we assign specific values to real-valued expressions.
			- (Perhaps this has to be perfect to within some epsilon, rather than truly perfect.)
		- My intuition is that LUV coherence provides most of what we need. A LUV-coherent BLI must have a distribution $\mathbb{P}_n(\mathbb{Q}_m=\mathcal{Q})$ which agrees with all *small* beliefs about the distributions of *particular* market prices in $\mathbb{Q}_m$. So LUV coherence appears to be enough ‘sensibly extrapolate’ all of the small beliefs about things that traders can trade on, into big beliefs about the probability of going down specific branches of evolution of our beliefs.
			- And in particular, I’m conjecturing that LUV coherence is almost enough to give us a reasonable evaluation of the expected utility of policy-points Agent(obs)=act. 
	3. **Check what other properties we still need in order to satisfy the assumptions of our proof sketches.** Figure out how to get those properties, or else, how to revise them such that they’re both achievable and useful.

#### Sam’s BLI vs Alternatives

#### What about UDT 1.1?

It would be even better to get UDT 1.1 into Garrabrant induction, obviously, but how do you condition on a “whole policy”? That’s apparently an infinite sentence which accounts for all possible observations. Even if you could do it for one policy, you’d have to *compare all the alternatives*. 

So it at least seems better to start with UDT 1.0. 

I have hopes that the gap between UDT1.0 and UDT1.1 can be bridged in other ways. If we can find good ways for agents with common interests to cooperate, then we can apply those to the single-agent case to ensure that UDT1.0 finds an equilibrium with itself amounting to what UDT1.1 would recommend. 

I also have some other ideas for how to get UDT1.1… but they’re all probably bad.

### “Indirect” Route: Learning Updateless Reasoning

The so-called “direct” route attempts to strap UDT on top of Garrabrant induction in the same way that UDT is strapped onto normal probability theory.

The so-called “indirect” route instead seeks to learn UDT-like behavior over time, by integrating UDT’s optimality notion into the loss principle which guides learning.

This route currently seems pretty doomed to me, due to working hard on it several times over the years without coming up with anything. But I also haven’t gotten any sharp impossibility results, which would be interesting to get.

The approach might involve modifying Garrabrant induction, or modifying BRIA, or combining the two somehow. 

BRIA can implement an approximation of UDT by imposing computational limitations on the bidders, and making them select policies (EG, specified as computer programs). This is not very satisfying, because it involves an arbitrary cutoff for the level of processing power used. It’s similar to LIDT policy selection using some ‘sufficiently early’ market state, EG using the log(n)th market state for the nth decision problem.

The desired property is something like: for any sequence of decision problems, the learner will eventually approach the sequence in an optimal manner. But if the optimal counterlogical mugging strategy is to hand over the money, the optimal strategy for the sub-sequence where omega asks for the money is to keep it. How are we supposed to trade off between these two subsequences? 

If we think of tiling as the goal, we might say: is there some decision-point at which the agent would fail to tile? Which way of balancing between different subsequences eliminates the incentive to self-modify?

I have more notes on this which I could attempt to make sensible, but I think they’re largely flailing around without nailing down too many concrete details.

## Dump of more recent UDT notes (quite unpolished)

- Immediate concerns to raise with Soto?
	- My tiling concern wrt Soto's forced-update prior suggests that there's a problem w the tiling argument so far, or a problem w the forced-update prior.
		- Well, Martin admits that he only gets the weak property, which in some sense doesn't tile.
		- Martin also separately decided that our foundations are broken anyway; see **A foundational problem**.
		- But do I expect that this is ultimately going to be a problem?
			- Maybe we can talk about the degree of update-eagerness of a prior, and talk about the limit as this goes to max, while admitting that anything following LIC will have some degree of non-dogmatism about updatefulness, and therefore won't be completely updateful wrt every possible tree.
			- Or, more nuanced, for any "speed of update" we wish ho discuss, we have a degree of trust in that. So we can talk about priors which approach perfect enforcement of the learning desideratum (eventually acting like any Q_n) without approaching perfect updatefulness (acting like Q_n at the node Q_n is observed).
				- f-updatefulness: behaving as if we use Q_f(n) at time n.
			- The result we're looking for is something like: for each environment, there is some epsilon such that if the agent's belief in acausal correlations is below epsilon, and the environment doesn't systematically introduce such correlations, then the performance of UDT will eventually be optimal in that environment.
	- The 'impossibility result' ideas didn't make a lot of sense to me.
		- In particular the attempted def of "learning".
		- Seems like the real underlying idea is limiting average reward (vs expected utility).
		- Maybe this should be reformulated as a version of Vanessa's thing, where any given agent must have bounded utility and therefore something like temporal discounting, but to examine learning we consider the limit, because any particular discounting rate may rationally block learning on a specific problem.
			- This gets augmented with driving endorsement of f-updatefulness
	- my idea for evil logical coins
	- universal learning questions
	- Other notes from the Soto call:
		- A lot of thoughts on the 'boundaries' stuff.
			- Martin seemed to think that there were a lot of possibilities but all of them failed for a small set of common reasons. My intuition is more like, there are a lot of possibilities and there's some degree of convergence to similar conclusions in each (a conclusion which has some good news and some bad news).
			- That is: Martin seems to think there's no good solution to the boundaries problem; I seem to think that there are several OK ways of thinking about it, all of which have some flaws, but most of which provide evidence in favor of a common way of thinking.
			- I wish I could provide a more thorough summary, though.
		- My concerns for losing LIC. Hopes for preserving LIC.
		- Analogy to no-traps.
		- Analogy to Vanessa's framework where we consider the limit of no temporal discounting.
		- Full list of assumptions that we know of?
		- Thoughts on realism about logical probabilities.
		- Acting updateless due to iterated problems despite 'actually being updateful' due to using a frame for decision problems where we think of Omega as only having access to the actions we actually perform.
		- Loose language:
			- It seems very tempting recently to use "update", "updateful", "updateless", "updatelessness", etc in ambiguous ways.
				- Actually updating, IE updating as part of one's decision procedure.
				- Behaving in a way compatible with updating; EG what UDT does when it doesn't believe in any acausal correlations.
				- Actually being updateless as one's decision procedure vs behaving in a way compatible with UDT (eg, as a result of reputational concerns in an iterated game)
				- Martin was using "argmaxing" in a way that felt very dangerous to me as well. Literally it just means taking the max value of some EV calculation. Martin seemed to use it to imply logical omniscience and perhaps other things.

- Notes on recent Soto emails. `UDT` `LUDT` `logical uncertainty` `Radical Skepticism` `logical updatelessness`
	- Goals?
		- Review the whole theory for LUDT, comparing with my initial notes.
			- Fill out the initial notes with added notes about my understanding of the current status.
			- Look for holes or things I think can be done better.
			- Convince myself that it makes sense (or doesn't).
		- Think over the o->a vs A(o)=a problem.
			- Clarify my thoughts on the happy-dance problem and Soto's claim that A(o)=a does not solve it.
			- Look for a variation of Soto's setup which does the A(o)=a thing.
		- Come to a better understanding of the consequences of Universal Instantiation.
			- Consequences for inferential semantics of quantification, if any.
				- Thoughts on the current status of the Gaifman condition.
			- Importance in the UDT theory.
				- Places where we need it to make arguments we want to make.
				- Senses in which it might block learning.
					- Dashed hopes for bounded correlations.
					- Concern that because of limits to the 'correctness' of beliefs about universals, anywhere where we rely on those probabilities for DT arguments will not have good learning properties.
		- Understand how we can constructively edit the prior to force "learning" for UDT.
			- How does this avoid breaking universal instantiation?
				- Does this address the concern that universal instantiation dashes hopes for bounded correlations?
				- Does this address the concern that universal probabilities are too poor for learning?
			- How does this avoid breaking LIC?
				- If we learn that there are inter-branch correlations, how can we forget without breaking LIC?
		- Understand what problems Soto sees for UDT, and to what degree I agree.
			- Understand his attempted statement of an impossibility result.
				- What did he mean when he said that the action-only version yields no problems?
				- 
			- Consider variations of the "learning UDT" hope that was dashed.
				- Does "eventually update" combined with LIC give us a plausible open-minded UDT?
				- Versions where there's a speed-of-update consideration?
					- Impossibility results around "no slowest speed"??
			- Consider variations of impossibility idea.
				- Understand learning vs stubbornness.
				- Consider status of "evolutionary" arguments for updatefulness.
				- 
			- Analyze my infinite muggings on the same coin problem more thoroughly.
				- Different problem scenarios?
				- What's the point?
				- What can or can't we accomplish?
			- List all "reasons for pessimism" / "negative result" / "potential negative results":
				- 
		- Think about agent-environment boundaries and what Omega can "fairly" depend on about our policy.
			- The idea of UDT is to depend on the full policy, but thinking about logical uncertainty reveals this as a subjective counterfactual.
		- Understand the 'instrumentality' stuff better.
			- Understand Soto's instrumental construction inspired by distributed oracles.
			- I still intuitively want to derive instrumentality from other assumptions, such as agent-environment boundary assumptions.
		- I should also probably write down some of my thoughts about the overall decision problem framework.
			- EG, game trees vs sequences of problems, unbounded vs bounded reward, unbounded vs bounded utility.
			- I argued at some point in favor of bounded utility without assuming reward.
				- Reward makes preference a feature of the environment, rather than a feature of the agent. (Or at least, it tries to.)
					- Well, agent vs environment isn't the true distinction -- there's no such distinction.
					- 
				- We can instead think of utility as a LUV, without assuming anything else about it. (So it could be a constant term with no explicit constraints; or it could be a fully computable expression; or whatever else.)
		- All told, what's the status?
			- Does Soto's work show that UDT succeeds, or fails?
			- Does UDT "need some other idea" to work?
			- Have we hit the true limits?
			- Does it make more sense to "face reality" or keep looking?
			- What ideas should be abandoned?
			- What implications does this have for the broader DT picture?
			- Contextualize `value change`.
				- Consider `updateless value learning`.
				- Can this motivate a form of updating-in-spite-of-UDT, beyond what's captured by UDT with a prior which doesn't anticipate acausal correlations?
			- Consider `ARAA` (Agents Reasoning About ARAA) -- which is to say, UDT `game theory`.
				- Considering all of the above, what hopes may we have?
		- Communicate all this stuff to Soto.
			- Review as many of Soto's recent notes as I need to to understand what's going on.
			- Answer the above questions to my satisfaction.
				- Review my notes on individual PDFs to squeeze all the thoughts out of them into the more organized Q&A.
			- Go thru and make sure the 'notes for Soto' are as up-to-date as possible.
			- Write emails on the most important thoughts.
	- Notes on specific Soto PDFs
		- **A foundational problem**
			- Context:
				- Words from Soto's emails about it:
					- First off, these "independence" properties might be naturally expressed in terms of d-separation.
					- More importantly, working on this (formalizing those two properties) made me
						- notice an apparent issue in our foundations. It's late and *maybe I'm just hallucinating, *I'll check this thoroughly tomorrow, but I include it just in case. As you will remember, we had for now resorted to conditioning on Q_n=q -> A_n=a, instead of A(q)=a, because that allowed for small beliefs affecting large beliefs (without needing to completely update).
						- Especially, in your email from 16 Aug you present the argument for why
						- that works.
						- (Words from my aug 16 email, slightly revised:)
							- Notes from today:
								- It seems like the biggest worry of yours was (more or less) put to rest by the clarification that we consider policy points in the form A(q)=a, where the observation q is the full market state at the future time.
								- So although the *prior* is entirely an extrapolation of a single market state, we *do* run the logical inductor longer, for the *observation*.
								- In particular, the concern was that the large future decision node could
									- have some subtle property P. The small beliefs know the correct action
									- to make given that property, but they can't compute which decision nodes
									- have the property.
								- My response was that q, the later inductor state, should be able to compute the property. (If it cannot, then the property is just too hard for the agent to compute; that's fine.)
								- In other words, the idea is that the necessary information is inside the observation.
								- Imagine for a moment that UDT considered a policy-point by conditioning on Q_n = q -> A_n=a.
									- Q_n is "the nth market beliefs", ie, a term referring to the nth market
										- beliefs without spelling out what they are; q is the actual written-out
										- (large) statement of the future market state; so Q_n=q is just the
										- assertion that the nth market beliefs turn out to be q in particular.
										- \$A_n\$ is similarly a term referring to the nth action of the agent, and \$a\$
										- is a specific action, so \$A_n=a\$ is just saying that the nth action turns
										- out to be some specific one.
									- So here we are just conditioning on the proposition that a specific observation implies a specific action.
									- This is the wrong thing for UDT to condition on; it creates a DT which is
										- too confident in its ability to rule out scenarios. EG, if the DT a
										- priori thinks that it will probably panic if there is a bomb, then it
										- will think it can reduce the probability of a bomb by refusing to panic
										- when it sees one. `happy dance problem`
									- But the point is that in this case, the propositional coherence plus LUV coherence can obviously do a lot of work for us.
										- "q" contains the specific belief we need to look at -- namely, the fact that P.
										- I think here we might need to invoke your universal quantification property. A small belief something like "P always implies that taking action a_1 is good" would come into effect in this case.
										- LUV coherence would give us q->(P_n has high probability).
										- BLI-style self-trust gets us (P_n has high probability)->P_n with high probability.
										- Instantiation of universals gets us from "P always implies that a_1 is good" to P_n -> a_1 is good.
										- Propositional coherence lets us chain all of that together to get q -> a_1 is good.
								- Now, of course, all of this is spelled out for the bad decision procedure which conditions on Q_n = q -> A_n=a rather than the good decision procedure which conditions on A(q)=a. This is because the argument seems a bit easier to see in this case.
									- Hopefully there is a version of this argument which goes through when conditioning on A(q)=a.
								- The general idea here is that we can guard against such problems with the "UDT behaves updatefully when appropriate" style theorems.
									- The least ambitious version is to just argue that *if* the prior doesn't see any (non-negligible) cross-branch correlations or any (non-negligible) impact of the policy-point on the branch's own probability, *then* UDT will behave just like updateful LI would. This would be proved by the branch-cutting argument we discussed.
										- An *observation partition* is a set of possible observations which entirely partitions the space of possibilities. I'll call the elements of this partition "branches".
										- Given an observation partition, the conditional expectation of a policy point is a sum over the conditional expectation in each branch (weighted by the branch's conditional probability).
											- We can ignore any branch whose conditional expectation, and relative branch weight, is the same given each alternative action we are currently considering.
									- A more ambitious version could seek to establish some conditions where
										- this will be true, EG the speculations I've previously made about how
										- cross-branch correlations should be bounded somehow, so that further-out decisions must effectively wash out the prior. (I'm less confident that
										- this will work out, now, due to the thing you're doing with instantiating universal sentences!) The hope would be to show that asymptotically, decisions are made based on empirical correlations, not flights of fancy.
					- But now I worry that, because P(A->B) is not the same as P(B|A), that argument doesn't go through. Since P's small beliefs that will be extrapolated to large beliefs look like "forall q
						- (A -> B)", there's no obvious way to fix this (other than being completely updateful).
					- 
					- Turns out the apparent issue in our foundations I noticed yesterday was
						- real, and our argument doesn't work. I adjoin an explainer of that.
						- I'm thinking of solutions, but probably we (or P) will have to pre-specify
						- which syntactic properties of future observations to check omnisciently
						- (which bits of information to be updateful about). But I already have
						- ideas for impleme nting that, and I don't think it'll change the picture
						- too much. (And then we can use A(q)=a, the right conditional.)
			- Blow by blow:
				- Suppose there is some universal belief that an action is good in specified circumstances (\$\uparrow\$ here stands for "is high", instead of tracking specific bounds):
					- \$\uparrow \mathbb{Q}_k (\forall \mathcal{Q} (P(\mathcal{Q}) \wedge (\mathbb{Q}_m = \mathcal{Q} \to A_m=a) \to \uparrow U)\$
				- What we want to happen:
					- Suppose \$P(\mathcal{Q})\$ for a specific \$\mathbb{Q}_m=\mathcal{Q}\$, and \$\mathcal{Q}\$ is aware of this fact, ie:
						- \$\uparrow \mathcal{Q}(P(\mathbb{Q}_m))\$
							- Soto wrote \$\uparrow \mathcal{Q}(P(\mathcal{Q}))\$, but this belief is too large, living only in the extrapolation.
					- (**IMPLICATION**) By instantiation, we have:
						- \$\uparrow \mathbb{P} (P(\mathcal{Q}) \wedge (\mathbb{Q}_m = \mathcal{Q} \; \to \; A_m=a) \to \uparrow U)\$
					- (**DESIRE**) We want it to be the case that:
						- \$\uparrow \mathbb{P}(\uparrow U | \mathbb{Q}_m = \mathcal{Q} \to A_m = a)\$
						- ie, the prior things utility is high conditioned on the material conditional policy point.
				- So how could we get this to be the case?
					- It would be satisfied if
						- \$\uparrow \mathbb{P} (P(\mathcal{Q}) | \mathbb{Q}_m = \mathcal{Q} \; \to \; A_m = a)\$
					- Because (IMPLICATION) plus this imply (DESIRE).
					- But this is not at all plausible in general. Conditioning on \$\mathbb{Q}_m = \mathcal{Q} \; \to \; A_m = a)\$ restricts us to two kinds of worlds: those where \$\neg \mathbb{Q}_m = \mathcal{Q}\$, and those where \$\mathbb{Q}_m = \mathcal{Q} \; \wedge \; A_m = a)\$. The second kind of world does what we need, but the first very much does not.
						- IE, other branches have no reason to believe \$P(\mathcal{Q})\$, since this has only been calculated in the 'true' \$\mathbb{Q}_m\$.
				- Soto's interpretation:
					- We thought that the knowledge would come together correctly (the prior knowledge that P means we should take action a, and the posterior knowledge that P). But actually, since the knowledge of P doesn't exist in other branches, it is not used there. We can follow the chain of logic if we know that P, but if we condition on this knowledge, we are just being updateful.
					- Martin suggests that the solution *is* to figure out how to be somewhat updateful; EG, let UDT choose some stuff to be strategically updateful about.
				- My interpretation:
					- To me, this feels like a problem with the o->a version of a policy point, which should hopefully be fixed by the A(o)=a version. The o->a version cuts out possibilities where o and not a, but it fails to inform the other branches of the proposed action. So of course other branches are not putting information together in an appropriate way! Other branches need to be conditioned on A(o)=a in order to evaluate it.
					- Indeed, it seems like the o->a version is equivalent to EDT in the case that P(a|o) is the same for every action. So this really isn't UDT, and inferring problems for UDT seems unwarranted.
					- To get the A(o)=a version to work, we just need every branch to be able to sensibly evaluate the impact of the policy-point for their own situation. EG, call the two branches in cf mugging "ask" and "get", with actions "give" and "refuse". What we need is for the "get" branch to correctly understand the impact of "A(ask)=give".
						- Well, we also need to correctly understand impacts on branch probabilities. In a version where the "get" branch doesn't include an observation of whether the large sum of money is received yet or not, that branch can condition on "A(ask)=give" and expect the large sum, and condition on "A(ask)=refuse" and not expect the large sum. But in a version where "get" does see the reward directly, we actually need to split the problem into three branches, "ask", "get", "nothing" (where "nothing" corresponds to not being asked and also not being given anything). The policy points shift probability between "get" and "nothing".
						- Part of the claim here is that we need to be very careful about the distinction between the global expected utility vs expected utility in specific branches.
							- Sentences like \$\uparrow \mathbb{Q}_k (\forall \mathcal{Q} (P(\mathcal{Q}) \wedge (\mathbb{Q}_m = \mathcal{Q} \to A_m=a) \to \uparrow U)\$ are making claims about the global expected utility being high under certain conditions. But this kind of thing is a meta-belief for UDT, which is to say, a statement about UDT's own evaluation of the expected utility. But I think we were thinking as if it were a more object-level statement about utility.
							- My claim is that it's weird for UDT to reason like "actions satisfying some condition are always UDT-approved, and this here action satisfies the condition, so it should be UDT-approved". Maybe this style of reasoning will be used in some cases, but for it to be correct, it should have been formed as a generalization from more specific cases where more object-level considerations decided things.
							- Object-level considerations for UDT involve weighing the pros and cons of a policy point in terms of positive and negative impacts across different branches (and re-weighing probabilities of branches). This means looking at the local (updateful) expected utilities within those different branches, and taking a weighted sum, rather than directly trying to reason about the global expected utility before having done that.
						- So we need two things to happen:
							- Branches have small beliefs about how policy points impact them, but A(o)=a is a large sentence. We need small and large beliefs to cohere appropriately so that conditioning on such large sentences has impacts consistent with the small beliefs of the branches.
								- So when we condition \$\mathbb{P}\$ on a policy-point, the sum decomposes to a sum over possible Q_m (themselves extrapolated to have large beliefs, since the BLI has 'already' extrapolated everything -- ie, \$\mathbb{P} (x | \mathcal{Q})\$ is an extrapolated version of \$\mathcal{Q}\$).
								- So suppose \$\mathcal{Q}\$ has a universal belief stating that \$P(\mathcal{Q}')\$ implies \$A(\mathcal{Q}')=a\$ is good or bad (in the updateful sense; ie, good/bad for \$\mathcal{Q}\$ specifically).
								- What we want is that extrapolate(\$\mathcal{Q}\$) has high/low expected utility conditioned on that policy point.
							- The prior, of course, has even smaller beliefs about how policy points re-weigh branch probabilities. The impact of conditioning the prior on the large policy point needs to impact relative branch probabilities in a way that fits with the small beliefs.
								- 
		- **The extra learning assumption**
			- Context:
				- [scrubbed] Soto and I became, finally, pessimistic about getting everything we might have wanted out of the UDT we've been working on.
					- [scrubbed] it became plausible that the importance of the universal instantiation property would dash my hopes for learning: the possibility of correlations with unbounded reach would, presumably, mean that Omega could incentivize behaviors which never die out.
					- [scrubbed] Soto explained how he hadn't found a way to get the A(o)=a solution to Happy Dance to work, and also explained his argument that the Happy Dance problem remains in any case.
					- Soto also explained his renewed pessimism about learning. I expressed my optimism for a more conservative result, that UDT could learn *if* it *didn't* believe in any forever-correlations preventing this. This is similar to learning in the absence of belief-in-traps: it's not *realistic*, it's not even justifiable as a prior (due to its extreme dogmatism), but it does give us some assurance that the DT is sane overall.
						- Soto expressed some kind of pessimism about this? I don't recall his exact thoughts here. I think Soto always agreed that we could force updatefulness by appropriately modifying the prior. So maybe the pessimism comes from seeing such modifications as an ugly hack?
						- Or perhaps Soto argued that performing such a modification wouldn't establish the philosophical point I hoped it would?
					- I wanted to argue for an analysis like: UDT handles counterfactual muggings by updating to the same extent that Omega does when Omega figures out what to do.
						- I'm not attached to this being exactly the correct heuristic; the point is to argue that there is some heuristic between "use the prior" and "use the most updated market beliefs we have time to calculate".
							- Omega's probability estimates should eventually be *calibrated*, no matter how objectively bad they are (due to not thinking for very long to estimate things).
								- So, because they are calibrated, they shouldn't be terrible to use for our heuristic about which payoff ratios to accept or reject.
							- From Omega's perspective, if we use LI information thinking any *longer* than that, it looks like noise in our accept/reject probabilities.
								- Let's suppose Omega probability-matches (so if Omega sees us paying up with prob p, then Omega pays out in the other branch with prob p, using a very hard to predict coin, EG an empirical coin).
								- So when we think about using a later LI estimate than Omega's, we think it'll give us better information, but we know that any branches where we use this info to decide not to pay up correspond to a reduced probability of payouts in cases where it *is* worth it.
									- At least, that's how it *should* work, according to me.
							- On the other hand, if we think *less* long than Omega, we will still (eventually) be using calibrated estimates, but we could be thinking longer and getting better information, without becoming less predictable in Omega's eyes.
							- So I think the optimal strategy is for us to think long enough to figure out Omega's own probability estimate exactly (since we want to use an estimate which Omega can "see" at the time when Omega is figuring out what to do).
						- This is meant to address a concern like: UDT will use its dumb prior to estimate the probability of a logical coin, so it will use that dumb probability to decide whether a cf-mugging cost/payoff ratio is acceptable or should be rejected.
						- One hope for my analysis might be that *if the prior is informed enough* (ie, if we run LI for long enough before freezing the prior), we get some heuristic like that.
						- A different hope for my analysis would be that *under the learning condition* (ie, assuming we have a prior which eventually acts as if we froze any arbitrarily late market state), we get some heuristic like that.
					- Soto wanted to argue that probability theory was inadequate to express what we wanted; that a tweaked prior couldn't possibly do what we wanted to do. I remain skeptical of this point. Soto himself seems to believe that the prior can be tweaked to force learning, but regards this as a hack. What more could we hope for with a generalization of probability theory?
					- I came up with the example of the iterated counterfactual mugging on a single (logical or empirical) coin-flip, to illustrate my understanding of the conundrum.
				- In our phone call last week, Soto expressed his pessimism in an extreme form, asking me why I wasn't acting desperate about it; stating that it seems UDT needs a new idea in order to work, and pointing out that this knocks out an entire pillar of my agenda.
					- I suggested that my equanimity came from facing reality, and that it didn't seem like some new idea would change the basic picture here.
					- Soto suggested that our UDT had strayed from **The heart of updatelessness about computations** because it made all of its decisions from a fixed point, like policy selection, rather than ... something else. Soto seems to think that using two market states (the small and the large) is a hack.
						- My intuition is that Soto wants something resembling the anthropic perspective instead, but I wasn't able to say any words that Soto really resonated with.
						- I argued for open-minded UDT as the best route for Soto to investigate. Soto thought the idea of updating on some things and not others seemed artificial, but I suggested that the real question was whether we could make sense of there being a truth of the matter about "good" prior probabilities to have, which Soto at least took note of.
				- In a subsequent email, I ask Soto for thoughts about sharply defining the problem as an impossibility result. I suggest that this would be useful whether the right answer is "give up and face reality" or "keep looking for new ideas to salvage things". Soto responded with a PDF later, but that's a different one from the 'extra learning assumption' one.
				- In a follow-up email I sent more thoughts about what "learning" should mean for UDT. Soto sent me his impossibility stuff while I was midway through composing this email, so I took some of it into account but without fully understanding where he had gone with the idea.
					- I argued that either we're in a situation where we've learned that some extra assumption is needed, like the no-traps situation, or else we're in a harsher situation where UDT is totally inconsistent with learning. It seemed to me like Soto was suggesting something between the two.
				- Soto then responded to these extra thoughts with the 'extra learning assumption' pdf.
					- Soto seems to affirm that learning can sometimes happen, and also that we can force the prior to be arranged so that learning definitely happens.
				- My concerns which Soto is responding to in the 'extra learning assumption' PDF:
					- I suggested before that the condition resembles "the
						- UDT, making decisions using a fixed market state LI_0, eventually acts
						- like it is making decisions using LI_N for arbitrary N." I was concerned
						- that this might allow a totally updateful thing to count. I would
						- prefer a more meaningful learning condition; EG, learning to pay up in
						- sequences of counterfactual muggings. (Modulo some assumptions about the
						- sequence of counterfactual muggings, perhaps.) Initially, I was
						- thinking about a requirement that the behavior updates, but "not too
						- fast". But this doesn't make sense, since in some situations, perfectly
						- updateful behavior is the right thing to learn.
					- But
						- perhaps "the UDT eventually acts like it is making decisions using
						- LI_N" is actually enough, due to interactions with the LIC. Suppose that
						- a sequence of Transparent Newcomb problems is encountered, for example.
						- The LIC should guarantee that the pattern of the decision problems is
						- understood. (This is hand-wavy.) The other conditions established for
						- the UDT should then guarantee that the UDT doesn't update too fast. So
						- UDT acting "fully updatefully" in such a case should be excluded by LIC.
					- Still, this might make
						- "the UDT eventually acts like it is making decisions using LI_N" **inconsistent**
						- ... like, can we really edit the prior to force behavior to be
						- eventually-updateful, while preserving all of the other nice conditions
						- of the UDT, including the LIC?
					- Maybe this speaks to your point:
						- > The thing we think we've learned is that some extra condition is needed, beyond what we had hoped.I haven't been able to find any natural assumption that captures what we need. I feel like what we've discovered is something more like "logically uncertain EVM is as bold (and sometimes risky) as we could expect". And as a consequence of that, indeed, we have that reward can be arbitrarily bad (except when we have some ultra-strong assumption like "this prior has been optimized for instrumentality by a reasoner that had all the correct opinions about this decision tree"). But it doesn't get captured by non-extreme assumptions about the decision tree or beliefs.
					- Again, I think the condition is something like "the prior is such that UDT's behavior can eventually be explained as if it has updated to day N, for every N". But
						- of course this is not a constructive condition on the prior, and
						- perhaps it isn't possible to construct such priors. So translating it to
						- some constructive condition (or showing that my condition can be
						- constructed) would be necessary, to support my "some extra condition is
						- needed" story.
					- In some sense I do agree with your "UDT doesn't work" narrative, if there really is no such condition. (Although, I'm not sure how to reconcile this with my feeling that we just need to face reality on this. It feels like "doesn't work" has some
						- kind of evolutionary intuition behind it... like beings who use UDT
						- will eventually be out-competed by beings who learn. But is that a
						- reason for an individual agent to prefer updating? Not necessarily!)
					- More specifically, my intuition is that the reason this could fail is the
						- universal instantiation condition. Since entanglements involving
						- universal statements can touch infinitely many instances, perhaps a
						- modification of the prior to behave somewhat-updatefully-eventually
						- would have to violate universal instantiation or some other important
						- property. But universal instantiation is an important part of how the
						- UDT proposal works. So if this were the case, the UDT setup would be
						- more directly "against learning". (Sorry, again, for the messy reasoning
						- here.)
						- So I guess ***either* **we have
					  a situation where "we've learned that some extra condition is needed, 
					  beyond what we had hoped" (in which case we can still get a picture of a
					  rational agent who learns, just with more restrictive assumptions in 
					  addition to the expected no-traps assumption)** *or else*** our
						- UDT is totally inconsistent with learning in this sense (which confirms
						- some of the worse fears one might have about logical updatelessness --
						- at least in so far as our UDT is the best formulation of UDT for logical
						- updatelessness).
					- And either way, it would be good to know which of those situations we're in.
					- But I'm somewhat confused about the role of universal instantiation. I need
						- to sit down and think about it for longer. I think we agreed that a
						- universal statement could remain near probability zero no matter how
						- many positive instances we see (and similarly, an existential statement
						- could remain near probability one no matter how many non-instances we
						- see). But in some sense this means learned generalizations which have to
						- go through universals are not guaranteed to be good. But many things
						- for UDT *do* have to go through universals. So this in itself
						- should disrupt some hopes for learning, no? EG, we may not correctly
						- learn "it is always better to one-box in transparent newcomb", since the
						- probability of the universal can remain low despite numerous examples.
						- Is there something wrong with my reasoning, or is this correct?
				- Soto's meta-remarks about the PDF:
					- About your extra learning assumption (the first half of your email), I
						- adjoin a PDF in which I basically show we can constructively edit the
						- prior to satisfy the assumption, as you wanted. It's mostly "Policy
						- Selection expressed inside the epistemic framework", but it has some
						- interesting ramifications. I also address your worries about Universal
						- instantiation and LIC, and other things.
			- Blow by blow notes:
				- The "extra assumption" is:
					- The UDT algorithm (based on the infinitely-extended market, \$\mathbb{P})\$ is such that, for every \$n\$, UDT eventually acts as if it's deciding using \$\mathbb{Q}_n\$.
						- Note that we can consider this *as a property of* \$\mathbb{P}\$, universalized across environments it faces; or, we can consider it as a property of (agent, environment) pairs. We might call the first the "universal" version, and the second the "contingent" version.
							- Universal f-learning:
								- For all infinite-depth game trees, for every n, there is a time f(n) such that UDT\$_\mathbb{P}\$ makes the same decisions as UDT\$_{Q_{f(n)}}\$ at and after that time.
							- Contingent f-learning:
								- For a given infinite-depth game tree, for every n, there is a time f(n) such that UDT\$_\mathbb{P}\$ makes the same decisions as UDT\$_{Q_{f(n)}}\$ at and after that time.
						- There's also an interesting intermediate version:
							- \$\mathbb{P}\$ is such that contingent f-learning applies for any game tree which does not give evidence against the belief that behaving f-updatefully is a good idea.
				- We want to make this constructive, to at least prove that there is an instance of the class.
				- Soto claims that **we already get this property contingently**, IE, there exist agent,environment pairs which do this without any special surgery on the LI:
					- Soto considers a game tree where Omega incentivizes satisfying the assumption, directly.
						- EG, there are some rounds with random decision problems, and some rounds with way higher reward just for behaving updatefully in recent rounds.
					- Then, if we freeze the prior at a late enough point (such that it has had time to reason about this game tree), it should understand the structure of the game and play updatefully.
						- Which is to say, it should believe a universal statement which holds the relevant information about what policy to implement.
							- Why should it believe such a universal statement? Why should the probability of such a universal statement converge toward 1?
								- **need to come back to this**
							- Can I sketch the reasoning whereby believing such a universal statement makes UDT follow the policy in practice?
								- UDT makes decisions by looking at a specific EV calculation. The universal statement claims that this EV calculation is always highest for an action which can be calculated in a specific way. The prior hasn't yet calculated the action, but ...
									- **need to come back to this**
					- If this construction works, it shows that we can construct environment-contingent updatefulness parameterized by any "learning rate" that is appropriately computable (we can make it update quickly or slowly).
					- Soto also claims that this isn't what normally happens.
						- If the prior believes we'll face infinitely many counterlogical muggings, and has the credence \$\mathbb{Q}_k(\phi)=.9\$, then Soto claims it will have the universal belief that accepting muggings with payoff ratios >\$1\over 9\$, and will never act like it thought for longer.
							- \$\mathbb{Q}_k\$ is the market state which gets unrolled into the prior.
							- I'm not sure what \$\phi\$ is here. The coin? Which coin?
							- Again I'm unsure where the universal belief comes from.
							- My suspicion is that Soto is basically wrong here? Like, this *could* happen, but I don't see why it *usually* happens.
								- EG, if my conjecture is right, then 'most' priors will evaluate cf muggings with Omega's probability.
				- Soto's argument that we can brain-surgery the prior to force updatefulness relies on the same idea as the argument that updatefulness may not happen: we can force a universal belief which simply says to update (at some given rate).
					- Soto's suggestion is a little more involved than this, but this seems like the basic idea, and anyway, this should work if the whole "universal belief insists on a specific strategy" idea works.
					- Soto tries to soften the blow of how ugly this is; but for me, the point is the existence proof. We can fruitfully assume the property for learning-theoretic analysis so long as instances exist.
						- Although, there are important questions of how 'nice' or 'ugly' such priors can be. For example, it would be interesting to prove that any prior which has the learning property must necessarily update at *some rate*, and therefore, cannot "learn to behave in an arbitrarily updateless manner"!
					- Soto's argument that the resulting thing is still a BLI and still follows all of our other coherence constraints is that it seems obvious -- he doesn't see why I am worried about this. But he agrees the argument needs to be spelled out.
						- If the universalized-strategy trick works, I am convinced.
						- But I'll try to spell out my concerns in a bit more detail.
						- Soto asserts that we have to trash knowledge which contradicts the policy we are trying to enforce, EG, universal beliefs which make contradictory claims about optimal policy. If we have to do this, it sounds as if we have to worry about maintaining some kind of coherence? So it seems the task of maintaining coherence is nontrivial.
						- Behaving as if we've made a decision based on LI_n for all n from 0 to N is perfectly consistent *provided that each n. But Soto asserts that although we modify LI_k, all further LI_n remain as they were.*
							- *So, what happens if some specific LI_n sees reason to stop behaving updatefully beyond that point?*
							- *In my mind, it seems like believing in making decisions based on LI_n at round m implies also endorsing being at least that updateful from then on, which could imply being at most that updateful from then on, depending on LI_n.*
							- *However, I suppose that's not necessarily the case. Behaving like LI_n would behave at round m does not imply the stronger condition of behaving like LI_n would behave from then on.*
								- *In particular, Soto isn't getting updateful behavior out of a restriction on acausal correlations.*
				- *Universal Instantiation*
					- *Soto stresses that although the market extrapolation satisfies Gaifman, this in no way implies that the LI itself satisfies Gaifman, and in particular, converges to the standard model or anything like that.*
					- *I think Soto misses my worry, which was that if Universal Instantiation is what dashes our hopes for learning-by-default, then it should be hard to construct a learner without breaking universal induction. But Soto's construction (if it works) addresses this concern, anyway, by leveraging the universals rather than suppressing them.*
						- *My worry was that if we satisfy LIC, and our policy amounts to a somewhat updateful one, then even if we heavily edit the prior, LI may wander into a universal belief contrary to updating at some point in the future. At this point, it should stop updating. But our modification of the prior supposedly made sure this cannot happen. So it must have violated LIC.*
							- *This is rather vague. It's not clear why an LIC-follower has to be so unpredictable. Perhaps a strong trader could approximately enforce pro-updating beliefs forever.*
								- *In particular, perhaps a strong trader could approximately enforce such beliefs forever so long as the environment complied with the assumption!*
									- *This is analogous to almost completely believing a no-traps assumption, and also, never seeing any strong evidence to the contrary.*
					- *Soto also somewhat dismisses my concern that the probabilities assigned to universals don't become good, since the LI isn't really Gaifman-inductive.*
						- *Soto suspects it won't be a problem in the presence of time-discounting, since the relevant universals will be provable.*
							- *This seems plausible.*
						- *Soto further opines that even if it's a problem, it wouldn't be UDT's fault, it would be the fault of LI.*
							- *This seems irrelevant.*
				- *LIC*
					- *Soto seems particularly confused about my concern that the LIC would somehow have to be broken in order to enforce the learning constraint.*
						- *I think my updated take on this is adequately captured in a couple of emails I just sent him:*
							- *Email 1:*
								- *I'm still working through things, but I think my main confusion was as follows:*
								- *I was imagining that forcing updateful behavior would be done through*  ***constraining the possible acausal correlations****. So for example, if  we want the prior to endorse using Q_n by decision m, we would ensure  that the prior thinks decision A_m does not possess correlations across  the possible Q_n (it only impacts the observed Q_n it belongs to;  alternative possible Q_n don't care about what happens in each other's  worlds), and also that different possible A_m do not modify the branch  probabilities (the relative probabilities of the different possible  Q_n).*
								- *Call the constraint on the prior C(n,m).*
								- *Suppose we want to enforce this property for two such (n,m) pairs: n1,m1 and  n2,m2, such that n1 Q_n1 endorses switching to Q_n2. In other words, C(n2,m2) has to be  enforced for the prior P, and also for the market state Q_n1.*
								- *Suppose now that we want to enforce C(n,m) for infinitely many pairs (to get an asymptotic learning property). By similar reasoning, we need to enforce infinitely many instances of the constraint not only for P, but for infinitely many Q_n as well.*
								- *This is why I was worried about somehow violating the logical induction  criterion: because apparently infinitely many market states need to be  modified.*
								- *Your proposed solution instead only modifies P, and leaves the future market states untouched. So the concern does not arise.*
								- *Relatedly, your idea for getting updateful behavior is more of a hack :) But it  doesn't matter if it's a hack; the idea is to prove the existence of  priors which prefer to update. So long as some exist, it can be a  fruitful learning-theoretic assumption. (But it could be interesting to  prove that all such priors are "hacky" or "unnatural" in some sense...  eg, if no BLI has a structure like the one I'm trying to describe above, enforcing infinitely many C(n,m), that would be interesting, since to  me it is the natural reason to choose to update. Your construction is  more like behaving updatefully because we think Omega will punish us  otherwise!)*
							- *Email 2:*
								- *Ah, here is a more general way to state the concern.*
								- *The desired learning property was "for every n, UDT eventually acts as if  using (the infinite extrapolation of) Q_n" instead of P.*
								- *I can think of two interpretations of this.*
								- *Weak interpretation: For every n, there is a time m, beyond which all actions can be interpreted as being chosen by (the infinite extension of) Q_x for x greater than or equal to n. **
								- ** ***
								- *(This weak interpretation allows future actions to move on from Q_n and be yet-more-updateful.)*
								- ** ***
								- *Strong interpretation: For every n, there is a time m, beyond which all actions can be interpreted as being chosen by (the infinite extension of)Q_n*.*
								- *(This strong interpretation only allows later actions to be even more  updateful than Q_n if Q_n itself endorses the further updatefulness.)*
								- *I was assuming the strong interpretation rather than the weak one. If we  need to edit P, it seems pretty clear that we need to edit every Q_n in  the same way, because every Q_n has to endorse all future choices in  exactly the same way that P does. So I hope it is pretty clear why the  LIC might be violated by some such construction.*
								- *As I understand it, your construction establishes the weak property rather than the strong one.*
								- *A construction which gets the weak interpretation and not the strong one  seems like it should have tiling concerns. Suppose Q_n does not endorse  updating further, but P does. Then on the round when P mimics Q_n, Q_n  should prefer self-modifications which overthrow P and stop the  updating.*
		- ***Impossibility results***
			- *Context:*
				- *See Context:.*
			- *Blow by blow:*
				- *The goal is to articulate the impossibility result which has Soto so worried about the viability of our UDT.*
				- *Soto begins by recalling that there's no problem in the case that Omega's behavior truly depends on our actions alone, as discussed in* ***Argmaxing our strategy****.*
					- *I need to review that PDF for the details, but at first blush I'm puzzled by the assertion. If the prior puts a 90% chance on Omega punishing it forever for any deviation from a specific strategy, it doesn't seem to matter what Omega's algorithm truly does. In other words, it seems to be a matter of the prior, too, not just the environment.*
				- *Soto also simply asserts that "Be More Updateful" can be encoded in the prior; his argument for this is, of course, provided in* ***The extra learning assumption****.*
				- *Soto thinks of UDT as fixed, and imagines two free parameters: the prior, and the tree.*
					- *Soto argues that it won't make sense to talk about finding the best prior for a single decision tree, since some decision trees aren't argmaxed by any prior, nor argmaxed to within \$\varepsilon\$.*
						- *Seems like he's talking about unbounded rewards / unbounded utility.*
						- *Not really sure of the relevance of this, yet.*
					- *Soto concludes that we should think about average performance over many trees to address this.*
				- *Soto defines \$\bar U_n(A)\$ as the average reward agent \$A\$ obtains across all decision trees of depth \$n\$, with max \$n\$ reward per node, and logical coins of length at most \$n\$.*
				- *A does "better on average" than A' if \$\bar U_n(A)\$ is eventually always higher than \$\bar U_n(A')\$ as a function of n.*
					- *With globally bounded reward, Soto instead suggests looking at the limit of \$\bar U_n()\$.*
				- ***Impossibility idea:*** *Suppose A doesn't learn, and A' does. Then A' does better on average.*
					- *How is this an impossibility result?*
						- *Is the idea that UDT doesn't learn? I guess that's what Soto is trying for: his remark about "even UDT" suggest that flavor:*
							- *"What if A thinks that a logical coin somewhere else talks about one of the two identical situations, but not the other? Even a completely updateless A might act differently in those two situations."*
						- *But I don't think this idea makes sense. Soto seeks to isolate "identical situations" and prove that UDT "doesn't learn" because it must act the same in identical situations. (I think.) But even if UDT sees that a subtree is identical to one it faced previously, and sees no acausal correlations incentivizing different behavior on the subtree, UDT faces a different observed market state in the two subtrees. The different market states could contain different relevant information. IE, it has had longer to think. In particular, the market could have learned something from previous instances of the subtree, and UDT could endorse a policy of utilizing such information.*
						- *Could a similar idea possibly make sense?*
							- *I don't especially agree with Soto's argument that we need to consider averages over game trees. So perhaps going back to individual game trees, argue that there's no one decision procedure (including prior) which can do best on all game trees?*
								- *It could conceivably be that we can always do better if more processing power is available to run LI faster.*
								- *But it could conceivably not be the case.*
							- *I do agree with the intuition that there can be arbitrarily farsighted agents, and these will do better in a long-run average sense (if we bound utility but let discounting be subjective, and judge agents by long-run average utility).*
					- ***Proposed def****: A "doesn't learn" if, for any decision tree, when A faces "identical situations" in different parts of the tree, A takes the same actions.*
						- *What's an identical situation?*
							- *Soto admits that this is a problem.*
								- *First, he supposes that "identical situations" must be sub-trees isolated from the rest of the tree; no acausal connections outside of their subtree.*
									- *But Soto is very concerned about how to define this.*
										- *"What if A thinks that a logical coin somewhere else talks about one of the two identical situations, but not the other? Even a completely updateless A might act differently in those two situations."*
										- *Soto suggests that we can't just assume this problem away, because the desired theorem statement has nothing to do with A's internal structure.*
											- *I don't get it. The proposed "impossibility" theorem assumes "A doesn't learn". Since this statement is universal across trees, it has to be a fact about the prior!*
											- *I guess it's true that Soto can't simply assume this away, tho, because this is part of his attempted definition of identical. So the "learning" idea would become trivial: to say that A "doesn't learn" would just be to say that when it thinks there's no reason to behave differently in two subtrees, it doesn't behave differently. (The def could have other facets, but would remain trivial: "if the agent sees no reason to behave differently, and also the subtrees are identical in properties XYZ, then the agent does not behave differently.")*
												- *Well, is that right? I should not equate "no acausal correlations outside the tree" with "no reason not to behave identically". There could be a nontrivial def somewhere around here.*
						- *This def of "doesn't learn" isn't very appealing to me.*
							- *It doesn't indicate that the agent is doing anything bad. It could be reacting optimally to the situation.*
							- *Maybe the point is that no prior can have an optimal response to all sub-tree-shapes already?*
							- *But if no situations are "identical" (EG: Omega continues to offer slightly different prices and payouts for cf mugging, forever), this def of learning is useless.*
						- *Soto suggests that this is related to my own def of learning: I demand that we can see the agent as using an improved prior; Soto demands that "anything change at all". So, Soto sees his condition as weaker and simpler.*
							- *I reject this analysis, though, since "identical situations" doesn't seem simpler, and since his idea doesn't seem implied by mine; EG, an agent can learn to use better estimates for Benford-esque cf muggings, without ever facing identical situations to illustrate the changed behavior.*
				- *Soto thinks the problem with defining "identical" has to do with difficulties reasoning about logical coins.*
					- *It seems like Soto's issue is that logical coins can possibly refer to the agents actions or other aspects of the agent's computation (due to embeddedness), which messes up the apparent causality of the game tree.*
					- *We can make a pseudo-objective agent-env boundary by imagining that we can vary the agent freely, so coins cannot consistently refer to "the agent's action" or any other aspect of the agent. Causality of the decision tree is recovered.*
					- *However, we then get "evil" problems which defeat specific DTs by successfully guessing their source code and referring to them anyway.*
					- *In the case of logical decision theory, there was a result showing that "evil" problems could be defeated by ascending in proof power: if the decision problem guesses your True Name, you may lose, but the same decision procedure with access to stronger axioms could get revenge.*
					- *I wonder if there could be a similar result here, replacing proof strength with computation: if Omega guesses your true name and punishes you specifically for making you-like decisions, then if you could think faster, you could figure out which actions are being punished and take different ones. So in some sense, the limits are only due to bounded computation, rather than the DT itself.*
						- *This is supposed to be helpful in the sense that it means, when using the proposed DT, all concerns can be addressed in principle by getting more computational resources. There's no tricky case where more computational resources is actually a worse idea, because it makes us harder to reason about or whatever.*
						- *But really, those cases still exist; they have simply been ruled out by the assumption that the environment doesn't get to change its logical coins in response to changes in the agent presented. This is a simplified assumption about the agent-environment interface, designed to make decision theory tractable!*
				- *Soto tries to remove the "boundary" problem in a few ways:*
					- *Speculation about restricting the coin. Soto conjectures that no way to do this will be satisfactory; any coin can be correlated with the actions of some UDT.*
					- *Getting rid of the coins entirely. Soto thinks we still face similar problems due to the subjective beliefs of the UDT (which makes sense to me).*
					- *Switching back to the empirical case.*
						- *Soto claims that the concerns about argmaxing trees to within epsilon disappear. (?)*
						- *Soto claims that it's then trivial that we don't learn: of course we deal w identical subtrees in the same way (since he gives UDT the prior corresponding to the exact decision tree).*
						- *Soto suggests that if we re-introduce uncertainty over trees, we just get a similarly trivial situation where the way we average performance across trees defines the new best prior.*
						- *Soto suggests that the problem lies with expected value maximization, and speculates about more kelly-like ideas (specifically, taking the log of the cumulative reward).*
				- *Soto suggests that the main bottleneck (to "proving interesting things") is better models of logical coins, which is to say logical uncertainty. Soto takes this as evidence that we need really new ideas (eg a more realist picture of logical uncertainty, or a replacement for EV maximization, or a generalization of probability) to get some things we wanted.*
				- *Soto concludes with a humbler "impossibility result" conjecture:*
					- *That contrasting UDT (based on running LI for k steps and then freezing and extrapolating) with a forced-update UDT (based on surgery on the prior), the second does better on average in the earlier-specified sense.*
						- *But LI can produce something that's already in agreement with the surgery? So this seems implausible.*
						- *However, it seems like similar ideas may be plausible.*
							- *UDT with bounded utilities can't care about the long-run average reward; so plausibly, there will be other DTs which do better on that metric.*
		- ***Argmaxing our strategy***
		- ***Epistemics and Instrumentality***
		- ***Problem or Opportunity: LIs do sometimes get tricked***
		- ***The heart of updatelessness about computations***
		- ***Formalizing my worry***
		- ***Formalizing the author's worry***
		- ***A naive proposal***
