
*Intake note (2026-10-02): the author's notes below on Scott Garrabrant's and Benja Fallenstein's proposals are partial recollections and do not represent those proposals accurately; their actual proposals were specific and technical. "BLI" throughout this bundle means Eisenstat's construction.*

---
journal: Daily
journal-date: 2023-09-11
---
- Notes on recent Soto emails. `UDT` `LUDT` `logical uncertainty` `Radical Skepticism` `logical updatelessness` `updatelessness`
	- Goals?
		- Review the whole theory for LUDT, comparing with my initial notes.
			- Fill out the initial notes with added notes about my understanding of the current status.
			- Look for holes or things I think can be done better.
			- Convince myself that it makes sense (or doesn't).
		- DONE Think over the o->a vs A(o)=a problem.
			- Clarify my thoughts on the `happy dance problem` and Soto's claim that A(o)=a does not solve it.
			  collapsed:: true
				- Original posts: (duplicated due to IAFF / alignment forum crossover)
					- https://www.lesswrong.com/posts/HY94LBqekihnx85WQ/the-happy-dance-problem-1
					- https://www.lesswrong.com/posts/5bd75cc58225bf067037550e/the-happy-dance-problem
				- The `o->a UDT` conditions on the material implication, that such and such observations imply such and such actions. This is in fact quite inadequate for representing full UDT concerns.
					- Because o->a only eliminates worlds where o is true and a is false, it necessarily reduces the probability of o.
					- Furthermore, if all available actions are equally probable given o, o->a UDT amounts to EDT!
					- So the *only* updateless influences which this decision theory can track are Transparent Newcomb style cases where the fact that an observation makes a specific action probable actually means that we can avoid that observation-state by taking a different action within it.
					- And furthermore, _this state of affairs cannot be distinguished from the more ordinary state of affairs where a specific action seems quite probable for ordinary reasons_.
						- Which is to say, Transparent Newcomb cannot be distinguished from Happy Dance.
					- Hmm, can Happy Dance be solved by `mixed-strategy ratifiability`?
						- IE if the agent knows that it dances with high probability, then ... well, no, this is already the case here.
				- Soto claims that `A(o)=a UDT` also has a happy dance problem.
					- The obvious argument against this claim is that `A(o)=a UDT` can have any conditional probability table it wants, so whatever the _correct_ probability distribution to believe upon learning $A(o)=a$, it can just believe that.
						- so long as the correct distribution puts probability 1 on $A(o)=a$
						- & so long as expected evidence is not violated
					- Soto's argument, iirc, was that $A(o)=a$ can still believe in spurious correlations, which can still spoil its performance in decision problems.
						- According to my understanding, Happy Dance is pointing at a _failure to be able to even represent a problem_, because o->a UDT can't represent Happy Dance (can't represent the important distinction between Happy Dance and Transparent Newcomb).
						- Soto appears to instead be pointing to *traps which UDT could fall into*. But this misses the important point that A(o)=a UDT *at least is not forced to fall into the trap*.
						- *Revised statement of Soto's argument*:
							- Assume the prior thinks P(A(see money)=dance | see money) >> P(A(see money)=dance).
								- This feels illegal, somehow??
								- But really, it's just another way to say that the policy of dancing-upon-money increases the probability of money.
								- Well, what if we bring in `mixed-strategy ratifiability`?
									- So the agent should still be able to make the decision from the perspective where they know what that decision is, to within some limits of self-knowledge.
									- This indeed seems to make this type of counterexample more difficult to produce.
							- Then, conditional on A(see money)=dance, the expected utility is higher than the prior, so A takes that action.
							- This certainly seems like a weird belief to have, weirder than the one needed for the original happy dance; but (according to Soto) there are many situations where this kind of belief does reflect reality.
								- Original Happy Dance involves an instrumentally poor, but self-fulfilling, prior. (It's true, from our perspective, that the agent dances when it sees money; we cannot object that the prior itself doesn't describe the decision problem well, like in Smoking Lesion.)
								- Soto's modified Happy Dance for A(o)=a UDT does not seem to have a similar feature: it seems like if we arranged for an iterated version of the problem, the UDT decision would turn out to be independent of the pile of money, contrary to the prior's belief in a correlation.
							- But perhaps more importantly, Soto's version does not directly point to a way in which _A(o)=a UDT is not expressive enough to represent a decision problem_, whereas the original Happy Dance does.
								- This seems, to me, related to the way we can't arrange for Soto's prior to be calibrated.
									- We could try and argue that A(o)=a UDT is insufficiently expressive because choosing a policy-point ensures that the probability of that policy-point is 1 (in our view of the consequences).
									- But to make this plausible, we would need to devise a scenario where it looks like the best way to model that scenario is for some policy-points to be self-defeating; IE, if the agent were to make that choice, then it would not in fact be an agent who made that choice (at least, with some probability).
									- This seems to violate... some important principle.
			- DONE Look for a variation of Soto's setup which does the A(o)=a thing.
				- The obstacle which Soto observed for this was, _more or less_, the fact that o->a reasoning follows from propositional coherence alone, whereas correct A(o)=a reasoning does not.
					- ***Argument that propositional coherence is enough to make*** $O=o \to A=a$ ***reasoning work:***
					  id:: 6536f844-cfdb-47f4-9e1c-a8280e8bfe97
					  collapsed:: true
						- Imagine for a moment that UDT considered a policy-point by conditioning on $Q_n = q \to A_n=a$.
							- Q_n is "the nth market beliefs", ie, a term referring to the nth market 
							  beliefs without spelling out what they are; q is the actual written-out 
							  (large) statement of the future market state; so Q_n=q is just the 
							  assertion that the nth market beliefs turn out to be q in particular. 
							  A_n is similarly a term referring to the nth action of the agent, and a 
							  is a specific action, so A_n=a is just saying that the nth action turns 
							  out to be some specific one.
							- So here we are just conditioning on the proposition that a specific observation implies a specific action.
							- This is the wrong thing for UDT to condition on; it creates a DT which is 
							  too confident in its ability to rule out scenarios. EG, if the DT a 
							  priori thinks that it will probably panic if there is a bomb, then it 
							  will think it can reduce the probability of a bomb by refusing to panic when it sees one.
							- But the point is that in this case, the propositional coherence plus LUV coherence can obviously do a lot of work for us. "q" contains the specific belief we need to look at -- namely, the fact that P. I think here we might need to invoke your universal quantification property. A small belief something like "P always implies that taking action a_1 is good" would come into effect in this case. LUV coherence would give us q->(P_n has high probability). BLI-style self-trust gets us (P_n has high 
							  probability)->P_n with high probability. Instantiation of universals 
							  gets us from "P always implies that a_1 is good" to P_n -> a_1 is 
							  good. Propositional coherence lets us chain all of that together to get q
							  -> a_1 is good.
							- Now, of course, all of this is spelled out for the bad decision procedure which conditions on Q_n = q -> A_n=a rather than the good decision procedure which conditions on A(q)=a. This is because the argument seems a bit easier to see in this case.
							- Hopefully there is a version of this argument which goes through when conditioning on A(q)=a.
						- See ((650343b1-ce36-4f4d-9325-f5995461bfc2)) for what goes wrong when we try to apply this to `A(o)=a UDT`.
					- Conditioning a branch on A(o)=a doesn't automatically correctly interface between the "large" $o$ and the "small" beliefs in the branch -- it isn't immediately clear how this even _should_ work.
						- Small beliefs have to somehow encode large probability distributions about this stuff. How does a single large policy point relate to outcomes, when there are many many such large policy points? They cannot all be fully determinative of the outcome, unless they also perfectly determine each other.
						- In principle all we need to know is the conditional probability distribution over other stuff _given_ policy points meeting a specific small description. However, small beliefs about large conditional probability distributions, like this, do not necessarily enforce themselves?
							- Is it reasonable and/or possible to specify and enforce a coherence condition which would make it so that the relevant small beliefs about large conditional probabilities would force those large conditional probabilities to conform?
							- Or, is there any other way of unfolding small probability distributions into large which has similar relevant impact?
					- However, it seems like more-or-less enough to require **`hypothetical marginalization`**:
						- Whereas `propositional coherence` and `LUV coherence` require that the _actual probability distribution over large stuff marginalizes correctly into a distribution over small stuff_, hypothetical marginalization requires that **UDT knows, a priori, how to marginalize large belief states given by description**.
						- So if Q is a large written-out description of a potential market state, and $\text{marg}$ is a specific marginalization function (which pulls out the expectation of a proposition or a LUV), and in truth, $\text{marge}(Q)=v$, then the prior assigns probability 1 to that truth, or at least assigns some very high probability to some very small interval around that truth.
						- ***Argument that hypothetical marginalization solves the*** $A(o)=a$ ***problem***:
						  id:: 6536f80b-4682-4c33-bb78-45492b18f806
							- First argument from email thread:
								- {{embed ((65392abe-0974-4591-b379-7ae788d649c1))}}
							- Second argument from thread:
							  collapsed:: true
								- {{embed ((65413c7c-dd38-401b-b124-3bc275911885))}}
							- Synthesis into a general theorem:
		- Come to a better understanding of the consequences of `Universal Instantiation`.
			- Consequences for inferential semantics of quantification, if any.
				- Thoughts on the current status of the `Gaifman condition`.
					- https://rationalistramble.wordpress.com/2015/08/08/the-gaifman-condition-and-the-%CF%801-%CF%802-problem/
					- https://intelligence.org/files/Pi1Pi2Problem.pdf
					-
			- Computability/complexity.
				- Mechanism of enforcement.
			- Importance in the UDT theory.
				- ***Places where we need Universal Instantiation to make arguments we want to make.***
					- ((6536f844-cfdb-47f4-9e1c-a8280e8bfe97))
					- ((6536f80b-4682-4c33-bb78-45492b18f806))
					- It seems to me like the way we're using Universal Instantiation is particularly suited to cases of _certainty_, like where we know the exact utility which will result from a specific policy-point, rather than only knowing some expectation.
						- Soto thinks these arguments will generalize.
						- But Soto also thinks there _are_ limitations for uncertainty & universal instantiation.
							- The only way to make a generalization about uncertainty is a universal belief *about your own belief*; but it seems dangerous to try to make universal instantiations about such things _enforce those beliefs on the actual distribution_.
							- So generalizations about belief will 'lack teeth', and hence, tend to either be trivial or incorrect. They're not _devices with which we can enforce structure on the extrapolated beliefs_, unlike the more object-level universals.
							-
				- Senses in which it might block learning.
					- Dashed hopes for bounded correlations.
					- Concern that because of limits to the 'correctness' of beliefs about universals, anywhere where we rely on those probabilities for DT arguments will not have good learning properties.
		- Understand how we can constructively edit the prior to force "learning" for UDT.
			- What kind of "learning" for UDT?
				- "eventually arbitrarily updateful"
					- Eventually acts as if the UDT had been extrapolated from $LI_n$, for each $n$.
					- The most obvious version of this requires _each_ $\text{extrapolate}(LI_n)$ to endorse eventually acting like _each other_ $\text{extrapolate}(LI_m)$.
						- A much less ambitious version would only require that $\text{extrp}(LI_n)$ endorses each $\text{extrp}(LI_m)$, m>n, _for some amount of time_ before switching to instead endorse another. Soto suggested that something like this could be achieved by imposing the beief that _Omega would punish behavior deviating from this_.
						- Can the more ambitious version be achieved by a similar omega-punishment belief?
							- I suspect not -- argument?
						- Can the property be achieved more naturally, by reasoned trust that behaving somewhat more updatefully is eventually a good idea, rather than through artificially imposed false beliefs / artificially imposed strong preferences?
							- More generally -- under what assumptions can such a thing happen?
				- frequentism-inspired properties
				- `infrabayes`-inspired properties
			- How does this avoid breaking universal instantiation?
				- Does this address the concern that universal instantiation dashes hopes for bounded correlations?
				- Does this address the concern that universal probabilities are too poor for learning?
			- How does this avoid breaking LIC?
				- If we learn that there are inter-branch correlations, how can we forget without breaking LIC?
		- Understand what problems Soto sees for UDT, and to what degree I agree.
			- Some email excerpts (possibly edited/entended):
			  collapsed:: true
				- AUTHOR:
				  collapsed:: true
					- The simplest statement is that there is a trade-off between learning and updatelessness, but this is not quite right:
						- Learning is not always possible anyway.
							- We always knew that we would not be able to learn if there are traps.
								- Or rather, if the prior believes the environment contains traps.
							- So we always knew that learning theorems would have conditions on them.
							- The thing we think we've learned is that some extra condition is needed, beyond what we had hoped.
							- So the question is: what is the tightest possible statement of the extra assumption we need?
								- (How little can we get away with assuming?)
						- It's not really learning vs updatelessness, since we can get learning by constraining the prior, which preserves updatelessness (despite making UDT behave more updatefully).
							- So what we throw away to get learning, more precisely, is correlations between actions and probabilities of branches.
								- Or perhaps we should split this up into:
									- Correlations between actions and the probability of branches (including changes to the probability of the branch the action gets taken in, and also to other branches).
									- Correlations between actions and the _utility_ of other branches.
					- However, I think this does not really highlight the hope that was dashed. Of course there will be a trade-off between UDT behaving updatefully (which happens when it does not think there are acausal correlations to account for) vs failing to (when it does think there are acausal correlations). This is too obvious.
					- A better statement would be: for any sequence of decision problems UDT could face, *UDT must behave at least a little bit updatefully*, like a policy-selector running at least some really slow LI to improve its selections. So you don't need to resort to the same early, dumb market state to explain UDT's choice; at least, not forever. For each inductor state, actions can eventually be explained in terms of a later state than that. You don't cling to some bad probability estimate *forever*.
					- If we don't want to treat logical uncertainty as different from empirical uncertainty, then we can extend this to say that you won't need to rely on the same prior to explain actions forever; even though UDT does in fact use a fixed prior, it should eventually act as if it has updated from any particular early distribution.
					- It seems kind of obvious from the form of this "learning" criterion that there's an arbitrary choice (*when* to move on from the prior). The fact that the desideratum has to be stated in this weird way could perhaps have been a sign that it wouldn't be achievable without hack-y manipulation of the prior.
					- So, that's the point which my example of infinitely many counterfactual muggings, all from the same (logical or empirical) coin, is supposed to make. It shows that some priors force a choice between learning vs selecting actions in a way which is optimal according to that prior. (Where "learning" is this weak notion of being able to eventually justify actions via a more accurate probability distribution, rather than forever needing to explain them in terms of the ignorance of the fixed prior.)
					- Anyway, refining a careful statement of the impossibility result seems like it would be a fruitful direction, even for your hopes to salvage things through some new idea; it would be good to have a more precise handle on what you could and could not expect such a new idea to achieve.
				- Martin:
				  collapsed:: true
					- I haven't been able to find any natural assumption that captures what we need. I feel like what we've discovered is something more like "logically uncertain EVM is as bold (and sometimes risky) as we could expect". And as a consequence of that, indeed, we have that reward can be arbitrarily bad (except when we have some ultra-strong assumption like "this prior has been optimized for instrumentality by a reasoner that had all the correct opinions about this decision tree"). But it doesn't get captured by non-extreme assumptions about the decision tree or beliefs.
				- AUTHOR:
				  collapsed:: true
					- I suggested before that the condition resembles "the UDT, making decisions using a fixed market state LI_0, eventually acts like it is making decisions using LI_N for arbitrary N." I was concerned that this might allow a totally updateful thing to count. I would prefer a more meaningful learning condition; EG, learning to pay up in sequences of counterfactual muggings. (Modulo some assumptions about the sequence of counterfactual muggings, perhaps.) Initially, I was thinking about a requirement that the behavior updates, but "not too fast". But this doesn't make sense, since in some situations, perfectly updateful behavior is the right thing to learn.
					- But perhaps "the UDT eventually acts like it is making decisions using LI_N" is actually enough, due to interactions with the LIC. Suppose that a sequence of Transparent Newcomb problems is encountered, for example. The LIC should guarantee that the pattern of the decision problems is understood. (This is hand-wavy.) The other conditions established for the UDT should then guarantee that the UDT doesn't update too fast. So UDT acting "fully updatefully" in such a case should be excluded by LIC.
					- Still, this might make "the UDT eventually acts like it is making decisions using LI_N" **inconsistent** ... like, can we really edit the prior to force behavior to be eventually-updateful, while preserving all of the other nice conditions of the UDT, including the LIC?
					- Maybe this speaks to your point:
						- > The thing we think we've learned is that some extra condition is needed, beyond what we had hoped.
					- I haven't been able to find any natural assumption that captures what we need. I feel like what we've discovered is something more like "logically uncertain EVM is as bold (and sometimes risky) as we could expect". And as a consequence of that, indeed, we have that reward can be arbitrarily bad (except when we have some ultra-strong assumption like "this prior has been optimized for instrumentality by a reasoner that had all the correct opinions about this decision tree"). But it doesn't get captured by non-extreme assumptions about the decision tree or beliefs.
					- Again, I think the condition is something like "the prior is such that UDT's behavior can eventually be explained as if it has updated to day N, for every N". But of course this is not a constructive condition on the prior, and perhaps it isn't possible to construct such priors. So translating it to some constructive condition (or showing that my condition can be constructed) would be necessary, to support my "some extra condition is needed" story.
					- In some sense I do agree with your "UDT doesn't work" narrative, if there really is no such condition. (Although, I'm not sure how to reconcile this with my feeling that we just need to face reality on this. It feels like "doesn't work" has some kind of evolutionary intuition behind it... like beings who use UDT will eventually be out-competed by beings who learn. But is that a reason for an individual agent to prefer updating? Not necessarily!)
					- More specifically, my intuition is that the reason this could fail is the universal instantiation condition. Since entanglements involving universal statements can touch infinitely many instances, perhaps a modification of the prior to behave somewhat-updatefully-eventually would have to violate universal instantiation or some other important property. But universal instantiation is an important part of how the UDT proposal works. So if this were the case, the UDT setup would be more directly "against learning". (Sorry, again, for the messy reasoning here.)
					  So I guess ***either*** we have a situation where "we've learned that some extra condition is needed, beyond what we had hoped" (in which case we can still get a picture of a rational agent who learns, just with more restrictive assumptions in addition to the expected no-traps assumption) ***or else*** our UDT is totally inconsistent with learning in this sense (which confirms some of the worse fears one might have about logical updatelessness -- at least in so far as our UDT is the best formulation of UDT for logical updatelessness).
					- And either way, it would be good to know which of those situations we're in.
					- But I'm somewhat confused about the role of universal instantiation. I need to sit down and think about it for longer. I think we agreed that a universal statement could remain near probability zero no matter how many positive instances we see (and similarly, an existential statement could remain near probability one no matter how many non-instances we see). But in some sense this means learned generalizations which have to go through universals are not guaranteed to be good. But many things for UDT *do* have to go through universals. So this in itself should disrupt some hopes for learning, no? EG, we may not correctly learn "it is always better to one-box in transparent newcomb", since the probability of the universal can remain low despite numerous examples. Is there something wrong with my reasoning, or is this correct?
					- I also wanted to write down some of the thoughts we had about implications of the impossibility result for game theory. Since it feels like a sort of learning vs consistency trade-off, it might yield some insights about "learning vs teaching" trade-offs in multi-agent settings, which could possibly formalize the commitment races problem.
					- An optimistic version of this might show that if at most one agent is stubborn (ie, the rest of the agents are of the "learning" type), then the joint action profile can converge to a pareto-optimal point. Out of the learning agents, we might expect "more stubborn" agents (agents who update more slowly) to have the advantage in the long run. (IE, the point on the Pareto frontier is skewed toward the interests of the stubborn.) If so, it would vindicate a version of commitment-races, because if we imagine longsighted agents designing UDT priors to play iterated games on their behalf, the most stubborn prior wins in some sense. But if you want to learn as little as possible, the obvious limit of that is to not learn at all. So even if it's true that UDT can be made to learn with the correct choice of prior, this result would illustrate one sense in which it "shouldn't".
					- For this to be true, it would still have to get around folk-theorem ideas, to achieve pareto-optimality. So it's still quite optimistic, even though it would also confirm a version of the commitment races problem.
					- Perhaps we could imagine that the priors are themselves designed with access to a cooperative oracle, in some way, so that the commitment-races result could be illustrated without requiring a realistic way to avoid the fold theorem? But I'm not sure how to do this... maybe the simplest way would be to abandon computability of the logical inductors and just do reflective-oracle-logical-induction (all traders have access to a reflective oracle, indeed, a cooperative oracle). So the point would be to show that *even when there's this tremendous resource that can be used for cooperation* there's a perverse commitment-races type problem.
				- Martin:
				  collapsed:: true
					- About your extra learning assumption (the first half of your email), I adjoin a PDF in which I basically show we can constructively edit the prior to satisfy the assumption, as you wanted. It's mostly "Policy Selection expressed inside the epistemic framework", but it has some interesting ramifications. I also address your worries about Universal instantiation and LIC, and other things.
						- ((64ff8294-e0f8-42ac-b95e-e73c7daaa0e2))
				- AUTHOR:
				  collapsed:: true
					- I'm still working through things, but I think my main confusion was as follows:
					- I was imagining that forcing updateful behavior would be done through **constraining the possible acausal correlations**. So for example, if we want the prior to endorse using Q_n by decision m, we would ensure that the prior thinks decision A_m does not possess correlations across the possible Q_n (it only impacts the observed Q_n it belongs to; alternative possible Q_n don't care about what happens in each other's worlds), and also that different possible A_m do not modify the branch probabilities (the relative probabilities of the different possible Q_n).
					- Call the constraint on the prior C(n,m).
					- Suppose we want to enforce this property for two such (n,m) pairs: n1,m1 and n2,m2, such that n1<n2 and m1<m2. Clearly, this can only work if Q_n1 endorses switching to Q_n2. In other words, C(n2,m2) has to be enforced for the prior P, *and also* for the market state Q_n1.
					- Suppose now that we want to enforce C(n,m) for infinitely many pairs (to get an asymptotic learning property). By similar reasoning, we need to enforce infinitely many instances of the constraint *not only for P, but for infinitely many Q_n as well*.
					- This is why I was worried about somehow violating the logical induction criterion: because apparently infinitely many market states need to be modified.
					- Your proposed solution instead only modifies P, and leaves the future market states untouched. So the concern does not arise.
					- Relatedly, your idea for getting updateful behavior is more of a hack :) But it doesn't matter if it's a hack; the idea is to prove the existence of priors which prefer to update. So long as some exist, it can be a fruitful learning-theoretic assumption. (But it could be interesting to prove that all such priors are "hacky" or "unnatural" in some sense... eg, if no BLI has a structure like the one I'm trying to describe above, enforcing infinitely many C(n,m), that would be interesting, since to me it is the natural reason to choose to update. Your construction is more like behaving updatefully because we think Omega will punish us otherwise!)
					- Ah, here is a more general way to state the concern.
					- The desired learning property was "for every n, UDT eventually acts as if using (the infinite extrapolation of) Q_n" instead of P.
					- I can think of two interpretations of this.
					- Weak interpretation: *For every n, there is a time m, beyond which all actions can be interpreted as being chosen by (the infinite extension of) ****Q_x for x greater than or equal to n****.*
					- (This weak interpretation allows future actions to move on from Q_n and be yet-more-updateful.)
					- Strong interpretation: *For every n, there is a time m, beyond which all actions can be interpreted as being chosen by (the infinite extension of)**** Q_n****.*
					- (This strong interpretation only allows later actions to be even more updateful than Q_n if Q_n itself endorses the further updatefulness.)
					- I was assuming the strong interpretation rather than the weak one. If we need to edit P, it seems pretty clear that we need to edit every Q_n in the same way, because every Q_n has to endorse all future choices in exactly the same way that P does. So I hope it is pretty clear why the LIC might be violated by some such construction.
					- As I understand it, your construction establishes the weak property rather than the strong one.
					- A construction which gets the weak interpretation and not the strong one seems like it should have tiling concerns. Suppose Q_n does not endorse updating further, but P does. Then on the round when P mimics Q_n, Q_n should prefer self-modifications which overthrow P and stop the updating.
				- Martin:
				  collapsed:: true
					- > I was imagining that forcing updateful behavior would be done through **constraining the possible acausal correlations**. So for example, if we want the prior to endorse using Q_n by decision m, we would ensure that the prior thinks decision A_m does not possess correlations across the possible Q_n (it only impacts the observed Q_n it belongs to; alternative possible Q_n don't care about what happens in each other's worlds), and also that different possible A_m do not modify the branch probabilities (the relative probabilities of the different possible Q_n).
					- First off, these "independence" properties might be naturally expressed in terms of d-separation.
					- More importantly, working on this (formalizing those two properties) made me notice an apparent issue in our foundations. It's late and *maybe I'm just hallucinating, *I'll check this thoroughly tomorrow, but I include it just in case.
					- As you will remember, we had for now resorted to conditioning on Q_n=q -> A_n=a, instead of A(q)=a, because that allowed for small beliefs affecting large beliefs (without needing to completely update). Especially, in your email from 16 Aug you present the argument for why that works.
					- But now I worry that, because P(A->B) is not the same as P(B|A), that argument doesn't go through. Since P's small beliefs that will be extrapolated to large beliefs look like "forall q (A -> B)", there's no obvious way to fix this (other than being completely updateful).
					- Anyway, going back to your ideas, I do think there is a way to enforce your constraints C(n, m) on any distribution, by just modifying continuously some conditional probabilities to get the uniformity we need (that represents independence), for example that P(Q_n=q | A_m=a) be constant on a. Although again I think this will look more like "letting Q_n run as normal, and then in our definition of Procedure() including those enforced changes". (Or maybe there's another clever way to do all that by modifying only P, by slightly violating BLI self-trust where we want to.)
					- > A construction which gets the weak interpretation and not the strong one seems like it should have tiling concerns. Suppose Q_n does not endorse updating further, but P does. Then on the round when P mimics Q_n, Q_n should prefer self-modifications which overthrow P and stop the updating.
					- Yes, you are right about the strong and weak interpretations, and my thing only satisfies weak ("Q_n might be forced kicking and screaming to update to Q_n+1"). But I think there's a subtlety here.
					- When we say "Q_n would prefer self-modification to overthrow P", we mean something like "if we give it an action doing that, it will take it". And I'm still not clear on what this "give it an action" should be. For example, whether it's present and observable in the decision tree from the start, or only introduce once Q_n is in control.
					- Hi,
					- Turns out the apparent issue in our foundations I noticed yesterday was real, and our argument doesn't work. I adjoin an explainer of that.
					- I'm thinking of solutions, but probably we (or P) will have to pre-specify which syntactic properties of future observations to check omnisciently (which bits of information to be updateful about). But I already have ideas for implementing that, and I don't think it'll change the picture too much. (And then we can use A(q)=a, the right conditional.)
					- ((650343b1-ce36-4f4d-9325-f5995461bfc2))
				- AUTHOR:
				  collapsed:: true
					- Question about the foundational issue.
					- When we condition on the o->a form of a policy-point, we cut out possibilities where o and not a, but we don't cut out anything else. So the branches where o is true have "been informed" that a is true within them, but other branches don't have any info about which policy point is being proposed.
					- But this seems to mean that branches inconsistent with o can be totally ignored in the EV calculation, right? Because the opinion of those other branches will be constant across different actions considered. The only thing that matters about those branches is their relative probability compared to P(o&a) (since this impacts the normalizing term when conditioning).
					- If the action probability P(a|o) for each action is identical, then this relative probability is the same, so we can fully ignore the other branches, which means in such cases, the version of UDT which conditions on policy-points of the o->a form is precisely equivalent to EDT.
					- Am I crazy?
				- Martin:
				  collapsed:: true
					- Thank you for all these notes!
						- (referring to notes under ((650343b1-ce36-4f4d-9325-f5995461bfc2)))
					- id:: 65382477-fbef-4224-9c1c-9df2cc7c558b
					  >  which means in such cases, the version of UDT which conditions on policy-points of the o->a form is precisely equivalent to EDT
					- Yes, you are completely right, and not crazy! In fact, I had already had this realization. I should have written it down in the doc, but if I didn't it was because of the following train of thought:
					- "Oh, yes, this just happens because in those few worlds we are completely updateful (like EDT), and in the others completely updateless (about the real observation). This is nothing new, this is just realizing again that we know how to be completely updateful, we know how to be completely updateless, but we're missing the useful thing in between (exactly as in the A(o)=a case). This just clearly shows that we cannot be agnostic: an explicit decision has to be made about what to update on. So we'll let the prior decide that a priori (and if we do that, then we might as well condition on A(o)=a instead of on implications, since we prefer it for other reasons)."
					- You also noticed that, when not all P(a|o) are the same, the fluctuating ration between P(o&a) and P(-o) can indeed change E(U). And in fact, this is exactly the mechanism that allows for the wrong behavior in Happy Dance (or, equivalently, the right behavior in Newcomb's). Although actually, this "mechanism" is nothing else than "how probability distributions work".
					- > Martin suggests that the solution *is* to figure out how to be somewhat updateful; EG, let UDT choose some stuff to be strategically updateful about.
					- Yes, I'll write that tomorrow.
					- > Sentences like $\uparrow \mathbb{Q}_k (\forall \mathcal{Q} (P(\mathcal{Q}) \wedge (\mathbb{Q}_m = \mathcal{Q} \to A_m=a) \to \uparrow U)$ are making claims about the global expected utility being high under certain conditions. But this kind of thing is a meta-belief for UDT, which is to say, a statement about UDT's own evaluation of the expected utility.
					- I don't yet understand what you mean. I think that's an object-level belief, not explicitly including UDT's evaluation in any way (except for correlations that UDT might believe between its taken actions and its evaluation process, etc.). All variables (Q satisfying P(), Q implying A_m=a, and the LUV U being high) pertain to the object-level (how the environment looks, which consequences certain actions will have on the environment, etc.). Also, if our prior believes something like that, it will certainly be because it has seen particular object-level examples of that general \forall (or has proven them in its head).
					  > (themselves extrapolated to have large beliefs, since the BLI has 'already' extrapolated everything -- ie, $\mathbb{P} (x | \mathcal{Q})$ is an extrapolated version of $\mathcal{Q}$)
					- Yes, that's also a realization I had, nice.
					- On a more general note, **here's a path I just thought of to a possible solution:**
					- Here's, first, a way to reframe the problem. When I want to represent "Q_k believes in the worlds in which A turns out true, so does B", of course I shouldn't formalize it as "Q_k(A->B) is high" (that might be high just because A is very unlikely). I should formalize it as "Q_k(B|A) is high". But then, what if I want to represent "Q_k believes that, for all Q, in the worlds in which A(Q) turns out true, so does B(Q)"?
					- (Here A(Q) is the above P(Q)&A(Q)=a, or "Omega asks for the capital of France, and I say Paris". And B(Q) is the above \uparrow U, or "I get $10".)
					- If I had gone with the implication, I could just say "Q_k(\forall Q (A(Q)->B(Q)) is high", and indeed that's what we were doing.
					- But inside Q_k's probability distribution, I can't say something like "\forall Q, Q_k(B(Q)|A(Q)) is high". Of course, Q_k can formalize such a mathematical sentence (call it \phi), and believe it strongly ("Q_k(\phi) is high"). But I'm pretty sure we've just pushed down the problem one mesa-level down, since Q_k will also have conditional opinions about \phi, and its relation to other sentences. (But this possibility should be explored further.)
					- So, what if we include some explicit mechanism, on top of the probability distribution, that plays the role of that "external \forall" that doesn't have a representation inside the distribution? This mechanism will probably need to be intertwined with the infinite extrapolation. But there's something hard I don't know how to solve: How does Q_k learn that this external \forall is the case? There's a sense in which Inductor states never get feedback about these conditionals, or better said, they are only able to check them when A(Q) turns out true. So it makes sense that "what they actually observe" is the implication A(Q)->B(Q), that doesn't distinguish between satisfying the conditional, or falsifying A(Q).
					- But... what if we add an external extrapolation on top of the Inductor states, looking at the historical evolution (instead of only the last state Q_k), such that we come to opinions about what successful traders are enforcing (not only the end-result fix-point). Then, if we see that indeed Q_k(B(Q)|A(Q)) is high for most Q we have seen, we can externally notice this pattern, and just enforce in the infinite extrapolation that P(B(Q)|A(Q)) is high for most Q. This does have some reference classes problems, though: how do you choose the class of "Qs" you should extrapolate to?
					- But there might be something nice to solve that, like "explicitly looking at the literal traders that are enforcing these patterns, and checking how they behave (individually) when seeing different future market states". This idea seems to follow the general motto "Don't only look at the final probabilities, look at the wealth distribution among the traders, since they are the actual mechanism by which extrapolation happens, and you can ask them things about the future that the static probabilities have no opinion on". "Find an infinite fix-point by giving more compute (as will happen in the future) to the finite amount of traders (with their wealth distribution) that you already have, without adding more (which is what actually happens when you run the LI)". The traders are like "the hypotheses you have considered (and have some feedback on)", and in being Updateless, you are happy to just extrapolate those infinitely, without worrying about whether you've missed a hypothesis. I'll pursue this line further.
				- AUTHOR:
				  collapsed:: true
					- I haven't read your email yet, this is a middle of the night thought.
					- One apparent problem with my idea is: if Q is thinking about A(Q'), with small thoughts, it cannot possibly be thinking of Q' in particular. So the small thoughts seemingly have to specify a way to aggregate over many Q' with the relevant property P. For example, in a counterfactual mugging, the 'get' branch doesn't know which precise branch is the real 'ask' branch. (There are two different relevant notions of the ""real"" ask branch: if the ask world is the real world, then the real ask branch is the actual market state; if the 'get' branch is the real world, then the "real" ask branch is the branch Omega simulates, to the extent that Omega simulates some actually specific market state.) What if we knew A(Q_1)=a_1, and A(Q_2)=a_2, but both Q_1 and Q_2 look like the 'ask' branch from the perspective of small beliefs? Are the actions in similar branches just supposed to be correlated enough that the prior doesn't expect this to happen?
					- My hope is that we don't have to deal with this problem directly, because the only thing we need is for the conditional expected utility on *one single Q'* to work out right.
				- Martin:
				  collapsed:: true
					- Yes, exactly! Now you are worrying about the small beliefs' opinions about the properties of some large states (even if the properties are "intuitively simple", like a syntactic property that's easy to check). That's exactly my point and my worry, and the reason I think we'll have to "explicitly choose" what to be updateful about. Because of course, who's to say what is "simple enough" that we can just be updateful about it? In fact, simplicity and "whatever it is instrumentally optimal to be updateful about" will many times come apart.
					- > Are the actions in similar branches just supposed to be correlated enough that the prior doesn't expect this to happen?
					- A priori that shouldn't work in general, since "arbitrarily small changes" (in the description of a branch) could lead to "arbitrarily different action recommendations" (or better said, our agent's beliefs about action recommendations).
					- > My hope is that we don't have to deal with this problem directly, because the only thing we need is for the conditional expected utility on *one single Q'* to work out right.
					- I'd certainly like to see this more developed because, despite my opinions, it's still conceivable that we can find an especially natural way to deal with this, that looks less like "we explicitly decide what to be updateful about" (although, strictly speaking, any solution will be implicitly deciding what to be updateful about).
					- Still, my intuition remains that the way of getting the right conditional expected utility on that single Q' must be letting it update on the right things.
					- Let me now address two of your previous points.
					- > Indeed, it seems like the o->a version is equivalent to EDT in the case that P(a|o) is the same for every action. So this really isn't UDT, and inferring problems for UDT seems unwarranted.
					- Yes, true. My point was just that what we thought we had the right version of UDT, and we were wrong! And given that, our intuitions differ about whether we'll find something more natural than "let the prior decide what to update on".
					- > What we want is that extrapolate($\mathcal{Q}$) has high/low expected utility conditioned on that policy point.
					- I think that happens by default, if by extrapolate(Q) you mean the extrapolated P conditioned on Q, as above. That is, if we condition on Q by BLI self-trust we get the implication, so if we also condition on the antecedent (policy point), we get the consequent (high utility). The problem is this (conditioning on the whole Q) amounts to being completely updateful! The problem isn't that we don't know how to get the implication across, but that we don't know how to do that without being completely updateful. (And I propose letting the prior decide what to update on, and you propose we'll find something else.)
					- Mathematical formalization of my straightforward idea for solving the foundational problem: "Let the prior decide what to be updateful about".
						- [insert pdf notes reference]
				- AUTHOR:
					- The following rambly email has a more important proposal at the end, which I'm particularly eager to hear your thoughts on. If your time is limited, skip past the "//////////////" mark.
					-
					- Yes, you are completely right, and not crazy! In fact, I had already had this realization. I should have written it down in the doc, but if I didn't it was because of the following train of thought:
					- "Oh, yes, this just happens because in those few worlds we are completely updateful (like EDT), and in the others completely updateless (about the real observation). This is nothing new, this is just realizing again that we know how to be completely updateful, we know how to be completely updateless, but we're missing the useful thing in between (exactly as in the A(o)=a case). This just clearly shows that we cannot be agnostic: an explicit decision has to be made about what to update on. So we'll let the prior decide that a priori (and if we do that, then we might as well condition on A(o)=a instead of on implications, since we prefer it for other reasons)."
					- As I've mentioned before, if we choose a set of observations which includes the observation we're considering a policy-point for, and which partitions the whole event space, we can call the elements of the partitions "branches". Call the observation which the policy-point we're evaluating belongs to the "home branch". We can then neatly divide consequences which UDT considers into three categories: (1) influences of the  policy-point on expected utility within other branches; (2) influences of the policy-point on relative branch probabilities; (3) impacts on the home branch (that is, updateful impacts).
					- Of the updateless impacts (1 and 2), the o->a version of UDT *only *considers (2), and further, *only changes the relative weight of the home branch compared to others*, and also *only reduces that weight*.
					- So the a->o version is extremely restricted in what type of updateless considerations it can consider. Plus it represents those considerations via non-equal action probabilities, which is a somewhat dubious way to represent Transparent Newcomb (since it cannot then distinguish Transparent Newcomb from merely being pretty confident that it won't take a specific action).
					- > Sentences like $\uparrow \mathbb{Q}_k (\forall \mathcal{Q} (P(\mathcal{Q}) \wedge (\mathbb{Q}_m = \mathcal{Q} \to A_m=a) \to \uparrow U)$ are making claims about the global expected utility being high under certain conditions. But this kind of thing is a meta-belief for UDT, which is to say, a statement about UDT's own evaluation of the expected utility.
					- I don't yet understand what you mean. I think that's an object-level belief, not explicitly including UDT's evaluation in any way (except for correlations that UDT might believe between its taken actions and its evaluation process, etc.). All variables (Q satisfying P(), Q implying A_m=a, and the LUV U being high) pertain to the object-level (how the environment looks, which consequences certain actions will have on the environment, etc.). Also, if our prior believes something like that, it will certainly be because it has seen particular object-level examples of that general \forall (or has proven them in its head).
					- The more I think about this, the more I agree that there's no way to revise my statement to make sense.
					- On a more general note, **here's a path I just thought of to a possible solution:**
					- Here's, first, a way to reframe the problem. When I want to represent "Q_k believes in the worlds in which A turns out true, so does B", of course I shouldn't formalize it as "Q_k(A->B) is high" (that might be high just because A is very unlikely). I should formalize it as "Q_k(B|A) is high". But then, what if I want to represent "Q_k believes that, for all Q, in the worlds in which A(Q) turns out true, so does B(Q)"?
					- (Here A(Q) is the above P(Q)&A(Q)=a, or "Omega asks for the capital of France, and I say Paris". And B(Q) is the above \uparrow U, or "I get $10".)
					- If I had gone with the implication, I could just say "Q_k(\forall Q (A(Q)->B(Q)) is high", and indeed that's what we were doing.
					- But inside Q_k's probability distribution, I can't say something like "\forall Q, Q_k(B(Q)|A(Q)) is high".
					- [...]
					- So, what if we include some explicit mechanism, on top of the probability distribution, that plays the role of that "external \forall" that doesn't have a representation inside the distribution? This mechanism will probably need to be intertwined with the infinite extrapolation.
					- [...]
					- The following isn't exactly the same as your idea, but has some resemblance.
					- Propositional coherence and LUV coherence succeed at relating 'small' and 'large' quite nicely, because there is a natural notion of marginalization in play which allows large beliefs to be turned into small beliefs (so we sort of know how to reverse the process).
					- The set of E(U|A(Q)=a) doesn't have an obvious notion of marginalization, so that is, in some sense, our bottleneck.
					- Imagine that the market has evolved for a long time and now has firm opinions about all A(Q)=a up to the size of Q_m, and also a highly informed estimate of U. How could all of that information be summarized in useful ways? Can we add a new mechanic, similar to propositional & LUV coherence, which forces coherence for such summaries? Perhaps most importantly, can the mechanism represent the intuitively important "small" relationships between the A(Q)=a sentences and U?
					- Well, I don't know what statistics will be important, but ***all ***statistics summarizing the joint A(Q)=a and U beliefs will be LUVs. So perhaps a new mechanism is not needed after all.
					- I'm also somewhat sympathetic to your idea that the information I'm trying to summarize is missing the conditional probability info in some sense, since I'm imagining as if we have solid values for all of the A(Q)=a and for U. But if we can summarize fully specified worlds with statistics, then we can take expectations of such summaries to summarize joint distributions, and joints imply conditionals.
					- So, for example, if I have small beliefs resembling counterfactual mugging, then possible Q divide into "asked" branches and "receive" branches (and others with low probability). Let's name those predicates Ask(Q) and Rec(Q). My belief that if I give $10 in response to being asked (Ask(Q)&A(Q)=give) then I should expect to get $100 (E(U|Rec(Q))=100) should somehow correspond to a summary of predictions I would make about the eventual joint state of all the A(Q)=a sentences and U. Maybe I think Omega picks one of the Q such that Ask(Q) at random, checks A(Q)=give, then checks the random coin, and gives me $100 if both are true. This should have implications about which small LUVs I would be willing to buy stock in.
					- Still, there seems to be a big problem connecting such things to the conditional probabilities. We want to condition P on A(Q)=refuse (where Ask(Q) is true) and see a dip in expected utility, compared to conditioning on A(Q)=give.
					- > Are the actions in similar branches just supposed to be correlated enough that the prior doesn't expect this to happen?
					- A priori that shouldn't work in general, since "arbitrarily small changes" (in the description of a branch) could lead to "arbitrarily different action recommendations" (or better said, our agent's beliefs about action recommendations).
					- Intuitively, it shouldn't matter too much whether I think all of the "give/refuse" decisions for different Q satisfying Ask(Q) are correlated or uncorrelated. (So long as they aren't anticorrelated.) If they're all quite correlated, then we should see a big change in U, since conditioning on any one A(Q)=give means many Ask(Q) end up 'give', and similarly for 'refuse'. If they're all independent, then conditioning on any one A(Q)=give would have a tiny influence on the expected utility, but in principle (if calculated with enough degrees of precision) giving up $10 in an epsilon-probable world to gain epsilon probability of $100 should still come out in favor of 'give'.
					- (But interestingly, how correlated these different decisions are depends in turn on the decision procedure (which itself depends on how correlated P thinks things are). Makes me feel like there should be a way to cut the loop and treat some decision classes as completely correlated based on the fact that the decision procedure does not distinguish the difference between them. I'm not claiming this thought is important to the overall idea, however.)
					- Sorry, I know this proposal is still not very concrete and I haven't said enough to prove that it works.
					- I'd certainly like to see this more developed because, despite my opinions, it's still conceivable that we can find an especially natural way to deal with this, that looks less like "we explicitly decide what to be updateful about" (although, strictly speaking, any solution will be implicitly deciding what to be updateful about).
					- Still, my intuition remains that the way of getting the right conditional expected utility on that single Q' must be letting it update on the right things.
					- Yeah, currently, I would really like either a stronger impossibility argument for "classic UDT" or a way to get it to work.
					- > What we want is that extrapolate($\mathcal{Q}$) has high/low expected utility conditioned on that policy point.
					- I think that happens by default, if by extrapolate(Q) you mean the extrapolated P conditioned on Q, as above.
					- Confirmation that this is what I meant.
					- That is, if we condition on Q by BLI self-trust we get the implication, so if we also condition on the antecedent (policy point), we get the consequent (high utility). The problem is this (conditioning on the whole Q) amounts to being completely updateful! The problem isn't that we don't know how to get the implication across, but that we don't know how to do that without being completely updateful. (And I propose letting the prior decide what to update on, and you propose we'll find something else.)
					- Notice that I'm not conditioning on Q, but rather, I'm noting that taking the expectation in P decomposes into many expectations given each possible Q. So I think your observation (that this just works by default) puts us in a pretty good situation.
					- id:: 65392abe-0974-4591-b379-7ae788d649c1
						- So in particular, let us suppose the 100% correlated picture:
						- -
						- P thinks Q_m will satisfy either Ask or Rec with 98% probability, and equal probability (49%) between the two possibilities.
						- -
						- Branches Q satisfying Rec(Q) believe that Ask(Q') implies A(Q')=give -> U=100, and A(Q')=refuse->U=0.
						- -
						- Branches Q satisfying Ask(Q) believe that Ask(Q') implies A(Q')=give -> -10, and A(Q')=refuse -> U=0.
						- Then conditioning P on the policy-point A(Q')=give where Q' satisfies Ask, the calculation (mostly) decomposes into two cases, those where Ask(Q_m) and those where Rec(Q_m) (with equal probability). Similarly for the calculation of A(Q')=give. The question is whether those four cases correctly evaluate to the numbers we want (-10, 0, +100, 0).
						- Let's consider one of those four cases: Ask(Q_m) for the policy point A(Q')=give.
						- Let's assume that Ask(Q) and Rec(Q) are themselves LUVs which can be defined from the LUVs of the Q they evaluate, so that conditioning P on Ask(Q_m) gives P the (average) beliefs of such Q. [So Ask(Q_m) is a small conjunction of basic claims about the market, such that LUV-coherence makes the expected probability of Ask(Q_m) equal the probability that Ask(Q) for a Q randomly drawn from P. Self-trust then means conditioning on the small statement Ask(Q_m) gives us the average beliefs of Q satisfying Ask(Q).]
						- So the expected utility of A(Q')=give according to P decomposes into 48% E(U | A(Q')=give, Ask(Q_m)) and 48% E(U | A(Q')=give, Rec(Q_m)) and 2% some other stuff I'm going to neglect. And we're here focusing on the component of this sum where Ask(Q_m). We want the expectation to equal -10.
						- Since P( . | Ask(Q_m)) has the average beliefs of ask branches, it believes that forall Q, Ask(Q) -> [A(Q)=give -> -10]. So in particular, for the Q' belonging to the policy point we're conditioning on, it believes Ask(Q') -> [A(Q')=give -> -10]. And it is also being conditioned on A(Q')=give. So what we need is for it to believe Ask(Q').
						- I expect you to say that, yes, this illustrates that we need P to decide to update on Ask(Q') before making the decision.
						- Because of course, who's to say what is "simple enough" that we can just be updateful about it? In fact, simplicity and "whatever it is instrumentally optimal to be updateful about" will many times come apart.
						-
						- But here we have an obvious candidate for "simple enough": Ask() already needs to satisfy the property I mentioned earlier, of being a simple compound LUV. So all we need here is the following extension of LUV coherence: if F(Q) is a small conjunction of simple claims about market Q, then P is updateful about the evaluation of F, even on large Q.
						- So I argue that given this, P evaluates the case we're considering to -10, and also correctly evaluates the three other cases; so, decides to take the counterfactual mugging.
						- Sorry for the slightly ambiguous notation in the above; hopefully the idea is clear enough?
						- As I argued earlier, the picture when decisions are less than 100% correlated between 'ask' branches should yield a similar result despite being more complex, although I'm far from certain that it works out.
				- Martin
				  collapsed:: true
					- Your reasoning is correct, as far as I can tell. And the heart of your proposal seems to be this:
					- > But here we have an obvious candidate for "simple enough": Ask() already needs to satisfy the property I mentioned earlier, of being a simple compound LUV. So all we need here is the following extension of LUV coherence: if F(Q) is a small conjunction of simple claims about market Q, then P is updateful about the evaluation of F, even on large Q.
					- And you are right: we can do that! Actually, this is no news for me. My claim is that this is not especially natural or privileged (even if it has some a priori intuitive pull), and that it's actually worse for our purposes than letting P decide what to be updateful about.
					- Why is this not natural or privileged? Well, what's your definition of "F(Q) is a small conjunction of simple claims about market Q"? We can fix an arbitrary definition (an arbitrary "complexity point" at which we stop being updateful). And that's the usual approach of "being updateful about things inside this complexity class, and updateless about things inside it". And it has its usual problems. It seems intuitively good because "we are okay updating on the simple, syntactic properties of nodes, because those will lead to correctly to extrapolating P's opinions about which policies to implement". That is, we like this proposal because it will intuitively have good consequences. But what if P could extrapolate some further beliefs (that correspond to reality) if it just were updateful about another, slightly more complex syntactic property F'() (that falls just outside the scope of our "complexity" barrier). Or on the contrary, what if P wanted to be updateless about a certain property F'() (because it correctly predicted Omega would take that into account), but unfortunately that F'() falls just inside our "complexity" barrier? Ask() and Rec() look especially obvious and "given", but in reality we'll be dealing with a myriad of logical formulas, which might mean a myriad of things, and whose simplicity and usefulness sometimes vary independently.
					- Yes, we have to draw the boundary of "what to update on" somewhere (that was my "foundational problem" realization). But what I'm explaining here is my earlier point: "updating on simple things" and "updating in an instrumentally optimal way" come apart. And we terminally care about the latter (consequences, reward, performance), and not the former. So our definition of "what to update on" should align with the latter, not the former.
					- And that's what "ask P what we should update on" does. Given we care about consequences, and that in a realistic situation the agent's only way to think about consequences will be its own opinions (we won't have access to an external oracle deciding optimal action for us, or anything like that), we need to use its opinions (that's the best we can do in bounded rationality). And of course they will sometimes be fallible (bounded rationality), but to the extent those beliefs are "what's being epistemically optimized to fit the world" (and indeed, in our current framework, the prior's beliefs have not yet been optimized for instrumentality), we have to trust that "in the limit they will approximate real consequences". We won't find a better proxy for "having good consequences", and that's what we care about ultimately.
				- The author
				  collapsed:: true
					- |
					- | to Martín[scrubbed] |
					- |
					- > And you are right: we can do that! Actually, this is no news for me. My claim is that this is not especially natural or privileged (even if it has some a priori intuitive pull), and that it's actually worse for our purposes than letting P decide what to be updateful about.
					- Why is this not natural or privileged? Well, what's your definition of "F(Q) is a small conjunction of simple claims about market Q"? We can fix an arbitrary definition (an arbitrary "complexity point" at which we stop being updateful). And that's the usual approach of "being updateful about things inside this complexity class, and updateless about things inside it". And it has its usual problems. It seems intuitively good because "we are okay updating on the simple, syntactic properties of nodes, because those will lead to correctly to extrapolating P's opinions about which policies to implement". That is, we like this proposal because it will intuitively have good consequences. But what if P could extrapolate some further beliefs (that correspond to reality) if it just were updateful about another, slightly more complex syntactic property F'() (that falls just outside the scope of our "complexity" barrier). Or on the contrary, what if P wanted to be updateless about a certain property F'() (because it correctly predicted Omega would take that into account), but unfortunately that F'() falls just inside our "complexity" barrier?
					- I expect I will end up agreeing with this to some extent, but I am still strongly entertaining the idea that the proposal I offered is indeed a privileged position. So, how do we adjudicate?
					- -
					- You ask how I define "small conjunction of simple claims". I'm implicitly claiming that a specific definition will be essentially forced; you are implicitly claiming that there will be many possibilities and an obvious parameter.
					- -
					- You ask, what if P could extrapolate some further beliefs if it were just a bit more updateful? On your side, you claim that we should allow P to decide to be more updateful than this, in order to capture those gains (in cases where we're lucky enough to have P which sees the gains). On my side, I claim** this should not be necessary**: If my intuition is correct, then so long as we meet the minimal logical-updatefulness condition I named, **any further updatefulness which P would endorse if we followed the two-step procedure will already be rolled into the one-step procedure**. I think this is probably the main crux.
					- -
					- You ask what happens if my proposal is actually too logically updateful, and Omega wants to offer a cf mugging on such things? On your side you expect a convincing decision problem to come out of such a story; on my side I might claim there won't be one. I think this is less of a crux, because if my previous claim is true, I might be happy to sacrifice such decision problems. I agree with the claim that there will always be some sort of logical updatefulness forced by the decision calculation itself; I'm happy to make some sacrifices on that front for nice properties.
					- So the main story I should work on elaborating is the bolded claim above.
					- Desired property: UDT already behaves updatefully with respect to some computational knowledge (some boundedly-knowable proposition X) if it thinks it's a good idea. Adding a two-step decision process in which UDT first decides what to be updateful about, and then makes the UDT calculation, never adds anything.
					- Rough argument: if X is boundedly-knowable by Q_m, and P thinks it is a good idea to make time-m decisions (both real and counterfactual) in a way that's updateful about X, then an argument similar to the one I made in the previous email will establish that UDT will already behave as if P had been updated on X before making the decision.
				- Martin
				  collapsed:: true
					- |
					- | to me[scrubbed] |
					- |
					- > You ask, what if P could extrapolate some further beliefs if it were just a bit more updateful? On your side, you claim that we should allow P to decide to be more updateful than this, in order to capture those gains (in cases where we're lucky enough to have P which sees the gains). On my side, I claim** this should not be necessary**: If my intuition is correct, then so long as we meet the minimal logical-updatefulness condition I named, **any further updatefulness which P would endorse if we followed the two-step procedure will already be rolled into the one-step procedure**. I think this is probably the main crux.
					- I don't see right now how this could be the case. That is, I think there will always be counter-examples to any proposed definition of "small conjunctions of simple claims" (choice of the parameter).
					- Say you define that to be any complexity class. I will be able to construct a situation in which our agent is very certain of the optimality of some policy, and they are right, and nonetheless they cannot implement it because they have to be updateful about something outside the complexity class. If the complexity class is "polynomial-time checks", then it could require an exponential-time check. Similarly for bounds on lengths of the logical formulas defining the properties, etc.
					- And I can also construct an opposite counterexample in which the agent learned early enough (correctly) that it should be updateless about a property, but our choice of complexity class forces it to update (but it seems like you're less worried about this one).
					- Something I could conceive happening is "it turns out, when  you average across all these decision trees, that updating on all polynomial-time properties is better than updating on all exponential-time properties". And maybe even something nicer like "there is an optimal complexity class". But this has more to do with average performance, and gets into the problem of how we average across trees (maybe different notions of average incentivize different complexity classes). And I think this is not what you have in mind.
					- > UDT already behaves updatefully with respect to some computational knowledge (some boundedly-knowable proposition X) if it thinks it's a good idea
					- Again, here I want to say: Yes, this is the desired property! We care about doing that when "it thinks it's a good idea". But then why would we use complexity classes instead of just letting it choose? Isn't it trivial that complexity classes and this subjective "it's a good idea" (which depends on P) will sometimes come apart? (Even if something nice about complexity classes and averages of decision trees might exist?)
					- ---------------------------------------------------
					- I've also been reading the longer part of your previous email, and it makes sense and is interesting! I'll have to think more about your take on my possible solution. Although after writing my "possible solution" paragraph, my feeling had been I should pursue the "extrapolating from the current traders" direction (instead of thinking solely in terms of probability distributions).
					- ---------------------------------------------------
					- I adjoin my idea to have finite states of an LI satisfy Reflection and Self-trust, which seems closer to Sam's original BLI motivation.
						- [reflection principle and epistemic self trust pdf]
					- I think it works, and the idea of having traders bet on "bundles" of possible worlds (instead of all possible worlds independently), a la credal sets, seems like a natural way to introduce constraints, and might be useful in other settings.
				- Martin
				  collapsed:: true
					- |
					- | to me[scrubbed] |
					- |
					- Just flagging the state of the debate about updating on stuff, since it felt central and I want to revise it more calmly:
					- It seems like the main differences are two
					- 1. Explicitly deciding to "forever update on whether the present node has the shape of a Counterfactual Mugging" will keep working forever (modulo changes of mind due to updating other things). On the contrary, it seems like your argument above "assumed that we already know we are in a Counterfactual Mugging", but P only knows this about a finite amount of decision nodes, so it will at some finite time "stop working", and dissolve into P being almost completely uncertain about what happens in that decision node (and maybe this results in updating, maybe it doesn't).
					- 2. Also, it seems like your definition of "P believes it is okay to update" is "these kinds of independence happen" (and we think there's no logical sentence expressing this, it's a meta-property of the distribution P). On the contrary, mine was "P believes the policy of "following P but updating on A" has higher expected U than the policy of "following P"". But this difference seems less important, and for example we can modify my proposal to use your definition.
				- The author
				  collapsed:: true
					- Here is my own attempt to summarize and expand upon our discussion.
					- First of all, there is an important definition question to flag: there are several possible definitions of "P thinks it is a good idea to behave updatefully wrt proposition X". The two main ideas are an expected-utility sense, vs an independence-assumptions sense.
					- I called my thing one-step UDT, and your thing two-step UDT. I suggested that your concern that my thing inherently has some parameter defining what to be updateful on, is similar to my concern about your thing, which is that if two steps are better than one, N steps might be better than N-1, which also creates an arbitrary parameter.
					- You clarified that this is also what you expect, and you also argued that this pushes toward arbitrary policy selection (since N steps of thinking how to think may approximate arbitrary procedures).
					- I clarified that I also believe this may be the case for some class of minds, but I want to codify the assumptions under which one-step UDT is equivalent to N-step UDT. We can *then *assess how realistic those assumptions are and what happens when they are broken. But I still currently believe there is a semi-distinguished set of assumptions where N-step is not needed.
					- It seemed like I did convince you, modulo more detailed review of my earlier email argument, that in ***individual ***cases where P thinks behaving updatefully with respect to X is a good idea (in the independence-assumptions sense). More specifically, this argument works under the assumption that (1) actual beliefs marginalize correctly (prop & luv coherence), (2) self-trust, (3) hypotheticals also marginalize correctly (so expressions of the form [variable](syntactic belief state specification) have correct known values, where 'variable' is a proposition or a LUV; or at least, have correct known values to within some tolerance).
					- To reiterate my argument a bit: my earlier email worked out the case where P expects a counterfactual mugging, and argued that (under the above-mentioned assumptions) the usual UDT calculation of the expected value falls out of the BLI's expected value calculation. If this argument indeed works, then I claim that similar reasoning will cause UDT to behave updatefully when no acausal correlations exist.
					- You raised the concern you mention in your email, that this argument depends too strongly on P already anticipating a counterfactual mugging:
					- Explicitly deciding to "forever update on whether the present node has the shape of a Counterfactual Mugging" will keep working forever (modulo changes of mind due to updating other things). On the contrary, it seems like your argument above "assumed that we already know we are in a Counterfactual Mugging", but P only knows this about a finite amount of decision nodes, so it will at some finite time "stop working", and dissolve into P being almost completely uncertain about what happens in that decision node (and maybe this results in updating, maybe it doesn't).
					- I now note that if X(node) are propositions claiming that particular nodes are counterfactual muggings, then plausibly my argument applies to all such propositions. In which case we can at least say that if P fails to treat a node as a counterfactual mugging (even though it was knowable that this node was a counterfactual mugging), it's because P saw some reason why it should not do so (in the form of acausal correlations).
					- However, it remains true that a big difference between my approach and yours is that my approach (apparently, at least) requires *specific* beliefs that *specific* propositions can be treated updatefully (in an independence sense). Despite Universal Instantiation, it remains plausible that P may have a universal belief about some predicate X(node) being good to update on *for all instances*, and that your approach will then do that, where my approach may fail to do that.
					- This is because the independence-based version of "X is good to update on" apparently has no universal version. As you say:
					- Also, it seems like your definition of "P believes it is okay to update" is "these kinds of independence happen" (and we think there's no logical sentence expressing this, it's a meta-property of the distribution P). On the contrary, mine was "P believes the policy of "following P but updating on A" has higher expected U than the policy of "following P"".
					- For some time you argued that there must be an object-level belief which we can universalize. But I asked whether a belief that "forall x, P(A(x)|B(x)) = P(A(x))" would end up enforcing the independence relation in all cases, vs just enforcing belief in the independence relation. You seemed immediately convinced that this would not work, and you said something about not being able to get universal instantiation to do something like that.
					- So this question still seems a bit open to me.
					- -
					- Does there exist some strengthened BLI for which universal beliefs about independence properties can indeed enforce specific independence properties?
					- -
					- Does there exist some alternate way to state my condition, such that it can be universalized? Some object-level beliefs which imply independence?
					- -
					- Can some other approach allow generalizations over subjective (non-object-level) stuff? EG, can a pseudo-proposition 'reifying' the conditional probability be introduced? Or can we move beyond probability somehow to make this sort of thing work?
					- But at present it seems quite plausible that there's no approach which is based on universal generalizations about what's good to update on, like yours, but uses an independence-based idea of "what's good to update on", like mine.
					- Probably there is still an argument to be had about which approach makes more sense if one has to choose between them. EG, you are suspicious that weird/bad things happen when P runs out of considered opinions, where I am optimistic that this just makes things more updateful. Also, I think you are more optimistic that universal generalizations typically represent real knowledge based on evidence, where I am more suspicious that universal generalizations represent the arbitrary beliefs of traders much more than non-universal beliefs do, since true-in-fact universals cannot always be proved, and there's nothing about logical induction which forces belief in such propositions to be high, even after LI has run for a long long time.
					  As a final note, I see two holes in my analysis of counterfactual mugging. First, I did not analyze shifting branch probabilities; I only analyzed the expected value of branches when conditioned on policy points. Second, the analysis appears to rely on *certainty* about what U will be in branches of specific types, rather than *expected values*. So the analysis might fall apart if we add Gaussian noise to the final utility. This is again because we can universalize object-level beliefs, like U=-10, but not subjective beliefs, like E(U)=-10. We cannot replace U=-10 with "U probably equals something close to -10" without making the argument rely on "universal instantiation of beliefs about probabilities enforces those constraints on the probabilities". And even if *that* worked, there might be some cases where the whole thing still fails, since the universal generalization can be spoiled by one case where such a subjective belief would be inappropriate (like, one case where we somehow know the gaussian noise is +100, so we don't want to instantiate our uncertainty -- so the universal is actually false, breaking the whole argument).
				- Martin
				  collapsed:: true
					- > I now note that if X(node) are propositions claiming that particular nodes are counterfactual muggings, then plausibly my argument applies to all such propositions. In which case we can at least say that if P fails to treat a node as a counterfactual mugging (even though it was knowable that this node was a counterfactual mugging), it's because P saw some reason why it should not do so (in the form of acausal correlations).
					- I disagree that "this solves the problem".
					- Indeed, what do you mean by "it was knowable that this node was a counterfactual mugging (that is, X(node))"?
					- P will have very valid opinions on X(n) for many n (all those it has had time to think about, before being frozen). But for infinitely many of them, it will have some "mostly random guess" (obtained through the extrapolation). For example, for a given very large n, it might think the probability of X(n) is 0.3 (because approximately 0.3 of all the nodes it's seen have been Counterfactual Muggings), and then 0.2 probability that it's Parfit's Hitchhiker, 0.25 that it's another random thing, etc. Say n is indeed a Counterfactual Mugging. Say also that, when this node is reached, our completely updated logical inductor Q_n already knows that n is a Counterfactual Mugging.
					- If we don't implement my thing, P won't "automatically play the Counterfactual Mugging correctly", because it won't have "automatically come to the realization that it's a Counterfactual Mugging". P is uncertain between many things, so it won't sensibly discern actions, and maybe choose a mostly random one. Sure, P might have a belief saying "in these situations I'd be better off checking whether X(n), and if so acting as in a Counterfactual Mugging" (call this policy Policy(n)). But if we're not implementing my thing, this belief won't be used in any way (we won't actually "run" this Policy). P will be uncertain about the value of Policy(n) (because by hypothesis it is uncertain about the value of X(n)), and so will not "run" Policy(n), just play its best guess as to what Policy(n) might be (which is a bad guess).
					- So, if by "it was knowable that X(node)" we mean that "P already knew that X(n)", the conclusion follows trivially.
					- But if we meant the actually interesting "the completely updated Q_n knew that X(n)", then the conclusion doesn't follow unless we implement my thing. Indeed, in this example P fails to treat n as a Counterfactual Mugging not because of "worries about acausal correlations", but just because it didn't know X(n) to begin with, and we haven't provided a mechanism for it to update on that knowledge (that is, we have always just implemented P as it was "to begin with").
					- Another way to say this is as follows:
					- Your original argument assumed some beliefs (about X(), Ask() and Rec()), and had as conclusion the right conditioned expectations.
					- I don't think there's an analogue version of this argument whose conclusion is "the right probabilistic beliefs about X(n)". You were already assuming the structure, which is, after all, information. We cannot derive this structure from nowhere. We cannot materialize information from thin air (since X(n) is something our P is truly uncertain about).
					- > However, it remains true that a big difference between my approach and yours is that my approach (apparently, at least) requires *specific* beliefs that *specific* propositions can be treated updatefully (in an independence sense). Despite Universal Instantiation, it remains plausible that P may have a universal belief about some predicate X(node) being good to update on *for all instances*, and that your approach will then do that, where my approach may fail to do that. This is because the independence-based version of "X is good to update on" apparently has no universal version.
					- I don't think that the reason why "your proposal eventually stops having information on X(node), while mine has incoming information forever if it chooses to" (main difference 1. in my previous email) is because your independence-based definition has no universal version.
					- In fact, my expectations-based version doesn't have a universal version either, since it talks about to conditionals of P, just like your version (although different conditionals).
					- I think these are two "orthogonal" axes of variation (as I tried to represent when talking about them as main differences 1. and 2. in my previous email).
					- Indeed, "my thing" of adding something on the conditionals (feeding these or those updates to P) is independent from whether these updates are chosen using your definition or my definition.
					- So when you say:
					- > But at present it seems quite plausible that there's no approach which is based on universal generalizations about what's good to update on, like yours, but uses an independence-based idea of "what's good to update on", like mine.
					- I again think this is not the case, and that using "my thing" (detailed on the document "Deciding what to be updateful about"), but with your definition as the way to choose what to update on, would completely work. It's just a different criterion for choosing what to update on.
					- So in summary I think both your and my definition are in the same "limbo" of not having a Universal version. But that's okay, because we'll have to ad hoc choose what to update on anyway, and we can define it however we want (in our ad hoc definition to decide what to update on, we are not constrained by "what can be expressed in a probability function").
					- Nonetheless, exactly because I'm interested in which "ad hoc mechanisms to implement above the probability distribution" are privileged, your following question is very interesting and natural:
					- > Can some other approach allow generalizations over subjective (non-object-level) stuff? EG, can a pseudo-proposition 'reifying' the conditional probability be introduced? Or can we move beyond probability somehow to make this sort of thing work?
					- Indeed, instead of taking the probability distribution and reading some things off it, what if we alter the probability distribution itself (or all states of the inductor) in some other way that more natively lends itself to that information being extracted? I shall think more about this, and my related idea of "extrapolating traders". Although I do think these will all ultimately be "more or less natural/privileged ways of choosing what to update on".
					- > Also, I think you are more optimistic that universal generalizations typically represent real knowledge based on evidence, where I am more suspicious that universal generalizations represent the arbitrary beliefs of traders much more than non-universal beliefs do, since true-in-fact universals cannot always be proved, and there's nothing about logical induction which forces belief in such propositions to be high, even after LI has run for a long long time.
					- That's a very important point that I wasn't considering. Thank you!
					- I guess I have generally indeed taken the approach "LIs don't have ALL properties we'd like, but let's just take their way of reasoning as the baseline for now and see which things we can extract or add on top".
					- > This is again because we can universalize object-level beliefs, like U=-10, but not subjective beliefs, like E(U)=-10.
					- I think this won't be a problem because the argument will go through "in each of the different possible worlds" (the world where U=-9, the one where U=-11, etc.), weighed by their probabilities (instead of the single very likely world U=-10). And this all works out thanks to LUV coherence. But I'll check it properly tomorrow.
					- > I want to codify the assumptions under which one-step UDT is equivalent to N-step UDT.
					- That makes sense. If I am comfortable with N-step UDT, it's mainly because I expect these assumptions to be something tantamount to baking in our desired consequence (because the consequence is broken in lots of natural situations). Of the kind "all checks that the optimal policy (according to P) performs can be performed at once (sequential checks, with dependencies, are not better according to P)". Because that property is fundamentally mind-dependent, and we don't know of another name for it. Or, if we turn to the dynamic setting and check against real feedback instead of P's beliefs (so the property becomes "a prior/LI with access to these N meta-levels won't eventually do better than one with a single level"), it's decision-tree-dependent instead of mind-dependent.
				- The author
				  collapsed:: true
					- Looks like I managed to uncover some remaining disagreements I wasn't aware of!
					- I now note that if X(node) are propositions claiming that particular nodes are counterfactual muggings, then plausibly my argument applies to all such propositions. In which case we can at least say that if P fails to treat a node as a counterfactual mugging (even though it was knowable that this node was a counterfactual mugging), it's because P saw some reason why it should not do so (in the form of acausal correlations).
					-
					- I disagree that "this solves the problem".
					- Indeed, what do you mean by "it was knowable that this node was a counterfactual mugging (that is, X(node))"?
					- This feels like some sort of miscommunication, so I will try to step thru what I was trying to say very carefully, while also attempting to directly respond to what you are saying.
					- As stated previously, I think we are somewhat on the same page about the following: given (a) correct marginalization for propositional and luv beliefs ("coherence"), (b) self-trust, and (c) correct marginalization of* hypothetical* propositional and luv beliefs, then *in an individual case where P expects a counterfactual mugging, (one-step) UDT will handle the counterfactual mugging as expected* (as classical UDT calculations expect, that is).
					- For clarity, I will call this the "single-instance success thesis" (SIST). The argument in favor of SIST is the one marked by "//////////////" in my email from Sept 18.
					- Where we differ is on what to expect in cases where P does not already anticipate a specific sort of decision problem. Here is one way of framing it:
					- -
					- When (classical) UDT is applied to a decision problem, we usually assume that the decision problem occupies the whole prior: UDT knows what decision problem it is about to face, and does not expect any other kind of branch.
					- -
					- SIST establishes that my one-step UDT solves that sort of problem.
					- -
					- However, you correctly point out that this is not what we realistically expect. We expect UDT to encounter many decision problems which it did not precisely foresee.
					- -
					- I take SIST as evidence that one-step UDT "correctly reasons about branches of probability". For me, uncertainty about which of many decision problems will be encountered is a sort of decision problem in itself; if I "correctly reason about branches" then I will handle the more complex case as rationally as I handle the simpler case (but with more uncertainty, of course, which does imply poorer performance). (*Note: this "evidence" is not going to be my main argument. I am not claiming you should find this persuasive. I am just describing my thinking, here.)*
					- -
					- You take SIST to be very little or no evidence to this effect. You continue to anticipate that if P does not anticipate a specific decision problem, then my one-step UDT will essentially fail on that decision problem, even if the details of the situation become clear in later Q_n and P correctly believes that it should behave updatefully on that information (ie, two-step UDT works).
					- This rough picture of our disagreement became clear during the phone call, although not quite in these terms, so perhaps you will disagree with some aspect of the above characterization. However, it seems consistent with your summary:
					- Explicitly deciding to "forever update on whether the present node has the shape of a Counterfactual Mugging" will keep working forever (modulo changes of mind due to updating other things). On the contrary, it seems like your argument above "assumed that we already know we are in a Counterfactual Mugging", but P only knows this about a finite amount of decision nodes, so it will at some finite time "stop working", and dissolve into P being almost completely uncertain about what happens in that decision node (and maybe this results in updating, maybe it doesn't).
					- This brings us to my remark that your latest email begins by quoting:
					- I now note that if X(node) are propositions claiming that particular nodes are counterfactual muggings, then plausibly my argument applies to all such propositions. In which case we can at least say that if P fails to treat a node as a counterfactual mugging (even though it was knowable that this node was a counterfactual mugging), it's because P saw some reason why it should not do so (in the form of acausal correlations).
					- I'll call this "the X(node) argument" for convenience.
					- The general hope of this remark is to argue that SIST implies some degree of "correctly reasoning about branches" which has some positive impact on decision problems which are not already fully encoded in P. I do not claim that this argument gives us everything we might possibly want in this respect. Your first reaction is:
					- I disagree that "this solves the problem".
					- I worry this misunderstands my intention. My hope was more limited. My statement of the argument was very brief because I saw it as a bit of a side-show to the more important notes. Indeed, my next paragraph after the argument begins...
					- However, it remains true that a big difference between my approach and yours is that my approach (apparently, at least) requires *specific* beliefs that *specific* propositions
					- ...but it's probably best to set that discussion aside for now and focus on what I *do* hope to establish with the X(node) argument.
					- You ask:
					- Indeed, what do you mean by "it was knowable that this node was a counterfactual mugging (that is, X(node))"?
					- First I'll describe what I mean by "this node is a counterfactual mugging" (that is, X(node)), and then "it was knowable".
					- The definition of X(node) borrows heavily from my "//////////////" argument:
					- -
					- There are predicates Rec() and Ask() which apply to whole branches Q. (Ask() is supposed to say something like "Q sees that Omega is asking for $10", while Rec() is something like "Omega is not asking for $10 (so I updatefully know that my reward, or lack thereof, is coming soon)".
					- -
					- Branches Q such that Rec(Q) believe that Ask(Q') implies A(Q')=give -> U=100, and A(Q')=refuse->U=0.
					- -
					- Branches Q such that Ask(Q) believe that Ask(Q') implies A(Q')=give -> -10, and A(Q')=refuse -> U=0.
					- -
					- X(node) is just "Rec(node) or Ask(node)"; that is, you believe that either you'll be asked, or on the receiving branch, when you get to "node".
					- Now for "it is knowable". iirc, our convention was that P = extrapolate(Q_n). Suppose that the "node" in question will be on day m. To recognize something as a counterfactual mugging is to recognize it *ahead *of time; so "it is knowable" means that there is some c such that n<c<m, and such that X(node) has a high probability in Q_c. Suppose for the moment that the probability was negligible before time c, and furthermore, *no other* acausal impacts on this decision node rise to high probability before the proposition X(node) does. Then my argument for SIST (the "//////////////" argument) applies to the expected value of the relevant policy-points down that specific branch.
					- Now furthermore suppose that the proposition X(node) itself is one which P thinks it should behave updatefully about, which is to say, it meets the relevant independence assumptions in P, such that SIST implies that the proposition X(node) is one which will be treated in an updateful manner (by single-step UDT). (For emphasis: this does not mean that P knows X(node); rather, P is such that one-step UDT will treat X(node) as true *or as false* depending on what more-updated opinions say).
					- Then since single-step UDT behaves updatefully about X(node), and knows X(node) at time c, it will treat "node" as a counterfactual mugging, in the same way that it would if P had believed X(node) from the beginning. Except, the branch probabilities for Rec(Q) vs Ask(Q) get derived from extrapolate(Q_c) rather than P.
					- This seems to establish the desired result, which is that **if one-step UDT fails to treat a node as a counterfactual mugging, even though it was knowable that the node would be a counterfactual mugging** (ie, Q_c comes to be confident in X(node))**, it's because P saw some reason why it should not do so** (ie, P thinks some other acausal influences deserve more consideration, meaning either: X(node) does not look worthy of updateful treatment, or "node" is involved in some other important acausal business before Q_c).
					- This conclusion is a moderate extension of SIST: I argue that single-step UDT not only gets problems right if P expects them; it also gets problems right if some intermediate Q_c sees them coming, and P sees no reason to ignore that information. So I will call this FIST, "foreseeable instance success thesis" (although I make no claims that these abbreviations are optimal descriptions of the thing abbreviated).
					- Having explained my intended argument more thoroughly, I'll now move on to address your criticisms:
					- P will have very valid opinions on X(n) for many n (all those it has had time to think about, before being frozen). But for infinitely many of them, it will have some "mostly random guess" (obtained through the extrapolation). For example, for a given very large n, it might think the probability of X(n) is 0.3 (because approximately 0.3 of all the nodes it's seen have been Counterfactual Muggings), and then 0.2 probability that it's Parfit's Hitchhiker, 0.25 that it's another random thing, etc. Say n is indeed a Counterfactual Mugging. Say also that, when this node is reached, our completely updated logical inductor Q_n already knows that n is a Counterfactual Mugging.
					- If we don't implement my thing, P won't "automatically play the Counterfactual Mugging correctly", because it won't have "automatically come to the realization that it's a Counterfactual Mugging". P is uncertain between many things, so it won't sensibly discern actions, and maybe choose a mostly random one. Sure, P might have a belief saying "in these situations I'd be better off checking whether X(n), and if so acting as in a Counterfactual Mugging" (call this policy Policy(n)). But if we're not implementing my thing, this belief won't be used in any way (we won't actually "run" this Policy). P will be uncertain about the value of Policy(n) (because by hypothesis it is uncertain about the value of X(n)), and so will not "run" Policy(n), just play its best guess as to what Policy(n) might be (which is a bad guess).
					- I hope it is clear that I am not denying this. An arbitrary P can think that the world has some arbitrary acausal considerations, which will result in some arbitrary behavior.
					- On the other hand, I don't think two-step UDT totally changes this, either, since the quality of the two-step process is still dependent on sanity on the part of P.
					- So, if by "it was knowable that X(node)" we mean that "P already knew that X(n)", the conclusion follows trivially.
					- But if we meant the actually interesting "the completely updated Q_n knew that X(n)", then the conclusion doesn't follow unless we implement my thing.
					- Hope it's clear that I meant neither of these things; rather, X(node) should be known by some intermediate Q_c.
					- Indeed, in this example P fails to treat n as a Counterfactual Mugging not because of "worries about acausal correlations", but just because it didn't know X(n) to begin with, and we haven't provided a mechanism for it to update on that knowledge (that is, we have always just implemented P as it was "to begin with").
					- Hope it's clear why I think this is false (under some assumptions I've articulated).
					- Another way to say this is as follows:
					- Your original argument assumed some beliefs (about X(), Ask() and Rec()), and had as conclusion the right conditioned expectations.
					- I don't think there's an analogue version of this argument whose conclusion is "the right probabilistic beliefs about X(n)". You were already assuming the structure, which is, after all, information. We cannot derive this structure from nowhere. We cannot materialize information from thin air (since X(n) is something our P is truly uncertain about).
					- I hope I've convinced you that there is an analogous version of the argument, which extends SIST slightly into the case where X(n) is truly uncertain for P.
					- This completes my remarks on the "X(node) argument" portion of your email.
					- ================
					- The rest of this email pertains to the rest of your email.
					- I don't think that the reason why "your proposal eventually stops having information on X(node), while mine has incoming information forever if it chooses to" (main difference 1. in my previous email) is because your independence-based definition has no universal version.
					- In fact, my expectations-based version doesn't have a universal version either, since it talks about to conditionals of P, just like your version (although different conditionals).
					- I think these are two "orthogonal" axes of variation (as I tried to represent when talking about them as main differences 1. and 2. in my previous email).
					- I was initially quite surprised to read this. A major motivation behind me writing my email was that *your* email suggested that 1 and 2 were orthogonal, whereas I had come away from our meeting with the impression that we had mutually concluded that they were not orthogonal. I thought this was your reason to think two-step could still be superior to one-step, even under my assumptions for getting one-step to work: because two-step UDT can "decide to update forever" while one-step UDT can "only know things about a finite number of decisions".
					- So I've finally consulted your pdf detailing the two-step procedure. I see that the relevant distinction is something like "always good to update" vs "good to always update". You don't look for generalizations about what's good to update on, but instead, you check the expeted value of computer programs which enumerate things to be updateful about.
					- But I'm still not seeing how a two-step independence-based UDT could achieve this sort of updatefulness about infinitely many sentences. So (1) and (2) still don't appear orthogonal to me.
					- By the way, I think this is not *quite* true:
					- so it will at some finite time "stop working", and dissolve into P being almost completely uncertain about what happens in that decision node (and maybe this results in updating, maybe it doesn't).
					- The SIST argument can handle the case where *every* decision node is (believed to be) a counterfactual mugging: forall n, X(n) can be known, in which case X(n) is known for infinitely many cases, so one-step UDT does not sputter out into oblivion (or updatefulness). Of course, this does not appear to be a very general exception to the rule. The problem, as you have said, is that if we try to put conditions on this belief (forall n: Y(n) -> X(n)), then P will only know the *condition* for finitely many instances (or for all instances, if P believes forall n: Y(n)).
					- I want to codify the assumptions under which one-step UDT is equivalent to N-step UDT.
					- That makes sense. If I am comfortable with N-step UDT, it's mainly because I expect these assumptions to be something tantamount to baking in our desired consequence (because the consequence is broken in lots of natural situations). Of the kind "all checks that the optimal policy (according to P) performs can be performed at once (sequential checks, with dependencies, are not better according to P)". Because that property is fundamentally mind-dependent, and we don't know of another name for it. Or, if we turn to the dynamic setting and check against real feedback instead of P's beliefs (so the property becomes "a prior/LI with access to these N meta-levels won't eventually do better than one with a single level"), it's decision-tree-dependent instead of mind-dependent.
					- I am not sure I understand, but perhaps the FIST idea illustrates that this is not the case? IE, FIST shows that a class of cases violating "all checks that the optimal policy performs can be performed at once, rather than sequentially" can be handled by one-step UDT as effectively as n-step UDT would handle them?
					- Specifically, something like distributions over finitely many finite decision trees, *or* trees having a sufficiently "IID" character such that universal beliefs about what decision problem is being faced can apply to every single node. Such properties apparently imply identicality of one-step and multi-step UDT without mention of "all checks can be performed at once", and in particular, the FIST argument illustrated how one-step can perform important checks at some intermediate point between P and the actual decision time.
					- So (barring other ideas, like solving the subjective generalization problem), it looks like the value of the two-step procedure is for more complex infinite trees.
					  Also note that I still expect that under some conditions, one-step UDT will become more updateful rather than dissolve into nonsense. One such condition is that P does not have false universal beliefs held strongly. Suppose, then, that I devote N traders with high starting wealth to vote against the N smallest universal statements. (I use N different traders rather than one so that others remain, if some are knocked out of the market by their cherished anti-belief being proved.) With this, and presumably some other assumptions, perhaps it is possible to get back to the early idea I had about a UDT which acts in a slightly more updateful way as it runs out of opinionated beliefs in P -- although this still only gets finitely many steps of such behavior, obviously, so it's not that great.
					- It would be really nice to have some kind of statement of limited negtive impact from false universal beliefs in P. For exmple, an optimistic dream would be if P eventually sees fit to behave updatefully about such beliefs. After all, if you're quite sure that you are right, what could be the harm *in principle* of being willing to update away from that belief in the face of a counterexample (which you will 'never' see)? If some result like this were true, it might allow one-step UDT to have good properties for infinitely many nodes. (But I'm not actually very optimistic about this.)
				- Martin
				  collapsed:: true
					- > As stated previously, I think we are somewhat on the same page about the following: given (a) correct marginalization for propositional and luv beliefs ("coherence"), (b) self-trust, and (c) correct marginalization of* hypothetical* propositional and luv beliefs, then *in an individual case where P expects a counterfactual mugging, (one-step) UDT will handle the counterfactual mugging as expected* (as classical UDT calculations expect, that is).
					- I confirm I agree with this, provided some smaller caveats of the form "no evil coins in other parts of the tree (that P knows about) prevent this". Also, let me note my understanding is that (c) is the Reflection Principle.
					- > SIST establishes that my one-step UDT solves that sort of problem.
					- SIST solves Counterfactual Mugging (assuming, of course, P knows we're in a Counterfactual Mugging).
					- I claim **SIST *****doesn't***** solve other problems, even when P knows we're in that problem**. (This is our first disagreement on the truth of a technical point.)
					- **An example is Counterfactual Mugging with Math Homework** (you have to state the correct digit of pi when paying up). Here's why:
					- In regular Counterfactual Mugging, "all information is already in P". In particular, P already knows (or better said "we assume it has a good guess about") the probability with which the logical coin turns out true (in your example, you assume P knows the probabilities of Ask(Q_m) and Rec(Q_m)). Given this situation, the right action is taken.
					- But in Counterfactual Mugging with Math Homework, assume P = extrapolate(Q_k) was not advanced enough to know the digit of pi, but that round at which the game is played (Q_m) is indeed advanced enough to actually know the digit of pi. Assume further that P, as above, already knows (or "has a good guess at") the probabilities Ask(Q_m) and Rec(Q_m). Assume these probabilities and the payoff are such that P knows it's better to Pay (by stating the correct digit) in Ask(). This will be witnessed by the fact that E(U | A(Q_m)="If Ask(Q_m), then output CorrectDigit") is high (where the expectation is taken according to P). Here CorrectDigit is a formula defining what it means to "be the actual digit of pi at that position", but P won't have a good guess as to which is the actual correct digit (which digit satisfies the formula CorrectDigit). Without any further mechanism, this will remain the case when we compute the values of E(U | A(Q_m)=Not Pay), E(U | A(Q_m)=(Pay, 0)), E(U | A(Q_m)=(Pay, 1)), etc., where the action corresponds to deciding whether to Pay, and if so also stating a digit. In particular, since P doesn't know which is the correct digit, there won't be one E(U | ... ) that is higher than the rest (attaining full payoff). On the contrary, all of them will have a mediocre payoff, corresponding to "one tenth probability of guessing it correctly". So P clearly "could have known" the correct digit (maybe P even knows explicitly that Q_m knows the correct digit), but doesn't take advantage of that knowledge because *it's just a frozen prior*, and we haven't allowed it any mechanism to update.
					- In fact, this problem (not allowing absolutely any kind of updating) **also affects regular Counterfactual Mugging, **except when we formalize the decision problem in one concrete way (facilitating it for updateless agents).
					- Say we formalize it as follows: no matter what happens (whether Ask(Q_m) or Rec(Q_m)), A will have to decide between Pay and Not Pay. And then, of course, if Receive(Q_m) is the case, this action is completely ignored. In this case (or any equivalent formalization in which "you don't have to distinguish between Ask() and Receive()"), your argument works. P knows that it will be either in Ask() or in Rec(), and knows that in both those cases it can take the same action (because one of them is irrelevant).
					- But say now we formalize it as follows: if Rec(Q_m) is the case, the action is not ignored, and Paying indeed leads tu losing that amount of money (although you possibly also receive the big payoff thanks to your counterfactual). This more naturaly reflects the "freedom of action" of the real world, in which taking a non-sensical action fit for a different situation (like arbitrarily giving $10 bills to people who aren't even asking for them) can result in bad outcomes. In this case, you clearly want to first check whether you're in Ask() or Rec(), and then only Pay if you're in Ask(). But again, we cannot achieve this without updating on something (granted P doesn't already know whether Ask(Q_m) or Rec(Q_m), that is, hasn't already completely decided the logical coin). Your argument does show that P will take all of this into account, and if even with this arbitrary Pay the policy of always Paying is better (because the other payoff is big enough), it will do so. But we are of course losing money senselessly, when we could perfectly fix the policy of updating on whether Ask() or Rec() and deciding whether to Pay accordingly (that is, never paying in Rec(), but still paying in Ask() if the global calculation saw it as optimal).
					- Note all of this applies exactly if we consider some state k<c<m as you do in your email, instead of Q_m itself, that already knows the updated information.
					- (But now that makes less sense to worry about, since you were asking for c<m to ensure the agent could see the Counterfactual Mugging coming "in advance", while here I'm dealing with information that can be exploited just the same by receiving it exactly at time m.)
					- > You take SIST to be very little or no evidence to this effect. You continue to anticipate that if P does not anticipate a specific decision problem, then my one-step UDT will essentially fail on that decision problem, even if the details of the situation become clear in later Q_n and P correctly believes that it should behave updatefully on that information (ie, two-step UDT works).
					- Exactly, and my worry here is: Even if P knows "Q_n will be right" and "Behaving updatefully is better", *how* will it obtain the updated information? The only way would be for it to already have it! SIST only shows that, *once* this information is available, P reasons correctly with it. Let me reason in more detail in the context of your next quote:
					- > Now furthermore suppose that the proposition X(node) itself is one which P thinks it should behave updatefully about, which is to say, it meets the relevant independence assumptions in P, such that SIST implies that the proposition X(node) is one which will be treated in an updateful manner (by single-step UDT). (For emphasis: this does not mean that P knows X(node); rather, P is such that one-step UDT will treat X(node) as true *or as false* depending on what more-updated opinions say).
					- I think this is not the case. (This is our second disagreement on the truth of a technical point.)
					- Maybe there's a confusion going on as to what "one-step UDT" means.
					- If by "one-step UDT" you mean something like "first we check which independence relations P believes to hold, and then, when the decision node comes, we update P on the information it believes it's safe to be updateful about (by adding it into the conditional)", then indeed updating works as you say. This is just "my thing" implemented with your definition of "it's safe to update on this fact".
					- If instead you mean "we just compute E(U | A(Q)=a) as usual, without any additional mechanism (for example, adding anything on the conditional which is not just A(Q)=a)", then I claim your quoted argument doesn't work. (And I do think this is the version you have in mind.)
					- The SIST argument shows that P reasons correctly when conditioned on different things. That is, provided the information (for example, Ask(Q) & A(Q)=Pay), it yields the desired beliefs about U. I don't see how it shows that P *attains* the right probabilities on these different conditionals (for example, being in a Counterfactual Mugging), when conditioned *just on sentences of the form* A(Q)=a.
					- And again, the "conceptual" reason why all of these "technical caveats" hold is that "if P doesn't have a belief already, the only way for it to obtain it is by adding stuff to the conditional, otherwise it will not appear magically (unless it is a consequence of A(Q)=a, the base conditional, but in the above cases this is not the case since uncertainty remains about what future we will inhabit)". That is, "everything is updating (including thinking about whether this node has this or that syntactic structure), and someone somewhere has to decide to perform that update (if the knowledge wasn't already present in P)".
					- > The general hope of this remark is to argue that SIST implies some degree of "correctly reasoning about branches" which has some positive impact on decision problems which are not already fully encoded in P. I do not claim that this argument gives us everything we might possibly want in this respect.
					- I do share the opinion that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems". That's why, even when P thinks that node has probability one third of being a Counterfactual Mugging, one third Parfit's Hitchhiker, one third something different, it will "correctly" (from its subjective perspective) assess between its available options, and maybe act as if playing the Counterfactual Mugging (or the Parfit's Hitchhiker) because it has high enough payoff, thus giving up on the worlds where it turns out to not be a Counterfactual Mugging. What I'm saying is: we can do this, but when the agent thinks it'd be better off updating (it satisfies independence), it is clearly sub-optimal to keep this course of thought and action, as opposed to deciding to update on whether node is a Counterfactual Mugging. So let's implement that instead.
					- > I hope it is clear that I am not denying this. An arbitrary P can think that the world has some arbitrary acausal considerations, which will result in some arbitrary behavior.
					- To clarify, what I'm trying to argue is "even if P has all the correct beliefs to understand this decision problem (but is not omniscient), then it will *not be able to* act optimally (even if it thinks that'd score higher) unless we give it a mechanism to ad hoc update".
					- It's true that an arbitrarily dumb P will act wrong both here, and in my proposal. That's not what I'm arguing.
					- > Hope it's clear that I meant neither of these things; rather, X(node) should be known by some intermediate Q_c.
					- I also want to make explicit that I think my technical caveats (the ones I'm expliciting here, and that I was referencing on the previous email too) don't depend at all on whether we take some intermediate Q_c, or the latest possible Q_m.
					- ================
					- > But I'm still not seeing how a two-step independence-based UDT could achieve this sort of updatefulness about infinitely many sentences. So (1) and (2) still don't appear orthogonal to me.
					- (I'm less sure about the following, and will try to write the proposal completely and formally before tomorrow, which will probably help us.)
					- It's true when doing "my thing" (explicitly deciding what to update on) with "your definition" (independence) we no longer have "a single quantified sentence we can condition on". But nonetheless we can implement it by checking one by one what P believes about the correlations between particular nodes.
					- Instead of checking for E(U | sigma) at the start and being done with it, just check at each decision node / level of the tree whether P believes that the independence properties hold (and we check this by reading some conditionals of P). For example, even for very far-off nodes n, n' we will have certain values for P(n=Ask | A(n')=a_1) and P(n=Ask | A(n')=a_2), which witness whether the nature of the node n is independent from actions taken in n'. It's true that for very far-off nodes Q_k (the finite seed for P) will never have thought about the numbers n, n', so the numbers P has on them will have been determined completely through Universal Instantiation, based on some general beliefs. And these might be of a lower accuracy that beliefs about simple things. That's partly why I feel like we need to "decide what to update on instrumentally at the beginning, based on consequences": maybe in many instances P would rather think longer about whether n and n' have this or that structure, and only then assess independence. But the point stands that this is a coherent proposal (even if I prefer mine).
					- More generally, I continue feeling like "my definition" (checking expected U) is superior to "your definition" (independence) because with yours we are already baking in more knowledge than we'd probably rather Q discover by itself naturally. We are imposing that "it is good to update exactly when this is the case". And I'm like, "no, let's let Q decide when it's good to update". This will play off particularly well in situations with Eventual Learning (like Policy Selection).
					- > The SIST argument can handle the case where *every* decision node is (believed to be) a counterfactual mugging
					- You are completely right, but of course I wanted something more general, and I think we need my kind of "deciding what to update on" for that.
					- I sadly have to leave now, but soon I'll answer the last part of your email ("I am not sure I understand, but...").
					- Thank you so much again for all of your thoughts!
					- P.S: This is the 100th email in this thread. Wooohoooo! :-D
				- The author
				  collapsed:: true
					- This of course deserves an extensive response, but I'll try and focus on brief responses for now, for a quick easy to read email:
					- Also, let me note my understanding is that (c) is the Reflection Principle.
					- I don't understand what you mean by this. In my current understanding, (c) is something like: for expressions of the form `proposition`, where Q is as usual a big explicit market state, and `prop` represents marginalizing Q in the given proposition, P already knows the correct value of those expressions (with some epsilon uncertainty added, perhaps). Is this "the reflection principle"? Perhaps you meant to say (b) is the reflection principle, instead? (Daniel Hermann called (b) Reflection, iirc)
					- SIST solves Counterfactual Mugging (assuming, of course, P knows we're in a Counterfactual Mugging).
					- I claim **SIST *****doesn't***** solve other problems, even when P knows we're in that problem**. (This is our first disagreement on the truth of a technical point.)
					- **An example is Counterfactual Mugging with Math Homework** (you have to state the correct digit of pi when paying up). Here's why:
					- Ah, a very surprising claim! I'll have to dig into your argument. It seems evident to me at the moment that my argument wrt Counterfactual Mugging generalizes to "all the problems UDT is typically understood to solve", but of course I have not formalized that or provided any explicit argument for it. (FIST is supposed to be further evidence to this effect, though.)
					- > You take SIST to be very little or no evidence to this effect. You continue to anticipate that if P does not anticipate a specific decision problem, then my one-step UDT will essentially fail on that decision problem, even if the details of the situation become clear in later Q_n and P correctly believes that it should behave updatefully on that information (ie, two-step UDT works).
					- Exactly, and my worry here is: Even if P knows "Q_n will be right" and "Behaving updatefully is better", *how* will it obtain the updated information? The only way would be for it to already have it! SIST only shows that, *once* this information is available, P reasons correctly with it.
					- This makes complete sense to me *with respect to infinite trees* (beyond the fairly trivial ones SIST can already get, like where you face a counterfactual mugging at every node). I currently see the difficulty of going from something like \forall n: X(n) to something like \forall n: Y(n) -> X(n) (because P does not know Y(n)). I currently do not see the difficulty for finite cases (but I need to go over your email in more detail!)
					- Let me reason in more detail in the context of your next quote:
					- [...] SIST implies that the proposition X(node) is one which will be treated in an updateful manner [...]
					- I think this is not the case. (This is our second disagreement on the truth of a technical point.)
					- Again, a very surprising claim! (IE I'm surprised that you think this *after* reading my clarified argument)
					-
					- Maybe there's a confusion going on as to what "one-step UDT" means.
					- [...]
					- If instead you mean "we just compute E(U | A(Q)=a) as usual,
					- Affirming that I use "one-step UDT" to mean *just* argmaxing E(U|A(Q)=a). No *extra* step is needed to account for (the independence version of) what P thinks it should behave updatefully about, because (the[point of the independence version](https://www.lesswrong.com/posts/W6nXfmKTrgaiaLSRg/why-and-why-not-bayesian-updating) is) UDT over P just already acts like that.
					- I do share the opinion that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems".
					- I'll have to think about how you can believe this while disagreeing with my other claims.
					-
					- It's true when doing "my thing" (explicitly deciding what to update on) with "your definition" (independence) we no longer have "a single quantified sentence we can condition on". But nonetheless we can implement it by checking one by one what P believes about the correlations between particular nodes. [...]  It's true that for very far-off nodes Q_k (the finite seed for P) will never have thought about the numbers n, n', so the numbers P has on them will have been determined completely through Universal Instantiation, based on some general beliefs.
					- Hmm. So basically, iiuc, you are pointing out that P may indeed have the required independence assumptions for infinitely many sentences, although these opinions may not be very good. Yeah, seems plausible. Although I would be happier with a more detailed picture.
					- It's true that for very far-off nodes Q_k (the finite seed for P) will never have thought about the numbers n, n', so the numbers P has on them will have been determined completely through Universal Instantiation, based on some general beliefs. And these might be of a lower accuracy that beliefs about simple things. That's partly why I feel like we need to "decide what to update on instrumentally at the beginning, based on consequences": maybe in many instances P would rather think longer about whether n and n' have this or that structure, and only then assess independence. But the point stands that this is a coherent proposal (even if I prefer mine).
					- I want to flag that this feels like a *less important disagreement*, but we're pretty far down the rabbit hole right now, and it feels like we just have a ton of detailed disagreements ... so anyway, flagging that the above does not quite make sense to me, as a distinction between the two theories (independence-based two-step and EV-based two-step). The expected value version has to entertain an arbitrarily limited number of hypotheses about which algorithm to use to decide which sentences to be updateful on, because (a) we want the argmax to be a terminating computation; (b) P will only have "good" opinions about some bounded number of such algorithms, so if we argmax over too many options, we stand a good chance of getting a bad result (much like algorithmic-policy selection). So both two-step theories have a "large-sentence opinions are bad" problem.
					- More generally, I continue feeling like "my definition" (checking expected U) is superior to "your definition" (independence) because with yours we are already baking in more knowledge than we'd probably rather Q discover by itself naturally. We are imposing that "it is good to update exactly when this is the case". And I'm like, "no, let's let Q decide when it's good to update". This will play off particularly well in situations with Eventual Learning (like Policy Selection).
					- The expected-utility version is of course a more obvious translation of "UDT thinks it would be good to update". I agree that it is superior. So why focus on the independence version? Because this is the version which is most directly tied to[the math of when UDT behaves updatefully](https://www.lesswrong.com/posts/W6nXfmKTrgaiaLSRg/why-and-why-not-bayesian-updating). IE, it is *supposed* to be the version which *has the most hope* of equivalence between two-step and one-step (but of course this is what we are debating). So basically, I am trying to work my way up to a tiling theorem in baby steps. If I got something working for the independence version, then a next step could be to find the assumptions under which the two notions of happy-to-update are equivalent.
					  Conceptually, two-step UDT is like policy selection in the sense that it makes direct modifications to its (final-step) decision procedure. I could get behind this in the end if it turned out to be the simplest way of achieving a tiling theorem. Maybe the best way to achieve reflective coherence is to pre-emptively make (a specific class of) self-modifications. But you do not even expect this -- you expect three-step, four step, etc to all be different (and in some sense further improvements). In my view, this leaves us afloat in decision-theory space, with no special notion of rationality.
					  My primary aim with decision theory work is to specify a decision rule which tiles -- something such that (under some assumptions, of course) it is already equivalent to any self-modifications it would approve of.
					- Of course, proving this goal to be impossible is of equal interest, and a major goal with the summer project was always to find the impossibility theorems where they exist.
				- Martin
				  collapsed:: true
					- Quick thoughts to help you probe my opinions.
					- Meta-point: I think the most efficient step now would be to try and completely flesh out technical disagreements one and two (but especially one) on a whiteboard, either running through my argument and trying to see where you disagree, or the other way around. I suspect we might be disagreeing in some small implicit assumption that decides whether the argument goes through.
					- I don't understand what you mean by this. In my current understanding, (c) is something like: for expressions of the form `proposition`, where Q is as usual a big explicit market state, and `prop` represents marginalizing Q in the given proposition, P already knows the correct value of those expressions (with some epsilon uncertainty added, perhaps). Is this "the reflection principle"? Perhaps you meant to say (b) is the reflection principle, instead? (Daniel Hermann called (b) Reflection, iirc)
					-
					- Thank you for your clarification on (c). You are right that it is not exactly the Reflection Principle. In fact, (b) + (c) yield the Reflection Principle.
					- Ah, a very surprising claim! I'll have to dig into your argument. It seems evident to me at the moment that my argument wrt Counterfactual Mugging generalizes to "all the problems UDT is typically understood to solve", but of course I have not formalized that or provided any explicit argument for it. (FIST is supposed to be further evidence to this effect, though.)
					- Just to express my opinion in different words: I think you're hiding under the rug some crucial small facts we need to update on, to ensure the desired updateful behavior, since they are not already present in P (and any "breaking up the situation into different worlds/conditionals" that might extract that knowledge amounts to already having the knowledge). From my perspective, you are examining the bells and whistles of an alleged perpetual motion machine. (Of course, it'd be better if I had managed to prove impossibility, while for now I'm just communicating technical points.)
					- This makes complete sense to me *with respect to infinite trees* (beyond the fairly trivial ones SIST can already get, like where you face a counterfactual mugging at every node). I currently see the difficulty of going from something like \forall n: X(n) to something like \forall n: Y(n) -> X(n) (because P does not know Y(n)). I currently do not see the difficulty for finite cases (but I need to go over your email in more detail!)
					- Well, my argument is of the shape "if P doesn't already have that information within itself, we'll have to update on it to use it, no alternative exists". And I think this can apply both to infinite and finite trees, unless P already knows everything there is to know about the finite tree, but this will usually not be the case (or not be the optimal Q_k to use, since it'd be too updated).
					- > I do share the opinion that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems".
					- I'll have to think about how you can believe this while disagreeing with my other claims.
					- To be clear, I was saying something fairly basic, like the following:
					- Obviously P doesn't compartmentalize its reasoning artificially into small decision problems (it just thinks about the whole tree), so the nice properties of thinking about the possible future branches (with P's uncertainty) and assessing what's best are also used "between decision trees", for example when P is unsure about which decision problem it finds in a node. But at the same time, I challenge the further claim that, through some circuitous chain of reasoning, P can act updatefully about a fact it doesn't actually know (when still only being conditioned on A(Q)=a, and nothing else). For example, the claim that even if P is unsure about whether the next node is a Counterfactual Mugging or Parfit's Hitchhiker, if the next inductor state knows it (and P thinks it's safe to update on it), then E(U | A(Q)=a) will automatically represent this knowledge obtained from the next inductor state.
					- flagging that the above does not quite make sense to me, as a distinction between the two theories (independence-based two-step and EV-based two-step). The expected value version has to entertain an arbitrarily limited number of hypotheses about which algorithm to use to decide which sentences to be updateful on, because (a) we want the argmax to be a terminating computation; (b) P will only have "good" opinions about some bounded number of such algorithms, so if we argmax over too many options, we stand a good chance of getting a bad result (much like algorithmic-policy selection). So both two-step theories have a "large-sentence opinions are bad" problem.
					- You are completely right, thank you for pointing that out! Thus my vague intuitive argument for the superiority of "EV-based two-step" actually suffers the same limitation, and so my reasons for choosing EV-based over independence-based have limited to just "we intuitively want to ask the agent what it thinks, instead of doing that work for it".
					- Although I understand your later point about using independence-based to get tiling through baby steps. I think this won't work because we'll somewhere have to "choose what to update on", and whenever the prior is such that it actually updates, tiling is not guaranteed (except under some very tight constraints of the form "updating didn't make that big a difference after all").
					- I also note another kind of argument to decide between independence-based and EV-based: in the case where we get Eventual Learning, maybe through periodically re-freezing the prior, or through ever-increasing the N-meta levels of policy selection, one of the two definitions might present better behavior. But actually I suspect both will converge on the right things.
					- I could get behind this in the end if it turned out to be the simplest way of achieving a tiling theorem.
					- To be clear (and similar to what I just mentioned), I don't expect these Policy Selection-like shoe-hornings of learning into our UDT to tile, except under some very tight constraints which amount to "updating wasn't so important after all". I for now feel like, in a dynamic learning-theoretic setting like ours, there's a fundamental trade-off between the Dynamic stability of strategic updatelessness and the Eventual learning we can find in Policy Selection. (In fact I shortly mentioned this in[my talk](https://www.youtube.com/watch?v=uNv1Cq-aVKY&t=810s&ab_channel=PIBBSSFellowship).)
					- Thank you again, this is all very exciting! We're closing in on stuff!
				- The author
					- [scrubbed] I'm writing this to organize some thoughts about your argument, but I might as well send it.
					- Adaptation of the ((65392abe-0974-4591-b379-7ae788d649c1)) argument to `counterlogical mugging with homework`:
					  id:: 65413c7c-dd38-401b-b124-3bc275911885
					  collapsed:: true
						- In regular Counterfactual Mugging, "all information is already in P". In particular, P already knows (or better said "we assume it has a good guess about") the probability with which the logical coin turns out true (in your example, you assume P knows the probabilities of Ask(Q_m) and Rec(Q_m)). Given this situation, the right action is taken.
						- But in Counterfactual Mugging with Math Homework, assume P = extrapolate(Q_k) was not advanced enough to know the digit of pi, but that round at which the game is played (Q_m) is indeed advanced enough to actually know the digit of pi. Assume further that P, as above, already knows (or "has a good guess at") the probabilities Ask(Q_m) and Rec(Q_m). Assume these probabilities and the payoff are such that P knows it's better to Pay (by stating the correct digit) in Ask(). This will be witnessed by the fact that E(U | A(Q_m)="If Ask(Q_m), then output CorrectDigit") is high (where the expectation is taken according to P). Here CorrectDigit is a formula defining what it means to "be the actual digit of pi at that position", but P won't have a good guess as to which is the actual correct digit (which digit satisfies the formula CorrectDigit). Without any further mechanism, this will remain the case when we compute the values of E(U | A(Q_m)=Not Pay), E(U | A(Q_m)=(Pay, 0)), E(U | A(Q_m)=(Pay, 1)), etc., where the action corresponds to deciding whether to Pay, and if so also stating a digit. In particular, since P doesn't know which is the correct digit, there won't be one E(U | ... ) that is higher than the rest (attaining full payoff). On the contrary, all of them will have a mediocre payoff, corresponding to "one tenth probability of guessing it correctly". So P clearly "could have known" the correct digit (maybe P even knows explicitly that Q_m knows the correct digit), but doesn't take advantage of that knowledge because *it's just a frozen prior*, and we haven't allowed it any mechanism to update.
						- I'm not really seeing any argument/analysis here to conclude that this is what one-step UDT does, other than the classic "UDT doesn't update, so it won't act updateful" error.
						- So let me run thru my argument as to why it does the right thing here.
						- We assume it knows that it is in cf-mugging-with-homework. To spell that out a bit more, we assume that rather than yes or no, Omega takes the $10 in the case that we utter the digit of pi in question. (Not sure if this is exactly the version you had in mind.) Let's say even-numbered branches get asked for $10 (and must utter the digit to agree), while odd-numbered branches are receivers. (Maybe for digit 5 Omega checks whether the agent would give up $10 on 4, etc, pairing everything off.)
						- Recall that (my argument for) regular cf mugging used two branch predicates, Ask and Rec, obeying the following:
						- -
						- Branches Q such that Rec(Q) believe that Ask(Q') implies A(Q')=give -> U=100, and A(Q')=refuse->U=0.
						- -
						- Branches Q such that Ask(Q) believe that Ask(Q') implies A(Q')=give -> -10, and A(Q')=refuse -> U=0.
						- Instead, we now add a branch for each numeral the digit of pi could be, with appropriate payoffs. By the "///////" style argument, all of these branch payoffs are correctly evaluated for each policy-point we can consider.
						- So for example, suppose that the true Q_m knows that the relevant digit of pi is 4. When we condition P on the policy point which says 4 upon seeing that Q_m; ie, we look at E_{P}(U | A(Q_m)=4).
						- As in the "/////" argument, we decompose the expectation into a sum over the different possible branches. A(Q_m)=4 will look like a -10 decision to 4-branches (again I am pretending that it is reasonable to assume that decisions are 100% correlated across similar branches, which I don't actually think is a reasonable assumption, but it makes the math a lot simpler), but it will look like a +100 decision for all 5-branches. No other significantly-probable sort of branch will have significant opinions. So the strategy will look good.
						- In fact, this problem (not allowing absolutely any kind of updating) **also affects regular Counterfactual Mugging, **except when we formalize the decision problem in one concrete way (facilitating it for updateless agents).
						- Say we formalize it as follows: no matter what happens (whether Ask(Q_m) or Rec(Q_m)), A will have to decide between Pay and Not Pay. And then, of course, if Receive(Q_m) is the case, this action is completely ignored. In this case (or any equivalent formalization in which "you don't have to distinguish between Ask() and Receive()"), your argument works. P knows that it will be either in Ask() or in Rec(), and knows that in both those cases it can take the same action (because one of them is irrelevant).
						- But say now we formalize it as follows: if Rec(Q_m) is the case, the action is not ignored, and Paying indeed leads tu losing that amount of money (although you possibly also receive the big payoff thanks to your counterfactual). This more naturaly reflects the "freedom of action" of the real world, in which taking a non-sensical action fit for a different situation (like arbitrarily giving $10 bills to people who aren't even asking for them) can result in bad outcomes. In this case, you clearly want to first check whether you're in Ask() or Rec(), and then only Pay if you're in Ask(). But again, we cannot achieve this without updating on something (granted P doesn't already know whether Ask(Q_m) or Rec(Q_m), that is, hasn't already completely decided the logical coin).
						- So the idea is again to decompose the expected value into different sorts of branches. Here, Ask and Rec are still adequate, but the Rec branches now care about two different sorts of policy points rather than one:
						- -
						- Branches Q such that Rec(Q) believe that Ask(Q') implies A(Q')=give -> +100, and A(Q')=refuse-> 0. They also believe that Rec(Q') implies that A(Q')=give -> -10, and A(Q')=refuse -> 0.
						- -
						- Branches Q such that Ask(Q) believe that Ask(Q') implies A(Q')=give -> -10, and A(Q')=refuse -> U=0.
						- Note the "+100", "-10" notation instead of U=100; this is because, eg, receiving 100 and giving up 10 make for a total utility of 90, but I didn't want to write all of those combinations out. (So the real logical beliefs involve conjunctions of policy points implying utilities.)
						  The analysis here becomes more complex, because now we have to account for joint beliefs -- we're conditioning on one policy point at a time, but the evaluation of exact utility requires knowing multiple policy points, so the expectation will involve some uncertainty about policy points not currently conditioned on.
						- If P believes that give/refuse in Rec branches vs Ask branches are 100% correlated (so refusing in Rec branches means refusing in Ask branches), then your analysis is exactly correct. But if P sees these as independent, then UDT will do the right thing here, instead: give up $10 in Ask branches and not in Rec branches.
						-
						- I do share the opinion that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems".
						- I'll have to think about how you can believe this while disagreeing with my other claims.
						- To be clear, I was saying something fairly basic, like the following:
						- Obviously P doesn't compartmentalize its reasoning artificially into small decision problems (it just thinks about the whole tree), so the nice properties of thinking about the possible future branches (with P's uncertainty) and assessing what's best are also used "between decision trees", for example when P is unsure about which decision problem it finds in a node. But at the same time, I challenge the further claim that, through some circuitous chain of reasoning, P can act updatefully about a fact it doesn't actually know (when still only being conditioned on A(Q)=a, and nothing else). For example, the claim that even if P is unsure about whether the next node is a Counterfactual Mugging or Parfit's Hitchhiker, if the next inductor state knows it (and P thinks it's safe to update on it), then E(U | A(Q)=a) will automatically represent this knowledge obtained from the next inductor state.
						- I get what you are saying here now that I understand how you think the SIST argument implied optimal updateless behavior (eg, getting cf mugging right) but not optimal updateful behavior (eg, cf mugging with homework). However, I still think you should buy the implication you're denying here. Optimal updateless behavior is a generalization of optimal updateful behavior, so while getting cf mugging right doesn't logically imply getting updateful stuff right as well, getting cf mugging right *for the same reason why classical UDT gets it right* should highly suggest solving cases which require updating.
						  I claim that classical UDT (no logical uncertainty) achieves the optimal policy for any single player game tree (with Omega controlling some variables in any way it wants based on the policy chosen by UDT), if it sees them coming -- ie its prior is just the game it is in. (With of course the necessary caveats to rule out self-coordination problems if we are talking about UDT 1.0.)
						- I then claim that one-step logically uncertain UDT (conditioning on policy points of the form A(Q)=a) has the same property, again if it sees those trees coming, because it evaluates those problems in exactly the same way, just with extra steps to account for how all this reasoning can happen in a computationally bounded system. This is the idea of the argument marked "/////".
						- This implies that one-step LU UDT has the same property as classical UDT, of behaving updatefully when it is optimal to do so.
						- So if you buy the claim that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems", then it seems to me you should buy the claim that a P which is uncertain of which of several decision problems it will face, but which will be able to observe/calculate this in the next market state, and understands this to be the case, will not only see the advantages of being able to behave updatefully, but will furthermore approve of those updateful behaviors in its policy-point evaluations.
						- I see why this conclusion does not follow from your current perspective, but it seems to me like this perspective misses the "correct updateless behavior is a generalization of correct updateful behavior" point. I would be curious to know what you think of your argument for the "classic UDT" case. Do you claim that empirically updateless UDT fails the empirical "cf mugging with homework"? If not, where does your argument for failure depend on logical uncertainty rather than empirical uncertainty?
				- Martin subsequently agrees with the argument.
			- Understand his attempted statement of an impossibility result.
				- What did he mean when he said that the action-only version yields no problems?
				-
			- Consider variations of the "learning UDT" hope that was dashed.
				- Does "eventually update" combined with LIC give us a plausible open-minded UDT?
				- Versions where there's a speed-of-update consideration?
					- Impossibility results around "no slowest speed"??
			- Consider variations of impossibility idea.
				- Understand learning vs stubbornness. `learning vs teaching`
					- In single-agent decision problems, it in-some-sense seems plausible that "the more updateless you are, the better off you are", even if there's also a conflicting intuition that you "should learn" in the long run.
						- Well, actually, now that I've written that out, it seems much less straightforward.
						- _In some sense_ it seems (subjectively) best to be totally updateless.
							- IE, _in some sense_, even if we assent to *behave* updatefully, we (subjectively) should do so as a consequence of updateless planning.
						- But _in some other sense_ it seems better to update somewhat.
							- IE, from a more objective perspective, it seems quite bad if the prior is just totally wrong, and then fails to update to the situation despite adequate evidence.
						- Given an asymptotic perspective, it seems like _in some third sense_ it is best to update, but as slowly as possible.
							- This can be illustrated with policy selection: we need to expand the list of policies, and think longer to evaluate the policies well; but asymptotically speaking, we do best if we do those things more slowly.
								- Formal version of this observation?
								- Do I think we "can beat" this in some sense, or do I agree with the notion that there's a fundamental trade-off here, even for versions of UDT which are not, apparently, policy selection?
						- Given that we want good performance at finite time, however, this is obviously an impractical observation.
					- However, in multi-agent scenarios, it seems as if there's a more straightforward trade-off between learning and stubbornness.
						- Well, actually isn't it the same picture?
							- Increasingly stubborn agents do at least as well or better in the long term, but potentially much worse in the short term.
							- Totally stubborn agents, however, can just be terrible forever.
				- Consider status of "evolutionary" arguments for updatefulness.
					-
			- Analyze my infinite muggings on the same coin problem more thoroughly.
				- Different problem scenarios?
				- What's the point?
				- What can or can't we accomplish?
			- List all "reasons for pessimism" / "negative result" / "potential negative results":
				-
		- Think about ***agent-environment boundaries*** and what Omega can "fairly" depend on about our policy.
			- The idea of UDT is to depend on the full policy, but thinking about logical uncertainty reveals this as a subjective counterfactual.
			- Soto argued that so long as we think of argmaxing the agent we put into the decision problem, we are actually slipping in an assumption of logical omniscience.
			- Omega/nature nodes which depend on internals of our agent's computation are "evil" -- but can we really rule them out?
				- What problems do such things create for us?
				- What technical means might we use to overcome such problems?
			- How do we want to represent decision problems?
			- How do we want to represent sequential/treeform decision problems?
			- How do we want to split up info between the observation and the prior?
			- How do we want to represent U?
				- Some thoughts from Soto:
				  collapsed:: true
					- We maximize E(U | A(q)=a), but what is U? (In a possibly infinite tree)
					  Consider this answer:
					  When judging an A(q)=a where q is a possible belief state of round n, we
					   maximize U_{>n} := U_1 + ... + U_n + d·U_{n+1} + d^2·U_{n+2} + ..., 
					  where d is the time-penalty. That is, the time-penalty starts after n.
					  This reintroduces some dynamic instability (although we can limit d to 1). And still gets swamped by infinities if some future rewards grow fast enough! (maybe we could add the assumption
					   that this doesn't happen in our tree, AND force our reasoner to be 
					  certain of that. Or maybe I want d to be dynamically chosen?)
					  Something
					   like "maximizing U_{>0} always" gets rid of dynamic instability, but
					   trades one penny today for infinite bankruptcy later (this would also 
					  happen with the above if the agent could commit at t=0, but we have the catastrophe-free assumption).
					  Something
					   like "maximizing the limit of the average utility obtained per round" 
					  feels good, but still has the problem of getting swamped by infinities 
					  (in fact, it gets swamped more easily).
			- It could be helpful to think in some detail about how I want to encode _specific_ decision problems.
			  collapsed:: true
				- Thoughts on Counterlogical Mugging:
					- Whatever the complexity class for our logical coins, we
					  need to ensure that Omega is using a logical inductor which is too slow
					  to compute it, and the agent is using a logical inductor which is fast 
					  enough.
					- (In some sense we want Omega to be using something too slow to make too-good guesses, also, like we discussed with approximate primality tests. But maybe this isn't so important? Mainly we just want to guarantee that Omega doesn't achieve certainty.)
					- 1. Omega predicts the agent by looking at conditional probabilities: if the coin is heads, will the agent pay me $10?
					- 2. Only after this does Omega use an external computer to compute the logical coin.
					- 3. If the coin is heads, Omega asks the agent for $10.
					- 4. If the coin is tails, Omega pays the agent $1K times the probability that Omega estimated in the first step.
					- Omega's
					  predictions aren't guaranteed to be "correct on an individual round" 
					  (it's unclear what that even should mean, of course); but if the agent 
					  tried to cleverly turn down real requests (since these have only 
					  hypothetical payout) and say yes to counterfactual requests (since these
					  have real payout), then Omega would definitely catch on and stop giving
					  out rewards to this agent. On the other hand, an agent who always gives
					  up the $10 when the coin is heads, will get rewards which converge to 
					  1K for every tails.
					- So it's very much as if "omega knows what you would have done in the other world".
					- However, it does seem like perhaps this way of imagining Omega taking counterfactuals has a problem: it tempts us into thinking about UDT-like behavior due to `shadow of the future` type arguments, rather than classical UDT-style reasoning.
						- Classical UDT may, in fact, see Omega's reasoning as not very correlated with individual policy choices!
					- [insert thoughts on correct solutions to counterlogical mugging, from myself and diff]
						-
		- Understand the 'instrumentality' stuff better.
			- Understand what important role Soto sees instrumentality as playing in our arguments.
				- UDT tiling arguments?
				- LI rewrite to UDT arguments?
				- Other arguments?
			- Understand Soto's instrumental construction inspired by distributed oracles.
			- I still intuitively want to derive instrumentality from other assumptions, such as agent-environment boundary assumptions.
				- What agent-environment boundary assumptions might we make?
				-
		- I should also probably write down some of my thoughts about the overall decision problem framework.
			- EG, game trees vs sequences of problems, unbounded vs bounded reward, unbounded vs bounded utility.
				- Trees vs Alternatives
				  collapsed:: true
					- email about this:
						- Martin also had a similar thought here. [scrubbed]
						- Vanessa's critique was that the trees sort of give up the interesting part of the
						  problem, because the agent's decisions are (at least apparently) 
						  already localized to specific nodes, while other nodes serve as 
						  nature/omega. One of the interesting problems of decision theory in an 
						  embedded/logical/mathematical context is for the agent to figure this 
						  out.
						- I don't think this is completely true, because obviously we want the agent to notice when omega/nature depends on the agent's decisions -- we're not trying to pretend that the decision nodes encapsulate all of the impact of the agent's decisions. But this does raise the question of why we are representing things this way, if the agent can also be "inside" Omega. At best it obscures the fact that we *are* trying to deal with embedded decision theory. 
						  And I do think, looking back, this has caused some confusion for Martin 
						  and I thinking about problems.
						- So Martin mentioned the possibility of getting rid of the tree representation, and just representing decision problems as computer programs, similar to 
						  what Caspar's BRIA does. I think this might be the right way to go.
						- There are some subtleties to think about.
						- Although it would be nice to somehow completely do away with well-defined "actions" and define a "decision problem" *only as a computation which somehow outputs a utility* (with no inputs -- so the agent must do all the work of locating "itself" within the computation), this seems unworkable at this stage -- the more sensible representation would (again, like BRIA) still 
						  explicitly ask the agent to choose an output out of several 
						  possibilities. So the apparent type signature of a decision problem 
						  might be [action -> utility]. But this is still somewhat misleading, 
						  because of course the action chosen in one decision problem might have 
						  an important impact on the utility of a *different* problem -- as Scott put it long ago, there are [purely functional side-effects](https://www.lesswrong.com/posts/WjXYsSqdwTY9sJ5mP/functional-side-effects).
						- This seems like an importantly misleading consequence of this 
						  representation, and I am very much open to other suggestions. Perhaps it
						  is misleading to make apparent attachments of actions to decision 
						  problems whatsoever, and instead we should distinguish between 
						  "decisions" (of type Act) and "problems" (of type Utility), letting *all*
						  of the dependence of U on A be represented as functional side-effects 
						  (either embedding the 'decision' output inside the 'problem' 
						  specification as code, or, correlating with it by other means).
						- In any case, a tree would then get represented as many different decision 
						  problems, linked together only implicitly by the (side-effect-like) 
						  influences they have on each other. Each "decision problem" would have 
						  the same end utility, but the actions would be different (which is to 
						  say, the actions chosen at each node have their own particular way of 
						  influencing the end utility, even though the end utility is 
						  mathematically equivalent in each decision problem which makes up the 
						  tree).
						- Martin's tree format represents a sequential decision problem in an encapsulated way, so that we can definitively say that a collection of decision nodes all belong to a single tree. This could be useful for thinking about "good" asymptotic behavior in infinite trees, for example. But it also seems significant 
						  for finite trees.
						- For example, Martin's tree format represents a counterfactual mugging via three nodes: first Nature (in the form of a pseudorandom computation) decides between two branches; then in one of those branches, we're asked to give up $10, while in the other branch, we may receive $100.
						- In the new non-tree representation, *those two branches are no longer linked by their inclusion in a single tree*. Instead, if we want to say "the agent thinks it is facing a counterfactual mugging", it would be *the prior itself* which assigns significant probability to those two branches (and insignificant probability to everything else).
						- This makes sense: the tree-based representation is somewhat "redundant" in having *both* a prior *and* a tree-based representation of the problem, since to some extent the tree representation specifies our prior. (For example, in the case of counterfactual mugging, the tree says "you will face one of these two 
						  branches and nothing else"; but the agent's prior is what gives a 
						  probability to the logical coin.) Moving away from the tree 
						  representation eliminates this redundancy and instead requires 
						  everything to be specified within the prior.
						- However, this does make some things confusing. The trees represented "objective" information about what kind of decision problem is faced. Moving more things to the prior makes it suddenly feel much more "subjective".
						- But I think this is the right decision.
						- Anyway, I had a lot more points written down from the conversation with Vanessa (like 11 more points!), but I observe that this email is already fairly
						  long, and there are still a lot of ideas to explore about this single 
						  point, without throwing anything else in. So I'll cut off my discussion 
						  here, and await thoughts on this question from the two of you.
				- I argued at some point in favor of bounded utility without assuming reward.
					- Reward makes preference a feature of the environment, rather than a feature of the agent. (Or at least, it tries to.)
						- Well, agent vs environment isn't the true distinction -- there's no such distinction.
						- The real distinction is more like: does the setup take the utility function (or the process delivering rewards) as a given, and define optimality wrt that, or does the setup characterize the space of rationally permissible preferences?
					- We can instead think of utility as a LUV, without assuming anything else about it. (So it could be a constant term with no explicit constraints; or it could be a fully computable expression; or whatever else.)
			- Other thoughts on the agent-environment boundary?
				- Taking the design perspective? IE, distinguishing both an agent-env boundary and an engineer-env boundary, where the engineer interacts w the environment via the agent.
					- Need to be careful not to implicitly assume that the engineer is logically omniscient, which we are at risk of doing given some ways of trying to argue that an agent design has max expected utility (taking expectation calculations for granted).
					- Engineer can't just be assumed to have a prior which we want to maximize wrt, because this trivializes the setup, it just reduces to subjective optimality wrt an agent's beliefs. Engineer wants more sophisticated guarantees. For example, the engineer might want frequentist-inspired guarantees, which provide some assurance that the agent will asymptotically learn to adapt to its environment, rather than just behaving in a subjectively optimal way.
						- If we could spell out the problem wrt realistic types of value uncertainty for the engineer, we would have made quite significant progress on the alignment problem!
				- Thoughts on (not) allowing time travel paradoxes.
					- If we generally say "Omega can correctly predict our policy-points", we can quickly get into paradoxes.
					- For example, if Omega shows us a red or blue ticket, and then asks us which color we would have wanted it to be (retroactively abiding by our decision) -- we can diagonalize, always asking Omega to have shown us a different color than Omega in fact chose.
					- Is this a problem?
						- Can we say that if an agent is incompatible with a specific decision problem (makes that decision problem inconsistent), we don't have to worry about that decision problem for that agent?
							- How should this factor into an optimality condition?
						- Alternatively, we may wish to require that decision problems are well-defined for any agent (from some well-defined class of agents) -- in which case we need to avoid this kind of time-travel paradox.
				- Thoughts on how Omega models `observation-counterfactuals`.
					- The way we give Omega a slower LI, so that from Omega's perspective the relevant logical counterfactuals are well-defined, is a pretty counterintuitive and nonobvious way of doing things; but it does seem like it might be the only way to do it.
						- Normally, we think of Omega as having much more computational power, in order to run simulations in detail; but this requires Omega to have some subjectively defined, yet objectively correct (from our perspective), notion of counterfactual -- this seems, at least, difficult to spell out in detail.
							- Can we spell it out via constraints on how the agent regards Omega's thinking, rather than having to spell out Omega's thinking in complete detail?
							- But, we would also want to show that there exists a way for Omega to think, such that the agent can rationally regard Omega's simulations as objectively correct in the relevant sense.
					- Note -- this is only a tactic which we use to model specific decision problems, so that we can make statements about how our UDT handles those specific decision problems. This is not on the same level as the general facts about how we set up the environment; facts about how Omega predicts us should not feature directly in optimality criteria, for example, unless we specifically want to write out restricted optimality criteria which deal with a well-understood class of Omega problems.
						-
			- What decision-theoretic optimality conditions might we possibly want to prove?
				- This is more specific than "what nice things do we want to prove in general" -- these are, specifically, notions by which we can measure the performance of UDT against other proposals and find those other proposals wanting.
				- UDT should, obviously, be subjectively optimal according to the prior.
					- This is more-or-less the same as a tiling theorem, since the UDT decision criterion is, itself, expected value according to the prior.
						- There's the version of the tiling theorem where we allow the agent to experiment for a time with bounded self-modification (adopting a fixed policy for some number of rounds), and then we show that if we let it do this for long enough before freezing the prior, it will prefer to stick with UDT rather than perform these self-modifications. (More precisely, UDT should never look significantly worse than a bounded self-modification.)
						- There's a different version, where we somehow explicitly assume that the prior understands the impact of self-modification (instead of learning the impact thru experience); and under that assumption, show that self-modification is not significantly preferred to UDT.
							- This might be able to deal with unbounded self-modification, unlike the learned version.
					- Also more-or-less the same as the assertion that LIDT chooses to self-modify into UDT.
						- Again, we can specify a version of this based on bounded self-modification, and we can also spell out a version of this based on spelling out sufficiently accurate understanding of the structure of consequences.
				- UDT should also satisfy some more "objective" optimality criteria.
					- If we face a sequence of game trees, and we re-freeze the prior for each new tree, according to some schedule (ie the computing power for the prior grows according to some specified function), then UDT's performance should approach optimal performance in some sense.
						-
					- Under some conditions, UDT will learn, IE will behave "somewhat updatefully" -- under those conditions, we would like to be able to show instrumental learning, IE eventual good performance compared to some class of possible strategies.
						-
					- Can we achieve optimality criteria inspired by `infrabayes`?
						-
		- All told, what's the status?
			- Does Soto's work show that UDT succeeds, or fails?
				- Under what assumptions?
			- Does UDT "need some other idea" to work?
			- Have we hit the true limits?
			- Does it make more sense to "face reality" or keep looking?
			- What ideas should be abandoned?
			- What implications does this have for the broader DT picture?
			- When can the advantages of updateful behavior be accommodated within UDT? When this is not the case, is there a broader framework in which the advantages of updatefulness can and should be obtained by moving beyond UDT?
			- How should we think about agent-environment boundaries? How should we think about optimality conditions?
			- What is the overall status of the `happy dance problem`?
			- What is the overall status of classic BLI, where arbitrary future market states are believable, vs alternatives, which might only accept fixed-points (making the relevant adjustments to any other market states observed)?
				- Email:
				  collapsed:: true
					- I am now rather pessimistic about the alternative BLI concept we've
					  been discussing, where conditioning on large market states yields 
					  beliefs which are different from what's been conditioned on (unless the 
					  belief is in fact a fixed point). It seems to me like we might need to stick close to Sam's BLI concept in that respect.
					- Here are some reasons:
						- The principle P_n (x | P_m (x) = p) = p for m>n is quite plausible, and 
						  together with propositional coherence plus luv coherence, implies Sam's 
						  BLI concept. (See the Notion for some partial arguments to this effect.)
						- My worry was that Sam's BLI concept would be too credulous when 
						  conditioned on weird states; eg, if Omega tries to spoof our belief in 
						  digits of pi, but does so poorly, we should be able to take advantage of this. However, note that Sam's BLI can note that a future belief state is implausible by assigning it low/zero probability. In this case, UDT should naturally focus on the consequences for other branches. For example, if I believe a 
						  mathematical conjecture, and Omega asks me for a million utilons in the 
						  case where the conjecture is false, in exchange for giving me one 
						  hundred utilons if it's true, then I can pay up by virtue of assigning low probability to the lose-a-million branch and seeing only the positive consequences in the more probable branch. I don't need to additionally disbelieve the observation *within* the branch where I give up money.
						- Perhaps most importantly, if my future beliefs conditioned on observing market prices are based on *how traders would respond to those prices*,
						  rather than just being the prices themselves, then my 'large' distribution over future beliefs must know more than me. For example, if my traders know how to compute pi at that later time, then whatever my distribution on future *prices*, nonetheless my distribution on *beliefs* (after having observed those prices) will correct any misconceptions about pi. But this means my current 'small' expectations about those beliefs cannot possibly be marginals of that 'large' distribution over beliefs, since I should not yet know those digits of pi! So, this seems to mess everything up.
					- I still see some room for something which is not exactly Sam's BLI concept. Perhaps we should not totally copy our own observed beliefs. But clearly we can't
					  accomplish this by reacting via the true future trading strategies; 
					  and, the decision-theoretic motivation for wanting to try something like
					  this now seems very unclear to me. Whereas the simplicity of Sam's 
					  assumptions seem like a strong point in their favor.
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
		- **UDT.pdf**
			- ![Soto 2023 - 01 UDT.pdf](../soto-2023/Soto%202023%20-%2001%20UDT.pdf)
			- Discusses some brute ideas for assigning probabilities to large sentences by decomposing them. Doesn't particularly try to achieve desirable coherence properties.
		- **Desiderata**
			- ![Soto 2023 - 02 Desiderata.pdf](../soto-2023/Soto%202023%20-%2002%20Desiderata.pdf)
			- Sketches Martin's notion of decision problem ('decision tree') and starts to lay out meaningful desiderata based on it.  Offers rough conjectured proof sketches for these desiderata.
		- **Desiderata Polished**
			- ![Soto 2023 - 03 Desiderata Polished.pdf](../soto-2023/Soto%202023%20-%2003%20Desiderata%20Polished.pdf)
		- **Constructions**
			- ![Soto 2023 - 04 Constructions.pdf](../soto-2023/Soto%202023%20-%2004%20Constructions.pdf)
			- Sketches a logical-induction-like construction which is propositionally coherent and luv coherent, but, which requires all sentences to be decided eventually. Also, expresses some concerns about how Bayesian Logical Induction could work.
		- **Definitions**
			- ![Soto 2023 - 05 Definitions.pdf](../soto-2023/Soto%202023%20-%2005%20Definitions.pdf)
			- More thought-out and detailed propositionally coherent & LUV coherent LI. Contains several conjectures and ideas for alternate definitions of traders.
		- **A framework for constraints**
			- ![Soto 2023 - 06 A framework for constraints.pdf](../soto-2023/Soto%202023%20-%2006%20A%20framework%20for%20constraints.pdf)
		- **A naive proposal**
			- ![Soto 2023 - 07 A naive proposal.pdf](../soto-2023/Soto%202023%20-%2007%20A%20naive%20proposal.pdf)
		- **Formalizing the author's worry**
			- ![Soto 2023 - 08 Formalizing the author's worry.pdf](../soto-2023/Soto%202023%20-%2008%20Formalizing%20Abram's%20worry.pdf)
		- **Formalizing my worry**
			- ![Soto 2023 - 09 Formalizing my worry.pdf](../soto-2023/Soto%202023%20-%2009%20Formalizing%20my%20worry.pdf)
		- **The heart of updatelessness about computations**
		  id:: 64ff8b86-e128-4bef-ba88-94deb8667e94
			- ![Soto 2023 - 10 The heart of updatelessness about computations.pdf](../soto-2023/Soto%202023%20-%2010%20The%20heart%20of%20updatelessness%20about%20computations.pdf)
		- **Problem or Opportunity: LIs do sometimes get tricked**
			- ![Soto 2023 - 11 Problem or opportunity - LIs do sometimes get tricked.pdf](../soto-2023/Soto%202023%20-%2011%20Problem%20or%20opportunity%20-%20LIs%20do%20sometimes%20get%20tricked.pdf)
		- **Epistemics and Instrumentality**
			- ![Soto 2023 - 12 Epistemics and Instrumentality.pdf](../soto-2023/Soto%202023%20-%2012%20Epistemics%20and%20Instrumentality.pdf)
		- **Argmaxing our strategy**
		  id:: 64ff842e-9e75-4759-ba96-7c7a9e2dfef2
			- ![Soto 2023 - 13 Argmaxing our strategy.pdf](../soto-2023/Soto%202023%20-%2013%20Argmaxing%20our%20strategy.pdf)
		- **Impossibility results**
			- ![Soto 2023 - 14 Impossibility results.pdf](../soto-2023/Soto%202023%20-%2014%20Impossibility%20results.pdf)
			- Context:
			  collapsed:: true
				- See ((64ff82a0-07ec-4368-af1d-92e6cf519e70)).
			- Blow by blow:
			  collapsed:: true
				- The goal is to articulate the impossibility result which has Soto so worried about the viability of our UDT.
				- Soto begins by recalling that there's no problem in the case that Omega's behavior truly depends on our actions alone, as discussed in ((64ff842e-9e75-4759-ba96-7c7a9e2dfef2)).
					- I need to review that PDF for the details, but at first blush I'm puzzled by the assertion. If the prior puts a 90% chance on Omega punishing it forever for any deviation from a specific strategy, it doesn't seem to matter what Omega's algorithm *truly* does. In other words, it seems to be a matter of the prior, too, not just the environment.
				- Soto also simply asserts that "Be More Updateful" can be encoded in the prior; his argument for this is, of course, provided in ((64ff8294-e0f8-42ac-b95e-e73c7daaa0e2)).
				- Soto thinks of UDT as fixed, and imagines two free parameters: the prior, and the tree.
					- Soto argues that it won't make sense to talk about finding the best prior for a single decision tree, since some decision trees aren't argmaxed by any prior, nor argmaxed to within $\varepsilon$.
						- Seems like he's talking about unbounded rewards / unbounded utility.
						- Not really sure of the relevance of this, yet.
					- Soto concludes that we should think about average performance over many trees to address this.
				- Soto defines $\bar U_n(A)$ as the average reward agent $A$ obtains across all decision trees of depth $n$, with max $n$ reward per node, and logical coins of length at most $n$.
				- A does "better on average" than A' if $\bar U_n(A)$ is eventually always higher than $\bar U_n(A')$ as a function of n.
					- With globally bounded reward, Soto instead suggests looking at the limit of $\bar U_n()$.
				- **Impossibility idea:** Suppose A doesn't learn, and A' does. Then A' does better on average.
					- How is this an impossibility result?
						- Is the idea that UDT doesn't learn? I guess that's what Soto is trying for: his remark about "even UDT" suggest that flavor:
							- ((6500c6b5-37c2-4806-a99d-5dad0de96469))
						- But I don't think this idea makes sense. Soto seeks to isolate "identical situations" and prove that UDT "doesn't learn" because it must act the same in identical situations. (I think.) But even if UDT sees that a subtree is identical to one it faced previously, and sees no acausal correlations incentivizing different behavior on the subtree, UDT faces a different observed market state in the two subtrees. The different market states could contain different relevant information. IE, it has had longer to think. In particular, the market could have learned something from previous instances of the subtree, and UDT could endorse a policy of utilizing such information.
						- Could a similar idea possibly make sense?
							- I don't especially agree with Soto's argument that we need to consider averages over game trees. So perhaps going back to individual game trees, argue that there's no one decision procedure (including prior) which can do best on _all_ game trees?
								- It could conceivably be that we can always do better if more processing power is available to run LI faster.
								- But it could conceivably not be the case.
							- I do agree with the intuition that there can be arbitrarily farsighted agents, and these will do better in a long-run average sense (if we bound utility but let discounting be subjective, and judge agents by long-run average utility).
					- **Proposed def**: A "doesn't learn" if, for any decision tree, when A faces "identical situations" in different parts of the tree, A takes the same actions.
						- What's an identical situation?
							- Soto admits that this is a problem.
								- First, he supposes that "identical situations" must be sub-trees isolated from the rest of the tree; no acausal connections outside of their subtree.
									- But Soto is very concerned about how to define this.
										- "What if A thinks that a logical coin somewhere else talks about one of the two identical situations, but not the other? Even a completely updateless A might act differently in those two situations."
										  id:: 6500c6b5-37c2-4806-a99d-5dad0de96469
										- Soto suggests that we can't just assume this problem away, because the desired theorem statement has nothing to do with A's internal structure.
											- I don't get it. The proposed "impossibility" theorem assumes "A doesn't learn". Since this statement is universal across trees, it has to be a fact about the prior!
											- I guess it's true that Soto can't simply assume this away, tho, because this is part of his attempted _definition_ of identical. So the "learning" idea would become trivial: to say that A "doesn't learn" would just be to say that when it thinks there's no reason to behave differently in two subtrees, it doesn't behave differently. (The def could have other facets, but would remain trivial: "if the agent sees no reason to behave differently, and also the subtrees are identical in properties XYZ, then the agent does not behave differently.")
												- Well, is that right? I should not equate "no acausal correlations outside the tree" with "no reason not to behave identically". There could be a nontrivial def somewhere around here.
						- This def of "doesn't learn" isn't very appealing to me.
							- It doesn't indicate that the agent is doing anything bad. It could be reacting optimally to the situation.
							- Maybe the point is that no prior can have an optimal response to all sub-tree-shapes already?
							- But if no situations are "identical" (EG: Omega continues to offer slightly different prices and payouts for cf mugging, forever), this def of learning is useless.
						- Soto suggests that this is related to my own def of learning: I demand that we can see the agent as using an improved prior; Soto demands that "anything change at all". So, Soto sees his condition as weaker and simpler.
							- I reject this analysis, though, since "identical situations" doesn't seem simpler, and since his idea doesn't seem implied by mine; EG, an agent can learn to use better estimates for Benford-esque cf muggings, without ever facing identical situations to illustrate the changed behavior.
				- Soto thinks the problem with defining "identical" has to do with difficulties reasoning about logical coins.
					- It seems like Soto's issue is that logical coins can possibly refer to the agents actions or other aspects of the agent's computation (due to embeddedness), which messes up the apparent causality of the game tree.
					- We can make a pseudo-objective agent-env boundary by imagining that we can vary the agent freely, so coins cannot consistently refer to "the agent's action" or any other aspect of the agent. Causality of the decision tree is recovered.
					- However, we then get "evil" problems which defeat specific DTs by successfully guessing their source code and referring to them anyway.
					- In the case of logical decision theory, there was a result showing that "evil" problems could be defeated by ascending in proof power: if the decision problem guesses your True Name, you may lose, but the same decision procedure with access to stronger axioms could get revenge.
					- I wonder if there could be a similar result here, replacing proof strength with computation: if Omega guesses your true name and punishes you specifically for making you-like decisions, then if you could think faster, you could figure out which actions are being punished and take different ones. So in some sense, the limits are only due to bounded computation, rather than the DT itself.
						- This is supposed to be helpful in the sense that it means, when using the proposed DT, all concerns can be addressed in principle by getting more computational resources. There's no tricky case where more computational resources is actually a worse idea, because it makes us harder to reason about or whatever.
						- But really, those cases still exist; they have simply been ruled out by the assumption that the environment doesn't get to change its logical coins in response to changes in the agent presented. This is a simplified assumption about the agent-environment interface, designed to make decision theory tractable!
				- Soto tries to remove the "boundary" problem in a few ways:
					- Speculation about restricting the coin. Soto conjectures that no way to do this will be satisfactory; any coin can be correlated with the actions of some UDT.
					- Getting rid of the coins entirely. Soto thinks we still face similar problems due to the subjective beliefs of the UDT (which makes sense to me).
					- Switching back to the empirical case.
						- Soto claims that the concerns about argmaxing trees to within epsilon disappear. (?)
						- Soto claims that it's then trivial that we don't learn: of course we deal w identical subtrees in the same way (since he gives UDT the prior corresponding to the exact decision tree).
						- Soto suggests that if we re-introduce uncertainty over trees, we just get a similarly trivial situation where the way we average performance across trees defines the new best prior.
						- Soto suggests that the problem lies with expected value maximization, and speculates about more kelly-like ideas (specifically, taking the log of the cumulative reward).
				- Soto suggests that the main bottleneck (to "proving interesting things") is better models of logical coins, which is to say logical uncertainty. Soto takes this as evidence that we need really new ideas (eg a more realist picture of logical uncertainty, or a replacement for EV maximization, or a generalization of probability) to get some things we wanted.
				- Soto concludes with a humbler "impossibility result" conjecture:
					- That contrasting UDT (based on running LI for k steps and then freezing and extrapolating) with a forced-update UDT (based on surgery on the prior), the second does better on average in the earlier-specified sense.
						- But LI can produce something that's already in agreement with the surgery? So this seems implausible.
						- However, it seems like similar ideas may be plausible.
							- UDT with bounded utilities can't care about the long-run average reward; so plausibly, there will be other DTs which do better on that metric.
		- **The extra learning assumption**
		  id:: 64ff8294-e0f8-42ac-b95e-e73c7daaa0e2
			- ![Soto 2023 - 15 The extra learning assumption.pdf](../soto-2023/Soto%202023%20-%2015%20The%20extra%20learning%20assumption.pdf)
			- Context:
			  id:: 64ff82a0-07ec-4368-af1d-92e6cf519e70
			  collapsed:: true
				- While in [scrubbed], Soto and I became, finally, pessimistic about getting everything we might have wanted out of the UDT we've been working on.
				  collapsed:: true
					- Before [scrubbed], I think, it became plausible that the importance of the universal instantiation property would dash my hopes for learning: the possibility of correlations with unbounded reach would, presumably, mean that Omega could incentivize behaviors which never die out.
					- In [scrubbed], Soto explained how he hadn't found a way to get the A(o)=a solution to Happy Dance to work, and also explained his argument that the Happy Dance problem remains in any case.
					- Soto also explained his renewed pessimism about learning. I expressed my optimism for a more conservative result, that UDT could learn _if_ it _didn't_ believe in any forever-correlations preventing this. This is similar to learning in the absence of belief-in-traps: it's not _realistic_, it's not even justifiable as a prior (due to its extreme dogmatism), but it does give us some assurance that the DT is sane overall.
						- Soto expressed some kind of pessimism about this? I don't recall his exact thoughts here. I think Soto always agreed that we could force updatefulness by appropriately modifying the prior. So maybe the pessimism comes from seeing such modifications as an ugly hack?
						- Or perhaps Soto argued that performing such a modification wouldn't establish the philosophical point I hoped it would?
					- I wanted to argue for an analysis like: UDT handles counterfactual muggings by updating to the same extent that Omega does when Omega figures out what to do.
						- I'm not attached to this being exactly the correct heuristic; the point is to argue that there is some heuristic between "use the prior" and "use the most updated market beliefs we have time to calculate".
							- Omega's probability estimates should eventually be *calibrated*, no matter how objectively bad they are (due to not thinking for very long to estimate things).
								- So, because they are calibrated, they shouldn't be terrible to use for our heuristic about which payoff ratios to accept or reject.
							- From Omega's perspective, if we use LI information thinking any *longer* than that, it looks like noise in our accept/reject probabilities.
								- Let's suppose Omega probability-matches (so if Omega sees us paying up with prob p, then Omega pays out in the other branch with prob p, using a very hard to predict coin, EG an empirical coin).
								- So when we think about using a later LI estimate than Omega's, we think it'll give us better information, but we know that any branches where we use this info to decide not to pay up correspond to a reduced probability of payouts in cases where it _is_ worth it.
									- At least, that's how it _should_ work, according to me.
							- On the other hand, if we think _less_ long than Omega, we will still (eventually) be using calibrated estimates, but we could be thinking longer and getting better information, without becoming less predictable in Omega's eyes.
							- So I think the optimal strategy is for us to think long enough to figure out Omega's own probability estimate exactly (since we want to use an estimate which Omega can "see" at the time when Omega is figuring out what to do).
						- This is meant to address a concern like: UDT will use its dumb prior to estimate the probability of a logical coin, so it will use that dumb probability to decide whether a cf-mugging cost/payoff ratio is acceptable or should be rejected.
						- One hope for my analysis might be that _if the prior is informed enough_ (ie, if we run LI for long enough before freezing the prior), we get some heuristic like that.
						- A different hope for my analysis would be that _under the learning condition_ (ie, assuming we have a prior which eventually acts as if we froze any arbitrarily late market state), we get some heuristic like that.
					- Soto wanted to argue that probability theory was inadequate to express what we wanted; that a tweaked prior couldn't possibly do what we wanted to do. I remain skeptical of this point. Soto himself seems to believe that the prior can be tweaked to force learning, but regards this as a hack. What more could we hope for with a generalization of probability theory?
					- I came up with the example of the iterated counterfactual mugging on a single (logical or empirical) coin-flip, to illustrate my understanding of the conundrum.
				- In our phone call last week, Soto expressed his pessimism in an extreme form, asking me why I wasn't acting desperate about it; stating that it seems UDT needs a new idea in order to work, and pointing out that this knocks out an entire pillar of my agenda.
					- I suggested that my equanimity came from facing reality, and that it didn't seem like some new idea would change the basic picture here.
					- Soto suggested that our UDT had strayed from ((64ff8b86-e128-4bef-ba88-94deb8667e94)) because it made all of its decisions from a fixed point, like policy selection, rather than ... something else. Soto seems to think that using two market states (the small and the large) is a hack.
					  collapsed:: true
						- My intuition is that Soto wants something resembling the anthropic perspective instead, but I wasn't able to say any words that Soto really resonated with.
						- I argued for open-minded UDT as the best route for Soto to investigate. Soto thought the idea of updating on some things and not others seemed artificial, but I suggested that the real question was whether we could make sense of there being a truth of the matter about "good" prior probabilities to have, which Soto at least took note of.
				- In a subsequent email, I ask Soto for thoughts about sharply defining the problem as an impossibility result. I suggest that this would be useful whether the right answer is "give up and face reality" or "keep looking for new ideas to salvage things". Soto responded with a PDF later, but that's a different one from the 'extra learning assumption' one.
				- In a follow-up email I sent more thoughts about what "learning" should mean for UDT. Soto sent me his impossibility stuff while I was midway through composing this email, so I took some of it into account but without fully understanding where he had gone with the idea.
					- I argued that either we're in a situation where we've learned that some extra assumption is needed, like the no-traps situation, or else we're in a harsher situation where UDT is totally inconsistent with learning. It seemed to me like Soto was suggesting something between the two.
				- Soto then responded to these extra thoughts with the 'extra learning assumption' pdf.
					- Soto seems to affirm that learning can sometimes happen, and also that we can force the prior to be arranged so that learning definitely happens.
				- My concerns which Soto is responding to in the 'extra learning assumption' PDF:
				  collapsed:: true
					- I suggested before that the condition resembles "the
					  UDT, making decisions using a fixed market state LI_0, eventually acts 
					  like it is making decisions using LI_N for arbitrary N." I was concerned
					  that this might allow a totally updateful thing to count. I would 
					  prefer a more meaningful learning condition; EG, learning to pay up in 
					  sequences of counterfactual muggings. (Modulo some assumptions about the
					  sequence of counterfactual muggings, perhaps.) Initially, I was 
					  thinking about a requirement that the behavior updates, but "not too 
					  fast". But this doesn't make sense, since in some situations, perfectly 
					  updateful behavior is the right thing to learn.
					- But
					  perhaps "the UDT eventually acts like it is making decisions using 
					  LI_N" is actually enough, due to interactions with the LIC. Suppose that
					  a sequence of Transparent Newcomb problems is encountered, for example.
					  The LIC should guarantee that the pattern of the decision problems is 
					  understood. (This is hand-wavy.) The other conditions established for 
					  the UDT should then guarantee that the UDT doesn't update too fast. So 
					  UDT acting "fully updatefully" in such a case should be excluded by LIC.
					- Still, this might make 
					  "the UDT eventually acts like it is making decisions using LI_N" **inconsistent**
					  ... like, can we really edit the prior to force behavior to be 
					  eventually-updateful, while preserving all of the other nice conditions 
					  of the UDT, including the LIC?
					- Maybe this speaks to your point:
						- > > The thing we think we've learned is that some extra condition is needed, beyond what we had hoped.
						  > 
						  >  I haven't been able to find any natural assumption that captures what we need. I feel like what we've discovered is something more like "logically 
						  uncertain EVM is as bold (and sometimes risky) as we could expect". And as a consequence of that, indeed, we have that reward can be arbitrarily bad (except when we have some ultra-strong assumption like "this prior has been optimized for instrumentality by a reasoner that had all the correct opinions about this decision tree"). But it doesn't get captured by non-extreme assumptions about the decision tree or beliefs.
					- Again, I think the condition is something like "the prior is such that UDT's behavior can eventually be explained as if it has updated to day N, for every N". But
					  of course this is not a constructive condition on the prior, and 
					  perhaps it isn't possible to construct such priors. So translating it to
					  some constructive condition (or showing that my condition can be 
					  constructed) would be necessary, to support my "some extra condition is 
					  needed" story.
					- In some sense I do agree with your "UDT doesn't work" narrative, if there really is no such condition. (Although, I'm not sure how to reconcile this with my feeling that we just need to face reality on this. It feels like "doesn't work" has some
					  kind of evolutionary intuition behind it... like beings who use UDT 
					  will eventually be out-competed by beings who learn. But is that a 
					  reason for an individual agent to prefer updating? Not necessarily!)
					- More specifically, my intuition is that the reason this could fail is the 
					  universal instantiation condition. Since entanglements involving 
					  universal statements can touch infinitely many instances, perhaps a 
					  modification of the prior to behave somewhat-updatefully-eventually
					  would have to violate universal instantiation or some other important 
					  property. But universal instantiation is an important part of how the 
					  UDT proposal works. So if this were the case, the UDT setup would be 
					  more directly "against learning". (Sorry, again, for the messy reasoning
					  here.)
					  So I guess ***either* **we have
					  a situation where "we've learned that some extra condition is needed, 
					  beyond what we had hoped" (in which case we can still get a picture of a
					  rational agent who learns, just with more restrictive assumptions in 
					  addition to the expected no-traps assumption)** *or else*** our 
					  UDT is totally inconsistent with learning in this sense (which confirms 
					  some of the worse fears one might have about logical updatelessness -- 
					  at least in so far as our UDT is the best formulation of UDT for logical
					  updatelessness).
					- And either way, it would be good to know which of those situations we're in.
					- But I'm somewhat confused about the role of universal instantiation. I need
					  to sit down and think about it for longer. I think we agreed that a 
					  universal statement could remain near probability zero no matter how 
					  many positive instances we see (and similarly, an existential statement 
					  could remain near probability one no matter how many non-instances we 
					  see). But in some sense this means learned generalizations which have to
					  go through universals are not guaranteed to be good. But many things 
					  for UDT *do* have to go through universals. So this in itself 
					  should disrupt some hopes for learning, no? EG, we may not correctly 
					  learn "it is always better to one-box in transparent newcomb", since the
					  probability of the universal can remain low despite numerous examples. 
					  Is there something wrong with my reasoning, or is this correct?
				- Soto's meta-remarks about the PDF:
					- About your extra learning assumption (the first half of your email), I 
					  adjoin a PDF in which I basically show we can constructively edit the 
					  prior to satisfy the assumption, as you wanted. It's mostly "Policy 
					  Selection expressed inside the epistemic framework", but it has some 
					  interesting ramifications. I also address your worries about Universal 
					  instantiation and LIC, and other things.
			- Blow by blow notes:
			  collapsed:: true
				- The "extra assumption" is:
					- The UDT algorithm (based on the infinitely-extended market, $\mathbb{P})$ is such that, for every $n$, UDT eventually acts as if it's deciding using $\mathbb{Q}_n$.
						- Note that we can consider this _as a property of_ $\mathbb{P}$, universalized across environments it faces; or, we can consider it as a property of (agent, environment) pairs. We might call the first the "universal" version, and the second the "contingent" version.
							- Universal f-learning:
								- For all infinite-depth game trees, for every n, there is a time f(n) such that UDT$_\mathbb{P}$ makes the same decisions as UDT$_{Q_{f(n)}}$ at and after that time.
							- Contingent f-learning:
								- For a given infinite-depth game tree, for every n, there is a time f(n) such that UDT$_\mathbb{P}$ makes the same decisions as UDT$_{Q_{f(n)}}$ at and after that time.
						- There's also an interesting intermediate version:
							- $\mathbb{P}$ is such that contingent f-learning applies for any game tree which does not give evidence against the belief that behaving f-updatefully is a good idea.
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
						- If the prior believes we'll face infinitely many counterlogical muggings, and has the credence $\mathbb{Q}_k(\phi)=.9$, then Soto claims it will have the universal belief that accepting muggings with payoff ratios >$1\over 9$, and will never act like it thought for longer.
							- $\mathbb{Q}_k$ is the market state which gets unrolled into the prior.
							- I'm not sure what $\phi$ is here. The coin? Which coin?
							- Again I'm unsure where the universal belief comes from.
							- My suspicion is that Soto is basically wrong here? Like, this _could_ happen, but I don't see why it _usually_ happens.
								- EG, if my conjecture is right, then 'most' priors will evaluate cf muggings with Omega's probability.
				- Soto's argument that we can brain-surgery the prior to force updatefulness relies on the same idea as the argument that updatefulness may not happen: we can force a universal belief which simply says to update (at some given rate).
					- Soto's suggestion is a little more involved than this, but this seems like the basic idea, and anyway, this should work if the whole "universal belief insists on a specific strategy" idea works.
					- Soto tries to soften the blow of how ugly this is; but for me, the point is the existence proof. We can fruitfully assume the property for learning-theoretic analysis so long as instances exist.
						- Although, there are important questions of how 'nice' or 'ugly' such priors can be. For example, it would be interesting to prove that any prior which has the learning property must necessarily update at _some rate_, and therefore, cannot "learn to behave in an arbitrarily updateless manner"!
					- Soto's argument that the resulting thing is still a BLI and still follows all of our other coherence constraints is that it seems obvious -- he doesn't see why I am worried about this. But he agrees the argument needs to be spelled out.
						- If the universalized-strategy trick works, I am convinced.
						- But I'll try to spell out my concerns in a bit more detail.
						- Soto asserts that we have to trash knowledge which contradicts the policy we are trying to enforce, EG, universal beliefs which make contradictory claims about optimal policy. If we have to do this, it sounds as if we have to worry about maintaining some kind of coherence? So it seems the task of maintaining coherence is nontrivial.
						- Behaving as if we've made a decision based on LI_n for all n from 0 to N is perfectly consistent _provided that each n<N endorses further updatefulness_. But Soto asserts that although we modify LI_k, _all further LI_n remain as they were_.
							- So, what happens if some specific LI_n sees reason to stop behaving updatefully beyond that point?
							- In my mind, it seems like believing in making decisions based on LI_n at round m implies also endorsing being at least that updateful _from then on_, which could imply being _at most_ that updateful from then on, depending on LI_n.
							- However, I suppose that's not necessarily the case. Behaving like LI_n would behave _at round m_ does not imply the stronger condition of behaving like LI_n would behave _from then on_.
								- In particular, Soto isn't getting updateful behavior out of a restriction on acausal correlations.
				- Universal Instantiation
					- Soto stresses that although the market extrapolation satisfies Gaifman, this in no way implies that the LI itself satisfies Gaifman, and in particular, converges to the standard model or anything like that.
					- I think Soto misses my worry, which was that if Universal Instantiation is what dashes our hopes for learning-by-default, then it should be hard to construct a learner without breaking universal induction. But Soto's construction (if it works) addresses this concern, anyway, by leveraging the universals rather than suppressing them.
						- My worry was that if we satisfy LIC, and our policy amounts to a somewhat updateful one, then even if we heavily edit the prior, LI may wander into a universal belief contrary to updating at some point in the future. At this point, it should stop updating. But our modification of the prior supposedly made sure this cannot happen. So it must have violated LIC.
							- This is rather vague. It's not clear why an LIC-follower has to be so unpredictable. Perhaps a strong trader could approximately enforce pro-updating beliefs forever.
								- In particular, perhaps a strong trader could approximately enforce such beliefs forever _so long as the environment complied with the assumption_!
									- This is analogous to almost completely believing a no-traps assumption, and also, never seeing any strong evidence to the contrary.
					- Soto also _somewhat_ dismisses my concern that the probabilities assigned to universals don't become good, since the LI isn't really Gaifman-inductive.
						- Soto suspects it won't be a problem in the presence of time-discounting, since the relevant universals will be provable.
							- This seems plausible.
						- Soto further opines that even if it's a problem, it wouldn't be UDT's fault, it would be the fault of LI.
							- This seems irrelevant.
				- LIC
					- Soto seems particularly confused about my concern that the LIC would somehow have to be broken in order to enforce the learning constraint.
						- I think my updated take on this is adequately captured in a couple of emails I just sent him:
							- Email 1:
								- I'm still working through things, but I think my main confusion was as follows:
								- I
								  was imagining that forcing updateful behavior would be done through 
								  **constraining the possible acausal correlations**. So for example, if 
								  we want the prior to endorse using Q_n by decision m, we would ensure 
								  that the prior thinks decision A_m does not possess correlations across 
								  the possible Q_n (it only impacts the observed Q_n it belongs to; 
								  alternative possible Q_n don't care about what happens in each other's 
								  worlds), and also that different possible A_m do not modify the branch 
								  probabilities (the relative probabilities of the different possible 
								  Q_n).
								- Call the constraint on the prior C(n,m).
								- Suppose
								  we want to enforce this property for two such (n,m) pairs: n1,m1 and 
								  n2,m2, such that n1<n2 and m1<m2. Clearly, this can only work if 
								  Q_n1 endorses switching to Q_n2. In other words, C(n2,m2) has to be 
								  enforced for the prior P, *and also* for the market state Q_n1.
								- Suppose
								  now that we want to enforce C(n,m) for infinitely many pairs (to get an
								  asymptotic learning property). By similar reasoning, we need to enforce
								  infinitely many instances of the constraint *not only for P, but for infinitely many Q_n as well*.
								- This
								  is why I was worried about somehow violating the logical induction 
								  criterion: because apparently infinitely many market states need to be 
								  modified.
								- Your proposed solution instead only modifies P, and leaves the future market states untouched. So the concern does not arise.
								- Relatedly,
								  your idea for getting updateful behavior is more of a hack :) But it 
								  doesn't matter if it's a hack; the idea is to prove the existence of 
								  priors which prefer to update. So long as some exist, it can be a 
								  fruitful learning-theoretic assumption. (But it could be interesting to 
								  prove that all such priors are "hacky" or "unnatural" in some sense... 
								  eg, if no BLI has a structure like the one I'm trying to describe above,
								  enforcing infinitely many C(n,m), that would be interesting, since to 
								  me it is the natural reason to choose to update. Your construction is 
								  more like behaving updatefully because we think Omega will punish us 
								  otherwise!)
							- Email 2:
								- Ah, here is a more general way to state the concern.
								- The
								  desired learning property was "for every n, UDT eventually acts as if 
								  using (the infinite extrapolation of) Q_n" instead of P.
								- I can think of two interpretations of this.
								- Weak interpretation: *For every n, there is a time m, beyond which all actions can be interpreted as being chosen by (the infinite extension of) **Q_x for x greater than or equal to n**.
								  *
								- **
								  **
								- (This weak interpretation allows future actions to move on from Q_n and be yet-more-updateful.)
								- **
								  **
								- Strong interpretation:
								  *For every n, there is a time m, beyond which all actions can be 
								  interpreted as being chosen by (the infinite extension of)** Q_n**.*
								- (This
								  strong interpretation only allows later actions to be even more 
								  updateful than Q_n if Q_n itself endorses the further updatefulness.)
								- I
								  was assuming the strong interpretation rather than the weak one. If we 
								  need to edit P, it seems pretty clear that we need to edit every Q_n in 
								  the same way, because every Q_n has to endorse all future choices in 
								  exactly the same way that P does. So I hope it is pretty clear why the 
								  LIC might be violated by some such construction.
								- As I understand it, your construction establishes the weak property rather than the strong one.
								- A
								  construction which gets the weak interpretation and not the strong one 
								  seems like it should have tiling concerns. Suppose Q_n does not endorse 
								  updating further, but P does. Then on the round when P mimics Q_n, Q_n 
								  should prefer self-modifications which overthrow P and stop the 
								  updating.
		- **A foundational problem**
		  id:: 650343b1-ce36-4f4d-9325-f5995461bfc2
			- ![Soto 2023 - 16 A foundational problem.pdf](../soto-2023/Soto%202023%20-%2016%20A%20foundational%20problem.pdf)
			  collapsed:: true
			- Context:
			  collapsed:: true
				- Words from Soto's emails about it:
					- First off, these "independence" properties might be naturally expressed in terms of d-separation.
					- More importantly, working on this (formalizing those two properties) made me
					  notice an apparent issue in our foundations. It's late and *maybe I'm just hallucinating, *I'll check this thoroughly tomorrow, but I include it just in case. As you will remember, we had for now resorted to conditioning on Q_n=q -> A_n=a, instead of A(q)=a, because that allowed for small beliefs affecting large beliefs (without needing to completely update). 
					  Especially, in your email from 16 Aug you present the argument for why 
					  that works.
						- (Words from my aug 16 email, slightly revised:)
						  collapsed:: true
							- Notes from today:
								- It seems like the biggest worry of yours was (more or less) put to rest by the clarification that we consider policy points in the form A(q)=a, where the observation q is the full market state at the future time.
								- So although the *prior* is entirely an extrapolation of a single market state, we *do* run the logical inductor longer, for the *observation*.
								- In particular, the concern was that the large future decision node could 
								  have some subtle property P. The small beliefs know the correct action 
								  to make given that property, but they can't compute which decision nodes
								  have the property.
								- My response was that q, the later inductor state, should be able to compute the property. (If it cannot, then the property is just too hard for the agent to compute; that's fine.)
								- In other words, the idea is that the necessary information is inside the observation.
								- Imagine for a moment that UDT considered a policy-point by conditioning on Q_n = q -> A_n=a.
									- Q_n is "the nth market beliefs", ie, a term referring to the nth market 
									  beliefs without spelling out what they are; q is the actual written-out 
									  (large) statement of the future market state; so Q_n=q is just the 
									  assertion that the nth market beliefs turn out to be q in particular. 
									  $A_n$ is similarly a term referring to the nth action of the agent, and $a$ 
									  is a specific action, so $A_n=a$ is just saying that the nth action turns 
									  out to be some specific one.
									- So here we are just conditioning on the proposition that a specific observation implies a specific action.
									- This is the wrong thing for UDT to condition on; it creates a DT which is 
									  too confident in its ability to rule out scenarios. EG, if the DT a 
									  priori thinks that it will probably panic if there is a bomb, then it 
									  will think it can reduce the probability of a bomb by refusing to panic 
									  when it sees one. `happy dance problem`
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
									  this will be true, EG the speculations I've previously made about how 
									  cross-branch correlations should be bounded somehow, so that further-out decisions must effectively wash out the prior. (I'm less confident that
									  this will work out, now, due to the thing you're doing with instantiating universal sentences!) The hope would be to show that asymptotically, decisions are made based on empirical correlations, not flights of fancy.
					- But now I worry that, because P(A->B) is not the same as P(B|A), that argument doesn't go through. Since P's small beliefs that will be extrapolated to large beliefs look like "forall q (A -> B)", there's no obvious way to fix this (other than being completely updateful).
					- ---
					- Turns out the apparent issue in our foundations I noticed yesterday was 
					  real, and our argument doesn't work. I adjoin an explainer of that.
					  I'm thinking of solutions, but probably we (or P) will have to pre-specify 
					  which syntactic properties of future observations to check omnisciently 
					  (which bits of information to be updateful about). But I already have 
					  ideas for implementing that, and I don't think it'll change the picture 
					  too much. (And then we can use A(q)=a, the right conditional.)
			- Blow by blow:
			  collapsed:: true
				- Suppose there is some universal belief that an action is good in specified circumstances ($\uparrow$ here stands for "is high", instead of tracking specific bounds):
					- $\uparrow \mathbb{Q}_k (\forall \mathcal{Q} (P(\mathcal{Q}) \wedge (\mathbb{Q}_m = \mathcal{Q} \to A_m=a) \to \uparrow U)$
				- What we want to happen:
					- Suppose $P(\mathcal{Q})$ for a specific $\mathbb{Q}_m=\mathcal{Q}$, and $\mathcal{Q}$ is aware of this fact, ie:
						- $\uparrow \mathcal{Q}(P(\mathbb{Q}_m))$
							- Soto wrote $\uparrow \mathcal{Q}(P(\mathcal{Q}))$, but this belief is too large, living only in the extrapolation.
					- (**IMPLICATION**) By instantiation, we have:
						- $\uparrow \mathbb{P} (P(\mathcal{Q}) \wedge (\mathbb{Q}_m = \mathcal{Q} \; \to \; A_m=a) \to \uparrow U)$
					- (**DESIRE**) We want it to be the case that:
						- $\uparrow \mathbb{P}(\uparrow U | \mathbb{Q}_m = \mathcal{Q} \to A_m = a)$
						- ie, the prior things utility is high conditioned on the material conditional policy point.
				- So how could we get this to be the case?
					- It would be satisfied if
						- $\uparrow \mathbb{P} (P(\mathcal{Q}) | \mathbb{Q}_m = \mathcal{Q} \; \to \; A_m = a)$
					- Because (IMPLICATION) plus this imply (DESIRE).
					- But this is not at all plausible in general. Conditioning on $\mathbb{Q}_m  =  \mathcal{Q} \; \to \; A_m  = a)$ restricts us to two kinds of worlds: those where $\neg \mathbb{Q}_m  =  \mathcal{Q}$, and those where $\mathbb{Q}_m  =  \mathcal{Q} \; \wedge \; A_m  = a)$. The second kind of world does what we need, but the first very much does not.
						- IE, other branches have no reason to believe $P(\mathcal{Q})$, since this has only been calculated in the 'true' $\mathbb{Q}_m$.
				- Soto's interpretation:
					- We thought that the knowledge would come together correctly (the prior knowledge that P means we should take action a, and the posterior knowledge that P). But actually, since the knowledge of P doesn't exist in other branches, it is not used there. We can follow the chain of logic if we know that P, but if we condition on this knowledge, we are just being updateful.
					- Martin suggests that the solution _is_ to figure out how to be somewhat updateful; EG, let UDT choose some stuff to be strategically updateful about.
				- My interpretation:
					- To me, this feels like a problem with the o->a version of a policy point, which should hopefully be fixed by the A(o)=a version. The o->a version cuts out possibilities where o and not a, but it fails to inform the other branches of the proposed action. So of course other branches are not putting information together in an appropriate way! Other branches need to be conditioned on A(o)=a in order to evaluate it.
					- Indeed, it seems like the o->a version is equivalent to EDT in the case that P(a|o) is the same for every action. So this really isn't UDT, and inferring problems for UDT seems unwarranted.
					- To get the A(o)=a version to work, we just need every branch to be able to sensibly evaluate the impact of the policy-point for their own situation. EG, call the two branches in cf mugging "ask" and "get", with actions "give" and "refuse". What we need is for the "get" branch to correctly understand the impact of "A(ask)=give".
						- Well, we also need to correctly understand impacts on branch probabilities. In a version where the "get" branch doesn't include an observation of whether the large sum of money is received yet or not, that branch can condition on "A(ask)=give" and expect the large sum, and condition on "A(ask)=refuse" and not expect the large sum. But in a version where "get" does see the reward directly, we actually need to split the problem into three branches, "ask", "get", "nothing" (where "nothing" corresponds to not being asked and also not being given anything). The policy points shift probability between "get" and "nothing".
						- Part of the claim here is that we need to be very careful about the distinction between the global expected utility vs expected utility in specific branches.
							- Sentences like $\uparrow \mathbb{Q}_k (\forall \mathcal{Q} (P(\mathcal{Q}) \wedge (\mathbb{Q}_m = \mathcal{Q} \to A_m=a) \to \uparrow U)$ are making claims about the global expected utility being high under certain conditions. But this kind of thing is a meta-belief for UDT, which is to say, a statement about UDT's own evaluation of the expected utility. But I think we were thinking as if it were a more object-level statement about utility.
								- This isn't true. U here is just U, not some kind of expected utility calculation. So the statement is making a prediction: either U will be high, or [Q_m will be Q and A_m will not be a], or not P(Q).
							- My claim is that it's weird for UDT to reason like "actions satisfying some condition are always UDT-approved, and this here action satisfies the condition, so it should be UDT-approved". Maybe this style of reasoning will be used in some cases, but for it to be correct, it should have been formed as a generalization from more specific cases where more object-level considerations decided things.
							- Object-level considerations for UDT involve weighing the pros and cons of a policy point in terms of positive and negative impacts across different branches (and re-weighing probabilities of branches). This means looking at the local (updateful) expected utilities within those different branches, and taking a weighted sum, rather than directly trying to reason about the global expected utility before having done that.
						- So we need two things to happen:
							- Branches have small beliefs about how policy points impact them, but A(o)=a is a large sentence. We need small and large beliefs to cohere appropriately so that conditioning on such large sentences has impacts consistent with the small beliefs of the branches.
								- So when we condition $\mathbb{P}$ on a policy-point, the sum decomposes to a sum over possible Q_m (themselves extrapolated to have large beliefs, since the BLI has 'already' extrapolated everything -- ie, $\mathbb{P} (x | \mathcal{Q})$ is an extrapolated version of $\mathcal{Q}$).
								- So suppose $\mathcal{Q}$ has a universal belief stating that $P(\mathcal{Q}')$ implies $A(\mathcal{Q}')=a$ is good or bad (in the updateful sense; ie, good/bad for $\mathcal{Q}$ specifically).
								- What we want is that extrapolate($\mathcal{Q}$) has high/low expected utility conditioned on that policy point.
							- The prior, of course, has even smaller beliefs about how policy points re-weigh branch probabilities. The impact of conditioning the prior on the large policy point needs to impact relative branch probabilities in a way that fits with the small beliefs.
								-
		- **Getting UDT1.1**
			- ![Soto 2023 - 17 Getting UDT1.1.pdf](../soto-2023/Soto%202023%20-%2017%20Getting%20UDT1.1.pdf)
			- !`Soto 2023 - 18 Getting UDT1.1 (fixed version).pdf`.pdf)
		- **Deciding what to be updateful about**
			- ![Soto 2023 - 19 Deciding what to be updateful about.pdf](../soto-2023/Soto%202023%20-%2019%20Deciding%20what%20to%20be%20updateful%20about.pdf)
		- **Reflection principle and epistemic self trust**
			- ![Soto 2023 - 20 Reflection principle and epistemic self-trust.pdf](../soto-2023/Soto%202023%20-%2020%20Reflection%20principle%20and%20epistemic%20self-trust.pdf)
		- **PIBBSS Final Report: Logically Updateless Decision-Making**
			- ![Soto 2023 - 21 PIBBSS final report - Logically updateless decision-making.pdf](../soto-2023/Soto%202023%20-%2021%20PIBBSS%20final%20report%20-%20Logically%20updateless%20decision-making.pdf)
			  collapsed:: true
				- {{video https://www.youtube.com/watch?v=uNv1Cq-aVKY&t=810s}}
		- **Directions to pursue**
			- !`Soto 2023 - 22 Directions to pursue (October 2023).pdf`.pdf)
		-
	- Notes on Diff PDFs
		- **A Poly-Time Implementation of UDT 1.0** `UDT` `UDT 1.1` `UDT 1.0`
			- !`UDT_1_0_Algorithm_1699298575267_0.pdf`
			- Blow-by-blow notes:
				- Basic UDT setup
					- $\mathbb{B}=\{0,1\}$. $\mathbb{B}^n$ is the space of n-digit strings. $\mathbb{B}^{\leq n}$ is the space of n-or-less digit strings. $b$ is often used to denote a bitstring. Extensions of a bitstring can be written like $b0$, $b01$, etc. Bitstrings will frequently be called "locations" or "nodes" in a complete binary tree which can be indexed by bit-strings.
					- There is a utility function on completed bitstrings, $U: \mathbb{B}^n \to [0,1]$
					- At each node, there are two possible actions. (Action bits are not observed -- not directly part of the binary tree.)
						- space of policies, $\Pi: \mathbb{B}^{<n} \to \mathbb{B}$
						- $\pi$ for a specific policy, $\pi(b)$ for the action at a location
					- Environment $e: \Pi \times \mathbb{B}^{<n} \to [0,1]$, probability $b$ will be extended with 1.
						- UDT is typically associated with problems where what happens at a node may depend arbitrarily on other parts of your policy.
						- The size of a raw environment description with $a$ bits of accuracy for the probabilities is $a 2^n 2^{2^n}$, which is pretty big.
					- $\pi \bowtie e : \Delta(\mathbb{B}^n)$, the probability distribution produced by $\pi$ interacting with $e$.
						- abuse of notation: $(\pi \bowtie e)(b)$ for $|b|<n$ gives the probability that $b$ is the prefix of a sampled bitstring.
						- $\pi \bowtie e$ can then be recursively defined as follows:
							- $(\pi \bowtie e)(b) = e(\pi, b) \cdot (\pi \bowtie e)(b1) + (1-e(\pi, b)) \cdot (\pi \bowtie e)(b0)$
								- This doesn't appear to handle the base case of the recursion, where $|b|=n$.
								- Seems like you'd instead want to recur in the opposite direction:
									- $(\pi \bowtie e)(b1) = e(\pi, b) \cdot (\pi \bowtie e)(b)$
									- $(\pi \bowtie e)(b0) = (1 - e(\pi, b)) \cdot (\pi \bowtie e) (b)$
								- Which reduces to an iteration:
									- Let $f_{1} (r) = r$ and $f_{0} (r) = 1-r$
										- $f_c(r) = (2c-1) r + 1-c$, if you will
									- $b|i$ is the length-i prefix of b
									- $(\pi \bowtie e)(b) = \Pi_{i \leq n} f_{b_i}(e(\pi, b|(i-1)))$
					- The goal is to maximize expected utility:
					  collapsed:: true
						- $\text{argmax}_\pi \mathbb{E}_{\pi \bowtie e} [U]$
						- This is a version of UDT 1.1. But, the naive way to compute it at least, it's very computationally expensive.
							- $2^{2^n-1} \cdot T(n)$
								- $T(n)$ is the time to calculate $\mathbb{E}_{\pi \bowtie e} [U]$ for given $\pi, e$
								- $2^n-1$ elements of $\mathbb{B}^{<n}$
								- space of policies maps this to $\mathbb{B}$, so $2^{2^n-1}$ policies to check
				- Linear Games
				  collapsed:: true
					- General games: if $a_j$ is the action of player j, so $\vec a$ is the joint action, the game can be described by a 'payoff matrix' (really a payoff function) that returns a tuple of utilities given a tuple of actions.
					- A linear game has $n^2$ functions $U_{i,j} : A_j \to \mathbb{R}$.
						- How player $i$ values the various actions that player $j$ could take.
						- $U_i(\vec a) = \sum_{j \leq n} U_{i,j}(a_j)$
					- There's only one Nash equilibrium, which is the one where players maximize $U_{i,i}$ and ignore the actions of others.
						- For any joint distribution over player moves, if everyone were to independently randomize instead, with the same marginal probabilities, then expected payoffs would remain the same. Correlated-equilibrium style coordination never matters.
				- application to udt
					- Linear games seem like a natural (if perhaps overzealous) way to simplify the UDT environment space.
						- This idea fits well with UDT 1.0, since linear games allow players to select their actions individually rather than worrying about how others are playing.
							- (But again, an actual linearity assumption may be more than we need, for that conclusion.)
								- Rather than actual linearity, the actions of others could merely fail to reorder our priorities; or even looser, they might reorder things without changing what choices are _best_.
						- A policy is like a joint action, and an environment is like a 'payoff matrix' (payoff function)
							- The space of players is $\mathbb{B}^{<n}$ -- what bitstring you see / the node you're at
							- The space of actions for each is $\mathbb{B}$ (but mixed actions are also possible)
							- A joint (pure) action is just a policy: $\mathbb{B}^{<n} \to \mathbb{B}$
							- 'payoff matrix' is $\pi \mapsto \mathbb{E}_{\pi \bowtie e} [U]$
								- Everyone has the same utility function, so no need to map to lots of them.
								- Following the analogy to linear games, we would like this to decompose to a sum over policy-points.
									- This would be able to capture classic UDT problems, as "what I do matters more to this other branch than it does to me, so all things considered, I should act for the other branch's benefit".
									- However, this seems too restrictive: ordinary markov decision processes require backwards-induction, which linear games don't allow since it would imply policy-points can't be decided without knowing what happens at other policy-points.
					- **affine environment** $e$ is a function of type $[0,1]^{\mathbb{B}^{<n}} \times \mathbb{B}^{<n}  \to [0,1]$, which is affine in its first argument.
						- That is, for all $b$, the function $\pi \mapsto e(\pi, b)$ is affine.
							- That is, $e(\pi, b)= c + \sum_{b'} c_{b'} \pi(b')$
						- In other words, the probability of $b0$ vs $b1$ is a weighted mix of behaviors of other policy-points.
						- Takes about $2^n \cdot 2^n = 2^{2n}$ data to specify; a weight for every pair of bitstrings.
						- $\mathbb{E}_{\pi \bowtie e} [U] =$
							- $\sum_{b \in \mathbb{B}^n}  U(b) \cdot  (\pi \bowtie e)(b)$
							- = $\sum_{b \in \mathbb{B}^n}  U(b) \cdot  \Pi_{i \leq n} f_{b_i}(e(\pi, b|(i-1)))$
								- by $(\pi \bowtie e)(b) = \Pi_{i \leq n} f_{b_i}(e(\pi, b|(i-1)))$
							- = $\sum_{b \in \mathbb{B}^n}  U(b) \cdot  \Pi_{i \leq n} f_{b_i}(c_b + \sum_{b'} c_{b',b} \pi(b'))$
								- by $e(\pi, b)= c + \sum_{b'} c_{b'} \pi(b')$
							- So we see that this is not a linear game; expanding out that product of sums into a sum over products would show different policy-points being multiplied by each other.
							- But it is at least a much-simplified space of possibilities.
				- Low Sensitivity
					- Diff seeks to characterize some sort of `importance measure`, which would say that location x is important to location y. A `UDT trap` would be a location x which cares (for its EV) about what we do at _infinitely many other locations_, sufficiently strongly that we never "learn" the optimal policy for those locations (our behavior forever depends on our prior probability for the 'trap'). So a natural idea is that the "importance measure from a location" should be bounded.
					- Consider non-affine environments, possibly sensitive to mixed actions:
						- $e: [0,1]^{\mathbb{B}^{<n}} \times \mathbb{B}^{<n} \to [0,1]$
						- Given a bitstring $b$, the function $\pi \mapsto e(\pi, b)$ says what happens as our policy changes.
							- If, starting from some specific policy $\pi^*$, lots of policy changes would make a big difference (to the expected continuation at b), then the function is necessarily very steep, ie has a high lipschitz constant in that region.
								- Isn't this not really what we want to ask about? Shouldn't "importance" be defined in EV terms, not in terms of modifying the probability of the next observation?
								- So we should look at $\pi \mapsto \mathbb{E}_{\pi \bowtie e} [U | b]$
							- Given a function of type $[0,1]^{\mathbb{B}^{<n}} \to \mathbb{R}$ (such as $\pi \mapsto e(\pi, b)$ or $\pi \mapsto \mathbb{E}_{\pi \bowtie e} [U | b]$) you can differentiate it at a point (at a given policy) to get an affine function of the same type.
								- This space is isomorphic to $\mathcal{M}^\pm (\mathbb{B}^{<n}) \times \mathbb{R}$, the space of signed measures on $\mathbb{B}^{<n}$, plus a constant to make the affine function.
								- Diff says we can take the absolute value of this measure to make it into an ordinary measure (??) corresponding to our "importance measure".
									- If it's all negative or all positive, this seems fine, but if we've got an event with negative and positive sub-parts, taking the absolute value will not preserve measure properties!
									- Does Diff have some way to take the absolute value of the whole measure, that's different from the absolute value of the individual event-values?
										- > Am treating measures as "things that linearly recieve a function as input and spit out a number". Then the ability to uniquely decompose a measure into a nonoverlapping positive and negative component m=m^+ - m^- lets you go m(f)=m^+(f) + m^-(f) and this defines the "absolute value" measure.
										- But does this have the behavior we want?
											- I think we don't really care how things "add up" here; the measure is just being used to put a number on each branch. So we don't get any weird results due to positive and negative mass adding up rather than cancelling out.
												- This makes sense if we anchor on b and ask what branches c are important to the outlook at b. We are essentially looking at the policy-points at c, not c itself. We don't care about the importance of c1 and c0 adding up to the importance of c, for example -- this constraint doesn't make sense. The policy-points at c1 and c0 might both be very important without c being important at all.
												- But if we anchor at c and ask which branches b care about what happens at c a lot, then because we're looking at forward-facing care, b's measure has an important relationship with the measure at b1 and b0.
												- Hm, maybe this isn't really important, though. We can just measure the importance of c to b in terms of shifting expected value. We don't need c to be considered important if c can make things in b1 look really good but can make things in b0 look really bad. We can just say it's unimportant to b but really important to b1 and b0.
								- Diff says that when the importance measure of a location c (according to b) times the probability of b is notably higher than the probability of , then the decision at c will be dominated by retrocausal or cross-branch influences rather than causal ones. (backward-looking rather than forward-looking considerations.)
								- Diff says that affine environments necessarily have impact measures which sum to 1 or less, so, no udt-traps.
									- This makes intuitive sense to me for Diff's weird notion of importance, but I'm less sure about EV-based importance.
				- Objective Reality?
					- Where did we get $e$ from?
						- There's not really an objectively correct $e$ to describe the environment (particularly not one which contains uncertainty).
						- Our probability estimates can improve over time, both as a result of observations, and as a result of thinking longer.
						- Also, probability estimates can _become meaningless_ -- down branches that don't happen, the probabilities "don't really mean anything", at least after we find out they're not happening.
						- Similarly, the environment's reaction to policies we don't choose "doesn't mean anything".
					- Stipulate that at each location there's an 'epistemic state' $\mathbb{S}_b$. We'll leave this unformalized at first, but gradually home in on how it must behave.
						- I would, of course, have loosened up the observation-model at the same time.
					- > We'd ideally like to have a view of UDT as a small simple control algorithm at the core of an agent, that is non-stupidly wielding the results of computational powers much greater than itself.
						- Corollary 1: 'epistemic states' are like an oracle we can access. We are OK with lots of computation going into the epistemic state; we don't count that against UDT. We must query the epistemic states via some interface.
						- Corollary 2: Oracle *queries* count against UDT's time-complexity, though; so we want to minimize those.
						- Corollary 3: We should get as much computation as we can from the epistemic state (via queries) and do as little computation as we can inside the UDT algorithm itself.
						- Corollary 4: As a special case of the previous, the UDT algorithm definitely isn't supposed to compute the epistemic state itself.
							- (This seems to rule out `FixDT`)
					- Claim 5: the UDT algorithm is only allowed to query the current and previous epistemic states. No future ones (we haven't computed that far yet) and no cross-branch ones (they don't actually exist).
					- So the computational model is something like this:
						- We have oracle access to epistemic states.
						  logseq.order-list-type:: number
						- We want to make only poly(|b|) queries.
						  logseq.order-list-type:: number
						- We should run in overall poly(|b|) time.
						  logseq.order-list-type:: number
						- UDT(b) is only permitted to query $\mathbb{S}_c$ for $c$ prefix of or equal to $b$
						  logseq.order-list-type:: number
				- Cross-Branch Effects?
					- Elaborating on the idea that UDT(d) should not try to access epistemic states cross-branch to d:
						- Let's say that $S_c$ is inconsistent with d but 'smaller' such that UDT(d) could compute it while remaining efficient. For concreteness, S_c is "a world where pi is different".
						- d is a prefix of both c and b.
						- From the perspective of d, if the computation of $S_c$ _is itself entangled with digits of pi_, then UDT(b), using this computation, will be _systematically incorrect_ about what $S_c$ looks like, from the perspective of d.
							- This seems like a correct and significant argument.
								- But it also seems like there are a lot of potential subtleties involved in spelling it out further.
								- In an LI version of this, "the market state if it sees counterfactual 
								  digits of pi" is not a good approximation of "what would happen if pi 
								  were different" (because there will be traders who can compute pi 
								  correctly internally, even if the ones who use such computations to 
								  explicitly bet about pi get killed -- but it seems like the "correct 
								  hypothetical" has those internal computations going differently).
								- A much better approximation of the counterfactual (and provisionally, all there "really is" to the idea) is *what an early market state would have to expected a later market state to look like, if pi had turned out to be different than it did*.
									- For example, an early state might expect that if the digits of pi turn out to be 333333... after some point, then the market will spot the pattern and continue predicting 3s into the future.
									- This depends, of course, on which earlier state we look at. And it'll also be a distribution, rather than a point-estimate.
								- Seems like we could slow down and try to spell things out better.
									- We're imagining there is some kind of _computation_ of $S_c$, much like "run the same logical inductor on a different deductive process".
										- We can call this $\text{comp}_{S_c}$.
									- Then there's a _subjective expectation of what_ $S_c$ _will be like_ from d. This is basically "what $S_d$ thinks about $S_c$". We can further distinguish course-grained expectations (beliefs about short propositions which talk about $S_c$) and fine-grained expectations (a full probability distribution over what $S_c$ looks like). Plausibly, $S_d$ will only include course-grained expectations.
									- Supposing that $S_d$ has reasonable self-trust properties about $S_b$, it should think that $S_b$ will predictably know better _about the computation_ $\text{comp}_{S_c}$. But it may think that this is a poor estimate of $S_c$
										- Well, more specifically, _if_ $S_b$ is the _real_ continuation, with access to _real_ computations, $S_d$ will expect it to be correct about that computation. Which is to say, if $b$ is the true nth observation. But absent that knowledge, $S_d$ thinks of $S_b$ as one of many branches, only one of which has true access to "how computations go".
										- "the true $S_c$" may be a poor articulation of what d disagrees about. More importantly, it disagrees about decisions, right? Or, terms which go into decision computations.
											- But there, I'm just pushing my own partition-based decomposition of UDT's calculation.
					- Diff argues that it seems sorta plausible that of the common ancestors of b and c, the latest common ancestor is the important one, for self-trust type reasons. So Diff argues that the latest common ancestor is the one to make happy when thinking about cross-branch effects between b and c.
						- Diff now recants on this view.
							- Diff's counterexample:
								- counterlogical mugging. Branches: give, get, prior, informed. 'get' is good if and only if 'give' branch chooses to give. Prior thinks it's a good idea to pay up. 'informed' has a good guess about the value of the logical coin and doesn't think it is worth paying up.
							- My counterexample:
								- Still counterlogical mugging, but we make the argument that the agent should "think exactly as long as Omega" to make the decision (more precisely, behave as if it's exactly that updateful).
					- Need the insights from affine environments:
						- It's important to be able to ask how one location impacts another without dragging in the rest of the policy, for UDT to do well.
						  logseq.order-list-type:: number
						- Impact measures should sum to 1 or less.
						  logseq.order-list-type:: number
					- So let's just assume those things of the epistemic state.
					- Now, divide the impact of UDT(b)'s decision into three classes:
						- **acausal**: impacts on inconsistent branches, like counterfactual mugging. Diff says we should consult the latest common ancestor here.
						- **retrocausal**: impacts on the prefix of the home branch. Here, we consult the prefix branch... which is, by the way, also the latest common ancestor.
						- **causal**: impacts on the home branch and its extensions. Here we have to just consult the home branch, since we can't compute further... again, the latest common ancestor.
					- So the conclusion is that we always look to the latest common ancestor! This conclusion is intriguing but wrong in several ways.
						- As discussed earlier, the argument that we should look to the latest common ancestor for cross-branch stuff is wrong. 
						  logseq.order-list-type:: number
						- Diff's three classes of decision don't seem to form a nice _decomposition_ of the overall UDT computation. It's not like UDT cares about a weighted sum over all branches. Rather, UDT cares about a weighted sum over any _partition_.
						  logseq.order-list-type:: number
				- Expected Utility as Complexity Shield
					- Utility function gets tossed out the window, but we still need some notion of utility.
					- Just require epistemic self-trust properties.
					- Let's say you're at $b$, which starts with a 0, trying to compute UDT(b).
						- You want to know how your action impacts locations starting with 1.
						- So you want to ask S_\empty about this.
						- If U was an actual function, you'd have to S_\empty exponentially many things to figure out how to evaluate U.
							- (You'd have to ask the probability of c0 vs c1 for every c that starts with 1.)
					- My general comment here is that this appears to miss the hard part: asking S_\empty about UDT(b)=a is hard because b can be too long, so that S_\empty doesn't know how to have opinions about it directly (although S_\empty does have many relevant small opinions, and would be upset to know that those small opinions were ignored, in a tiling-relevant sense).
					-
			-
		- **UDT 1.01 + Dynamic Consistency Arguments**
			- !`UDT_1.01_1700067233961_0.pdf`
			- Blow-by-blow:
				- `Reactables vs Seeables`
					- `reactable` -- the notion of 'observation' relevant to `policy`; things which you can explicitly plan how to react to, regarding your actions as a function of those things. Things in your explicit representation of the-state-you're-in when you consider a policy-point.
						- Seems very similar to the `cartesian frames` definition of observation.
					- `seeable` -- any kind of information/computation which goes into computing an agent's action/policy. In classic UDT, the calculated EV of a policy[-point] would be an important seeable, but not a reactable.
						- Seeables are a bit ineffable; I mean, it's kind of subjective which subcomputations make up a computation. But we could think of it as causal nodes which make up a causal graph leading to the output. Or, similarly, we could apply `finite factored sets`.
					- One way of framing the problem of `logical updatelessness` or `computational updatelessness` is that reactables do not in general equal seeables. If digits of pi are not treated as reactables, then you'll have a hard time when you encounter a `counterlogical mugging`.
						- Another key part of `computational updatelessness` is that _seeables increase over time_, as computation proceeds. This is why we don't want to just set a policy at the beginning of time; we can't actually compute everything at the beginning of time. We need to compute our policy incrementally, like `UDT 1.0` and unlike `UDT 1.1`.
							- Arguably, reactables are *not* the sort of thing that changes over time. But perhaps our *perspective* on what is reactable could change over time.
								- Following a `UDT 1.0` sort of idea, we don't need to describe the situation we're in until we find ourselves in it; so it isn't really necessary to define reactables at the beginning of time. What-is-reactable need not become seeable until the point where we make the relevant decision.
					- Diff argues that there's a sort of infinite regress: you can always do better (at least, in some weird new decision problems, and ignoring computational cost) by turning more of your seeables into reactables, but doing so blows up the amount of computation you need, creating more seeables.
						- Can we define `counterlogical mugging on the EV of an action`?
						- This ultimately relates to `small vs large beliefs` -- in the current author-Soto synthesis UDT, small beliefs are reactables, while some large beliefs end up being seeables. Can't make a policy depend explicitly on large beliefs; but, need large beliefs to evaluate policies.
					- Diff argues that [tiling](`tiling agents`) problems apply to seeables as well as reactables. UDT is dynamically consistent about how it reacts to reactables, by construction, but it had better react appropriately to seeables as well, else there's an incentive to self-modify.
						- To the extent that we can parse seeables as _beliefs_, this suggests that seeables which are not reactables had better be _updateless_ beliefs. For example, the EV of a policy-point had better check out from an updateless perspective.
							- But this implies that we need to define what it means for beliefs we compute later on to nonetheless be "updateless".
				- `UDT 1.01` Setting, Notation, and Motivation
					- $\mathcal{O}$ atomic observations
					- $\mathcal{A}$ actions; baseline action $i$ (though the choice here won't matter)
					- Reactables: $\mathcal{O}^{<\omega}$, finite strings of atomic observations. Elements of this are called histories, $h$
					- $\mathcal{O}^{\geq h}$ is the set of all finite extensions of history $h$
					- $h_m$ denotes the $m$th atomic observation in $h$
					- $h_{m:n}$ refers to a substring
					- $h_{1:0}$ is the empty string, also $\empty$
					- At each history, you may select a probability over actions (although UDT1.01 will be deterministic)
						- so policies $\pi : \mathcal{O}^{<\omega} \to \Delta \mathcal{A}$
					- The assumption that $\mathcal{O}$ and $\mathcal{A}$ don't depend on history is for notational convenience.
					- No weird policy correlation stuff; in spirit, $\pi(h): \Delta \mathcal{A}$ is optimizing $\mathbb{E}_\empty [U|\pi(h)=a]$.
					- At each $h$, you receive an "epistemic state" which contains (at least) the following:
						- $\hat{\mathbb{P}}_h : \Delta \mathcal{O}$, a "baseline" distribution over what the next atomic observation will be. Think of it as a vector.
							- "baseline" in the sense of being consistent with some notion of the agent's expectations of what they'll do, _not_ the "baseline action" $i$
							  id:: 65789376-54f7-4614-bb2f-98a6918fcf9e
						- $\hat{\mathbb{E}}_h [U|\_] : \mathcal{O} \to [0,1]$, a "baseline" conditional expected utility for each observation. Think of it as a vector.
							- ((65789376-54f7-4614-bb2f-98a6918fcf9e))
						- $\hat{\Delta}^\mathbb{P}_h : \mathcal{O}^{\geq h} \to (\mathcal{O} \times \mathcal{A} \to [-1, 1])$, a "probability influence function"
							- Given a decision point $h'$ in the future of $h$, $\hat{\Delta}^\mathbb{P}_h (h')$ returns a function which scores observation-action pairs.
							- The score of an observation-action pair tells us how the probability of observation $o$ shifts as we replace $\epsilon$ probability of the baseline action $i$ with $\epsilon$ probability of the new action $a$ instead.
								- If we shift entirely from $\pi(h')=i$ to $\pi(h')=a$, the probability $ho|h$ should change by $\hat{\Delta}^\mathbb{P}_h (h', o, a)$.
									- If $\epsilon$ of your probability moves from $i$ to $a$, the probability should be perturbed by $\epsilon \hat{\Delta}^\mathbb{P}_h (h', o, a)$.
										- So there's an assumption that changes to probabilities of actions result in *linear* changes to probabilities of observations.
											- Is it really just locally linear, like a derivative?
												- Diff replies: 
												  > More similar to the tangent line from the current point. The environment can react nonlinearly to action probabilities but it should react approximately linearly to perturbations in action probabilities.
								- The baseline action $i$ is a notational choice, not essential to the algorithm. It would be redundant to compare each action against _every_ other action.
							- $\hat{\Delta}^\mathbb{P}_h (h', o, \mu)$ is an abbreviation for $\mathbb{E}_{a \sim \mu} [\hat{\Delta}^\mathbb{P}_h (h', o, a)]$
						- $\hat{\Delta}^\mathbb{E}_h : \mathcal{O}^{\geq h} \to (\mathcal{O} \times \mathcal{A} \to [-1, 1])$, a "utility influence function"
							- How does this particular decision in the future shift _expected utilities_ around (analogous to the previous thing which dealt with how probabilities get pushed around)?
							- $\hat{\Delta}^\mathbb{E}_h (h', o, \mu)$ is an abbreviation for $\mathbb{E}_{a \sim \mu} [\hat{\Delta}^\mathbb{E}_h (h', o, a)]$
						- $\hat{\Delta}^{\mathbb{E}, f}_h : \mathcal{O}^{\geq h} \to (\mathcal{O} \times \mathcal{A} \to [-1, 1])$, an "expected future influence function"
							- $\hat{\Delta}^{\mathbb{E}, f}_h (h', o, a)$ is your prediction, at position $h$, of the quantity (seeable at $ho$):
								- $\sum_{o'} \big( \hat{\mathbb{P}}_{ho}(o') \cdot \hat{\Delta}^\mathbb{E}_{h o} (h', o', a) + \hat{\Delta}^\mathbb{P}_{h o} (h', o', a) \cdot  \hat{\mathbb{E}}_{ho} [U|o']  \big)$
									- > So, $ho$ is where you're at. $o'$ is the upcoming observation. $h'$ is where 
									  the decision will end up being made. So it's saying "sum over 
									  observations of (probability of $o'$ x perturbation of expected utility 
									  conditional on $o'$ from playing a at position $h'$) + (perturbation of 
									  probability of $o'$ from playing a at position $h'$ x expected utility 
									  conditional on $o'$)"
									- $\hat{\mathbb{P}}_{ho}(o') \cdot \hat{\Delta}^\mathbb{E}_{h o} (h', o', a)$
										- $\hat{\mathbb{P}}_{ho}(o')$ is the baseline distribution of $o'$ next, after the history $ho$.
										- $\hat{\Delta}^\mathbb{E}_{h o} (h', o', a)$ is the utility influence according to $ho$, of performing action $a$ in (future) context $h'$, on potential outcome $o'$.
									- $\hat{\Delta}^\mathbb{P}_{h o} (h', o', a) \cdot  \hat{\mathbb{E}}_{ho} [U|o']  \big)$
										- $\hat{\Delta}^\mathbb{P}_{h o} (h', o', a)$: the probability influence at $ho$, of action $a$ in the context $h'$, on potential outcome $o'$.
										- $\hat{\mathbb{E}}_{ho} [U|o']$: the "baseline" expected utility for $o'$ coming after $ho$
									- This quantity is "basically the derivative of expected utility".
					- The last three pieces of data (the three $\hat\Delta$ functions: probability influence, utility influence, expected future influence) have some niceness constraints:
						- 1: For all $h$, $h' \supseteq h$, and all three influence functions, we have:
							- $\hat{\Delta}_h (h', o, i) = 0$
							- This just says that there shouldn't be a difference between adding a little bit of $i$ and adding a little bit of $i$.
						- 2: For all $h$, $h' \supseteq h$, and $a$,
							- $\sum_{o \in \mathcal{O}} \hat{\Delta}^\mathbb{P}_h (h', o, a)=0$
							- This says an action's perturbations have to keep $ho|h$ a probability distribution.
						- 3: For all $h$, $a_1$, $a_2$, and all influence functions, we have:
							- $\sum_{o, h' \supseteq h} \Big| \hat{\Delta}_h (h', o, a_1) - \hat{\Delta}_h (h', o, a_2) \Big| \leq 1$
							- This is the thing about bounding influence to ensure learning.
							- > Let’s call a ”fate” the ability to switch the probability of an observation entirely from one observation to a different one. This condition is saying that in expectation across all the future branches, you’ll be able to affect the ”fate” of what happens now only once.
							- We can replace 1 with C, but then we need some extra "C decays fast enough" across the other variables?
				- Dynamic Consistency "Proof"
					-
			-
	- `2023-11-15` UDT write-up?
		- # Updateless Decision Theory Without Cheating
			- ## Classic UDT
				- ### Setup
				- ### Problems where updatelessness is correct are a superset of problems where updatefulness is correct.
				- ### Tiling
				- ### Importance Measures & Learning
				- ### Subjective Utility vs Reinforcement Learning
				- ### Learning Correct (Updateful) Counterfactuals
				- ### The Partition Assumption
			- ## Reasons to Generalize
				- ### Seeables vs Reactables
					- #### Seeables exceed reactables.
					- #### For dynamic consistency, seeables (that aren't reactables) need to be "valid beliefs" from the updateless perspective.
				- ### Radical Probabilism
				- ### Realizability
				- ### Multiagent Modeling
				- ### Calibrated vs Uncalibrated Priors
				- ### Cooperative Oracles & Ignoring Needy Branches
				- ### Geometric Rationality
				- ### Addition of Hypotheses
				- ### FixDT and Epistemic Decision Theory
				- ### Rewards Are Traders, Evidence Is Traders
				- ###
			- ## Beliefs As Observations
				- ### The Problem of Radical Updatelessness
				- ### What Computational Updatelessness Should Be
					- #### The Branch Decomposition
					- #### Thinking: Short and Long
					- #### Example: Don't Outthink Omega in Counterlogical Mugging
					- #### Alternate Branches Aren't Real
						- (my version of diff's argument about early self disagreeing with late self estimates of what other branches would have looked like)
					- #### The Essence of Computational Updatelessness
						- (my version of diff's points about throwing away the concept of a prior, diff's points about keeping udt simple and leaving the complexity to the epistemics, soto's points about what logical updatelessness needs to be)
				- ### Multigrain Models
				- ### Markets Over Time
					- #### Universal Induction
				- ### Bayesian Logical Induction
					- #### Basic Construction
					- #### Decomposition-Invariance
					- #### Rejecting Alternatives
				- ### Radical Value Change
				- ### Decision Problems
					- #### Equivalence between game-tree nodes and computations.
					- #### The decision problem is in the prior.
				- ### Real Marginalization
				- ### Hypothetical Marginalization
				- ### Universal Instantiation
				- ### Correct Updateless Behavior \sup Correct Updateful Behavior
				- ### Worked Examples
				- ### Learning?
				- ### Optimality?
				- ###
			- ## Generalizing Critch
				- ###
		-
		-
	-