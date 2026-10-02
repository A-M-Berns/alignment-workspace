---
title: "Troll Bridge"
author: abramdemski
date: 2019-08-23
url: https://www.lesswrong.com/posts/hpAbfXtqYC2BrpeiC/troll-bridge-5
karma: 88
comments: 59
fetched: 2026-09-03 via LessWrong GraphQL API (html2text conversion; math may need re-setting)
---

# Troll Bridge

_All of the results in this post, and most of the informal observations/interpretations, are due to Sam Eisenstat. I think the Troll Bridge story, as a way to make the decision problem understandable, is due to Tsvi; but I'm not sure._

## Pure Logic Version

Troll Bridge is a decision problem which has been floating around for a while, but which has lacked a good introductory post. The [original post](https://agentfoundations.org/item?id=369) gives the essential example, but it lacks the "troll bridge" story, which (1) makes it hard to understand, since it is just stated in mathematical abstraction, and (2) makes it difficult to find if you search for "troll bridge".

The basic idea is that you want to cross a bridge. However, there is a troll who will blow up the bridge with you on it, _**if**_ (and only if) you cross it "for a dumb reason" — for example, due to unsound logic. You can get to where you want to go by a worse path (through the stream). This path is better than being blown up, though.

We apply a Löbian proof to show not only that you choose not to cross, but furthermore, that your counterfactual reasoning is confident that the bridge would have blown up if you had crossed. This is supposed to be a counterexample to various proposed notions of counterfactual, and for various proposed decision theories.

![](https://i.imgur.com/tS3A6fQ.png)

The pseudocode for the environment (more specifically, the utility gained from the environment) is as follows:

![](https://i.imgur.com/6T3nIwk.png)

IE, if the agent crosses the bridge and is inconsistent, then U=-10. (□⊥ means "PA proves an inconsistency".) Otherwise, if the agent crosses the bridge, U=+10. If neither of these (IE, the agent does not cross the bridge), U=0.

The pseudocode for the agent could be as follows:

![](https://i.imgur.com/clODkKp.png)

This is a little more complicated, but the idea is supposed to be that you search for every "action implies utility" pair, and take the action for which you can prove the highest utility (with some tie-breaking procedure). Importantly, this is [the kind of proof-based decision theory which eliminates spurious counterfactuals in 5-and-10 type problems](https://www.alignmentforum.org/posts/5bd75cc58225bf0670374e8f/an-optimality-result-for-modal-udt). It isn't that easy to trip up with Löbian proofs. _(Historical/terminological note: This decision theory was initially called MUDT, and is still sometimes referred to in that way. However, I now often call it proof-based decision theory, because it isn't centrally a UDT. "Modal DT" (MDT) would be reasonable, but the modal operator involved is the "provability" operator, so "proof-based DT" seems more direct.)_

Now, the proof:

![](https://i.imgur.com/L6fJu7J.png)

  * Reasoning within PA (ie, the logic of the agent): 
    * Suppose the agent crosses. 
      * Further suppose that the agent proves that crossing implies U=-10. 
        * Examining the source code of the agent, because we're assuming the agent crosses, either PA proved that crossing implies U=+10, or it proved that crossing implies U=0.
        * So, either way, PA is inconsistent -- by way of 0=-10 or +10=-10.
        * So the troll actually blows up the bridge, and really, U=-10.
      * Therefore (popping out of the second assumption), if the agent proves that crossing implies U=-10, then in fact crossing implies U=-10.
      * By Löb's theorem, crossing really implies U=-10.
      * So (since we're still under the assumption that the agent crosses), U=-10.
    * So (popping out of the assumption that the agent crosses), the agent crossing implies U=-10.
  * Since we proved all of this in PA, the agent proves it, and proves no better utility in addition (unless PA is truly inconsistent). On the other hand, it will prove that not crossing gives it a safe U=0. So it will in fact not cross.



The paradoxical aspect of this example is not that the agent doesn't cross -- it makes sense that a proof-based agent can't cross a bridge whose safety is dependent on the agent's own logic being consistent, since proof-based agents can't know whether their logic is consistent. Rather, the point is that the agent's "counterfactual" reasoning looks crazy. _(However, keep reading for a version of the argument where it**does** make the agent take the wrong action.)_ Arguably, the agent should be uncertain of what happens if it crosses the bridge, rather than certain that the bridge would blow up. Furthermore, the agent is reasoning as if it can control whether PA is consistent, which is arguably wrong.

In [a comment](https://www.alignmentforum.org/posts/hpAbfXtqYC2BrpeiC/troll-bridge-5#4AQdDtGEfzs8Prb9d), Stuart points out that this reasoning seems highly dependent on the code of the agent; the "else" clause could be different, and the argument falls apart. I think the argument keeps its force:

  * On the one hand, it's still very concerning if the sensibility of the agent depends greatly on which action it performs in the "else" case.
  * On the other hand, we can modify the troll's behavior to match the modified agent. The general rule is that the troll blows up the bridge if the agent would cross for a "dumb reason" -- the agent then concludes that the bridge would be blown up if it crossed. I can no longer complain that the agent reasons as if it were controlling the consistency of PA, but I can still complain that the agent thinks an action is bad because that action indicates its own insanity, due to a troublingly circular argument.



## Analogy to Smoking Lesion

One interpretation of this thought-experiment is that it shows proof-based decision theory to be essentially a version of EDT, in that it has EDT-like behavior for Smoking Lesion. The analogy to Smoking Lesion is relatively strong:

  * An agent is at risk of having a significant internal issue. (In Smoking Lesion, it’s a medical issue. In Troll Bridge, it is logical inconsistency.)
  * The internal issue would bias the agent toward a particular action. (In Smoking Lesion, the agent smokes. In Troll Bridge, an inconsistent agent crosses the bridge.)
  * The internal issue also causes some imagined practical problem for the agent. (In Smoking Lesion, the lesion makes one more likely to get cancer. In Troll Bridge, the inconsistency would make the troll blow up the bridge.)
  * There is a chain of reasoning which combines these facts to stop the agent from taking the action. (In smoking lesion, EDT refuses to smoke due to the correlation with cancer. In Troll Bridge, the proof-based agent refuses to cross the bridge because of a Löbian proof that crossing the bridge leads to disaster.)
  * We intuitively find the conclusion nonsensical. (It seems the EDT agent should smoke; it seems the proof-based agent should not expect the bridge to explode.)



Indeed, the analogy to smoking lesion seems to strengthen the final point -- that the counterfactual reasoning is wrong.

I've come to think of Troll Bridge as "the real smoking lesion", since I'm [generally not satisfied with how smoking lesion is set up](https://www.lesswrong.com/posts/5bd75cc58225bf0670375452/smoking-lesion-steelman).

But is proof-based decision theory _really_ a version of EDT? I think there's more to say about the analogy, but a simple explanation is this: both EDT and proof-based decision theory evaluate actions by adding them to the knowledge base and seeing what the world looks like under that additional assumption. Or, to put it differently, proof-based DT reasons about actions as if they're observations. That's the fundamental idea of evidential decision theory.

Still, as good as the analogy might be, you still probably shouldn't be convinced until you've seen the Troll Bridge defeat _real_ EDT.

## Probabilistic Version

For the purely logical version, I said that we can't fault the conclusion (because the agent can't prove that it is safe to cross the bridge) – only the _reasoning_ is being critiqued. However, the probabilistic version better demonstrates the severity of the reasoning error; it illustrates an EDT agent making what seems to be an outright mistake.

It's reasonable to avoid crossing the bridge if you're only thinking about provable results. But we might expect an agent who balances risks and rewards would decide to cross, so long as it believes the probability of PA being inconsistent is low. Thus turns out not to be the case.

Here's the setup.

Suppose that the agent uses a probability distribution which "respects logic" in the sense that it assigns probability zero to anything which is logically refutable. (This assumes logical omniscience. I'll drop that assumption later.)

The agent is as follows: _if P(cross)=0, cross; if P(¬cross)=0, don't cross; else, take the action with highest expected utility, breaking ties by not crossing._ The idea is that we are trying to take the highest-expected-utility action; however, we must handle cases where this isn't well-defined. Choosing to take an action when the probability of the action is zero guarantees that the agent can never prove its own action; it is a version of the chicken rule. Breaking ties by not crossing is arbitrary, but gives the simplest version of the example, because this choice reduces the number of cases we need to check.

The troll is as follows: _if the agent crosses the bridge due to the P(cross)=0 clause, blow up the bridge._

Reasoning in the logic of the agent:

  * Suppose □(A=cross→U=−10)
    * Suppose A=cross
      * Examining the agent, either crossing had higher expected utility, or P(cross)=0. But we assumed □(A=cross→U=−10), so it must be the latter. So the bridge gets blown up.
    * Therefore, A=cross→U=−10.
  * Therefore, □(A=cross→U=−10)→(A=cross→U=−10)



Thus, by Löb's theorem, we see that □(A=cross→U=−10).

Therefore, since the agent is certain of things which are provable, the agent assigns expected value -10 to crossing. Since the expected value of the other action will always be higher than this, and since we know the agent doesn't ever really enter into the P=0 conditions, the agent will choose not to cross. □

Notice that this reasoning did not depend much on the values 10, 0, and -10. The utility of the bridge getting blown up could be -0.000001, and the agent still won't cross. _It isn't weighing the risk; it's decided that the worst outcome is inevitable._ In the case of proof-based agents, I said that the overall decision not to cross was understandable, since proof-based agents are unable to weigh the risks. A probabilistic agent, however, should intuitively be able to say "I don't know whether the bridge will get blown up, because it involves reasoning about properties of myself which I'm fundamentally uncertain about; but, the odds look decent." But that's not what happens: instead, it is sure that crossing is unfavorable, _no matter what overall probability it assigns to P(A=cross)=0_.

So, in this case we conclude that the Troll Bridge example results in a chicken-rule-based agent taking the wrong action overall. The agent shouldn't be sure that it would cross "for the right reason" (it should assign some probability to P(A=cross)=0, since it can't know that its own logic is consistent). However, intuitively, it should be able to assign some probability to this, and balance the risks. If the downside risk is U=-0.000001, and the probability it assigns to its logic being consistent is not similarly small, it should cross -- and in doing so, it would get +10.

As mentioned for the proof-based agent, the agent's code is a bit arbitrary, and it is worth asking how important the details were. In particular, the default in the case of a tie was to not cross. What if the default in case of a tie were to cross?

We then modify the troll's algorithm to blow up the bridge if and only if P(A=cross)=0 **or** there is a tie. The proof then goes through in the same way.

Perhaps you think that the problem with the above version is that I assumed logical omniscience. It is unrealistic to suppose that agents have beliefs which perfectly respect logic. (Un)Fortunately, the argument doesn't really depend on this; it only requires that the agent respects proofs which it can see, and eventually sees the Löbian proof referenced.

## Random Exploration

The frustrating thing about Troll Bridge is that it seems like the agent could just cross the bridge, and things would be fine. The proof that things _wouldn't_ be fine _relies on the fact that the agent accepts that very proof as sufficient reason_ ; so can't we just ignore that kind of proof somehow?

One thing you might try is to consider a learning agent, and force random exploration so the agent just crosses the bridge sometimes. If the agent crosses the bridge, it should be able to see that it's safe, right?

However, we have to ask: what's the appropriate version of Troll Bridge for the exploring agent? Remember I said that the basic idea of Troll Bridge is that the troll blows up the bridge if the agent crosses "for a dumb reason" -- ie, for a reason other than "crossing is a good idea". Random exploration falls into this category.

Furthermore, random exploration is really closely analogous to the chicken rule. Consider:

  * (A) The first chicken rule I mentioned: if you prove that you don't take an action, you immediately take it.
  * (B) The second chicken rule mentioned: if P(A)=0, then do A.
  * (C) Epsilon-chicken: if P(A)<epsilon, then do A.
  * (D) Epsilon-exploration: randomly do A with probability epsilon.



(A) is very similar to (B) if the probability distribution respects proofs in the way I mentioned previously; if the probability distribution has the further property of assigning positive probability to anything not disproven, then they're exactly the same. (C) is a natural generalization of (B). (B) tells us what to do when the EDT decision rule isn't well-defined (we can't condition on probability zero events). (C) generalizes this by treating small-probability events in the same way (we might expect our conditional beliefs to be bad for small-probability events, since we presumably don't have much experience with them; so we treat it as if it's the undefined case). (B) ensures there are no zero-probability actions, which means we don't actually ever have to deal with the EDT decision rule being non-well-defined; similarly, (C) ensures no action is almost surely never taken, which helps ensure that our conditional expectations for all actions are empirically grounded.

(C) and (D) are very similar; (C) just supplies pseudorandomness vie the agent's own probabilities. Whenever the agent is too confident about what it does, it does something else. This makes the randomization unpredictable _too the agent_. (D) supplies randomness from an external source instead.

So we have a chain connecting the chicken rule to random exploration.

(Another way of thinking about the similarity: The chicken rule ensures that there are models of the agent's beliefs in which each action is taken, so that the agent can have sensible logical reasoning about each alternative. Epsilon-exploration ensures that the empirical experiences of the agent include all of the actions, so that the agent can have reasonable empirical estimates of consequences of each action.)

OK. So Troll Bridge for an exploring agent should blow up the bridge on exploration, _or_ if PA is inconsistent. An agent could look like this:

  * With small probability, explore. 
    * If exploring, flip a coin to cross or not cross.
  * If P(cross)=0, cross.
  * If P(¬cross)=0, don't cross.
  * Otherwise, take the max-expected-value action, breaking ties randomly.



I'm still assuming that the agent's probability distribution respects proofs, as before. I'm also assuming this agent is playing the game repeatedly, and learning. I also must assume that the agent has found Now, the agent reasons:

  * Suppose □(cross → u=-10) for a particular round. 
    * Further suppose I crossed on that round. 
      * By the first supposition, I knew the payout of crossing to be low; and I must also have known that the payout of not crossing is higher, since I can prove that. Since I can prove what both payouts are, the expected values must equal those, unless PA is inconsistent (in which case P(cross)=0 anyway, since my beliefs respect proofs). So I can only be crossing the bridge for two reasons -- either this is an exploration round, or P(cross)=0.
      * In either case, crossing the bridge yields payout u=-10.
    * Therefore, cross → u=-10 in fact.
  * So □(cross → u=-10) → (cross → u=-10).



Since the agent proves that a proof of crossing being bad implies crossing is actually bad, the agent further must prove that crossing is bad in fact, by Löb.

I did this for the logically omniscient case again, but as before, I claim that you can translate the above proof to work in the case that the agent's beliefs respect proofs it can find. That's maybe a bit weird, though, because it involves a Bayesian agent updating on logical proofs; we know this isn't a particularly good way of handling logical uncertainty.

We can use logical induction instead, using an epsilon-exploring version of LIDT. We consider LIDT on a sequence of troll-bridge problems, and show that it eventually notices the Löbian proof and starts refusing to cross. This is even more frustrating than the previous examples, because LIDT might successfully cross for a long time, apparently learning that crossing is safe, and reliably gets +10 payoff. Then, one day, it finds the Löbian proof and stops crossing the bridge!

That case is a little more complicated to work out than the Bayesian probability case, and I omit the proof here.

## Non-examples: RL

On the other hand, consider an agent which uses random exploration but doesn't do any logical reasoning, like a typical RL agent. Such an agent doesn't need any chicken rule, since it doesn't care about proofs of what it'll do. It still needs to explore, though. So the troll can blow up the bridge whenever the RL agent crosses due to exploration.

This obviously messes with the RL agent's ability to learn to cross the bridge. The RL agent might never learn to cross, since every time it tries it, it looks bad. So this is sort of similar to Troll Bridge.

However, I think this isn't really the point of Troll Bridge. The key difference is this: the RL agent can get past the bridge if its prior expectation that crossing is a good idea is high enough. It just starts out crossing, and happily crosses all the time.

Troll Bridge is about the inevitable confidence that crossing the bridge is bad. We would be fine if an agent decided not to cross because it assigned high probability to PA being inconsistent. The RL example seems similar in that it depends on the agent's prior.

We could try to alter the example to get that kind of inevitability. Maybe we argue it's still "dumb" to cross only because you start with a high prior probability of it being good. Have the troll punish crossing _unless the crossing is justified by an empirical history of crossing being good_. Then RL agents do poorly no matter what -- no one can get the good outcome in order to build up the history, since getting the good outcome _requires_ the history.

But this still doesn't seem so interesting. You're just messing with these agents. It isn't illustrating the degree of pathological reasoning which the Löbian proof illustrates -- **of course** you don't put your hand in the fire if you get burned every single time you try it. There's nothing wrong with the way the RL agent is reacting!

So, Troll Bridge seems to be more exclusively about agents who do reason logically.

## Conclusions

All of the examples have depended on a version of the chicken rule. This leaves us with a fascinating catch-22:

  * We need the chicken rule to avoid [spurious proofs](https://www.alignmentforum.org/s/Rm6oQRJJmhGCcLvxh/p/zcPLNNw4wgBX5k8kQ). As a reminder: spurious proofs are cases where an agent would reject an action if it could prove that it would not take that action. These actions can then be rejected by an application of Löb's theorem. The chicken rule avoids this problem by ensuring that agents cannot know their own actions, since if they did then they'd take a different action from the one they know they'll take (and they know this, conditional on their logic being consistent).
  * However, Troll Bridge shows that the chicken rule can lead to another kind of problematic Löbian proof.



So, we might take Troll Bridge to show that the chicken rule does not achieve its goal, and therefore reject the chicken rule. However, this conclusion is very severe. We cannot simply drop the chicken rule and open the gates to the (much more common!) spurious proofs. We would need an altogether different way of rejecting the spurious proofs; perhaps a full account of logical counterfactuals.

Furthermore, it is possible to come up with variants of Troll Bridge which counter some such proposals. In particular, Troll Bridge was originally invented to counter proof-length counterfactuals, which essentially [generalize chicken rules](https://agentfoundations.org/item?id=369), and therefore lead to the same Troll Bridge problems).

Another possible conclusion could be that Troll Bridge is simply too hard, and we need to accept that agents will be vulnerable to this kind of reasoning.

---

## Comments (59, threaded, chronological)

**Jiro** (2019-08-23, karma 1):
How can you (in general) conclude something by examining the source code of an agent, without potentially implicating the Halting Problem?

> **Gurkenglas** (2019-08-23, karma 14):
> Nothing stops the Halting problem being solved in particular instances. I can prove that some agent halts, and so can it. See FairBot in Robust Cooperation in the Prisoner's Dilemma.

> **abramdemski** (2019-08-26, karma 4):
> In this case, we have (by assumption) an output of the program, so we just look at the cases where the program gives that output.

**Gurkenglas** (2019-08-23, karma 35):
Written slightly differently, the reasoning seems sane: Suppose I cross. I must have proven it's a good idea. Aka I proved that I'm consistent. Aka I'm inconsistent. Aka the bridge blows up. Better not cross.

> **abramdemski** (2019-08-26, karma 16):
> I agree with your English characterization, and I also agree that it isn't really obvious that the reasoning is pathological. However, I don't think it is so obviously sane, either.
> 
>   * It seems like counterfactual reasoning about alternative actions should avoid going through "I'm obviously insane" in almost every case; possibly in every case. If you think about what would happen if you made a particular chess move, you need to divorce the consequences from any "I'm obviously insane in that scenario, so the rest of my moves in the game will be terrible" type reasoning. You CAN'T assess that making a move would be insane UNTIL you reason out the consequences w/o any presumption of insanity; otherwise, you might end up avoiding a move _only_ because it looks insane (and it looks insane only because you avoid it, so you think you've gone mad if you take it). This principle seems potentially strong enough that you'd want to apply it to the Troll Bridge case as well, even though in Troll Bridge it won't actually help us make the right decision (it just suggests that expecting the bridge to blow up isn't a legit counterfactual).
>   * Also, counterfactuals which predict that the bridge blows up seem to be saying that the agent can control whether PA is consistent or inconsistent. That might be considered unrealistic.

> > **Gurkenglas** (2019-08-26, karma 3):
> > Troll Bridge is a rare case where agents that require proof to take action can prove they would be insane to take some action before they've thought through its consequences. Can you show how they could unwisely do this in chess, or some sort of Troll Chess?
> > 
> > I don't see how this agent seems to control his sanity. Does the agent who jumps off a roof iff he can (falsely) prove it wise choose whether he's insane by choosing whether he jumps?

> > > **abramdemski** (2019-09-04, karma 14):
> > > > I don't see how this agent seems to control his sanity.
> > > 
> > > The agent in Troll Bridge thinks that it can make itself insane by crossing the bridge. (Maybe this doesn't answer your question?)
> > > 
> > > > Troll Bridge is a rare case where agents that require proof to take action can prove they would be insane to take some action before they've thought through its consequences. Can you show how they could unwisely do this in chess, or some sort of Troll Chess?
> > > 
> > > I make no claim that this sort of case is common. Scenarios where it comes up and is relevant to X-risk might involve alien superintelligences trolling human-made AGI. But it isn't exactly high on my list of concerns. The question is more about whether particular theories of counterfactual are right. Troll Bridge might be "too hard" in some sense -- we may just have to give up on it. But, generally, these weird philosophical counterexamples are more about pointing out problems. Complex real-life situations are difficult to deal with (in terms of reasoning about what a particular theory of counterfactuals will actually do), so we check simple examples, even if they're outlandish, to get a better idea of what the counterfactuals are doing in general.

> > > > **Gurkenglas** (2019-09-04, karma 1):
> > > > > (Maybe this doesn't answer your question?)
> > > > 
> > > > Correct. I am trying to pin down exactly what you mean by an agent controlling a logical statement. To that end, I ask whether an agent that takes an action iff a statement is true controls the statement through choosing whether to take the action. ("The Killing Curse doesn't crack your soul. It just takes a cracked soul to cast.")
> > > > 
> > > > Perhaps we could equip logic with a "causation" preorder such that all tautologies are equivalent, causation implies implication, and whenever we define an agent, we equip its control circuits with causation. Then we could say that A doesn't cross the bridge because it's not insane. (I perhaps contentiously assume that insanity and proving sanity are causally equivalent.)
> > > > 
> > > > If we really wanted to, we could investigate the agent that only accepts utility proofs that don't go causally backwards. (Or rather, it requires that its action provably causes the utility.)
> > > > 
> > > > You claimed this reasoning is unwise in chess. Can you give a simple example illustrating this?

> > > > > **abramdemski** (2019-10-02, karma 2):
> > > > > > Correct. I am trying to pin down exactly what you mean by an agent controlling a logical statement. To that end, I ask whether an agent that takes an action iff a statement is true controls the statement through choosing whether to take the action. ("The Killing Curse doesn't crack your soul. It just takes a cracked soul to cast.")
> > > > > 
> > > > > The point here is that the agent described is acting like EDT is supposed to -- it is checking whether its action implies X. If yes, it is acting as if it controls X _in the sense that_ it is deciding which action to take using those implications. I'm not arguing at all that _we_ should think "implies X" is causal, nor even that the agent has opinions on the matter; only that _the agent seems to be doing something wrong_ , and one way of analyzing what it is doing wrong is to take a CDT stance and say "the agent is behaving as if it controls X" \-- in the same way that CDT says to EDT "you are behaving as if correlation implies causation" even though EDT would not assent to this interpretation of its decision.
> > > > > 
> > > > > > If we really wanted to, we could investigate the agent that only accepts utility proofs that don't go causally backwards. (Or rather, it requires that its action provably causes the utility.)
> > > > > 
> > > > > > You claimed this reasoning is unwise in chess. Can you give a simple example illustrating this?
> > > > > 
> > > > > I think you have me the wrong way around; I was suggesting that certain causally-backwards reasoning would be unwise in chess, not the reverse. In particular, I was suggesting that we should not judge a move poor _because_ we think the move is something only a poor player would do, but always the other way around. For example, suppose we have a prior on moves which suggests that moving a queen into danger is something only a poor player would do. Further suppose we are in a position to move our queen into danger in a way which forces checkmate in 4 moves. I'm saying that if we reason "I could move my queen into danger to open up a path to checkmate in 4. However, only poor players move their queen into danger. Poor players would not successfully navigate a checkmate-in-4. Therefore, if I move my queen into danger, I expect to make a mistake costing me the checkmate in 4. Therefore, I will not move my queen into danger." That's an example of the mistake I was pointing at.
> > > > > 
> > > > > Note: I do not personally endorse this as an argument for CDT! I am expressing these arguments because it is part of the significance of Troll Bridge. I think these arguments are the kinds of things one should grapple with if one is grappling with Troll Bridge. I have defended EDT from these kinds of critiques extensively elsewhere. My defenses do not work against Troll Bridge, but they do work against the chess example. But I'm not going into those defenses here because it would distract from the points relevant to Troll Bridge.

> > > > > > **Gurkenglas** (2019-10-03, karma 1):
> > > > > > If I'm a poor enough player that I merely have evidence, not proof, that the queen move mates in four, then the heuristic that queen sacrifices usually don't work out is fine and I might use it in real life. If I can prove that queen sacrifices don't work out, the reasoning is fine even for a proof-requiring agent. Can you give a chesslike game where some proof-requiring agent can prove from the rules and perhaps the player source codes that queen sacrifices don't work out, and therefore scores worse than some other agent would have? (Perhaps through mechanisms as in Troll bridge.)

> > > > > > > **abramdemski** (2019-10-04, karma 2):
> > > > > > > The heuristic can override mere evidence, agreed. The problem I'm pointing at isn't that the heuristic is fundamentally bad and shouldn't be used, but rather that it shouldn't circularly reinforce its own conclusion by counting a hypothesized move as **differentially** suggesting you're a bad player **in the hypothetical where you make that move**. Thinking that way seems contrary to the spirit of the hypothetical (whose purpose is to help evaluate the move). It's fine for the heuristic to suggest things are bad in that hypothetical (because you heuristically think the move is bad); it seems much more questionable to suppose that _your subsequent moves_ will be worse in that hypothetical, particularly if that inference is a lynchpin if your overall negative assessment of the move.
> > > > > > > 
> > > > > > > What do you want out of the chess-like example? Is it enough for me to say the troll could be the other player, and the bridge could be a strategy which you want to employ? (The other player defeats the strategy if they think you did it for a dumb reason, and they let it work if they think you did it smartly, and they know you well, but you don't know whether they think you're dumb, but you do know that _if_ you were being dumb _then_ you would use the strategy.) This is can be exactly troll bridge as stated in the post, but set in chess with player source code visible.
> > > > > > > 
> > > > > > > I'm guessing that's not what you want, but I'm not sure what you want.

> > > > > > > > **Gurkenglas** (2019-10-05, karma 1):
> > > > > > > > I started asking for a chess example because you implied that the reasoning in the top-level comment stops being sane in iterated games.
> > > > > > > > 
> > > > > > > > In a simple iteration of Troll bridge, whether we're dumb is clear after the first time we cross the bridge. In a simple variation, the troll requires smartness even given past observations. In either case, the best worst-case utility bound requires never to cross the bridge, and A knows crossing blows A up. You seemed to expect more.
> > > > > > > > 
> > > > > > > > Suppose my chess skill varies by day. If my last few moves were dumb, I shouldn't rely on my skill today. I don't see why I shouldn't deduce this ahead of time and, until I know I'm smart today, be extra careful around moves that to dumb players look extra good and are extra bad.
> > > > > > > > 
> > > > > > > > More concretely: Suppose that an unknown weighting of three subroutines approval-votes on my move: Timmy likes moving big pieces, Johnny likes playing good chess, and Spike tries to win in this meta. Suppose we start with move A, B or C available. A and B lead to a Johnny gambit that Timmy would ruin. Johnny thinks "If I play alone, A and B lead to 80% win probability and C to 75%. I approve exactly A and B.". Timmy gives 0, 0.2 and 1 of his maximum vote to A, B and C. Spike wants the gambit to happen iff Spike and Johnny can outvote Timmy. Spike wants to vote for A and against B. How hard Spike votes for C trades off between his test's false positive and false negative rates. If B wins, ruin is likely. Spike's reasoning seems to require those hypothetical skill updates you don't like.

> > > > > > > > > **abramdemski** (2019-10-05, karma 2):
> > > > > > > > > > I started asking for a chess example because you implied that the reasoning in the top-level comment stops being sane in iterated games.
> > > > > > > > > 
> > > > > > > > > > In a simple iteration of Troll bridge, whether we're dumb is clear after the first time we cross the bridge.
> > > > > > > > > 
> > > > > > > > > Right, OK. I would say "sequential" rather than "iterated" \-- my point was about making a weird assessment of your own future behavior, not what you can do if you face the same scenario repeatedly. IE: Troll Bridge might be seen as artificial in that the environment is explicitly designed to punish you if you're "dumb"; but, perhaps a sequential game can punish you more naturally by virtue of poor future choices.
> > > > > > > > > 
> > > > > > > > > > Suppose my chess skill varies by day. If my last few moves were dumb, I shouldn't rely on my skill today. I don't see why I shouldn't deduce this ahead of time 
> > > > > > > > > 
> > > > > > > > > Yep, I agree with this.
> > > > > > > > > 
> > > > > > > > > I concede the following points:
> > > > > > > > > 
> > > > > > > > >   * If there is a mistake in the troll-bridge reasoning, predicting that your next actions are likely to be dumb conditional on a dumb-looking action is not an example of the mistake.
> > > > > > > > >   * Furthermore, that inference makes perfect sense, and if it is as analogous to the troll-bridge reasoning as I was previously suggesting, the troll-bridge reasoning makes sense.
> > > > > > > > > 
> > > > > > > > > 
> > > > > > > > > 
> > > > > > > > > However, I still assert the following:
> > > > > > > > > 
> > > > > > > > >   * Predicting that your next actions are likely to be dumb conditional on a dumb looking action doesn't make sense _if the very reason why you think the action looks dumb is that the next actions are probably dumb if you take it_.
> > > > > > > > > 
> > > > > > > > > 
> > > > > > > > > 
> > > > > > > > > IE, you don't have a prior heuristic judgement that a move is one which you make when you're dumb; rather, you've circularly concluded that the move would be dumb -- because it's likely to lead to a bad outcome -- because if you take that move your subsequent moves are likely to be bad -- because it is a dumb move.
> > > > > > > > > 
> > > > > > > > > I don't have a natural setup which would lead to this, but the point is that it's a crazy way to reason rather than a natural one.
> > > > > > > > > 
> > > > > > > > > The question, then, is whether the troll-bridge reasoning is analogous to to this.
> > > > > > > > > 
> > > > > > > > > I think we should probably focus on the probabilistic case (recently added to the OP), rather than the proof-based agent. I could see myself deciding that the proof-based agent is more analogous to the sane case than the crazy one. But the probabilistic case seems completely wrong.
> > > > > > > > > 
> > > > > > > > > In the proof-based case, the question is: do we see the Löbian proof as "circular" in a bad way? It makes sense to conclude that you'd only cross the bridge when it is bad to do so, if you can see that proving it's a good idea is inconsistent. But does the proof that that's inconsistent "go through" that very inference? We know that the troll blows up the bridge if we're dumb, but that in itself doesn't constitute outside reason that crossing is dumb.
> > > > > > > > > 
> > > > > > > > > But I can see an argument that our "outside reason" is that we can't _know_ that crossing is safe, and since we're a proof-based agent, would never take the risk unless we're being dumb.
> > > > > > > > > 
> > > > > > > > > However, this reasoning does not apply to the probabilistic agent. It can cross the bridge as a calculated risk. So its reasoning seems absolutely circular. There is no "prior reason" for it to think crossing is dumb; and, even if it did think it more likely dumb than not, it doesn't seem like it should be 100% certain of that. There should be some utilities for the three outcomes which preserve the preference ordering but which make the risk of crossing worthwhile.

> > **AlexMennen** (2019-09-15, karma 2):
> > I think the counterfactuals used by the agent are the correct counterfactuals for someone else to use while reasoning about the agent from the outside, but not the correct counterfactuals for the agent to use while deciding what to do. After all, knowing the agent's source code, if you see it start to cross the bridge, it is correct to infer that it's reasoning is inconsistent, and you should expect to see the troll blow up the bridge. But while deciding what to do, the agent should be able to reason about purely causal effects of its counterfactual behavior, screening out other logical implications.
> > 
> > > Also, counterfactuals which predict that the bridge blows up seem to be saying that the agent can control whether PA is consistent or inconsistent. 
> > 
> > Disagree that that's what's happening. The link between the consistency of the reasoning system and the behavior of the agent is because the consistency of the reasoning system controls the agent's behavior, rather than the other way around. Since the agent is selecting outcomes based on their consequences, it does make sense to speak of the agent choosing actions to some extent, but I think speaking of logical implications of the agent's actions on the consistency of formal systems as "controlling" the consistency of the formal system seems like an inappropriate attribution of agency to me.

> > > **abramdemski** (2019-10-02, karma 6):
> > > I agree with everything you say here, but I read you as thinking you disagree with me.
> > > 
> > > > I think the counterfactuals used by the agent are the correct counterfactuals for someone else to use while reasoning about the agent from the outside, but not the correct counterfactuals for the agent to use while deciding what to do. 
> > > 
> > > Yeah, that's the problem I'm pointing at, right?
> > > 
> > > > Disagree that that's what's happening. The link between the consistency of the reasoning system and the behavior of the agent is because the consistency of the reasoning system controls the agent's behavior, rather than the other way around. Since the agent is selecting outcomes based on their consequences, it does make sense to speak of the agent choosing actions to some extent, but I think speaking of logical implications of the agent's actions on the consistency of formal systems as "controlling" the consistency of the formal system seems like an inappropriate attribution of agency to me.
> > > 
> > > I think we just agree on that? As I [responded](https://www.lesswrong.com/posts/hpAbfXtqYC2BrpeiC/troll-bridge-5#YZMPzBkd7ZyEx9G6D) to another comment here:
> > > 
> > > > The point here is that the agent described is acting like EDT is supposed to -- it is checking whether its action implies X. If yes, it is acting as if it controls X _in the sense that_ it is deciding which action to take using those implications. I'm not arguing at all that _we_ should think "implies X" is causal, nor even that the agent has opinions on the matter; only that _the agent seems to be doing something wrong_ , and one way of analyzing what it is doing wrong is to take a CDT stance and say "the agent is behaving as if it controls X" \-- in the same way that CDT says to EDT "you are behaving as if correlation implies causation" even though EDT would not assent to this interpretation of its decision.

> > > **Gurkenglas** (2021-07-09, karma 2):
> > > Suppose the bridge is safe iff there's a proof that the bridge is safe. Then you would forbid the reasoning "Suppose I cross. I must have proven it's safe. Then it's safe, and I get 10. Let's cross.", which seems sane enough in the face of Löb.

> > > > **AlexMennen** (2021-07-12, karma 2):
> > > > > Suppose the bridge is safe iff there's a proof that the bridge is safe.
> > > > 
> > > > Then you can prove the bridge is safe without any reference to your own actions.

> > > > > **Gurkenglas** (2021-07-13, karma 2):
> > > > > Suppose the bridge is safe iff A() would decide to cross?

> > > > > > **AlexMennen** (2021-07-18, karma 2):
> > > > > > Not good enough. If I know that the bridge isn't safe, and that I'm not going to cross it, then I know that the bridge is safe iff I'm going to cross it, but not crossing it is still the correct decision.

**ESRogs** (2019-08-24, karma 4):
> there is a troll who will blow up the bridge with you on it, _**if**_ you cross it "for a dumb reason"

Does this way of writing "if" mean the same thing as "iff", i.e. "if and only if"?

> **abramdemski** (2019-08-26, karma 4):
> No, but I probably should have said "iff" or "if and only if". I'll edit.

**AprilSR** (2019-08-24, karma 4):
"(It makes sense that) A proof-based agent can't cross a bridge whose safety is dependent on the agent's own logic being consistent, since proof-based agents can't know whether their logic is consistent."

If the agent crosses the bridge, then the agent knows itself to be consistent.

The agent cannot know whether they are consistent.

Therefore, crossing the bridge implies an inconsistency (they know themself to be consistent, even though that's impossible.)

The counterfactual reasoning seems quite reasonable to me.

> **abramdemski** (2019-08-26, karma 4):
> See my [reply to Gurkenglass](https://www.alignmentforum.org/posts/hpAbfXtqYC2BrpeiC/troll-bridge-5#ecCqFdPjoJdMK4Kjq).

**Donald Hobson** (2019-08-24, karma 4):
Viewed from the outside, in the logical counterfactual where the agent crosses, PA can prove its own consistency, and so is inconsistent. There is a model of PA in which "PA proves False". Having counterfactualed away all the other models, these are the ones left. Logical counterfactualing on any statement that can't be proved or disproved by a theory should produce the same result as adding it as an axiom. Ie logical counterfactualing ZF on choice should produce ZFC. 

The only unreasonableness here comes from the agent's worst case optimizing behaviour. This agent is excessively cautious. A logical induction agent, with PA as a deductive process will assign some prob P strictly between 0 and 1 to "PA is consistent". Depending on which version of logical induction you run, and how much you want to cross the bridge, crossing might be worth it. (the troll is still blowing up the bridge iff PA proves False)

A logical counterfactual where you don't cross the bridge is basically a counterfactual world where your design of logical induction assigns lower prob to "PA is consistent". In this world it doesn't cross and gets zero.

The alternative is a logical factual where it expects +ve util.

So if we make logical induction like crossing enough, and not mind getting blown up much, it crosses the bridge. Lets reverse this. An agent really doesn't want blown up.

In the counterfactual world where it crosses, logical induction assigns more prob to "PA is consistant". The expected utility procedure has to use its real probability distribution, not ask the counterfactual agent for its expected util. 

I am not sure what happens after this, I think you still need to think about what you do in impossible worlds. Still working it out.

> **abramdemski** (2019-08-26, karma 4):
> I don't totally disagree, but [see my reply to Gurkenglas](https://www.alignmentforum.org/posts/hpAbfXtqYC2BrpeiC/troll-bridge-5#ecCqFdPjoJdMK4Kjq) as well as my [reply to Andrew Sauer](https://www.alignmentforum.org/posts/hpAbfXtqYC2BrpeiC/troll-bridge-5#mJZszxrodert8yrvD). Uncertainty doesn't really save us, and the behavior isn't really due to the worst-case-minimizing behavior. It can end up doing the same thing even if getting blown up is only slightly worse than not crossing! I'll try to edit the post to add the argument wherein logical induction fails eventually (maybe not for a week, though). I'm much more inclined to say "Troll Bridge is too hard; we can't demand so much of our counterfactuals" than I am to say "the counterfactual is actually perfectly reasonable" or "the problem won't occur if we have reasonable uncertainty".

> **abramdemski** (2019-10-02, karma 10):
> I've now edited the post to address uncertainty more extensively.

**Andrew Jacob Sauer** (2019-08-24, karma 6):
Seems to me that if an agent with a reasonable heuristic for logical uncertainty came upon this problem, and was confident but not certain of its consistency, it would simply cross because expected utility would be above zero, which is a reason that doesn't betray an inconsistency. (Besides, if it survived it would have good 3rd party validation of its own consistency, which would probably be pretty useful.)

> **abramdemski** (2019-08-26, karma 11):
> I agree that "it seems that it should". I'll try and eventually edit the post to show why this is (at least) more difficult to achieve than it appears. The short version is that a proof is still a proof for a logically uncertain agent; so, if the Löbian proof did still work, then the agent would update to 100% believing it, eliminating its uncertainty; therefore, the proof still works (via its Löbian nature).

> > **Andrew Jacob Sauer** (2019-09-15, karma 3):
> > The proof doesn't work on a logically uncertain agent. The logic fails here:
> > 
> > > Examining the source code of the agent, because we're assuming the agent crosses, either PA proved that crossing implies U=+10, or it proved that crossing implies U=0.
> > 
> > A logically uncertain agent does not need a proof of either of those things in order to cross, it simply needs a positive expectation of utility, for example a heuristic which says that there's a 99% chance crossing implies U=+10.
> > 
> > Though you did say there's a version which still works for logical induction. Do you have a link to where I can see that version of the argument?
> > 
> > Edit: Now I still see the logic. On the assumption that the agent crosses but also proves that U=-10, the agent must have a contradiction somewhere, because that, and the logical uncertainty agents I'm aware of have a contradiction upon proving U=-10 because they prove that they will not cross, and then immediately cross in a maneuver meant to prevent exactly this kind of problem.
> > 
> > Wait but proving crossing implies U=-10 does not mean that prove they will not cross, exactly because they might still cross, if they have a contradiction.
> > 
> > God this stuff is confusing. I still don't think the logic holds though.

> > > **abramdemski** (2019-10-02, karma 14):
> > > I've now edited the post to give the version which I claim works in the empirically uncertain case, and give more hints for how it still goes through in the fully logically uncertain case.

> > > > **Andrew Jacob Sauer** (2020-09-16, karma 7):
> > > > Sorry to necro this here, but I find this topic extremely interesting and I keep coming back to this page to stare at it and tie my brain in knots. Thanks for your notes on how it works in the logically uncertain case. I found a different objection based on the assumption of logical omniscience:
> > > > 
> > > > Regarding this you say:
> > > > 
> > > > > Perhaps you think that the problem with the above version is that I assumed logical omniscience. It is unrealistic to suppose that agents have beliefs which perfectly respect logic. (Un)Fortunately, the argument doesn't really depend on this; it only requires that the agent respects proofs which it can see, and eventually sees the Löbian proof referenced.
> > > > 
> > > > However, this assumes that the Löbian proof exists. We show that the Löbian proof of A=cross→U=−10 exists by showing that the agent can prove □(A=cross→U=−10)→(A=cross→U=−10), and the agent's proof seems to assume logical omniscience:
> > > > 
> > > > > Examining the agent, either crossing had higher expected utility, or P(cross)=0. **But we assumed □(A=cross→U=−10)**, so it must be the latter. So the bridge gets blown up. 
> > > > 
> > > > If **□** here means "provable in PA", the logic does not follow through if the agent is not logically omniscient: the agent might find crossing to have a higher expected utility regardless, because it may not have seen the proof. If **□ **here instead means "discoverable by the agent's proof search" or something to that effect, then the logic here seems to follow through (making the reasonable assumption that if the agent can discover a proof for A=cross->U=-10, then it will set its expected value for crossing to -10). However, that would mean we are talking about provability in a system which can only prove finitely many things, which in particular cannot contain PA and so Löb's theorem does not apply.
> > > > 
> > > > I am still trying to wrap my head around exactly what this means, since your logic seems unassailable in the logically omniscient case. It is counterintuitive to me that the logically omniscient agent would be susceptible to trolling but the more limited one would not. Perhaps there is a clever way for the troll to get around this issue? I dunno. I certainly have no proof that such an agent cannot be trolled in such a way.

> > > > > **abramdemski** (2020-09-16, karma 3):
> > > > > > If **□** here instead means "discoverable by the agent's proof search" or something to that effect, then the logic here seems to follow through (making the reasonable assumption that if the agent can discover a proof for A=cross->U=-10, then it will set its expected value for crossing to -10).
> > > > > 
> > > > > Right, this is what you have to do.
> > > > > 
> > > > > > However, that would mean we are talking about provability in a system which can only prove finitely many things, which in particular cannot contain PA and so Löb's theorem does not apply.
> > > > > 
> > > > > Hmm. So, a bounded theorem prover using PA can still prove Löb about itself. I think everything is more complicated and you need to make some assumptions (because there's no guarantee a bounded proof search will find the right Löbian proof to apply to itself, in general), but you can make it go through.
> > > > > 
> > > > > I believe the technical details you're looking for will be in [Critch's paper on bounded Löb](http://arxiv.org/abs/1602.04184).

> > > > > > **Andrew Jacob Sauer** (2020-09-16, karma 1):
> > > > > > Thanks for the link, I will check it out!

> > > > > **abramdemski** (2020-09-16, karma 10):
> > > > > > Sorry to necro this here, but I find this topic extremely interesting and I keep coming back to this page to stare at it and tie my brain in knots.
> > > > > 
> > > > > (As for this, I think a major goal of LessWrong -- and the alignment forum -- is to facilitate sustained intellectual progress; a subgoal of that is that discussions can be sustained over long periods of time, rather than flitting about as would be the case if we only had attention for discussing the most recent posts!!)

**reavowed** (2019-08-28, karma 7):
I'm having difficulty following the line of the proof beginning "so, either way, PA is inconsistent". We have □(A=cross⇒U=−10) and □(A=cross⇒U≠−10), which together imply that □(A≠cross), but I'm not immediately seeing how this leads to □⊥?

> **reavowed** (2019-08-31, karma 5):
> Ah, got there. From □(A≠cross), we get specifically □(A=cross⇒U=10) and thus □□(A=cross⇒U=10). But we have □(A=cross⇒U=10)⇒A=cross directly as a theorem (axiom?) about the behaviour of A, and we can lift this to □□(A=cross⇒U=10)⇒□(A=cross), so □(A=cross) also and thus □⊥.

**Chris_Leong** (2019-09-01, karma 3):
I'm finding some of the text in the comic slightly hard to read.

> **abramdemski** (2019-09-04, karma 4):
> Yep, sorry. The illustrations were not actually originally meant for publication; they're from my personal notes. I did it this way (1) because the pictures are kind of nice, (2) because I was frustrated that no one had written a good summary post on Troll Bridge yet, (3) because I was in a hurry. Ideally I'll edit the images to be more suitable for the post, although adding the omitted content is a higher priority.

**Stuart_Armstrong** (2019-10-01, karma 2):
Interesting.

I have two issues with the reasoning as presented; the second one is more important.

First of all, I'm unsure about "Rather, the point is that the agent's "counterfactual" reasoning looks crazy." I think we don't know the agent's counterfactual reasoning. We know, by Löb's theorem, that "there exists a proof that (proof of L implies L)" implies "there exists a proof of L". It doesn't tell us what structure this proof of L has to take, right? Who knows what counterfactuals are being considered to make that proof? (I may be misunderstanding this).

Second of all, it seems that if we change the last line of the agent to [else, "cross"], the argument fails. Same if we insert [else if A()="cross" ⊢ U=-10, then output "cross"; else if A()="not cross" ⊢ U=-10, then output "not cross"] above the last line. In both cases, this is because U=-10 is now possible, given crossing. I'm suspicious when the argument seems to depend so much on the structure of the agent.

To develop that a bit, it seems the agent's algorithm as written implies "If I cross the bridge, I am consistent" (because U=-10 is not an option). If we modify the algorithm as I just suggested, then that's no longer the case; it can consider counterfactuals where it crosses the bridge and is inconsistent (or, at least, of unknown consistency). So, given that, the agent's counterfactual reasoning no longer seems so crazy, even if it's as claimed. That's because the agent's reasoning needs to deduce something from "If I cross the bridge, I am consistent" that it can't deduce without that. Given that statement, then being Löbian or similar seems quite natural, as those are some of the few ways of dealing with statements of that type.

> **abramdemski** (2019-10-02, karma 2):
> > First of all, I'm unsure about "Rather, the point is that the agent's "counterfactual" reasoning looks crazy." I think we don't know the agent's counterfactual reasoning. We know, by Löb's theorem, that "there exists a proof that (proof of L implies L)" implies "there exists a proof of L". It doesn't tell us what structure this proof of L has to take, right? Who knows what counterfactuals are being considered to make that proof? (I may be misunderstanding this).
> 
> The agent as described is using provable consequences of actions to make decisions. So, it is using provable consequences _as counterfactuals_. At least, that's the sense in which I mean it -- forgive my terminology if this doesn't make sense to you. I could have said "the agent's conditional reasoning" or "the agent's consequentialist reasoning" etc.
> 
> > Second of all, it seems that if we change the last line of the agent to [else, "cross"], the argument fails. Same if we insert [else if A()="cross" ⊢ U=-10, then output "cross"; else if A()="not cross" ⊢ U=-10, then output "not cross"] above the last line. In both cases, this is because U=-10 is now possible, given crossing. I'm suspicious when the argument seems to depend so much on the structure of the agent.
> 
> I think the benefit of the doubt does not go to the agent, here. If the agent's reasoning is sensible only under certain settings of the default action clause, then one would want a story about how to set the default action clause ahead of time so that we can ensure that the agent's reasoning is always sensible. But this seems impossible.
> 
> However, I furthermore think the example can be modified to make the agent's reasoning look silly in any case.
> 
> If the last line of the agent reads "cross" rather than "not cross", I think we can recover the argument by changing what the troll is doing. The general pattern is supposed to be: the troll blows up the bridge if we cross "for a dumb reason" \-- where "dumb" is targeted at agents who do anything analogous to epsilon exploration or the chicken rule.
> 
> So, we modify the troll to blow up the bridge if PA is inconsistent OR if the agent reaches its "else" clause.
> 
> The agent can no longer be accused of reasoning as if it controlled PA. However, it still sees the bridge blowing up as a definite consequence of its crossing the bridge. This still doesn't seem sensible, because its very reason for believing this involves a circular supposition that it's provable -- much like [my chess example](https://www.lesswrong.com/posts/hpAbfXtqYC2BrpeiC/troll-bridge-5#YZMPzBkd7ZyEx9G6D) where an agent concludes that an action is poor due to a probabilistic belief that it would be a poor player if it took that sort of action.
> 
> [Note that I have not checked the proof for the proposed variant in detail, so, could be wrong.]

> > **Stuart_Armstrong** (2019-10-03, karma 2):
> > > If the agent's reasoning is sensible only under certain settings of the default action clause
> > 
> > That was my first rewriting; the second is an example of a more general algorithm that would go something like this. If we assume that both probabilities and utilities are discrete, all of the form q/n for some q, and bounded above and below by N, then something like this (for EU the expected utility, and Actions the set of actions, and b some default action):
> > [code] 
> >     for q integer in N*n^2 to -N*n^2 (ordered from highest to lowest):
> >         for a in Actions:
> >             if A()=a ⊢ EU=q/n^2 then output a
> >     else output b
> >     
> > [/code]
> > 
> > Then the Löbian proof fails. The agent will fail to prove any of those "if" implications, until it proves "A()="not cross" ⊢ EU=0". Then it outputs "not cross"; the default action b is not relevant. Also not relevant, here, is the order in which a is sampled from "Actions".

> > > **abramdemski** (2019-10-04, karma 3):
> > > I don't see why the proof fails here; it seems to go essentially as usual.
> > > 
> > > Reasoning in PA:
> > > 
> > > Suppose a=cross->u=-10 were provable.
> > > 
> > > Further suppose a=cross.
> > > 
> > > Note that we can see there's a proof that not crossing gets 0, so it must be that a better (or equal) value was found for crossing, which must have been +10 unless PA is inconsistent, since crossing implies that u is either +10 or -10. Since we already assumed crossing gets -10, this leads to trouble in the usual way, and the proof proceeds from there.
> > > 
> > > (Actually, I guess everything is a little messier since you haven't stipulated the search order for actions, so we have to examine more cases. Carrying out some more detailed reasoning: So (under our assumptions) we know PA must have proved (a=cross -> u=10). But we already supposed that it proves (a=cross -> u=-10). So PA must prove not(a=cross). But then it must prove prove(not(a=cross)), since PA has self-knowledge of proofs. Which means PA can't prove that it'll cross, if PA is to be consistent. But it knows that proving it doesn't take an action makes that action very appealing; so it knows it would cross, unless not crossing was equally appealing. But it can prove that not crossing nets zero. So the only way for _not_ crossing to be equally appealing is for PA to _also_ prove not crossing nets 10. For this to be consistent, PA has to prove that the agent doesn't not-cross. But now we have PA proving that the agent doesn't cross and also that it doesn't not cross! So PA must be inconsistent under our assumptions. The rest of the proof continues as usual.)

> > > > **Stuart_Armstrong** (2019-10-13, karma 3):
> > > > You are entirely correct; I don't know why I was confused.
> > > > 
> > > > However, looking at the proof again, it seems there might be a potential hole. You use Löb's theorem within an assumption sub-loop. This seems to assume that from "A→(□B→B)", we can deduce "A→B".
> > > > 
> > > > But this cannot be true in general! To see this, set A=□B→B. Then A→(□B→B), trivially; if, from that, we could deduce A→B, we would have (□B→B)→B for any B. But this statement, though it looks like Löb's theorem, is one that we cannot deduce in general (see Eliezer's "medium-hard problem" [here](https://www.lesswrong.com/posts/ALCnqX6Xx8bpFMZq3/the-cartoon-guide-to-loeb-s-theorem)).
> > > > 
> > > > Can this hole be patched?
> > > > 
> > > > (note that if A→(□AB→B), where □A is a PA proof that adds A as an extra axiom, then we can deduce A→B).

**Bunthut** (2021-03-22, karma 12):
Heres what I imagine the agent saying in its defense:

Yes, of course I can control the consistency of PA, just like everything else can. For example, imagine that you're using PA and you see a ball rolling. And then in the next moment, you see the ball stopping and you also see the ball continuing to roll. Then obviously PA is inconsistent.

Now you might think this is dumb, because its impossible to see that. But why do you think its impossible? Only because its inconsistent. But if you're using PA, you must believe PA really might be inconsistent, so you can't believe its impossible. Remember also that in our agent design theres no clear boundary between perceiving and thinking that you could use to avoid that.

So whether PA is inconsistent depends on the ball: if it stopped and continued to roll, that would make PA inconsistent. Similarly, if my source code implies that I won't do something, and then I do it, I make PA inconsistent. You just don't really believe that your logic might be inconsistent. If you want me to do something else, give me a new theory of logic.

I'm not sure I believe the agent about this, but its not obviously worse than the interpretation given here.

> **abramdemski** (2021-03-23, karma 3):
> > Now you might think this is dumb, because its impossible to see that. But why do you think its impossible? Only because its inconsistent. But if you're using PA, you must believe PA really might be inconsistent, so you can't believe its impossible.
> 
> This part, at least, I disagree with. If I'm using PA, I can prove that ¬(A&¬A). So I don't need to believe PA is consistent to believe that the ball won't stop rolling and also continue rolling.
> 
> On the other hand, I have no direct objection to believing you can control the consistency of PA by doing something else than PA says you will do. It's not _a priori_ absurd to me. I have two objections to the line of thinking, but both are indirect.
> 
>   1. It seems absurd to think that if you cross the bridge, it will _definitely_ collapse. It seems particularly absurd that, in some sense, the reason you think that is just _because you think that._
>   2. From a pragmatic/consequentialist perspective, thinking in this way seems to result in poor outcomes.

> > **Bunthut** (2021-03-23, karma 1):
> > > If I'm using PA, I can prove that ¬(A&¬A).
> > 
> > Sure, thats always true. But sometimes its also true that A&¬A. So unless you believe PA is consistent, you need to hold open the possibility that the ball will both (stop and continue) and (do at most one of those). But of course you can also prove that it will do at most one of _those_. And so on. I'm not very confident whats right, ordinary imagination is probably just misleading here.
> > 
> > > It seems particularly absurd that, in some sense, the reason you think that is just _because you think that._
> > 
> > The facts about what you think are theorems of PA. Judging from the outside: clearly if an agent with this source code crosses the bridge, then PA is inconsistent. So, I think the agent is reasoning correctly about the kind of agent it is. I agree that the outcome looks bad - but its not clear if the agent is "doing something wrong". For comparison, if we built an agent that would only act if it could be sure its logic is consistent, it wouldn't do anything - but its not doing anything wrong. Its looking for logical certainty, and there isn't any, but thats not its fault.

> > > **abramdemski** (2021-03-25, karma 5):
> > > > Sure, thats always true. But sometimes its also true that A&¬A. So unless you believe PA is consistent, you need to hold open the possibility that the ball will both (stop and continue) and (do at most one of those). But of course you can also prove that it will do at most one of _those_. And so on. I'm not very confident whats right, ordinary imagination is probably just misleading here.
> > > 
> > > I think you're still just confusing levels here. If you're reasoning using PA, you'll hold open the possibility that PA is inconsistent, but you _won't_ hold open the possibility that A&¬A. You believe the _world_ is consistent. You're just not so sure about PA.
> > > 
> > > I'm wondering what you mean by "hold open the possibility".
> > > 
> > >   * If you mean "keep some probability mass on this possibility", then I think most reasonable definitions of "keep your probabilities consistent with your logical beliefs" will forbid this.
> > >   * If you mean "hold off on fully believing things which contradict the possibility", then obviously the agent would hold off on fully believing PA itself.
> > >   * Etc for other reasonable definitions of holding open the possibility (I claim).

> > > > **Bunthut** (2021-03-26, karma 1):
> > > > > If you're reasoning using PA, you'll hold open the possibility that PA is inconsistent, but you _won't_ hold open the possibility that A&¬A. You believe the _world_ is consistent. You're just not so sure about PA.
> > > > 
> > > > Do you? This sounds like PA is not actually the logic you're using. Which is realistic for a human. But if PA is indeed inconsistent, and you don't have some further-out system to think in, then what is the difference to you between "PA is inconsistent" and "the world is inconsistent"? In both cases you just believe everything and its negation. This also goes with what I said about thought and perception not being separated in this model, which stand in for "logic" and "the world". So I suppose that is where you would look when trying to fix this.
> > > > 
> > > > > If you mean "hold off on fully believing things which contradict the possibility", then obviously the agent would hold off on fully believing PA itself.
> > > > 
> > > > You do fully believe in PA. But it might be that you also believe its negation. Obviously this doesn't go well with probabilistic approaches.

> > > > > **abramdemski** (2021-03-30, karma 4):
> > > > > > This sounds like PA is not actually the logic you're using.
> > > > > 
> > > > > Maybe this is the confusion. _I'm_ not using PA. I'm assuming (well, provisionally assuming) PA is consistent.
> > > > > 
> > > > > If PA is consistent, then an agent using PA believes the world is consistent -- in the sense of assigning probability 1 to tautologies, and also assigning probability 0 to contradictions.
> > > > > 
> > > > > (At least, 1 to tautologies it can recognize, and 0 to contradictions it can recognize.)
> > > > > 
> > > > > Hence, I (standing outside of PA) assert that (since I think PA is probably consistent) agents who use PA don't know whether PA is consistent, but, believe the world is consistent.
> > > > > 
> > > > > If PA were inconsistent, then we need more assumptions to tell us how probabilities are assigned. EG, maybe the agent "respects logic" in the sense of assigning 0 to refutable things. Then It assigns 0 to everything. Maybe it "respects logic" in the sense of assigning 1 to provable things. Then it assigns 1 to everything. (But we can't have both. The two notions of "respect logic" are equivalent if the underlying logic is consistent, but not otherwise.)
> > > > > 
> > > > > But such an agent doesn't have much to say for itself anyway, so it's more interesting to focus on what the consistent agent has to say for itself.
> > > > > 
> > > > > And I think the consistent agent _very much does not_ "hold open the possibility" that the world is inconsistent. It actively denies this.

> > > > > > **Bunthut** (2021-04-02, karma 1):
> > > > > > > Hence, I (standing outside of PA) assert that (since I think PA is probably consistent) agents who use PA don't know whether PA is consistent, but, believe the world is consistent.
> > > > > > 
> > > > > > Theres two ways to express "PA is consistent". The first is ∀A¬(A∧¬A). The other is a complicated construct about Gödel-encodings. Each has a corresponding version of "the world is consistent" (indeed,  this "world" is inside PA, so they are basically equivalent). The agent using PA will believe only the former. The Troll expresses the consistency of PA using provability logic, which if I understand correctly has the gödelization in it.

**Diffractor** (2021-10-14, karma 3):
A note to clarify for confused readers of the proof. We started out by assuming □(cross→U=−10), and cross. We conclude □(cross→U=10)∨□(cross→U=0) by how the agent works. But the step from there to □⊥ (ie, inconsistency of PA) isn't entirely spelled out in this post.  
  
Pretty much, that follows from a proof by contradiction. Assume con(PA) ie ¬□⊥, and it happens to be a con(PA) theorem that the agent can't prove in advance what it will do, ie, ¬□(¬cross). (I can spell this out in more detail if anyone wants) However, combining □(cross→U=−10) and □(cross→U=10) (or the other option) gets you □(¬cross), which, along with ¬□(¬cross), gets you ⊥. So PA isn't consistent, ie, □⊥.

**Chantiel** (2021-10-18, karma 11):
I'm not entirely sure what you consider to be a "bad" reason for crossing the bridge. However, I'm having a hard time finding a way to define it that both causes agents using evidential counterfactuals to necessarily fail while not having other agents fail.

One way to define a "bad" reason is an irrational one (or the chicken rule). However, if this is what is meant by a "bad" reason, it seems like this is an avoidable problem for an evidential agent, as long as that agent has control over what it decides to think about.

To illustrate, consider what I would do if I was in the troll bridge situation and used evidential counterfactuals. Then I would reason, "I know the troll will only blow up the bridge if I cross for a bad reason, but I'm generally pretty reasonable, so I think I'll do fine if I cross". And then I'd stop thinking about it. I know that certain agents, given enough time to think about it, would end up not crossing, so I'd just make sure I didn't do that.

Another way that you might have had in mind is that a "bad" reason is one such that the action the AI takes results in a provably bad outcome despite the AI thinking the action would result in a good outcome, or the reason being the chicken rule. However, in this is the case, it seems to me that _no_ agent would be able to cross the bridge without it being blown up, unless the agent's counterfactual environment in which it didn't cross scored less than -10 utility. But this doesn't seem like a very reasonable counterfactual environment.

To see why, consider an arbitrary agent with the following decision procedure. Let `counterfactual` be an arbitrary specification of what would happen in some counterfactual world.
[code] 
    def act():
        cross_eu = expected_utility(counterfactual('A = Cross'))
        stay_eu = expected_utility(counterfactual('A = Stay'))
        if cross_eu > stay_eu:
            return cross
        return stay
    
[/code]

The chicken rule can be added, too, if you wish. I'll assume the expected utility of staying is greater than -10.

Then it seems you can adapt the proof you gave for your agent to show that an arbitrary agent satisfying the above description would also get -10 utility if it crossed. Specifically,

Suppose ⊢(A=Cross⟹U=−10). Suppose 'A = Cross' Then the agent crossed either because of the chicken rule or because counterfactual environment in which the agent crossed had utility greater than -10, or the counterfactual environment in which the agent didn't cross had less than -10 utility. We assumed the counterfactual environment in which the agent doesn't cross has more than -10 utility. Thus, it must be either the chicken rule or because crossing had more than -10 utility in expectation. If it's because of the chicken rule, then this is a "bad" reason, so, the troll will destroy the bridge just like in the original proof. Thus, utility would equal -10. Suppose instead the agent crosses because `expected_utility(counterfactual(A = Cross)) > -10`. However, by the assumption, ⊢A=Cross⟹U=−10. Thus, since the agent actually crosses, this in fact provably results in -10 utility and the AI is thus wrong in thinking it would get a good outcome. Thus, the AI's action results in provably bad outcomes. Therefore, the troll destroys the bridge. Thus, utility would equal -10. Thus, 'A = Cross \implies U = -10`. Thus, (⊢A=Cross⟹U=−10)⟹(A=Cross⟹U=−10). Thus, by Lob's theorem, A=Cross⟹U=−10

As I said, you could potentially avoid getting the bridge destroyed by assigning expected utility less than -10 to the counterfactual environment in which the AI doesn't cross. This seems like a "silly" counterfactual environment, so it doesn't seem like something we would want an AI to think. Also, since it seems like a silly thing to think, a troll may consider the use of such a counterfactual environment to be a bad reason to cross the bridge, and thus destroy it anyways.

> **abramdemski** (2021-11-06, karma 2):
> Ok. This threw me for a loop briefly. It seems like I hadn't considered your proposed definition of "bad reasoning" (ie "it's bad if the agent crosses despite it being provably bad to do so") -- or had forgotten about that case.
> 
> I'm not sure I endorse the idea of defining "bad" first and then considering the space of agents who pass/fail according to that notion of "bad"; how this is supposed to work is, rather, that we critique a particular decision theory by proposing a notion of "bad" tailored to that particular decision theory. For example, if a specific decision theorist thinks proofs are the way to evaluate possible actions, then "PA proves ⊥" will be a convincing notion of "bad reasoning" for that specific decision theorist.
> 
> If we define "bad reasoning" as "crossing when there is a proof that crossing is bad" _in general_ , this begs the question of how to evaluate actions. _Of course_ the troll will punish counterfactual reasoning which doesn't line up with this principle, in that case. The only surprising thing in the proof, then, is that the troll also punishes reasoners whose counterfactuals respect proofs (EG, EDT). 
> 
> If I had to make a stab at a generic notion of "bad", it would be "the agent's own way of evaluating consequences says that the consequences of its actions will be bad". But this is pretty ambiguous in some cases, such as chicken rule. I think a more appropriate way to generally characterize "bad reasoning" is just to say that proponents of the decision theory in question should agree that it looks bad.
> 
> This is an open question, even for the examples I gave! I've been in discussions about Troll Bridge where proponents of proof-based DT (aka MUDT) argue that it makes perfect sense for the agent to think its action can control the consistency of PA in this case, so the reasoning isn't "bad", so the problem is unfair. I think it's correct to identify this as the crux of the argument -- whether I think the troll bridge argument incriminates proof-based DT almost entirely depends on whether I think it is unreasonable for the agent to think it controls whether PA proves ⊥ in this case.
> 
> > To illustrate, consider what I would do if I was in the troll bridge situation and used evidential counterfactuals. Then I would reason, "I know the troll will only blow up the bridge if I cross for a bad reason, but I'm generally pretty reasonable, so I think I'll do fine if I cross". And then I'd stop thinking about it. I know that certain agents, given enough time to think about it, would end up not crossing, so I'd just make sure I didn't do that.
> 
> But thinking more is _usually_ a good idea, so, the agent might also decide to think more! What reasoning are you using to decide to stop? If it's reasoning _based on the troll bridge proof_ , you're already in trouble.
> 
> You seem to be assuming that the agent's architecture has solved the problem of logical updatelessness, IE, of applying reasoning only to the (precise) extent to which it is beneficial to do so. But this is one of the problems we would like to solve! So I object to the "stop thinking about it" step w/o more details of the decision theory which allows you to do so.
> 
> Simply put, this is not evidential reasoning. This is evidential reasoning _within conveniently placed limits._ Without a procedure for placing those limits correctly, it isn't a decision theory to me; it's a sketch of what might possibly be a decision theory (but clearly not EDT).
> 
> Furthermore, because the proof is pretty short, it makes it look kind of hard to limit reasoning in precisely the way you want. At least, we can't do it simply by supposing that we only look at a few proofs before deciding whether we should or shouldn't look more -- it is quite possible that the "bad" proof is already present before you make the decision of whether to continue.

> > **Chantiel** (2021-11-07, karma 3):
> > > If we define "bad reasoning" as "crossing when there is a proof that crossing is bad" in general, this begs the question of how to evaluate actions. Of course the troll will punish counterfactual reasoning which doesn't line up with this principle, in that case. The only surprising thing in the proof, then, is that the troll also punishes reasoners whose counterfactuals respect proofs (EG, EDT).
> > 
> > I'm concerned that may not realize that your own current take on counterfactuals respects logical to some extent, and that, if I'm reasoning correctly, could result in agents using it to fail the troll bridge problem.
> > 
> > You said in "My current take on counterfactuals", that counterfactual should line up with reality. That is, the action the agent actually takes should in the utility it was said to have in its counterfactual environment.
> > 
> > You say that a "bad reason" is one such that the agents the procedure would think is bad. The counterfactuals in your approach are supposed to line up with reality, so if an AI's counterfactuals don't line up in reality, then this seems like this is a "bad" reason according to the definition you gave. Now, if you let your agent think "I'll get < -10 utility if I don't cross", then it could potentially cross and not get blown up. But this seems like a very unintuitive and seemingly ridiculous counterfactual environment. Because of this, I'm pretty worried it could result in an AI with such counterfactual environments malfunctioning somehow. So I'll assume the AI doesn't have such a counterfactual environment.
> > 
> > Suppose acting using a counterfactual environment that doesn't line up with reality counts as a "bad" reason for agents using your counterfactuals. Also suppose that in the counterfactual environment in which the agent doesn't cross, the agent counterfactually gets more than -10 utility. Then:
> > 
> >   1. Suppose ⊢A=′Cross′⟹U=−10
> >   2. Suppose A=′Cross′. Then if the agent crosses it must be because either it used the chicken rule or because its counterfactual environment doesn't line up with reality in this case. Either way, this is a bad reason for crossing, so the bridge gets blown up. Thus, the AI gets -10 utility.
> >   3. Thus, ⊢(⊢A=′Cross′⟹U=−10)⟹U=−10
> >   4. Thus, by Lob's theorem, ⊢A=′Cross′⟹U=−10
> > 
> > 
> > 
> > Thus, either the agent doesn't cross the bridge or it does and the bridge explodes. You might just decide to get around this by saying it's okay for the agent to think it would get less than -10 utility if it didn't cross. But I'm rather worried that this would cause other problems.
> > 
> > > You seem to be assuming that the agent's architecture has solved the problem of logical updatelessness, IE, of applying reasoning only to the (precise) extent to which it is beneficial to do so. But this is one of the problems we would like to solve! So I object to the "stop thinking about it" step w/o more details of the decision theory which allows you to do so.
> > 
> > I'll talk about some ways I thought of potentially formalizing, "stop thinking if it's bad".
> > 
> > One simple way to try to do so is to have an agent using regular evidential decision theory but have a special, "stop thinking about this thing" action that it can take. Every so often, the agent considers taking this action using regular evidential decision theory. So, in the troll bridge case, it could potentially see that the path of reasoning it's following is potentially dangerous, and thus decide to stop. Also, the agent needs to avoid thinking too many thoughts before considering to take the "stop thinking about this thing" action. Otherwise, it could think all sorts of problematic thoughts before being able to stop itself.
> > 
> > This simple technique might actually be enough to solve the problem, especially if the AI has the ability to choose its own inference algorithm to find one that makes the AI able to realize, "thinking about this is bad" before it finds the concrete bad thing. And, for what it's worth, it's enough for me personally to get across the bridge.
> > 
> > Now, this might not work reliably, because the AI might stumble upon a problematic thought before realizing it's bad. So, instead, consider this. The AI has an ability to "rollback" its belief state and then adjust its search path. For example, suppose the AI thinks through the Troll Bridge proof and then realizes that it really messed up in doing so. Then it could have a hard-coded way rolling back its belief state to what it was before it thought about the troll bridge thing, mark the nodes it expanded as verboten, and then go expand some other node.
> > 
> > When should it rollback? Well, it shouldn't rollback every time it comes across any evidence that decreases its expected utility. Doing so would result in the AI being very poorly calibrated by ignoring all negative evidence.
> > 
> > One option to do this is to actually manually come up with a rollback method that both rollbacks whenever doing so increases expected utility without resulting in poor calibration.
> > 
> > However, this sounds sort of hard. One cheap trick get around doing this is to just give the AI a special action to modify its rollback method, and then to select the new rollback method using its regular decision procedure. For example, I think it's clear, using evidential decision theory, that choosing the rollback method, "Rollback any thought that decreases my expected utility estimate" would result in low utility. Because that would just mean the AI would delude itself. But I bet a rollback method that says, "Roll back if you find any troll bridge proofs" would work okay.
> > 
> > This trick might not be perfect, since the AI could potentially think about problematic before getting a rollback procedure good enough to roll it back. But as long as the AI is smart enough to realize that it should try to get a really good rollback function before doing much of anything else, then I bet it would work okay.
> > 
> > Also, don't forget that we still need to do something about the agent-simulates-predictor problem. In the agent-simulates-predictor problem, agents are penalized for thinking about things in too much detail. And in whatever counterfactual environment you use, you'll need a way to deal with the agent-simulates-predictor problem. I think the most obvious approach is by controlling what the AI things about. And if you've already done that, then you can pass the troll bridge problem for free.
> > 
> > Also, I think it's important to note that just the fact the AI is _trying_ to avoid thinking of crossing-is-bad proofs makes the proofs (potentially) not go through. For example, in the proof you originally gave, you supposed there is a proof the crossing results in -10 utility, and thus says the agent must have crossed from the chicken rule. But if the AI is trying to avoid these sorts of "proofs", then if it does cross, it simply could have been because the AI decided to avoid following whatever train of thought would prove that it would get -10 utility. This is considered a reasonable thing to do by the AI, so it doesn't seem like a "bad" reason.
> > 
> > There may be possible alternative proofs that apply to an AI that tries to steer its reasoning away from problematic areas. I'm not sure, though. I also suspect that any such proofs would be more complicated and thus harder to find.

> > > **abramdemski** (2021-11-08, karma 2):
> > > > You say that a "bad reason" is one such that the agents the procedure would think is bad.
> > > 
> > > To elaborate a little, one way we could think about this would be that "in a broad variety of situations" the agent would think this property sounded pretty bad.
> > > 
> > > For example, the hypothetical "PA proves ⊥" would be evaluated as pretty bad by a proof-based agent, in many situations; it would not expect its future self to make decisions well, so, it would often have pretty poor performance bounds for its future self (eg the lowest utility available in the given scenario).
> > > 
> > > So far so good -- your condition seems like one which a counterfactual reasoner would broadly find concerning.
> > > 
> > > It also passes the sniff test of "would I think the agent is being dumb if it didn't cross for this reason?" The fact that there's a troll waiting to blow up a bridge if I'm empirically incorrect _about that very setup_ should not, in itself, make me too reluctant to cross a bridge. If I'm very confident that the situation is indeed as described, then intuitively, I should confidently cross.
> > > 
> > > But it seems that, if I believe your proof, I would not believe this any more. You don't prove whether the agent crosses or not, but you do claim to prove that if the agent crosses, it in fact gets blown up. It seems you think the correct counterfactual (for such an agent) _is indeed_ that it would get blown up if it crosses:
> > > 
> > > > Thus, either the agent doesn't cross the bridge or it does and the bridge explodes.
> > > 
> > > So if the proof is to be believed, it seems like the philosophical argument falls flat? If the agent fails to cross for this reason, then it seems you think it is reasoning correctly. If it crosses and explodes, then it fails _because it had wrong counterfactuals_. This also does not seem like much of an indictment of how it was reasoning -- garbage in, garbage out. We can concern ourselves with achieving more robust reasoners, for sure, so that sometimes garbage in -> treasure out. But that's a far cry from the usual troll bridge argument, where the agent has a 100% correct description of the situation, and nonetheless, appears to mishandle it.
> > > 
> > > To summarize:
> > > 
> > >   * The usual troll bridge argument proves that the agent doesn't cross. You fail to do so. This makes your argument less convincing, because we don't actually see that the agent engages in the weird behavior.
> > >   * The usual troll bridge argument establishes a case where we intuitively disagree with the way the agent reasons for not crossing. You've agreed with such reasoning in the end.
> > > 
> > > 
> > > 
> > > _EDIT: I think I should withdraw the first point here; the usual Troll Bridge argument also only proves an either-or in a sense. That is: it only proves not-cross if we assume PA is consistent. However, most people seem to think PA is consistent, which does seem somewhat different from your argument. In any case, I think the second point stands?_
> > > 
> > > However, I grant that your result would be unsettling in a broader sense. It would force me to either abandon my theory, or, accept the conclusion that I should not cross a bridge with a troll under it if the troll blows up the bridge when I'm mistaken about the consequences of crossing.
> > > 
> > > If I bought your proof I think I'd also buy your conclusion, namely that crossing the bridge does in fact blow up such an agent. So I'd then be comfortable accepting my own theory of counterfactuals (and resigning myself to never cross such bridges). 
> > > 
> > > However, I don't currently see how your proof goes through.
> > > 
> > > > 2\. Suppose A=′Cross′. Then if the agent crosses it must be because either it used the chicken rule or because its counterfactual environment doesn't line up with reality in this case. Either way, this is a bad reason for crossing, so the bridge gets blown up. Thus, the AI gets -10 utility.
> > > 
> > > I don't get this step. How does the agent conclude that its counterfactual environment doesn't line up with reality in this case? By supposition, it has proved that crossing is bad. But this does not (in itself) imply that crossing is bad. For counterfactuals not to line up with reality means that the counterfactuals are one way, and the reality is another. So presumably to show that crossing is bad, you _first_ have to show that crossing gets -10 utility, correct? Or rather, the agent has to conclude this within the hypothetical. But here you are not able to conclude that without first having shown that crossing is bad (rather than only that the agent has concluded it is so). See what I mean? You seem to be implicitly stripping off the "⊢" from the first premise in your argument, in order to then justify explicitly doing so.
> > > 
> > > Perhaps you are implicitly assuming that ⊢A=′Cross′⟹U=−10 implies that the correct counterfactual on crossing is -10. But that is precisely what the _original_ Troll Bridge argument disputes, by disputing proof-based decision theory.

> > > > **Chantiel** (2021-11-09, karma 1):
> > > > Oh, I'm sorry; you're right. I messed up on step two of my proposed proof that your technique would be vulnerable to the same problem.
> > > > 
> > > > However, it still seems to me that agents using your technique would also be concerning likely to fail to cross, or otherwise suffer from other problems. Like last time, suppose ⊢(A=′Cross′⟹U=−10) and that A=′Cross′. So if the agent decides to cross, it's either because of the chicken rule, because not crossing counterfactually results in utility ≤ -10, or because crossing counterfactually results in utility greater than -10.
> > > > 
> > > > If the agent crosses because of the chicken rule, then this is a bad reason, so the bridge will blow up.
> > > > 
> > > > I had already assumed that not crossing counterfactually results in utility greater than -10, so it can't be the middle case.
> > > > 
> > > > Suppose instead the crossing counterfactual results in a utility greater than -10 utility. This seems very strange. By assumption, it's provable using the AI's proof system that (A=′Cross⟹U=−10). And the AI's counterfactual environment is supposed to line up with reality.
> > > > 
> > > > So, in other words, the AI has decided to cross and has already proven that crossing entails it will get -10 utility. And if the counterfactual environment assigns greater than -10 utility, then that counterfactual environment provably, within the agent's proof system, doesn't line up with reality. So how do you get an AI to both believe it will cross, believe crossing entails -10 utility, and still counterfactually thinks that crossing will result in greater than -10 utility?
> > > > 
> > > > In this situation, the AI can prove, within its own proof system, that the counterfactual environment of getting > -10 utility is wrong. So I guess we need an agent that allows itself to use a certain counterfactual environment even though the AI already proved that it's wrong. I'm concerned about the functionality of such an agent. If it already ignores clear evidence that it's counterfactual environment is wrong in reality, then that would really make me question that agent's ability to use counterfactual environments in other situations that line up in reality.
> > > > 
> > > > So it seems to me that for an agent using your take on counterfactuals to cross, it would need to either think that not crossing counterfactually results in utility ≤−10, or to ignore conclusive evidence that the counterfactual environment it's using for its chosen action would in fact not line up with reality. Both of these options seem rather concerning to me.
> > > > 
> > > > Also, even if you do decide to let the AI ignore conclusive evidence (to the AI) that crossing makes utility be -10, I'm concerned the bridge would get blown up anyways. I know we haven't formalized "a bad reason", but we've taken it to mean something like, "something that seems like a bad reason to the AI". If the AI wants its counterfactual environments to line up with reality, and it can clearly see that, for the action it decides to take, it doesn't line up with reality, then this seems like a "bad" reason to me.

> > > > > **abramdemski** (2021-11-09, karma 2):
> > > > > > Suppose instead the crossing counterfactual results in a utility greater than -10 utility. This seems very strange. By assumption, it's provable using the AI's proof system that (A=′Cross⟹U=−10). And the AI's counterfactual environment is supposed to line up with reality.
> > > > > 
> > > > > Right. This is precisely the sacrifice I'm making in order to solve Troll Bridge. Something like this seems to be necessary for any solution, because we already know that if your expectations of consequences _entirely_ respect entailment, you'll fall prey to the Troll Bridge! In fact, your "stop thinking"/"rollback" proposals have precisely the same feature: you're trying to construct expectations which don't respect the entailment.
> > > > > 
> > > > > So I think if you reject this, you just have to accept Troll Bridge.
> > > > > 
> > > > > > In this situation, the AI can prove, within its own proof system, that the counterfactual environment of getting > -10 utility is wrong. So I guess we need an agent that allows itself to use a certain counterfactual environment even though the AI already proved that it's wrong. I'm concerned about the functionality of such an agent. If it already ignores clear evidence that it's counterfactual environment is wrong in reality, then that would really make me question that agent's ability to use counterfactual environments in other situations that line up in reality.
> > > > > 
> > > > > Well, this is precisely _not_ what I mean when _I_ say that the counterfactuals line up with reality. What _I_ mean is that they should be _empirically_ grounded, so, in cases where the condition is _actually_ met, we see the predicted result.
> > > > > 
> > > > > Rather than saying this AI's counterfactual expectations are "wrong in reality", you should say they are "wrong in logic" or something like that. Otherwise you are sneaking in an assumption that (a) counterfactual scenarios are real, and (b) they really do respect entailment.
> > > > > 
> > > > > We can become confident in my strange counterfactual by virtue of having seen it play out many times, eg, crossing similar bridges many times. This is the meat of my take on counterfactuals: to learn them in a way that respects reality, rather than trying to deduce them. To impose empiricism on them, ie, the idea that they must make accurate predictions in the cases we actually see.
> > > > > 
> > > > > And it _simply is the case_ that if we prefer such empirical beliefs to logic, here, we can cross. So in this particular example, we see a sort of evidence that respecting entailment is a wrong principle for counterfactual expectations. The 5&10 problem can also be thought of as evidence against entailment as counterfactual.
> > > > > 
> > > > > > Also, even if you do decide to let the AI ignore conclusive evidence (to the AI) that crossing makes utility be -10, I'm concerned the bridge would get blown up anyways. I know we haven't formalized "a bad reason", but we've taken it to mean something like, "something that seems like a bad reason to the AI". If the AI wants its counterfactual environments to line up with reality, and it can clearly see that, for the action it decides to take, it doesn't line up with reality, then this seems like a "bad" reason to me.
> > > > > 
> > > > > You have to realize that reasoning in this way _amounts to insisting that the correct answer to Troll Bridge is not crossing,_ because the troll bridge variant you are proposing just punishes anyone whose reasoning differs from entailment. And again, you were _also_ proposing a version of "ignore the conclusive evidence". It's just that on your theory, it _is really_ evidence, so you _have to_ figure out a way to ignore it. On my theory, it's not really evidence, so we _can_ update on such information and still cross.
> > > > > 
> > > > > But also, _if the agent works as I describe, it will never actually see such a proof_. So it isn't so much that its counterfactuals _actually disagree_ with entailment. It's just that they _can hypothetically disagree_.

> > > **abramdemski** (2021-11-08, karma 2):
> > > > I'll talk about some ways I thought of potentially formalizing, "stop thinking if it's bad".
> > > 
> > > If your point is that there are a lot of things to try, I readily accept this point, and do not mean to argue with it. I only intended to point out that, for your proposal to work, you would have to solve another hard problem.
> > > 
> > > > One simple way to try to do so is to have an agent using regular evidential decision theory but have a special, "stop thinking about this thing" action that it can take. Every so often, the agent considers taking this action using regular evidential decision theory. So, in the troll bridge case, it could potentially see that the path of reasoning it's following is potentially dangerous, and thus decide to stop. Also, the agent needs to avoid thinking too many thoughts before considering to take the "stop thinking about this thing" action. Otherwise, it could think all sorts of problematic thoughts before being able to stop itself.
> > > > 
> > > > This simple technique might actually be enough to solve the problem, especially if the AI has the ability to choose its own inference algorithm to find one that makes the AI able to realize, "thinking about this is bad" before it finds the concrete bad thing. And, for what it's worth, it's enough for me personally to get across the bridge.
> > > 
> > > Ordinary Bayesian EDT has to finish its computation (of its probabilistic expectations) in order to proceed. What you are suggesting is to halt those calculations midway. I think you are imagining an agent who can think longer to get better results. But vanilla EDT does not describe such an agent. So, you can't start with EDT; you have to start with something else (such as logical induction EDT) which does already have a built-in notion of thinking longer.
> > > 
> > > Then, my concern is that we won't have many guarantees for the performance of this system. True, it can stop thinking if it knows thinking will be harmful. However, if it _mistakenly_ thinks a specific form of thought will be harmful, it has no device for correction.
> > > 
> > > This is concerning because we expect "early" thoughts to be bad -- after all, you've got to spend a certain amount of time thinking before things converge to anything at all reasonable.
> > > 
> > > So we're between a rock and a hard spot here: we _have to_ stop quite early, because we know the proof of troll bridge is small. But we _con't stop_ early, because we know things take a bit to converge.
> > > 
> > > So I think this proposal is just "somewhat-logically-updateless-DT", which I don't think is a good solution.
> > > 
> > > Generally I think rollback solutions are bad. (Several people have argued in their favor over the years; I find that I'm just never intrigued by that direction...) Some specific remarks:
> > > 
> > >   * Note that if you literally just roll back, you would go forward the same way again. So you need to somehow modify the rolled back state, creating a "pseudo-ignorant" belief states where you're not really uninformed, but rather, reconstruct something merely similar to an uninformed state. 
> > >     * It is my impression that this causes problems. 
> > >     * You might be able to deduce the dangerous info from the fact that you have gone down a different reasoning path. 
> > >       * I would thus argue that the rollback criterion _has to use only info available before rolling back_ to decide whether to roll back; otherwise, it introduces new and potentially dangerous info to the earlier state.
> > >       * But this means you're just back to the non-rollback proposal, where you decide to stop reasoning at some point.
> > >     * Or, if you solve that problem, rollbacks may leave you truly ignorant, but not solve the original problem which you rolled back to solve.
> > >       * For example, suppose that Omega manipulates you as follows: reward [some target action] and punish [any other action], but _only in the case that you realize Omega implements this incentive scheme._ If you never realize the possibility, then Omega leaves you alone.
> > >       * If you realize that Omega is doing this, and then roll back, you can easily end up in the worst possible world: you don't realize how to get the reward, so you just go about your business, but Omega punishes you for it anyway.
> > >       * For this reason, I think rollbacks belong in a category I'd call "phony updatelessness" where you're basically trying to fool Omega by somehow approximating an updateless state, but also sneakily taking some advantages from updatefullness. This can work, of course, against a naive Omega; but it doesn't seem like it really gets at the heart of the problem.
> > > 
> > > 
> > > 
> > > Simply put, I think rolled-back states are "contaminated" in some sense; you're trying to get them clean, but the future reasoning has left a permanent stain.

**the gears to ascension** (2024-05-21, karma 8):
I found the code hard to read, so here's a transcription for the next me who passes by:

troll:
[code]
    U():
      if A() == "cross" & provable(False):
        return -10
      else if A() == "cross":
        return 10
      else:
        return 0
[/code]

agent:
[code]
    A():
      if A()="cross" proves U()=10
        return "cross"
      else if A()="not cross" proves U()=10
        return "not cross"
      else if A()="cross" proves U()=0
        return "cross"
      else if A()="not cross" proves U()=0
        return "not cross"
      else:
        return "not cross"
[/code]

proof sketch:
[code]
    reasoning u/u- PA
      $A = "cross"
        $\provable(A="cross" -> U=-10)
          either PA proved A()="cross" -> 10,
          or it proved A()="cross" -> 0
          in either case, PA \proves False by way of no
          number being equal to another
        \triforce \provable( (A="cross" -> -10) -> (A="cross" -> U=-10) ).
          by Lob, A="cross" -> u=-10
          so u=-10
      \triforce A="cross" => u=-10
      since we proved this in PA, the bot proves it, and proves no better utility in addition because if it did, then PA would actually be inconsistent.
[/code]

(transcription revision 1)

