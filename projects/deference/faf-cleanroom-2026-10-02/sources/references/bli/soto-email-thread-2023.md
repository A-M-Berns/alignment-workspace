# Martín Soto / the author email thread, Sept 2023 (full text, from the "UDT Email Dump" Google Doc)

*Source: the author's Google Doc "UDT Email Dump" [scrubbed], exported as Markdown and copied here by a Keeper on 2026-09-29. Martín gave permission to share the thread. The doc holds 25 messages, Sep 8 – Sep 27, 2023, pasted from Gmail (the "(N days ago)" stamps date the paste to about Oct 5, 2023). Any later messages in the Gmail thread are not in it, and the Gmail thread itself was not checked. Inline images were moved to `soto-email-thread-images/`: all but one are Gmail avatars, icons and spacers; `soto-email-thread-img-605c1e95.png` is a video thumbnail ("Implementing Logical Counterfactuals").*

*The `//////////////` argument is in the author's email of **Sep 18, 2023, 8:02 PM**: search this file for the line of slashes. The text after it begins "So in particular, let us suppose the 100% correlated picture". Later messages call it the argument for the "single-instance success thesis" (SIST). The author's Logseq paste of excerpts from this thread, with his notes around it, is [soto-email-thread-excerpts-2023](soto-email-thread-excerpts-2023.md).*

---

![][image1]

|  the author [scrubbed]  | Sep 8, 2023, 4:07 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image2]  |  |  |
| :---- | ----- | ----- |

I'm curious if you have any thoughts on precisely spelling out an impossibility result with respect to what we hoped for and have become pessimistic about.

The simplest statement is that there is a trade-off between learning and updatelessness, but this is not quite right:

* Learning is not always possible anyway.  
  * We always knew that we would not be able to learn if there are traps.   
    * Or rather, if the prior believes the environment contains traps.  
  * So we always knew that learning theorems would have conditions on them.  
  * The thing we think we've learned is that some extra condition is needed, beyond what we had hoped.  
  * So the question is: what is the tightest possible statement of the extra assumption we need?  
    * (How little can we get away with assuming?)  
* It's not really learning vs updatelessness, since we can get learning by modifying the prior, which preserves updatelessness (despite making UDT behave more updatefully).  
  * So what we throw away to get learning, more precisely, is correlations between actions and probabilities of branches.  
    * Or perhaps we should split this up into:  
      * Correlations between actions and the probability of branches (including changes to the probability of the branch the action gets taken in, and also to other branches).  
      * Correlations between actions and the \_utility\_ of other branches.

However, I think this does not really highlight the hope that was dashed. Of course there will be a trade-off between UDT behaving updatefully (which happens when it does not think there are acausal correlations to account for) vs failing to (when it does think there are acausal correlations). This is too obvious.

A better statement would be: for any sequence of decision problems UDT could face, *UDT must behave at least a little bit updatefully*, like a policy-selector running at least some really slow LI to improve its selections. So you don't need to resort to the same early, dumb market state to explain UDT's choice; at least, not forever. For each inductor state, actions can eventually be explained in terms of a later state than that. You don't cling to some bad probability estimate *forever*.

If we don't want to treat logical uncertainty as different from empirical uncertainty, then we can extend this to say that you won't need to rely on the same prior to explain actions forever; even though UDT does in fact use a fixed prior, it should eventually act as if it has updated from any particular early distribution.

It seems kind of obvious from the form of this "learning" criterion that there's an arbitrary choice (*when* to move on from the prior). The fact that the desideratum has to be stated in this weird way could perhaps have been a sign that it wouldn't be achievable without hack-y manipulation of the prior.

So, that's the point which my example of infinitely many counterfactual muggings, all from the same (logical or empirical) coin, is supposed to make. It shows that some priors force a choice between learning vs selecting actions in a way which is optimal according to that prior. (Where "learning" is this weak notion of being able to eventually justify actions via a more accurate probability distribution, rather than forever needing to explain them in terms of the ignorance of the fixed prior.)

Anyway, refining a careful statement of the impossibility result seems like it would be a fruitful direction, even for your hopes to salvage things through some new idea; it would be good to have a more precise handle on what you could and could not expect such a new idea to achieve.  
![][image3]  
![][image4]

|  Martín Soto  | ![Attachments][image5]Sep 8, 2023, 5:48 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image6]  |  |  |
| :---- | ----- | ----- |

Hi,

I was just about to write you\!  
Thank you for these thoughts. Getting a non-obvious impossibility result indeed seems very valuable. I'll think more about it tomorrow.

Meanwhile, here are my updates:

  1\. In the pdf, I see that two natural notions of optimality (nearby things might be interesting for impossibility results) are immediately achieved by just argmaxing. Because of that and other things, I posit we might want to        look into **computational complexity, instead of only computability**, to peek at the nature of privileged reasoning in these scenarios.

  2\. There already exists [some research](https://personal.ntu.edu.sg/boan/papers/EC20.pdf) on finite state machines playing games. It seems way more into the complexity nitty-gritty of tractable approximations than our original ideas about just proving eventual                          convergence to good equilibria.

  3\. [scrubbed]

Best,  
Martín  
![][image7]  
One attachment • Scanned by Gmail  
![][image8]

|  Martín Soto  | ![Attachments][image9]Sep 10, 2023, 11:32 AM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image10]  |  |  |
| :---- | ----- | ----- |

Hi,

I adjoin my ideas on Impossibility results. See especially "Average results" and "Humbler results". I'll keep working on them. Let me additionally answer to one part of your email:

\> The thing we think we've learned is that some extra condition is needed, beyond what we had hoped.

I haven't been able to find any natural assumption that captures what we need. I feel like what we've discovered is something more like "logically uncertain EVM is as bold (and sometimes risky) as we could expect". And as a consequence of that, indeed, we have that reward can be arbitrarily bad (except when we have some ultra-strong assumption like "this prior has been optimized for instrumentality by a reasoner that had all the correct opinions about this decision tree"). But it doesn't get captured by non-extreme assumptions about the decision tree or beliefs.

On another note, I've got a simple idea for turning our thing into UDT1.1. That'll be coming up soon\!

Best,  
Martín  
![][image11]  
One attachment • Scanned by Gmail  
![][image12]

|  the author [scrubbed]  | Sep 10, 2023, 1:06 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image13]  |  |  |
| :---- | ----- | ----- |

I was just composing an email when I received yours, so the below isn't written with complete understanding of your email :)

I suggested before that the condition resembles "the UDT, making decisions using a fixed market state LI\_0, eventually acts like it is making decisions using LI\_N for arbitrary N." I was concerned that this might allow a totally updateful thing to count. I would prefer a more meaningful learning condition; EG, learning to pay up in sequences of counterfactual muggings. (Modulo some assumptions about the sequence of counterfactual muggings, perhaps.) Initially, I was thinking about a requirement that the behavior updates, but "not too fast". But this doesn't make sense, since in some situations, perfectly updateful behavior is the right thing to learn.

But perhaps "the UDT eventually acts like it is making decisions using LI\_N" is actually enough, due to interactions with the LIC. Suppose that a sequence of Transparent Newcomb problems is encountered, for example. The LIC should guarantee that the pattern of the decision problems is understood. (This is hand-wavy.) The other conditions established for the UDT should then guarantee that the UDT doesn't update too fast. So UDT acting "fully updatefully" in such a case should be excluded by LIC.

Still, this might make "the UDT eventually acts like it is making decisions using LI\_N" *\*\*inconsistent\*\** ... like, can we really edit the prior to force behavior to be eventually-updateful, while preserving all of the other nice conditions of the UDT, including the LIC?

Maybe this speaks to your point:

\> The thing we think we've learned is that some extra condition is needed, beyond what we had hoped.

I haven't been able to find any natural assumption that captures what we need. I feel like what we've discovered is something more like "logically uncertain EVM is as bold (and sometimes risky) as we could expect". And as a consequence of that, indeed, we have that reward can be arbitrarily bad (except when we have some ultra-strong assumption like "this prior has been optimized for instrumentality by a reasoner that had all the correct opinions about this decision tree"). But it doesn't get captured by non-extreme assumptions about the decision tree or beliefs.

Again, I think the condition is something like "the prior is such that UDT's behavior can eventually be explained as if it has updated to day N, for every N". But of course this is not a constructive condition on the prior, and perhaps it isn't possible to construct such priors. So translating it to some constructive condition (or showing that my condition can be constructed) would be necessary, to support my "some extra condition is needed" story.

In some sense I do agree with your "UDT doesn't work" narrative, if there really is no such condition. (Although, I'm not sure how to reconcile this with my feeling that we just need to face reality on this. It feels like "doesn't work" has some kind of evolutionary intuition behind it... like beings who use UDT will eventually be out-competed by beings who learn. But is that a reason for an individual agent to prefer updating? Not necessarily\!)

More specifically, my intuition is that the reason this could fail is the universal instantiation condition. Since entanglements involving universal statements can touch infinitely many instances, perhaps a modification of the prior to behave somewhat-updatefully-eventually would have to violate universal instantiation or some other important property. But universal instantiation is an important part of how the UDT proposal works. So if this were the case, the UDT setup would be more directly "against learning". (Sorry, again, for the messy reasoning here.)

So I guess ***either*** we have a situation where "we've learned that some extra condition is needed, beyond what we had hoped" (in which case we can still get a picture of a rational agent who learns, just with more restrictive assumptions in addition to the expected no-traps assumption) ***or else*** our UDT is totally inconsistent with learning in this sense (which confirms some of the worse fears one might have about logical updatelessness \-- at least in so far as our UDT is the best formulation of UDT for logical updatelessness).

And either way, it would be good to know which of those situations we're in.

But I'm somewhat confused about the role of universal instantiation. I need to sit down and think about it for longer. I think we agreed that a universal statement could remain near probability zero no matter how many positive instances we see (and similarly, an existential statement could remain near probability one no matter how many non-instances we see). But in some sense this means learned generalizations which have to go through universals are not guaranteed to be good. But many things for UDT *do* have to go through universals. So this in itself should disrupt some hopes for learning, no? EG, we may not correctly learn "it is always better to one-box in transparent newcomb", since the probability of the universal can remain low despite numerous examples. Is there something wrong with my reasoning, or is this correct?

I also wanted to write down some of the thoughts we had about implications of the impossibility result for game theory. Since it feels like a sort of learning vs consistency trade-off, it might yield some insights about "learning vs teaching" trade-offs in multi-agent settings, which could possibly formalize the commitment races problem.

An optimistic version of this might show that if at most one agent is stubborn (ie, the rest of the agents are of the "learning" type), then the joint action profile can converge to a pareto-optimal point. Out of the learning agents, we might expect "more stubborn" agents (agents who update more slowly) to have the advantage in the long run. (IE, the point on the Pareto frontier is skewed toward the interests of the stubborn.) If so, it would vindicate a version of commitment-races, because if we imagine longsighted agents designing UDT priors to play iterated games on their behalf, the most stubborn prior wins in some sense. But if you want to learn as little as possible, the obvious limit of that is to not learn at all. So even if it's true that UDT can be made to learn with the correct choice of prior, this result would illustrate one sense in which it "shouldn't".

For this to be true, it would still have to get around folk-theorem ideas, to achieve pareto-optimality. So it's still quite optimistic, even though it would also confirm a version of the commitment races problem.

Perhaps we could imagine that the priors are themselves designed with access to a cooperative oracle, in some way, so that the commitment-races result could be illustrated without requiring a realistic way to avoid the fold theorem? But I'm not sure how to do this... maybe the simplest way would be to abandon computability of the logical inductors and just do reflective-oracle-logical-induction (all traders have access to a reflective oracle, indeed, a cooperative oracle). So the point would be to show that *even when there's this tremendous resource that can be used for cooperation* there's a perverse commitment-races type problem.

\----

[scrubbed]

One suggestion that comes to mind is homomorphic encryption. I've heard it speculated many times that advances in homomorphic encryption would help AI safety (mostly by providing some degree of guaranteed boxing techniques, against clever inner optimizers). But this requires cryptography, which may be a bit distant from the sort of computational complexity research you would be able to do.

Another idea is to work on distributed coordination (similar to blockchain), although I don't have any specific ideas of what theoretical breakthroughs would be useful here. Just the general impression that something "like blockchain, but better" could possibly be good for the world. Again, not sure whether this has anything to do with complexity theory (though surely there are some computational complexity issues in the general vicinity).

Definitely feels like there should be some computational complexity stuff adjacent to reflective oracles, logical inductors, cooperative oracles, [COEDT](https://www.lesswrong.com/posts/4MLpRxz7ZoX8YXSY3/coedt-equilibria-in-games), and that sort of stuff. Not sure if it's interesting enough qua complexity?

[scrubbed]

Best,  
The author  
![][image14]  
![][image15]

|  Martín Soto  | ![Attachments][image16]Sep 11, 2023, 11:05 AM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image17]  |  |  |
| :---- | ----- | ----- |

Hi,

Thank you so much for all your detailed ideas\!

About your extra learning assumption (the first half of your email), I adjoin a PDF in which I basically show we can constructively edit the prior to satisfy the assumption, as you wanted. It's mostly "Policy Selection expressed inside the epistemic framework", but it has some interesting ramifications. I also address your worries about Universal instantiation and LIC, and other things.

Your ideas about game theory are also very interesting, I'll think more about them soon\!

[scrubbed]

Also, UDT1.1 still coming up soon.

Best,  
Martín  
![][image18]  
One attachment • Scanned by Gmail  
![][image19]

|  the author [scrubbed]  | Sep 11, 2023, 3:11 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image20]  |  |  |
| :---- | ----- | ----- |

Thanks for the very useful notes\!  
![][image21]  
![][image22]

|  the author [scrubbed]  | Sep 12, 2023, 2:08 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image23]  |  |  |
| :---- | ----- | ----- |

I'm still working through things, but I think my main confusion was as follows:

I was imagining that forcing updateful behavior would be done through \*\*constraining the possible acausal correlations\*\*. So for example, if we want the prior to endorse using Q\_n by decision m, we would ensure that the prior thinks decision A\_m does not possess correlations across the possible Q\_n (it only impacts the observed Q\_n it belongs to; alternative possible Q\_n don't care about what happens in each other's worlds), and also that different possible A\_m do not modify the branch probabilities (the relative probabilities of the different possible Q\_n).

Call the constraint on the prior C(n,m).

Suppose we want to enforce this property for two such (n,m) pairs: n1,m1 and n2,m2, such that n1\<n2 and m1\<m2. Clearly, this can only work if Q\_n1 endorses switching to Q\_n2. In other words, C(n2,m2) has to be enforced for the prior P, *and also* for the market state Q\_n1.

Suppose now that we want to enforce C(n,m) for infinitely many pairs (to get an asymptotic learning property). By similar reasoning, we need to enforce infinitely many instances of the constraint *not only for P, but for infinitely many Q\_n as well*.

This is why I was worried about somehow violating the logical induction criterion: because apparently infinitely many market states need to be modified.

Your proposed solution instead only modifies P, and leaves the future market states untouched. So the concern does not arise.

Relatedly, your idea for getting updateful behavior is more of a hack :) But it doesn't matter if it's a hack; the idea is to prove the existence of priors which prefer to update. So long as some exist, it can be a fruitful learning-theoretic assumption. (But it could be interesting to prove that all such priors are "hacky" or "unnatural" in some sense... eg, if no BLI has a structure like the one I'm trying to describe above, enforcing infinitely many C(n,m), that would be interesting, since to me it is the natural reason to choose to update. Your construction is more like behaving updatefully because we think Omega will punish us otherwise\!)  
![][image24]  
![][image25]

|  the author [scrubbed]  | Sep 12, 2023, 2:23 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image26]  |  |  |
| :---- | ----- | ----- |

Ah, here is a more general way to state the concern.

The desired learning property was "for every n, UDT eventually acts as if using (the infinite extrapolation of) Q\_n" instead of P.

I can think of two interpretations of this.

Weak interpretation: *For every n, there is a time m, beyond which all actions can be interpreted as being chosen by (the infinite extension of) **Q\_x for x greater than or equal to n**.*

(This weak interpretation allows future actions to move on from Q\_n and be yet-more-updateful.)

Strong interpretation: *For every n, there is a time m, beyond which all actions can be interpreted as being chosen by (the infinite extension of) **Q\_n**.* 

(This strong interpretation only allows later actions to be even more updateful than Q\_n if Q\_n itself endorses the further updatefulness.)

I was assuming the strong interpretation rather than the weak one. If we need to edit P, it seems pretty clear that we need to edit every Q\_n in the same way, because every Q\_n has to endorse all future choices in exactly the same way that P does. So I hope it is pretty clear why the LIC might be violated by some such construction.

As I understand it, your construction establishes the weak property rather than the strong one.

A construction which gets the weak interpretation and not the strong one seems like it should have tiling concerns. Suppose Q\_n does not endorse updating further, but P does. Then on the round when P mimics Q\_n, Q\_n should prefer self-modifications which overthrow P and stop the updating.  
![][image27]  
![][image28]

|  Martín Soto  | Sep 12, 2023, 6:47 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image29]  |  |  |
| :---- | ----- | ----- |

Thank you, that's very useful\!

\> I was imagining that forcing updateful behavior would be done through \*\*constraining the possible acausal correlations\*\*. So for example, if we want the prior to endorse using Q\_n by decision m, we would ensure that the prior thinks decision A\_m does not possess correlations across the possible Q\_n (it only impacts the observed Q\_n it belongs to; alternative possible Q\_n don't care about what happens in each other's worlds), and also that different possible A\_m do not modify the branch probabilities (the relative probabilities of the different possible Q\_n).

First off, these "independence" properties might be naturally expressed in terms of d-separation.

More importantly, working on this (formalizing those two properties) made me notice an apparent issue in our foundations. It's late and *maybe I'm just hallucinating,* I'll check this thoroughly tomorrow, but I include it just in case.  
As you will remember, we had for now resorted to conditioning on Q\_n=q \-\> A\_n=a, instead of A(q)=a, because that allowed for small beliefs affecting large beliefs (without needing to completely update). Especially, in your email from 16 Aug you present the argument for why that works.  
But now I worry that, because P(A-\>B) is not the same as P(B|A), that argument doesn't go through. Since P's small beliefs that will be extrapolated to large beliefs look like "forall q (A \-\> B)", there's no obvious way to fix this (other than being completely updateful).

Anyway, going back to your ideas, I do think there is a way to enforce your constraints C(n, m) on any distribution, by just modifying continuously some conditional probabilities to get the uniformity we need (that represents independence), for example that P(Q\_n=q | A\_m=a) be constant on a. Although again I think this will look more like "letting Q\_n run as normal, and then in our definition of Procedure() including those enforced changes". (Or maybe there's another clever way to do all that by modifying only P, by slightly violating BLI self-trust where we want to.)

\> A construction which gets the weak interpretation and not the strong one seems like it should have tiling concerns. Suppose Q\_n does not endorse updating further, but P does. Then on the round when P mimics Q\_n, Q\_n should prefer self-modifications which overthrow P and stop the updating.

Yes, you are right about the strong and weak interpretations, and my thing only satisfies weak ("Q\_n might be forced kicking and screaming to update to Q\_n+1"). But I think there's a subtlety here.  
When we say "Q\_n would prefer self-modification to overthrow P", we mean something like "if we give it an action doing that, it will take it". And I'm still not clear on what this "give it an action" should be. For example, whether it's present and observable in the decision tree from the start, or only introduce once Q\_n is in control.  
...

\[Message clipped\]  [scrubbed]  
![][image30]

|  Martín Soto  | ![Attachments][image31]Sep 13, 2023, 10:03 AM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image32]  |  |  |
| :---- | ----- | ----- |

Hi,

Turns out the apparent issue in our foundations I noticed yesterday was real, and our argument doesn't work. I adjoin an explainer of that.  
I'm thinking of solutions, but probably we (or P) will have to pre-specify which syntactic properties of future observations to check omnisciently (which bits of information to be updateful about). But I already have ideas for implementing that, and I don't think it'll change the picture too much. (And then we can use A(q)=a, the right conditional.)

See you later,  
Martín  
...

\[Message clipped\]  [scrubbed]  
One attachment • Scanned by Gmail

## **Gmail virus scanners are temporarily unavailable**

– The attached files haven't been scanned for viruses. Download these files at your own risk.

![][image33]

|  Martín Soto  | ![Attachments][image34]Sep 13, 2023, 11:59 AM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image35]  |  |  |
| :---- | ----- | ----- |

Short and fairly obvious idea to get in-the-limit UDT1.1.  
...

\[Message clipped\]  [scrubbed]  
One attachment • Scanned by Gmail

## **Gmail virus scanners are temporarily unavailable**

– The attached files haven't been scanned for viruses. Download these files at your own risk.

![][image36]

|  the author [scrubbed]  | Sep 14, 2023, 4:06 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image37]  |  |  |
| :---- | ----- | ----- |

Question about the foundational issue.

When we condition on the o-\>a form of a policy-point, we cut out possibilities where o and not a, but we don't cut out anything else. So the branches where o is true have "been informed" that a is true within them, but other branches don't have any info about which policy point is being proposed.

But this seems to mean that branches inconsistent with o can be totally ignored in the EV calculation, right? Because the opinion of those other branches will be constant across different actions considered. The only thing that matters about those branches is their relative probability compared to P(o\&a) (since this impacts the normalizing term when conditioning).

If the action probability P(a|o) for each action is identical, then this relative probability is the same, so we can fully ignore the other branches, which means in such cases, the version of UDT which conditions on policy-points of the o-\>a form is precisely equivalent to EDT.

Am I crazy?  
...

\[Message clipped\]  [scrubbed]  
![][image38]

|  the author [scrubbed]  | Sep 14, 2023, 5:01 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image39]  |  |  |
| :---- | ----- | ----- |

Below is a dump of the relevant notes I wrote today. Sorry about poor formatting.

I will also dump all the notes I wrote in the last few days into the [scrubbed], with similar formatting problems. (New notes dump is at the very end.)

* Blow by blow:  
  * Suppose there is some universal belief that an action is good in specified circumstances (\$\\uparrow\$ here stands for "is high", instead of tracking specific bounds):  
    * \$\\uparrow \\mathbb{Q}\_k (\\forall \\mathcal{Q} (P(\\mathcal{Q}) \\wedge (\\mathbb{Q}\_m \= \\mathcal{Q} \\to A\_m=a) \\to \\uparrow U)\$  
  * What we want to happen:  
    * Suppose \$P(\\mathcal{Q})\$ for a specific \$\\mathbb{Q}\_m=\\mathcal{Q}\$, and \$\\mathcal{Q}\$ is aware of this fact, ie:  
      * \$\\uparrow \\mathcal{Q}(P(\\mathbb{Q}\_m))\$  
        * Soto wrote \$\\uparrow \\mathcal{Q}(P(\\mathcal{Q}))\$, but this belief is too large, living only in the extrapolation.  
    * (**IMPLICATION**) By instantiation, we have:  
      * \$\\uparrow \\mathbb{P} (P(\\mathcal{Q}) \\wedge (\\mathbb{Q}\_m \= \\mathcal{Q} \\; \\to \\; A\_m=a) \\to \\uparrow U)\$  
    * (**DESIRE**) We want it to be the case that:  
      * \$\\uparrow \\mathbb{P}(\\uparrow U | \\mathbb{Q}\_m \= \\mathcal{Q} \\to A\_m \= a)\$  
      * ie, the prior things utility is high conditioned on the material conditional policy point.  
  * So how could we get this to be the case?  
    * It would be satisfied if  
      * \$\\uparrow \\mathbb{P} (P(\\mathcal{Q}) | \\mathbb{Q}\_m \= \\mathcal{Q} \\; \\to \\; A\_m \= a)\$  
    * Because (IMPLICATION) plus this imply (DESIRE).  
    * But this is not at all plausible in general. Conditioning on \$\\mathbb{Q}\_m \= \\mathcal{Q} \\; \\to \\; A\_m \= a)\$ restricts us to two kinds of worlds: those where \$\\neg \\mathbb{Q}\_m \= \\mathcal{Q}\$, and those where \$\\mathbb{Q}\_m \= \\mathcal{Q} \\; \\wedge \\; A\_m \= a)\$. The second kind of world does what we need, but the first very much does not.  
      * IE, other branches have no reason to believe \$P(\\mathcal{Q})\$, since this has only been calculated in the 'true' \$\\mathbb{Q}\_m\$.  
  * Soto's interpretation:  
    * We thought that the knowledge would come together correctly (the prior knowledge that P means we should take action a, and the posterior knowledge that P). But actually, since the knowledge of P doesn't exist in other branches, it is not used there. We can follow the chain of logic if we know that P, but if we condition on this knowledge, we are just being updateful.  
    * Martin suggests that the solution *is* to figure out how to be somewhat updateful; EG, let UDT choose some stuff to be strategically updateful about.  
  * My interpretation:  
    * To me, this feels like a problem with the o-\>a version of a policy point, which should hopefully be fixed by the A(o)=a version. The o-\>a version cuts out possibilities where o and not a, but it fails to inform the other branches of the proposed action. So of course other branches are not putting information together in an appropriate way\! Other branches need to be conditioned on A(o)=a in order to evaluate it.  
    * Indeed, it seems like the o-\>a version is equivalent to EDT in the case that P(a|o) is the same for every action. So this really isn't UDT, and inferring problems for UDT seems unwarranted.  
    * To get the A(o)=a version to work, we just need every branch to be able to sensibly evaluate the impact of the policy-point for their own situation. EG, call the two branches in cf mugging "ask" and "get", with actions "give" and "refuse". What we need is for the "get" branch to correctly understand the impact of "A(ask)=give".  
      * Well, we also need to correctly understand impacts on branch probabilities. In a version where the "get" branch doesn't include an observation of whether the large sum of money is received yet or not, that branch can condition on "A(ask)=give" and expect the large sum, and condition on "A(ask)=refuse" and not expect the large sum. But in a version where "get" does see the reward directly, we actually need to split the problem into three branches, "ask", "get", "nothing" (where "nothing" corresponds to not being asked and also not being given anything). The policy points shift probability between "get" and "nothing".  
      * Part of the claim here is that we need to be very careful about the distinction between the global expected utility vs expected utility in specific branches.  
        * Sentences like \$\\uparrow \\mathbb{Q}\_k (\\forall \\mathcal{Q} (P(\\mathcal{Q}) \\wedge (\\mathbb{Q}\_m \= \\mathcal{Q} \\to A\_m=a) \\to \\uparrow U)\$ are making claims about the global expected utility being high under certain conditions. But this kind of thing is a meta-belief for UDT, which is to say, a statement about UDT's own evaluation of the expected utility. But I think we were thinking as if it were a more object-level statement about utility.  
        * My claim is that it's weird for UDT to reason like "actions satisfying some condition are always UDT-approved, and this here action satisfies the condition, so it should be UDT-approved". Maybe this style of reasoning will be used in some cases, but for it to be correct, it should have been formed as a generalization from more specific cases where more object-level considerations decided things.  
        * Object-level considerations for UDT involve weighing the pros and cons of a policy point in terms of positive and negative impacts across different branches (and re-weighing probabilities of branches). This means looking at the local (updateful) expected utilities within those different branches, and taking a weighted sum, rather than directly trying to reason about the global expected utility before having done that.  
      * So we need two things to happen:  
        * Branches have small beliefs about how policy points impact them, but A(o)=a is a large sentence. We need small and large beliefs to cohere appropriately so that conditioning on such large sentences has impacts consistent with the small beliefs of the branches.  
          * So when we condition \$\\mathbb{P}\$ on a policy-point, the sum decomposes to a sum over possible Q\_m (themselves extrapolated to have large beliefs, since the BLI has 'already' extrapolated everything \-- ie, \$\\mathbb{P} (x | \\mathcal{Q})\$ is an extrapolated version of \$\\mathcal{Q}\$).  
          * So suppose \$\\mathcal{Q}\$ has a universal belief stating that \$P(\\mathcal{Q}')\$ implies \$A(\\mathcal{Q}')=a\$ is good or bad (in the updateful sense; ie, good/bad for \$\\mathcal{Q}\$ specifically).  
          * What we want is that extrapolate(\$\\mathcal{Q}\$) has high/low expected utility conditioned on that policy point.  
        * The prior, of course, has even smaller beliefs about how policy points re-weigh branch probabilities. The impact of conditioning the prior on the large policy point needs to impact relative branch probabilities in a way that fits with the small beliefs.  
          * 

...

\[Message clipped\]  [scrubbed]  
![][image40]

|  Martín Soto  | Sep 14, 2023, 7:02 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image41]  |  |  |
| :---- | ----- | ----- |

Thank you for all these notes\!

\>  which means in such cases, the version of UDT which conditions on policy-points of the o-\>a form is precisely equivalent to EDT

Yes, you are completely right, and not crazy\! In fact, I had already had this realization. I should have written it down in the doc, but if I didn't it was because of the following train of thought:  
"Oh, yes, this just happens because in those few worlds we are completely updateful (like EDT), and in the others completely updateless (about the real observation). This is nothing new, this is just realizing again that we know how to be completely updateful, we know how to be completely updateless, but we're missing the useful thing in between (exactly as in the A(o)=a case). This just clearly shows that we cannot be agnostic: an explicit decision has to be made about what to update on. So we'll let the prior decide that a priori (and if we do that, then we might as well condition on A(o)=a instead of on implications, since we prefer it for other reasons)."

You also noticed that, when not all P(a|o) are the same, the fluctuating ration between P(o\&a) and P(-o) can indeed change E(U). And in fact, this is exactly the mechanism that allows for the wrong behavior in Happy Dance (or, equivalently, the right behavior in Newcomb's). Although actually, this "mechanism" is nothing else than "how probability distributions work".

\> Martin suggests that the solution *is* to figure out how to be somewhat updateful; EG, let UDT choose some stuff to be strategically updateful about.

Yes, I'll write that tomorrow.

\> Sentences like \$\\uparrow \\mathbb{Q}\_k (\\forall \\mathcal{Q} (P(\\mathcal{Q}) \\wedge (\\mathbb{Q}\_m \= \\mathcal{Q} \\to A\_m=a) \\to \\uparrow U)\$ are making claims about the global expected utility being high under certain conditions. But this kind of thing is a meta-belief for UDT, which is to say, a statement about UDT's own evaluation of the expected utility.

I don't yet understand what you mean. I think that's an object-level belief, not explicitly including UDT's evaluation in any way (except for correlations that UDT might believe between its taken actions and its evaluation process, etc.). All variables (Q satisfying P(), Q implying A\_m=a, and the LUV U being high) pertain to the object-level (how the environment looks, which consequences certain actions will have on the environment, etc.). Also, if our prior believes something like that, it will certainly be because it has seen particular object-level examples of that general \\forall (or has proven them in its head).

\> (themselves extrapolated to have large beliefs, since the BLI has 'already' extrapolated everything \-- ie, \$\\mathbb{P} (x | \\mathcal{Q})\$ is an extrapolated version of \$\\mathcal{Q}\$)

Yes, that's also a realization I had, nice.

On a more general note, **here's a path I just thought of to a possible solution:**  
Here's, first, a way to reframe the problem. When I want to represent "Q\_k believes in the worlds in which A turns out true, so does B", of course I shouldn't formalize it as "Q\_k(A-\>B) is high" (that might be high just because A is very unlikely). I should formalize it as "Q\_k(B|A) is high". But then, what if I want to represent "Q\_k believes that, for all Q, in the worlds in which A(Q) turns out true, so does B(Q)"?  
(Here A(Q) is the above P(Q)\&A(Q)=a, or "Omega asks for the capital of France, and I say Paris". And B(Q) is the above \\uparrow U, or "I get \$10".)  
If I had gone with the implication, I could just say "Q\_k(\\forall Q (A(Q)-\>B(Q)) is high", and indeed that's what we were doing.  
But inside Q\_k's probability distribution, I can't say something like "\\forall Q, Q\_k(B(Q)|A(Q)) is high". Of course, Q\_k can formalize such a mathematical sentence (call it \\phi), and believe it strongly ("Q\_k(\\phi) is high"). But I'm pretty sure we've just pushed down the problem one mesa-level down, since Q\_k will also have conditional opinions about \\phi, and its relation to other sentences. (But this possibility should be explored further.)  
So, what if we include some explicit mechanism, on top of the probability distribution, that plays the role of that "external \\forall" that doesn't have a representation inside the distribution? This mechanism will probably need to be intertwined with the infinite extrapolation. But there's something hard I don't know how to solve: How does Q\_k learn that this external \\forall is the case? There's a sense in which Inductor states never get feedback about these conditionals, or better said, they are only able to check them when A(Q) turns out true. So it makes sense that "what they actually observe" is the implication A(Q)-\>B(Q), that doesn't distinguish between satisfying the conditional, or falsifying A(Q).  
But... what if we add an external extrapolation on top of the Inductor states, looking at the historical evolution (instead of only the last state Q\_k), such that we come to opinions about what successful traders are enforcing (not only the end-result fix-point). Then, if we see that indeed Q\_k(B(Q)|A(Q)) is high for most Q we have seen, we can externally notice this pattern, and just enforce in the infinite extrapolation that P(B(Q)|A(Q)) is high for most Q. This does have some reference classes problems, though: how do you choose the class of "Qs" you should extrapolate to?  
But there might be something nice to solve that, like "explicitly looking at the literal traders that are enforcing these patterns, and checking how they behave (individually) when seeing different future market states". This idea seems to follow the general motto "Don't only look at the final probabilities, look at the wealth distribution among the traders, since they are the actual mechanism by which extrapolation happens, and you can ask them things about the future that the static probabilities have no opinion on". "Find an infinite fix-point by giving more compute (as will happen in the future) to the finite amount of traders (with their wealth distribution) that you already have, without adding more (which is what actually happens when you run the LI)". The traders are like "the hypotheses you have considered (and have some feedback on)", and in being Updateless, you are happy to just extrapolate those infinitely, without worrying about whether you've missed a hypothesis. I'll pursue this line further.  
...

\[Message clipped\]  [scrubbed]  
![][image42]

|  the author [scrubbed]  | Sep 14, 2023, 11:39 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image43]  |  |  |
| :---- | ----- | ----- |

I haven't read your email yet, this is a middle of the night thought.

One apparent problem with my idea is: if Q is thinking about A(Q'), with small thoughts, it cannot possibly be thinking of Q' in particular. So the small thoughts seemingly have to specify a way to aggregate over many Q' with the relevant property P. For example, in a counterfactual mugging, the 'get' branch doesn't know which precise branch is the real 'ask' branch. (There are two different relevant notions of the ""real"" ask branch: if the ask world is the real world, then the real ask branch is the actual market state; if the 'get' branch is the real world, then the "real" ask branch is the branch Omega simulates, to the extent that Omega simulates some actually specific market state.) What if we knew A(Q\_1)=a\_1, and A(Q\_2)=a\_2, but both Q\_1 and Q\_2 look like the 'ask' branch from the perspective of small beliefs? Are the actions in similar branches just supposed to be correlated enough that the prior doesn't expect this to happen?

My hope is that we don't have to deal with this problem directly, because the only thing we need is for the conditional expected utility on *one single Q'* to work out right.

...

\[Message clipped\]  [scrubbed]  
![][image44]

|  Martín Soto  | Sep 15, 2023, 11:56 AM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image45]  |  |  |
| :---- | ----- | ----- |

Yes, exactly\! Now you are worrying about the small beliefs' opinions about the properties of some large states (even if the properties are "intuitively simple", like a syntactic property that's easy to check). That's exactly my point and my worry, and the reason I think we'll have to "explicitly choose" what to be updateful about. Because of course, who's to say what is "simple enough" that we can just be updateful about it? In fact, simplicity and "whatever it is instrumentally optimal to be updateful about" will many times come apart.

\> Are the actions in similar branches just supposed to be correlated enough that the prior doesn't expect this to happen?

A priori that shouldn't work in general, since "arbitrarily small changes" (in the description of a branch) could lead to "arbitrarily different action recommendations" (or better said, our agent's beliefs about action recommendations).

\> My hope is that we don't have to deal with this problem directly, because the only thing we need is for the conditional expected utility on *one single Q'* to work out right.

I'd certainly like to see this more developed because, despite my opinions, it's still conceivable that we can find an especially natural way to deal with this, that looks less like "we explicitly decide what to be updateful about" (although, strictly speaking, any solution will be implicitly deciding what to be updateful about).  
Still, my intuition remains that the way of getting the right conditional expected utility on that single Q' must be letting it update on the right things.

Let me now address two of your previous points.

\> Indeed, it seems like the o-\>a version is equivalent to EDT in the case that P(a|o) is the same for every action. So this really isn't UDT, and inferring problems for UDT seems unwarranted.

Yes, true. My point was just that what we thought we had the right version of UDT, and we were wrong\! And given that, our intuitions differ about whether we'll find something more natural than "let the prior decide what to update on".

\> What we want is that extrapolate(\$\\mathcal{Q}\$) has high/low expected utility conditioned on that policy point.

I think that happens by default, if by extrapolate(Q) you mean the extrapolated P conditioned on Q, as above. That is, if we condition on Q by BLI self-trust we get the implication, so if we also condition on the antecedent (policy point), we get the consequent (high utility). The problem is this (conditioning on the whole Q) amounts to being completely updateful\! The problem isn't that we don't know how to get the implication across, but that we don't know how to do that without being completely updateful. (And I propose letting the prior decide what to update on, and you propose we'll find something else.)

P.S: My doc about UDT1.1 contains an important mistake. Fixed version coming soon.  
...

\[Message clipped\]  [scrubbed]  
![][image46]

|  Martín Soto  | ![Attachments][image47]Sep 15, 2023, 2:01 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image48]  |  |  |
| :---- | ----- | ----- |

Mathematical formalization of my straightforward idea for solving the foundational problem: "Let the prior decide what to be updateful about".  
...

\[Message clipped\]  [scrubbed]  
One attachment • Scanned by Gmail  
![][image49]

|  Martín Soto  | ![Attachments][image50]Sep 15, 2023, 4:27 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image51]  |  |  |
| :---- | ----- | ----- |

As promised, fixed version of Getting UDT1.1.  
...

\[Message clipped\]  [scrubbed]  
One attachment • Scanned by Gmail

## **Gmail virus scanners are temporarily unavailable**

– The attached files haven't been scanned for viruses. Download these files at your own risk.

![][image52]

|  the author [scrubbed]  | Sep 18, 2023, 8:02 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image53]  |  |  |
| :---- | ----- | ----- |

The following rambly email has a more important proposal at the end, which I'm particularly eager to hear your thoughts on. If your time is limited, skip past the "//////////////" mark.  
   
Yes, you are completely right, and not crazy\! In fact, I had already had this realization. I should have written it down in the doc, but if I didn't it was because of the following train of thought:  
"Oh, yes, this just happens because in those few worlds we are completely updateful (like EDT), and in the others completely updateless (about the real observation). This is nothing new, this is just realizing again that we know how to be completely updateful, we know how to be completely updateless, but we're missing the useful thing in between (exactly as in the A(o)=a case). This just clearly shows that we cannot be agnostic: an explicit decision has to be made about what to update on. So we'll let the prior decide that a priori (and if we do that, then we might as well condition on A(o)=a instead of on implications, since we prefer it for other reasons)."

As I've mentioned before, if we choose a set of observations which includes the observation we're considering a policy-point for, and which partitions the whole event space, we can call the elements of the partitions "branches". Call the observation which the policy-point we're evaluating belongs to the "home branch". We can then neatly divide consequences which UDT considers into three categories: (1) influences of the  policy-point on expected utility within other branches; (2) influences of the policy-point on relative branch probabilities; (3) impacts on the home branch (that is, updateful impacts).

Of the updateless impacts (1 and 2), the o-\>a version of UDT *only* considers (2), and further, *only changes the relative weight of the home branch compared to others*, and also *only reduces that weight*.

So the a-\>o version is extremely restricted in what type of updateless considerations it can consider. Plus it represents those considerations via non-equal action probabilities, which is a somewhat dubious way to represent Transparent Newcomb (since it cannot then distinguish Transparent Newcomb from merely being pretty confident that it won't take a specific action).

\> Sentences like \$\\uparrow \\mathbb{Q}\_k (\\forall \\mathcal{Q} (P(\\mathcal{Q}) \\wedge (\\mathbb{Q}\_m \= \\mathcal{Q} \\to A\_m=a) \\to \\uparrow U)\$ are making claims about the global expected utility being high under certain conditions. But this kind of thing is a meta-belief for UDT, which is to say, a statement about UDT's own evaluation of the expected utility.

I don't yet understand what you mean. I think that's an object-level belief, not explicitly including UDT's evaluation in any way (except for correlations that UDT might believe between its taken actions and its evaluation process, etc.). All variables (Q satisfying P(), Q implying A\_m=a, and the LUV U being high) pertain to the object-level (how the environment looks, which consequences certain actions will have on the environment, etc.). Also, if our prior believes something like that, it will certainly be because it has seen particular object-level examples of that general \\forall (or has proven them in its head).

The more I think about this, the more I agree that there's no way to revise my statement to make sense.

On a more general note, **here's a path I just thought of to a possible solution:**  
Here's, first, a way to reframe the problem. When I want to represent "Q\_k believes in the worlds in which A turns out true, so does B", of course I shouldn't formalize it as "Q\_k(A-\>B) is high" (that might be high just because A is very unlikely). I should formalize it as "Q\_k(B|A) is high". But then, what if I want to represent "Q\_k believes that, for all Q, in the worlds in which A(Q) turns out true, so does B(Q)"?  
(Here A(Q) is the above P(Q)\&A(Q)=a, or "Omega asks for the capital of France, and I say Paris". And B(Q) is the above \\uparrow U, or "I get \$10".)  
If I had gone with the implication, I could just say "Q\_k(\\forall Q (A(Q)-\>B(Q)) is high", and indeed that's what we were doing.  
But inside Q\_k's probability distribution, I can't say something like "\\forall Q, Q\_k(B(Q)|A(Q)) is high".  
\[...\]  
So, what if we include some explicit mechanism, on top of the probability distribution, that plays the role of that "external \\forall" that doesn't have a representation inside the distribution? This mechanism will probably need to be intertwined with the infinite extrapolation.   
\[...\]

The following isn't exactly the same as your idea, but has some resemblance.

Propositional coherence and LUV coherence succeed at relating 'small' and 'large' quite nicely, because there is a natural notion of marginalization in play which allows large beliefs to be turned into small beliefs (so we sort of know how to reverse the process).

The set of E(U|A(Q)=a) doesn't have an obvious notion of marginalization, so that is, in some sense, our bottleneck.

Imagine that the market has evolved for a long time and now has firm opinions about all A(Q)=a up to the size of Q\_m, and also a highly informed estimate of U. How could all of that information be summarized in useful ways? Can we add a new mechanic, similar to propositional & LUV coherence, which forces coherence for such summaries? Perhaps most importantly, can the mechanism represent the intuitively important "small" relationships between the A(Q)=a sentences and U?

Well, I don't know what statistics will be important, but ***all*** statistics summarizing the joint A(Q)=a and U beliefs will be LUVs. So perhaps a new mechanism is not needed after all. 

I'm also somewhat sympathetic to your idea that the information I'm trying to summarize is missing the conditional probability info in some sense, since I'm imagining as if we have solid values for all of the A(Q)=a and for U. But if we can summarize fully specified worlds with statistics, then we can take expectations of such summaries to summarize joint distributions, and joints imply conditionals.

So, for example, if I have small beliefs resembling counterfactual mugging, then possible Q divide into "asked" branches and "receive" branches (and others with low probability). Let's name those predicates Ask(Q) and Rec(Q). My belief that if I give \$10 in response to being asked (Ask(Q)\&A(Q)=give) then I should expect to get \$100 (E(U|Rec(Q))=100) should somehow correspond to a summary of predictions I would make about the eventual joint state of all the A(Q)=a sentences and U. Maybe I think Omega picks one of the Q such that Ask(Q) at random, checks A(Q)=give, then checks the random coin, and gives me \$100 if both are true. This should have implications about which small LUVs I would be willing to buy stock in.

Still, there seems to be a big problem connecting such things to the conditional probabilities. We want to condition P on A(Q)=refuse (where Ask(Q) is true) and see a dip in expected utility, compared to conditioning on A(Q)=give.

\> Are the actions in similar branches just supposed to be correlated enough that the prior doesn't expect this to happen?

A priori that shouldn't work in general, since "arbitrarily small changes" (in the description of a branch) could lead to "arbitrarily different action recommendations" (or better said, our agent's beliefs about action recommendations).

Intuitively, it shouldn't matter too much whether I think all of the "give/refuse" decisions for different Q satisfying Ask(Q) are correlated or uncorrelated. (So long as they aren't anticorrelated.) If they're all quite correlated, then we should see a big change in U, since conditioning on any one A(Q)=give means many Ask(Q) end up 'give', and similarly for 'refuse'. If they're all independent, then conditioning on any one A(Q)=give would have a tiny influence on the expected utility, but in principle (if calculated with enough degrees of precision) giving up \$10 in an epsilon-probable world to gain epsilon probability of \$100 should still come out in favor of 'give'.

(But interestingly, how correlated these different decisions are depends in turn on the decision procedure (which itself depends on how correlated P thinks things are). Makes me feel like there should be a way to cut the loop and treat some decision classes as completely correlated based on the fact that the decision procedure does not distinguish the difference between them. I'm not claiming this thought is important to the overall idea, however.)

Sorry, I know this proposal is still not very concrete and I haven't said enough to prove that it works.

I'd certainly like to see this more developed because, despite my opinions, it's still conceivable that we can find an especially natural way to deal with this, that looks less like "we explicitly decide what to be updateful about" (although, strictly speaking, any solution will be implicitly deciding what to be updateful about).  
Still, my intuition remains that the way of getting the right conditional expected utility on that single Q' must be letting it update on the right things.

Yeah, currently, I would really like either a stronger impossibility argument for "classic UDT" or a way to get it to work.

\> What we want is that extrapolate(\$\\mathcal{Q}\$) has high/low expected utility conditioned on that policy point.

I think that happens by default, if by extrapolate(Q) you mean the extrapolated P conditioned on Q, as above.

Confirmation that this is what I meant.

That is, if we condition on Q by BLI self-trust we get the implication, so if we also condition on the antecedent (policy point), we get the consequent (high utility). The problem is this (conditioning on the whole Q) amounts to being completely updateful\! The problem isn't that we don't know how to get the implication across, but that we don't know how to do that without being completely updateful. (And I propose letting the prior decide what to update on, and you propose we'll find something else.)

Notice that I'm not conditioning on Q, but rather, I'm noting that taking the expectation in P decomposes into many expectations given each possible Q. So I think your observation (that this just works by default) puts us in a pretty good situation.

//////////////

So in particular, let us suppose the 100% correlated picture:

* P thinks Q\_m will satisfy either Ask or Rec with 98% probability, and equal probability (49%) between the two possibilities.  
* Branches Q satisfying Rec(Q) believe that Ask(Q') implies A(Q')=give \-\> U=100, and A(Q')=refuse-\>U=0.  
* Branches Q satisfying Ask(Q) believe that Ask(Q') implies A(Q')=give \-\> \-10, and A(Q')=refuse \-\> U=0.

Then conditioning P on the policy-point A(Q')=give where Q' satisfies Ask, the calculation (mostly) decomposes into two cases, those where Ask(Q\_m) and those where Rec(Q\_m) (with equal probability). Similarly for the calculation of A(Q')=give. The question is whether those four cases correctly evaluate to the numbers we want (-10, 0, \+100, 0).

Let's consider one of those four cases: Ask(Q\_m) for the policy point A(Q')=give.

Let's assume that Ask(Q) and Rec(Q) are themselves LUVs which can be defined from the LUVs of the Q they evaluate, so that conditioning P on Ask(Q\_m) gives P the (average) beliefs of such Q. \[So Ask(Q\_m) is a small conjunction of basic claims about the market, such that LUV-coherence makes the expected probability of Ask(Q\_m) equal the probability that Ask(Q) for a Q randomly drawn from P. Self-trust then means conditioning on the small statement Ask(Q\_m) gives us the average beliefs of Q satisfying Ask(Q).\]

So the expected utility of A(Q')=give according to P decomposes into 48% E(U | A(Q')=give, Ask(Q\_m)) and 48% E(U | A(Q')=give, Rec(Q\_m)) and 2% some other stuff I'm going to neglect. And we're here focusing on the component of this sum where Ask(Q\_m). We want the expectation to equal \-10.

Since P( . | Ask(Q\_m)) has the average beliefs of ask branches, it believes that forall Q, Ask(Q) \-\> \[A(Q)=give \-\> \-10\]. So in particular, for the Q' belonging to the policy point we're conditioning on, it believes Ask(Q') \-\> \[A(Q')=give \-\> \-10\]. And it is also being conditioned on A(Q')=give. So what we need is for it to believe Ask(Q').

I expect you to say that, yes, this illustrates that we need P to decide to update on Ask(Q') before making the decision.

Because of course, who's to say what is "simple enough" that we can just be updateful about it? In fact, simplicity and "whatever it is instrumentally optimal to be updateful about" will many times come apart.  
   
But here we have an obvious candidate for "simple enough": Ask() already needs to satisfy the property I mentioned earlier, of being a simple compound LUV. So all we need here is the following extension of LUV coherence: if F(Q) is a small conjunction of simple claims about market Q, then P is updateful about the evaluation of F, even on large Q.

So I argue that given this, P evaluates the case we're considering to \-10, and also correctly evaluates the three other cases; so, decides to take the counterfactual mugging.

Sorry for the slightly ambiguous notation in the above; hopefully the idea is clear enough?

As I argued earlier, the picture when decisions are less than 100% correlated between 'ask' branches should yield a similar result despite being more complex, although I'm far from certain that it works out.

Curious to hear what you think\!

Best,  
The author

![][image54]

|  Martín Soto  | Sep 19, 2023, 9:08 AM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image55]  |  |  |
| :---- | ----- | ----- |

Hi,

Thank you so much for all these thoughts\! I've only read the "important proposal" part for now, since I'm busy finishing the report and presentation (but I'll try to read the rest before tomorrow).

Your reasoning is correct, as far as I can tell. And the heart of your proposal seems to be this:

\> But here we have an obvious candidate for "simple enough": Ask() already needs to satisfy the property I mentioned earlier, of being a simple compound LUV. So all we need here is the following extension of LUV coherence: if F(Q) is a small conjunction of simple claims about market Q, then P is updateful about the evaluation of F, even on large Q.

And you are right: we can do that\! Actually, this is no news for me. My claim is that this is not especially natural or privileged (even if it has some a priori intuitive pull), and that it's actually worse for our purposes than letting P decide what to be updateful about.

Why is this not natural or privileged? Well, what's your definition of "F(Q) is a small conjunction of simple claims about market Q"? We can fix an arbitrary definition (an arbitrary "complexity point" at which we stop being updateful). And that's the usual approach of "being updateful about things inside this complexity class, and updateless about things inside it". And it has its usual problems. It seems intuitively good because "we are okay updating on the simple, syntactic properties of nodes, because those will lead to correctly to extrapolating P's opinions about which policies to implement". That is, we like this proposal because it will intuitively have good consequences. But what if P could extrapolate some further beliefs (that correspond to reality) if it just were updateful about another, slightly more complex syntactic property F'() (that falls just outside the scope of our "complexity" barrier). Or on the contrary, what if P wanted to be updateless about a certain property F'() (because it correctly predicted Omega would take that into account), but unfortunately that F'() falls just inside our "complexity" barrier? Ask() and Rec() look especially obvious and "given", but in reality we'll be dealing with a myriad of logical formulas, which might mean a myriad of things, and whose simplicity and usefulness sometimes vary independently.

Yes, we have to draw the boundary of "what to update on" somewhere (that was my "foundational problem" realization). But what I'm explaining here is my earlier point: "updating on simple things" and "updating in an instrumentally optimal way" come apart. And we terminally care about the latter (consequences, reward, performance), and not the former. So our definition of "what to update on" should align with the latter, not the former.

And that's what "ask P what we should update on" does. Given we care about consequences, and that in a realistic situation the agent's only way to think about consequences will be its own opinions (we won't have access to an external oracle deciding optimal action for us, or anything like that), we need to use its opinions (that's the best we can do in bounded rationality). And of course they will sometimes be fallible (bounded rationality), but to the extent those beliefs are "what's being epistemically optimized to fit the world" (and indeed, in our current framework, the prior's beliefs have not yet been optimized for instrumentality), we have to trust that "in the limit they will approximate real consequences". We won't find a better proxy for "having good consequences", and that's what we care about ultimately.

Thanks again and best,  
Martín

P.S: I have an idea for making Logical Inductors satisfy the Reflection principle and Future self-trust (in every finite state), that seems closer to Sam's original BLI idea. I'll also try to write that before tomorrow.  
![][image56]  
![][image57]

|  the author [scrubbed]  | Sep 19, 2023, 10:15 AM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image58]  |  |  |
| :---- | ----- | ----- |

Seems like we are converging in our understanding of the situation\!   
![][image59]  
![][image60]

|  the author [scrubbed]  | Sep 19, 2023, 3:07 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image61]  |  |  |
| :---- | ----- | ----- |

\> And you are right: we can do that\! Actually, this is no news for me. My claim is that this is not especially natural or privileged (even if it has some a priori intuitive pull), and that it's actually worse for our purposes than letting P decide what to be updateful about.

Why is this not natural or privileged? Well, what's your definition of "F(Q) is a small conjunction of simple claims about market Q"? We can fix an arbitrary definition (an arbitrary "complexity point" at which we stop being updateful). And that's the usual approach of "being updateful about things inside this complexity class, and updateless about things inside it". And it has its usual problems. It seems intuitively good because "we are okay updating on the simple, syntactic properties of nodes, because those will lead to correctly to extrapolating P's opinions about which policies to implement". That is, we like this proposal because it will intuitively have good consequences. But what if P could extrapolate some further beliefs (that correspond to reality) if it just were updateful about another, slightly more complex syntactic property F'() (that falls just outside the scope of our "complexity" barrier). Or on the contrary, what if P wanted to be updateless about a certain property F'() (because it correctly predicted Omega would take that into account), but unfortunately that F'() falls just inside our "complexity" barrier?

I expect I will end up agreeing with this to some extent, but I am still strongly entertaining the idea that the proposal I offered is indeed a privileged position. So, how do we adjudicate?

* You ask how I define "small conjunction of simple claims". I'm implicitly claiming that a specific definition will be essentially forced; you are implicitly claiming that there will be many possibilities and an obvious parameter.  
* You ask, what if P could extrapolate some further beliefs if it were just a bit more updateful? On your side, you claim that we should allow P to decide to be more updateful than this, in order to capture those gains (in cases where we're lucky enough to have P which sees the gains). On my side, I claim **this should not be necessary**: If my intuition is correct, then so long as we meet the minimal logical-updatefulness condition I named, **any further updatefulness which P would endorse if we followed the two-step procedure will already be rolled into the one-step procedure**. I think this is probably the main crux.  
* You ask what happens if my proposal is actually too logically updateful, and Omega wants to offer a cf mugging on such things? On your side you expect a convincing decision problem to come out of such a story; on my side I might claim there won't be one. I think this is less of a crux, because if my previous claim is true, I might be happy to sacrifice such decision problems. I agree with the claim that there will always be some sort of logical updatefulness forced by the decision calculation itself; I'm happy to make some sacrifices on that front for nice properties.

So the main story I should work on elaborating is the bolded claim above.

Desired property: UDT already behaves updatefully with respect to some computational knowledge (some boundedly-knowable proposition X) if it thinks it's a good idea. Adding a two-step decision process in which UDT first decides what to be updateful about, and then makes the UDT calculation, never adds anything.

Rough argument: if X is boundedly-knowable by Q\_m, and P thinks it is a good idea to make time-m decisions (both real and counterfactual) in a way that's updateful about X, then an argument similar to the one I made in the previous email will establish that UDT will already behave as if P had been updated on X before making the decision.

... I seem to be out of brainpower for now, and you probably don't have time to read this email at the moment anyway :) I'll send more when I have more.

Best,  
The author  
![][image62]  
![][image63]

|  Martín Soto  | ![Attachments][image64]Sep 20, 2023, 11:40 AM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image65]  |  |  |
| :---- | ----- | ----- |

\> You ask, what if P could extrapolate some further beliefs if it were just a bit more updateful? On your side, you claim that we should allow P to decide to be more updateful than this, in order to capture those gains (in cases where we're lucky enough to have P which sees the gains). On my side, I claim **this should not be necessary**: If my intuition is correct, then so long as we meet the minimal logical-updatefulness condition I named, **any further updatefulness which P would endorse if we followed the two-step procedure will already be rolled into the one-step procedure**. I think this is probably the main crux.

I don't see right now how this could be the case. That is, I think there will always be counter-examples to any proposed definition of "small conjunctions of simple claims" (choice of the parameter).  
Say you define that to be any complexity class. I will be able to construct a situation in which our agent is very certain of the optimality of some policy, and they are right, and nonetheless they cannot implement it because they have to be updateful about something outside the complexity class. If the complexity class is "polynomial-time checks", then it could require an exponential-time check. Similarly for bounds on lengths of the logical formulas defining the properties, etc.  
And I can also construct an opposite counterexample in which the agent learned early enough (correctly) that it should be updateless about a property, but our choice of complexity class forces it to update (but it seems like you're less worried about this one).

Something I could conceive happening is "it turns out, when  you average across all these decision trees, that updating on all polynomial-time properties is better than updating on all exponential-time properties". And maybe even something nicer like "there is an optimal complexity class". But this has more to do with average performance, and gets into the problem of how we average across trees (maybe different notions of average incentivize different complexity classes). And I think this is not what you have in mind.

\> UDT already behaves updatefully with respect to some computational knowledge (some boundedly-knowable proposition X) if it thinks it's a good idea

Again, here I want to say: Yes, this is the desired property\! We care about doing that when "it thinks it's a good idea". But then why would we use complexity classes instead of just letting it choose? Isn't it trivial that complexity classes and this subjective "it's a good idea" (which depends on P) will sometimes come apart? (Even if something nice about complexity classes and averages of decision trees might exist?)

\---------------------------------------------------

I've also been reading the longer part of your previous email, and it makes sense and is interesting\! I'll have to think more about your take on my possible solution. Although after writing my "possible solution" paragraph, my feeling had been I should pursue the "extrapolating from the current traders" direction (instead of thinking solely in terms of probability distributions).

\---------------------------------------------------

I adjoin my idea to have finite states of an LI satisfy Reflection and Self-trust, which seems closer to Sam's original BLI motivation.  
I think it works, and the idea of having traders bet on "bundles" of possible worlds (instead of all possible worlds independently), a la credal sets, seems like a natural way to introduce constraints, and might be useful in other settings.

\---------------------------------------------------

Here's my Final report\! [scrubbed] It's very far from a paper, both stylistically and because we're still deciding on which mathematical results to prove. But it's been very useful to write down a lot of thoughts in a more strucutred manner to see the bigger picture, and has given me some ideas.

Thanks, and see you later,  
Martín  
![][image66]  
2 Attachments • Scanned by Gmail  
![][image67]

|  the author [scrubbed]  | Sep 20, 2023, 1:53 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image68]  |  |  |
| :---- | ----- | ----- |

[scrubbed]
![][image69]  
![][image70]

|  Martín Soto  | Sep 20, 2023, 1:55 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image71]  |  |  |
| :---- | ----- | ----- |

[scrubbed]
[scrubbed]
![][image72]  
![][image73]

|  Martín Soto  | Sep 20, 2023, 3:30 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image74]  |  |  |
| :---- | ----- | ----- |

Just flagging the state of the debate about updating on stuff, since it felt central and I want to revise it more calmly:

It seems like the main differences are two  
1\. Explicitly deciding to "forever update on whether the present node has the shape of a Counterfactual Mugging" will keep working forever (modulo changes of mind due to updating other things). On the contrary, it seems like your argument above "assumed that we already know we are in a Counterfactual Mugging", but P only knows this about a finite amount of decision nodes, so it will at some finite time "stop working", and dissolve into P being almost completely uncertain about what happens in that decision node (and maybe this results in updating, maybe it doesn't).  
2\. Also, it seems like your definition of "P believes it is okay to update" is "these kinds of independence happen" (and we think there's no logical sentence expressing this, it's a meta-property of the distribution P). On the contrary, mine was "P believes the policy of "following P but updating on A" has higher expected U than the policy of "following P"". But this difference seems less important, and for example we can modify my proposal to use your definition.

Thanks again for your ideas\!  
![][image75]  
![][image76]

|  the author [scrubbed]  | Sep 21, 2023, 2:29 PM |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image77]  |  |  |
| :---- | ----- | ----- |

Here is my own attempt to summarize and expand upon our discussion.

First of all, there is an important definition question to flag: there are several possible definitions of "P thinks it is a good idea to behave updatefully wrt proposition X". The two main ideas are an expected-utility sense, vs an independence-assumptions sense.

I called my thing one-step UDT, and your thing two-step UDT. I suggested that your concern that my thing inherently has some parameter defining what to be updateful on, is similar to my concern about your thing, which is that if two steps are better than one, N steps might be better than N-1, which also creates an arbitrary parameter.

You clarified that this is also what you expect, and you also argued that this pushes toward arbitrary policy selection (since N steps of thinking how to think may approximate arbitrary procedures).

I clarified that I also believe this may be the case for some class of minds, but I want to codify the assumptions under which one-step UDT is equivalent to N-step UDT. We can *then* assess how realistic those assumptions are and what happens when they are broken. But I still currently believe there is a semi-distinguished set of assumptions where N-step is not needed.

It seemed like I did convince you, modulo more detailed review of my earlier email argument, that in ***individual*** cases where P thinks behaving updatefully with respect to X is a good idea (in the independence-assumptions sense). More specifically, this argument works under the assumption that (1) actual beliefs marginalize correctly (prop & luv coherence), (2) self-trust, (3) hypotheticals also marginalize correctly (so expressions of the form \[variable\](syntactic belief state specification) have correct known values, where 'variable' is a proposition or a LUV; or at least, have correct known values to within some tolerance).

To reiterate my argument a bit: my earlier email worked out the case where P expects a counterfactual mugging, and argued that (under the above-mentioned assumptions) the usual UDT calculation of the expected value falls out of the BLI's expected value calculation. If this argument indeed works, then I claim that similar reasoning will cause UDT to behave updatefully when no acausal correlations exist.

You raised the concern you mention in your email, that this argument depends too strongly on P already anticipating a counterfactual mugging:

Explicitly deciding to "forever update on whether the present node has the shape of a Counterfactual Mugging" will keep working forever (modulo changes of mind due to updating other things). On the contrary, it seems like your argument above "assumed that we already know we are in a Counterfactual Mugging", but P only knows this about a finite amount of decision nodes, so it will at some finite time "stop working", and dissolve into P being almost completely uncertain about what happens in that decision node (and maybe this results in updating, maybe it doesn't).

I now note that if X(node) are propositions claiming that particular nodes are counterfactual muggings, then plausibly my argument applies to all such propositions. In which case we can at least say that if P fails to treat a node as a counterfactual mugging (even though it was knowable that this node was a counterfactual mugging), it's because P saw some reason why it should not do so (in the form of acausal correlations).

However, it remains true that a big difference between my approach and yours is that my approach (apparently, at least) requires *specific* beliefs that *specific* propositions can be treated updatefully (in an independence sense). Despite Universal Instantiation, it remains plausible that P may have a universal belief about some predicate X(node) being good to update on *for all instances*, and that your approach will then do that, where my approach may fail to do that.

This is because the independence-based version of "X is good to update on" apparently has no universal version. As you say:

Also, it seems like your definition of "P believes it is okay to update" is "these kinds of independence happen" (and we think there's no logical sentence expressing this, it's a meta-property of the distribution P). On the contrary, mine was "P believes the policy of "following P but updating on A" has higher expected U than the policy of "following P"".

For some time you argued that there must be an object-level belief which we can universalize. But I asked whether a belief that "forall x, P(A(x)|B(x)) \= P(A(x))" would end up enforcing the independence relation in all cases, vs just enforcing belief in the independence relation. You seemed immediately convinced that this would not work, and you said something about not being able to get universal instantiation to do something like that.

So this question still seems a bit open to me. 

* Does there exist some strengthened BLI for which universal beliefs about independence properties can indeed enforce specific independence properties?  
* Does there exist some alternate way to state my condition, such that it can be universalized? Some object-level beliefs which imply independence?  
* Can some other approach allow generalizations over subjective (non-object-level) stuff? EG, can a pseudo-proposition 'reifying' the conditional probability be introduced? Or can we move beyond probability somehow to make this sort of thing work?

But at present it seems quite plausible that there's no approach which is based on universal generalizations about what's good to update on, like yours, but uses an independence-based idea of "what's good to update on", like mine.

Probably there is still an argument to be had about which approach makes more sense if one has to choose between them. EG, you are suspicious that weird/bad things happen when P runs out of considered opinions, where I am optimistic that this just makes things more updateful. Also, I think you are more optimistic that universal generalizations typically represent real knowledge based on evidence, where I am more suspicious that universal generalizations represent the arbitrary beliefs of traders much more than non-universal beliefs do, since true-in-fact universals cannot always be proved, and there's nothing about logical induction which forces belief in such propositions to be high, even after LI has run for a long long time.

As a final note, I see two holes in my analysis of counterfactual mugging. First, I did not analyze shifting branch probabilities; I only analyzed the expected value of branches when conditioned on policy points. Second, the analysis appears to rely on *certainty* about what U will be in branches of specific types, rather than *expected values*. So the analysis might fall apart if we add Gaussian noise to the final utility. This is again because we can universalize object-level beliefs, like U=-10, but not subjective beliefs, like E(U)=-10. We cannot replace U=-10 with "U probably equals something close to \-10" without making the argument rely on "universal instantiation of beliefs about probabilities enforces those constraints on the probabilities". And even if *that* worked, there might be some cases where the whole thing still fails, since the universal generalization can be spoiled by one case where such a subjective belief would be inappropriate (like, one case where we somehow know the gaussian noise is \+100, so we don't want to instantiate our uncertainty \-- so the universal is actually false, breaking the whole argument).  
![][image78]  
![][image79]

|  Martín Soto  | Sep 24, 2023, 6:58 PM (11 days ago) |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image80]  |  |  |
| :---- | ----- | ----- |

\> I now note that if X(node) are propositions claiming that particular nodes are counterfactual muggings, then plausibly my argument applies to all such propositions. In which case we can at least say that if P fails to treat a node as a counterfactual mugging (even though it was knowable that this node was a counterfactual mugging), it's because P saw some reason why it should not do so (in the form of acausal correlations).

I disagree that "this solves the problem".  
Indeed, what do you mean by "it was knowable that this node was a counterfactual mugging (that is, X(node))"?  
P will have very valid opinions on X(n) for many n (all those it has had time to think about, before being frozen). But for infinitely many of them, it will have some "mostly random guess" (obtained through the extrapolation). For example, for a given very large n, it might think the probability of X(n) is 0.3 (because approximately 0.3 of all the nodes it's seen have been Counterfactual Muggings), and then 0.2 probability that it's Parfit's Hitchhiker, 0.25 that it's another random thing, etc. Say n is indeed a Counterfactual Mugging. Say also that, when this node is reached, our completely updated logical inductor Q\_n already knows that n is a Counterfactual Mugging.  
If we don't implement my thing, P won't "automatically play the Counterfactual Mugging correctly", because it won't have "automatically come to the realization that it's a Counterfactual Mugging". P is uncertain between many things, so it won't sensibly discern actions, and maybe choose a mostly random one. Sure, P might have a belief saying "in these situations I'd be better off checking whether X(n), and if so acting as in a Counterfactual Mugging" (call this policy Policy(n)). But if we're not implementing my thing, this belief won't be used in any way (we won't actually "run" this Policy). P will be uncertain about the value of Policy(n) (because by hypothesis it is uncertain about the value of X(n)), and so will not "run" Policy(n), just play its best guess as to what Policy(n) might be (which is a bad guess).  
So, if by "it was knowable that X(node)" we mean that "P already knew that X(n)", the conclusion follows trivially.  
But if we meant the actually interesting "the completely updated Q\_n knew that X(n)", then the conclusion doesn't follow unless we implement my thing. Indeed, in this example P fails to treat n as a Counterfactual Mugging not because of "worries about acausal correlations", but just because it didn't know X(n) to begin with, and we haven't provided a mechanism for it to update on that knowledge (that is, we have always just implemented P as it was "to begin with").

Another way to say this is as follows:  
Your original argument assumed some beliefs (about X(), Ask() and Rec()), and had as conclusion the right conditioned expectations.  
I don't think there's an analogue version of this argument whose conclusion is "the right probabilistic beliefs about X(n)". You were already assuming the structure, which is, after all, information. We cannot derive this structure from nowhere. We cannot materialize information from thin air (since X(n) is something our P is truly uncertain about).

\> However, it remains true that a big difference between my approach and yours is that my approach (apparently, at least) requires *specific* beliefs that *specific* propositions can be treated updatefully (in an independence sense). Despite Universal Instantiation, it remains plausible that P may have a universal belief about some predicate X(node) being good to update on *for all instances*, and that your approach will then do that, where my approach may fail to do that. This is because the independence-based version of "X is good to update on" apparently has no universal version.

I don't think that the reason why "your proposal eventually stops having information on X(node), while mine has incoming information forever if it chooses to" (main difference 1\. in my previous email) is because your independence-based definition has no universal version.  
In fact, my expectations-based version doesn't have a universal version either, since it talks about to conditionals of P, just like your version (although different conditionals).  
I think these are two "orthogonal" axes of variation (as I tried to represent when talking about them as main differences 1\. and 2\. in my previous email).  
Indeed, "my thing" of adding something on the conditionals (feeding these or those updates to P) is independent from whether these updates are chosen using your definition or my definition.  
So when you say:  
\> But at present it seems quite plausible that there's no approach which is based on universal generalizations about what's good to update on, like yours, but uses an independence-based idea of "what's good to update on", like mine.  
I again think this is not the case, and that using "my thing" (detailed on the document "Deciding what to be updateful about"), but with your definition as the way to choose what to update on, would completely work. It's just a different criterion for choosing what to update on.

So in summary I think both your and my definition are in the same "limbo" of not having a Universal version. But that's okay, because we'll have to ad hoc choose what to update on anyway, and we can define it however we want (in our ad hoc definition to decide what to update on, we are not constrained by "what can be expressed in a probability function").  
Nonetheless, exactly because I'm interested in which "ad hoc mechanisms to implement above the probability distribution" are privileged, your following question is very interesting and natural:  
\> Can some other approach allow generalizations over subjective (non-object-level) stuff? EG, can a pseudo-proposition 'reifying' the conditional probability be introduced? Or can we move beyond probability somehow to make this sort of thing work?  
Indeed, instead of taking the probability distribution and reading some things off it, what if we alter the probability distribution itself (or all states of the inductor) in some other way that more natively lends itself to that information being extracted? I shall think more about this, and my related idea of "extrapolating traders". Although I do think these will all ultimately be "more or less natural/privileged ways of choosing what to update on".

\> Also, I think you are more optimistic that universal generalizations typically represent real knowledge based on evidence, where I am more suspicious that universal generalizations represent the arbitrary beliefs of traders much more than non-universal beliefs do, since true-in-fact universals cannot always be proved, and there's nothing about logical induction which forces belief in such propositions to be high, even after LI has run for a long long time.

That's a very important point that I wasn't considering. Thank you\!  
I guess I have generally indeed taken the approach "LIs don't have ALL properties we'd like, but let's just take their way of reasoning as the baseline for now and see which things we can extract or add on top".

\> This is again because we can universalize object-level beliefs, like U=-10, but not subjective beliefs, like E(U)=-10.

I think this won't be a problem because the argument will go through "in each of the different possible worlds" (the world where U=-9, the one where U=-11, etc.), weighed by their probabilities (instead of the single very likely world U=-10). And this all works out thanks to LUV coherence. But I'll check it properly tomorrow.

\> I want to codify the assumptions under which one-step UDT is equivalent to N-step UDT.

That makes sense. If I am comfortable with N-step UDT, it's mainly because I expect these assumptions to be something tantamount to baking in our desired consequence (because the consequence is broken in lots of natural situations). Of the kind "all checks that the optimal policy (according to P) performs can be performed at once (sequential checks, with dependencies, are not better according to P)". Because that property is fundamentally mind-dependent, and we don't know of another name for it. Or, if we turn to the dynamic setting and check against real feedback instead of P's beliefs (so the property becomes "a prior/LI with access to these N meta-levels won't eventually do better than one with a single level"), it's decision-tree-dependent instead of mind-dependent.

Thank you again for all your thoughts\!  
![][image81]  
![][image82]

|  the author [scrubbed]  | Sep 25, 2023, 6:14 PM (10 days ago) |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image83]  |  |  |
| :---- | ----- | ----- |

Looks like I managed to uncover some remaining disagreements I wasn't aware of\!

  I now note that if X(node) are propositions claiming that particular nodes are counterfactual muggings, then plausibly my argument applies to all such propositions. In which case we can at least say that if P fails to treat a node as a counterfactual mugging (even though it was knowable that this node was a counterfactual mugging), it's because P saw some reason why it should not do so (in the form of acausal correlations).   
   
I disagree that "this solves the problem".  
Indeed, what do you mean by "it was knowable that this node was a counterfactual mugging (that is, X(node))"?

This feels like some sort of miscommunication, so I will try to step thru what I was trying to say very carefully, while also attempting to directly respond to what you are saying.

As stated previously, I think we are somewhat on the same page about the following: given (a) correct marginalization for propositional and luv beliefs ("coherence"), (b) self-trust, and (c) correct marginalization of *hypothetical* propositional and luv beliefs, then *in an individual case where P expects a counterfactual mugging, (one-step) UDT will handle the counterfactual mugging as expected* (as classical UDT calculations expect, that is).

For clarity, I will call this the "single-instance success thesis" (SIST). The argument in favor of SIST is the one marked by "//////////////" in my email from Sept 18\.

Where we differ is on what to expect in cases where P does not already anticipate a specific sort of decision problem. Here is one way of framing it:

* When (classical) UDT is applied to a decision problem, we usually assume that the decision problem occupies the whole prior: UDT knows what decision problem it is about to face, and does not expect any other kind of branch.  
* SIST establishes that my one-step UDT solves that sort of problem.  
* However, you correctly point out that this is not what we realistically expect. We expect UDT to encounter many decision problems which it did not precisely foresee.  
* I take SIST as evidence that one-step UDT "correctly reasons about branches of probability". For me, uncertainty about which of many decision problems will be encountered is a sort of decision problem in itself; if I "correctly reason about branches" then I will handle the more complex case as rationally as I handle the simpler case (but with more uncertainty, of course, which does imply poorer performance). (*Note: this "evidence" is not going to be my main argument. I am not claiming you should find this persuasive. I am just describing my thinking, here.)*  
* You take SIST to be very little or no evidence to this effect. You continue to anticipate that if P does not anticipate a specific decision problem, then my one-step UDT will essentially fail on that decision problem, even if the details of the situation become clear in later Q\_n and P correctly believes that it should behave updatefully on that information (ie, two-step UDT works).

This rough picture of our disagreement became clear during the phone call, although not quite in these terms, so perhaps you will disagree with some aspect of the above characterization. However, it seems consistent with your summary:

Explicitly deciding to "forever update on whether the present node has the shape of a Counterfactual Mugging" will keep working forever (modulo changes of mind due to updating other things). On the contrary, it seems like your argument above "assumed that we already know we are in a Counterfactual Mugging", but P only knows this about a finite amount of decision nodes, so it will at some finite time "stop working", and dissolve into P being almost completely uncertain about what happens in that decision node (and maybe this results in updating, maybe it doesn't).

This brings us to my remark that your latest email begins by quoting:

I now note that if X(node) are propositions claiming that particular nodes are counterfactual muggings, then plausibly my argument applies to all such propositions. In which case we can at least say that if P fails to treat a node as a counterfactual mugging (even though it was knowable that this node was a counterfactual mugging), it's because P saw some reason why it should not do so (in the form of acausal correlations).

I'll call this "the X(node) argument" for convenience.

The general hope of this remark is to argue that SIST implies some degree of "correctly reasoning about branches" which has some positive impact on decision problems which are not already fully encoded in P. I do not claim that this argument gives us everything we might possibly want in this respect. Your first reaction is:

I disagree that "this solves the problem".

I worry this misunderstands my intention. My hope was more limited. My statement of the argument was very brief because I saw it as a bit of a side-show to the more important notes. Indeed, my next paragraph after the argument begins...

However, it remains true that a big difference between my approach and yours is that my approach (apparently, at least) requires *specific* beliefs that *specific* propositions

 ...but it's probably best to set that discussion aside for now and focus on what I *do* hope to establish with the X(node) argument.

You ask:

Indeed, what do you mean by "it was knowable that this node was a counterfactual mugging (that is, X(node))"?

First I'll describe what I mean by "this node is a counterfactual mugging" (that is, X(node)), and then "it was knowable".

The definition of X(node) borrows heavily from my "//////////////" argument:

* There are predicates Rec() and Ask() which apply to whole branches Q. (Ask() is supposed to say something like "Q sees that Omega is asking for \$10", while Rec() is something like "Omega is not asking for \$10 (so I updatefully know that my reward, or lack thereof, is coming soon)".  
* Branches Q such that Rec(Q) believe that Ask(Q') implies A(Q')=give \-\> U=100, and A(Q')=refuse-\>U=0.  
* Branches Q such that Ask(Q) believe that Ask(Q') implies A(Q')=give \-\> \-10, and A(Q')=refuse \-\> U=0.  
* X(node) is just "Rec(node) or Ask(node)"; that is, you believe that either you'll be asked, or on the receiving branch, when you get to "node".

Now for "it is knowable". iirc, our convention was that P \= extrapolate(Q\_n). Suppose that the "node" in question will be on day m. To recognize something as a counterfactual mugging is to recognize it *ahead* of time; so "it is knowable" means that there is some c such that n\<c\<m, and such that X(node) has a high probability in Q\_c. Suppose for the moment that the probability was negligible before time c, and furthermore, *no other* acausal impacts on this decision node rise to high probability before the proposition X(node) does. Then my argument for SIST (the "//////////////" argument) applies to the expected value of the relevant policy-points down that specific branch.

Now furthermore suppose that the proposition X(node) itself is one which P thinks it should behave updatefully about, which is to say, it meets the relevant independence assumptions in P, such that SIST implies that the proposition X(node) is one which will be treated in an updateful manner (by single-step UDT). (For emphasis: this does not mean that P knows X(node); rather, P is such that one-step UDT will treat X(node) as true *or as false* depending on what more-updated opinions say).

Then since single-step UDT behaves updatefully about X(node), and knows X(node) at time c, it will treat "node" as a counterfactual mugging, in the same way that it would if P had believed X(node) from the beginning. Except, the branch probabilities for Rec(Q) vs Ask(Q) get derived from extrapolate(Q\_c) rather than P.

This seems to establish the desired result, which is that **if one-step UDT fails to treat a node as a counterfactual mugging, even though it was knowable that the node would be a counterfactual mugging** (ie, Q\_c comes to be confident in X(node))**, it's because P saw some reason why it should not do so** (ie, P thinks some other acausal influences deserve more consideration, meaning either: X(node) does not look worthy of updateful treatment, or "node" is involved in some other important acausal business before Q\_c).

This conclusion is a moderate extension of SIST: I argue that single-step UDT not only gets problems right if P expects them; it also gets problems right if some intermediate Q\_c sees them coming, and P sees no reason to ignore that information. So I will call this FIST, "foreseeable instance success thesis" (although I make no claims that these abbreviations are optimal descriptions of the thing abbreviated).

Having explained my intended argument more thoroughly, I'll now move on to address your criticisms:

P will have very valid opinions on X(n) for many n (all those it has had time to think about, before being frozen). But for infinitely many of them, it will have some "mostly random guess" (obtained through the extrapolation). For example, for a given very large n, it might think the probability of X(n) is 0.3 (because approximately 0.3 of all the nodes it's seen have been Counterfactual Muggings), and then 0.2 probability that it's Parfit's Hitchhiker, 0.25 that it's another random thing, etc. Say n is indeed a Counterfactual Mugging. Say also that, when this node is reached, our completely updated logical inductor Q\_n already knows that n is a Counterfactual Mugging.  
If we don't implement my thing, P won't "automatically play the Counterfactual Mugging correctly", because it won't have "automatically come to the realization that it's a Counterfactual Mugging". P is uncertain between many things, so it won't sensibly discern actions, and maybe choose a mostly random one. Sure, P might have a belief saying "in these situations I'd be better off checking whether X(n), and if so acting as in a Counterfactual Mugging" (call this policy Policy(n)). But if we're not implementing my thing, this belief won't be used in any way (we won't actually "run" this Policy). P will be uncertain about the value of Policy(n) (because by hypothesis it is uncertain about the value of X(n)), and so will not "run" Policy(n), just play its best guess as to what Policy(n) might be (which is a bad guess).

I hope it is clear that I am not denying this. An arbitrary P can think that the world has some arbitrary acausal considerations, which will result in some arbitrary behavior.

On the other hand, I don't think two-step UDT totally changes this, either, since the quality of the two-step process is still dependent on sanity on the part of P.

So, if by "it was knowable that X(node)" we mean that "P already knew that X(n)", the conclusion follows trivially.  
But if we meant the actually interesting "the completely updated Q\_n knew that X(n)", then the conclusion doesn't follow unless we implement my thing.

Hope it's clear that I meant neither of these things; rather, X(node) should be known by some intermediate Q\_c.

Indeed, in this example P fails to treat n as a Counterfactual Mugging not because of "worries about acausal correlations", but just because it didn't know X(n) to begin with, and we haven't provided a mechanism for it to update on that knowledge (that is, we have always just implemented P as it was "to begin with").

Hope it's clear why I think this is false (under some assumptions I've articulated).

Another way to say this is as follows:  
Your original argument assumed some beliefs (about X(), Ask() and Rec()), and had as conclusion the right conditioned expectations.  
I don't think there's an analogue version of this argument whose conclusion is "the right probabilistic beliefs about X(n)". You were already assuming the structure, which is, after all, information. We cannot derive this structure from nowhere. We cannot materialize information from thin air (since X(n) is something our P is truly uncertain about).

I hope I've convinced you that there is an analogous version of the argument, which extends SIST slightly into the case where X(n) is truly uncertain for P.

This completes my remarks on the "X(node) argument" portion of your email.

\================

The rest of this email pertains to the rest of your email.

I don't think that the reason why "your proposal eventually stops having information on X(node), while mine has incoming information forever if it chooses to" (main difference 1\. in my previous email) is because your independence-based definition has no universal version.  
In fact, my expectations-based version doesn't have a universal version either, since it talks about to conditionals of P, just like your version (although different conditionals).  
I think these are two "orthogonal" axes of variation (as I tried to represent when talking about them as main differences 1\. and 2\. in my previous email).

I was initially quite surprised to read this. A major motivation behind me writing my email was that *your* email suggested that 1 and 2 were orthogonal, whereas I had come away from our meeting with the impression that we had mutually concluded that they were not orthogonal. I thought this was your reason to think two-step could still be superior to one-step, even under my assumptions for getting one-step to work: because two-step UDT can "decide to update forever" while one-step UDT can "only know things about a finite number of decisions".

So I've finally consulted your pdf detailing the two-step procedure. I see that the relevant distinction is something like "always good to update" vs "good to always update". You don't look for generalizations about what's good to update on, but instead, you check the expeted value of computer programs which enumerate things to be updateful about.

But I'm still not seeing how a two-step independence-based UDT could achieve this sort of updatefulness about infinitely many sentences. So (1) and (2) still don't appear orthogonal to me.

By the way, I think this is not *quite* true: 

so it will at some finite time "stop working", and dissolve into P being almost completely uncertain about what happens in that decision node (and maybe this results in updating, maybe it doesn't).

The SIST argument can handle the case where *every* decision node is (believed to be) a counterfactual mugging: forall n, X(n) can be known, in which case X(n) is known for infinitely many cases, so one-step UDT does not sputter out into oblivion (or updatefulness). Of course, this does not appear to be a very general exception to the rule. The problem, as you have said, is that if we try to put conditions on this belief (forall n: Y(n) \-\> X(n)), then P will only know the *condition* for finitely many instances (or for all instances, if P believes forall n: Y(n)).

 I want to codify the assumptions under which one-step UDT is equivalent to N-step UDT.

That makes sense. If I am comfortable with N-step UDT, it's mainly because I expect these assumptions to be something tantamount to baking in our desired consequence (because the consequence is broken in lots of natural situations). Of the kind "all checks that the optimal policy (according to P) performs can be performed at once (sequential checks, with dependencies, are not better according to P)". Because that property is fundamentally mind-dependent, and we don't know of another name for it. Or, if we turn to the dynamic setting and check against real feedback instead of P's beliefs (so the property becomes "a prior/LI with access to these N meta-levels won't eventually do better than one with a single level"), it's decision-tree-dependent instead of mind-dependent.

I am not sure I understand, but perhaps the FIST idea illustrates that this is not the case? IE, FIST shows that a class of cases violating "all checks that the optimal policy performs can be performed at once, rather than sequentially" can be handled by one-step UDT as effectively as n-step UDT would handle them?

Specifically, something like distributions over finitely many finite decision trees, *or* trees having a sufficiently "IID" character such that universal beliefs about what decision problem is being faced can apply to every single node. Such properties apparently imply identicality of one-step and multi-step UDT without mention of "all checks can be performed at once", and in particular, the FIST argument illustrated how one-step can perform important checks at some intermediate point between P and the actual decision time.

So (barring other ideas, like solving the subjective generalization problem), it looks like the value of the two-step procedure is for more complex infinite trees.

Also note that I still expect that under some conditions, one-step UDT will become more updateful rather than dissolve into nonsense. One such condition is that P does not have false universal beliefs held strongly. Suppose, then, that I devote N traders with high starting wealth to vote against the N smallest universal statements. (I use N different traders rather than one so that others remain, if some are knocked out of the market by their cherished anti-belief being proved.) With this, and presumably some other assumptions, perhaps it is possible to get back to the early idea I had about a UDT which acts in a slightly more updateful way as it runs out of opinionated beliefs in P \-- although this still only gets finitely many steps of such behavior, obviously, so it's not that great.

It would be really nice to have some kind of statement of limited negtive impact from false universal beliefs in P. For exmple, an optimistic dream would be if P eventually sees fit to behave updatefully about such beliefs. After all, if you're quite sure that you are right, what could be the harm *in principle* of being willing to update away from that belief in the face of a counterexample (which you will 'never' see)? If some result like this were true, it might allow one-step UDT to have good properties for infinitely many nodes. (But I'm not actually very optimistic about this.)

Best,  
The author  
![][image84]  
![][image85]

|  Martín Soto  | Sep 26, 2023, 11:07 AM (9 days ago) |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image86]  |  |  |
| :---- | ----- | ----- |

\> As stated previously, I think we are somewhat on the same page about the following: given (a) correct marginalization for propositional and luv beliefs ("coherence"), (b) self-trust, and (c) correct marginalization of *hypothetical* propositional and luv beliefs, then *in an individual case where P expects a counterfactual mugging, (one-step) UDT will handle the counterfactual mugging as expected* (as classical UDT calculations expect, that is).

I confirm I agree with this, provided some smaller caveats of the form "no evil coins in other parts of the tree (that P knows about) prevent this". Also, let me note my understanding is that (c) is the Reflection Principle.

\> SIST establishes that my one-step UDT solves that sort of problem.

SIST solves Counterfactual Mugging (assuming, of course, P knows we're in a Counterfactual Mugging).  
I claim **SIST *doesn't* solve other problems, even when P knows we're in that problem**. (This is our first disagreement on the truth of a technical point.)  
**An example is Counterfactual Mugging with Math Homework** (you have to state the correct digit of pi when paying up). Here's why:

In regular Counterfactual Mugging, "all information is already in P". In particular, P already knows (or better said "we assume it has a good guess about") the probability with which the logical coin turns out true (in your example, you assume P knows the probabilities of Ask(Q\_m) and Rec(Q\_m)). Given this situation, the right action is taken.  
But in Counterfactual Mugging with Math Homework, assume P \= extrapolate(Q\_k) was not advanced enough to know the digit of pi, but that round at which the game is played (Q\_m) is indeed advanced enough to actually know the digit of pi. Assume further that P, as above, already knows (or "has a good guess at") the probabilities Ask(Q\_m) and Rec(Q\_m). Assume these probabilities and the payoff are such that P knows it's better to Pay (by stating the correct digit) in Ask(). This will be witnessed by the fact that E(U | A(Q\_m)="If Ask(Q\_m), then output CorrectDigit") is high (where the expectation is taken according to P). Here CorrectDigit is a formula defining what it means to "be the actual digit of pi at that position", but P won't have a good guess as to which is the actual correct digit (which digit satisfies the formula CorrectDigit). Without any further mechanism, this will remain the case when we compute the values of E(U | A(Q\_m)=Not Pay), E(U | A(Q\_m)=(Pay, 0)), E(U | A(Q\_m)=(Pay, 1)), etc., where the action corresponds to deciding whether to Pay, and if so also stating a digit. In particular, since P doesn't know which is the correct digit, there won't be one E(U | ... ) that is higher than the rest (attaining full payoff). On the contrary, all of them will have a mediocre payoff, corresponding to "one tenth probability of guessing it correctly". So P clearly "could have known" the correct digit (maybe P even knows explicitly that Q\_m knows the correct digit), but doesn't take advantage of that knowledge because *it's just a frozen prior*, and we haven't allowed it any mechanism to update.

In fact, this problem (not allowing absolutely any kind of updating) **also affects regular Counterfactual Mugging,** except when we formalize the decision problem in one concrete way (facilitating it for updateless agents).  
Say we formalize it as follows: no matter what happens (whether Ask(Q\_m) or Rec(Q\_m)), A will have to decide between Pay and Not Pay. And then, of course, if Receive(Q\_m) is the case, this action is completely ignored. In this case (or any equivalent formalization in which "you don't have to distinguish between Ask() and Receive()"), your argument works. P knows that it will be either in Ask() or in Rec(), and knows that in both those cases it can take the same action (because one of them is irrelevant).  
But say now we formalize it as follows: if Rec(Q\_m) is the case, the action is not ignored, and Paying indeed leads tu losing that amount of money (although you possibly also receive the big payoff thanks to your counterfactual). This more naturaly reflects the "freedom of action" of the real world, in which taking a non-sensical action fit for a different situation (like arbitrarily giving \$10 bills to people who aren't even asking for them) can result in bad outcomes. In this case, you clearly want to first check whether you're in Ask() or Rec(), and then only Pay if you're in Ask(). But again, we cannot achieve this without updating on something (granted P doesn't already know whether Ask(Q\_m) or Rec(Q\_m), that is, hasn't already completely decided the logical coin). Your argument does show that P will take all of this into account, and if even with this arbitrary Pay the policy of always Paying is better (because the other payoff is big enough), it will do so. But we are of course losing money senselessly, when we could perfectly fix the policy of updating on whether Ask() or Rec() and deciding whether to Pay accordingly (that is, never paying in Rec(), but still paying in Ask() if the global calculation saw it as optimal).

Note all of this applies exactly if we consider some state k\<c\<m as you do in your email, instead of Q\_m itself, that already knows the updated information.  
(But now that makes less sense to worry about, since you were asking for c\<m to ensure the agent could see the Counterfactual Mugging coming "in advance", while here I'm dealing with information that can be exploited just the same by receiving it exactly at time m.)

\> You take SIST to be very little or no evidence to this effect. You continue to anticipate that if P does not anticipate a specific decision problem, then my one-step UDT will essentially fail on that decision problem, even if the details of the situation become clear in later Q\_n and P correctly believes that it should behave updatefully on that information (ie, two-step UDT works).

Exactly, and my worry here is: Even if P knows "Q\_n will be right" and "Behaving updatefully is better", *how* will it obtain the updated information? The only way would be for it to already have it\! SIST only shows that, *once* this information is available, P reasons correctly with it. Let me reason in more detail in the context of your next quote:

\> Now furthermore suppose that the proposition X(node) itself is one which P thinks it should behave updatefully about, which is to say, it meets the relevant independence assumptions in P, such that SIST implies that the proposition X(node) is one which will be treated in an updateful manner (by single-step UDT). (For emphasis: this does not mean that P knows X(node); rather, P is such that one-step UDT will treat X(node) as true *or as false* depending on what more-updated opinions say).

I think this is not the case. (This is our second disagreement on the truth of a technical point.)  
Maybe there's a confusion going on as to what "one-step UDT" means.  
If by "one-step UDT" you mean something like "first we check which independence relations P believes to hold, and then, when the decision node comes, we update P on the information it believes it's safe to be updateful about (by adding it into the conditional)", then indeed updating works as you say. This is just "my thing" implemented with your definition of "it's safe to update on this fact".  
If instead you mean "we just compute E(U | A(Q)=a) as usual, without any additional mechanism (for example, adding anything on the conditional which is not just A(Q)=a)", then I claim your quoted argument doesn't work. (And I do think this is the version you have in mind.)  
The SIST argument shows that P reasons correctly when conditioned on different things. That is, provided the information (for example, Ask(Q) & A(Q)=Pay), it yields the desired beliefs about U. I don't see how it shows that P *attains* the right probabilities on these different conditionals (for example, being in a Counterfactual Mugging), when conditioned *just on sentences of the form* A(Q)=a.

And again, the "conceptual" reason why all of these "technical caveats" hold is that "if P doesn't have a belief already, the only way for it to obtain it is by adding stuff to the conditional, otherwise it will not appear magically (unless it is a consequence of A(Q)=a, the base conditional, but in the above cases this is not the case since uncertainty remains about what future we will inhabit)". That is, "everything is updating (including thinking about whether this node has this or that syntactic structure), and someone somewhere has to decide to perform that update (if the knowledge wasn't already present in P)".

\> The general hope of this remark is to argue that SIST implies some degree of "correctly reasoning about branches" which has some positive impact on decision problems which are not already fully encoded in P. I do not claim that this argument gives us everything we might possibly want in this respect.

I do share the opinion that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems". That's why, even when P thinks that node has probability one third of being a Counterfactual Mugging, one third Parfit's Hitchhiker, one third something different, it will "correctly" (from its subjective perspective) assess between its available options, and maybe act as if playing the Counterfactual Mugging (or the Parfit's Hitchhiker) because it has high enough payoff, thus giving up on the worlds where it turns out to not be a Counterfactual Mugging. What I'm saying is: we can do this, but when the agent thinks it'd be better off updating (it satisfies independence), it is clearly sub-optimal to keep this course of thought and action, as opposed to deciding to update on whether node is a Counterfactual Mugging. So let's implement that instead.

\> I hope it is clear that I am not denying this. An arbitrary P can think that the world has some arbitrary acausal considerations, which will result in some arbitrary behavior.

To clarify, what I'm trying to argue is "even if P has all the correct beliefs to understand this decision problem (but is not omniscient), then it will *not be able to* act optimally (even if it thinks that'd score higher) unless we give it a mechanism to ad hoc update".  
It's true that an arbitrarily dumb P will act wrong both here, and in my proposal. That's not what I'm arguing.

\> Hope it's clear that I meant neither of these things; rather, X(node) should be known by some intermediate Q\_c.

I also want to make explicit that I think my technical caveats (the ones I'm expliciting here, and that I was referencing on the previous email too) don't depend at all on whether we take some intermediate Q\_c, or the latest possible Q\_m.

\================

\> But I'm still not seeing how a two-step independence-based UDT could achieve this sort of updatefulness about infinitely many sentences. So (1) and (2) still don't appear orthogonal to me.

(I'm less sure about the following, and will try to write the proposal completely and formally before tomorrow, which will probably help us.)

It's true when doing "my thing" (explicitly deciding what to update on) with "your definition" (independence) we no longer have "a single quantified sentence we can condition on". But nonetheless we can implement it by checking one by one what P believes about the correlations between particular nodes.  
Instead of checking for E(U | sigma) at the start and being done with it, just check at each decision node / level of the tree whether P believes that the independence properties hold (and we check this by reading some conditionals of P). For example, even for very far-off nodes n, n' we will have certain values for P(n=Ask | A(n')=a\_1) and P(n=Ask | A(n')=a\_2), which witness whether the nature of the node n is independent from actions taken in n'. It's true that for very far-off nodes Q\_k (the finite seed for P) will never have thought about the numbers n, n', so the numbers P has on them will have been determined completely through Universal Instantiation, based on some general beliefs. And these might be of a lower accuracy that beliefs about simple things. That's partly why I feel like we need to "decide what to update on instrumentally at the beginning, based on consequences": maybe in many instances P would rather think longer about whether n and n' have this or that structure, and only then assess independence. But the point stands that this is a coherent proposal (even if I prefer mine).

More generally, I continue feeling like "my definition" (checking expected U) is superior to "your definition" (independence) because with yours we are already baking in more knowledge than we'd probably rather Q discover by itself naturally. We are imposing that "it is good to update exactly when this is the case". And I'm like, "no, let's let Q decide when it's good to update". This will play off particularly well in situations with Eventual Learning (like Policy Selection).

\> The SIST argument can handle the case where *every* decision node is (believed to be) a counterfactual mugging

You are completely right, but of course I wanted something more general, and I think we need my kind of "deciding what to update on" for that.

I sadly have to leave now, but soon I'll answer the last part of your email ("I am not sure I understand, but...").  
Thank you so much again for all of your thoughts\!

P.S: This is the 100th email in this thread. Wooohoooo\! :-D  
![][image87]  
![][image88]

|  the author [scrubbed]  | Sep 26, 2023, 1:30 PM (9 days ago) |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image89]  |  |  |
| :---- | ----- | ----- |

This of course deserves an extensive response, but I'll try and focus on brief responses for now, for a quick easy to read email:

Also, let me note my understanding is that (c) is the Reflection Principle.

I don't understand what you mean by this. In my current understanding, (c) is something like: for expressions of the form \`proposition\`, where Q is as usual a big explicit market state, and \`prop\` represents marginalizing Q in the given proposition, P already knows the correct value of those expressions (with some epsilon uncertainty added, perhaps). Is this "the reflection principle"? Perhaps you meant to say (b) is the reflection principle, instead? (Daniel Hermann called (b) Reflection, iirc)

SIST solves Counterfactual Mugging (assuming, of course, P knows we're in a Counterfactual Mugging).  
I claim **SIST *doesn't* solve other problems, even when P knows we're in that problem**. (This is our first disagreement on the truth of a technical point.)  
**An example is Counterfactual Mugging with Math Homework** (you have to state the correct digit of pi when paying up). Here's why:

Ah, a very surprising claim\! I'll have to dig into your argument. It seems evident to me at the moment that my argument wrt Counterfactual Mugging generalizes to "all the problems UDT is typically understood to solve", but of course I have not formalized that or provided any explicit argument for it. (FIST is supposed to be further evidence to this effect, though.)

\> You take SIST to be very little or no evidence to this effect. You continue to anticipate that if P does not anticipate a specific decision problem, then my one-step UDT will essentially fail on that decision problem, even if the details of the situation become clear in later Q\_n and P correctly believes that it should behave updatefully on that information (ie, two-step UDT works).

Exactly, and my worry here is: Even if P knows "Q\_n will be right" and "Behaving updatefully is better", *how* will it obtain the updated information? The only way would be for it to already have it\! SIST only shows that, *once* this information is available, P reasons correctly with it.

This makes complete sense to me *with respect to infinite trees* (beyond the fairly trivial ones SIST can already get, like where you face a counterfactual mugging at every node). I currently see the difficulty of going from something like \\forall n: X(n) to something like \\forall n: Y(n) \-\> X(n) (because P does not know Y(n)). I currently do not see the difficulty for finite cases (but I need to go over your email in more detail\!)

Let me reason in more detail in the context of your next quote:  
 \[...\] SIST implies that the proposition X(node) is one which will be treated in an updateful manner \[...\]  
I think this is not the case. (This is our second disagreement on the truth of a technical point.)

Again, a very surprising claim\! (IE I'm surprised that you think this *after* reading my clarified argument)  
   
Maybe there's a confusion going on as to what "one-step UDT" means.  
\[...\]  
If instead you mean "we just compute E(U | A(Q)=a) as usual,

Affirming that I use "one-step UDT" to mean *just* argmaxing E(U|A(Q)=a). No *extra* step is needed to account for (the independence version of) what P thinks it should behave updatefully about, because (the [point of the independence version](https://www.lesswrong.com/posts/W6nXfmKTrgaiaLSRg/why-and-why-not-bayesian-updating) is) UDT over P just already acts like that.

I do share the opinion that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems".

I'll have to think about how you can believe this while disagreeing with my other claims.  
   
It's true when doing "my thing" (explicitly deciding what to update on) with "your definition" (independence) we no longer have "a single quantified sentence we can condition on". But nonetheless we can implement it by checking one by one what P believes about the correlations between particular nodes. \[...\]  It's true that for very far-off nodes Q\_k (the finite seed for P) will never have thought about the numbers n, n', so the numbers P has on them will have been determined completely through Universal Instantiation, based on some general beliefs.

Hmm. So basically, iiuc, you are pointing out that P may indeed have the required independence assumptions for infinitely many sentences, although these opinions may not be very good. Yeah, seems plausible. Although I would be happier with a more detailed picture.

It's true that for very far-off nodes Q\_k (the finite seed for P) will never have thought about the numbers n, n', so the numbers P has on them will have been determined completely through Universal Instantiation, based on some general beliefs. And these might be of a lower accuracy that beliefs about simple things. That's partly why I feel like we need to "decide what to update on instrumentally at the beginning, based on consequences": maybe in many instances P would rather think longer about whether n and n' have this or that structure, and only then assess independence. But the point stands that this is a coherent proposal (even if I prefer mine).

I want to flag that this feels like a *less important disagreement*, but we're pretty far down the rabbit hole right now, and it feels like we just have a ton of detailed disagreements ... so anyway, flagging that the above does not quite make sense to me, as a distinction between the two theories (independence-based two-step and EV-based two-step). The expected value version has to entertain an arbitrarily limited number of hypotheses about which algorithm to use to decide which sentences to be updateful on, because (a) we want the argmax to be a terminating computation; (b) P will only have "good" opinions about some bounded number of such algorithms, so if we argmax over too many options, we stand a good chance of getting a bad result (much like algorithmic-policy selection). So both two-step theories have a "large-sentence opinions are bad" problem.

More generally, I continue feeling like "my definition" (checking expected U) is superior to "your definition" (independence) because with yours we are already baking in more knowledge than we'd probably rather Q discover by itself naturally. We are imposing that "it is good to update exactly when this is the case". And I'm like, "no, let's let Q decide when it's good to update". This will play off particularly well in situations with Eventual Learning (like Policy Selection).

The expected-utility version is of course a more obvious translation of "UDT thinks it would be good to update". I agree that it is superior. So why focus on the independence version? Because this is the version which is most directly tied to [the math of when UDT behaves updatefully](https://www.lesswrong.com/posts/W6nXfmKTrgaiaLSRg/why-and-why-not-bayesian-updating). IE, it is *supposed* to be the version which *has the most hope* of equivalence between two-step and one-step (but of course this is what we are debating). So basically, I am trying to work my way up to a tiling theorem in baby steps. If I got something working for the independence version, then a next step could be to find the assumptions under which the two notions of happy-to-update are equivalent.

Conceptually, two-step UDT is like policy selection in the sense that it makes direct modifications to its (final-step) decision procedure. I could get behind this in the end if it turned out to be the simplest way of achieving a tiling theorem. Maybe the best way to achieve reflective coherence is to pre-emptively make (a specific class of) self-modifications. But you do not even expect this \-- you expect three-step, four step, etc to all be different (and in some sense further improvements). In my view, this leaves us afloat in decision-theory space, with no special notion of rationality.

My primary aim with decision theory work is to specify a decision rule which tiles \-- something such that (under some assumptions, of course) it is already equivalent to any self-modifications it would approve of.

Of course, proving this goal to be impossible is of equal interest, and a major goal with the summer project was always to find the impossibility theorems where they exist.

Best,  
The author

   
...

![][image90]

|  Martín Soto  | Sep 26, 2023, 6:08 PM (9 days ago) |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to me ![][image91]  |  |  |
| :---- | ----- | ----- |

Quick thoughts to help you probe my opinions.

Meta-point: I think the most efficient step now would be to try and completely flesh out technical disagreements one and two (but especially one) on a whiteboard, either running through my argument and trying to see where you disagree, or the other way around. I suspect we might be disagreeing in some small implicit assumption that decides whether the argument goes through.

I don't understand what you mean by this. In my current understanding, (c) is something like: for expressions of the form \`proposition\`, where Q is as usual a big explicit market state, and \`prop\` represents marginalizing Q in the given proposition, P already knows the correct value of those expressions (with some epsilon uncertainty added, perhaps). Is this "the reflection principle"? Perhaps you meant to say (b) is the reflection principle, instead? (Daniel Hermann called (b) Reflection, iirc)  
   
Thank you for your clarification on (c). You are right that it is not exactly the Reflection Principle. In fact, (b) \+ (c) yield the Reflection Principle.

Ah, a very surprising claim\! I'll have to dig into your argument. It seems evident to me at the moment that my argument wrt Counterfactual Mugging generalizes to "all the problems UDT is typically understood to solve", but of course I have not formalized that or provided any explicit argument for it. (FIST is supposed to be further evidence to this effect, though.)

Just to express my opinion in different words: I think you're hiding under the rug some crucial small facts we need to update on, to ensure the desired updateful behavior, since they are not already present in P (and any "breaking up the situation into different worlds/conditionals" that might extract that knowledge amounts to already having the knowledge). From my perspective, you are examining the bells and whistles of an alleged perpetual motion machine. (Of course, it'd be better if I had managed to prove impossibility, while for now I'm just communicating technical points.)

This makes complete sense to me *with respect to infinite trees* (beyond the fairly trivial ones SIST can already get, like where you face a counterfactual mugging at every node). I currently see the difficulty of going from something like \\forall n: X(n) to something like \\forall n: Y(n) \-\> X(n) (because P does not know Y(n)). I currently do not see the difficulty for finite cases (but I need to go over your email in more detail\!)

Well, my argument is of the shape "if P doesn't already have that information within itself, we'll have to update on it to use it, no alternative exists". And I think this can apply both to infinite and finite trees, unless P already knows everything there is to know about the finite tree, but this will usually not be the case (or not be the optimal Q\_k to use, since it'd be too updated).

\> I do share the opinion that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems".  
I'll have to think about how you can believe this while disagreeing with my other claims.

To be clear, I was saying something fairly basic, like the following:  
Obviously P doesn't compartmentalize its reasoning artificially into small decision problems (it just thinks about the whole tree), so the nice properties of thinking about the possible future branches (with P's uncertainty) and assessing what's best are also used "between decision trees", for example when P is unsure about which decision problem it finds in a node. But at the same time, I challenge the further claim that, through some circuitous chain of reasoning, P can act updatefully about a fact it doesn't actually know (when still only being conditioned on A(Q)=a, and nothing else). For example, the claim that even if P is unsure about whether the next node is a Counterfactual Mugging or Parfit's Hitchhiker, if the next inductor state knows it (and P thinks it's safe to update on it), then E(U | A(Q)=a) will automatically represent this knowledge obtained from the next inductor state.

flagging that the above does not quite make sense to me, as a distinction between the two theories (independence-based two-step and EV-based two-step). The expected value version has to entertain an arbitrarily limited number of hypotheses about which algorithm to use to decide which sentences to be updateful on, because (a) we want the argmax to be a terminating computation; (b) P will only have "good" opinions about some bounded number of such algorithms, so if we argmax over too many options, we stand a good chance of getting a bad result (much like algorithmic-policy selection). So both two-step theories have a "large-sentence opinions are bad" problem.

You are completely right, thank you for pointing that out\! Thus my vague intuitive argument for the superiority of "EV-based two-step" actually suffers the same limitation, and so my reasons for choosing EV-based over independence-based have limited to just "we intuitively want to ask the agent what it thinks, instead of doing that work for it".  
Although I understand your later point about using independence-based to get tiling through baby steps. I think this won't work because we'll somewhere have to "choose what to update on", and whenever the prior is such that it actually updates, tiling is not guaranteed (except under some very tight constraints of the form "updating didn't make that big a difference after all").  
I also note another kind of argument to decide between independence-based and EV-based: in the case where we get Eventual Learning, maybe through periodically re-freezing the prior, or through ever-increasing the N-meta levels of policy selection, one of the two definitions might present better behavior. But actually I suspect both will converge on the right things.

I could get behind this in the end if it turned out to be the simplest way of achieving a tiling theorem.

To be clear (and similar to what I just mentioned), I don't expect these Policy Selection-like shoe-hornings of learning into our UDT to tile, except under some very tight constraints which amount to "updating wasn't so important after all". I for now feel like, in a dynamic learning-theoretic setting like ours, there's a fundamental trade-off between the Dynamic stability of strategic updatelessness and the Eventual learning we can find in Policy Selection. (In fact I shortly mentioned this in [my talk](https://www.youtube.com/watch?v=uNv1Cq-aVKY&t=810s&ab_channel=PIBBSSFellowship).)

Thank you again, this is all very exciting\! We're closing in on stuff\!  
...

\[Message clipped\]  [scrubbed]  
Attachments area  
[Preview YouTube video Martin Soto \- Constructing Logically Updateless Decision Theory \- PIBBSS Symposium '23](https://www.youtube.com/watch?v=uNv1Cq-aVKY&t=810s&authuser=0)  
[![][image92]](https://www.youtube.com/watch?v=uNv1Cq-aVKY&t=810s&authuser=0)  
[![][image93]](https://www.youtube.com/watch?v=uNv1Cq-aVKY&t=810s&authuser=0)  
[![][image94]](https://www.youtube.com/watch?v=uNv1Cq-aVKY&t=810s&authuser=0)

|  the author [scrubbed]  | Sep 27, 2023, 1:06 AM (8 days ago) |
| :---- | :---- |

|  |  |
| :---- | :---- |

|  to Martín ![][image95]  |  |  |
| :---- | ----- | ----- |

Since this is so soon before our next meeting, I'm not particularly expecting you to read it; I'm writing this to organize some thoughts about your argument, but I might as well send it.

In regular Counterfactual Mugging, "all information is already in P". In particular, P already knows (or better said "we assume it has a good guess about") the probability with which the logical coin turns out true (in your example, you assume P knows the probabilities of Ask(Q\_m) and Rec(Q\_m)). Given this situation, the right action is taken.  
But in Counterfactual Mugging with Math Homework, assume P \= extrapolate(Q\_k) was not advanced enough to know the digit of pi, but that round at which the game is played (Q\_m) is indeed advanced enough to actually know the digit of pi. Assume further that P, as above, already knows (or "has a good guess at") the probabilities Ask(Q\_m) and Rec(Q\_m). Assume these probabilities and the payoff are such that P knows it's better to Pay (by stating the correct digit) in Ask(). This will be witnessed by the fact that E(U | A(Q\_m)="If Ask(Q\_m), then output CorrectDigit") is high (where the expectation is taken according to P). Here CorrectDigit is a formula defining what it means to "be the actual digit of pi at that position", but P won't have a good guess as to which is the actual correct digit (which digit satisfies the formula CorrectDigit). Without any further mechanism, this will remain the case when we compute the values of E(U | A(Q\_m)=Not Pay), E(U | A(Q\_m)=(Pay, 0)), E(U | A(Q\_m)=(Pay, 1)), etc., where the action corresponds to deciding whether to Pay, and if so also stating a digit. In particular, since P doesn't know which is the correct digit, there won't be one E(U | ... ) that is higher than the rest (attaining full payoff). On the contrary, all of them will have a mediocre payoff, corresponding to "one tenth probability of guessing it correctly". So P clearly "could have known" the correct digit (maybe P even knows explicitly that Q\_m knows the correct digit), but doesn't take advantage of that knowledge because *it's just a frozen prior*, and we haven't allowed it any mechanism to update.

I'm not really seeing any argument/analysis here to conclude that this is what one-step UDT does, other than the classic "UDT doesn't update, so it won't act updateful" error.

So let me run thru my argument as to why it does the right thing here.

We assume it knows that it is in cf-mugging-with-homework. To spell that out a bit more, we assume that rather than yes or no, Omega takes the \$10 in the case that we utter the digit of pi in question. (Not sure if this is exactly the version you had in mind.) Let's say even-numbered branches get asked for \$10 (and must utter the digit to agree), while odd-numbered branches are receivers. (Maybe for digit 5 Omega checks whether the agent would give up \$10 on 4, etc, pairing everything off.)

Recall that (my argument for) regular cf mugging used two branch predicates, Ask and Rec, obeying the following:

* Branches Q such that Rec(Q) believe that Ask(Q') implies A(Q')=give \-\> U=100, and A(Q')=refuse-\>U=0.  
* Branches Q such that Ask(Q) believe that Ask(Q') implies A(Q')=give \-\> \-10, and A(Q')=refuse \-\> U=0.

Instead, we now add a branch for each numeral the digit of pi could be, with appropriate payoffs. By the "///////" style argument, all of these branch payoffs are correctly evaluated for each policy-point we can consider.

So for example, suppose that the true Q\_m knows that the relevant digit of pi is 4\. When we condition P on the policy point which says 4 upon seeing that Q\_m; ie, we look at E\_{P}(U | A(Q\_m)=4). 

As in the "/////" argument, we decompose the expectation into a sum over the different possible branches. A(Q\_m)=4 will look like a \-10 decision to 4-branches (again I am pretending that it is reasonable to assume that decisions are 100% correlated across similar branches, which I don't actually think is a reasonable assumption, but it makes the math a lot simpler), but it will look like a \+100 decision for all 5-branches. No other significantly-probable sort of branch will have significant opinions. So the strategy will look good.

In fact, this problem (not allowing absolutely any kind of updating) **also affects regular Counterfactual Mugging,** except when we formalize the decision problem in one concrete way (facilitating it for updateless agents).  
Say we formalize it as follows: no matter what happens (whether Ask(Q\_m) or Rec(Q\_m)), A will have to decide between Pay and Not Pay. And then, of course, if Receive(Q\_m) is the case, this action is completely ignored. In this case (or any equivalent formalization in which "you don't have to distinguish between Ask() and Receive()"), your argument works. P knows that it will be either in Ask() or in Rec(), and knows that in both those cases it can take the same action (because one of them is irrelevant).  
But say now we formalize it as follows: if Rec(Q\_m) is the case, the action is not ignored, and Paying indeed leads tu losing that amount of money (although you possibly also receive the big payoff thanks to your counterfactual). This more naturaly reflects the "freedom of action" of the real world, in which taking a non-sensical action fit for a different situation (like arbitrarily giving \$10 bills to people who aren't even asking for them) can result in bad outcomes. In this case, you clearly want to first check whether you're in Ask() or Rec(), and then only Pay if you're in Ask(). But again, we cannot achieve this without updating on something (granted P doesn't already know whether Ask(Q\_m) or Rec(Q\_m), that is, hasn't already completely decided the logical coin).

So the idea is again to decompose the expected value into different sorts of branches. Here, Ask and Rec are still adequate, but the Rec branches now care about two different sorts of policy points rather than one:

* Branches Q such that Rec(Q) believe that Ask(Q') implies A(Q')=give \-\> \+100, and A(Q')=refuse-\> 0\. They also believe that Rec(Q') implies that A(Q')=give \-\> \-10, and A(Q')=refuse \-\> 0\.  
* Branches Q such that Ask(Q) believe that Ask(Q') implies A(Q')=give \-\> \-10, and A(Q')=refuse \-\> U=0.

Note the "+100", "-10" notation instead of U=100; this is because, eg, receiving 100 and giving up 10 make for a total utility of 90, but I didn't want to write all of those combinations out. (So the real logical beliefs involve conjunctions of policy points implying utilities.)

The analysis here becomes more complex, because now we have to account for joint beliefs \-- we're conditioning on one policy point at a time, but the evaluation of exact utility requires knowing multiple policy points, so the expectation will involve some uncertainty about policy points not currently conditioned on.

If P believes that give/refuse in Rec branches vs Ask branches are 100% correlated (so refusing in Rec branches means refusing in Ask branches), then your analysis is exactly correct. But if P sees these as independent, then UDT will do the right thing here, instead: give up \$10 in Ask branches and not in Rec branches.  
   
I do share the opinion that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems".  
I'll have to think about how you can believe this while disagreeing with my other claims.  
To be clear, I was saying something fairly basic, like the following:  
Obviously P doesn't compartmentalize its reasoning artificially into small decision problems (it just thinks about the whole tree), so the nice properties of thinking about the possible future branches (with P's uncertainty) and assessing what's best are also used "between decision trees", for example when P is unsure about which decision problem it finds in a node. But at the same time, I challenge the further claim that, through some circuitous chain of reasoning, P can act updatefully about a fact it doesn't actually know (when still only being conditioned on A(Q)=a, and nothing else). For example, the claim that even if P is unsure about whether the next node is a Counterfactual Mugging or Parfit's Hitchhiker, if the next inductor state knows it (and P thinks it's safe to update on it), then E(U | A(Q)=a) will automatically represent this knowledge obtained from the next inductor state.

I get what you are saying here now that I understand how you think the SIST argument implied optimal updateless behavior (eg, getting cf mugging right) but not optimal updateful behavior (eg, cf mugging with homework). However, I still think you should buy the implication you're denying here. Optimal updateless behavior is a generalization of optimal updateful behavior, so while getting cf mugging right doesn't logically imply getting updateful stuff right as well, getting cf mugging right *for the same reason why classical UDT gets it right* should highly suggest solving cases which require updating.

I claim that classical UDT (no logical uncertainty) achieves the optimal policy for any single player game tree (with Omega controlling some variables in any way it wants based on the policy chosen by UDT), if it sees them coming \-- ie its prior is just the game it is in. (With of course the necessary caveats to rule out self-coordination problems if we are talking about UDT 1.0.)

I then claim that one-step logically uncertain UDT (conditioning on policy points of the form A(Q)=a) has the same property, again if it sees those trees coming, because it evaluates those problems in exactly the same way, just with extra steps to account for how all this reasoning can happen in a computationally bounded system. This is the idea of the argument marked "/////".

This implies that one-step LU UDT has the same property as classical UDT, of behaving updatefully when it is optimal to do so.

So if you buy the claim that "if P is good enough at reasoning about these particular cases (like Counterfactual Mugging), it's also good in that same way at reasoning about the whole distribution of decision problems", then it seems to me you should buy the claim that a P which is uncertain of which of several decision problems it will face, but which will be able to observe/calculate this in the next market state, and understands this to be the case, will not only see the advantages of being able to behave updatefully, but will furthermore approve of those updateful behaviors in its policy-point evaluations.

I see why this conclusion does not follow from your current perspective, but it seems to me like this perspective misses the "correct updateless behavior is a generalization of correct updateful behavior" point. I would be curious to know what you think of your argument for the "classic UDT" case. Do you claim that empirically updateless UDT fails the empirical "cf mugging with homework"? If not, where does your argument for failure depend on logical uncertainty rather than empirical uncertainty?

Best,  
The author

[image1]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image2]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image3]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image4]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image5]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png> "Argmaxing_our_strategy (1).pdf"

[image6]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image7]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image8]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image9]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png> "Impossibility_results.pdf"

[image10]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image11]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image12]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image13]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image14]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image15]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image16]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png> "The_extra_learning_assumption.pdf"

[image17]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image18]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image19]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image20]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image21]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image22]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image23]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image24]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image25]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image26]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image27]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image28]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image29]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image30]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image31]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png> "A_foundational_problem.pdf"

[image32]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image33]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image34]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png> "Getting_UDT1_1.pdf"

[image35]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image36]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image37]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image38]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image39]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image40]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image41]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image42]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image43]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image44]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image45]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image46]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image47]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png> "Deciding_what_to_be_updateful_about.pdf"

[image48]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image49]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image50]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png> "Getting_UDT1_1__Fixed_version_.pdf"

[image51]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image52]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image53]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image54]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image55]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image56]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image57]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image58]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image59]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image60]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image61]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image62]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image63]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image64]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png> "Reflection_principle_and_Epistemic_self_trust.pdf"

[image65]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image66]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image67]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image68]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image69]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image70]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image71]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image72]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image73]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image74]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image75]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image76]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image77]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image78]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image79]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image80]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image81]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image82]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image83]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image84]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image85]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image86]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image87]: <soto-email-thread-images/soto-email-thread-img-760ea039.png>

[image88]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image89]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image90]: <soto-email-thread-images/soto-email-thread-img-f449a48d.png>

[image91]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>

[image92]: <soto-email-thread-images/soto-email-thread-img-605c1e95.png>

[image93]: <soto-email-thread-images/soto-email-thread-img-b260b20b.png>

[image94]: <soto-email-thread-images/soto-email-thread-img-1050c62b.png>

[image95]: <soto-email-thread-images/soto-email-thread-img-241fc57e.png>