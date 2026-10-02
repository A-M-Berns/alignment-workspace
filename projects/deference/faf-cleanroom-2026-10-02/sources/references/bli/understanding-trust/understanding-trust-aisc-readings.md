*Copy of the author's Google Doc "Understanding Trust - Readings" ([scrubbed]): the reading list for the AISC 2025 Understanding Trust group (Hanna Gábor, Roman Malov, Norman Hsia, Paul Rapoport), who helped revise the paper into its final form. Copied verbatim from the Drive text export by a Keeper on 2026-09-29. Its first Dropbox link is [Understanding Trust paper 2025-03-13.pdf](Understanding%20Trust%20paper%202025-03-13.pdf), its second is [AISC 2025 - 1 Understanding Trust.pdf](../slides/AISC%202025%20-%201%20Understanding%20Trust.pdf), and its Drive link to Martín's final report is [Soto 2023 - 21 PIBBSS final report - Logically updateless decision-making.pdf](../soto-2023/Soto%202023%20-%2021%20PIBBSS%20final%20report%20-%20Logically%20updateless%20decision-making.pdf).*

---

# The author

# The Project Plan

My paper draft and talk slides, explaining the state of my tiling-theorem efforts so far:

  - [scrubbed]
  - [scrubbed]

This is by far the best place to start understanding what I hope we can accomplish over the three-month period of the project, because it gives the theorems in the best form I currently have, and also sketches directions for improving them.

The final part is extremely sketchy. For somewhat more detail on that part, you can read Martin Soto's final report on the work he did with me:

  - [scrubbed]

[scrubbed]

  - [scrubbed]

# Decision Theory Background

I have recently revised the LessWrong wiki page on UDT, to make it a better starting point:

  - <https://www.lesswrong.com/tag/updateless-decision-theory>

The LessWrong articles listed below are also quite relevant, and a good place to learn more.

The Timeless Decision Theory paper is also an excellent place to get started. It lacks insights that UDT has, but, it is a good explanation of lots of critical pieces of background intuition which led to the development of UDT, and I highly recommend reading it if you haven't:

  - <https://intelligence.org/files/TDT.pdf>

This is very esoteric stuff. It might also be helpful to brush up on the basics of decision theory. 

  - <https://plato.stanford.edu/entries/decision-theory/>
  - <https://plato.stanford.edu/entries/decision-causal/>

I particularly like Complete Class Theorems:

  - <https://www.lesswrong.com/posts/sZuw6SGfmZHvcAAEP/complete-class-consequentialist-foundations>

I also particularly like the Jeffrey-Bolker approach to decision theory, which I write about here:

  - <https://www.lesswrong.com/posts/A8iGaZ3uHNNGgJeaD/an-orthodox-case-against-utility-functions>
  - <https://www.lesswrong.com/posts/oheKfWA7SsvpK7SGp/probability-is-real-and-value-is-complex>

# Logical Uncertainty

The other major branch of ideas we're going to integrate with UDT is "logical uncertainty". I've personally come to prefer the term "computational uncertainty" so you might see me use these two terms interchangeably. The basic idea is that this is the type of uncertainty that you can reduce purely by thinking longer, without any empirical observations. (Obviously, this is closely related to bounded rationality, but bounded rationality is a larger cluster of concepts, while computational uncertainty focuses in on the mode of uncertain reasoning that is necessitated by bounded computational ability.)

The main model of computational uncertainty which we will use as a starting point is Logical Induction:

  - <https://arxiv.org/abs/1609.03543>

Understanding this well will be very important to the project, unless you decide to use an alternative model of computational uncertainty in your efforts to improve tiling theorems. (In particular, I think it could be reasonable to use infrabayesianism instead, especially for those of you who are already familiar with infrabayesianism.)

Some exercises which can help achieve fluency with relevant math:

  - <https://www.lesswrong.com/s/5WF3wmwvxX9TEbFXf>

Logical Induction is some fairly heavy math, which might be difficult to understand at first, and might also obscure some of the philosophical implications. Logical Induction can be seen (in hindsight) as a specific instance of the more general philosophical program called Radical Probabilism. I would encourage everyone to understand the basic ideas of Radical Probabilism in order to position Logical Induction within the broader landscape of Bayesian thinking. Here is my write-up on the subject:

  - <https://www.lesswrong.com/posts/xJyY5QkQvNJpZLJRo/radical-probabilism-1>

I think it is also important to understand the context in which logical induction came to be proposed. After all, you need to be motivated enough to see why all this extra complexity is worth considering. Why aren't simpler Bayesian methods enough?

One form of motivation comes from Scott Garrabrant's "trolling" result:

  - <https://www.lesswrong.com/posts/5bd75cc58225bf0670375533/an-untrollable-mathematician>
  - <https://www.lesswrong.com/posts/CvKnhXTu9BPcdKE4W/an-untrollable-mathematician-illustrated>
  - <https://www.lesswrong.com/posts/fhJkQo34cYw6KqpH3/thinking-about-filtered-evidence-is-very-hard>

A more general (but closely related) form of motivation comes from "realizability" (aka "grain of truth") problems with Bayesianism. Many of the desirable properties of Bayesian learning theory only hold under the assumption that the true hypothesis is in the agent's hypothesis space, or similar assumptions. This is unrealistic in the real world, since the real world contains a lot more detail than can fit into an agent's head. This and related philosophical issues are discussed further in the Emdedded Agency comic I wrote with Scott:

  - <https://www.lesswrong.com/s/Rm6oQRJJmhGCcLvxh>

# Moving Beyond UDT

In my project write-up, I mentioned several big directions for taking this project after the initial UDT + Logical Uncertainty question. I'll briefly give some readings related to those directions.

Informal essays on some weaknesses of UDT:

  - <https://www.lesswrong.com/posts/9sYzoRnmqmxZm4Whf/conceptual-problems-with-udt-and-policy-selection>
  - <https://www.lesswrong.com/posts/brXr7PJ2W4Na2EW2q/the-commitment-races-problem>

An important part of the problem is that it is unclear how we should model multi-agent decision problems (ie, games) in UDT. When UDT faces an intelligent predictor, we typically model the predictor's behavior as being dependent on UDT's policy. However, in a multi-agent scenario, this creates a situation where we need to model *both* UDT agents as depending on *each other's* policy in order to determine *their own* policy. The mathematical difficulty involved in doing so was abstracted into the Ubiquitous Converse Lawvere Problem:

  - <https://www.lesswrong.com/posts/5bd75cc58225bf06703753b9/the-ubiquitous-converse-lawvere-problem>

Ubiquitous Converse Lawvere is a sophisticated mathematical treatment of the basic idea that it seems hard to model agent1 as a function of agent2 while also modeling agent2 as a function of agent1. The problem is 'reduced' to a difficult topology problem.

Sam Eisenstat argues that the problem is solved in practice, if not in principle, by reflective oracles:

  - <https://www.lesswrong.com/posts/5bd75cc58225bf067037550d/reflective-oracles-as-a-solution-to-the-converse-lawvere>

Background reading on reflective oracles:

  - <https://arxiv.org/abs/1508.04145>
  - <https://intelligence.org/files/ReflectiveOraclesAI.pdf>
  - <https://www.auai.org/uai2016/proceedings/papers/87.pdf>

The reflective-oracle solution, when applied to UDT, has a serious problem: it solves the tgunder-definedness of the multi-agent case by magically taking a fixed point. This fixed-point can be a bad equilibrium where the agents fight for no reason (ie, [Moloch](https://slatestarcodex.com/2014/07/30/meditations-on-moloch/)). Scott Garrabrant solves this in principle by identifying a "cooperative" fixed-point which also seems rational, IE, agents won't cooperate when it costs them, but they won't engage in fights that are bad for everyone involved:

  - <https://www.lesswrong.com/posts/5bd75cc58225bf0670375419/cooperative-oracles-introduction>

This also comes with a nice computational procedure by which agents can reason about each other and arrive at a cooperative equilibrium:

  - <https://www.lesswrong.com/posts/SgkaXQn3xqJkGQ2D8/cooperative-oracles>

The resulting theory does not feel "perfectly rational" (the cooperative behavior is a little bit exploitable), but it does seem like a nice compromise with a lot of rationality and a lot of cooperativeness and relatively little exploitability. (Also, maybe we can fix this in some way, proposing a non-exploitable variant?)

However, there is still much to be desired, and I am also enthusiastic about different directions to try to solve the problems in UDT, which don't resemble Scott's cooperative oracles at all.

One such direction involves Payor's Lemma:

  - <https://www.lesswrong.com/tag/payor-s-lemma>

Another direction is Open-Minded Updatelessness:

  - <https://www.lesswrong.com/posts/uPWDwFJnxLaDiyv4M/open-minded-updatelessness>
  - <https://www.lesswrong.com/posts/p8zxx9pZvMRcoqZDm/in-defense-of-open-minded-udt>

That's all for now\! Focus on the attached paper and slides first, as the theorems there are what we need to improve on.

# Previous Literature on Tiling

<https://www.lesswrong.com/posts/5bd75cc58225bf067037556d/logical-inductor-tiling-and-why-it-s-hard>

<https://www.lesswrong.com/posts/nsbKeodxHJFKX2yYp/probabilistic-tiling-preliminary-attempt>

<https://intelligence.org/files/TilingAgentsDraft.pdf>
